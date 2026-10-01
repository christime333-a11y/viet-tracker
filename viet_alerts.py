#!/usr/bin/env python3
"""
IkaTracker -> Discord: alerts about one alliance (VIET) on one Ikariam server.

Reads the IkaTracker world map for the server and posts to a Discord webhook when:
  * a Helios Tower appears on an island where VIET has a city
  * the sawmill or luxury mine levels up on an island where VIET has a city
  * a VIET city with a Town Hall above level 5 moves to another island
  * a VIET city appears in, or disappears from, the corner zone
  * a player joins or leaves VIET (renames are reported as renames)

IkaTracker re-scans each world roughly once a day. Every run reads its small server
list first and only downloads the large world map after a fresh scan has finished.
The first scan quietly records the current situation; alerts start with the next.

    python viet_alerts.py          keep running, check every POLL_MINUTES
    python viet_alerts.py --once   one check, then exit (GitHub Actions / cron)
    python viet_alerts.py --test   read the map now and post a sample alert

Needs Python 3.8+ and nothing else.
"""
import argparse
import gzip
import html
import json
import os
import re
import sys
import time
from collections import defaultdict
from datetime import datetime, timezone
from http.cookiejar import CookieJar
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import HTTPCookieProcessor, Request, build_opener, urlopen

# ================================ SETTINGS ================================
# Discord webhook. On GitHub it comes from the VIET_WEBHOOK_URL secret, or from
# DISCORD_WEBHOOK_URL (the inactive-alerts webhook) if you don't add a separate one.
WEBHOOK_URL = (os.environ.get("VIET_WEBHOOK_URL") or os.environ.get("DISCORD_WEBHOOK_URL")
               or "PASTE_YOUR_WEBHOOK_URL_HERE")

SERVER = "s63-us"          # IkaTracker server id (s63-us = Theseus, US)
ALLIANCE = "VIET"          # alliance tag to watch (exact spelling)
ZONE_X = (1, 40)           # corner zone, X from..to (west -> east)
ZONE_Y = (80, 100)         # corner zone, Y from..to (north -> south)
MOVE_MIN_TOWN_HALL = 6     # only report moved cities with a Town Hall at least this level
POLL_MINUTES = 15          # how often to check when running continuously
MENTION = ""               # optional ping on each update, e.g. "@here" or "<@&ROLE_ID>"
# ==========================================================================

BASE_URL = "https://ikatracker.com"
MAP_URL = f"{BASE_URL}/map?" + urlencode({"server": SERVER, "alliances[]": ALLIANCE})
STATE_FILE = Path(__file__).resolve().with_name(f"{ALLIANCE.lower()}_state_{SERVER}.json")
USER_AGENT = "Mozilla/5.0 (compatible; IkaAllianceAlerts/1.0; Discord webhook notifier)"
SETTLE_MINUTES = 15        # wait this long after IkaTracker finishes scanning the server
STALE_HOURS = 48           # treat it as a problem if the server hasn't been scanned for this long
FALLBACK_HOURS = 6         # if the server list can't be understood, re-read the map this often
WARN_AFTER_HOURS = 6       # post a warning in Discord once problems have lasted this long
HELIOS_MAX_PAGES = 40      # safety cap for the Helios Tower list
MAX_EVENTS = 40            # per scan; anything beyond this is summarised in one embed

_opener = build_opener(HTTPCookieProcessor(CookieJar()))


def log(msg):
    print(f"[{datetime.now():%Y-%m-%d %H:%M:%S}] {msg}", flush=True)


def _int(value):
    try:
        return int(value)
    except (TypeError, ValueError):
        return 0


def _text(fragment):
    return html.unescape(" ".join(re.sub(r"<[^>]+>", " ", fragment).split()))


def md(text):
    """Escape Discord markdown in player/city names."""
    return re.sub(r"([\\*_~`|>\[\]])", r"\\\1", str(text))


# ------------------------------- IkaTracker -------------------------------

def http_get(url):
    req = Request(url, headers={
        "User-Agent": USER_AGENT,
        "Accept": "text/html,application/xhtml+xml",
        "Accept-Language": "en-US,en;q=0.8",
        "Accept-Encoding": "gzip",
    })
    for attempt in range(3):
        try:
            with _opener.open(req, timeout=90) as resp:
                body = resp.read()
                if resp.headers.get("Content-Encoding", "").lower() == "gzip":
                    body = gzip.decompress(body)
                return body.decode(resp.headers.get_content_charset() or "utf-8", "replace")
        except HTTPError as e:
            if e.code == 403:
                raise RuntimeError("IkaTracker refused the request (HTTP 403); "
                                   "its Cloudflare protection may be blocking scripts") from None
            if (e.code < 500 and e.code != 429) or attempt == 2:
                raise RuntimeError(f"IkaTracker returned HTTP {e.code}") from None
        except (URLError, OSError, EOFError) as e:
            if attempt == 2:
                raise RuntimeError(f"couldn't reach IkaTracker ({getattr(e, 'reason', e)})") from None
        time.sleep(10 * (attempt + 1))


AGO_RE = re.compile(r"scraped\s+(\d+)\s+(second|minute|hour|day|week|month|year)s?\s+ago", re.I)
UNITS = {"second": 1, "minute": 60, "hour": 3600, "day": 86400,
         "week": 604800, "month": 2592000, "year": 31536000}


def server_status(page):
    """(world name, scan in progress?, seconds since last scan) for SERVER, or None."""
    for chunk in re.split(r'(?=<div class="card server-row)', page)[1:]:
        if not re.search(r'server-row-id">\s*' + re.escape(SERVER) + r"\s*<", chunk):
            continue
        # The card runs until the next card's hidden forms (or the end of the list);
        # its progress bar, if any, sits after its own hidden "clear progress" form.
        card = re.split(r'<form id="form-verify-|<img\b|</main>', chunk, maxsplit=1)[0]
        text = _text(re.sub(r"<form\b.*?</form>", " ", card, flags=re.S))
        m = AGO_RE.search(text)
        ago = int(m.group(1)) * UNITS[m.group(2).lower()] if m else None
        busy = "scrape-badge" in card or bool(re.search(r"·\s*(?:Sent|Area|Type)\b|\d\s*%", text))
        return text.split(SERVER, 1)[0].strip() or SERVER, busy, ago
    return None


def parse_map(page):
    """{island id: {name, x, y, sawmill, mine, mine_level, cities}} from the map page.
    Each city is (owner, alliance tag, city name, Town Hall level)."""
    coords = {}
    for m in re.finditer(r'<a\b[^>]*\bclass="map-island-link"[^>]*>', page):
        tag = m.group(0)
        iid = re.search(r'\bdata-island-id="(\d+)"', tag)
        xy = re.search(r'\bdata-island-coords="(\d+):(\d+)"', tag)
        name = re.search(r'\bdata-island-name="([^"]*)"', tag)
        if iid and xy:
            coords[iid.group(1)] = (html.unescape(name.group(1)) if name else "",
                                    int(xy.group(1)), int(xy.group(2)))
    start = re.search(r"window\.MAP_ISLANDS\s*=\s*", page)
    if not start:
        raise RuntimeError("no island data on the map page; IkaTracker's layout may have changed")
    data, _ = json.JSONDecoder().raw_decode(page, start.end())
    islands = {}
    for iid, d in data.items():
        iid = str(iid)
        if iid not in coords or not isinstance(d, list) or len(d) < 9:
            continue
        name, x, y = coords[iid]
        cities = [(str(c[0]), str(c[1] or ""), str(c[2] or ""), _int(c[3]))
                  for c in (d[8] or []) if isinstance(c, list) and len(c) >= 4 and c[0]]
        islands[iid] = {"name": name, "x": x, "y": y, "sawmill": _int(d[0]),
                        "mine": str(d[1] or ""), "mine_level": _int(d[2]), "cities": cities}
    if len(islands) < 1000:
        raise RuntimeError(f"only {len(islands)} islands found on the map; "
                           "IkaTracker's layout may have changed")
    return islands


def helios_url(page):
    query = {"server": SERVER, "has_helios": 1}
    if page > 1:
        query["page"] = page
    return f"{BASE_URL}/islands?{urlencode(query)}"


def parse_helios_page(page):
    """(island ids whose Helios column isn't empty, highest page linked, rows seen)."""
    ids, rows, header = set(), 0, None
    for tr in re.finditer(r"<tr\b.*?</tr>", page, re.S):
        cells = re.findall(r"<t([hd])\b[^>]*>(.*?)</t[hd]>", tr.group(0), re.S)
        if not cells:
            continue
        if all(kind == "h" for kind, _ in cells):
            header = header or [_text(c).lower() for _, c in cells]
            continue
        link = re.search(r'/islands/(\d+)"', tr.group(0))
        if not link:
            continue
        rows += 1
        col = next((i for i, h in enumerate(header or []) if "helios" in h), None)
        if col is not None and col < len(cells):
            if _text(cells[col][1]).lower() in ("", "—", "-", "no"):
                continue
        ids.add(link.group(1))
    pages = [int(p) for p in re.findall(r'/islands\?[^"]*?[?&;]page=(\d+)', page)]
    return ids, max(pages, default=1), rows


def fetch_helios():
    """(set of island ids with a Helios Tower, whether the whole list was read)."""
    ids, page, last = set(), 1, 1
    while page <= last:
        if page > HELIOS_MAX_PAGES:
            return ids, False
        if page > 1:
            time.sleep(1.5)  # go easy on a free, volunteer-run site
        found, last_link, rows = parse_helios_page(http_get(helios_url(page)))
        if not rows:
            break
        ids |= found
        last = max(last, last_link)
        page += 1
    return ids, True


# ------------------------------- comparing -------------------------------

def in_zone(island):
    return bool(island) and ZONE_X[0] <= island["x"] <= ZONE_X[1] and ZONE_Y[0] <= island["y"] <= ZONE_Y[1]


def diff_cities(prev, now):
    """Match cities per owner. prev/now: lists of [owner, name, level, island].
    Returns (moves as (old, new) pairs, cities gone, cities new)."""
    old_by, new_by = defaultdict(list), defaultdict(list)
    for c in prev:
        old_by[c[0]].append(c)
    for c in now:
        new_by[c[0]].append(c)
    moves, gone, appeared = [], [], []
    for owner in set(old_by) | set(new_by):
        old, new = list(old_by[owner]), list(new_by[owner])

        def pair(test):
            pairs = sorted((abs(n[2] - o[2]), oi, ni) for oi, o in enumerate(old)
                           for ni, n in enumerate(new) if test(o, n))
            used_o, used_n, out = set(), set(), []
            for _, oi, ni in pairs:
                if oi not in used_o and ni not in used_n:
                    used_o.add(oi)
                    used_n.add(ni)
                    out.append((old[oi], new[ni]))
            old[:] = [o for i, o in enumerate(old) if i not in used_o]
            new[:] = [n for i, n in enumerate(new) if i not in used_n]
            return out

        def compatible(o, n):  # a moved or renamed city keeps its Town Hall level
            return o[2] - 1 <= n[2] <= o[2] + 3

        pair(lambda o, n: o[3] == n[3] and o[1] == n[1])                    # unchanged
        pair(lambda o, n: o[3] == n[3] and compatible(o, n))                # renamed
        moves += pair(lambda o, n: o[3] != n[3] and o[1] == n[1] and compatible(o, n))
        gone += old
        appeared += new
    return moves, gone, appeared


GOLD, BROWN, BLUE, GREEN, ORANGE, TEAL, RED, GREY = (
    0xF1C40F, 0xA0522D, 0x3498DB, 0x2ECC71, 0xE67E22, 0x1ABC9C, 0xE74C3C, 0x95A5A6)


def make_embed(title, description, url, color, world):
    return {
        "title": title[:256],
        "description": description[:4000],
        "url": url,
        "color": color,
        "footer": {"text": f"{world} · IkaTracker"[:2048]},
        "timestamp": datetime.now(timezone.utc).isoformat(timespec="seconds"),
    }


def compute_events(state, islands, helios, helios_ok):
    """Compare the new map with the saved snapshot; update the snapshot; return embeds."""
    world = state.get("world") or SERVER
    now_cities = sorted([o, n, lvl, iid] for iid, isl in islands.items()
                        for o, tag, n, lvl in isl["cities"] if tag == ALLIANCE)
    now_players = {c[0] for c in now_cities}
    prev_cities = [list(c) for c in state.get("cities", [])]
    prev_players = set(state.get("players", []))
    prev_islands = state.get("islands", {})
    prev_helios = set(state["helios"]) if state.get("helios") is not None else None

    owner_tag, owner_cities = {}, defaultdict(set)
    for iid, isl in islands.items():
        for owner, tag, name, _ in isl["cities"]:
            owner_tag[owner] = tag
            owner_cities[owner].add((iid, name))
    viet_on = defaultdict(set)
    for owner, _, _, iid in now_cities:
        viet_on[iid].add(owner)

    def label(iid):
        isl = islands.get(iid)
        return f"{md(isl['name'])} [{isl['x']}:{isl['y']}]" if isl else f"island {iid}"

    def link(iid):
        return f"{BASE_URL}/islands/{iid}"

    def players_on(iid):
        names = sorted(viet_on.get(iid, ()))
        shown = ", ".join(md(n) for n in names[:8])
        return shown + (f" and {len(names) - 8} more" if len(names) > 8 else "")

    def elsewhere(owner):
        if owner not in owner_tag:
            return "no longer on the map"
        tag = owner_tag[owner]
        return f"now in [{md(tag)}]" if tag else "now without an alliance"

    events = []
    left, joined = prev_players - now_players, now_players - prev_players

    # A player who vanished while someone new holds the same cities was renamed.
    renamed = {}
    for old in sorted(left):
        if old in owner_tag:
            continue
        old_set = {(c[3], c[1]) for c in prev_cities if c[0] == old}
        candidates = [(len(old_set & {(c[3], c[1]) for c in now_cities if c[0] == new})
                       / max(len(old_set), 1), new)
                      for new in sorted(joined) if new not in renamed.values()]
        score, new = max(candidates, default=(0, None))
        if new and score >= 0.6:
            renamed[old] = new
    for c in prev_cities:
        c[0] = renamed.get(c[0], c[0])
    left -= set(renamed)
    joined -= set(renamed.values())

    moves, gone, appeared = diff_cities(prev_cities, now_cities)

    # 1. Helios Towers
    if helios_ok and prev_helios is not None:
        for iid in sorted((helios - prev_helios) & set(viet_on), key=label):
            events.append(make_embed(
                "🗼 Helios Tower on a VIET island",
                f"**{label(iid)}** now has a Helios Tower.\n{ALLIANCE} players there: {players_on(iid)}",
                link(iid), GOLD, world))

    # 2. Mines
    for iid in sorted(set(viet_on) & set(prev_islands), key=label):
        old, isl = prev_islands[iid], islands[iid]
        lines = []
        if isl["sawmill"] > _int(old[3]):
            lines.append(f"Sawmill {_int(old[3])} → **{isl['sawmill']}**")
        if isl["mine_level"] > _int(old[5]):
            lines.append(f"{isl['mine'].capitalize() or 'Luxury'} mine {_int(old[5])} → **{isl['mine_level']}**")
        if lines:
            events.append(make_embed(
                "⛏️ Mine upgraded on a VIET island",
                f"**{label(iid)}**\n" + "\n".join(lines) + f"\n{ALLIANCE} players there: {players_on(iid)}",
                link(iid), BROWN, world))

    # 3. Moves
    for old, new in moves:
        if new[2] >= MOVE_MIN_TOWN_HALL:
            events.append(make_embed(
                "🚚 VIET city moved",
                f"**{md(new[0])}** moved **{md(new[1])}** (Town Hall {new[2]})\n"
                f"from {label(old[3])}\nto **{label(new[3])}**",
                link(new[3]), BLUE, world))

    # 4. Corner zone
    def zone_event(entered, city, reason):
        verb = "entered" if entered else "left"
        events.append(make_embed(
            f"{'📍' if entered else '🏃'} VIET city {verb} the corner zone",
            f"**{md(city[1])}** (Town Hall {city[2]}) of **{md(city[0])}**\n"
            f"{'on' if entered else 'was on'} {label(city[3])}\n{reason}",
            link(city[3]), GREEN if entered else ORANGE, world))

    for old, new in moves:
        was, now_in = in_zone(islands.get(old[3])), in_zone(islands.get(new[3]))
        if now_in and not was:
            zone_event(True, new, f"Moved in from {label(old[3])}")
        elif was and not now_in:
            zone_event(False, old, f"Moved out to {label(new[3])}")
    for city in appeared:
        if in_zone(islands.get(city[3])):
            zone_event(True, city, f"{md(city[0])} just joined {ALLIANCE}" if city[0] in joined else "New city")
    for city in gone:
        if in_zone(islands.get(city[3])):
            if city[0] in left and (city[3], city[1]) in owner_cities.get(city[0], ()):
                reason = f"{md(city[0])} left {ALLIANCE} ({elsewhere(city[0])})"
            elif city[0] not in owner_tag:
                reason = f"{md(city[0])} is no longer on the map"
            else:
                reason = "The city is no longer on the map (abandoned or destroyed)"
            zone_event(False, city, reason)

    # 5. Joins, leaves, renames
    for player in sorted(joined):
        count = sum(1 for c in now_cities if c[0] == player)
        events.append(make_embed(
            f"➕ New {ALLIANCE} member",
            f"**{md(player)}** joined {ALLIANCE} with {count} cit{'y' if count == 1 else 'ies'}.",
            MAP_URL, TEAL, world))
    for player in sorted(left):
        events.append(make_embed(
            f"➖ Player left {ALLIANCE}",
            f"**{md(player)}** left {ALLIANCE} ({elsewhere(player)}).",
            MAP_URL, RED, world))
    for old, new in sorted(renamed.items()):
        events.append(make_embed(
            f"✏️ {ALLIANCE} member renamed",
            f"**{md(old)}** is now **{md(new)}**.", MAP_URL, GREY, world))

    if len(events) > MAX_EVENTS:
        extra = events[MAX_EVENTS - 1:]
        counts = defaultdict(int)
        for e in extra:
            counts[e["title"]] += 1
        events = events[:MAX_EVENTS - 1] + [make_embed(
            f"…and {len(extra)} more changes",
            "\n".join(f"{n} × {t}" for t, n in sorted(counts.items())),
            MAP_URL, GREY, world)]

    state["cities"] = now_cities
    state["players"] = sorted(now_players)
    state["islands"] = {iid: [islands[iid]["name"], islands[iid]["x"], islands[iid]["y"],
                              islands[iid]["sawmill"], islands[iid]["mine"], islands[iid]["mine_level"]]
                        for iid in sorted(viet_on)}
    if helios_ok:
        state["helios"] = sorted(helios)
    return events


# --------------------------------- Discord ---------------------------------

class WebhookError(RuntimeError):
    """The webhook URL is wrong or was deleted; retrying won't help."""


def _retry_after(err, body):
    try:
        return min(60.0, float(err.headers.get("Retry-After")) + 0.5)
    except (TypeError, ValueError):
        pass
    try:
        wait = float(json.loads(body).get("retry_after", 5))
        return min(60.0, (wait / 1000 if wait > 100 else wait) + 0.5)
    except Exception:
        return 5.0


def post_to_discord(payload):
    body = json.dumps(payload).encode("utf-8")
    for attempt in range(5):
        req = Request(WEBHOOK_URL, data=body, method="POST",
                      headers={"Content-Type": "application/json", "User-Agent": USER_AGENT})
        try:
            with urlopen(req, timeout=30):
                return
        except HTTPError as e:
            try:
                detail = e.read().decode("utf-8", "replace")[:300]
            except Exception:
                detail = ""
            if e.code == 429:
                wait = _retry_after(e, detail)
                log(f"Discord rate limit; waiting {wait:.1f}s")
                time.sleep(wait)
                continue
            if e.code in (401, 403, 404):
                raise WebhookError(f"Discord rejected the webhook (HTTP {e.code}); "
                                   "check the webhook URL") from None
            if e.code < 500:
                raise RuntimeError(f"Discord returned HTTP {e.code}: {detail}") from None
        except (URLError, OSError):
            pass
        time.sleep(5 * (attempt + 1))
    raise RuntimeError("couldn't post to Discord after several attempts")


def flush_pending(state):
    """Send queued alert embeds, 10 per message, keeping unsent ones for next time."""
    pending = state.get("pending") or []
    allowed = {"parse": ["everyone", "roles", "users"] if MENTION else []}
    try:
        while pending:
            payload = {"embeds": pending[:10], "allowed_mentions": allowed}
            if state.get("pending_header"):
                payload["content"] = state["pending_header"]
            post_to_discord(payload)
            log(f"Posted {len(pending[:10])} alert(s) to Discord.")
            del pending[:10]
            state["pending"] = pending
            state.pop("pending_header", None)
            save_state(state)
            if pending:
                time.sleep(2)
    except WebhookError:
        raise
    except Exception as e:
        log(f"Discord error: {e}. Unsent alerts will be retried next check.")
    finally:
        if not pending:
            state.pop("pending", None)
            state.pop("pending_header", None)


# ---------------------------------- state ----------------------------------

def load_state():
    if STATE_FILE.exists():
        try:
            state = json.loads(STATE_FILE.read_text(encoding="utf-8"))
            if isinstance(state, dict):
                return state
        except (OSError, ValueError) as e:
            log(f"Couldn't read {STATE_FILE.name} ({e}); starting fresh.")
    return {"seeded": False}


def save_state(state):
    text = json.dumps(state, indent=1, ensure_ascii=False, sort_keys=True)
    try:
        if STATE_FILE.read_text(encoding="utf-8") == text:
            return  # unchanged: don't touch the file
    except OSError:
        pass
    tmp = STATE_FILE.with_suffix(".tmp")
    tmp.write_text(text, encoding="utf-8")
    os.replace(tmp, STATE_FILE)


def note_failure(state, err):
    now = int(time.time())
    hours = (now - state.setdefault("failing_since", now)) / 3600
    if hours >= WARN_AFTER_HOURS and not state.get("failure_warned"):
        try:
            post_to_discord({
                "content": (f"⚠️ {ALLIANCE} alerts for **{SERVER}** have been failing for "
                            f"{hours:.0f} hours: {err}. Still retrying; I'll post here when "
                            "it's working again."),
                "allowed_mentions": {"parse": []},
            })
            state["failure_warned"] = True
        except Exception as e:
            log(f"Couldn't post the warning to Discord either: {e}")
    save_state(state)


def note_recovery(state):
    if state.pop("failing_since", None) is not None and state.pop("failure_warned", False):
        try:
            post_to_discord({"content": f"✅ {ALLIANCE} alerts for **{SERVER}** are working again.",
                             "allowed_mentions": {"parse": []}})
        except Exception as e:
            log(f"Discord error: {e}")


# ---------------------------------- main ----------------------------------

def _ago(seconds):
    for unit, size in (("day", 86400), ("hour", 3600), ("minute", 60)):
        if seconds >= size:
            n = seconds // size
            return f"{n} {unit}{'s' if n != 1 else ''}"
    return "moments"


def check(state):
    flush_pending(state)
    now = int(time.time())
    scraped_at = None
    status = server_status(http_get(f"{BASE_URL}/servers"))
    if status and status[2] is not None:
        world, busy, ago = status
        state["world"] = world
        if ago > STALE_HOURS * 3600:
            raise RuntimeError(f"IkaTracker hasn't scanned {SERVER} for {_ago(ago)}, "
                               "so there's nothing new to check")
        note_recovery(state)
        if busy:
            log(f"IkaTracker is scanning {SERVER} right now; checking again later.")
            save_state(state)
            return
        if ago < SETTLE_MINUTES * 60:
            log(f"IkaTracker just finished scanning {SERVER}; checking again shortly.")
            save_state(state)
            return
        scraped_at = now - ago
        if state.get("seeded") and scraped_at <= state.get("scan_seen", 0) + 2 * 3600:
            log(f"No new IkaTracker scan of {SERVER} yet (last one {_ago(ago)} ago).")
            save_state(state)
            return
    else:
        log(f"Couldn't find {SERVER} on IkaTracker's server list; using a timed check instead.")
        if state.get("seeded") and now - state.get("map_read", 0) < FALLBACK_HOURS * 3600:
            return

    log(f"New IkaTracker scan of {SERVER}; reading the world map...")
    islands = parse_map(http_get(MAP_URL))
    note_recovery(state)
    try:
        helios, helios_ok = fetch_helios()
        if not helios_ok:
            log("The Helios Tower list was longer than expected; skipping Helios checks this time.")
    except Exception as e:
        log(f"Couldn't read the Helios Tower list ({e}); skipping Helios checks this time.")
        helios, helios_ok = set(), False

    world = state.get("world") or SERVER
    if not state.get("seeded"):
        compute_events(state, islands, helios, helios_ok)  # just records the snapshot
        state["seeded"] = True
        zone = sum(1 for c in state["cities"] if in_zone(islands.get(c[3])))
        summary = (f"{len(state['players'])} players, {len(state['cities']):,} cities on "
                   f"{len(state['islands'])} islands ({zone} in the corner zone)")
        log(f"First scan recorded: {summary}. Alerts start with the next change.")
        state.update(scan_seen=scraped_at or now, map_read=now)
        save_state(state)
        try:
            post_to_discord({
                "content": (f"👀 Now watching **{ALLIANCE}** on **{world}**: {summary}.\n"
                            "Alerts: Helios Towers and mine upgrades on VIET islands, "
                            f"city moves (Town Hall {MOVE_MIN_TOWN_HALL}+), cities entering or "
                            f"leaving the corner zone (X {ZONE_X[0]}–{ZONE_X[1]}, "
                            f"Y {ZONE_Y[0]}–{ZONE_Y[1]}), and players joining or leaving."),
                "allowed_mentions": {"parse": []},
            })
        except WebhookError:
            raise
        except Exception as e:
            log(f"Discord error: {e}")
        return

    events = compute_events(state, islands, helios, helios_ok)
    state.update(scan_seen=scraped_at or now, map_read=now)
    if events:
        plural = "s" if len(events) != 1 else ""
        state["pending"] = (state.get("pending") or []) + events
        state["pending_header"] = (f"{MENTION} **{len(events)} {ALLIANCE} update{plural}** "
                                   f"on {world}").strip()
        log(f"{len(events)} change(s) found.")
    else:
        log("New scan read; nothing to report.")
    save_state(state)
    flush_pending(state)
    save_state(state)


def send_test():
    islands = parse_map(http_get(MAP_URL))
    cities = [(o, n, lvl, iid) for iid, isl in islands.items()
              for o, tag, n, lvl in isl["cities"] if tag == ALLIANCE]
    if not cities:
        raise RuntimeError(f"no {ALLIANCE} cities found on the {SERVER} map")
    players = {c[0] for c in cities}
    zone = [c for c in cities if in_zone(islands[c[3]])]
    sample = max(zone or cities, key=lambda c: c[2])
    isl = islands[sample[3]]
    summary = (f"{len(players)} {ALLIANCE} players with {len(cities):,} cities on "
               f"{len({c[3] for c in cities})} islands; {len(zone)} of those cities are in the "
               f"corner zone (X {ZONE_X[0]}–{ZONE_X[1]}, Y {ZONE_Y[0]}–{ZONE_Y[1]})")
    log(f"Read the map: {summary}.")
    post_to_discord({
        "content": f"🧪 **Test message**: found {summary}. Alerts will look like this:",
        "embeds": [make_embed(
            "📍 VIET city entered the corner zone",
            f"**{md(sample[1])}** (Town Hall {sample[2]}) of **{md(sample[0])}**\n"
            f"on {md(isl['name'])} [{isl['x']}:{isl['y']}]\n(example only)",
            f"{BASE_URL}/islands/{sample[3]}", GREEN, SERVER)],
        "allowed_mentions": {"parse": []},
    })
    log("Test alert sent. Check your Discord channel.")


def main():
    ap = argparse.ArgumentParser(description=f"Discord alerts about {ALLIANCE} on IkaTracker.")
    ap.add_argument("--once", action="store_true", help="run a single check and exit")
    ap.add_argument("--test", action="store_true", help="send a sample alert to Discord and exit")
    args = ap.parse_args()
    try:
        sys.stdout.reconfigure(errors="replace")
    except Exception:
        pass

    if not WEBHOOK_URL.startswith("http"):
        sys.exit("Set WEBHOOK_URL at the top of this script (or the VIET_WEBHOOK_URL / "
                 "DISCORD_WEBHOOK_URL environment variable) to your Discord webhook URL.")
    try:
        if args.test:
            try:
                send_test()
            except Exception as e:
                log(f"Test failed: {e}")
                sys.exit(1)
            return

        state = load_state()
        log(f"Watching {ALLIANCE} on {SERVER}"
            + ("" if args.once else f", checking every {POLL_MINUTES} min (Ctrl+C to stop)"))
        while True:
            try:
                check(state)
            except WebhookError as e:
                log(f"Discord error: {e}")
                save_state(state)
                if args.once:
                    sys.exit(1)
            except Exception as e:
                log(f"Check failed: {e}")
                if os.environ.get("GITHUB_ACTIONS") == "true":
                    print(f"::warning::{e}", flush=True)
                note_failure(state, e)
            if args.once:
                return
            time.sleep(POLL_MINUTES * 60)
    except KeyboardInterrupt:
        log("Stopped.")


if __name__ == "__main__":
    main()

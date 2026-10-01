#!/usr/bin/env python3
"""eBay parts watcher -> Discord webhook. Stdlib only, reuses relay.py's eBay client.
Finds the lowest delivered price on genuine (OEM) parts from reputable sellers, Buy It Now and auctions.
The webhook comes from env PARTS_HOOK (repo secret). Nothing personal lives in this file.
Modes:  python3 parts.py scan   -> post NEW listings that pass every rule (new lowest price pings)
        python3 parts.py board  -> one "best price right now" board, one line per part"""
import json, os, re, sys, time, html, urllib.parse, datetime as dt
from zoneinfo import ZoneInfo
ET = ZoneInfo("America/New_York")
from relay import ebay_token, ebay_json, aspects_of, num, post, log, NOW

HOOK = os.environ.get("PARTS_HOOK")
STATE = "state/parts.json"
AV = "https://cdn.jsdelivr.net/gh/jdecked/twemoji@latest/assets/72x72/1f527.png"
MIN_FB, MIN_FB_N = 98.5, 100            # reputable sellers only
AUCTION_WINDOW_H = 48                   # surface auctions in their last 48h
GETITEM_CAP = int(os.environ.get("PARTS_GETITEM_CAP", 10))   # per scan run; board runs get 60
SCAN_SLICE = 16                          # search calls per 15-min scan; full list cycles every ~90 min (eBay quota shared with the laptop hunter)

# Aftermarket listings almost always say one of these. A genuine part may still say "replacement" in the sense of
# "replacement part", so that word is only fatal next to compatible/for-brand wording.
AFTERMARKET = re.compile(r"\bcompatible\b|\bcompatibility\b|\breplacement for\b|\bfor (?:lenovo|thinkpad|ibm)\b|"
                         r"\baftermarket\b|\bgeneric\b|\bnon[- ]?oem\b|\bthird[- ]party\b|\bnew replacement\b|"
                         r"\bfits\b|\bwork(?:s)? with\b|\bhigh capacity\b|\bupgraded?\b|\bpremium\b|\boem quality\b|"
                         r"\bunbranded\b|\bcopy\b|\bclone\b|\breplica\b|^\W*replacement\b|\breplacement (?:lenovo|thinkpad|ibm)\b", re.I)
GENUINE = re.compile(r"\bgenuine\b|\boriginal\b|\boem\b|\bauthentic\b|\blenovo\b", re.I)
JUNK = re.compile(r"for parts|not working|as[- ]is|\bdead\b|\bswollen\b|\bbulg|\bdamaged\b|\bbroken\b|\blot of\b|"
                  r"\b\d+ ?(?:pcs|pack)\b|\bwholesale\b|\bempty\b|\bshell\b|\bcase only\b|\bdummy\b|\bfiller\b|"
                  r"\bblank\b|\bcover\b(?! included)", re.I)
BAD_SELLER_COND = re.compile(r"\bfor parts\b|not working", re.I)

INTERNAL_FRU = r"01AV419|01AV420|01AV421|01AV489|SB10K9757[678]"
EXT24_FRU = r"01AV422|01AV423|01AV424|01AV452|SB10K9757[9]|SB10K9758[01]|4X50M08810"
EXT48_FRU = r"01AV425|01AV426|01AV490|01AV491|SB10K9758[23]|4X50M08811"
EXT72_FRU = r"01AV427|01AV428|01AV492|SB10K9758[45]|4X50M08812"

PARTS = [
    {"id": "int", "label": "Internal battery (front, 24Wh)", "cat": "14295", "max_total": 60,
     "q": ["01AV421 battery", "01AV420 battery", "01AV419 battery", "01AV489 battery", "t480 internal battery genuine",
           "thinkpad t480 internal battery oem"],
     "must": INTERNAL_FRU, "brand": "lenovo", "battery": True},
    {"id": "ext", "label": "External battery (rear 61 / 61+ / 61++)", "cat": "14295", "max_total": 95,
     "q": ["01AV427 battery", "01AV428 battery", "01AV422 battery", "01AV423 battery", "01AV424 battery",
           "4X50M08812", "4X50M08810", "thinkpad t480 battery 72wh genuine", "thinkpad t480 61++ battery",
           "t480 rear battery genuine", "thinkpad t480 external battery oem"],
     "must": "|".join([EXT24_FRU, EXT48_FRU, EXT72_FRU]), "brand": "lenovo", "battery": True},
    {"id": "scr", "label": "Smart card reader (00HW553)", "cat": "31530", "max_total": 35,
     "q": ["00HW553", "t480 smart card reader", "t470 smart card reader", "thinkpad t480 smartcard reader"],
     "must": r"00HW553|(?=.*smart ?card)(?=.*\bt4[78]0\b(?!s))", "exclude": r"\bt4[78]0s\b|\bt49\d|filler|dummy|blank",
     "brand": None, "battery": False},
    {"id": "ram", "label": "16GB DDR4 SO-DIMM (one stick)", "cat": "170083", "max_total": 45,
     "q": ["16gb ddr4 2400 sodimm", "16gb ddr4 2666 sodimm", "16gb ddr4 3200 sodimm", "16gb pc4-2400t sodimm",
           "16gb pc4-2666v sodimm", "16gb pc4-3200aa sodimm", "samsung 16gb ddr4 sodimm", "sk hynix 16gb ddr4 sodimm",
           "crucial 16gb ddr4 sodimm", "micron 16gb ddr4 sodimm", "kingston 16gb ddr4 sodimm"],
     "must": r"(?=.*\b16 ?gb\b)(?=.*(?:ddr4|pc4))(?=.*(?:so-?dimm|sodimm|laptop|notebook|260[- ]?pin))",
     "exclude": r"\b[24] ?x ?(?:4|8|16) ?gb\b|\b(?:4|8|16) ?gb ?x ?[24]\b|\b(?:4|8) ?gb\b|\b32 ?gb\b|\bkit\b|\bpair\b|"
                r"\b[2-9] ?(?:pcs|pieces|sticks|modules)\b|\bset of\b|\becc\b|\bregistered\b|\brdimm\b|\budimm\b|"
                r"\bdesktop\b|\b288[- ]?pin\b|\bddr3\b|\bddr5\b|\bserver\b",
     "brands": r"samsung|sk ?hynix|hynix|micron|crucial|kingston|lenovo", "oem": False,
     "brand": None, "battery": False},
    {"id": "chg", "label": "Charger (genuine 65W USB-C)", "cat": "31510", "max_total": 25,
     "q": ["ADLX65YLC3A", "ADLX65YLC2A", "ADLX65YCC3A", "01FR024 charger", "01FR025 charger", "4X20M26272",
           "genuine lenovo 65w usb-c charger", "lenovo thinkpad usb-c 65w adapter oem"],
     "must": r"(?=.*(?:ADLX65Y[LCD]C[23]A|01FR02[4-7]|01FR030|SA10M1394[5-8]|4X20M26272|65 ?w))(?=.*(?:usb[- ]?c|type[- ]?c|ADLX65Y))",
     "exclude": r"\b(?:45|90|95|100|135|170|230) ?w\b|slim tip|square tip|rectangular|dock|cable only|car charger",
     "brand": "lenovo", "battery": False},
    {"id": "wifi", "label": "Wi-Fi card (Intel AX210, M.2 2230)", "cat": None, "max_total": 30, "oem": False,
     "q": ["intel ax210ngw", "intel ax210 m.2 2230", "ax210ngw wifi 6e card", "intel wi-fi 6e ax210 2230"],
     "must": r"(?=.*ax210)(?=.*(?:ngw|m\.?2|2230|ngff))", "brands": r"intel",
     "exclude": r"desktop|pci-?e x1|pcie card|\badapter\b|antenna kit|with antennas?|\bkit\b|usb|vpro|ax211|cnvio",
     "brand": None, "battery": False},
    {"id": "fpr", "label": "Fingerprint reader (01YR508)", "cat": None, "max_total": 40, "off": True,   # unit already has one
     "q": ["01YR508", "01LW329 fingerprint", "t480 fingerprint reader", "thinkpad t480 fingerprint sensor"],
     "must": r"01YR50[89]|01LW329|(?=.*fingerprint)(?=.*\bt480\b(?!s))",
     "exclude": r"\bt480s\b|\bt580\b|\bl[45]80\b|\be480\b|01YN09[67]|palm ?rest|keyboard|touchpad|cable only",
     "brand": None, "battery": False},
]

PARTS = [p for p in PARTS if not p.get("off")]      # parked watches stay defined so they can be switched back on


def load():
    try: return json.load(open(STATE))
    except Exception: return {"seen": {}, "best": {}, "board": {}}

def save(s):
    cutoff = (NOW - dt.timedelta(days=30)).timestamp()
    s["seen"] = {k: v for k, v in s["seen"].items() if v > cutoff}
    os.makedirs("state", exist_ok=True); json.dump(s, open(STATE, "w"))

def search(tok, part, q, auction):
    qs = urllib.parse.urlencode({"q": q, **({"category_ids": part["cat"]} if part.get("cat") else {}), "limit": "100",
        "sort": "endingSoonest" if auction else "price",
        "filter": f"price:[1..{part['max_total']}],priceCurrency:USD,itemLocationCountry:US,"
                  "conditionIds:{1000|1500|2000|2010|2020|2500|3000},"
                  "buyingOptions:{" + ("AUCTION" if auction else "FIXED_PRICE") + "}"})
    d = ebay_json(tok, "https://api.ebay.com/buy/browse/v1/item_summary/search?" + qs) or {}
    out = []
    for x in d.get("itemSummaries") or []:
        sel = x.get("seller") or {}
        try:
            if float(sel.get("feedbackPercentage") or 0) < MIN_FB or int(sel.get("feedbackScore") or 0) < MIN_FB_N: continue
        except Exception: continue
        auc = "AUCTION" in (x.get("buyingOptions") or [])
        p = float(((x.get("currentBidPrice") if auc else None) or x.get("price") or {}).get("value") or 0)
        sh = None
        for so in x.get("shippingOptions") or []:
            try: sh = float((so.get("shippingCost") or {}).get("value") or 0); break
            except Exception: pass
        ends = None
        try: ends = dt.datetime.fromisoformat((x.get("itemEndDate") or "").replace("Z", "+00:00"))
        except Exception: pass
        out.append({"id": x.get("itemId"), "title": x.get("title") or "", "link": (x.get("itemWebUrl") or "").split("?")[0],
                    "img": (x.get("image") or {}).get("imageUrl"), "price": p, "ship": sh, "auction": auc, "ends": ends,
                    "bids": x.get("bidCount") or 0, "cond": x.get("condition") or "",
                    "seller": f"{sel.get('username','?')} · {sel.get('feedbackPercentage','?')}% ({sel.get('feedbackScore','?')})"})
    return out

def title_ok(part, it):
    t = it["title"]
    if JUNK.search(t) or (part.get("oem", True) and AFTERMARKET.search(t)): return False
    if part.get("exclude") and re.search(part["exclude"], t, re.I): return False
    if not re.search(part["must"], t, re.I): return False
    if part.get("oem", True) and not GENUINE.search(t): return False
    if part.get("brands") and not re.search(part["brands"], t, re.I): return False
    total = it["price"] + (it["ship"] or 0)
    return 0 < total <= part["max_total"]

def verify(part, it, tok):
    """Open the listing: brand/OEM item specifics, seller condition notes and description must all hold up."""
    d = ebay_json(tok, "https://api.ebay.com/buy/browse/v1/item/" + urllib.parse.quote(it["id"], safe="|"))
    if not d: return None
    a = aspects_of(d)
    desc = re.sub(r"<[^>]+>", " ", html.unescape(d.get("description") or ""))[:6000]
    notes_txt = " ".join([d.get("conditionDescription") or "", d.get("shortDescription") or ""])
    if BAD_SELLER_COND.search(d.get("condition") or "") or JUNK.search(notes_txt): return None
    brand = (a.get("brand") or "").lower()
    if part["battery"]:
        if brand and not re.search(r"lenovo|ibm", brand): return None          # e.g. "Unbranded", "Topkaiyuen"
        if AFTERMARKET.search(" ".join([notes_txt, a.get("type", ""), a.get("mpn", ""), desc[:1500]])): return None
        if re.search(r"\bnot (?:genuine|original|oem)\b", desc + " " + notes_txt, re.I): return None
    if part.get("brands"):
        mb = brand or (a.get("manufacturer") or "").lower()
        if mb and not re.search(part["brands"], mb, re.I): return None
        spd = " ".join([a.get("bus speed", ""), a.get("speed", ""), it["title"]])
        if re.search(r"\b(?:2133|1866|1600)\b", spd): return None                # too slow for the T480's 2400 bus
        mods = num(a.get("number of modules", ""))                               # ONE 16GB stick only, never a kit
        per = a.get("capacity per module", "") or a.get("total capacity", "")
        if (mods and mods != 1) or (per and not re.search(r"\b16 ?gb\b", per, re.I)): return None
    if it.get("ship") is None:
        try: it["ship"] = float((((d.get("shippingOptions") or [{}])[0]).get("shippingCost") or {}).get("value") or 0)
        except Exception: it["ship"] = 0.0
    total = it["price"] + (it["ship"] or 0)
    if total > part["max_total"]: return None
    cap = ""
    if part["id"] == "ext":
        blob = " ".join([it["title"], a.get("capacity", ""), a.get("battery capacity", "")])
        cap = ("72Wh 61++" if re.search(r"\b7[0-2] ?wh\b|61\+\+|" + EXT72_FRU, blob, re.I) else
               "48Wh 61+" if re.search(r"\b4[78] ?wh\b|61\+(?!\+)|" + EXT48_FRU, blob, re.I) else
               "24Wh 61" if re.search(r"\b2[34] ?wh\b|" + EXT24_FRU, blob, re.I) else "capacity ?")
    notes = []
    cond = d.get("condition") or it["cond"]
    if part["battery"] and re.search(r"used|pre-?owned", cond, re.I):
        notes.append("used battery: ask for cycle count / wear level")
    if part["battery"] and re.search(r"\bnew\b", cond, re.I) and not re.search(r"20(?:2[2-9])", desc + it["title"]):
        notes.append("new-old-stock: ask manufacture date")
    if part["id"] == "ram":
        notes.append("confirm your current RAM is ONE 16GB stick (2 slots, 32GB max)")
    if part["id"] == "scr":
        notes.append("needs the reader-to-board cable: confirm included")
    if part["id"] == "fpr":
        notes.append("confirm your palm rest has the fingerprint opening (non-FPR units use a blank)")
    if part["id"] == "wifi":
        notes.append("T480 has no Wi-Fi whitelist; reuse your 2 antenna leads (MHF4)")
    if it["auction"]:
        left = (it["ends"] - NOW).total_seconds() / 3600 if it.get("ends") else None
        notes.insert(0, f"AUCTION, {it['bids']} bids" + (f", ends in {left:.0f}h" if left is not None else "") +
                     f". Max bid ${part['max_total'] - (it['ship'] or 0):,.0f} keeps it under ${part['max_total']} delivered")
    return {"total": round(total, 2), "cap": cap, "cond": cond, "notes": notes,
            "mpn": a.get("mpn") or a.get("manufacturer part number") or "", "brand": a.get("brand") or ""}

def embed(part, it, v, tag):
    f = [{"name": "Delivered", "value": f"**${v['total']:,.2f}**", "inline": True},
         {"name": "Price", "value": f"${it['price']:,.2f}" + (" (bid)" if it["auction"] else ""), "inline": True},
         {"name": "Ship", "value": "free" if not it["ship"] else f"${it['ship']:,.2f}", "inline": True},
         {"name": "Condition", "value": v["cond"][:60] or "?", "inline": True},
         {"name": "Seller", "value": it["seller"][:80], "inline": True}]
    if v["cap"]: f.append({"name": "Capacity", "value": v["cap"], "inline": True})
    if v["mpn"] or v["brand"]: f.append({"name": "Brand / MPN", "value": f"{v['brand']} {v['mpn']}".strip()[:80], "inline": True})
    if v["notes"]: f.append({"name": "Check", "value": " · ".join(v["notes"])[:300], "inline": False})
    e = {"title": it["title"][:250], "url": it["link"], "color": 0xE5A639 if it["auction"] else 0x3987E5,
         "author": {"name": f"{tag} · {part['label']}"}, "fields": f, "footer": {"text": "eBay · OEM filter + seller ≥98.5%"},
         "timestamp": NOW.isoformat()}
    if (it.get("img") or "").startswith("https://"): e["thumbnail"] = {"url": it["img"]}
    return e

def gather(full=False):
    tok = ebay_token()
    if not tok: log("parts: no eBay token"); sys.exit(1)
    found = {p["id"]: [] for p in PARTS}
    seen_ids = set()
    jobs = [(p, q, auc) for p in PARTS for q in p["q"] for auc in (False, True)]
    if not full:                                    # frequent scans rotate through the list (eBay daily call quota)
        n = min(SCAN_SLICE, len(jobs)); start = (int(NOW.timestamp() // 900) * n) % len(jobs)
        jobs = [jobs[(start + i) % len(jobs)] for i in range(n)]
    for p, q, auc in jobs:
        for it in search(tok, p, q, auc):
            if it["id"] in seen_ids or not title_ok(p, it): continue
            if auc and (not it["ends"] or (it["ends"] - NOW).total_seconds() > AUCTION_WINDOW_H * 3600
                        or it["ends"] <= NOW): continue
            seen_ids.add(it["id"]); found[p["id"]].append(it)
        time.sleep(0.25)
    return tok, found

def run(mode):
    if not HOOK: log("parts: PARTS_HOOK not set"); sys.exit(1)
    s = load(); first = not s["seen"]
    global GETITEM_CAP
    if mode == "board": GETITEM_CAP = 100
    per_part = 14 if mode == "board" else 3              # every part gets its share; big result sets can't starve the rest
    tok, found = gather(full=(mode == "board"))
    checked, verified, posts = 0, {p["id"]: [] for p in PARTS}, []
    for p in PARTS:
        pc = 0
        for it in sorted(found[p["id"]], key=lambda x: x["price"] + (x["ship"] or 0)):
            cached = s["board"].get(it["id"])
            if cached and mode == "board":
                verified[p["id"]].append((it, cached)); continue
            if it["id"] in s["seen"] and mode == "scan": continue
            if checked >= GETITEM_CAP or pc >= per_part: break
            checked += 1; pc += 1
            v = verify(p, it, tok); time.sleep(0.2)
            s["seen"][it["id"]] = NOW.timestamp()
            if not v: continue
            s["board"][it["id"]] = v
            verified[p["id"]].append((it, v))
    if mode == "scan":
        for p in PARTS:
            for it, v in sorted(verified[p["id"]], key=lambda x: x[1]["total"]):
                best = s["best"].get(p["id"])
                new_low = best is None or v["total"] < best - 0.01
                if new_low: s["best"][p["id"]] = v["total"]
                tag = "📉 NEW LOW" if new_low and best is not None else "🆕 NEW"
                posts.append((p, it, v, tag, new_low and best is not None))
        if first: posts = posts[:8]
        sent = 0
        for p, it, v, tag, ping in posts[:10]:
            ok = post(HOOK, {"username": "Computer Project", "avatar_url": AV,
                             "content": ("@everyone " if ping else "") + f"**{tag}** · {p['label']}",
                             "allowed_mentions": {"parse": ["everyone"]}, "embeds": [embed(p, it, v, tag)]})
            sent += ok; time.sleep(1.2)
        log(json.dumps({"mode": "scan", "found": {k: len(v) for k, v in found.items()}, "getitem": checked, "posted": sent}))
    else:
        lines = []
        for p in PARTS:
            rows = sorted(verified[p["id"]], key=lambda x: x[1]["total"])
            if p["id"] == "ext":            # best per capacity, rear battery comes in three sizes
                pick, have = [], set()
                for it, v in rows:
                    if v["cap"] not in have: have.add(v["cap"]); pick.append((it, v))
                rows = pick
            else:
                rows = rows[:2]
            lines.append(f"**{p['label']}**")
            if not rows: lines.append("> nothing genuine under $%d right now" % p["max_total"])
            for it, v in rows[:3]:
                kind = f"🔨 bid, ends {it['ends'].astimezone(ET):%a %-I%p} ET" if it["auction"] and it.get("ends") else "BIN"
                lines.append(f"> [${v['total']:,.2f} delivered]({it['link']}) · {(v['cap'] + ' · ') if v['cap'] else ''}"
                             f"{v['cond'][:22]} · {kind} · {it['seller'].split(' · ')[-1]}")
            if rows: s["best"][p["id"]] = rows[0][1]["total"]
        total = sum(min((v["total"] for _, v in verified[p["id"]]), default=0) for p in PARTS if p["id"] != "ext")  # incl. charger/wifi/fpr
        ext = min((v["total"] for _, v in verified["ext"]), default=0)
        e = {"title": f"🔧 Best genuine prices · {NOW:%a %b %-d}", "color": 0x2ECC71,
             "description": "\n".join(lines)[:3900],
             "footer": {"text": f"Cheapest full set ≈ ${total + ext:,.2f} delivered · eBay · OEM only · seller ≥98.5%"}}
        ok = post(HOOK, {"username": "Computer Project", "avatar_url": AV, "embeds": [e]})
        log(json.dumps({"mode": "board", "ok": ok, "getitem": checked}))
        if not ok: sys.exit(1)
    s["board"] = {k: v for k, v in s["board"].items() if k in s["seen"]}
    save(s)

if __name__ == "__main__":
    run(sys.argv[1] if len(sys.argv) > 1 else "scan")

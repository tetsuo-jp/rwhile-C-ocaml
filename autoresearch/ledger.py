#!/usr/bin/env python3
"""ledger.py — 候補の採否台帳。**同じ課題を毎晩掘り返さないため**にある。

  ./ledger.py mark --id ID --status {done,deferred,rejected} --note "..."
  ./ledger.py list [--status S]
  ./ledger.py dry-rounds        直近で「新規候補ゼロ」が何回続いたか

status の意味:
  done      解けた。以後は候補に出さない
  rejected  課題として成立しない（受入コマンドが着手前から通る等）。出さない
  deferred  今回は解けなかった。**また出す**——状況が変われば解ける
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

LEDGER = Path(__file__).resolve().parent / "ledger.json"


def load() -> dict:
    if LEDGER.exists():
        return json.loads(LEDGER.read_text())
    return {"entries": [], "rounds": []}


def save(d: dict) -> None:
    LEDGER.write_text(json.dumps(d, ensure_ascii=False, indent=2) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)

    m = sub.add_parser("mark")
    m.add_argument("--id", required=True)
    m.add_argument("--status", required=True, choices=["done", "deferred", "rejected"])
    m.add_argument("--note", default="")
    m.add_argument("--date", default="", help="省略時は記録しない（テストの再現性のため）")

    ls = sub.add_parser("list")
    ls.add_argument("--status")

    sub.add_parser("dry-rounds")

    a = ap.parse_args()
    d = load()

    if a.cmd == "mark":
        if not a.id:
            print("id が空。台帳には載せない", file=sys.stderr)
            return 1
        for e in d["entries"]:
            if e["id"] == a.id:
                e.update(status=a.status, note=a.note, date=a.date)
                break
        else:
            d["entries"].append({"id": a.id, "status": a.status, "note": a.note, "date": a.date})
        save(d)
        print(f"{a.id}: {a.status}")
        return 0

    if a.cmd == "list":
        for e in d["entries"]:
            if a.status and e["status"] != a.status:
                continue
            print(f"{e['id']}  {e['status']:<9} {e.get('note', '')[:100]}")
        return 0

    if a.cmd == "dry-rounds":
        n = 0
        for r in reversed(d.get("rounds", [])):
            if r.get("candidates", 0) == 0:
                n += 1
            else:
                break
        print(n)
        return 0

    return 1


if __name__ == "__main__":
    sys.exit(main())

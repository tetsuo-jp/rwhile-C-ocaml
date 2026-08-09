#!/usr/bin/env python3
"""extract_task.py — 選定フェーズのログから課題 JSON を取り出す。

`claude -p` の出力は散文＋JSON なので、`accept_cmd` を持つ **最後の** JSON
オブジェクトを採る（モデルが途中で例を書くことがあるため、最後を正とする）。

  extract_task.py <select.log> <task.json>   見つかれば書き出し 0、無ければ 1
"""
from __future__ import annotations

import json
import re
import sys


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    txt = open(sys.argv[1], errors="replace").read()
    best = None
    for m in re.finditer(r"\{[^{}]*\"accept_cmd\"[^{}]*\}", txt, re.S):
        try:
            best = json.loads(m.group(0))
        except Exception:
            pass
    if not best or not best.get("accept_cmd"):
        return 1
    best.setdefault("title", "(無題)")
    json.dump(best, open(sys.argv[2], "w"), ensure_ascii=False)
    return 0


if __name__ == "__main__":
    sys.exit(main())

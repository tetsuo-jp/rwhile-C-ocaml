#!/usr/bin/env python3
"""enumerate.py — 残課題の候補を「機械が観測できる信号」から列挙する。

LLM は呼ばない。ここが決定的でないと、ループは毎晩もっともらしい作り話を
生み出すだけになる。候補の順位づけと言語化だけを LLM に任せる。

  ./enumerate.py                 候補を JSONL で stdout へ
  ./enumerate.py --metrics F     metrics.sh の出力を使い回す（再測定しない）
  ./enumerate.py --no-ledger     採否台帳による除外をしない（デバッグ用）

信号（増やすときは「exit code か数で判定できるか」を先に確かめること）:
  skip-test        走っていない検査。SKIP は「異常なし」と区別がつかない
  open-pin         期待される失敗として固定された穴（OPEN / KNOWN BUG）
  agda-postulate   証明の穴
  agda-unchecked   一度も型検査されていないモジュール（.agdai が無い）
  metric-regress   baseline.json からの退行
  roadmap-open     ロードマップの未完項目（優先度は低い。文言なので機械判定が弱い）
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent


def cid(source: str, title: str) -> str:
    return hashlib.sha1(f"{source}|{title}".encode()).hexdigest()[:12]


def cand(out: list, source: str, title: str, evidence: str, gate_hint: str) -> None:
    out.append({
        "id": cid(source, title),
        "source": source,
        "title": title,
        "evidence": evidence.strip()[:600],
        "gate_hint": gate_hint,
    })


def run(cmd: list[str], cwd: Path, timeout: int = 900) -> str:
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        return p.stdout + p.stderr
    except Exception as e:  # noqa: BLE001 — 列挙は落とさない。信号が取れないこと自体を報告する
        return f"<failed: {e}>"


def sig_skips(out: list) -> None:
    txt = run(["./test-suite"], REPO / "src")
    for line in txt.splitlines():
        if "[SKIP]" in line:
            name = line.split("]", 1)[-1].strip()
            cand(out, "skip-test", f"走っていない検査を走らせる: {name}",
                 line.strip(),
                 "その検査が SKIP でなく実行され、緑になること")


def sig_open_pins(out: list) -> None:
    ts = REPO / "src" / "TestSuite.ml"
    if not ts.exists():
        return
    for i, line in enumerate(ts.read_text(errors="replace").splitlines(), 1):
        # 「was a KNOWN BUG」は**直った印**（過去形）。候補にしない（2026-08-09 偽陽性）。
        if re.search(r"\bOPEN\b|KNOWN BUG", line) and not re.search(
                r"was a KNOWN BUG|was an OPEN|WAS A KNOWN BUG|FIXED", line, re.I):
            title = re.sub(r"\s+", " ", line.strip())[:120]
            cand(out, "open-pin", f"pin されている穴を塞ぐ: {title}",
                 f"src/TestSuite.ml:{i}: {title}",
                 "その pin が「期待される失敗」でなく「直った」を主張する形に書き換わり、緑になること")


def sig_agda(out: list) -> None:
    agda = REPO / "proofs" / "agda"
    if not agda.is_dir():
        return
    build = sorted(agda.glob("_build/*/agda"))
    build = build[0] if build else None
    for f in sorted(agda.glob("RWhile*.agda")):
        text = f.read_text(errors="replace")
        if re.search(r"^\s*postulate", text, re.M):
            cand(out, "agda-postulate", f"postulate を消す: {f.name}",
                 f"{f.name} に postulate がある",
                 f"agda --safe {f.name} が通り、postulate がゼロになること")
        # NOTE: 1 行目の `{-# OPTIONS --safe #-}` の有無は信号にしない。
        # check.sh は全モジュールに `agda --safe` をコマンドラインで渡すので、
        # プラグマが無くても検査は --safe で走っている（2026-08-09 に偽陽性として棄却）。
        if build is not None and not (build / f"{f.stem}.agdai").exists():
            cand(out, "agda-unchecked", f"一度も型検査されていない: {f.name}",
                 f"{build}/{f.stem}.agdai が無い",
                 f"agda --safe {f.name} が通り .agdai が生成されること")


def sig_metrics(out: list, cur: dict, base: dict) -> None:
    if not base:
        return
    b, c = base, cur

    if c.get("fp2", {}).get("comp2_eq_B") != b.get("fp2", {}).get("comp2_eq_B"):
        cand(out, "metric-regress", "fp2 の自己適用が退行した（最優先）",
             f"comp2_eq_B: {b['fp2']['comp2_eq_B']} -> {c.get('fp2', {}).get('comp2_eq_B')}",
             "./measure_proj full で [comp2](('S.swap)) == B : true に戻ること")

    bt, ct = b.get("tests", {}), c.get("tests", {})
    if ct.get("total", 0) < bt.get("total", 0):
        cand(out, "metric-regress", "テストが減った",
             f"total: {bt.get('total')} -> {ct.get('total')}",
             "テスト総数が基準以上に戻ること")
    if ct.get("skipped", 0) > bt.get("skipped", 0):
        cand(out, "metric-regress", "SKIP が増えた（走っていない検査が増えた）",
             f"skipped: {bt.get('skipped')} -> {ct.get('skipped')}",
             "SKIP の数が基準以下に戻ること")

    def jr(d: dict, key: str) -> dict:
        return {r["subject"]: r["jr_work"] for r in d.get(key, [])}

    for key in ("jones_self", "dyncontrol"):
        bj, cj = jr(b, key), jr(c, key)
        for subj, bv in bj.items():
            cv = cj.get(subj)
            if cv is None:
                cand(out, "metric-regress", f"被験が消えた: {key}/{subj}",
                     f"{subj} が {key} の表から消えた", f"{key} の表に {subj} が戻ること")
            elif cv > bv + 1e-9:
                cand(out, "metric-regress", f"Jr(work) が悪化: {key}/{subj}",
                     f"{subj}: {bv} -> {cv}", f"{subj} の Jr(work) が {bv} 以下に戻ること")

    ba, ca = b.get("agda", {}), c.get("agda", {})
    for k, label in (("files_with_postulate", "postulate を含むファイル"),
                     ("never_checked", "未検査モジュール")):
        if ca.get(k, 0) > ba.get(k, 0):
            cand(out, "metric-regress", f"{label}が増えた",
                 f"{k}: {ba.get(k)} -> {ca.get(k)}", f"{k} が基準以下に戻ること")


def sig_roadmap(out: list) -> None:
    rm = REPO / "RESEARCH_ROADMAP.md"
    if not rm.exists():
        return
    for i, line in enumerate(rm.read_text(errors="replace").splitlines(), 1):
        # 進捗の記録行（★）と取り消し線は「完了済み」なので候補にしない。
        # 「残り」「要る」は文中に頻出して偽陽性を生むため語彙から外した（2026-08-09）。
        if re.search(r"未着手|未解決|未検討", line) and "~~" not in line and "★" not in line:
            t = re.sub(r"\s+", " ", line.strip())
            if len(t) < 25:
                continue
            cand(out, "roadmap-open", f"ロードマップの未完項目: {t[:110]}",
                 f"RESEARCH_ROADMAP.md:{i}", "その項目に対応する検査が新設され、緑になること")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--metrics", type=Path, help="metrics.sh の出力（再測定を省く）")
    ap.add_argument("--no-ledger", action="store_true")
    args = ap.parse_args()

    if args.metrics and args.metrics.exists():
        cur = json.loads(args.metrics.read_text())
    else:
        cur = json.loads(run([str(HERE / "metrics.sh")], REPO, timeout=2400) or "{}")

    base_f = HERE / "baseline.json"
    base = json.loads(base_f.read_text()) if base_f.exists() else {}

    out: list = []
    sig_skips(out)
    sig_open_pins(out)
    sig_agda(out)
    sig_metrics(out, cur, base)
    sig_roadmap(out)

    seen: dict = {}
    led_f = HERE / "ledger.json"
    if led_f.exists() and not args.no_ledger:
        seen = {e["id"]: e for e in json.loads(led_f.read_text()).get("entries", [])}

    # 却下済み・解決済みは出さない。保留（deferred）は出す——状況が変われば解けるので。
    kept = [c for c in out if seen.get(c["id"], {}).get("status") not in ("done", "rejected")]

    for c in kept:
        print(json.dumps(c, ensure_ascii=False))
    print(f"# candidates={len(kept)} (raw={len(out)}, filtered_by_ledger={len(out) - len(kept)})",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())

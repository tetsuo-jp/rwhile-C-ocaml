#!/usr/bin/env python3
"""validate_accept.py — 受入コマンドが「そもそも通り得る」かを検査する。

なぜ要るか（2026-08-09、SMOKE の実運用で判明）:
事前 FAIL 検査は「いま落ちる」ことしか見ない。**壊れた受入コマンドも落ちる**ので、
そのまま通してしまう。実例——モデルが書いたのは

  cd src && make run-tests 2>&1 | grep -c 'test_fp1_dyncond_known_bug' \\
    && ! ./test-suite test dyn-cond 2>&1 | grep -q 'error in update'

`dyn-cond` という群は存在せず（正しくは `dyn-control`）、`test_fp1_...` は OCaml の
関数名なので Alcotest の出力には決して現れない。**課題を正しく解いても永久に通らない。**
一晩を無駄にする前に、機械で分かる範囲を落とす。

  validate_accept.py <task.json> <repo>   問題なければ 0、あれば理由を出して 1
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path


def groups(repo: Path) -> set[str]:
    """TestSuite.ml のテスト群名（`"name", [` の形）を集める。"""
    ts = repo / "src" / "TestSuite.ml"
    if not ts.exists():
        return set()
    return set(re.findall(r'^\s*"([a-z0-9][a-z0-9-]*)",\s*\[', ts.read_text(errors="replace"), re.M))


def ocaml_idents(repo: Path) -> set[str]:
    ts = repo / "src" / "TestSuite.ml"
    if not ts.exists():
        return set()
    return set(re.findall(r"^let\s+(test_[A-Za-z0-9_']+)", ts.read_text(errors="replace"), re.M))


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    task = json.loads(Path(sys.argv[1]).read_text())
    repo = Path(sys.argv[2])
    cmd = task.get("accept_cmd", "")
    problems: list[str] = []

    if not cmd.strip():
        problems.append("accept_cmd が空")

    # 1. 存在しないテスト群を指していないか
    known = groups(repo)
    for g in re.findall(r"test-suite\s+test\s+([A-Za-z0-9_-]+)", cmd):
        if known and g not in known:
            near = [k for k in known if k.startswith(g[:4])]
            hint = f"（近いもの: {', '.join(sorted(near)[:3])}）" if near else ""
            problems.append(f"テスト群 '{g}' は存在しない{hint}")

    # 2. OCaml の識別子をテスト出力から grep していないか（出力には現れない）
    idents = ocaml_idents(repo)
    for lit in re.findall(r"grep[^|;&]*?['\"]([^'\"]+)['\"]", cmd):
        if lit in idents:
            problems.append(f"'{lit}' はソースの関数名で、テスト出力には現れない")
        elif lit.startswith("test_"):
            problems.append(f"'{lit}' は関数名らしき文字列。テスト出力を grep しても当たらない")

    # 3. テストの「人間向け出力」を grep して判定していないか
    #    Alcotest が出すのは `[OK]` / `[FAIL]` / `Test Successful in ...` であって
    #    `PASS` ではない。2026-08-09 に `grep -c "....*PASS"` を書かれ、これは
    #    課題を解いても永久に 0 件になる。判定は exit code で取ること。
    ALCOTEST_MARKERS = ("[FAIL]", "[OK]", "Test Successful", "failure", "error in update")
    pipes_test_output = re.search(r"(test-suite|make\s+run-tests)[^|]*\|[^|]*grep", cmd)
    if pipes_test_output:
        pats = re.findall(r"grep[^|;&]*?['\"]([^'\"]+)['\"]", cmd)
        for lit in pats:
            if not any(m in lit for m in ALCOTEST_MARKERS):
                problems.append(
                    f"テスト出力を grep して '{lit}' を探している。Alcotest の出力は "
                    f"[OK]/[FAIL]/Test Successful であって PASS ではない。exit code で判定すること")
    if re.search(r"grep\s+-c\b", cmd):
        problems.append("grep -c は 0 件のとき非ゼロ終了する。"
                        "「無いことの確認」と「コマンドの失敗」が区別できないので使わない")

    # 4. 危ないもの
    for bad, why in (("git push", "外部へ反映する"), ("rm -rf", "破壊的"),
                     ("curl", "ネットワークを使う"), ("wget", "ネットワークを使う")):
        if bad in cmd:
            problems.append(f"'{bad}' を含む（{why}）")

    # 5. 常設ゲートに合成しているか（新しい検査だけで合格させない）
    if "make run-tests" not in cmd and "check.sh" not in cmd and "measure_proj" not in cmd \
            and "test-suite" not in cmd and "agda" not in cmd:
        problems.append("既存のゲート（make run-tests / test-suite / check.sh / measure_proj / agda）"
                        "を 1 つも呼んでいない")

    if problems:
        for p in problems:
            print(f"NG: {p}")
        return 1
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())

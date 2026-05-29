#!/usr/bin/env python3
"""Report the number of real `sorry`s in the project (informational only).

Counts term/tactic-position `sorry`s — block comments (`/- ... -/`) and line
comments (`-- ...`) are stripped first, so docstrings narrating proof plans do
not inflate the count (a naive grep over-counts ~10x; see docs/EXTERNAL_AUDIT.md).

Prints the total and a per-file breakdown and always exits 0. This is a
visibility tool, not a gate: it deliberately does NOT assert an exact count, so
closing or decomposing a theorem requires no bookkeeping here. Correctness of
the *axiom surface* is guarded separately by `AxiomCheck.lean`.
"""
import re
import pathlib

TOKEN = re.compile(r"(?<![A-Za-z_])sorry(?![A-Za-z_])")


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)  # block comments
    text = re.sub(r"--.*", "", text)                 # line comments
    return text


root = pathlib.Path(__file__).resolve().parent.parent
total = 0
per_file = []
for p in sorted(root.rglob("*.lean")):
    if ".lake" in p.parts:
        continue
    n = len(TOKEN.findall(strip_comments(p.read_text(encoding="utf-8"))))
    if n:
        per_file.append((n, str(p.relative_to(root))))
        total += n

print(f"Term-position sorries: {total}")
for n, f in sorted(per_file, reverse=True):
    print(f"  {n:3d}  {f}")

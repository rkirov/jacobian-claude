#!/usr/bin/env python3
"""Regression guard: assert exactly the expected number of term-position
`sorry`s in the project.

Counts only real `sorry`s in code — block comments (`/- ... -/`) and line
comments (`-- ...`) are stripped first, so docstrings narrating closure
chains do not inflate the count (see docs/EXTERNAL_AUDIT.md for why a naive
grep over-counts ~10x).

Usage:  python3 scripts/check_sorries.py [EXPECTED]   (default EXPECTED=8)
Exit 0 if the count matches, 1 otherwise.
"""
import re
import sys
import pathlib

EXPECTED = int(sys.argv[1]) if len(sys.argv) > 1 else 11

# The remaining classical-content sorries, for a readable report.
# (S1 closed 2026-05-29; S4 decomposed into 6 named classical sub-walls,
# with the algebraic glue proven — see PeriodLattice.lean §S4.)
KNOWN = {
    "S2": "DiscreteTopology (truePeriodLattice X)",
    "S3": "IsZLattice ℝ (truePeriodLattice X)",
    "S4a": "isLocalHomeoOffCritical (inverse fn thm)",
    "S4b": "chartPullback_not_eventuallyConst (globalized identity thm; isOpenMap now PROVEN from it)",
    "S4c": "isCoveringMapOn_compl_branchLocus (covering off branch locus)",
    "S4e": "exists_loop_off_branchLocus (genericity)",
    "S4f": "exists_preimageCycle_of_off_branchLocus (lift + trace)",
    "S5": "genus_eq_zero_iff_homeo (uniformization)",
    "S6": "deg_div (residue theorem)",
    "S7": "abelJacobi_twoPoint_ne_zero (Abel + Riemann-Hurwitz)",
    "S8": "ambientPhi_ambientPsi_eq (degree identity)",
}

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

print(f"Term-position sorries (comment-stripped): {total} (expected {EXPECTED})")
for n, f in sorted(per_file, reverse=True):
    print(f"  {n:3d}  {f}")
print("Known classical-content sorries:")
for k, v in KNOWN.items():
    print(f"  {k}: {v}")

if total != EXPECTED:
    print(
        f"\nERROR: sorry count {total} != expected {EXPECTED}.\n"
        "If you intentionally added or closed a sorry, update EXPECTED here "
        "and docs/STATUS.md. If you added an UNSOUND free-parameter `sorry` "
        "lemma (cf. the S8 ambientPhi_ambientPsi_eq bug), fix the statement "
        "rather than bumping the count.",
        file=sys.stderr,
    )
    sys.exit(1)
print("\nOK: sorry count matches.")

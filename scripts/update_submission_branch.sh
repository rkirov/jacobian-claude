#!/usr/bin/env bash
# Rebuild the derived `submission` branch: main + one generated commit containing
# the lean-eval workspace (submission/jacobian_challenge_diffgeo/). Run from a clean
# main checkout. The branch is disposable — always regenerated from scratch.
set -euo pipefail
git switch -C submission main
python3 scripts/make_submission.py
git add submission/
git commit -m "Generated lean-eval submission workspace (jacobian_challenge_diffgeo)

Derived from main $(git rev-parse --short main) by scripts/make_submission.py."
git switch main
echo "submission branch rebuilt on top of main $(git rev-parse --short main)"

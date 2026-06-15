#!/usr/bin/env bash
# Run leanprover/comparator against this repo's solution to the lean-eval problem
# `jacobian_challenge_diffgeo`, mirroring lean-eval's own check as closely as possible:
# same toolchain, same Mathlib, the verbatim Challenge.lean/Solution.lean/config.json,
# and the real comparator (statement match + permitted-axiom check + kernel replay).
#
# A local PASS here should mean a PASS on the lean-eval leaderboard.
#
# Trust required: the Lean kernel, Mathlib, comparator/Challenge.lean (the statement), and
# comparator itself. The proofs in the Jacobians library are NOT trusted — comparator
# re-checks them independently via lean4export + the kernel, in a landrun sandbox.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WS="$HERE/comparator"
TOOLCHAIN_TAG=$(sed -e 's/^leanprover\/lean4://' "$WS/lean-toolchain" | tr -d '[:space:]')
WORK="${COMPARATOR_WORK:-$HOME/.cache/jacobian-comparator}"
mkdir -p "$WORK"

# comparator + lean4export pinned to the SAME toolchain that built the library, so
# lean4export can read its `.olean`s (the export format is toolchain-locked).
if [ ! -d "$WORK/comparator" ]; then
  git clone --branch "$TOOLCHAIN_TAG" --depth 1 \
    https://github.com/leanprover/comparator "$WORK/comparator"
fi
if [ ! -d "$WORK/lean4export" ]; then
  git clone --branch "$TOOLCHAIN_TAG" --depth 1 \
    https://github.com/leanprover/lean4export "$WORK/lean4export"
fi
(cd "$WORK/comparator" && lake build)
(cd "$WORK/lean4export" && lake build)

# landrun sandbox binary, wrapped to grant the dynamic loader the read+exec paths its
# -ldd resolution can miss (the ELF interpreter on Ubuntu, the Nix store on NixOS) —
# without exec on the interpreter every execve inside the sandbox fails with EACCES.
if [ ! -x "$WORK/landrun-bin" ]; then
  curl -sL -o "$WORK/landrun-bin" \
    https://github.com/Zouuup/landrun/releases/download/v0.1.14/landrun-linux-amd64
  chmod +x "$WORK/landrun-bin"
fi
EXTRA=""
for d in /lib64 /lib /usr/lib /nix/store; do
  [ -e "$d" ] && EXTRA="$EXTRA --rox $d"
done
printf '#!/usr/bin/env bash\nexec "%s/landrun-bin"%s "$@"\n' "$WORK" "$EXTRA" \
  > "$WORK/landrun"
chmod +x "$WORK/landrun"
export COMPARATOR_LANDRUN="$WORK/landrun"
export PATH="$WORK/lean4export/.lake/build/bin:$WORK:$PATH"

# Build the workspace (Challenge spec, Solution bridge, Submission → library) and run.
cd "$WS"
lake build Challenge Solution Submission
exec lake env "$WORK/comparator/.lake/build/bin/comparator" config.json

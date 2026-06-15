import Lake
open Lake DSL

package jacobian where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

-- Pinned to lean-eval's v4.30.0 environment (toolchain + Mathlib commit) so the
-- in-repo comparator checks the identical environment the hosted judge uses.
-- (Verso, used only by the docs site under `site/`, is required there, not here.)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c5ea00351c28e24afc9f0f84379aa41082b1188f"

@[default_target]
lean_lib Jacobians where
  -- Build *every* module under `Jacobians/`, not just those reachable from the
  -- `Jacobians.lean` root. Without this, orphan modules (probes / in-progress
  -- endgames not yet wired into the challenge aggregator) are skipped by
  -- `lake build`, which once let a RED commit sit undetected on `main`.
  globs := #[.andSubmodules `Jacobians]

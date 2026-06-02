# docs/ — index

Navigation for the Jacobians challenge design/research notes. Grouped by role.
For the authoritative *code* state, prefer `git grep -nE ':= *sorry|=> *sorry'`
over any prose status doc (status docs lag the tree).

## Canonical references (start here)

| Doc | What it is |
|---|---|
| [DESIGN.md](DESIGN.md) | Construction choices (period-lattice Jacobian, topological genus, what is deferred). |
| [REFERENCES.md](REFERENCES.md) | Textbooks/papers to fall back on (Forster, Miranda, …). |
| [architecture_map.md](architecture_map.md) | Live dependency DAG to a sorry-free finish. |
| [STATUS.md](STATUS.md) | Living status snapshot. **Lags the tree** — verify against `git grep sorry`. |

## Active per-problem playbooks

The remaining work is ~5 problems (see `architecture_map.md`). Per-problem notes:

| Problem | Doc(s) |
|---|---|
| **RR / Serre core** | [riemann_roch_proof_plan.md](riemann_roch_proof_plan.md) (deep reference), [dolbeault_ladder_derisk.md](dolbeault_ladder_derisk.md) (representation + refined cost), [cech_finiteness_research.md](cech_finiteness_research.md) (H¹ finiteness, Forster 14.9), [dolbeault_disk_atom_decomposition.md](dolbeault_disk_atom_decomposition.md) (∂̄-on-a-disk atom), [dolbeault_comparison_forward_plan.md](dolbeault_comparison_forward_plan.md) (Čech↔Dolbeault forward operator) |
| **#3 Abel two-point** | [abel_riemannroch_research.md](abel_riemannroch_research.md) |
| **#7 period-lattice full rank** | [period_lattice_realbasis_research.md](period_lattice_realbasis_research.md) |

## Archive (`archive/`) — historical / superseded

Recon and superseded plans, kept for provenance. Not load-bearing.

- `archive/EXTERNAL_AUDIT.md` — external-repo recon (brsanch port + mrdouglasny vendoring; complete).
- `archive/dolbeault_hodge_feasibility.md` — feasibility/LoC study; superseded by `dolbeault_ladder_derisk.md`.
- `archive/loop_off_branch_research.md`, `archive/genus_endgame_wiring_plan.md`,
  `archive/period_realbasis_plan.md`, `archive/trace_branchpoint_plan.md`,
  `archive/preimage_cycle_lift_plan.md`, `archive/S8_TRACE_PLAN.md` — superseded plan docs.

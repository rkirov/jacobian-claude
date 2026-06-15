/-
Unreferenced-declaration report (Tier-2 polish): every non-internal `Jacobians.*` declaration
that no other declaration's type or proof references, with its defining module.

These are candidates for deletion or `private`, NOT automatic deletions: API endpoints,
`#print axioms` targets (AuditAll), challenge-surface declarations, and instances
(used by synthesis, which DOES leave references — an unreferenced instance is genuinely unused)
must be filtered against before acting.

Run: lake env lean scripts/unused_decls.lean   → docs/unused_decls.txt
-/
import Jacobians
import Lean

open Lean

#eval show CoreM Unit from do
  let env ← getEnv
  let names := env.header.moduleNames
  let datas := env.header.moduleData
  let isOurs (n : Name) : Bool := (`Jacobians).isPrefixOf n
  -- all constants referenced by ANY Jacobians declaration (types + proof bodies)
  let mut used : NameSet := {}
  let mut declared : Array (Name × Name) := #[]   -- (decl, module)
  for i in [0:datas.size] do
    let mod := names[i]!
    unless isOurs mod do continue
    for c in datas[i]!.constNames do
      let some ci := env.find? c | continue
      unless c.isInternalDetail do
        declared := declared.push (c, mod)
      for u in ci.type.getUsedConstants do
        used := used.insert u
      if let some v := ci.value? (allowOpaque := true) then
        for u in v.getUsedConstants do
          used := used.insert u
  let mut out : Array String := #[]
  for (c, mod) in declared do
    unless used.contains c do
      out := out.push s!"{mod} | {c}"
  let sorted := out.qsort (· < ·)
  IO.FS.writeFile "docs/unused_decls.txt" (String.intercalate "\n" sorted.toList ++ "\n")
  IO.println s!"{sorted.size} unreferenced declarations (of {declared.size} non-internal) -> docs/unused_decls.txt"

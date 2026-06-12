/-
Kernel-level usage graph of the Jacobians library.

For every constant declared in a `Jacobians.*` module, collect the constants referenced by its
elaborated type and value (`Expr.getUsedConstants`) and attribute them to their defining modules.
This sees what text search cannot: instances, lemmas applied by automation, anything that ends up
in a proof term. (It does NOT see elaboration-only artifacts that leave no constant behind —
notation, macros, bare `attribute` retags; grep for those separately.)

Run from the repo root (slow — loads the full environment, walks every term):

  lake env lean scripts/usage_graph.lean

Output: `docs/usage_graph.json` with
  modules : { module → declaration count }
  edges   : [ { from, to, count, witnesses : [ [userDecl, usedDecl] ] } ]
where an edge `from → to` means: a declaration of `from` references a constant declared in `to`
(both restricted to `Jacobians.*`, self-edges dropped). `count` is the number of (user, used)
constant pairs; `witnesses` samples up to 5 non-internal pairs.
-/
import Jacobians
import Lean

open Lean

#eval show CoreM Unit from do
  let env ← getEnv
  let names := env.header.moduleNames
  let datas := env.header.moduleData
  let isOurs (n : Name) : Bool := (`Jacobians).isPrefixOf n
  let mut declCount : Std.HashMap Name Nat := {}
  let mut count : Std.HashMap (Name × Name) Nat := {}
  let mut wit : Std.HashMap (Name × Name) (Array (Name × Name)) := {}
  for i in [0:datas.size] do
    let src := names[i]!
    unless isOurs src do continue
    for c in datas[i]!.constNames do
      declCount := declCount.insert src (declCount.getD src 0 + 1)
      let some ci := env.find? c | continue
      -- NB v4.30: `ci.value?` returns none for theorems by default (proofs are opaque-gated);
      -- ask for the value explicitly or the graph silently loses all proof-level usage.
      let used := ci.type.getUsedConstants
        ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      let mut seen : NameSet := {}
      for u in used do
        if seen.contains u then continue
        seen := seen.insert u
        let some j := env.getModuleIdxFor? u | continue
        let tgt := names[j.toNat]!
        if isOurs tgt && tgt != src then
          let k := (src, tgt)
          count := count.insert k (count.getD k 0 + 1)
          let ws := wit.getD k #[]
          if ws.size < 5 && !c.isInternalDetail && !u.isInternalDetail then
            wit := wit.insert k (ws.push (c, u))
  let modsJson := Json.mkObj <| declCount.toList.map fun (m, n) => (m.toString, Json.num n)
  let edgesJson := Json.arr <| count.toList.toArray.map fun ((a, b), n) =>
    Json.mkObj [("from", Json.str a.toString), ("to", Json.str b.toString),
      ("count", Json.num n),
      ("witnesses", Json.arr <| (wit.getD (a, b) #[]).map fun (u, v) =>
        Json.arr #[Json.str u.toString, Json.str v.toString])]
  let out := Json.mkObj [("modules", modsJson), ("edges", edgesJson)]
  IO.FS.writeFile "docs/usage_graph.json" out.pretty
  IO.println s!"wrote docs/usage_graph.json: {declCount.size} modules, {count.size} edges"

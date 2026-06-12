#!/usr/bin/env python3
"""Cross-check textual imports against the kernel-level usage graph.

Inputs: docs/usage_graph.json (from `lake env lean scripts/usage_graph.lean`) and the
`import Jacobians.*` lines of the sources. Reports, per module:

  REMOVABLE  direct imports whose module contributes no constant to this module's terms,
             directly or through any transitively-reachable usage (shake-style candidates;
             check for notation/attribute effects before deleting);
  HIDDEN     usage of a module that is not a direct import (reaches through a re-export) —
             these are the "sneaky" couplings that text search misses.

Run from the repo root after regenerating the json."""
import json, os, re, sys, collections

imp = re.compile(r'^import (Jacobians[\w.]*)', re.M)
deps = {}
for root, _, files in os.walk('Jacobians'):
    for f in files:
        if f.endswith('.lean'):
            p = os.path.join(root, f)
            m = 'Jacobians.' + p[len('Jacobians/'):-5].replace('/', '.')
            deps[m] = [d for d in imp.findall(open(p).read()) if d != 'Jacobians']

g = json.load(open('docs/usage_graph.json'))
uses = collections.defaultdict(set)            # module -> modules whose constants it references
for e in g['edges']:
    uses[e['from']].add(e['to'])
wit = {(e['from'], e['to']): e['witnesses'] for e in g['edges']}

def used_transitively(m, d):
    """d (or anything below d) supplies a constant used by m, via imports inside d's cone."""
    seen, todo = set(), [d]
    while todo:
        x = todo.pop()
        if x in seen: continue
        seen.add(x)
        if x in uses[m]: return True
        todo += [y for y in deps.get(x, []) if y in deps]
    return False

removable, hidden = [], []
for m, ds in sorted(deps.items()):
    for d in ds:
        if d in deps and not used_transitively(m, d):
            removable.append((m, d))
    for u in sorted(uses[m]):
        if u not in ds:
            hidden.append((m, u))

print(f"modules: {len(deps)}   usage edges: {len(g['edges'])}")
print(f"\nREMOVABLE imports (no constant used from the import's cone) — {len(removable)}:")
for m, d in removable:
    print(f"  {m}  -X->  {d}")
print(f"\nHIDDEN usage (constant used without a direct import) — {len(hidden)}:")
for m, u in hidden:
    ws = wit.get((m, u), [])
    w = f"   e.g. {ws[0][0]} uses {ws[0][1]}" if ws else ''
    print(f"  {m}  ~~>  {u}{w}")

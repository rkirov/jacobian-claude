#!/usr/bin/env python3
"""List Jacobians.* modules unreachable from the challenge files' import graph.

Run from the repo root:  python3 scripts/dead_modules.py
Roots: ChallengeConformance.lean + ChallengeLeaderboard.lean (which import the
Jacobians root library). A module listed here is dead code w.r.t. the challenge;
per repo convention (2026-06-09 cleanup directive) dead orphans get deleted, but
re-run AFTER any in-flight branch is merged - phase files are often committed
before their consumers wire them into the root imports.
"""
import os, re, collections

def mod_of_path(p): return p[:-5].replace('/', '.')
def path_of_mod(m): return m.replace('.', '/') + '.lean'

allmods = {mod_of_path(os.path.join(r, f))
           for r, _, fs in os.walk('Jacobians') for f in fs if f.endswith('.lean')}
allmods.add('Jacobians')
imp_re = re.compile(r'^import\s+(Jacobians[\w.]*)', re.M)

def imports(mod):
    p = 'Jacobians.lean' if mod == 'Jacobians' else path_of_mod(mod)
    try: return imp_re.findall(open(p).read())
    except FileNotFoundError: return []

roots = []
for f in ('ChallengeConformance.lean', 'ChallengeLeaderboard.lean'):
    roots += imp_re.findall(open(f).read())
seen, queue = set(), collections.deque(roots)
while queue:
    m = queue.popleft()
    if m in seen: continue
    seen.add(m)
    queue.extend(imports(m))

dead = sorted(allmods - seen)
print(f"live: {len(seen & allmods)}   dead: {len(dead)}")
for m in dead: print(m)

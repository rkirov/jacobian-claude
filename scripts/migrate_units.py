#!/usr/bin/env python3
"""Phase-M1 unit migration: move every module into its unit's directory, rewrite imports
and docstring path references everywhere, and emit per-unit umbrella files.

Reads the assignment from scripts/unit_design.py (RULES/META). Single-module units keep
their top-level file. Run with --dry-run to print the plan; without it, executes git mv +
rewrites. Run from the repo root."""
import os, re, subprocess, sys, collections

DRY = '--dry-run' in sys.argv

src = open('scripts/unit_design.py').read()
exec(src.split('# cycle detection')[0])          # mods, deps, assign, units, uedges
exec(src.split('# ---- per-unit metadata')[1].split('imp = re.compile')[0]
     if False else '')                            # META comes from the exec above
# (META is defined in the first exec segment since it precedes the import scan)

# ---- plan ----
moves = {}      # old module (short) -> (new module short, old path, new path)
for u, members in units.items():
    if len(members) < 2:
        for m in members:                         # single-module units: top-level file
            base = m.split('.')[-1]
            if m != base:
                moves[m] = (base, mods[m], f"Jacobians/{base}.lean")
        continue
    d = META[u][0]
    base_seen = {}
    for m in members:
        base = m.split('.')[-1]
        if base in base_seen:
            sys.exit(f"COLLISION in unit {u}: {m} vs {base_seen[base]} -> {base}.lean")
        base_seen[base] = m
        new = f"{d}.{base}"
        if new != m:
            moves[m] = (new, mods[m], f"Jacobians/{d}/{base}.lean")

print(f"moves: {len(moves)}  (of {len(mods)} modules; "
      f"{sum(1 for u in units if len(units[u]) < 2)} single-module units untouched)")
if DRY:
    bydir = collections.Counter(v[2].split('/')[1] for v in moves.values())
    for d, n in sorted(bydir.items()):
        print(f"  {n:>4} -> Jacobians/{d}/")
    for m, (new, op, np_) in sorted(moves.items())[:8]:
        print(f"  e.g. {op}  ->  {np_}")
    sys.exit(0)

# ---- execute moves ----
for m, (new, op, np_) in sorted(moves.items()):
    os.makedirs(os.path.dirname(np_), exist_ok=True)
    subprocess.run(['git', 'mv', op, np_], check=True)

# ---- rewrite imports + docstring path references in every tracked text file ----
lean_files = []
for root, dirs, files in os.walk('.'):
    if any(p in root for p in ['.git', '.lake', '/submission']): continue
    for f in files:
        if f.endswith(('.lean', '.py', '.md', '.sh', '.yml')):
            lean_files.append(os.path.join(root, f))

imp_subs = [(re.compile(rf'\bJacobians\.{re.escape(m)}(?![\w.])'), f'Jacobians.{new}')
            for m, (new, _, _) in moves.items()]
path_subs = [(op[:-5], np_[:-5]) for _, (_, op, np_) in moves.items()]  # sans .lean

def rewrite_imports_only(text):
    """Apply module renames ONLY on `import` lines. Declaration namespaces often coincide
    textually with module names (`namespace Jacobians.Forms.Montel`) — a global substitution
    silently RENAMES DECLARATIONS. Import lines are the only module references in Lean."""
    out = []
    for line in text.split('\n'):
        if line.startswith('import '):
            for rx, rep in imp_subs:
                line = rx.sub(rep, line)
        out.append(line)
    return '\n'.join(out)

changed = 0
for p in lean_files:
    try: t = open(p).read()
    except UnicodeDecodeError: continue
    t0 = t
    if p.endswith('.lean'):
        t = rewrite_imports_only(t)
    else:
        for rx, rep in imp_subs:
            t = rx.sub(rep, t)
    for old, new in path_subs:
        t = t.replace(old + '.lean', new + '.lean')
    if t != t0:
        open(p, 'w').write(t)
        changed += 1
print(f"rewrote references in {changed} files")

# ---- per-unit umbrella files with the unit docstring ----
WHITE, GRAY, BLACK = 0, 1, 2  # recompute reduced deps on NEW names (same graph shape)
for u, members in sorted(units.items()):
    if len(members) < 2: continue
    d = META[u][0]
    dirname, desc, keys = META[u]
    dep_units = sorted(uedges.get(u, set()))
    newmods = sorted(moves[m][0] if m in moves else m for m in members)
    body = [f"/-!\n# {u.replace('-', ' ').title()} (`Jacobians/{d}/`)\n"]
    body.append(desc + '\n')
    body.append('**Keystones:** ' + '; '.join(f'`{k}`' for k in keys) + '\n')
    body.append('**Builds on units:** ' + (', '.join(dep_units) or 'none (foundation)') + '\n-/')
    imports = '\n'.join(f'import Jacobians.{m}' for m in newmods)
    open(f'Jacobians/{d}.lean', 'w').write(imports + '\n\n' + '\n'.join(body) + '\n')
    subprocess.run(['git', 'add', f'Jacobians/{d}.lean'], check=True)
print("umbrella files written")

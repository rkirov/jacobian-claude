#!/usr/bin/env python3
"""Per-file #min_imports sweep (the safe import-minimization route; shake --fix lied to us).

Phase 1 (`collect`): for each module under Jacobians/ (skipping the root and the unit
umbrella files, whose imports are deliberate re-exports), elaborate a temp copy with
`import Mathlib.Tactic.MinImports` appended to the import block and `#min_imports` at EOF,
and record the suggested import list. Sequential (8 GB box). Suggestions are cached in
/tmp/min_imports_cache/ keyed by module name, so the phase is resumable.

Phase 2 (`apply`): replace each file's contiguous import block with the suggestion.
Apply ONLY after a green full build; afterwards run the full gate and repair stragglers
(missing notation/tactic imports show up as precise unknown-identifier errors).

Usage:
  python3 scripts/min_imports_sweep.py collect [N]   # process at most N files (default all)
  python3 scripts/min_imports_sweep.py apply         # rewrite import blocks from cache
  python3 scripts/min_imports_sweep.py status
"""
import os, re, subprocess, sys, tempfile

CACHE = '/tmp/min_imports_cache'
os.makedirs(CACHE, exist_ok=True)

def modules():
    out = []
    for root, _, files in os.walk('Jacobians'):
        for f in sorted(files):
            if not f.endswith('.lean'):
                continue
            p = os.path.join(root, f)
            mod = p[:-5].replace('/', '.')
            # skip unit umbrellas (Jacobians/<Dir>.lean with a sibling dir): re-export files
            if root == 'Jacobians' and os.path.isdir(p[:-5]):
                continue
            out.append((mod, p))
    return out

def split_imports(text):
    """(prefix-comments, import-lines, rest). Imports are the contiguous block of
    `import` lines (allowing blank/comment lines between)."""
    lines = text.split('\n')
    i, n = 0, len(lines)
    # leading comments / blank lines before the first import
    while i < n and not lines[i].startswith('import '):
        i += 1
    if i == n:
        return text, [], ''
    j, imports = i, []
    last_import = i
    while j < n:
        if lines[j].startswith('import '):
            imports.append(lines[j]); last_import = j
        elif lines[j].strip() == '' or lines[j].lstrip().startswith('--'):
            pass
        else:
            break
        j += 1
    return '\n'.join(lines[:i]), imports, '\n'.join(lines[last_import + 1:])

def collect(limit):
    import functools, builtins
    global print
    print = functools.partial(builtins.print, flush=True)
    mods = modules()
    todo = [(m, p) for m, p in mods if not os.path.exists(f'{CACHE}/{m}')]
    print(f"{len(mods)} modules, {len(todo)} uncollected")
    for k, (m, p) in enumerate(todo[:limit]):
        text = open(p).read()
        head, imports, rest = split_imports(text)
        tmp = os.path.join(tempfile.mkdtemp(), 'probe.lean')
        open(tmp, 'w').write(
            head + '\n' + '\n'.join(imports)
            + '\nimport Mathlib.Tactic.MinImports\n' + rest
            + '\n\nset_option maxHeartbeats 1600000 in\n#min_imports\n')
        r = subprocess.run(['lake', 'env', 'lean', tmp], capture_output=True, text=True)
        # this toolchain's #min_imports emits `public import X` (module-system syntax);
        # our files use plain imports, so strip the prefix
        sugg = [l.strip().removeprefix('public ').strip() for l in r.stdout.splitlines()
                if (l.strip().startswith('import ') or l.strip().startswith('public import '))
                and 'Mathlib.Tactic.MinImports' not in l]
        if r.returncode != 0 or not sugg:
            print(f"  [{k}] FAIL {m} (exit {r.returncode}, {len(sugg)} suggestions)")
            open(f'{CACHE}/{m}.fail', 'w').write(r.stdout[-3000:] + r.stderr[-2000:])
            continue
        open(f'{CACHE}/{m}', 'w').write('\n'.join(sorted(set(sugg))))
        print(f"  [{k}] {m}: {len(imports)} -> {len(sugg)} imports")

def apply():
    changed = 0
    for m, p in modules():
        c = f'{CACHE}/{m}'
        if not os.path.exists(c):
            continue
        sugg = open(c).read().strip().split('\n')
        text = open(p).read()
        head, imports, rest = split_imports(text)
        if sorted(set(imports)) == sorted(set(sugg)):
            continue
        open(p, 'w').write((head + '\n' if head.strip() else '')
                           + '\n'.join(sugg) + rest)
        changed += 1
    print(f"applied to {changed} files — now run the full gate")

def status():
    mods = modules()
    done = sum(1 for m, _ in mods if os.path.exists(f'{CACHE}/{m}'))
    fail = sum(1 for m, _ in mods if os.path.exists(f'{CACHE}/{m}.fail'))
    print(f"{done}/{len(mods)} collected, {fail} failed")

cmd = sys.argv[1] if len(sys.argv) > 1 else 'status'
if cmd == 'collect':
    collect(int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9)
elif cmd == 'apply':
    apply()
else:
    status()

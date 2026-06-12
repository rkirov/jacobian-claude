#!/usr/bin/env python3
"""Generate the Verso exposition site sources from the unit decomposition.

The unit docstrings in scripts/unit_design.py (META) are the single source of truth:
this script emits site/Site.lean (landing page + table of contents) and one
site/Site/<Dir>.lean chapter per unit — description, keystone declarations (linked to
the doc-gen4 API docs), member modules (linked to GitHub), and builds-on cross-links.

Run from the repo root; then `cd site && lake exe jacobianssite` renders _out/html-multi.
"""
import os, re, collections

REPO = 'https://github.com/rkirov/jacobian-claude'

src = open('scripts/unit_design.py').read()
exec(src.split('# cycle detection')[0])   # mods, deps, assign, units, uedges, META

loc = collections.Counter()
for m, p in mods.items():
    loc[assign[m]] += sum(1 for _ in open(p))

# longest-path layer for chapter ordering (foundations first)
layer = {}
def depth(u):
    if u in layer: return layer[u]
    layer[u] = 1 + max((depth(v) for v in uedges.get(u, ())), default=-1)
    return layer[u]
for u in units: depth(u)
order = sorted(units, key=lambda u: (layer[u], u))


decl_rx_tpl = (r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:protected\s+)?'
               r'(?:theorem|def|structure|abbrev|instance|inductive)\s+(?:[\w\u00ab\u00bb.]*\.)?%s(?![\w.])')

def find_decl_statement(short, files):
    """Locate declaration `short` in member files; return (path, line, header-text) with the
    header cut at the body marker (`:=` / `where` / trailing `by`)."""
    rx = re.compile(decl_rx_tpl % re.escape(short))
    opens, closes = '([{\u27e8', ')]}\u27e9'
    for p in files:
        lines = open(p).read().split('\n')
        for i, l in enumerate(lines):
            if rx.match(l):
                block, depth = [], 0
                for j in range(i, min(i + 24, len(lines))):
                    s, cut = lines[j], None
                    for k in range(len(s)):
                        c = s[k]
                        if c in opens: depth += 1
                        elif c in closes: depth -= 1
                        elif depth == 0 and s[k:k + 2] == ':=':
                            cut = k
                            break
                    if cut is not None:
                        block.append(s[:cut].rstrip())
                        return p, i + 1, '\n'.join(b for b in block if b.strip())
                    block.append(s)
                    if depth == 0 and s.rstrip().endswith((' where', ' by')):
                        return p, i + 1, '\n'.join(block)
                return p, i + 1, '\n'.join(block)
    return None

def lean_str(s):
    return s.replace('\\', '\\\\').replace('"', '\\"')

def md_escape(s):
    return s.replace('{', '\\{').replace('}', '\\}')

os.makedirs('site/Site', exist_ok=True)
chapters = []
for u in order:
    dirname, desc, keys = META[u]
    mem = sorted(units[u])
    deps_u = sorted(uedges.get(u, ()))
    title = u.replace('-', ' ')
    lines = [f'import VersoManual', '', 'open Verso.Genre Manual', '',
             f'#doc (Manual) "{lean_str(title)}" =>', '']
    lines.append(md_escape(desc))
    lines.append('')
    lines.append(f'*{len(mem)} modules, {loc[u]:,} lines, under `Jacobians/{dirname}/`.*')
    lines.append('')
    if unit_refs.get(u):
        lines.append('*References: ' + ' \u00b7 '.join(unit_refs[u]) + '.*')
        lines.append('')
    lines.append('# Keystones')
    lines.append('')
    memfiles = [mods[m] for m in mem]
    for k in keys:
        m_id = re.match(r'^([A-Za-z_][\w.]*)', k)
        found = find_decl_statement(m_id.group(1).split('.')[-1], memfiles) if m_id else None
        if found:
            p, ln, stmt = found
            lines.append(f'**`{k}`** — [source]({REPO}/blob/main/{p}#L{ln})')
            lines.append('')
            lines.append('```')
            lines.append(stmt)
            lines.append('```')
        else:
            lines.append(f'* `{k}`')
        lines.append('')
    if deps_u:
        lines.append('# Builds on')
        lines.append('')
        for v in deps_u:
            lines.append(f'* {v.replace("-", " ")}')
        lines.append('')
    lines.append('# Modules')
    lines.append('')
    for m in mem:
        path = mods[m]
        lines.append(f'* [`{m}`]({REPO}/blob/main/{path})')
    lines.append('')
    open(f'site/Site/{dirname}.lean', 'w').write('\n'.join(lines))
    chapters.append(dirname)

root = ['import VersoManual'] + [f'import Site.{c}' for c in chapters] + ['',
    'open Verso.Genre Manual', '',
    '#doc (Manual) "The Jacobians Challenge, by unit" =>', '',
    'A machine-checked solution of Kevin Buzzard\'s Jacobians challenge: genus,',
    'the genus-0 sphere theorem, Riemann–Roch, Abel\'s theorem, and the Jacobian',
    f'as a complex torus. [Source]({REPO}) · [unit dependency graph](../units.html).', '',
    'Chapters are the 30 units of the decomposition, ordered foundations-first;',
    'each unit page is generated from the unit docstring in the repository, so the',
    'source of truth stays in code.', '']
for c in chapters:
    root.append('{include 0 Site.' + c + '}')
root.append('')
open('site/Site.lean', 'w').write('\n'.join(root))

open('site/Main.lean', 'w').write('''import VersoManual
import Site

open Verso.Genre Manual

def main := manualMain (%doc Site) (config := {
  emitHtmlSingle := .no,
  emitHtmlMulti := .immediately,
  htmlDepth := 1,
  sourceLink := some "REPO",
  issueLink := some "REPO/issues"
})
'''.replace('REPO', REPO))
print(f"generated site/Site.lean + {len(chapters)} chapters")

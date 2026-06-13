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


from urllib.parse import quote

def issue_url(decl, path, line):
    """Prefilled GitHub new-issue link for a specific declaration (Bridgeland-style)."""
    title = quote(f'Issue with `{decl}`')
    body = quote(f'Concerning the statement or proof of `{decl}`\n'
                 f'({REPO}/blob/main/{path}#L{line}).\n\nDescribe the problem:\n')
    return f'{REPO}/issues/new?title={title}&body={body}'

DECL_HEAD = re.compile(
    r'^(?:noncomputable\s+)?(?:protected\s+)?'
    r'(theorem|def|lemma|structure|abbrev|instance|inductive)\s+([\w\u00ab\u00bb.]+)')

def module_public_decls(path):
    """All public declarations of a module: (name, docstring, statement-header)."""
    lines = open(path).read().split('\n')
    opens, closes = '([{\u27e8', ')]}\u27e9'
    out, i, comment = [], 0, 0
    while i < len(lines):
        l = lines[i]
        if comment > 0:
            comment += l.count('/-') - l.count('-/')
            i += 1
            continue
        comment += l.count('/-') - l.count('-/')
        if comment > 0 or l.startswith('private '):
            i += 1
            continue
        m = DECL_HEAD.match(re.sub(r'^@\[[^\]]*\]\s*', '', l))
        if not m or l.startswith(('--', '/-', ' ')):
            i += 1
            continue
        doc = []
        j = i - 1
        while j >= 0 and lines[j].startswith('@['):
            j -= 1
        if j >= 0 and lines[j].rstrip().endswith('-/'):
            k = j
            while k >= 0 and not lines[k].lstrip().startswith('/--'):
                k -= 1
            if k >= 0:
                doc = lines[k:j + 1]
        block, depth, end = [], 0, i
        for j2 in range(i, min(i + 24, len(lines))):
            s, cut = lines[j2], None
            for k2 in range(len(s)):
                c = s[k2]
                if c in opens: depth += 1
                elif c in closes: depth -= 1
                elif depth == 0 and s[k2:k2 + 2] == ':=':
                    cut = k2
                    break
            if cut is not None:
                block.append(s[:cut].rstrip())
                end = j2
                break
            block.append(s)
            end = j2
            if depth == 0 and s.rstrip().endswith((' where', ' by')):
                break
        doctext = re.sub(r'^\s*/--\s?', '', '\n'.join(doc))
        doctext = re.sub(r'\s*-/\s*$', '', doctext)
        out.append((m.group(2), doctext.strip(), '\n'.join(b for b in block if b.strip())))
        i = end + 1
    return out

def lean_str(s):
    return s.replace('\\', '\\\\').replace('"', '\\"')

def md_escape(s):
    """Render docstring text as inert Verso prose: keep backtick code spans, convert
    list bullets to dashes, strip bold markers, escape other markup characters."""
    out_lines = []
    for line in s.split('\n'):
        if line.lstrip().startswith('```'):
            continue
        line = re.sub(r'^(\s*)\* ', r'\1- ', line)
        parts = re.split(r'(`[^`]*`)', line)
        for i, part in enumerate(parts):
            if i % 2 == 0:
                part = part.replace('**', '')
                for c in '*_[]{}':
                    part = part.replace(c, '\\' + c)
                parts[i] = part
        out_lines.append(''.join(parts))
    return '\n'.join(out_lines)

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
            lines.append(f'**`{k}`** — [source]({REPO}/blob/main/{p}#L{ln}) · '
                         f'[report an issue]({issue_url(k, p, ln)})')
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
    for m in mem:
        path = mods[m]
        lines.append(f'# {m}')
        lines.append('')
        lines.append(f'`Jacobians.{m}` — [source]({REPO}/blob/main/{path})')
        lines.append('')
        for name, doc, stmt in module_public_decls(path):
            lines.append(f'**`{name}`**')
            lines.append('')
            if doc:
                lines.append(md_escape(doc))
                lines.append('')
            lines.append('```')
            lines.append(stmt)
            lines.append('```')
            lines.append('')
    lines.append('')
    open(f'site/Site/{dirname}.lean', 'w').write('\n'.join(lines))
    chapters.append(dirname)

# the conformance/validation chapter (generated separately) leads the book.
root = ['import VersoManual', 'import Site.Conformance'] \
    + [f'import Site.{c}' for c in chapters] + ['',
    'open Verso.Genre Manual', '',
    '#doc (Manual) "A machine-checked solution to the Jacobians challenge" =>', '',
    'This site documents a complete, machine-checked solution to Kevin Buzzard\'s',
    f'[Jacobians challenge]({REPO}/blob/main/Jacobian_challenge.lean) — an API for the',
    'Jacobian of a compact Riemann surface, formalized in Lean 4 on top of Mathlib. The',
    'mathematics (genus, the genus-0 sphere theorem, Riemann–Roch, Abel\'s theorem, the',
    'Jacobian as a complex torus) is written by AI agents under human direction; nothing',
    'is taken on trust — every statement is checked by the Lean kernel.', '',
    '# How to validate this solution', '',
    'The challenge ships as a list of definitions and theorems left as `sorry`. A solution',
    'must replace every `sorry` with a real, axiom-free proof of the *exact* statement asked',
    'for — no weakened hypotheses, no renamed goals. Two artifacts let you confirm that:', '',
    f'* The **conformance table** (first chapter below) restates each of Buzzard\'s'
    f' signatures verbatim and discharges it with our declaration. It is checked by'
    f' `lake env lean ChallengeConformance.lean`.',
    f'* The unit chapters below decompose the proof into self-contained pieces, each linking'
    f' to its source so you can read the actual argument.', '',
    f'[Source repository]({REPO}) · [verbatim spec]({REPO}/blob/main/Jacobian_challenge.lean)'
    f' · [axiom check]({REPO}/blob/main/AxiomCheck.lean) · [unit dependency graph](docs/units.html).', '',
    'Chapters are the 30 units of the decomposition, ordered foundations-first; each unit',
    'page is generated from the unit docstring in the repository, so the source of truth',
    'stays in code.', '',
    '{include 0 Site.Conformance}', '']
for c in chapters:
    root.append('{include 0 Site.' + c + '}')
root.append('')
open('site/Site.lean', 'w').write('\n'.join(root))

# Custom theme: Verso is entirely CSS-variable driven, and `extraHead` is rendered
# last in <head> (after book.css), so this <style> wins the cascade. Tightens
# typography, widens the column for long Lean signatures, and gives code blocks and
# section headings a clean "comparator manual" look.
THEME_CSS = r'''
:root {
  --verso-content-max-width: 52rem;
  --verso-font-size: 17px;
  --verso-text-font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", "Inter", Roboto, Helvetica, Arial, sans-serif;
  --verso-structure-font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", "Inter", Roboto, Helvetica, Arial, sans-serif;
  --verso-code-font-family: "JetBrains Mono", "SFMono-Regular", "Menlo", "Consolas", monospace;
  --verso-text-color: #1b1f24;
  --verso-structure-color: #0d1117;
  --jac-accent: #4f46e5;
  --jac-rule: #e6e8eb;
  --jac-code-bg: #f6f8fa;
}
body { line-height: 1.65; }
a { color: var(--jac-accent); text-decoration: none; }
a:hover { text-decoration: underline; }
h1, h2, h3, h4 { letter-spacing: -0.012em; line-height: 1.25; }
.content-wrapper h2 {
  margin-top: 2.2rem; padding-bottom: 0.3rem;
  border-bottom: 1px solid var(--jac-rule);
}
.content-wrapper h3 { margin-top: 1.6rem; }
/* Lean signatures: crisp card, horizontal scroll instead of ugly wraps */
pre {
  background: var(--jac-code-bg);
  border: 1px solid var(--jac-rule);
  border-radius: 8px;
  padding: 0.85rem 1rem;
  overflow-x: auto;
  font-size: 0.86em;
  line-height: 1.5;
}
:not(pre) > code {
  background: var(--jac-code-bg);
  border: 1px solid var(--jac-rule);
  border-radius: 5px;
  padding: 0.08em 0.34em;
  font-size: 0.9em;
}
/* Title / landing hero */
.titlepage h1 {
  font-size: 2.5rem; font-weight: 800;
  border-bottom: 3px solid var(--jac-accent);
  padding-bottom: 0.6rem; margin-bottom: 0.4rem;
}
.titlepage .authors { color: #57606a; }
/* Table of contents accent */
nav#toc .split-toc .title > a:hover { color: var(--jac-accent); }
header { border-bottom: 1px solid var(--jac-rule); }
'''

main_tpl = '''import VersoManual
import Site

open Verso.Genre Manual

/-- Injected verbatim into every page's `<head>` (after `book.css`). -/
def jacobianTheme : String := JAC_CSS_LIT

def main := manualMain (%doc Site) (config := {
  emitHtmlSingle := .no,
  emitHtmlMulti := .immediately,
  htmlDepth := 2,
  sourceLink := some "REPO",
  issueLink := some "REPO/issues",
  extraHead := #[Verso.Output.Html.tag "style" #[] (Verso.Output.Html.text false jacobianTheme)]
})
'''
# embed the CSS as a Lean raw string literal that won't collide with `"#`
css_lit = 'r##"' + THEME_CSS + '"##'
open('site/Main.lean', 'w').write(
    main_tpl.replace('JAC_CSS_LIT', css_lit).replace('REPO', REPO))

# the conformance/validation chapter is generated from the challenge spec + the
# machine-check file; keep it in lock-step with the rest of the site.
os.system('python3 scripts/generate_conformance_page.py')
print(f"generated site/Site.lean + Conformance + {len(chapters)} chapters")

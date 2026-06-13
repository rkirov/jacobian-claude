#!/usr/bin/env python3
"""Generate the conformance/validation chapter for the Verso site.

Source of truth:
  * `Jacobian_challenge.lean`   — Kevin Buzzard's verbatim v0.4 spec (every item a
                                  `sorry` stub, with its docstring/description).
  * `ChallengeConformance.lean` — one `example` per spec item restating Buzzard's
                                  *exact* signature and discharging it with our
                                  declaration. This file compiling green is the
                                  machine-check that the formalization conforms.

For each item we emit, verbatim, the conformance `example` (Buzzard's required type
on the left of `:=`, our discharging declaration on the right), Buzzard's prose
description, and links to the submission surface (`Jacobians.lean`), the spec line,
and the machine-check line — so a human can spot-check that the Lean statement
really says what the challenge asked.

Writes `site/Site/Conformance.lean`. Run from the repo root.
"""
import os, re

REPO = 'https://github.com/rkirov/jacobian-claude'
SPEC = 'Jacobian_challenge.lean'
CONF = 'ChallengeConformance.lean'


def blob(path, line):
    return f'{REPO}/blob/main/{path}#L{line}'


# ---- spec: name -> (description, spec line) ----------------------------------
spec_src = open(SPEC).read().split('\n')
spec_desc, spec_line = {}, {}
doc_re = re.compile(r'/--(.*?)-/', re.S)
decl_re = re.compile(r'^\s*(?:noncomputable\s+|universe \w+ in\s*)?'
                     r'(?:def|lemma|theorem|instance)\s+(_root_\.[\w.]+|[\w.]+)?')
# accumulate the most recent docstring / `-- comment` as the description
pending_doc = ''
for i, line in enumerate(spec_src):
    ds = re.search(r'/--(.*)', line)
    if '/--' in line:
        # gather possibly-multiline docstring
        j, buf = i, []
        while j < len(spec_src):
            buf.append(spec_src[j]);
            if '-/' in spec_src[j]:
                break
            j += 1
        m = doc_re.search('\n'.join(buf))
        if m:
            pending_doc = re.sub(r'\s+', ' ', m.group(1)).strip()
        continue
    cm = re.match(r'^\s*--\s*(.+)', line)
    if cm and 'let X' not in line and 'this is' not in line and 'this proof' not in line \
            and 'functoriality' not in line and 'data' != cm.group(1).strip() \
            and 'Prop' != cm.group(1).strip() and 'pushforward is' not in line \
            and 'pullback is' not in line:
        pending_doc = pending_doc  # keep docstring priority; ignore noise comments
    d = decl_re.match(line)
    if d and d.group(1):
        name = d.group(1).replace('_root_.', '')
        for key in {name, name.split('.')[-1]}:   # also index the short name (degree)
            spec_desc.setdefault(key, pending_doc)
            spec_line.setdefault(key, i + 1)
        pending_doc = ''


# ---- submission surface: name -> (file, line) --------------------------------
# Prefer the challenge-facing definitions in Jacobians.lean (the final
# `namespace Jacobian` block); fall back to the wider tree for genus / degree.
surface = {}
surf_decl = re.compile(r'^\s*(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev|instance)\s+'
                       r'(_root_\.[\w.]+|[\w.]+)')
inst_re = re.compile(r'^\s*(?:noncomputable\s+)?instance\s*:\s*([A-Z]\w+).*\(Jacobian X\)')
for i, line in enumerate(open('Jacobians.lean'), 1):
    m = surf_decl.match(line)
    if m and m.group(1):
        nm = m.group(1).replace('_root_.', '').split('.')[-1]
        surface[nm] = ('Jacobians.lean', i)   # last occurrence wins → the shim block
    im = inst_re.match(line)
    if im:
        surface[im.group(1)] = ('Jacobians.lean', i)  # the seven Jacobian instances
for root, _, files in os.walk('Jacobians'):
    for fn in files:
        if fn.endswith('.lean'):
            p = os.path.join(root, fn)
            for i, line in enumerate(open(p), 1):
                m = surf_decl.match(line)
                if m and m.group(1):
                    nm = m.group(1).replace('_root_.', '').split('.')[-1]
                    surface.setdefault(nm, (p, i))


# ---- conformance: ordered (example block, discharge name) --------------------
conf_src = open(CONF).read().split('\n')
items = []          # (name, kind, example_text, conf_line)
i = 0
INSTANCE_DESC = {
    'AddCommGroup': 'The Jacobian is naturally an additive commutative group.',
    'TopologicalSpace': 'The Jacobian is naturally a topological space.',
    'T2Space': 'The Jacobian is Hausdorff.',
    'CompactSpace': 'The Jacobian is compact.',
    'ChartedSpace': 'The Jacobian is a complex manifold of dimension equal to the genus.',
    'IsManifold': 'The Jacobian is a complex manifold.',
    'LieAddGroup': 'The Jacobian is a complex Lie group.',
}
while i < len(conf_src):
    if conf_src[i].startswith('example'):
        # gather the whole example — binders, type and body — up to the next blank
        # line, comment, or top-level keyword (handles `:=` at end of line with the
        # discharging term on the following line).
        block, j = [conf_src[i]], i
        while j + 1 < len(conf_src):
            nxt = conf_src[j + 1]
            if nxt.strip() == '' or re.match(r'^(example|variable|namespace|end|--)', nxt):
                break
            j += 1
            block.append(nxt)
        text = '\n'.join(block).rstrip()
        # discharge term = first identifier after the final `:=`
        rhs = text.split(':=')[-1].strip()
        head = re.match(r'(?:by\s+apply\s+)?([\w.]+)', rhs)
        term = head.group(1) if head else rhs
        if term == 'inferInstance':
            # name by the typeclass head of the example's type
            tc = re.search(r':\s*([A-Z]\w+)', text)
            name = tc.group(1) if tc else 'instance'
            kind = 'instance'
        else:
            name = term.split('.')[-1]
            kind = 'def' if name in ('genus', 'Jacobian', 'ofCurve', 'pushforward',
                                     'pullback', 'degree') else 'theorem'
        items.append((name, kind, text, i + 1))
        i = j + 1
    else:
        i += 1


# ---- emit Verso chapter ------------------------------------------------------
def lean_str(s):
    return s.replace('\\', '\\\\').replace('"', '\\"')


out = ['import VersoManual', '', 'open Verso.Genre Manual', '',
       '#doc (Manual) "Conformance: Buzzard’s spec vs. this formalization" =>', '']

out += [
    f"Kevin Buzzard’s challenge ([`{SPEC}`]({blob(SPEC, 40)})) lists {len(items)} "
    "definitions, instances and theorems as `sorry` stubs — the API a solution must "
    "provide, with exact names and types. This repository supplies real declarations for "
    "every one.", '',
    f"[`{CONF}`]({blob(CONF, 1)}) is the machine-check: each item below is an `example` "
    "that restates Buzzard’s **verbatim** signature and discharges it with our "
    "declaration. The file compiles with no errors, no `sorry`, and "
    f"[axiom-clean]({blob('AxiomCheck.lean', 1)}) — so the table is not a claim, it is "
    "checked by the Lean kernel.", '',
    "To validate an item yourself: read Buzzard’s required type (left of `:=`), confirm "
    "it matches the spec, then follow the **submission surface** link into "
    "`Jacobians.lean` and on into the proof. Every row links the spec, the check, and our "
    "code.", '',
    "*Reproduce the check: `lake env lean ChallengeConformance.lean` (expects no output).*", '',
]

groups = [('def', 'Definitions'), ('instance', 'Instances on the Jacobian'),
          ('theorem', 'Theorems & lemmas')]
for kind, title in groups:
    rows = [it for it in items if it[1] == kind]
    if not rows:
        continue
    out += [f'# {title}', '']
    for name, _k, text, cline in rows:
        desc = spec_desc.get(name) or INSTANCE_DESC.get(name) or ''
        links = [f'[machine-check]({blob(CONF, cline)})']
        if name in surface:
            f, ln = surface[name]
            links.insert(0, f'[submission surface]({blob(f, ln)})')
        if name in spec_line:
            links.append(f'[spec]({blob(SPEC, spec_line[name])})')
        out += [f'## `{name}`', '']
        if desc:
            out += [f'*{desc}*', '']
        out += ['```', text, '```', '', ' · '.join(links), '']

open('site/Site/Conformance.lean', 'w').write('\n'.join(out))
print(f'generated site/Site/Conformance.lean: {len(items)} conformance items')
for name, kind, _t, _l in items:
    print(f'  [{kind:8}] {name:28} surface={surface.get(name, ("?",))[0]}')

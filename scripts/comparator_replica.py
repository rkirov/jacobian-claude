#!/usr/bin/env python3
"""Local replica of the lean-eval comparator's statement check (the failure class we have
actually hit, four times). Elaborates the 24 `JacobianChallenge.*` declarations twice —

  challenge env : Jacobian_challenge.lean verbatim (import Mathlib, sorry bodies)
  solution env  : the same declaration text with SubmissionShimTest.lean inlined first and
                  the six data declarations + seven instances delegated to the shim with the
                  challenge's exact explicit arguments (theorem bodies stay `sorry`: a
                  theorem's body cannot affect any compared statement, and the challenge's
                  own bodies are sorries)

— prints each declaration's `pp.all` type + universe params, and diffs. A mismatch is what
the real comparator rejects ("statement do not match"). This does NOT replicate the
export/kernel stage; use a real lean-eval submission for the authoritative verdict.

Run from the repo root after `lake build` (needs Jacobians + Mathlib oleans):
  python3 scripts/comparator_replica.py
"""
import os, re, subprocess, sys, tempfile

CHALLENGE = open('scripts/lean_eval_problem.lean').read()
SHIM = open('SubmissionShimTest.lean').read()

# the 24 compared declarations, in challenge order, with the delegation shape for data
# declarations (None = theorem/Prop: keep `sorry`). The challenge file is frozen, so the
# explicit-argument lists are stable.
DECLS = [
    ('JacobianChallenge.genus',                       'genus X'),
    ('JacobianChallenge.genus_eq_zero_iff_homeo',     None),
    ('JacobianChallenge.Jacobian',                    'Jacobian X'),
    ('JacobianChallenge.Jacobian.instAddCommGroup',   'Jacobian.instAddCommGroup'),
    ('JacobianChallenge.Jacobian.instTopologicalSpace', 'Jacobian.instTopologicalSpace'),
    ('JacobianChallenge.Jacobian.instT2Space',        'Jacobian.instT2Space'),
    ('JacobianChallenge.Jacobian.instCompactSpace',   'Jacobian.instCompactSpace'),
    ('JacobianChallenge.Jacobian.instChartedSpace',   'Jacobian.instChartedSpace'),
    ('JacobianChallenge.Jacobian.instIsManifold',     'Jacobian.instIsManifold'),
    ('JacobianChallenge.Jacobian.instLieAddGroup',    'Jacobian.instLieAddGroup'),
    ('JacobianChallenge.Jacobian.ofCurve',            'Jacobian.ofCurve P'),
    ('JacobianChallenge.Jacobian.ofCurve_contMDiff',  None),
    ('JacobianChallenge.Jacobian.ofCurve_self',       None),
    ('JacobianChallenge.Jacobian.ofCurve_inj',        None),
    ('JacobianChallenge.Jacobian.pushforward',        'Jacobian.pushforward f hf'),
    ('JacobianChallenge.Jacobian.pushforward_contMDiff', None),
    ('JacobianChallenge.Jacobian.pushforward_id_apply', None),
    ('JacobianChallenge.Jacobian.pushforward_comp_apply', None),
    ('JacobianChallenge.Jacobian.pullback',           'Jacobian.pullback f hf'),
    ('JacobianChallenge.Jacobian.pullback_contMDiff', None),
    ('JacobianChallenge.Jacobian.pullback_id_apply',  None),
    ('JacobianChallenge.Jacobian.pullback_comp_apply', None),
    ('JacobianChallenge.Jacobian.degree',             'Jacobian.degree f hf'),
    ('JacobianChallenge.Jacobian.pushforward_pullback', None),
]

PRINTER = '''
section ComparatorReplicaPrinter
open Lean in
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let names : List Lean.Name := [{names}]
  for n in names do
    match env.find? n with
    | none => IO.println s!"### {{n}}\\nMISSING"
    | some ci =>
      let fmt ← Lean.Meta.MetaM.run' (ctx := {{}}) (s := {{}}) do
        Lean.withOptions (fun o => (o.setBool `pp.all true).setBool `pp.fullNames true) do
          Lean.Meta.ppExpr ci.type
      IO.println s!"### {{n}} {{ci.levelParams}}"
      IO.println (fmt.pretty 200)
end ComparatorReplicaPrinter
'''.format(names=', '.join(f'`{n}' for n, _ in DECLS))

def delegated_challenge_text():
    """Replace the i-th `sorry` (one per declaration, in order) with the shim delegation
    for data declarations; keep `sorry` for theorems."""
    parts = re.split(r'\bsorry\b', CHALLENGE)
    assert len(parts) == len(DECLS) + 1, \
        f"challenge sorry count {len(parts)-1} != {len(DECLS)} declarations"
    out = [parts[0]]
    for (name, deleg), tail in zip(DECLS, parts[1:]):
        if deleg:
            head = deleg.split()[0]
            body = f'Submission.JacobianChallenge.{head}' + \
                ''.join(' ' + a for a in deleg.split()[1:])
        else:
            body = 'sorry'
        out.append(body)
        out.append(tail)
    text = ''.join(out)
    # delegations to noncomputable shim defs need the keyword (lean-eval PR #422 behavior);
    # statements (types) are unaffected.
    for name, deleg in DECLS:
        if not deleg:
            continue
        short = name.split('.')[-1]
        for kw in ('def', 'instance'):
            text = text.replace(f'\n{kw} {short} ', f'\nnoncomputable {kw} {short} ', 1)
            text = text.replace(f'\n{kw} {short}\n', f'\nnoncomputable {kw} {short}\n', 1)
    return text

def run_env(tag, text):
    path = os.path.join(tempfile.mkdtemp(), f'replica_{tag}.lean')
    open(path, 'w').write(text)
    r = subprocess.run(['lake', 'env', 'lean', path], capture_output=True, text=True)
    # `sorry` warnings are expected; errors are not
    errs = [l for l in (r.stdout + r.stderr).splitlines() if 'error' in l.lower()]
    if r.returncode != 0 or errs:
        print(f"[{tag}] elaboration FAILED:")
        print('\n'.join((r.stdout + r.stderr).splitlines()[:40]))
        sys.exit(1)
    blocks = {}
    cur = None
    for line in r.stdout.splitlines():
        if line.startswith('### '):
            cur = line[4:]
            blocks[cur] = []
        elif cur is not None:
            blocks[cur].append(line)
    return {k.split()[0]: (k, '\n'.join(v).strip()) for k, v in blocks.items()}

# challenge side: verbatim + printer
chal = run_env('challenge', CHALLENGE + PRINTER)
print(f"[challenge] {len(chal)} statements elaborated")

# solution side: shim imports + shim body + delegated challenge + printer
shim_imports = '\n'.join(l for l in SHIM.splitlines() if l.startswith('import '))
shim_body = '\n'.join(l for l in SHIM.splitlines() if not l.startswith('import '))
chal_delegated = '\n'.join(l for l in delegated_challenge_text().splitlines()
                           if not l.startswith('import '))
sol_text = 'import Mathlib\n' + shim_imports + '\n' + shim_body \
    + '\n' + chal_delegated + PRINTER
sol = run_env('solution', sol_text)
print(f"[solution]  {len(sol)} statements elaborated")

bad = 0
for n, _ in DECLS:
    ch, so = chal.get(n), sol.get(n)
    if ch is None or so is None:
        print(f"MISSING {n}: challenge={ch is not None} solution={so is not None}")
        bad += 1
    elif ch[1] != so[1] or ch[0] != so[0]:
        bad += 1
        print(f"STATEMENT MISMATCH: {n}")
        print(f"  challenge: {ch[0]}\n{ch[1]}")
        print(f"  solution:  {so[0]}\n{so[1]}")
if bad:
    print(f"\n{bad}/{len(DECLS)} statements differ — the comparator would REJECT this.")
    sys.exit(1)
print(f"\nall {len(DECLS)} statements identical — comparator statement check would pass")

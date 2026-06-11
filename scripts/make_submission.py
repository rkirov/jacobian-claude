#!/usr/bin/env python3
"""Generate the lean-eval leaderboard submission workspace for jacobian_challenge_diffgeo.

Layout (committed in-repo; the lean-eval CI walks the repo, matches the lakefile name,
and overlays ONLY Submission.lean + Submission/** onto its pristine problem workspace):

  submission/jacobian_challenge_diffgeo/
    lakefile.toml        (name = problem id; content otherwise unused by the CI)
    Submission.lean      (JacobianChallenge-namespace shim, mirrors the problem file)
    Submission/**        (the whole Jacobians library, imports rewritten)

The shim body is sourced from SubmissionShimTest.lean (kept in-repo, validated against
our own pins by `lake env lean SubmissionShimTest.lean`).
Run from the repo root: python3 scripts/make_submission.py
Check staleness (CI-able, exits 1 if the committed copy differs from a fresh
generation): python3 scripts/make_submission.py --check
"""
import os, re, shutil, sys, filecmp

CHECK = '--check' in sys.argv
REAL = 'submission/jacobian_challenge_diffgeo'
DST = '/tmp/jacobian_submission_check' if CHECK else REAL
shutil.rmtree(DST, ignore_errors=True)
os.makedirs(f'{DST}/Submission', exist_ok=True)

imp = re.compile(r'^import Jacobians(?=[.\s])', re.M)

def rewrite(text):
    return imp.sub(lambda m: 'import Submission', text)

n = 0
for root, _, files in os.walk('Jacobians'):
    for f in files:
        if not f.endswith('.lean'):
            continue
        src = os.path.join(root, f)
        dst = os.path.join(DST, 'Submission', os.path.relpath(src, 'Jacobians'))
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with open(src) as fh:
            open(dst, 'w').write(rewrite(fh.read()))
        n += 1

# the old root library file becomes Submission/Root.lean
root_text = rewrite(open('Jacobians.lean').read()).replace(
    'import Jacobians\n', 'import Submission.Root\n')  # (no self-import exists; safety)
open(f'{DST}/Submission/Root.lean', 'w').write(root_text)

# Submission.lean = header + Root import + the validated shim body
shim = open('SubmissionShimTest.lean').read()
shim = shim.split('import Jacobians\n', 1)[1]
header = (
    "/-\nSubmission for the lean-eval problem `jacobian_challenge_diffgeo`\n"
    "(Kevin Buzzard's Jacobian challenge). The full development lives under\n"
    "`Submission/` (root module `Submission.Root`); this file provides the\n"
    "challenge declarations in the problem file's `JacobianChallenge` namespace,\n"
    "each delegating to the proven development. Sorry-free; axioms:\n"
    "[propext, Classical.choice, Quot.sound].\n-/\n"
    "import Submission.Root\n")
open(f'{DST}/Submission.lean', 'w').write(header + shim)

open(f'{DST}/lakefile.toml', 'w').write(
    'name = "jacobian_challenge_diffgeo"\n'
    'defaultTargets = ["Submission"]\n\n'
    '[[lean_lib]]\nname = "Submission"\n')

if CHECK:
    # the committed copy lives on the derived `submission` branch, not main
    if not os.path.isdir(REAL):
        import subprocess, tempfile
        tmp = tempfile.mkdtemp(prefix='subm_branch_')
        tar = subprocess.run(['git', 'archive', 'submission', REAL],
                             capture_output=True, check=True).stdout
        subprocess.run(['tar', '-x', '-C', tmp], input=tar, check=True)
        REAL = os.path.join(tmp, REAL)
    cmp = filecmp.dircmp(REAL, DST)
    def stale(c):
        return c.left_only or c.right_only or c.diff_files or any(
            stale(sub) for sub in c.subdirs.values())
    if stale(cmp):
        print("STALE: the submission branch's workspace differs from a fresh generation — "
              "rerun scripts/update_submission_branch.sh")
        sys.exit(1)
    print("submission/ is up to date with Jacobians/**")
else:
    print(f"wrote {n} library modules + Root + Submission.lean + lakefile.toml -> {DST}")

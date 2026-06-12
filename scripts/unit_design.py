#!/usr/bin/env python3
"""Unit decomposition proposal: assign all modules to ~35 chapter-units via ordered
pattern rules, compute the induced unit dependency graph from real imports, and report
cycles / heavy edges. Emits docs/UNITS_PROPOSAL.md. Run from repo root."""
import os, re, collections

# ---- ordered (regex, unit) rules; first match wins. Paths relative to Jacobians/. ----
RULES = [
    # After the M1 migration, directory = unit. Umbrella files (Jacobians/<Dir>.lean)
    # belong to their unit via the optional-suffix pattern.
    (r'^Surface(\..*)?$', 'surfaces-and-charts'),
    (r'^ProjectiveLine$', 'projective-line'),
    (r'^Meromorphic(\..*)?$', 'meromorphic-and-divisors'),
    (r'^Forms(\..*)?$', 'holomorphic-forms'),
    (r'^Path(\..*)?$', 'paths-and-integrals'),
    (r'^LocalMultiplicity(\..*)?$', 'local-multiplicity'),
    (r'^MappingDegree(\..*)?$', 'mapping-degree'),
    (r'^ProperDegree(\..*)?$', 'proper-map-degree'),
    (r'^MeromorphicTrace(\..*)?$', 'meromorphic-trace'),
    (r'^FormTraceSheetCovector$', 'form-trace-tower'),
    (r'^Cech(\..*)?$', 'cech-cohomology'),
    (r'^Finiteness(\..*)?$', 'finiteness-and-chi'),
    (r'^H1Genus(\..*)?$', 'cech-h1-genus'),
    (r'^Dbar(\..*)?$', 'dbar-solvability'),
    (r'^DolbeaultComparison(\..*)?$', 'dolbeault-comparison'),
    (r'^ResidueCalculus(\..*)?$', 'residue-calculus'),
    (r'^PlanarStokes(\..*)?$', 'planar-stokes-atoms'),
    (r'^ResidueTheorem(\..*)?$', 'residue-theorem'),
    (r'^CanonicalForms(\..*)?$', 'canonical-forms'),
    (r'^SerrePairing(\..*)?$', 'serre-duality-cech'),
    (r'^LaurentTail(\..*)?$', 'laurent-tails'),
    (r'^TailDuality(\..*)?$', 'serre-duality-tails'),
    (r'^RiemannRoch$', 'riemann-roch'),
    (r'^Monodromy(\..*)?$', 'monodromy'),
    (r'^SphereTopology(\..*)?$', 'sphere-topology'),
    (r'^GenusSphereHeadline$', 'genus-zero-headline'),
    (r'^AbelWeak(\..*)?$', 'abel-weak-solutions'),
    (r'^Abel(\..*)?$', 'abel-theorem'),
    (r'^JacobianConstruction(\..*)?$', 'jacobian-construction'),
    (r'^PeriodLattice(\..*)?$', 'period-lattice-rank'),
]

# ---- per-unit metadata: (proposed dir under Jacobians/, description, keystones) ----
META = {
    'surfaces-and-charts': ('Surface',
        'Riemann-surface foundations: charted spaces from local homeomorphisms, `ULift` '
        'transport of manifold structure, the holomorphic inverse function theorem on '
        'manifolds, and the underlying real 2-manifold of a Riemann surface.',
        ['ManifoldIFT (holomorphic IFT)', 'chartedSpace-of-localHomeomorph constructors']),
    'projective-line': ('ProjectiveLine',
        'The Riemann sphere `ℙ¹` as the model compact Riemann surface.',
        ['ProjectiveLine instances + genus ℙ¹ facts']),
    'meromorphic-and-divisors': ('Meromorphic',
        'Meromorphic functions as germ data, divisors (`Finsupp`), orders, linear systems '
        'and their dimension; Liouville and normal-form repair. (Migration: split the mixed '
        '`Abel.lean` into divisor foundations here vs the Abel–Jacobi map upstairs.)',
        ['MeromorphicFunction', 'Divisor', 'lDim / linearSystem']),
    'holomorphic-forms': ('Forms',
        'Global holomorphic 1-forms as a `ContMDiffSection` bundle, the genus as their '
        'dimension, and Montel-type compactness for form/function families.',
        ['HolomorphicOneForms', 'genus']),
    'paths-and-integrals': ('Path',
        'Smooth paths and loops, path line integrals of 1-forms, primitives along paths, '
        'and perturbing loops off a finite bad set.',
        ['SmoothPath', 'lineIntegral']),
    'local-multiplicity': ('LocalMultiplicity',
        'Local theory at a point: analytic local factorization `z^k·unit`, derivative '
        'orders, local multiplicity of a holomorphic map.',
        ['AnalyticLocalFactorization', 'LocalMultiplicity']),
    'mapping-degree': ('MappingDegree',
        'The mapping degree machine: regular values, critical-value finiteness, fibre '
        'counting, well-definedness of the degree (largest unit; contains the ported '
        'degree-well-definedness tree).',
        ['ContMDiff.degree well-definedness engine']),
    'proper-map-degree': ('ProperDegree',
        'Degree of a global meromorphic map: `ContMDiff.degree`, sheet counting, '
        'multiplicity patching, `deg (div f) = 0`, and degree-one maps to the sphere '
        'are homeomorphisms.',
        ['ContMDiff.degree', 'exists_properMapDegree', 'DegDivResidue (deg∘div = 0)',
         'DegreeOneSphere']),
    'meromorphic-trace': ('MeromorphicTrace',
        'Surface-level trace of meromorphic functions/forms along a degree-d map and the '
        'argument principle on `X` (zeros = poles for `div f = 0` log-derivative traces).',
        ['ResidueTheoremX.zerosCount_eq_polesCount_of_logDerivTrace',
         'residue change of variables']),
    'form-trace-tower': ('FormTrace',
        'The fibrewise trace tower for pair forms `h·ω₀` along a branched cover '
        '`f : X → ℙ¹`: fibre traces, branch handling, coherent selections, globalization '
        'and rationality of the traced form (the Gate-A reduction machinery).',
        ['FormTraceFibre', 'FormTraceGlobal* (traced form is rational)']),
    'residue-via-trace': ('ResidueViaTrace',
        'The residue theorem on `X` obtained through the trace: adapted functions, '
        'ramified fibre conservation, and `∑ Res = 0` at the Serre-pairing level.',
        ['residueTheorem_of_adaptedF', 'residueSum_of_adaptedF']),
    'cech-cohomology': ('Cech',
        'Čech theory for `𝒪_D`: junk-free germ cochains over `codiscreteWithin`, the '
        'complex, refinements, chart-disk covers, and `H⁰ = L(D)`.',
        ['CechH0.h0Dim_eq_lDim', 'CechComplex / MGerm cochains']),
    'finiteness-and-chi': ('Finiteness',
        'Finite-dimensionality of `H¹(X, 𝒪_D)` (Forster §14, Schwartz + Montel functional-'
        'analysis spine) and the Euler-characteristic / cohomological Riemann–Roch '
        'bookkeeping via skyscraper sequences.',
        ['finiteDimensional_cechH1', 'exists_cechModel', 'cohomological χ(D) ledger']),
    'cech-h1-genus': ('H1Genus',
        '`dim H¹(X, 𝒪) = g`: cup-product kill, monotonicity, and the effective-divisor '
        'vanishing comparison.',
        ['FiniteCover.h1Dim_zero_eq_genus']),
    'dbar-solvability': ('Dbar',
        'The intrinsic `∂̄` operator on the surface and its local solvability: the planar '
        'Dolbeault lemma on disks (Forster 13.2), disk acyclicity for the Čech complex, '
        'and holomorphic representatives of `∂̄`-closed germs.',
        ['RealForms.dbar', 'DbarOpenDisk.dbar_solvable_open_disk', 'CechDiskAcyclic']),
    'dolbeault-comparison': ('DolbeaultComparison',
        'The PDE-free comparison `Čech H¹(X, 𝒪) ≅ H^{0,1}_∂̄(X)`, local realization of '
        'cocycles, Mittag-Leffler gluing, and existence of Leray covers.',
        ['DolbeaultComparison (the iso)', 'LerayCoverExists']),
    'residue-calculus': ('ResidueCalculus',
        'Planar residue calculus: `resAt`, Laurent coefficients of pair integrands, and '
        'Mittag-Leffler distributions of principal parts.',
        ['resAt / FormCoeff', 'MittagLeffler']),
    'planar-stokes-atoms': ('PlanarStokes',
        'The planar integration atoms: compact-support Stokes in the plane, annulus '
        'residue integrals, holomorphic change of variables for contour integrals.',
        ['PlanarCompactSupportStokes', 'AnnulusResidueIntegral']),
    'residue-theorem': ('ResidueTheorem',
        'The unconditional residue theorem `∑_p Res_p(h·dg₀) = 0` for meromorphic pair '
        'forms on a compact surface, any genus, via partition of unity + planar Stokes.',
        ['residueSum_pairForm_eq_zero_unconditional']),
    'canonical-forms': ('CanonicalForms',
        'Meromorphic 1-form systems and the canonical divisor: removable singularities, '
        'differentials of canonical forms, and existence of a nonconstant meromorphic '
        'function / nonzero `ω₀` (via cohomological χ).',
        ['MeromorphicOneFormSystem', 'exists_nonconstant_meromorphic', 'SerreOmega0']),
    'serre-duality-cech': ('SerrePairing',
        'The Serre pairing interface at the Čech level: dimension-counting surjectivity '
        'core and the duality bookkeeping consumed by the Laurent-tail route.',
        ['serre_surjectivity_dim_core', 'SerreDualityData ladder']),
    'laurent-tails': ('LaurentTail',
        'Miranda Ch. VI Laurent-tail calculus: tail spaces, truncation maps, tail '
        'finiteness, and the first (tail) form of Riemann–Roch.',
        ['TailSpace', 'riemannRoch_tailForm']),
    'serre-duality-tails': ('TailDuality',
        'Serre duality through Laurent tails (Miranda VI.3): multiplication action on '
        'H¹-tails, surjectivity, the order downgrade, and `h¹(D) = l(K−D)`.',
        ['tail duality injectivity/surjectivity', 'Miranda Lemma 3.6 order downgrade']),
    'riemann-roch': ('RiemannRoch',
        'The Riemann–Roch theorem: `l(D) − l(K−D) = deg D + 1 − g` with the canonical '
        'divisor `K`, plus `deg K = 2g−2`, `l(K) = g`, and the single-simple-pole '
        'consequence for genus 0.',
        ['exists_riemannRoch_divisor']),
    'monodromy': ('Monodromy',
        'Global primitives on simply connected surfaces by discrete analytic continuation '
        'along chains (no integration): local primitive frames, chain values, homotopy '
        'invariance.',
        ['hasHolomorphicPrimitives']),
    'sphere-topology': ('SphereTopology',
        'Topology of the 2-sphere: Van Kampen, simple connectivity, and the backward '
        'headline direction (homeomorphic-to-sphere ⇒ genus 0).',
        ['SphereSimplyConnected', 'GenusZeroOfSphere']),
    'genus-zero-headline': ('GenusSphereHeadline',
        'The headline equivalence `genus X = 0 ↔ X ≃ₜ S²`, assembled from Riemann–Roch '
        '(forward) and sphere topology (backward).',
        ['genus_eq_zero_iff_homeo']),
    'abel-weak-solutions': ('AbelWeak',
        'Weak/planar solution steps for the Abel engine: chain decompositions and '
        'piecewise planar solutions.',
        ['AbelChains', 'AbelCurveSolution']),
    'abel-theorem': ('Abel',
        "Abel's theorem (Forster 20.7, dissection-free): the two-point Abel–Jacobi value "
        'is nonzero for distinct points on genus ≥ 1, hence `ofCurve` is injective.',
        ['abelJacobi_twoPoint_ne_zero']),
    'jacobian-construction': ('JacobianConstruction',
        'The Jacobian as a complex torus: the period lattice (ℤ-span of loop periods), '
        'period vectors, and the `ZLattice` quotient manifold machinery.',
        ['truePeriodLattice / periodVec', 'ZLatticeQuotient']),
    'period-lattice-rank': ('PeriodLattice',
        'The period lattice has a real basis of rank 2g (Forster 21.4, dissection-free): '
        'discreteness via the local Jacobi map, nondegeneracy, and the real basis.',
        ['exists_periodLattice_realBasis']),
}

imp = re.compile(r'^import (Jacobians[\w.]*)', re.M)
def modname(p): return p[:-5].replace('/', '.')

mods, deps = {}, {}
for root, _, files in os.walk('Jacobians'):
    for f in files:
        if f.endswith('.lean'):
            p = os.path.join(root, f)
            short = modname(p)[len('Jacobians.'):]
            mods[short] = p
            deps[short] = [d[len('Jacobians.'):] for d in imp.findall(open(p).read())
                           if d != 'Jacobians']

def unit_of(m):
    for pat, u in RULES:
        if re.match(pat, m): return u
    return 'UNASSIGNED'

assign = {m: unit_of(m) for m in mods}
units = collections.defaultdict(list)
for m, u in assign.items(): units[u].append(m)

# induced unit graph
uedges = collections.defaultdict(set)
for m, ds in deps.items():
    for d in ds:
        if d in assign and assign[d] != assign[m]:
            uedges[assign[m]].add(assign[d])

# cycle detection (simple DFS)
WHITE, GRAY, BLACK = 0, 1, 2
color = {u: WHITE for u in units}
cycles = []
def dfs(u, path):
    color[u] = GRAY; path.append(u)
    for v in uedges.get(u, ()):
        if color.get(v) == GRAY:
            cycles.append(path[path.index(v):] + [v])
        elif color.get(v) == WHITE:
            dfs(v, path)
    path.pop(); color[u] = BLACK
for u in list(units):
    if color[u] == WHITE: dfs(u, [])

# ---- strict-deps manifest: computed unit edges must be declared in advance ----
# docs/unit_dag_manifest.json holds the ALLOWED direct unit→unit edges. A new cross-unit
# import that induces an undeclared edge fails this script (and CI). To accept a new edge,
# rerun with --update-manifest and commit the diff — making the dependency reviewable.
import sys
MANIFEST = 'docs/unit_dag_manifest.json'
computed = sorted((a, b) for a in uedges for b in uedges[a])
if '--update-manifest' in sys.argv:
    import json as _json
    open(MANIFEST, 'w').write(_json.dumps({'edges': computed}, indent=1))
    print(f"manifest updated: {len(computed)} declared edges")
elif os.path.exists(MANIFEST):
    import json as _json
    declared = {tuple(e) for e in _json.load(open(MANIFEST))['edges']}
    bad = [e for e in computed if e not in declared]
    if bad:
        print(f"UNDECLARED unit edges ({len(bad)}) — declare via --update-manifest if intended:")
        for a, b in bad:
            print(f"  {a} -> {b}")
            for m, ds in deps.items():
                if assign[m] != a: continue
                for d in ds:
                    if d in assign and assign[d] == b:
                        print(f"      {m} imports {d}")
        sys.exit(1)

print(f"units: {len(units)}  modules: {len(mods)}  unassigned: {len(units.get('UNASSIGNED', []))}")
for m in units.get('UNASSIGNED', []): print("  UNASSIGNED:", m)
if cycles:
    print(f"CYCLES ({len(cycles)}):")
    for c in cycles[:10]: print("  " + " -> ".join(c))
else:
    print("unit graph is ACYCLIC")
# mutual (2-cycle) pairs with witness imports
pairs = set()
for a in uedges:
    for b in uedges[a]:
        if a in uedges.get(b, set()) and (b, a) not in pairs:
            pairs.add((a, b))
print(f"\nMUTUAL PAIRS ({len(pairs)}):")
for a, b in sorted(pairs):
    print(f"  {a} <-> {b}")
    shown = 0
    for m, ds in deps.items():
        for d in ds:
            if d in assign and ((assign[m], assign[d]) in [(a,b),(b,a)]):
                print(f"      {m} -> {d}")
                shown += 1
                if shown >= 6: break
        if shown >= 6: break
for u in sorted(units):
    print(f"{len(units[u]):>4}  {u}")

# ---- emit docs/UNITS_PROPOSAL.md (only when acyclic) ----
if cycles or units.get('UNASSIGNED'):
    raise SystemExit('not emitting proposal: graph has cycles or unassigned modules')

# longest-path layering (layer 0 = no in-repo unit dependencies)
layer = {}
def depth(u, stack=()):
    if u in layer: return layer[u]
    if u in stack: raise RuntimeError('cycle')
    layer[u] = 1 + max((depth(v, stack + (u,)) for v in uedges.get(u, ())), default=-1)
    return layer[u]
for u in units: depth(u)

# transitive reduction of the unit DAG, for readable edge lists
def reachable(u, skip_direct=None):
    seen, todo = set(), [v for v in uedges.get(u, ()) if v != skip_direct]
    while todo:
        v = todo.pop()
        if v in seen: continue
        seen.add(v); todo.extend(uedges.get(v, ()))
    return seen
redges = {u: sorted(v for v in uedges.get(u, set())
                    if v not in reachable(u, skip_direct=v)) for u in units}

out = []
out.append('# Unit decomposition proposal\n')
out.append('Generated by `python3 scripts/unit_design.py` — regenerate after edits; the\n'
           'script fails if the unit graph acquires a cycle or an unassigned module.\n')
out.append(f'**{len(units)} units** covering all **{len(mods)} modules**; the induced unit '
           'dependency graph (from real `import`s) is **acyclic**.\n')
out.append('Each unit ≈ one textbook chapter: a proposed directory under `Jacobians/`, a '
           'description, keystone declarations, member modules, and the units it builds on '
           '(transitively reduced).\n')

out.append('## The unit DAG, bottom-up\n')
out.append('| layer | unit | modules | builds on |')
out.append('|---|---|---|---|')
for u in sorted(units, key=lambda u: (layer[u], u)):
    dep_str = ', '.join(redges[u]) or '—'
    out.append(f'| {layer[u]} | **{u}** | {len(units[u])} | {dep_str} |')
out.append('')

out.append('## Units\n')
for u in sorted(units, key=lambda u: (layer[u], u)):
    dirname, desc, keys = META[u]
    out.append(f'### {u}  →  `Jacobians/{dirname}/`\n')
    out.append(desc + '\n')
    out.append('**Keystones:** ' + '; '.join(f'`{k}`' for k in keys) + '\n')
    dep_str = ', '.join(redges[u]) or 'none (foundation)'
    out.append(f'**Builds on:** {dep_str}\n')
    out.append('**Members:** ' + ', '.join(f'`{m}`' for m in sorted(units[u])) + '\n')

out.append('## Migration plan (not yet executed)\n')
out.append('''1. **File moves**: relocate each member module into its unit directory
   (`git mv`), flattening the current `Dolbeault/` grab-bag; rewrite `import` lines
   mechanically. Lean namespaces follow in a second pass (names are decoupled from paths).
2. **Unit umbrella files**: one `Jacobians/<Dir>.lean` per unit importing its members and
   carrying the unit docstring (description, keystones, dependencies) — the in-code source
   of truth; this proposal becomes generated output.
3. **Targeted splits** surfaced by the DAG analysis:
   - `Abel.lean` mixes divisor foundations with the Abel–Jacobi map — split.
   - `PeriodLattice.lean` imports `CutSurfaceRelations` only to keep the banked archive
     compiling — move that import to the root `Jacobians.lean`.
4. **CI enforcement**: keep this script as the checker — it exits nonzero on any cycle or
   unassigned module, so unit-DAG discipline is enforced by the build.
''')
open('docs/UNITS_PROPOSAL.md', 'w').write('\n'.join(out))
print('\nwrote docs/UNITS_PROPOSAL.md')

# ---- emit docs/units.html: self-contained layered DAG viewer (no external deps) ----
import json
loc = collections.Counter()
for m, p in mods.items():
    loc[assign[m]] += sum(1 for _ in open(p))

# kernel-level usage weights per unit pair (docs/usage_graph.json, optional):
# weight = number of (user-decl, used-decl) constant pairs crossing the unit boundary
uweight, uwit = collections.Counter(), collections.defaultdict(list)
if os.path.exists('docs/usage_graph.json'):
    ug = json.load(open('docs/usage_graph.json'))
    for e in ug['edges']:
        a, b = e['from'][len('Jacobians.'):], e['to'][len('Jacobians.'):]
        if a in assign and b in assign and assign[a] != assign[b]:
            k = (assign[a], assign[b])
            uweight[k] += e['count']
            if len(uwit[k]) < 4:
                uwit[k] += e['witnesses'][:2]

NODE_H, ROW_GAP, XGAP, PAD = 36, 64, 16, 28
maxL = max(layer.values())
rows = collections.defaultdict(list)
for u in units: rows[layer[u]].append(u)

def width(u): return 24 + 7.6 * len(u)

pos = {}
for L in range(maxL + 1):  # bottom-up: order each row by barycenter of placed deps
    def bary(u):
        ds = [v for v in uedges.get(u, ()) if v in pos]
        return sum(pos[v][0] + width(v) / 2 for v in ds) / len(ds) if ds else 1e9
    rows[L].sort(key=lambda u: (bary(u), u))
    x = 0
    for u in rows[L]:
        pos[u] = [x, 0]
        x += width(u) + XGAP
totalW = max(pos[u][0] + width(u) for u in pos) + 2 * PAD
for L in range(maxL + 1):  # center each row
    roww = sum(width(u) for u in rows[L]) + XGAP * (len(rows[L]) - 1)
    off = (totalW - 2 * PAD - roww) / 2 + PAD
    for u in rows[L]: pos[u][0] += off
for u in pos:
    pos[u][1] = PAD + (maxL - layer[u]) * (NODE_H + ROW_GAP)
totalH = 2 * PAD + (maxL + 1) * NODE_H + maxL * ROW_GAP

data = {u: dict(layer=layer[u], loc=loc[u], n=len(units[u]), dir=META[u][0],
                desc=META[u][1], keys=META[u][2], deps=redges[u],
                depmeta={v: dict(w=uweight.get((u, v), 0),
                                 wit=[f'{a.split(".")[-1]} uses {b.split(".")[-1]}'
                                      for a, b in uwit.get((u, v), [])][:2])
                         for v in redges[u]},
                members=sorted(units[u]), x=round(pos[u][0], 1),
                y=round(pos[u][1], 1), w=round(width(u), 1)) for u in units}

html = '''<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<title>Jacobians — unit dependency graph</title>
<style>
  body { margin:0; font:14px/1.45 -apple-system, "Segoe UI", Roboto, sans-serif;
         color:#1a1a2e; background:#fafafa; display:flex; height:100vh; }
  #graph { flex:1; overflow:auto; }
  #panel { width:380px; border-left:1px solid #ddd; padding:18px 20px; overflow-y:auto;
           background:#fff; }
  #panel h2 { margin:0 0 2px; font-size:18px; }
  #panel .meta { color:#666; font-size:12.5px; margin-bottom:10px; }
  #panel h3 { font-size:12px; text-transform:uppercase; letter-spacing:.06em;
              color:#888; margin:16px 0 4px; }
  #panel code { background:#f0f0f4; padding:1px 4px; border-radius:3px; font-size:12.5px; }
  #panel ul { margin:4px 0; padding-left:18px; }
  #panel li { margin:2px 0; }
  #panel .members { font-size:12px; columns:1; }
  .hint { color:#999; font-size:13px; }
  svg text { font:12.5px ui-monospace, "SF Mono", Menlo, monospace; cursor:pointer;
             user-select:none; }
  .node rect { fill:#fff; stroke:#9aa0b4; stroke-width:1.2; rx:7; cursor:pointer; }
  .node.sel rect  { fill:#1a1a2e; stroke:#1a1a2e; }
  .node.sel text  { fill:#fff; }
  .node.dep rect  { fill:#fde8e8; stroke:#c0392b; }
  .node.use rect  { fill:#e8f0fd; stroke:#2b5fc0; }
  .node.dim rect  { opacity:.25; } .node.dim text { opacity:.25; }
  .edge { fill:none; stroke:#c5c9d6; stroke-width:1.1; }
  .edge.dep { stroke:#c0392b; stroke-width:2; }
  .edge.use { stroke:#2b5fc0; stroke-width:2; }
  .edge.dim { opacity:.12; }
  .laylab { fill:#bbb; font:11px sans-serif; }
  .deplink { cursor:pointer; color:#2b5fc0; }
</style></head><body>
<div id="graph"><svg id="svg" width="__W__" height="__H__"></svg></div>
<div id="panel">
  <h2>Unit dependency graph</h2>
  <div class="meta">__NU__ units / __NM__ modules / __NL__ LoC, layered by
  longest path over the (transitively reduced) import-induced DAG.
  Foundations at the bottom, headline results on top.</div>
  <p class="hint">Click a unit: <span style="color:#c0392b">red = builds on</span>,
  <span style="color:#2b5fc0">blue = used by</span> (direct, reduced edges).
  Click the background to reset.</p>
  <div id="info"></div>
</div>
<script>
const DATA = __DATA__;
const NODE_H = __NODE_H__;
const svg = document.getElementById('svg'), NS = 'http://www.w3.org/2000/svg';
function el(t, a) { const e = document.createElementNS(NS, t);
  for (const k in a) e.setAttribute(k, a[k]); return e; }
// layer labels
const seen = new Set();
for (const u in DATA) { const d = DATA[u];
  if (!seen.has(d.layer)) { seen.add(d.layer);
    svg.appendChild(el('text', {x: 6, y: d.y + NODE_H / 2 + 4, 'class': 'laylab'}))
       .textContent = d.layer; } }
// edges under nodes
const edges = [];
for (const u in DATA) for (const v of DATA[u].deps) {
  const a = DATA[u], b = DATA[v];
  const x1 = a.x + a.w / 2, y1 = a.y + NODE_H, x2 = b.x + b.w / 2, y2 = b.y;
  const w = (DATA[u].depmeta[v] || {}).w || 0;
  const p = el('path', {d: `M${x1},${y1} C${x1},${y1 + 45} ${x2},${y2 - 45} ${x2},${y2}`,
                        'class': 'edge',
                        'stroke-width': (0.7 + Math.log2(1 + w) / 3).toFixed(2)});
  p.dataset.from = u; p.dataset.to = v; svg.appendChild(p); edges.push(p);
}
// nodes
const nodes = {};
for (const u in DATA) { const d = DATA[u];
  const g = el('g', {'class': 'node'}); g.dataset.u = u;
  g.appendChild(el('rect', {x: d.x, y: d.y, width: d.w, height: NODE_H, rx: 7}));
  const t = el('text', {x: d.x + d.w / 2, y: d.y + NODE_H / 2 + 4,
                        'text-anchor': 'middle'});
  t.textContent = u; g.appendChild(t);
  g.addEventListener('click', ev => { ev.stopPropagation(); select(u); });
  svg.appendChild(g); nodes[u] = g;
}
function esc(s) { return s.replace(/&/g,'&amp;').replace(/</g,'&lt;'); }
function select(u) {
  const d = DATA[u];
  const users = Object.keys(DATA).filter(v => DATA[v].deps.includes(u));
  for (const v in nodes) nodes[v].setAttribute('class', 'node ' +
    (v === u ? 'sel' : d.deps.includes(v) ? 'dep' : users.includes(v) ? 'use' : 'dim'));
  for (const e of edges) e.setAttribute('class', 'edge ' +
    (e.dataset.from === u ? 'dep' : e.dataset.to === u ? 'use' : 'dim'));
  const link = v => `<code class="deplink" onclick="select('${v}')">${v}</code>`;
  const dep = v => {
    const m = d.depmeta[v] || {};
    const wt = m.w ? ` <span class="hint">(${m.w} decl refs${
      m.wit && m.wit.length ? '; e.g. ' + esc(m.wit[0]) : ''})</span>` : '';
    return `<li>${link(v)}${wt}</li>`;
  };
  document.getElementById('info').innerHTML =
    `<h2>${u}</h2>
     <div class="meta">layer ${d.layer} · ${d.n} modules · ${d.loc.toLocaleString()} LoC
       · proposed <code>Jacobians/${d.dir}/</code></div>
     <p>${esc(d.desc)}</p>
     <h3>Keystones</h3><ul>${d.keys.map(k => `<li><code>${esc(k)}</code></li>`).join('')}</ul>
     <h3>Builds on <span class="hint">(weight = kernel-level decl references)</span></h3>
     <ul>${d.deps.map(dep).join('') || '<span class="hint">nothing (foundation)</span>'}</ul>
     <h3>Used by</h3><p>${users.map(link).join(', ') || '<span class="hint">nothing (headline)</span>'}</p>
     <h3>Members (${d.n})</h3><div class="members">${d.members.map(m => `<code>${m}</code>`).join('<br>')}</div>`;
}
document.getElementById('graph').addEventListener('click', () => {
  for (const v in nodes) nodes[v].setAttribute('class', 'node');
  for (const e of edges) e.setAttribute('class', 'edge');
  document.getElementById('info').innerHTML = '';
});
</script></body></html>'''

html = (html.replace('__DATA__', json.dumps(data))
            .replace('__W__', str(int(totalW))).replace('__H__', str(int(totalH)))
            .replace('__NODE_H__', str(NODE_H)).replace('__NU__', str(len(units)))
            .replace('__NM__', str(len(mods))).replace('__NL__', f'{sum(loc.values()):,}'))
open('docs/units.html', 'w').write(html)
print('wrote docs/units.html')

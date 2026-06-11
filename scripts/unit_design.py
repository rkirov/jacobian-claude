#!/usr/bin/env python3
"""Unit decomposition proposal: assign all modules to ~35 chapter-units via ordered
pattern rules, compute the induced unit dependency graph from real imports, and report
cycles / heavy edges. Emits docs/UNITS_PROPOSAL.md. Run from repo root."""
import os, re, collections

# ---- ordered (regex, unit) rules; first match wins. Paths relative to Jacobians/. ----
RULES = [
    # 1. foundations
    (r'^(ChartedSpaceOfLocalHomeomorph|ULiftManifold|ManifoldIFT|Dolbeault\.RealManifold|Discharge\.Manifold\.ContMDiffOmegaAnalytic)$', 'surfaces-and-charts'),
    (r'^(ProjectiveLine)$', 'projective-line'),
    (r'^(Abel|LinearSystem|MeromorphicLiouville|MeromorphicNFRepair)$', 'meromorphic-and-divisors'),
    (r'^(HolomorphicForms|Genus|Montel(\..*)?)$', 'holomorphic-forms'),
    (r'^(LineIntegral|SmoothPath|SmoothPathCore|Primitive|CotangentCoeff|LoopOffBranch)$', 'paths-and-integrals'),
    # 2. degree theory
    (r'^Discharge\.Manifold\.(MeromorphicAt|LocalMultiplicity|AnalyticDerivOrder|AnalyticLocalFactorization)$', 'local-multiplicity'),
    (r'^Discharge\..*$', 'mapping-degree'),
    (r'^(Degree|ProperMapDegree|ProperMapDegreeConstruct|ProperMapDegreeSheets|MultiplicityPatching|MultiplicityPatchingConstruct|DegDivResidue|LinearSystemDegree|DegreeOneSphere|ToSphereGeneral)$', 'proper-map-degree'),
    # 3. trace machinery (the residue theorem via traces)
    (r'^(MeromorphicTrace|TraceForm|TracePullback|TraceResidue|ResidueChangeOfVariables|RamifiedResidueChangeOfVariables|ResidueTheoremX|SymmetricFunctionDescent)$', 'meromorphic-trace'),
    (r'^Dolbeault\.FormTracePrincipalPart$', 'residue-calculus'),  # Mathlib-only planar atom
    (r'^Dolbeault\.(FormTrace.*|FormResidueTheorem)$', 'form-trace-tower'),
    (r'^Dolbeault\.SerreResidue.*$', 'residue-via-trace'),
    # 4. Čech cohomology
    (r'^Dolbeault\.(CechComplex|CechSection|CechH0|CechRefinement|CechRefinementHomotopy|ChartDiskCover|ChartDiskRefinement|MeromorphicAnalyticBadSet)$', 'cech-cohomology'),
    (r'^Dolbeault\.(Cech(Finiteness.*|Model.*)|CechRefinementLeray|CechRefinementInjective|SchwartzFiniteness|BddHol|CohomologicalH0Finiteness|ChartDiskFiniteness.*|ChartDiskLeray|CohomologicalRR.*|Skyscraper.*)$', 'finiteness-and-chi'),
    (r'^Dolbeault\.(CechH1CupKill|CechH1Genus|CechH1Monotonicity|SerreCupProduct)$', 'cech-h1-genus'),
    # 5. dbar + Dolbeault comparison
    (r'^(DbarDisk|Dolbeault\.(RealForms|DbarLocal|DbarOpenDisk|DbarDiskCohomology|DiskAcyclicCore|CechDiskAcyclic.*|HoloRep))$', 'dbar-solvability'),
    (r'^Dolbeault\.(DolbeaultH01|DolbeaultComparison.*|LocalRealization|GeneralMittagLeffler|GoodCover|LerayCoverExists)$', 'dolbeault-comparison'),
    # 6. residue calculus
    (r'^Dolbeault\.(Residue|FormCoeff|MittagLeffler)$', 'residue-calculus'),
    (r'^Dolbeault\.(PlanarCompactSupportStokes|PlanarHolomorphicChangeOfVariables|AnnulusResidue.*)$', 'planar-stokes-atoms'),
    (r'^Dolbeault\.(ResidueTheoremStokes|ResidueLedgerTransport|ResidueStokes.*|PairFormResidueTheorem|OmegaFactorization)$', 'residue-theorem'),
    # 7. canonical forms + Serre + RR
    (r'^Dolbeault\.(MeromorphicOneFormSystem|CanonicalForm.*|FormRemovableSingularity|SerreOmega0)$', 'canonical-forms'),
    (r'^Dolbeault\.(SerreDuality|SerreDualityPairing|DolbeaultLadder)$', 'serre-duality-cech'),
    (r'^LaurentTail\.(TailSpace|TailMap|LaurentCoeff|Finiteness|DimensionBookkeeping|LinearSystemFiniteDimensional|RiemannRochFirstForm)$', 'laurent-tails'),
    (r'^LaurentTail\..*$', 'serre-duality-tails'),
    (r'^RiemannRoch$', 'riemann-roch'),
    # 8. monodromy + genus-sphere
    (r'^(HolomorphicPrimitive.*|HolomorphicPrimitives)$', 'monodromy'),
    (r'^(VanKampen|SphereSimplyConnected|GenusZeroOfSphere|GenusSphereBackward)$', 'sphere-topology'),
    (r'^(GenusSphereHeadline)$', 'genus-zero-headline'),
    # 9. abel + jacobian
    (r'^(AbelChains|AbelWeakSolutions|AbelPlanarPiece|AbelPieceSolution|AbelCurveSolution)$', 'abel-weak-solutions'),
    (r'^(AbelFormRead|AbelLogDbar|AbelPairing.*|AbelDbarKill|AbelEngine.*|AbelFinal)$', 'abel-theorem'),
    (r'^(PeriodLattice|ZLatticeQuotient)$', 'jacobian-construction'),
    (r'^(PeriodLattice.*|JacobiBasePoints|JacobiLocalMap|OfCurveAnalyticitySkeleton)$', 'period-lattice-rank'),
    # 10. archived bilinear-relations track
    (r'^(CutSurface.*|Dissection|GreenBox|GreenPositivity|BoundaryWordR2|BoundaryPositivity|SurfacePositivity|PeriodMatrixIndep)$', 'riemann-bilinear-archive'),
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
    'riemann-bilinear-archive': ('Archive',
        'Banked, superseded route: cut-surface dissection and the Riemann bilinear '
        'relations R1/R2 with positivity. Kept compiling as an archive; no live consumer '
        '(migration: re-anchor its umbrella import at the root).',
        ['cutSurface_R1 / cutSurface_R2 (banked)']),
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

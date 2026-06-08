# Gate A — geometric global trace `T` from the bundle pushforward (Miranda §VIII.3)

Goal: bridge the PROVEN `TraceForm` bundle pushforward (`traceForm F α : HolomorphicOneForms RiemannSphere`)
to the value-chart trace function `T : ℂ → ℂ` consumed by `globalTrace_of_glue`, discharging the
glue/analyticity hypotheses so Gate A `∑Res(α)=0` becomes unconditional (modulo the honest separation
genericity already recorded by the predecessor).

## The definition
`F := f.toRiemannSphere : X → RiemannSphere` (ContMDiff, nonconstant when `f.div ≠ 0`).
`T α b := coeffAt (traceForm F hF hnc α) ((b:ℂ):RiemannSphere) b`
       = value-chart `dz`-coefficient of the bundle pushforward `Tr_F α`, read in the affine chart
         `chartCoe` at `coe b` (where `chartCoe (coe b) = b`, `chartAt ℂ (coe b) = chartCoe`).

Off the affine-chart-image-of-branchLocus ∪ poles, `T` is analytic (coeffAt_analyticAt + traceForm
holomorphy off branch). At a finite pole-value `p`, `T` is the value-chart coefficient of the trace,
which has the SAME residue as the pole sub-fibre trace `fibreReg`.

## The pieces (bottom-up)
1. DONE-target: `T` definition + `coeffAt`-based read.  AXIOM-CLEAN, foundational.
2. `hT_off`: `T` analytic off the finite exceptional set (coeffAt of traceForm, holomorphic off branch).
3. Glue `hglue_fin`/`hglue_inf`: `T` germ = pole sub-fibre `fibreTrace.traceCoeff`. The deep monodromy
   bridge: identify the bundle sheet-pullback chart coefficient with the planar `coeff·deriv(sheet)`.
   SOUNDNESS: glue is to the POLE SUB-FIBRE (matching globalTrace_of_glue), with the pole/regular
   separation genericity folded into the cover (Gate D refinement). Do NOT assert a false full-fibre
   germ-equality.
4. `R₀ 0 = 0`: genus-0 ∞-vanishing. `traceForm F α : HolomorphicOneForms RiemannSphere` and
   `genus RiemannSphere = 0` ⟹ the holomorphic remainder's `dζ`-coeff at ∞ is 0
   (holomorphicOneForm_eq_zero / the proven coefficient Liouville).

## Honest fallback
Build 1+2 first (axiom-clean). Then glue (hard) + ∞-vanishing. Reduce remainder to MINIMAL named
obligation with precise diagnosis + close-path. No unsound shortcut.

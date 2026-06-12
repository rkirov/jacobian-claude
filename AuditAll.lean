import Jacobians
import Jacobians.Abel
import Jacobians.AbelWeak
import Jacobians.CanonicalForms
import Jacobians.Cech
import Jacobians.Dbar
import Jacobians.DolbeaultComparison
import Jacobians.Finiteness
import Jacobians.Forms
import Jacobians.H1Genus
import Jacobians.JacobianConstruction
import Jacobians.LaurentTail
import Jacobians.LocalMultiplicity
import Jacobians.MappingDegree
import Jacobians.Meromorphic
import Jacobians.MeromorphicTrace
import Jacobians.Monodromy
import Jacobians.Path
import Jacobians.PeriodLattice
import Jacobians.PlanarStokes
import Jacobians.ProperDegree
import Jacobians.ResidueCalculus
import Jacobians.ResidueTheorem
import Jacobians.SerrePairing
import Jacobians.SphereTopology
import Jacobians.Surface
import Jacobians.TailDuality
open scoped ContDiff Manifold

-- Comprehensive ground-truth axiom audit of every challenge deliverable.
-- `sorryAx` in the output = contains unproved obligations (not yet finished).

#print axioms genus_eq_zero_iff_homeo
#print axioms Jacobian.ofCurve_inj
#print axioms Jacobian.ofCurve_contMDiff
#print axioms Jacobian.pushforward_pullback
#print axioms Jacobian.pushforward_contMDiff
#print axioms Jacobian.pullback_contMDiff
#print axioms ContMDiff.degree

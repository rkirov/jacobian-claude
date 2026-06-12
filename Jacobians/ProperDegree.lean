import Jacobians.ProperDegree.DegDivResidue
import Jacobians.ProperDegree.Degree
import Jacobians.ProperDegree.DegreeOneSphere
import Jacobians.ProperDegree.LinearSystemDegree
import Jacobians.ProperDegree.MultiplicityPatching
import Jacobians.ProperDegree.MultiplicityPatchingConstruct
import Jacobians.ProperDegree.ProperMapDegree
import Jacobians.ProperDegree.ProperMapDegreeConstruct
import Jacobians.ProperDegree.ProperMapDegreeSheets
import Jacobians.ProperDegree.ToSphereGeneral

/-!
# Proper Map Degree (`Jacobians/ProperDegree/`)

Degree of a global meromorphic map: `ContMDiff.degree`, sheet counting, multiplicity patching, `deg (div f) = 0`, and degree-one maps to the sphere are homeomorphisms.

**Keystones:** `ContMDiff.degree`; `exists_properMapDegree`; `DegDivResidue (deg∘div = 0)`; `DegreeOneSphere`

**Builds on units:** local-multiplicity, mapping-degree, meromorphic-and-divisors, monodromy, projective-line, sphere-topology
-/

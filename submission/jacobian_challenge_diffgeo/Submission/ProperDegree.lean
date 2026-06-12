import Submission.ProperDegree.DegDivResidue
import Submission.ProperDegree.Degree
import Submission.ProperDegree.DegreeOneSphere
import Submission.ProperDegree.LinearSystemDegree
import Submission.ProperDegree.MultiplicityPatching
import Submission.ProperDegree.MultiplicityPatchingConstruct
import Submission.ProperDegree.ProperMapDegree
import Submission.ProperDegree.ProperMapDegreeConstruct
import Submission.ProperDegree.ProperMapDegreeSheets
import Submission.ProperDegree.ToSphereGeneral

/-!
# Proper Map Degree (`Jacobians/ProperDegree/`)

Degree of a global meromorphic map: `ContMDiff.degree`, sheet counting, multiplicity patching, `deg (div f) = 0`, and degree-one maps to the sphere are homeomorphisms.

**Keystones:** `ContMDiff.degree`; `exists_properMapDegree`; `DegDivResidue (deg∘div = 0)`; `DegreeOneSphere`

**Builds on units:** local-multiplicity, mapping-degree, meromorphic-and-divisors, monodromy, projective-line, sphere-topology
-/

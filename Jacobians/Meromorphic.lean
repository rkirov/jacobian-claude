import Jacobians.Meromorphic.Abel
import Jacobians.Meromorphic.LinearSystem
import Jacobians.Meromorphic.MeromorphicInverse
import Jacobians.Meromorphic.MeromorphicLiouville
import Jacobians.Meromorphic.MeromorphicNFRepair

/-!
# Meromorphic And Divisors (`Jacobians/Meromorphic/`)

Meromorphic functions as germ data, divisors (`Finsupp`), orders, linear systems and their dimension; Liouville and normal-form repair. (Migration: split the mixed `Abel.lean` into divisor foundations here vs the Abel–Jacobi map upstairs.)

**Keystones:** `MeromorphicFunction`; `Divisor`; `lDim / linearSystem`

**Builds on units:** jacobian-construction
-/

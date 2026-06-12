import Submission.Dbar.CechDiskAcyclic
import Submission.Dbar.CechDiskAcyclicAssembly
import Submission.Dbar.CechDiskAcyclicProof
import Submission.Dbar.DbarDisk
import Submission.Dbar.DbarDiskCohomology
import Submission.Dbar.DbarLocal
import Submission.Dbar.DbarOpenDisk
import Submission.Dbar.DiskAcyclicCore
import Submission.Dbar.HoloRep
import Submission.Dbar.RealForms

/-!
# Dbar Solvability (`Jacobians/Dbar/`)

The intrinsic `∂̄` operator on the surface and its local solvability: the planar Dolbeault lemma on disks (Forster 13.2), disk acyclicity for the Čech complex, and holomorphic representatives of `∂̄`-closed germs.

**Keystones:** `RealForms.dbar`; `DbarOpenDisk.dbar_solvable_open_disk`; `CechDiskAcyclic`

**Builds on units:** cech-cohomology, surfaces-and-charts
-/

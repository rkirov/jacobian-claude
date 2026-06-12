import Jacobians.Dbar.CechDiskAcyclic
import Jacobians.Dbar.CechDiskAcyclicAssembly
import Jacobians.Dbar.CechDiskAcyclicProof
import Jacobians.Dbar.DbarDisk
import Jacobians.Dbar.DbarDiskCohomology
import Jacobians.Dbar.DbarLocal
import Jacobians.Dbar.DbarOpenDisk
import Jacobians.Dbar.DiskAcyclicCore
import Jacobians.Dbar.HoloRep
import Jacobians.Dbar.RealForms

/-!
# Dbar Solvability (`Jacobians/Dbar/`)

The intrinsic `∂̄` operator on the surface and its local solvability: the planar Dolbeault lemma on disks (Forster 13.2), disk acyclicity for the Čech complex, and holomorphic representatives of `∂̄`-closed germs.

**Keystones:** `RealForms.dbar`; `DbarOpenDisk.dbar_solvable_open_disk`; `CechDiskAcyclic`

**Builds on units:** cech-cohomology, surfaces-and-charts
-/

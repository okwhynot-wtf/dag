/-!
# Geom.Core

Version markers for the archive-geometry library.
-/

namespace Geom.Core

/-- Spine completeness index (v1.0). -/
def stage : Nat := 5

/-- Package major version. -/
def versionMajor : Nat := 1

theorem stage_ge_charter : 1 ≤ stage := by
  decide

theorem stage_is_v1 : stage = 5 := rfl

theorem version_major_one : versionMajor = 1 := rfl

#print axioms stage_ge_charter
#print axioms stage_is_v1
#print axioms version_major_one

end Geom.Core

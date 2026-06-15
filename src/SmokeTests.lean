import EndKan.TestFixtures
import EndKan.Kan.Core

namespace EndKan.SmokeTests

open CategoryTheory
open CategoryTheory.Functor

universe u v

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D] {H : Type u} [Category.{v} H]

#check EndKan.Kan.Lan
#check EndKan.Kan.Ran
#check EndKan.Kan.lan_obj_eq
#check EndKan.Kan.ran_obj_eq

/-- Run all EndKan smoke tests. -/
def runAll : IO Unit := do
  IO.println "EndKan smoke tests"
  IO.println "=================="
  IO.println "✓ TestFixtures (ends/coends β/η on abstract categories)"
  IO.println "✓ Kan.Core (pointwise Kan abbreviations)"
  IO.println "=================="
  IO.println "All smoke tests completed successfully."

end EndKan.SmokeTests

def main (_args : List String) : IO Unit :=
  EndKan.SmokeTests.runAll

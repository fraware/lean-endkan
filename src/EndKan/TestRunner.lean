import EndKan.TestFixtures
import EndKan.Fubini
import EndKan.Kan.Core

namespace EndKan.TestRunner

/-- Unified test runner: compile-time fixtures plus runtime smoke output. -/
def runAllTests : IO Unit := do
  IO.println "EndKan test runner"
  IO.println "=================="
  IO.println "Compile-time checks:"
  IO.println "  EndKan.TestFixtures (end/coend β/η on abstract categories)"
  IO.println "  EndKan.Fubini (Fubini β helpers)"
  IO.println "  EndKan.Kan.Core (pointwise Kan abbreviations)"
  IO.println "=================="
  IO.println "All compile-time checks passed."

end EndKan.TestRunner

def main (_args : List String) : IO Unit :=
  EndKan.TestRunner.runAllTests

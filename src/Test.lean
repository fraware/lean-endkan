import EndKan.TestFixtures

namespace EndKan.Test

/-- Smoke entry point for `lake exe test`. -/
def runAllTests : IO Unit := do
  IO.println "EndKan test suite"
  IO.println "================="
  IO.println "Compile-time fixtures: EndKan.TestFixtures (built with the library)"
  IO.println "✓ End/coend β/η API elaborates (abstract categories)"
  IO.println "================="
  IO.println "All tests completed successfully."

end EndKan.Test

def main (_args : List String) : IO Unit :=
  EndKan.Test.runAllTests

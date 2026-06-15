import EndKan.Kan.BeckChevalley

namespace EndKan.Attr

open CategoryTheory

/-- Metadata for registered Beck–Chevalley squares. -/
structure KanSquareData where
  derivedLemma : Lean.Name
  deriving Inhabited

end EndKan.Attr

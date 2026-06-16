import EndKan.Core

/-!
# EndKan

Stable mathematical API for ends, coends, Fubini lemmas, Kan extensions, and Beck–Chevalley
infrastructure on the diagonal/product-category interface.

## Core modules

- `EndKan.End` — ends `∫_{c} F(c,c)` for `F : Cᵒᵖ × C ⥤ D`
- `EndKan.Coend` — coends `∫^{c} F(c,c)` for `F : C × Cᵒᵖ ⥤ E`
- `EndKan.Fubini` — Fubini targets and β helpers
- `EndKan.Kan` — Mathlib-backed pointwise Kan extensions
- `EndKan.Kan.BeckChevalley` — commutative squares and Beck–Chevalley class

## Optional modules

- `EndKan.Automation` — tactics (`end_beta`, `coend_beta`, …), attributes, FFI
- `EndKan.Experimental` — telemetry, monitoring, regression, optimization

See `docs/EXTRACTION_LEDGER.md` for Mathlib upstream candidates.
-/

# Fubini extraction staging (upstream order #3)

Nested product Fubini for ends and coends over `(C × D)ᵒᵖ × (C × D)` and
`(C × D) × (C × D)ᵒᵖ`. See `docs/MATHLIB_PR_FUBINI.md` and `docs/EXTRACTION_LEDGER.md` §5–§6.

**Not Mathlib-ready as a single PR today:** slice contr-leg isomorphisms require
`AllEndSliceContrIso` / `CoendSliceContrIso` hypothesis classes on Lean `v4.31.0-rc1`
(mutual `IsIso` bootstrap blocked). Package helper lemmas and a concrete constant
example first; full unconditional Fubini is a follow-up design issue.

## Local build

```powershell
lake build Scratch.MathlibFubiniExamples
lake build EndKan.Fubini
```

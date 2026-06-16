# Mathlib end β/η extraction staging

First upstream PR candidate from `lean-endkan` (see `docs/EXTRACTION_LEDGER.md` §1).

| File | Purpose |
|------|---------|
| `LEMMA_MAP.md` | EndKan → Mathlib name/path checklist with readiness status |
| `MODULE_STRUCTURE.md` | Draft `CategoryTheory.Limits.Shapes.End.*` layout |
| `../src/Scratch/MathlibEndBetaExamples.lean` | Buildable abstract-category β/η examples (no tactics) |

Build:

```powershell
lake build Scratch.MathlibEndBetaExamples
```

PR brief: `docs/MATHLIB_PR_END_BETA_ETA.md`.

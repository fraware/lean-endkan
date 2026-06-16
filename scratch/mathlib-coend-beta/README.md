# Mathlib coend β/η extraction staging

Second upstream PR candidate from `lean-endkan` (see `docs/EXTRACTION_LEDGER.md` §2).

| File | Purpose |
|------|---------|
| `LEMMA_MAP.md` | EndKan → Mathlib name/path checklist with readiness status |
| `MODULE_STRUCTURE.md` | Draft `CategoryTheory.Limits.Shapes.Coend.*` layout |
| `../src/Scratch/MathlibCoendBetaExamples.lean` | Buildable abstract-category β/η examples (no tactics) |

Build:

```powershell
lake build Scratch.MathlibCoendBetaExamples
```

PR brief: `docs/MATHLIB_PR_COEND_BETA_ETA.md`.

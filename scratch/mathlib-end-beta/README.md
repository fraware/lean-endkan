# Minimal diagonal-end adapter staging

This directory contains the evidence-backed first Mathlib proposal from `lean-endkan`.

The current decision is `ESCALATE AND NARROW`. The package proposes one `endBifunctor` adapter and three general simplification lemmas. The broader diagonal-end structures, wrappers, β and η aliases, and namespace design remain deferred.

| File | Purpose |
|---|---|
| `LEMMA_MAP.md` | Inclusion, derivation, deferral, and rejection decisions for each declaration |
| `MODULE_STRUCTURE.md` | Minimal placement and import boundary |
| `ACCEPTANCE_PACKET.md` | Downstream evidence, before-and-after comparison, gates, utility ledger, and falsification conditions |
| `../../docs/MATHLIB_PR_END_BETA_ETA.md` | Narrowed PR brief and maintainer question |
| `../../src/Scratch/MathlibEndBifunctorConsumer.lean` | Candidate implementation tested against the Fubini consumer |
| `../../src/Scratch/MathlibEndBetaExamples.lean` | Historical broad β and η staging examples retained for comparison |

## Build gates

```powershell
lake build Scratch.MathlibEndBifunctorConsumer
lake build Scratch.MathlibEndBetaExamples
lake build EndKan
.\scripts\acceptance.ps1
```

The minimal proposal should advance only after these gates pass and a Mathlib maintainer confirms naming and placement.

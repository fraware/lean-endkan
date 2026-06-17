# Mathlib submission readiness

Last verified: **2026-06-17** on Lean `v4.31.0` / Mathlib `v4.31.0`.

Gate: `lake build EndKan`, all four `Scratch.Mathlib*` smoke targets, and
`.\scripts\acceptance.ps1` — all green on this pin.

Briefs: `docs/MATHLIB_PR_*.md`. Staging maps: `scratch/mathlib-*/LEMMA_MAP.md`.
Ledger: `docs/EXTRACTION_LEDGER.md`.

| Candidate PR | Is it new API? | Is it only documentation? | Thin alias over existing Mathlib? | Buildable scratch file | Recommended action |
|--------------|----------------|---------------------------|-----------------------------------|------------------------|--------------------|
| **End β/η** (`docs/MATHLIB_PR_END_BETA_ETA.md`) | Yes — diagonal profunctor layer on `Cᵒᵖ × C`, named β/η lemmas, `post_ext` / `post_uniq` | No | Mostly — wraps `Limits.end_` on `curry.obj F`; new wedge packaging and simp-normal fiber lemmas | `Scratch.MathlibEndBetaExamples` | **Submit first.** Maintainer naming pass (`endDiagonal` vs abbreviations), then port scratch examples into `CategoryTheory/Limits/Shapes/End/Diagonal.lean` + `BetaEta.lean`. |
| **Coend β/η** (`docs/MATHLIB_PR_COEND_BETA_ETA.md`) | Yes — swap + curried diagonal layer on `C × Cᵒᵖ`, β/η lemmas, `eqToHom` bridge | No | Mostly — wraps `Limits.coend` on `coendBifunctor F`; `eqToHom_symm_comp_mpr_diagonal` and `ι_dinatural` are substantive glue | `Scratch.MathlibCoendBetaExamples` | **Submit second** after end β/η lands. Mirror naming with PR #1; proof port is ready (`ι_dinatural` fixed for `Eq.heq` / `HEq.eq` API on v4.31.0). |
| **Nested Fubini** (`docs/MATHLIB_PR_FUBINI.md`) | Yes — slice embeddings, inner ends/coends, nested outer profunctors, `endFubiniIso` / `coendFubiniIso` | No | No — new nested-product Fubini infrastructure; hypothesis classes `AllEndSliceContrIso` / `CoendSliceContrIso` are explicit boundaries | `Scratch.MathlibFubiniExamples` | **Submit third** (phased: slice helpers → nested iso under hypothesis → examples). Open Zulip design thread on hypothesis class vs cov-only inner map before Mathlib PR. |
| **Kan / Beck–Chevalley** (`docs/MATHLIB_PR_KAN_BECKCHEVALLEY.md`) | Partial — comparison morphism + instances under equivalence; comma-pullback path not packaged | No | Partially — `Lan`/`Ran` abbreviations and `beckChevalleyCompare` sit on Mathlib pointwise Kan API | `Scratch.MathlibKanBcExamples` | **Design issue first**, then minimal Mathlib PR (`reflSquare` + `[IsEquivalence K]` only). Do not bundle tactics, comma-final proofs, or Fubini in the first upstream change. |

## Submission order

1. End β/η → 2. Coend β/η → 3. Fubini (helpers + hypothesized iso) → 4. Beck–Chevalley (after design approval).

## Out of scope for Mathlib (stay in lean-endkan)

- Tactics (`end_beta!`, `coend_beta!`, `beck_chevalley!`, attributes, telemetry)
- `EndKan.Automation`, `EndKan.Experimental`, FFI / Rust production paths
- Unconditional contr-leg `IsIso` bootstrap (blocked; documented in `scratch/SliceIsoMin.lean`)

## Pre-submission checklist (all candidates)

- [x] Toolchain aligned with Mathlib master (`v4.31.0`)
- [x] Local acceptance matrix green
- [ ] Mathlib Zulip design thread (especially Fubini hypothesis + BC API shape)
- [ ] Maintainer naming / module layout sign-off
- [ ] Port proofs from `src/Scratch/Mathlib*.lean` into Mathlib namespace
- [ ] Mathlib CI + CHANGELOG on each PR

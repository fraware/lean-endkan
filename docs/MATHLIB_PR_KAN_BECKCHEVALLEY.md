# Mathlib design issue: Beck–Chevalley for comma squares

## Issue title

`Design: Beck–Chevalley comparison for commutative squares of functors`

## Summary

Propose a Mathlib API for the **Beck–Chevalley comparison morphism**

`Lan_K (L ⋙ N ⋙ F) ⟶ M ⋙ F`

associated to a commutative square `K ⋙ M = L ⋙ N`, and document which geometric
hypotheses imply it is an isomorphism.

EndKan staging: `EndKan.Kan.BeckChevalley`, `EndKan.Kan.BeckChevalley.Hypotheses`,
`scratch/mathlib-kan-bc/`.

## What Mathlib already has

- Pointwise left Kan extensions (`Functor.KanExtension.Pointwise`)
- Comma categories (`CostructuredArrow`, `StructuredArrow`)
- Finality lemmas (not yet wired into a BC pipeline in EndKan default import graph)

## What EndKan proves today

| Result | Hypothesis |
|--------|------------|
| `reflSquare_beckChevalley` | `[IsEquivalence K]` |
| `pullbackSquare_of_equivalence` | `[IsEquivalence K]` |
| `fullyFaithfulSquare_of_equivalence` | `[IsEquivalence K,L]`, `[Faithful M]`, FF on legs |
| `exactSquare_of_equivalence` | + `[Faithful L]`, `[PreservesFilteredColimits M]` |

Comparison map is `descOfIsLeftKanExtension` from the pointwise unit; iso follows from
`isLeftKanExtensionAlongEquivalence'`.

## Open design questions

1. Should `BeckChevalley` be a typeclass with a `compare_iso` field, or a theorem family?
2. Naming: `beckChevalleyCompare` vs Mathlib `Lan` API conventions
3. Pullback squares: comma-category formulation vs equivalence shortcut
4. Whether `Comma.final_fst` imports are acceptable in core Mathlib (linker budget)

## Proposed minimal Mathlib PR (after design approval)

- Document comparison morphism for `reflSquare`
- Instance under `[IsEquivalence K]` mirroring `isLeftKanExtensionAlongEquivalence'`
- **No** EndKan tactics in Mathlib

## Explicitly out of scope for first Mathlib PR

- Full comma-pullback proof of BC
- EndKan automation (`beck_chevalley!`)
- Fubini lemmas (separate PR track)

## Local verification

```powershell
lake build EndKan.Kan.BeckChevalley
lake build Scratch.MathlibKanBcExamples
.\scripts\acceptance.ps1
```

## Staging artifacts

- `scratch/mathlib-kan-bc/LEMMA_MAP.md`
- `src/Scratch/MathlibKanBcExamples.lean` — `reflSquare` instance smoke test

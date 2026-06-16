# Kan / Beck–Chevalley — Mathlib upstream map

Staging for extraction waves **4–5** (`docs/EXTRACTION_LEDGER.md` §7, §10).

## Kan extensions (mostly Mathlib already)

| Status | EndKan name | Notes |
|--------|-------------|-------|
| alias | `Lan`, `Ran` | `pointwiseLeftKanExtension` / `pointwiseRightKanExtension` |
| alias | `lan_obj_eq`, `ran_obj_eq` | Document in Mathlib docstrings |
| defer | EndKan tactics | local automation |

## Beck–Chevalley

| Status | EndKan name | Mathlib-ready? | Notes |
|--------|-------------|----------------|-------|
| ready | `Square`, `reflSquare`, `beckChevalleyCompare` | API | Comparison morphism |
| ready | `beckChevalleyIso`, `beckChevalleyPullback` | extraction | tactic keys |
| proved | `reflSquare_beckChevalley` | under `[IsEquivalence K]` | `Hypotheses.lean` |
| proved | `pullbackSquare_of_equivalence` | equivalence hypothesis | not bare pullback |
| proved | `fullyFaithfulSquare_of_equivalence` | strong hypotheses | |
| proved | `exactSquare_of_equivalence` | PES-style | |
| boundary | `IsPullbackSquare.comma_pullback` | Prop placeholder | comma finality deferred |
| ready | `beckChevalleySouth`, `beckChevalleyNorth` | staging aliases | `Hypotheses.lean` |
| ready | `square_comm_whisker`, `refl_beckChevalleySouth_eq` | partial geometry | |

## Recommended Mathlib sequence

1. **Design issue:** Beck–Chevalley for comma squares (goals, naming, `compare_iso` field)
2. **Small PR:** `lan_obj_eq` / structured-arrow documentation if missing
3. **Later:** equivalence-based instances (mirror `Hypotheses.lean`)

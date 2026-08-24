# EndKan current-upstream audit — 2026-08-24

This document supersedes the June 2026 extraction queue **for current upstream decisions**. The older extraction ledger remains useful as a historical record of what was proved and staged on Lean/Mathlib 4.31, but its statements about upstream gaps must not be treated as current without revalidation.

## Audit baseline

- Lean: `leanprover/lean4:v4.34.0-rc2`
- Mathlib: `dc84fcbe9e049439c1c36d6db290cc0565f77788` (master, 2026-08-24)
- Audit branch: `audit/2026-08-current-mathlib`
- Build status on this baseline: **pending CI** until the branch workflow completes successfully.

No 4.34 build claim should be inferred from the older 4.31 certification.

## Decision table

| Local stream | June plan | Current finding | Decision |
|---|---|---|---|
| End β/η | first Mathlib PR | Most proposed declarations are aliases/rephrasings of existing `Limits.end_` API | Do not upstream in current form |
| Coend β/η | second Mathlib PR | Same issue on the dual side | Do not upstream in current form |
| End/coend bifunctor convenience | package `Cᵒᵖ × C ⥤ D` around Mathlib's curried API | Potential ergonomic value, but Mathlib already has a mature curry/uncurry equivalence | Keep only if real downstream proofs demonstrate material compression |
| Fubini ends/coends | dedicated Mathlib files | Mathlib already has a general categorical Fubini theorem for limits/colimits; local specialized proof currently assumes strong slice-isomorphism/epi hypotheses | Reset theorem from the mathematical statement and derive from generic Fubini if possible |
| Beck–Chevalley/Kan | new `Square` / `BeckChevalley` hierarchy | Current Mathlib has `TwoSquare`, Guitart exact squares, Kan-extension base change, and active right-Kan dualization work | Retire parallel hierarchy as an upstream proposal; translate local examples into current Mathlib vocabulary |
| Automation | later tactic discussion | Primitive API is not yet validated against current upstream | Keep local |

## 1. End and coend β/η

Current Mathlib's `Mathlib/CategoryTheory/Limits/Shapes/End.lean` already provides the universal-property API used by the local wrappers, including:

- `Wedge` / `Cowedge` and their constructors;
- `Wedge.IsLimit.lift` and simp theorem `lift_ι`;
- `Cowedge.IsColimit.desc` and simp theorem `π_desc`;
- `end_`, `end_.π`, `end_.condition`, `end_.hom_ext`, `end_.lift`, `end_.lift_π`;
- `end_.map`, `end_.map_π`, `end_.map_comp`, `end_.map_id`;
- the dual coend API.

In the current local files:

- `end_beta` is a name around `lift_π`;
- `end_π_beta` is a name around projection dinaturality;
- `end_map_beta` is a name around `map_π`;
- `end_π_eta` is reflexivity;
- analogous coend declarations package existing universal-property equations.

These are useful locally for notation and experimentation, but they do not presently clear the upstream novelty/need bar.

### Required evidence before reconsideration

A product-bifunctor convenience layer may be reconsidered only if at least one of the following is demonstrated against current Mathlib:

1. three independent real downstream proofs become materially shorter or more stable;
2. a substantial theorem is awkward specifically because current end/coend API is curried;
3. an upstream maintainer explicitly asks for an uncurried convenience layer.

Synthetic β/η renamings alone are insufficient evidence.

## 2. Fubini reset

Mathlib already contains `Mathlib/CategoryTheory/Limits/Fubini.lean`, whose purpose is a general Fubini theorem for categorical limits and colimits. It provides canonical isomorphisms comparing a limit over a product category with an iterated limit, and dual colimit results.

The local `endFubiniIso` is therefore not to be evaluated as if Mathlib lacked Fubini infrastructure.

More importantly, the current local construction assumes conditions including:

- `AllEndSliceContrIso F`, which requires every relevant contravariant slice leg to be an isomorphism;
- epimorphism hypotheses on `endInnerLift`;
- existence of the relevant ends.

Those assumptions arise from the present implementation strategy. They must not be promoted to the intended mathematical theorem merely because they make the prototype go through.

### New research question

For a suitable profunctor

`F : (C × D)ᵒᵖ × (C × D) ⥤ E`,

formalize the mathematically expected comparison between:

- the end over `C × D`; and
- an iterated end over `C` and `D`.

Then determine whether the result can be obtained by:

1. expressing the relevant end as an ordinary categorical limit;
2. applying Mathlib's generic `Limits.Fubini` theorem;
3. transporting across the required curry/uncurry and indexing equivalences.

### Desired outcome hierarchy

1. **Best:** a clean specialized end/coend Fubini theorem under ordinary existence assumptions, proved from generic Fubini.
2. **Also valuable:** a small missing bridge theorem between Mathlib's end presentation and generic limit infrastructure.
3. **Research result:** a precise explanation of which indexing/category equivalence is missing and why.
4. **Not acceptable as a flagship upstream theorem:** preserving strong local slice-isomorphism/epi assumptions without mathematical necessity.

## 3. Kan extension / Beck–Chevalley reset

The June plan treated Beck–Chevalley infrastructure as a major Mathlib gap. That is no longer current.

Current Mathlib contains Guitart-exact-square/Kan-extension infrastructure under `Mathlib/CategoryTheory/GuitartExact/`, including:

- `TwoSquare`-based square data;
- composition of squares;
- exactness/finality formulations;
- left Kan-extension base-change transformations and isomorphism results under exactness hypotheses.

As of 2026-08-23, Mathlib PR #43063 (`feat(CategoryTheory): right Kan extensions and Guitart exact squares`) is extending the same framework to right Kan extensions.

### Consequence

Do not upstream EndKan's local `Square`, `ExactSquare`, `BeckChevalley`, or parallel comparison-map hierarchy as foundational infrastructure.

Instead:

1. translate each local example to `TwoSquare` / current Guitart-exact terminology;
2. delete or quarantine local abstractions that become redundant;
3. diff the remaining desired theorems against current master and open PR #43063;
4. extract only genuinely missing instances, interoperability lemmas, or specialized consequences.

## 4. Current upstream candidate ranking

### A. Research priority: specialized end/coend Fubini

Potential value: **high**.
Current readiness: **low**.
Reason: mathematically substantive, but current local proof architecture is too assumption-heavy and must be reconciled with generic Mathlib Fubini.

### B. Conditional candidate: uncurried end/coend convenience API

Potential value: **medium**.
Current readiness: **low**.
Reason: possible ergonomics gain, but novelty is not yet demonstrated beyond wrappers around existing declarations.

### C. Conditional candidate: GuitartExact/Kan interoperability

Potential value: **medium to high** if a concrete missing theorem survives the current-master diff.
Current readiness: **research**.

### Retired as current upstream proposals

- standalone β/η alias PRs;
- parallel Beck–Chevalley square hierarchy;
- tactic extraction before primitive API validation.

## 5. Acceptance gate for any EndKan-derived Mathlib PR

A candidate may move to `PR_READY` only when all of the following hold:

1. **Current baseline:** builds against the recorded current Mathlib SHA / Lean toolchain.
2. **Novelty:** current master and open PRs do not already provide the result or a clean equivalent mechanism.
3. **Need:** demonstrated by real downstream use, not only synthetic examples.
4. **Mathematical statement first:** hypotheses are justified independently of implementation accidents.
5. **Minimal abstraction:** uses current Mathlib vocabulary and does not introduce a parallel hierarchy.
6. **Proof integrity:** no `sorry`, `admit`, custom axioms, or hidden experimental automation dependencies.
7. **Reviewability:** the PR can explain the missing capability and immediate use without requiring reviewers to understand the EndKan repository.

## 6. Immediate work queue

1. Obtain CI evidence for this 4.34/current-Mathlib audit branch.
2. Build a declaration-level diff between local end/coend wrappers and current `Limits.End` API.
3. Write a clean target statement for specialized end Fubini before modifying the proof.
4. Reduce that target to `Limits.Fubini` or identify the smallest missing bridge.
5. Translate Kan/Beck–Chevalley examples to `TwoSquare` / Guitart exact squares.
6. Only after these steps, select the first new Mathlib candidate.

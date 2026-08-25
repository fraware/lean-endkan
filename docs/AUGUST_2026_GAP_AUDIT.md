# August 2026 Mathlib gap audit

Date: 2026-08-24

This document supersedes the upstream recommendations in `EXTRACTION_LEDGER.md`. The older ledger
remains useful as a record of the June extraction program, but its proposed PR order must not be
used as a current Mathlib gap map.

## Verification boundary

- Target toolchain for the current audit: Lean `v4.34.0-rc2`.
- Current Mathlib source was re-audited directly on 2026-08-24.
- EndKan's Rust formatting, Clippy, tests, cargo-deny, and security audit pass after refreshing the
  vulnerable `anyhow` lock entry.
- The current Lean migration branch has a self-contained toolchain setup and fresh-dependency build
  path. A green Lean build is still a separate evidence obligation; this document does not claim one
  until CI completes successfully.

## Executive decision

None of the June End/Coend beta-eta wrappers, the existing nested Fubini construction, or the local
Beck--Chevalley hierarchy should be upstreamed in their present form.

The current research priority is narrower:

1. determine whether Mathlib benefits from a *direct end/coend Fubini API* built on its existing
   `Limits.end_` / `Limits.coend` interfaces;
2. if so, construct it using a genuine two-parameter inner end/coend, not the diagonal slice used by
   the current EndKan implementation;
3. express any Kan base-change results in Mathlib's current `TwoSquare` / Guitart-exact vocabulary.

No upstream PR should be opened until the replacement construction is both general and shown to
remove friction in a real downstream proof.

## 1. End API: current overlap

Current Mathlib's `CategoryTheory.Limits.Shapes.End` already provides the core end API for
`F : Jᵒᵖ ⥤ J ⥤ C`:

- `HasEnd`;
- `end_` and `end_.π`;
- `end_.condition`;
- `end_.hom_ext`;
- `end_.lift` and the simp lemma `end_.lift_π`;
- `end_.map`, `end_.map_π`, `end_.map_comp`, and `end_.map_id`;
- `endFunctor`.

The EndKan layer

- `EndObj`, `π`, `lift`, `uniq`, `map`, `map_π`;
- `end_beta` / eta-style aliases;
- `endBifunctor := curry.obj` and its object/map simp lemmas

is therefore primarily a wrapper around existing Mathlib declarations.

Mathlib's currying API already generates the component simp lemmas for `curry.obj`. A separate
`endBifunctor` adapter is not, by itself, sufficient upstream value.

**Decision:** retire the June end beta/eta and adapter PR plans. Keep these declarations local only
when they materially improve EndKan's own notation or experiments.

## 2. Coend API: current overlap

The dual conclusions apply to the existing coend wrappers. Current Mathlib already provides
`coend`, `coend.ι`, its dinaturality equation, extensionality, `coend.desc`, the corresponding simp
lemma, and functorial maps.

A new upstream contribution would need to expose genuinely missing structure or remove a recurring
proof obstacle; renamed beta/eta wrappers are not enough.

**Decision:** retire the June coend beta/eta PR plan.

## 3. General categorical Fubini already exists

Current `Mathlib.CategoryTheory.Limits.Fubini` already proves categorical Fubini results for ordinary
limits and colimits. In particular it provides, with component simp lemmas:

- `limitUncurryIsoLimitCompLim`;
- `colimitUncurryIsoColimitCompColim`;
- `limitIsoLimitCurryCompLim`;
- `colimitIsoColimitCurryCompColim`;
- `limitFlipCompLimIsoLimitCompLim` and its colimit dual;
- `limitCurrySwapCompLimIsoLimitCurryCompLim` and its colimit dual.

Consequently EndKan must not introduce a parallel general-purpose Fubini framework.

A potentially useful remaining question is whether a direct theorem for *ends/coends over product
categories* is missing. That question is distinct from ordinary limit Fubini because Mathlib defines
ends through multiequalizers rather than exposing them merely as limits over `C × D`.

## 4. Structural audit of the current EndKan nested-end construction

The existing implementation in `Fubini/Slice.lean` and `Fubini/Nested.lean` is not the general
product-end Fubini theorem that should be considered for upstreaming.

### 4.1 The current inner slice is diagonal in `D`

`endSlice F d` embeds `Cᵒᵖ × C` by fixing both `D` coordinates to the same object `d`:

```text
(op c, c') ↦ (op (c, d), (c', d)).
```

Thus `endInnerObj F d` is only the inner end of the diagonal `D` slice.

A genuine iterated end needs an inner object for an arbitrary pair `(d₀, d₁)`:

```text
Inner F (op d₀, d₁)
  = ∫_c F (op (c, d₀), (c, d₁)).
```

Those objects must assemble into a profunctor `Dᵒᵖ × D ⥤ E` before taking the outer end.

### 4.2 The current outer morphism action is one-sided

`endOuterProfunctor` currently defines its map using only the covariant component of a morphism in
`Dᵒᵖ × D`. This is a direct consequence of having only diagonal inner objects available.

The additional `AllEndSliceContrIso`, invertibility, and `Epi (endInnerLift F d)` hypotheses are used
to manufacture enough transport to prove the local isomorphism. They are not hypotheses of the
standard general Fubini theorem for ends.

### 4.3 Consequence

The fact that `endFubiniIso` is proved under these assumptions is a valid local theorem, but it
should not be advertised as the general end-Fubini theorem and should not be extracted to Mathlib
in its present form.

The coend construction has the dual issue.

**Decision:** retire the existing `endFubiniIso` / `coendFubiniIso` extraction plan. Treat these files
as historical experimental evidence until the two-parameter construction replaces them.

## 5. Replacement research target: two-parameter iterated ends

The next mathematically sound experiment should have this shape.

For

```text
F : (C × D)ᵒᵖ × (C × D) ⥤ E,
```

define, for every `(op d₀, d₁) : Dᵒᵖ × D`, the `C`-profunctor

```text
F[d₀,d₁] : Cᵒᵖ × C ⥤ E
F[d₀,d₁](op c₀, c₁) = F(op (c₀,d₀), (c₁,d₁)).
```

Then define

```text
InnerEnd F : Dᵒᵖ × D ⥤ E
InnerEnd F (op d₀, d₁) = end_ (curry.obj F[d₀,d₁]).
```

The morphism action should be induced canonically using `Limits.end_.map` from the natural
transformation generated by the two `D` morphism components. No invertibility assumption on those
components should be necessary.

The target theorem is then an isomorphism between

```text
∫_(c,d) F((c,d),(c,d))
```

and

```text
∫_d (∫_c F((c,d),(c,d)))
```

where the displayed notation is only mnemonic: the implementation must respect Mathlib's curried
end API and its universe constraints.

### Required evidence before upstream consideration

1. The two-parameter `InnerEnd F` is a genuine functor on `Dᵒᵖ × D` with no artificial
   invertibility, epi, or mono assumptions.
2. The forward and backward maps are defined only from the universal properties of the relevant
   ends.
3. The inverse laws are proved by existing `end_.hom_ext` / `end_.lift_π` infrastructure.
4. The coend theorem follows by a clean dual construction, not by a parallel ad hoc hierarchy.
5. At least one nontrivial downstream example becomes materially shorter or clearer.
6. Current Mathlib source and open PRs are searched again immediately before any extraction.

Until all six obligations hold, this remains research rather than an upstream candidate.

## 6. Kan extensions and base change

The June ledger treated a local `Square` / `BeckChevalley` hierarchy as a major Mathlib gap. That is
no longer current.

Mathlib now contains Guitart-exact-square / Kan-extension infrastructure built around `TwoSquare`,
including left-Kan base-change constructions, and active work has been extending the dual right-Kan
side.

**Decision:** do not upstream a parallel square or Beck--Chevalley hierarchy. Any surviving EndKan
result must first be translated into current `TwoSquare` / Guitart-exact terminology and shown to
be absent there.

## 7. Current upstream posture

| EndKan area | August 2026 posture |
|---|---|
| End beta/eta wrappers | Local convenience only; upstream plan retired |
| Coend beta/eta wrappers | Local convenience only; upstream plan retired |
| `endBifunctor` / curry wrappers | Existing Mathlib currying API is sufficient; upstream plan retired |
| Current nested Fubini implementation | Research artifact; not general enough for upstream extraction |
| Two-parameter end/coend Fubini | Active research target; no PR until evidence obligations are met |
| Local Beck--Chevalley hierarchy | Superseded as an upstream design direction |
| Guitart-exact interoperability | Active differential-audit target |
| Tactics | Remain local until a primitive missing API is established |

## 8. Stop conditions

The EndKan track should produce **no Mathlib PR** if the replacement two-parameter construction
turns out to be a thin restatement of existing categorical Fubini machinery, requires unnatural
hypotheses, or lacks a real downstream consumer.

A negative gap audit is a successful research result. The objective is durable upstream value, not
PR count.

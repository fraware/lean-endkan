# Acceptance packet for the minimal `endBifunctor` proposal

## Packet identity

- Evidence packet `E-END-002`
- Repository `fraware/lean-endkan`
- Target Lean and Mathlib version `v4.31.0`
- Candidate branch `agent/narrow-end-bifunctor-api`
- Decision state `ESCALATE AND NARROW`

## Claim under review

A named adapter from `F : Cᵒᵖ × C ⥤ D` to the curried functor consumed by Mathlib's end API, together with three general object and map simplification lemmas, provides useful downstream value while avoiding a parallel diagonal-end API.

## Candidate surface

1. `endBifunctor`
2. `endBifunctor_fiber_obj`
3. `endBifunctor_obj_map`
4. `endBifunctor_map_app`

The candidate derives `endBifunctor_obj_obj` locally from the general fiber equation.

## Real downstream consumer

The selected consumer is the Fubini layer in `EndKan.Fubini`.

### Consumer A

`EndKan.Fubini.end_fubini_beta` proves the computation rule for the universal morphism used by Fubini diagrams.

Current proof path

```lean
EndKan.Fubini.end_fubini_beta f h c
```

Underlying EndKan path

```lean
EndKan.End.end_beta f h c
```

Narrowed Mathlib path

```lean
exact Limits.end_.lift_π (F := endBifunctor F) f h c
```

The comparison shows that Mathlib already owns the β theorem. The missing interface is the product-to-curried adapter.

### Consumer B

`EndKan.Fubini.Slice` currently declares local product-index normalization theorems for the curried functor.

- `endBifunctor_fiber_obj_wedge`
- `endBifunctor_obj_map_wedge`
- `endBifunctor_map_app_wedge`

The proposed general simp lemmas cover all three proof shapes. The off-diagonal slice use also provides evidence for publishing `fiber_obj` and deriving the diagonal-only object lemma.

## Before and after assessment

| Dimension | Broad proposal | Narrowed proposal |
|---|---:|---:|
| Proposed public declarations | More than fifteen | Four |
| New structures | Up to two | Zero |
| New universal-property wrappers | Several | Zero |
| New β and η aliases | Several | Zero |
| Dedicated namespace or module hierarchy | Proposed | Deferred |
| Demonstrated real downstream consumers | Zero | Two proof shapes in Fubini |
| Existing Mathlib theorem reused for β | Indirectly | Directly |

## Acceptance gates

### Mechanical gates

- [ ] `lake build Scratch.MathlibEndBifunctorConsumer`
- [ ] `lake build Scratch.MathlibEndBetaExamples`
- [ ] `lake build EndKan`
- [ ] repository acceptance script passes
- [ ] no `sorry`, `admit`, additional axioms, or local options are introduced by the candidate

### API gates

- [x] candidate contains exactly one adapter
- [x] candidate contains three general simp lemmas
- [x] diagonal object equality is derived from the general fiber lemma
- [x] no new wedge or cowedge structure is proposed
- [x] no new end object, projection, lift, uniqueness, map, β, or η wrapper is proposed
- [x] no new namespace hierarchy is required for the first PR

### Utility gates

- [x] one existing Fubini β theorem maps directly to `end_.lift_π`
- [x] one existing Fubini slice normalization family maps to the candidate simp lemmas
- [ ] the candidate removes or replaces duplicate local Fubini normalization lemmas in a controlled follow-up
- [ ] at least one external Mathlib maintainer confirms that the adapter solves a recognizable interface problem

### Review gates

- [ ] maintainer decision on the name `endBifunctor`
- [ ] maintainer decision on placement in `End.lean` or an adjacent module
- [ ] maintainer confirmation that the three simp normal forms are desirable
- [ ] maintainer confirmation that the broad diagonal-end API should remain deferred

## Utility ledger

| Measure | Baseline | Current evidence | Acceptance threshold |
|---|---:|---:|---:|
| Trusted progress per review hour | 0 | Unmeasured | Positive after maintainer review |
| Real downstream theorem families | 0 | 2 | At least 1 |
| Public declarations proposed | More than 15 | 4 | At most 5 |
| Existing Mathlib declarations reused | Partial | `end_.lift_π` plus the core end API | Direct reuse required |
| Duplicate local normalization families covered | 0 | 1 family with 3 lemmas | At least 1 family |
| Maintainer decisions required | Several architectural questions | 2 focused questions | At most 3 |

The utility ledger does not assign a positive trusted-progress score before external review. The current packet establishes evidence of use and a bounded review surface.

## Failure and falsification conditions

The candidate should be rejected or revised if any of the following occurs.

- Mathlib maintainers consider `curry.obj F` sufficiently discoverable without a named adapter.
- The proposed simp lemmas conflict with established normal forms or trigger undesirable rewriting.
- The candidate consumer fails to build under Mathlib `v4.31.0`.
- The off-diagonal object equation is judged too specialized for the end module.
- A smaller surface, such as the adapter alone, supports the same consumers with comparable readability.
- Maintainers prefer a general currying API outside the end namespace that subsumes this proposal.

## Current conclusion

The broad End β and η extraction is unsupported as a first PR. The minimal adapter proposal has direct downstream evidence, a four-declaration review surface, and a clear falsification path. Submission should follow only after the mechanical gates pass and the focused maintainer question receives a favorable answer.

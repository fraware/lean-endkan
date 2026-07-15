# Acceptance packet for the minimal `endBifunctor` proposal

## Packet identity

- Evidence packet `E-END-002`
- Repository `fraware/lean-endkan`
- Target Lean and Mathlib version `v4.31.0`
- Candidate branch `agent/narrow-end-bifunctor-api`
- Decision state `ESCALATE AND NARROW`

## Claim under review

A named adapter from `F : Cᵒᵖ × C ⥤ D` to the curried functor consumed by Mathlib's end API, together with three general object and map equations, provides bounded downstream value without creating a parallel diagonal-end API.

## Candidate surface

1. `endBifunctor`
2. `endBifunctor_fiber_obj`
3. `endBifunctor_obj_map`
4. `endBifunctor_map_app`

The candidate derives the diagonal equation `endBifunctor_obj_obj` locally from the general fiber equation.

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
exact Limits.end_.lift_π
  (F := endBifunctor F) f (fun _ _ g => h g) c
```

The comparison establishes that Mathlib already owns the β theorem. The adapter supplies the functor shape expected by the existing end API.

### Consumer B

`EndKan.Fubini.Slice` currently declares three local product-index equations for the curried functor.

- `endBifunctor_fiber_obj_wedge`
- `endBifunctor_obj_map_wedge`
- `endBifunctor_map_app_wedge`

The candidate file instantiates each proposed general equation at the Fubini product index. The off-diagonal slice use supports publishing the general `fiber_obj` equation and deriving the diagonal-only object equation locally.

## Evidence boundary discovered during validation

The three equations cover isolated object and map normalizations, while they do not by themselves normalize an entire dependent dinaturality equality through `simp only`.

The attempted whole-equation proof retained the hom target

```lean
X ⟶ ((curry.obj F).obj (op c)).obj c'
```

while the product-form goal used

```lean
X ⟶ F.obj (op c, c')
```

Lean therefore required additional dependent transport or a reformulated statement. The unsupported whole-equation claim was removed from the candidate instead of adding casts or another abstraction layer.

This finding narrows the utility claim. The proposal demonstrates direct equations for recurring slice terms and a direct bridge to Mathlib's universal-property API. It makes no claim that the simp set converts arbitrary dependent profunctor equations into product normal form.

## Before and after assessment

| Dimension | Broad proposal | Validated narrowed proposal |
|---|---:|---:|
| Proposed public declarations | More than fifteen | Four |
| New structures | Up to two | Zero |
| New universal-property wrappers | Several | Zero |
| New β and η aliases | Several | Zero |
| Dedicated namespace or module hierarchy | Proposed | Deferred |
| Demonstrated downstream proof shapes | Zero | One β proof and three slice equations |
| Existing Mathlib theorem reused for β | Indirectly | Directly |
| Whole dependent equation normalization | Implied | Explicitly unsupported |

## Acceptance gates

### Mechanical gates

- [x] `lake build Scratch.MathlibEndBifunctorConsumer`
- [ ] `lake build Scratch.MathlibEndBetaExamples`
- [x] `lake build EndKan`
- [ ] repository acceptance script passes
- [x] no `sorry`, `admit`, additional axioms, or local options are introduced by the candidate

The checked build gates were validated in pull-request CI on Lean and Mathlib `v4.31.0`.

### API gates

- [x] candidate contains exactly one adapter
- [x] candidate contains three general equations
- [x] diagonal object equality is derived from the general fiber equation
- [x] no new wedge or cowedge structure is proposed
- [x] no new end object, projection, lift, uniqueness, map, β, or η wrapper is proposed
- [x] no new namespace hierarchy is required for the first PR
- [x] the candidate avoids dependent transports and new equality-packaging machinery

### Utility gates

- [x] one existing Fubini β theorem maps directly to `end_.lift_π`
- [x] three existing Fubini slice equations map directly to the candidate equations
- [x] unsupported whole-equation simp behavior is excluded from the claim
- [ ] the candidate removes or replaces duplicate local Fubini equations in a controlled follow-up
- [ ] at least one external Mathlib maintainer confirms that the adapter solves a recognizable interface problem

### Review gates

- [ ] maintainer decision on the name `endBifunctor`
- [ ] maintainer decision on placement in `End.lean` or an adjacent module
- [ ] maintainer decision on which equations should carry the `simp` attribute
- [ ] maintainer confirmation that the broad diagonal-end API should remain deferred

## Utility ledger

| Measure | Baseline | Current evidence | Acceptance threshold |
|---|---:|---:|---:|
| Trusted progress per review hour | 0 | Unmeasured | Positive after maintainer review |
| Real downstream proof shapes | 0 | 4 | At least 1 |
| Public declarations proposed | More than 15 | 4 | At most 5 |
| Existing Mathlib declarations reused | Partial | `end_.lift_π` plus the core end API | Direct reuse required |
| Duplicate local equations covered | 0 | 3 | At least 1 |
| Unsupported convenience claims removed | 0 | 1 | Every observed failure reflected in scope |
| Maintainer decisions required | Several architectural questions | 3 focused questions | At most 3 |

The utility ledger assigns no positive trusted-progress score before external review. The current packet establishes a compiling candidate, a bounded review surface, direct downstream witnesses, and an explicit negative result.

## Confidence assessment

- Confidence that the broad diagonal-end API should stay out of the first Mathlib PR is above 90 percent.
- Confidence that a named adapter is worth discussing upstream is approximately 80 percent.
- Confidence that all three equations belong in the public API with `simp` attributes is approximately 60 percent.
- Confidence that the current four-declaration set is the final Mathlib design remains below the submission threshold until maintainer review.

## Failure and falsification conditions

The candidate should be rejected or reduced if any of the following occurs.

- Mathlib maintainers consider `curry.obj F` sufficiently discoverable without a named adapter.
- The proposed simp attributes conflict with established normal forms or trigger undesirable rewriting.
- The off-diagonal object equation is judged too specialized for the end module.
- The adapter alone supports the same consumers with comparable readability.
- Maintainers prefer a general currying API outside the end namespace that subsumes this proposal.
- Replacing the local Fubini equations produces no material readability or maintenance gain.

## Current conclusion

The broad End β and η extraction is unsupported as a first PR. The four-declaration adapter candidate compiles and has direct downstream witnesses, while its utility claim is limited to isolated object and map equations plus access to Mathlib's existing end theorems. The next decision belongs in a focused Mathlib maintainer discussion before any upstream code submission.

# Coend β/η — Mathlib upstream lemma map

Staging for the **second** Mathlib extraction PR (see `docs/EXTRACTION_LEDGER.md` §2).
Source: `EndKan.Coend.Core`, `EndKan.Coend.BetaEta`. Target Mathlib pin: `v4.31.0-rc1`.

## Mathlib overlap (already upstream)

These Mathlib lemmas make several EndKan wrappers **thin aliases**. Do not re-upstream
as new declarations; reference them in proofs and docstrings.

| Mathlib | Role |
|---------|------|
| `Limits.coend`, `Limits.coend.ι`, `Limits.coend.desc` | Coend object and universal morphisms |
| `Limits.coend.ι_desc`, `Limits.coend.condition`, `Limits.coend.hom_ext` | Dinaturality axioms and uniqueness |
| `Limits.coend.map`, `Limits.coend.ι_map`, `Limits.coend.map_id` | Functoriality |

## Lemma checklist (proposed upstream)

Status key: **ready** = minimal deps, no sorry, Mathlib naming plausible; **alias** = definitional
wrapper only; **review** = naming or API overlap needs Mathlib maintainer input; **defer** = not
for this PR.

| Status | EndKan name | Local path | Proposed Mathlib name | Proposed Mathlib path |
|--------|-------------|------------|----------------------|------------------------|
| ready | `coendSwap` | `src/EndKan/Coend/Core.lean` | `coendSwap` | `.../Coend/Diagonal.lean` |
| ready | `coendBifunctor` | Core | `coendBifunctor` | Diagonal |
| ready | `coendDiagonal` | Core | `coendDiagonal` (simp lemma) | Diagonal |
| ready | `coendDiagonal_app` | Core | `coendDiagonal_app` | Diagonal |
| ready | `coendBifunctor_map_app` | Core | `coendBifunctor_map_app` | Diagonal |
| ready | `coendBifunctor_obj_map` | Core | `coendBifunctor_obj_map` | Diagonal |
| ready | `coendNatTrans` | Core | `coendNatTrans` | Diagonal |
| review | `DinaturalTransformation` | Core | `DiagonalDinaturality` or reuse `DinaturalTransformation` on curried data | Diagonal |
| review | `DinaturalTransformation.ofDiagonal` | Core | `ofDiagonal` | Diagonal |
| ready | `eqToHom_symm_comp_mpr_diagonal` | Core | `eqToHom_symm_comp_mpr_diagonal` | Diagonal |
| ready | `mpr_hom_ιCurry` | Core | `mpr_hom_ιCurry` | Diagonal |
| alias | `CoendObj` | Core | `coendDiagonal` (abbrev `coend (coendBifunctor F)`) | Diagonal |
| alias | `ιCurry` | Core | `coendDiagonal.ι` or `coend.ι (coendBifunctor F)` | Diagonal |
| alias | `ι` | Core | `coendDiagonal.ιDiagonal` | Diagonal |
| alias | `dinatural` | Core | doc-only / packaging of `coend.condition` | Diagonal |
| alias | `desc` | Core | `coend.desc` on curried data | Diagonal |
| alias | `desc_ιCurry` | Core | `coend.ι_desc` | Diagonal |
| alias | `desc_ι` | Core | `ι_desc` via `eqToHom` bridge | Diagonal |
| alias | `uniq` | Core | `coend.hom_ext` | Diagonal |
| alias | `ιCurry_natural` | Core | `coend.condition` | Diagonal |
| alias | `ι_dinatural` | Core | diagonal `ι` dinaturality | Diagonal |
| alias | `map` | Core | `coend.map (coendNatTrans α)` | Diagonal |
| alias | `map_ιCurry` | Core | `coend.ι_map` | Diagonal |
| ready | `coend_beta` | `src/EndKan/Coend/BetaEta.lean` | `coendDiagonal.beta` | `.../Coend/BetaEta.lean` |
| ready | `coend_eta` | BetaEta | `coendDiagonal.eta` | BetaEta |
| alias | `coend_ιCurry_beta` | BetaEta | `coend.condition` | omit or one-line alias |
| ready | `coend_ι_beta` | BetaEta | `coendDiagonal.ι_beta` | BetaEta |
| defer | `coend_ι_eta` | BetaEta | — | trivial `rfl`; omit from PR |
| alias | `coend_map_ιCurry` | BetaEta | `coend.ι_map` | omit or one-line alias |
| defer | `coend_map_id` | BetaEta | — | use `coend.map_id` |

## Dependency graph (Mathlib imports only)

```
Mathlib.CategoryTheory.Limits.Shapes.End          (existing; coend API)
Mathlib.CategoryTheory.Functor.Currying           (existing)
Mathlib.CategoryTheory.Products.Basic             (existing)
Mathlib.CategoryTheory.Whiskering                 (existing)
Mathlib.CategoryTheory.EqToHom                    (existing)
        │
        ▼
Mathlib.CategoryTheory.Limits.Shapes.Coend.Diagonal  (new)
        │
        ▼
Mathlib.CategoryTheory.Limits.Shapes.Coend.BetaEta   (new)
        │
        ▼
Mathlib.CategoryTheory.Limits.Shapes.Coend.Examples  (new; no downstream imports)
```

## Not in scope for PR #2

- EndKan tactics (`coend_beta`, `coend_eta`, `endkan_beta`, …)
- Fubini (`EndKan.Fubini.*`)
- Concrete instance lemmas that rely on automation
- `coend_ι_eta` (reflexivity placeholder)
- `coend_map_id` (use Mathlib `coend.map_id`)

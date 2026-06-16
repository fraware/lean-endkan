# Draft Mathlib module structure — nested Fubini

Proposed layout under `Mathlib/CategoryTheory/Limits/Shapes/`:

```
End/Fubini/
  Slice.lean      -- endSliceEmbed, endInnerMap, wedge indexing
  Nested.lean     -- endOuterProfunctor, endFubiniIso
  Examples.lean   -- constant / representable instances (hypothesis discharge)
Coend/Fubini/
  Slice.lean
  Nested.lean
  Examples.lean
```

## PR sequencing (recommended)

1. **Slice lemmas only** — embedding, inner end, `d`-action, `endSlice_cov_contr`
2. **Nested iso** — `endFubiniIso` under explicit `AllEndSliceContrIso`-style class
3. **Design issue** — unconditional contr-leg iso / remove hypothesis class

## Namespace sketch (`End/Fubini/Slice.lean`)

```lean
namespace CategoryTheory.Limits

variable {C D E : Type*} [Category C] [Category D] [Category E]

abbrev EndIdx (C D : Type*) [Category C] [Category D] :=
  Prod ((C × D)ᵒᵖ) (C × D)

def endWedge (c : C) (d : D) : EndIdx C D := (op (c, d), c, d)

def endSliceEmbed (d : D) : Cᵒᵖ × C ⥤ EndIdx C D := ...

def endSlice (F : EndIdx C D ⥤ E) (d : D) : Cᵒᵖ × C ⥤ E := endSliceEmbed d ⋙ F

-- inner end, endInnerMap, endSlice_cov_contr, ...

end CategoryTheory.Limits
```

## Extraction boundary (document in Mathlib PR)

On Lean 4.31-rc1, default `[IsIso (endSliceContrMap …)]` instances require a mutual
fixpoint that the kernel rejects. Mathlib should either:

- accept a typeclass `EndSliceContrIso` per profunctor, or
- wait for a cov-only inner-map API that avoids bootstrap isos.

EndKan documents both in `Slice.lean` `sliceIsoBootstrap` and `scratch/SliceIsoMin.lean`.

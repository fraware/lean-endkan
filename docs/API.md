# EndKan API reference

> **Note:** This overview is edited by hand. When you add or change public names or tactics, update this file too. See [BUILDING_DOCS.md](BUILDING_DOCS.md).

## Core types

### Ends
- `EndObj F` — The end of a functor F : Cᵒᵖ × C ⥤ D
- `End.π F c` — Projection from the end to F(c,c)
- `End.lift f h` — Universal property of ends
- `End.map α` — Functoriality of ends

### Coends
- `CoendObj F` — The coend of a functor F : C × Cᵒᵖ ⥤ D
- `Coend.ι F c` — Inclusion from F(c,c) to the coend
- `Coend.desc f h` — Universal property of coends
- `Coend.map α` — Functoriality of coends

### Kan extensions
- `Lan K F` — Left Kan extension of F along K
- `Ran K F` — Right Kan extension of F along K
- `Lan.universal α` — Universal property of left Kan extensions
- `Ran.universal α` — Universal property of right Kan extensions

### Beck–Chevalley
- `BeckChevalley.Square K L M N` — Commutative square of functors
- `BeckChevalley S` — Beck–Chevalley condition for a square
- `beckChevalleyIso` — Beck–Chevalley isomorphism

## Tactics

See [TACTIC_INDEX.md](TACTIC_INDEX.md) for every registered tactic, including variants with `!` and combined tactics.

### End tactics
- `end_beta` — β-style step for ends
- `end_eta` — η-style step for ends
- `endkan_beta` — Combined end/coend β-style step
- `endkan_eta` — Combined end/coend η-style step

### Coend tactics
- `coend_beta` — β-style step for coends
- `coend_eta` — η-style step for coends

### Kan tactics
- `kan_fuse` — Use known universal properties for Kan extensions
- `beck_chevalley!` — Beck–Chevalley on a declared square

### Combined tactics
- `endkan_all` — Run the combined pipeline

## Attributes

- `@[kan.square]` — Mark a commutative square for Beck–Chevalley tactics

## Configuration

### Options
- `endkan.timeoutMs` — Timeout in milliseconds (default: 2000)
- `endkan.trace` — Tracing on or off (default: false)
- `endkan.maxSteps` — Step limit (default: 200)

### Functions
- `setTimeout ms` — Set timeout
- `setTrace b` — Set tracing
- `setMaxSteps n` — Set step limit

## Examples

### End
```lean
example (F : Cᵒᵖ × C ⥤ D) (c : C) :
  End.lift (fun c => f c) h ≫ End.π F c = f c := by
  end_beta
```

### Coend
```lean
example (F : C × Cᵒᵖ ⥤ D) (c : C) :
  Coend.ι F c ≫ Coend.desc f h = f c := by
  coend_beta
```

### Kan extension
```lean
example (K : C ⥤ D) (F : C ⥤ E) (hK : Full K) (hK' : Faithful K) :
  Lan K F ≅ F := by
  kan_fuse
```

### Beck–Chevalley
```lean
example (S : BeckChevalley.Square K L M N) [BeckChevalley S] :
  M ⋙ Lan L (𝟙 E) ≅ Lan K (𝟙 D) ⋙ N := by
  beck_chevalley!
```

### Fubini-style sketch
```lean
example (F : (C × D)ᵒᵖ × (C × D) ⥤ E) :
  EndObj F ≅ EndObj (fun c => EndObj (fun d => F.obj (op (c, d), (c, d)))) := by
  endkan_beta
  endkan_eta
  simp
```

## Performance

Tactics are meant for **interactive** proofs. Speed depends on your goal and context.

## Rust command-line tool

The program under `rust_production` can print simple health and timing messages. You do **not** need it to use the Lean library.

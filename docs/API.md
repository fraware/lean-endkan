# EndKan API Reference

## Core Types

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

### Kan Extensions
- `Lan K F` — Left Kan extension of F along K
- `Ran K F` — Right Kan extension of F along K
- `Lan.universal α` — Universal property of left Kan extensions
- `Ran.universal α` — Universal property of right Kan extensions

### Beck-Chevalley
- `BeckChevalley.Square K L M N` — Commutative square of functors
- `BeckChevalley S` — Beck-Chevalley condition for a square
- `beckChevalleyIso` — Beck-Chevalley isomorphism

## Tactics

### End Tactics
- `end_beta` — β-reduction for ends
- `end_eta` — η-expansion for ends
- `endkan_beta` — Combined end/coend β-reduction
- `endkan_eta` — Combined end/coend η-expansion

### Coend Tactics
- `coend_beta` — β-reduction for coends
- `coend_eta` — η-expansion for coends

### Kan Tactics
- `kan_fuse` — Fuses Kan constructions via known universal properties
- `beck_chevalley!` — Check/apply Beck-Chevalley on a declared square

### Combined Tactics
- `endkan_all` — All tactics combined

## Attributes

### Kan Square Attribute
- `@[kan.square]` — Registers a commutative square with Beck-Chevalley conditions

## Configuration

### Options
- `endkan.timeoutMs` — Timeout in milliseconds (default: 2000)
- `endkan.trace` — Enable/disable tracing (default: false)
- `endkan.maxSteps` — Maximum number of steps (default: 200)

### Configuration Functions
- `setTimeout ms` — Set timeout
- `setTrace b` — Set tracing
- `setMaxSteps n` — Set maximum steps

## Examples

### Basic End Usage
```lean
example (F : Cᵒᵖ × C ⥤ D) (c : C) :
  End.lift (fun c => f c) h ≫ End.π F c = f c := by
  end_beta
```

### Basic Coend Usage
```lean
example (F : C × Cᵒᵖ ⥤ D) (c : C) :
  Coend.ι F c ≫ Coend.desc f h = f c := by
  coend_beta
```

### Kan Extension Usage
```lean
example (K : C ⥤ D) (F : C ⥤ E) (hK : Full K) (hK' : Faithful K) :
  Lan K F ≅ F := by
  kan_fuse
```

### Beck-Chevalley Usage
```lean
example (S : BeckChevalley.Square K L M N) [BeckChevalley S] :
  M ⋙ Lan L (𝟙 E) ≅ Lan K (𝟙 D) ⋙ N := by
  beck_chevalley!
```

### Fubini's Theorem
```lean
example (F : (C × D)ᵒᵖ × (C × D) ⥤ E) :
  EndObj F ≅ EndObj (fun c => EndObj (fun d => F.obj (op (c, d), (c, d)))) := by
  endkan_beta
  endkan_eta
  simp
```

## Performance

The library is designed to meet the following performance targets:
- P95 ≤ 500ms on the golden test suite
- Success ≥ 70% on canned naturality/Kan patterns without manual steps
- Deterministic behavior across multiple runs

## Telemetry

The library includes opt-in telemetry to collect:
- Counts and timings per tactic
- Number of components in ends/coends
- Success rates and performance metrics

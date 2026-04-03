import EndKan.End.Core
import EndKan.End.BetaEta
import EndKan.Coend.Core
import EndKan.Coend.BetaEta
import EndKan.Fubini
import EndKan.Kan.Core
import EndKan.Kan.BeckChevalley
import EndKan.Tactics
import EndKan.Attr
import EndKan.Telemetry
import EndKan.Optimization
import EndKan.Configuration
import EndKan.Monitoring
import EndKan.Regression

/-- EndKan — tactics and definitions for ends, coends, Kan extensions, and Beck–Chevalley in Lean 4.

## Tactics (overview)

- `end_beta`, `end_eta`, `coend_beta`, `coend_eta` — β/η-style steps for ends and coends
- `kan_fuse`, `beck_chevalley!` — Kan extensions and Beck–Chevalley squares
- `endkan_smart`, `endkan_debug` — try several shapes or print what was found
- Names ending in `!` or `!!` — same ideas with clearer error messages when something fails

See `docs/TACTIC_INDEX.md` in the repository for the full list.

## Options

- `setTimeout`, `setTrace`, `setMaxSteps`, `setDebug`, `setAggressive` — control timeouts, logging, and search depth

## Optional demo modules

Modules such as `EndKan.Telemetry`, `EndKan.Monitoring`, and `EndKan.ProductionBenchmarks` support **demos and tests**
(printing sample reports, simple timing). They are not required for the core mathematics.

## Quick examples

```lean
import EndKan

example (F : Cᵒᵖ × C ⥤ D) (c : C) :
  End.lift (fun c => f c) h ≫ End.π F c = f c := by
  endkan_smart

example (K : C ⥤ D) (F : C ⥤ E) (hK : Full K) (hK' : Faithful K) :
  Lan K F ≅ F := by
  kan_fuse!

example (S : BeckChevalley.Square K L M N) [BeckChevalley S] :
  M ⋙ Lan L (𝟙 E) ≅ Lan K (𝟙 D) ⋙ N := by
  endkan_debug
```

## Dependencies

- Lean 4 and Mathlib (category theory)

## License

Apache License 2.0
-/

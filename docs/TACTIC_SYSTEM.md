# EndKan Tactic System Documentation

> **Note:** Updated by hand. For every user-facing tactic name, see [TACTIC_INDEX.md](TACTIC_INDEX.md) and `src/EndKan/Tactics.lean`.

## Overview

EndKan adds tactics for category theory in Lean 4: it looks at the goal, picks a strategy (ends, coends, Kan extensions, Beck–Chevalley, and related shapes), and applies rewrite-style steps. Errors and timeouts are handled in [`ErrorHandling.lean`](../src/EndKan/ErrorHandling.lean).

## Architecture

### Core Components

1. **Tactics** (`src/EndKan/Tactics.lean`) — goal inspection and which rule to try next.  
2. **Transformations** (`src/EndKan/Transformation.lean`) — the actual rewrites and universal-property steps.  
3. **Errors** (`src/EndKan/ErrorHandling.lean`) — messages, timeouts, and step limits.

## Features

### Pattern Matching

The system automatically detects and categorizes goals into patterns:

- **End Patterns**: `EndObj`, `End.π`, `End.lift`, `End.map`
- **Coend Patterns**: `CoendObj`, `Coend.ι`, `Coend.desc`, `Coend.map`
- **Kan Extension Patterns**: `Lan`, `Ran`, `Lan.universal`, `Ran.universal`
- **Beck-Chevalley Patterns**: `Square`, `beckChevalleyIso`, etc.
- **Dinaturality Patterns**: `DinaturalTransformation`
- **Functor Composition Patterns**: `Functor.comp`, `Functor.map`
- **Natural Transformation Patterns**: `NatTrans`, `NatTrans.app`
- **Limit/Colimit Patterns**: `LimitCone`, `ColimitCocone`, etc.

### Transformation Strategies

Each pattern has associated transformation strategies:

#### End Transformations
- `end_beta`: β-reduction for ends
- `end_eta`: η-expansion for ends
- `end_comp`: Composition rules
- `end_universal`: Universal property applications

#### Coend Transformations
- `coend_beta`: β-reduction for coends
- `coend_eta`: η-expansion for coends
- `coend_comp`: Composition rules
- `coend_universal`: Universal property applications

#### Kan Extension Transformations
- `kan_fuse`: Fusion rules
- `kan_universal`: Universal property applications
- `kan_preserves`: Preservation properties

#### Beck-Chevalley Transformations
- `beck_chevalley`: Basic Beck-Chevalley
- `beck_chevalley_comp`: Composition rules

### Error Handling

#### Error Types
- `timeout`: Operation exceeded time limit
- `maxStepsReached`: Maximum transformation steps reached
- `patternMatchFailed`: Pattern recognition failed
- `transformationFailed`: Transformation application failed
- `invalidGoal`: Goal is not suitable for the tactic
- `dependencyMissing`: Required dependencies not available
- `typeMismatch`: Type checking failed
- `proofSearchFailed`: Proof search unsuccessful
- `resourceExhausted`: System resources exhausted
- `unsupportedPattern`: Pattern not supported

#### Rough priority labels
- `low` — minor (for example unsupported pattern)
- `medium` — normal failure (rewrite did not apply)
- `high` — time or step limit hit
- `critical` — missing dependency or similar hard stop

### Configuration Options

```lean
structure EndKanConfig where
  timeoutMs : Nat := 2000        -- Timeout in milliseconds
  trace : Bool := false          -- Enable tracing
  maxSteps : Nat := 200          -- Maximum transformation steps
  debug : Bool := false          -- Enable debug mode
  aggressive : Bool := false     -- Enable aggressive transformations
```

## Usage

### Basic Tactics

```lean
-- End transformations
end_beta
end_eta

-- Coend transformations
coend_beta
coend_eta

-- Kan extension transformations
kan_fuse

-- Beck-Chevalley transformations
beck_chevalley!
```

### Variants that report more detail on failure

```lean
end_beta!
end_eta!
coend_beta!
coend_eta!
kan_fuse!
beck_chevalley!!
```

### Automatic and debug tactics

```lean
endkan_smart
endkan_debug
```

### Combined tactics

```lean
endkan_beta
endkan_eta
endkan_all
```

### Configuration

```lean
-- Set timeout
setTimeout 5000

-- Enable tracing
setTrace true

-- Set maximum steps
setMaxSteps 500

-- Enable debug mode
setDebug true

-- Enable aggressive mode
setAggressive true
```

## Examples

### Basic End β-reduction

```lean
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D] 
        (f : ∀ c : C, D.obj (op c, c)) (h : ∀ {c c' : C} (g : c ⟶ c'), f c ≫ F.map (op g, g) = f c') (c : C) :
  End.lift f h ≫ End.π F c = f c := by
  end_beta
```

### Using `endkan_smart`

```lean
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D] 
        (G : C × Cᵒᵖ ⥤ D) [HasCoproductsOfShape C D] [HasWideCoequalizers D] :
  EndObj F ≅ EndObj F ∧ CoendObj G ≅ CoendObj G := by
  constructor
  · endkan_smart
  · endkan_smart
```

## Performance

Tactics are meant for **interactive** proofs. Speed depends on your goal and Mathlib version.

## Testing

Lean tests and the runner live under `src/EndKan/` (for example `UnitTests/`, `IntegrationTests/`, `TestRunner.lean`). Benchmark Lean files are under `bench/` if present.

### Commands

```bash
lake build
lake exe test
lake exe run_tests
lake exe test-runner -- dev unit
```

See [tests/README.md](../tests/README.md) for more.

## Where to read the code

- Goal classification and tactics: `src/EndKan/Tactics.lean`  
- Rewrites and rules: `src/EndKan/Transformation.lean`  
- Errors and limits: `src/EndKan/ErrorHandling.lean`  

The real definitions differ from any informal sketch; open these files for accurate names and behavior.

## Extending the system

- New goal shapes: extend the pattern type and recognition code in the tactics layer.  
- New rewrites: hook them into the transformation module and add tests under `src/EndKan/`.  
- New options: extend the configuration structure and document them in [API.md](API.md).

## Contributing

See [CONTRIBUTING.md](../CONTRIBUTING.md). When you add patterns or tactics, add tests and update the docs in `docs/`.

## License

This project is licensed under the Apache License 2.0.

## Questions

Open an issue on the project repository or see [CONTRIBUTING.md](../CONTRIBUTING.md).

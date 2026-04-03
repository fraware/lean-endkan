# Maintaining documentation

HTML documentation is **not** generated automatically for this repository. These files are edited directly when the library changes:

- [API.md](API.md) — public names and tactics  
- [TACTIC_SYSTEM.md](TACTIC_SYSTEM.md) — how the tactic layer is organized  

## Optional generated docs later

You can later add a standard Lean documentation generator ([doc-gen4](https://github.com/leanprover/doc-gen4)) so API pages build in automation. That would mean:

1. Adding the generator as a dependency compatible with your Lean and Mathlib versions.  
2. Adding a build step that produces HTML.  
3. Optionally uploading or publishing those files (for example as a static site).

Until then, keep module comments in `src/EndKan/` accurate and refresh the markdown above when you change the public surface.

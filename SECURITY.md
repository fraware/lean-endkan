# Security policy

## Supported versions

Security fixes are applied to the default branch (`main`) when practical. There are no separate long-term support release lines at this time.

## Reporting a vulnerability

Please **do not** open a public issue for undisclosed security problems.

Instead, contact the maintainers privately (for example via GitHub Security Advisories for this repository, if enabled, or the contact method listed in the repository settings).

Include:

- A short description of the issue and its impact
- Steps to reproduce (if applicable)
- Affected components (Lean library, Rust CLI, CI, etc.)

We aim to acknowledge reports within a few business days.

## Rust dependencies

Automated checks on the Rust code in `rust_production` include dependency security scanning and license rules defined in [`rust_production/deny.toml`](rust_production/deny.toml).

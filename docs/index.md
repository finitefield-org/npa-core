# NPA User Documentation

The canonical user documentation index is [docs/README.md](README.md).

The current core implementation emits only `NPA-CERT-0.4.0` /
`NPA-Core-0.4.0`, and both independent checkers accept only that pair. The
package ecosystem and public CLI use v0.9.0. The last
published external toolchain tag remains v0.2.0 until a new release is
published; see the canonical index for the separate source,
checker-capability, input-pair, and package-profile axes.

This file is a stable alias for tools, links, and public-readiness scans that
look for `docs/index.md`.

The current reference also documents the advisory targeted command
`build-certs --build-check-cache local-hit`. It is a local-only authoring cache,
not `verify-certs --audit-cache local-hit`, and neither mode can replace the
cache-off canonical/source-free completion and release gates.

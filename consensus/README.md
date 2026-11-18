# commonware-consensus

[![Crates.io](https://img.shields.io/crates/v/commonware-consensus.svg)](https://crates.io/crates/commonware-consensus)

Order opaque messages in a Byzantine environment.

## Status

Stability varies by primitive. See [README](https://github.com/commonwarexyz/monorepo#stability) for details.

## Extension Agreement

This fork includes experimental Simplex vote extensions and interpretation
recovery. See the [agreement guide](src/simplex/extension/agreement/README.md)
for authenticated subjects, issuance and recovery boundaries, supported profiles,
and focused tests. The general-committee foundation is not an activated recovery
service.

# Simplex Extension Agreement

Authenticate application interpretation alongside native Simplex voting.

## Status

**ALPHA.** This fork contains multiple experimental profiles. Their encoded
messages, verification capabilities, journal records, and recovery certificates
are not interchangeable. Use a fresh, explicitly configured profile; do not
clear old signing history to change profiles.

- `phase2::Extended` is the retained integration. Its recovery verifier requires
  an attributable scheme and `n > 5f`. It does not support seven validators with
  `f = 2`.
- `agreement` contains fixed-seven foundations. Their evidence and tests do not
  activate a seven-validator Engine/Marshal recovery path.
- `agreement::general` and `phase2::general::General` contain general-committee
  authentication, checked assembly, issuance, history, and recovery-verification
  foundations. The declared resource domain is 4 through 64 equal-weight
  validators, `f = floor((n - 1) / 3)`, and `q = n - f`. This API domain is not
  an operating-support claim. The native General voter exposes the original
  SELECT, RECOVER, recovery ballots and timeout WISH through Readiness.
  Alignment collects recovery evidence and drives attempts.

### Read the initial recovery history

The voter arms a recovery-only clock when it first observes the admitted original
NQC, checked local input, native parent and leader together. A later readiness
request can provide that observation if custody became available after the NQC.
After one configured certification-timeout interval from this observation,
`Readiness::request_initial_history` freezes the local history and optional
report. The voter journals the entry, original NQC and reservation before
signing. It synchronizes the released outbox before returning RECOVER. The
first published notice fixes the report for that attempt.

Use `history_material(HistoryQuery::published(...))` to recover a lost reply.
Use its signed head to read the entry and individual pages. This lookup also
works in a retained historical round and never invokes the signer. A replayed
reservation with no release receipt cannot publish a new signature. A RECOVER
notice authenticates the history owner and head. A caller must retrieve and
validate the referenced authorities before using the history to choose a value.

### Recover the interpretation of an included ancestor

Alignment uses the same Readiness requests after native finality passes the
original view. The voter resolves the nearest retained descendant finalization
and follows its authenticated parent round and payload digest back to the
requested cut. Each link requires a matching notarization, consecutive height,
domain, profile, roster and an existing locally journaled FIRST vote. Missing
links or an unresolved local signing history keep that issuer unavailable.

A verified ancestor can enter interpretation recovery immediately. RECOVER,
WISH and recovery ballots use the original round's sole ledger and the same
journal synchronization and release checks as live recovery. The authority
does not admit SELECT or an old native FINAL. Marshal delivery independently
checks the final anchor, full block ancestry and terminal interpretation.

### Replace a stalled recovery coordinator

Configure the recovery-only timeout and a durable entry resolver before starting
the voter. After the initial RECOVER, request a WISH for the exact predecessor
artifact. Repeated calls leave the deadline fixed. The voter signs after expiry,
persists the receipt, and returns the same bytes on retry. A crash between the
reservation and its receipt leaves that signature unavailable.

Alignment collects WISHes from distinct validators and retains the complete
successor entry, including each signer's original entry proof. On a
`request_higher_history` call the voter verifies this graph and its quorum,
fences older ballots in the journal, then signs a new RECOVER. Restore the same
entry resolver before voter replay. For a WISH after the first handoff, both
live issuance and replay load the bounded predecessor graph through that
resolver. Missing ancestors prevent release. A successor entry alone authorizes no
PREPARE, COMMIT, native finalization or Marshal delivery.

## Agreement

Native Simplex owns proposal eligibility, parent/view transitions, nullification,
descendant finality, and the voting journal. Application policy validates the
exact input and interpretation. It cannot manufacture native finality.

The intended normal path retains two voting phases:

1. An original native first vote accompanies an authenticated application report
   or the profile's explicit absence representation.
2. The leader freezes the admitted original population and obtains application
   validation of its exact decision. Final voting binds that decision and its
   original native subject.

The current general foundation derives an authenticated Core and checks matching
original follower preferences for fast eligibility. That is this candidate's
rule, not a general property of deterministic selection. A separately proposed
selector-stability gate has not replaced it. Reports authenticate claims; they
do not prove completed execution or reusable state. No extra report wait or
native timer/quorum change is supplied by these helpers.

## Recovery

Recovery verification is implemented in `general/recovery.rs`, entry provenance
in `general/entry.rs`, and local issuance/history replay in `general/issuance.rs`
and `general/issuance/history.rs`.

| Step | Checked evidence and outcome |
| --- | --- |
| Entry | An exact original Core/input and bounded authenticated entry proof. A local timeout or a decoded message alone is insufficient. Native eligibility, timers, and durable entry installation remain owner responsibilities. |
| History | Exactly `q` distinct context-matching notices, with their complete hash-linked record prefixes and referenced material. Original reservations and released outbox records remain visible. Missing material, malformed transitions, or exhausted limits reject admission. |
| Final catch-up | A complete valid original or recovery terminal requires catch-up to its exact decision. A recovered interpretation terminal is not a native P-finality certificate. |
| Prepared carry | Carry the highest valid earlier recovery preparation certificate. A same-or-higher ballot certificate makes the proposed entry stale. Conflicting certificates reject admission. |
| Original carry | Without a required preparation certificate, the current candidate conservatively carries the unique authenticated original decision. Conflicting gated originals reject admission. |
| Fresh selection | The current verifier admits fresh application Build only when neither required preparation nor original authority is present. Build receives the frozen authenticated recovery rows; its output is independently checked. |
| Prepare | The coordinator signs the exact admitted proposal; `q` matching PREPARE signatures form its preparation certificate. |
| Commit | Retain and verify that complete preparation certificate before reserving COMMIT. `q` matching COMMIT signatures form the interpretation terminal. |

This is an evidence-verification/issuance foundation, not a running recovery
coordinator. Its dependency graph is bounded by encoded bytes, nodes, links,
verification work, and history/entry budgets. Verification rejects cycles and
incomplete dependencies before application callbacks can acquire authority.

Latest-route snapshots can accompany recovery notices without waiting for new
execution. They do not erase previous votes or independently authorize a fresh
decision. The newer proposed empty-terminal-history exclusion rule would allow
fresh selection despite a retained original authority when old finality is
proved impossible. That optimization is not implemented by this candidate:
absence of a terminal in a local lookup is never its proof.

## Issuance and Durability

Native-owned issuance separates reservation, journal synchronization, signing,
outbox publication, and replay. A caller must synchronize each required record
before using its signing permission. Lower-ballot fences revoke new permission;
they cannot retract a signature already reserved or released. An incomplete
signer call must remain conservatively represented after restart.

Verification capabilities belong to one local verification context. Deserialize
and reverify the original evidence after restart; a cached successful Boolean or
a token created by another context grants no signing authority. Restore retained
choices and publication records before allowing additional signing. A storage
failure requires reopening the affected owner.

The voting adapters retain exact native/application pairs. Marshal verifies the
mode-specific companion at fetched-finalization and explicit-floor admission.
Application delivery must additionally retain the exact interpretation and
native inclusion/ancestry witnesses. Interpretation recovery does not authorize
casting its terminal into a Plain certificate or releasing an application ACK.

## Testing

Run focused deterministic tests with the workspace's contributor tools:

```sh
just test -p commonware-consensus --test extension_agreement
just test -p commonware-consensus --test extension_mode
just test -p commonware-consensus --test extension_tracking
just test -p commonware-consensus --test extension_voter_round
just test -p commonware-consensus general
just test -p commonware-consensus companion
just test -p commonware-cryptography test_scoped_verifier
just clippy -p commonware-consensus
```

The `general_*` cases cover larger/slack rosters, exact subjects, entry/history
replay, missing/cyclic material, deterministic resource limits, prepared/final
carry, reservation replay, and context isolation. Actor/WAL/Marshal cases test
their own integration boundaries. Passing these component tests does not prove
arbitrary-retry safety/progress, activate general recovery, or establish network
performance. Complete service activation requires those separate proofs and
actual native-to-application recovery/delivery tests.

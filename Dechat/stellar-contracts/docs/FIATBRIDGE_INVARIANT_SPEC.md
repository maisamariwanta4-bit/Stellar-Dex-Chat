# FiatBridge Invariant Specification

This document is the **executable specification** for FiatBridge's accounting,
authorization, queue-ordering, and pause invariants. Each invariant is numbered,
described as a predicate, and mapped to the contract code that enforces it and
to the test module that verifies it.

---

## 1. Core Accounting Invariants

These three invariants are enforced at the end of every state-changing entry
point that touches token accounting by calling `FiatBridge::check_invariants`.
Violations abort the transaction with a typed error rather than committing
corrupt state.

### INV-A1: `total_deposited >= total_withdrawn`

```
∀ accepted transactions T:
  token_config.total_deposited ≥ token_config.total_withdrawn
```

**Where enforced**: `check_invariants` → returns `Error::InternalError` on
violation. Called from `deposit`, `withdraw`, `request_withdrawal`,
`execute_withdrawal`, `cancel_withdrawal`, `finalize_cancellation`,
`reclaim_expired_withdrawal`, and `withdraw_fees`.

**Assumption**: `total_deposited` is incremented exactly once per `deposit`
call by the transferred amount, and `total_withdrawn` is incremented exactly
once per outbound transfer.

**Test modules**:
- `test_deposit_invariants` — asserts after every accepted deposit
- `test_execute_withdrawal_invariants::test_execute_withdrawal_maintains_total_deposited_ge_total_withdrawn`
- `test_request_withdrawal_invariants::assert_core_accounting_invariants` (called in every test)
- `test_escrow_solvency_proptest` — asserts after every step in arbitrary operation sequences

---

### INV-A2: `net_deposited >= total_liabilities`

```
let net = total_deposited - total_withdrawn;
∀ accepted transactions T:
  net ≥ token_config.total_liabilities
```

**Where enforced**: `check_invariants` → returns `Error::InternalError`.
`request_withdrawal` also explicitly guards this before writing a new
liability: it rejects if `new_liabilities > net_deposited`.

**Assumption**: `total_liabilities` tracks the aggregate outstanding withdrawal
queue amount. Partial executions and cancellations reduce it by exactly the
amount transferred or refunded.

**Test modules**:
- `test_request_withdrawal_invariants::liabilities_accumulate_exactly_and_never_exceed_net_deposited`
- `test_request_withdrawal_invariants::liabilities_can_never_be_pushed_past_net_deposited`
- `test_execute_withdrawal_invariants::test_execute_withdrawal_maintains_net_deposited_ge_total_liabilities`
- `test_escrow_solvency_proptest::escrow_liabilities_never_exceed_balance`
- `test_withdrawal_lifecycle_model` — asserts after every model step

---

### INV-A3: `balance >= net_deposited`

```
let balance = token.balance(contract_address);
∀ accepted transactions T:
  balance ≥ (total_deposited - total_withdrawn)
```

**Where enforced**: `check_invariants` → returns `Error::InsufficientFunds`.
The `>=` comparison (not `==`) intentionally permits untracked extra balance
such as accrued fees not yet withdrawn.

**Assumption**: The token contract is a standard SEP-41 implementation.
`token.transfer` moves exactly `amount` from the contract to the recipient.
No fee-on-transfer or rebasing behavior is assumed. The contract verifies
this explicitly using pre/post balance checks in `execute_withdrawal`
(`ShortTransfer` / `TransferFailed` guards).

**Test modules**:
- `test_execute_withdrawal_invariants::test_execute_withdrawal_maintains_balance_ge_net_deposited`
- `test_escrow_solvency_proptest` — balance check in every step
- `test_withdrawal_lifecycle_model::assert_model_invariants` — balance check in every step

---

## 2. Per-Token Escrow Decomposition

```
token_balance == user_assets + fee_liability + unassigned_dust
```

Where:
- `user_assets` = `total_deposited - total_withdrawn` (net deposited)
- `fee_liability` = `FeeVault[token]` (accrued but not yet withdrawn fees)
- `unassigned_dust` = rounding remainder from fee calculations

The pending withdrawal queue amount (`total_liabilities`) is a subset of
`user_assets`. `get_token_escrow_accounting` computes this decomposition and
returns an error rather than a negative dust value.

**Where documented**: `TokenEscrowAccounting` struct (lib.rs)

**Test modules**:
- `test_withdraw_fees_invariants` — `withdraw_fees` never eats into `user_assets`
- `test_withdraw_fees_batch_invariants`

---

## 3. Queue-Ordering Invariants

### INV-Q1: Request IDs are monotonically increasing and never reused

```
∀ accepted request_withdrawal calls:
  request_id == pre_call_next_request_id
  post_call_next_request_id == pre_call_next_request_id + 1

∀ cancelled or reclaimed requests R:
  the slot R.request_id is never allocated again
```

**Where enforced**: `request_withdrawal` reads `DataKey::NextRequestID`,
uses that value as the new request ID, then writes `next + 1`.
`cancel_withdrawal`, `finalize_cancellation`, and `reclaim_expired_withdrawal`
remove the queue entry but never decrement or recycle the counter.

**Test modules**:
- `test_request_withdrawal_invariants::ids_are_allocated_in_order_and_never_reused`
- `test_request_withdrawal_invariants::ids_stay_dense_and_ordered_for_any_request_count` (proptest)
- `test_withdrawal_lifecycle_model::ids_are_monotonic_across_lifecycle`

---

### INV-Q2: Queue depth changes by exactly one per enqueue / dequeue

```
after request_withdrawal (accepted):
  queue_depth == pre_depth + 1

after execute_withdrawal (full), cancel_withdrawal, finalize_cancellation,
reclaim_expired_withdrawal (accepted):
  queue_depth == pre_depth - 1

after execute_withdrawal (partial):
  queue_depth == pre_depth  (the entry stays)
```

**Where enforced**: `WithdrawQueueLen` and `WithdrawQueueHead` are updated
atomically with the entry write/removal in every queue-mutating entry point.

**Test modules**:
- `test_request_withdrawal_invariants::queue_depth_grows_by_exactly_one_per_request`
- `test_execute_withdrawal_invariants::test_full_execute_withdrawal_removes_from_queue`
- `test_execute_withdrawal_invariants::test_partial_execute_withdrawal_invariants`
- `test_cancel_withdrawal_invariants`
- `test_withdrawal_lifecycle_model`

---

### INV-Q3: Scheduler priority ordering

```
∀ non-empty queues:
  get_next_priority_withdrawal() returns the request_id R such that
  aging_score(R) ≤ aging_score(R') for all queued R'

Where:
  age_intervals      = (current_ledger - queued_ledger) / RISK_AGING_INTERVAL_LEDGERS
  effective_tier     = max(0, risk_tier - age_intervals)
  aging_score        = effective_tier * (MAX_RISK_TIER + 1) + (MAX_RISK_TIER - min(age_intervals, MAX_RISK_TIER))
  tie-break:         by queued_ledger ASC, then request_id ASC
```

**Bound**: `aging_score ∈ [0, MAX_RISK_TIER * (MAX_RISK_TIER + 2)]` = `[0, 1088]`.

**Where enforced**: `get_next_priority_withdrawal` reads tier heads from
`TierQueueHead` / `TierQueueLen` per tier (bounded at `MAX_RISK_TIER + 1`
tiers).

**Test modules**:
- `test_get_next_priority_withdrawal_invariants`
- `test_aging_fairness`
- `test_withdrawal_lifecycle_model::scheduler_respects_tier_and_age_ordering`

---

### INV-Q4: `stored_request` faithfully reflects inputs

```
after request_withdrawal(to, amount, token, memo_hash, risk_tier):
  request.to == to
  request.token == token
  request.amount == amount
  request.memo_hash == memo_hash
  request.risk_tier == risk_tier
  request.queued_ledger == current_ledger
  request.unlock_ledger == current_ledger + lock_period
```

**Where enforced**: `request_withdrawal` constructs `WithdrawRequest` directly
from its arguments.

**Test modules**:
- `test_request_withdrawal_invariants::stored_request_reflects_its_inputs_faithfully`
- `test_request_withdrawal_invariants::unlock_ledger_always_trails_the_configured_lock_period` (proptest)

---

## 4. Authorization Invariants

### INV-Z1: Only admin or the configured withdraw-operator can execute / queue withdrawals

```
execute_withdrawal:    caller ∈ {admin, withdraw_operator, Role::Operator}
request_withdrawal:    caller.require_auth() gated by admin
withdraw:              caller ∈ {admin, withdraw_operator, Role::Operator}
```

**Where enforced**: every entry point calls `admin.require_auth()` or
`caller.require_auth()` with an explicit role check before any storage read
or write.

**Test modules**:
- `test_request_withdrawal_invariants::unauthorised_caller_queues_nothing`
- `test_withdraw_invariants`
- `test_role_capabilities`

---

### INV-Z2: Cancellation lifecycle requires the right actor at each step

```
request_cancellation:  caller ∈ {request.to, admin}
approve_cancellation:  caller == admin
finalize_cancellation: caller == admin
```

**Where enforced**: `request_cancellation` checks the caller against
`request.to` and `admin`. `approve_cancellation` / `finalize_cancellation`
each call `admin.require_auth()`.

**Test modules**:
- `test_cancellation_lifecycle_invariants::unauthorized_third_party_cannot_request_cancellation`
- `test_cancellation_lifecycle_invariants::non_admin_cannot_approve_cancellation`
- `test_cancellation_lifecycle_invariants::non_admin_cannot_finalize_cancellation`

---

### INV-Z3: Failure paths leave no partial state

```
∀ rejected calls to request_withdrawal, execute_withdrawal,
  request_cancellation, approve_cancellation, finalize_cancellation:
  (queue_depth, total_liabilities, total_deposited, total_withdrawn,
   next_request_id) are identical to their pre-call values
```

**Where enforced**: Soroban's transactional execution model rolls back all
storage writes on `Err` return. The contract never performs a side-effecting
external call before the authorization guard.

**Test modules**:
- `test_request_withdrawal_invariants::unregistered_token_rolls_back_the_queue_write`
- `test_request_withdrawal_invariants::over_balance_request_reserves_nothing`
- `test_request_withdrawal_invariants::denied_recipient_is_rejected_without_side_effects`
- `test_execute_withdrawal_invariants::test_execute_withdrawal_locked_leaves_no_state_change`
- `test_execute_withdrawal_invariants::test_execute_withdrawal_replay_protection_nonce_invariants`

---

## 5. Pause Invariants

### INV-P1: Global pause blocks all value-moving entry points

```
paused == true implies:
  deposit(...)          → Error::ContractPaused
  withdraw(...)         → Error::ContractPaused
  request_withdrawal(…) → Error::ContractPaused
  execute_withdrawal(…) → Error::ContractPaused
```

**Where enforced**: `is_paused!` guard at the top of each entry point.

**Test modules**:
- `test_pause_invariants` (not yet registered; tracked in issue #1380)

---

### INV-P2: Scoped pause blocks only its designated path

```
PauseScope::Deposits           → deposit blocked; others unaffected
PauseScope::WithdrawalRequests → request_withdrawal blocked; others unaffected
PauseScope::WithdrawalExecution → execute_withdrawal blocked; others unaffected
PauseScope::AdminTransfers     → withdraw + withdraw_fees blocked; others unaffected
```

**Where enforced**: `PauseState` struct; each path checks only its own flag.

**Test modules**:
- `test_pause_invariants::scoped_pause_blocks_only_its_path_and_preserves_recovery`
- `test_pause_invariants::deposit_scope_does_not_block_withdrawal_requests`
- `test_pause_invariants::request_scope_does_not_block_deposits`

---

### INV-P3: Cancellation and recovery paths remain available under any pause

```
∀ pause states P (global or scoped):
  request_cancellation(…) is accepted
  approve_cancellation(…) is accepted
  finalize_cancellation(…) is accepted
  cancel_withdrawal(…) is accepted
```

**Where enforced**: these entry points do not check the global or scoped pause
flags.

**Test modules**:
- `test_cancellation_lifecycle_invariants::paused_contract_allows_request_cancellation`
- `test_cancellation_lifecycle_invariants::paused_contract_allows_approve_cancellation`
- `test_cancellation_lifecycle_invariants::paused_contract_allows_finalize_cancellation`

---

## 6. Cancellation State-Machine Invariants

### INV-C1: Cancellation status advances exactly Requested → Approved → (deleted)

```
∀ request_id R with an active withdrawal:
  request_cancellation(R, _)   sets CancellationRequest.status = Requested
  approve_cancellation(R)      sets CancellationRequest.status = Approved
  finalize_cancellation(R)     removes CancellationRequest and WithdrawRequest
```

Skipping a step returns a typed error without mutating state.
Full execution, shortcut cancellation, and expiry reclaim remove the withdrawal
but leave an existing cancellation record in storage. Such an orphan can still
be approved, but finalization returns `RequestNotFound`; this compatibility
behavior is covered by `test_cancellation_lifecycle_invariants`.

**Where enforced**: each step reads the current `CancellationStatus` and
returns `CancellationNotRequested`, `CancellationAlreadyRequested`, or
`CancellationNotApproved` for out-of-sequence calls. `finalize_cancellation`
is the only path that deletes the cancellation record.

**Test modules**:
- `test_cancellation_lifecycle_invariants::full_lifecycle_request_approve_finalize`
- `test_cancellation_lifecycle_invariants::finalize_without_approval_is_rejected`
- `test_cancellation_lifecycle_invariants::approve_without_request_is_rejected`
- `test_withdrawal_lifecycle_model::cancellation_state_machine_is_one_way`

---

### INV-C2: Liabilities do not change before finalization

```
after request_cancellation:  total_liabilities == pre_call_value
after approve_cancellation:  total_liabilities == pre_call_value
after finalize_cancellation: total_liabilities == pre_call_value - request.amount
```

**Where enforced**: `request_cancellation` and `approve_cancellation` only
write `CancellationRequest`; they do not touch `TokenConfig`. Liability release
happens atomically in `finalize_cancellation`.

**Test modules**:
- `test_cancellation_lifecycle_invariants::full_lifecycle_request_approve_finalize`
- `test_cancellation_lifecycle_invariants::lifecycle_cancel_after_partial_payment_releases_residual_only`

---

## 7. Expiry Invariants

### INV-E1: A request expires only after `queued_ledger + expiry_window`

```
reclaim_expired_withdrawal(R):
  if current_ledger < R.queued_ledger + expiry_window → Error::WithdrawalLocked
  else → remove R, reduce total_liabilities by R.amount
```

**Where enforced**: `reclaim_expired_withdrawal` reads `WithdrawalExpiryWindow`
and compares against `request.queued_ledger`.

**Test modules**:
- `test_reclaim_expired_withdrawal_invariants::test_reclaim_not_expired_is_rejected`
- `test_reclaim_expired_withdrawal_invariants::test_reclaim_expired_withdrawal_decreases_liabilities`
- `test_withdrawal_lifecycle_model::expiry_requires_window_to_elapse`

---

## 8. Token Behavior Assumptions

The following assumptions about the token contract are **explicit and load-bearing**.
Any token that violates them may break the accounting invariants above.

| # | Assumption | Consequence if violated |
|---|-----------|-------------------------|
| T1 | `transfer(from, to, amount)` moves exactly `amount` units; no fee-on-transfer, no rebasing | INV-A3 may be violated; `ShortTransfer` / `TransferFailed` guards are the only runtime defense |
| T2 | `balance(address)` returns the current token units held; no delayed settlement | INV-A3 comparison in `check_invariants` may read stale data |
| T3 | The token is non-reentrant (no call-back into FiatBridge during `transfer`) | Authorization and state guards could be bypassed |
| T4 | `transfer` is atomic; it either completes fully or reverts | Partial transfers would corrupt `total_withdrawn` |

**Where documented in code**: `execute_withdrawal` explicitly compares
`balance_before - balance_after` against `execute_amount` and returns
`Error::ShortTransfer` or `Error::TransferFailed` if the amounts disagree.
`check_invariants` calls `token.try_balance` and returns
`Error::TokenInterfaceInvalid` if the call fails.
See also `test_token_conformance` for the SEP-41 conformance harness.

---

## 9. Ledger Time Assumptions

The contract uses `env.ledger().sequence()` (not wall-clock time) for all
time-dependent logic. The following assumptions are explicit:

| # | Assumption | Where used |
|---|-----------|------------|
| L1 | Ledger sequence increases monotonically (never decreases or repeats within a contract lifetime) | `unlock_ledger`, `expiry_window`, `rate_limit`, nonce windows |
| L2 | Ledger sequence advances by at most one per transaction | Anti-sandwich delay `last_deposit + delay > current` is a strict inequality |
| L3 | `WINDOW_LEDGERS` (17,280 ≈ 24 h) and `CIRCUIT_BREAKER_RESET_LEDGERS` (34,560 ≈ 48 h) assume a ~5-second average ledger close time | Misconfigured validator timing could stretch or compress windows |

**Consequence**: if a Stellar network upgrade changes average ledger time
significantly, the effective wall-clock durations of timelocks, cooldowns,
and rate-limit windows will change without any change to the contract's
numeric constants. No code changes in FiatBridge are needed, but operators
should be aware of this relationship.

---

## 10. Test-to-Invariant Coverage Matrix

| Test module | INV-A1 | INV-A2 | INV-A3 | INV-Q1 | INV-Q2 | INV-Q3 | INV-Q4 | INV-Z1 | INV-Z2 | INV-Z3 | INV-P1 | INV-P2 | INV-P3 | INV-C1 | INV-C2 | INV-E1 |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `test_request_withdrawal_invariants` | ✓ | ✓ | ✓ | ✓ | ✓ | | ✓ | ✓ | | ✓ | | | | | | |
| `test_execute_withdrawal_invariants` | ✓ | ✓ | ✓ | | ✓ | | | | | ✓ | ✓ | | | | | |
| `test_cancel_withdrawal_invariants` | ✓ | ✓ | ✓ | | ✓ | | | | | ✓ | | | | | | |
| `test_cancellation_lifecycle_invariants` | ✓ | ✓ | ✓ | | ✓ | | | | ✓ | | | | ✓ | ✓ | ✓ | |
| `test_reclaim_expired_withdrawal_invariants` | ✓ | ✓ | | | ✓ | | | | | | | | | | | ✓ |
| `test_pause_invariants` | ✓ | | | | | | | | | | ✓ | ✓ | ✓ | | | |
| `test_escrow_solvency_proptest` | ✓ | ✓ | ✓ | | | | | | | | | | | | | |
| `test_aging_fairness` | | | | | | ✓ | | | | | | | | | | |
| `test_get_next_priority_withdrawal_invariants` | | | | | | ✓ | | | | | | | | | | |
| `test_role_capabilities` | | | | | | | | ✓ | | | | | | | | |
| **`test_withdrawal_lifecycle_model`** | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | | | ✓ | ✓ | | | ✓ | ✓ | ✓ | ✓ |

Rows marked **bold** are new in this PR. See
[INVARIANT_TESTING.md](INVARIANT_TESTING.md) for contributor guidance on
extending this table.

---

## 11. Registering a New Invariant Test

See [INVARIANT_TESTING.md § Adding a new test module](INVARIANT_TESTING.md#adding-a-new-test-module)
for the step-by-step process. In brief:

1. Create `src/test_<name>.rs` with a `//!` module-level doc comment that lists
   which invariant IDs from this document the module asserts.
2. Add `#[cfg(test)] mod test_<name>;` to the end of `src/lib.rs`.
3. Update the coverage matrix in §10 of this document.
4. Run `cargo test test_<name>` to confirm the module is compiled and executed.

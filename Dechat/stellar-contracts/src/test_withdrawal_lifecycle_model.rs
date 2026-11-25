//! Stateful model-based tests for the complete withdrawal lifecycle (Issue #173).
//!
//! ## Goal
//!
//! Build a reference model that tracks the full withdrawal lifecycle — queue,
//! partial execution, cancellation, expiry, reclaim, and finalization — and
//! compare the contract's state and emitted events against that model after
//! every operation.
//!
//! ## Invariants asserted (see `docs/FIATBRIDGE_INVARIANT_SPEC.md`)
//!
//! * **INV-A1–A3** (core accounting): `total_deposited >= total_withdrawn`,
//!   `net_deposited >= total_liabilities`, `balance >= net_deposited`.
//! * **INV-Q1**: request IDs are strictly monotonic and never reused.
//! * **INV-Q2**: queue depth changes by exactly one per enqueue / dequeue.
//! * **INV-Q3**: the scheduler respects tier-and-age ordering.
//! * **INV-Z2**: cancellation lifecycle enforces the right caller at each step.
//! * **INV-Z3**: rejected calls leave no partial state.
//! * **INV-C1**: cancellation advances Requested → Approved → (deleted) on
//!   finalization; other terminal paths may leave an orphaned record.
//! * **INV-C2**: liabilities do not change before finalization.
//! * **INV-E1**: a request can only be reclaimed after the expiry window elapses.
//!
//! ## Strategy
//!
//! A `LifecycleModel` struct mirrors every piece of state the tests care about
//! using plain Rust types (`std::collections::HashMap`, integers). After every
//! operation the test asserts:
//!
//! 1. The model and the contract agree on accounting, queue, request, and
//!    cancellation state.
//! 2. Ordered FiatBridge event names match the model's expected outcomes.
//! 3. The applicable invariant predicates hold.
//!
//! Property tests sweep random sequences of operations using `proptest`. Targeted
//! example-based tests pin individual lifecycle paths and boundary conditions.
//!
//! Registered from `lib.rs` behind `#[cfg(test)]`.

#![cfg(test)]
extern crate std;

use std::collections::HashMap;

use crate::{CancellationStatus, Error, FiatBridge, FiatBridgeClient};
use proptest::prelude::*;
use soroban_sdk::{
    testutils::{Address as _, Events as _, Ledger},
    token,
    xdr::ContractEventBody,
    Address, Bytes, Env, Symbol, Vec,
};

// ── Constants ──────────────────────────────────────────────────────────────

const TOKEN_LIMIT: i128 = 1_000_000;
const MIN_DEP: i128 = 100;
const EXPIRY_WINDOW: u32 = 17_280;

// ── Helpers ────────────────────────────────────────────────────────────────

fn create_token_contract<'a>(
    env: &Env,
    admin: &Address,
) -> (token::Client<'a>, token::StellarAssetClient<'a>) {
    let contract_address = env.register_stellar_asset_contract_v2(admin.clone());
    (
        token::Client::new(env, &contract_address.address()),
        token::StellarAssetClient::new(env, &contract_address.address()),
    )
}

struct Ctx<'a> {
    bridge: FiatBridgeClient<'a>,
    contract_id: Address,
    token_addr: Address,
    token_client: token::Client<'a>,
    token_admin: token::StellarAssetClient<'a>,
    admin: Address,
    contract_event_baseline: usize,
    env: Env,
}

fn setup(env: &Env) -> Ctx<'_> {
    let admin = Address::generate(env);
    let (token_client, token_admin) = create_token_contract(env, &admin);
    let token_addr = token_client.address.clone();
    let contract_id = env.register(FiatBridge, ());
    let bridge = FiatBridgeClient::new(env, &contract_id);
    let mut signers = Vec::new(env);
    signers.push_back(admin.clone());
    bridge.init(
        &admin,
        &token_addr,
        &TOKEN_LIMIT,
        &MIN_DEP,
        &signers,
        &1,
        &0,
    );
    let contract_event_baseline = env
        .events()
        .all()
        .filter_by_contract(&contract_id)
        .events()
        .len();
    Ctx {
        bridge,
        contract_id,
        token_addr,
        token_client,
        token_admin,
        admin,
        contract_event_baseline,
        env: env.clone(),
    }
}

fn funded_user(ctx: &Ctx<'_>, deposit: i128) -> Address {
    let user = Address::generate(&ctx.env);
    ctx.token_admin.mint(&user, &(deposit * 2));
    ctx.bridge.deposit(
        &user,
        &deposit,
        &ctx.token_addr,
        &Bytes::from_slice(&ctx.env, b"seed"),
        &0,
        &0,
        &None,
    );
    user
}

// ── Reference model ────────────────────────────────────────────────────────

/// Mirror of the subset of contract state that the lifecycle model tracks.
#[derive(Clone, Debug, Default)]
struct LifecycleModel {
    /// Funds deposited by each user (address string key).
    user_deposited: HashMap<std::string::String, i128>,
    /// Active withdrawal requests: id → (user_key, amount).
    active_requests: HashMap<u64, (std::string::String, i128)>,
    /// Requests awaiting cancellation approval: id → amount_at_request.
    pending_cancellations: HashMap<u64, i128>,
    /// Requests with an approved-but-not-finalized cancellation.
    approved_cancellations: HashMap<u64, i128>,
    /// Ledger sequence at which each active request was queued.
    queued_ledgers: HashMap<u64, u32>,
    /// Requests that have been partially paid: id → remaining amount.
    partial_requests: HashMap<u64, i128>,
    /// Current total liabilities (sum of active request amounts).
    total_liabilities: i128,
    /// Total deposited across all users.
    total_deposited: i128,
    /// Total withdrawn (executed) across all requests.
    total_withdrawn: i128,
    /// Next expected request ID.
    next_id: u64,
    /// Ordered event names expected from successful modeled operations.
    expected_events: std::vec::Vec<&'static str>,
}

impl LifecycleModel {
    fn deposit(&mut self, user_key: std::string::String, amount: i128) {
        *self.user_deposited.entry(user_key).or_insert(0) += amount;
        self.total_deposited += amount;
        self.expected_events
            .extend(["deposit_event", "receipt_issued_event"]);
    }

    fn request_withdrawal(
        &mut self,
        user_key: std::string::String,
        amount: i128,
        queued_ledger: u32,
    ) -> Result<u64, ()> {
        let available = self.user_deposited.get(&user_key).copied().unwrap_or(0)
            - self
                .active_requests
                .values()
                .filter(|(k, _)| k == &user_key)
                .map(|(_, a)| *a)
                .sum::<i128>();
        let net_deposited = self.total_deposited - self.total_withdrawn;
        if amount <= 0 || amount > available || self.total_liabilities + amount > net_deposited {
            return Err(());
        }
        let id = self.next_id;
        self.next_id += 1;
        self.active_requests.insert(id, (user_key, amount));
        self.queued_ledgers.insert(id, queued_ledger);
        self.total_liabilities += amount;
        self.expected_events.push("withdrawal_requested_event");
        Ok(id)
    }

    fn execute_full(&mut self, id: u64) -> Result<i128, ()> {
        let amount = match self.partial_requests.remove(&id) {
            Some(remaining) => remaining,
            None => self.active_requests.get(&id).map(|(_, a)| *a).ok_or(())?,
        };
        self.active_requests.remove(&id);
        self.queued_ledgers.remove(&id);
        self.total_withdrawn += amount;
        self.total_liabilities -= amount;
        self.expected_events.push("withdrawal_executed_event");
        Ok(amount)
    }

    fn execute_partial(&mut self, id: u64, partial: i128) -> Result<(), ()> {
        let current = self
            .partial_requests
            .get(&id)
            .copied()
            .or_else(|| self.active_requests.get(&id).map(|(_, a)| *a))
            .ok_or(())?;
        if partial <= 0 || partial >= current {
            return Err(());
        }
        let remaining = current - partial;
        self.partial_requests.insert(id, remaining);
        // Update active_requests amount to remaining
        if let Some(entry) = self.active_requests.get_mut(&id) {
            entry.1 = remaining;
        }
        self.total_withdrawn += partial;
        self.total_liabilities -= partial;
        self.expected_events.push("withdrawal_executed_event");
        Ok(())
    }

    fn request_cancellation(&mut self, id: u64) -> Result<i128, ()> {
        if self.pending_cancellations.contains_key(&id)
            || self.approved_cancellations.contains_key(&id)
        {
            return Err(()); // duplicate
        }
        let amount = self
            .partial_requests
            .get(&id)
            .copied()
            .or_else(|| self.active_requests.get(&id).map(|(_, a)| *a))
            .ok_or(())?;
        self.pending_cancellations.insert(id, amount);
        self.expected_events.push("cancellation_requested_event");
        Ok(amount)
    }

    fn approve_cancellation(&mut self, id: u64) -> Result<(), ()> {
        let amount = self.pending_cancellations.remove(&id).ok_or(())?;
        self.approved_cancellations.insert(id, amount);
        self.expected_events.push("cancellation_approved_event");
        Ok(())
    }

    fn finalize_cancellation(&mut self, id: u64) -> Result<i128, ()> {
        if !self.approved_cancellations.contains_key(&id) {
            return Err(());
        }
        let amount = self
            .partial_requests
            .get(&id)
            .copied()
            .or_else(|| self.active_requests.get(&id).map(|(_, amount)| *amount))
            .ok_or(())?;
        self.approved_cancellations.remove(&id);
        self.active_requests.remove(&id);
        self.partial_requests.remove(&id);
        self.queued_ledgers.remove(&id);
        self.total_liabilities -= amount;
        self.expected_events
            .extend(["withdrawal_cancelled_event", "cancellation_finalized_event"]);
        Ok(amount)
    }

    fn reclaim_expired(&mut self, id: u64, current_ledger: u32) -> Result<i128, ()> {
        let queued_ledger = self.queued_ledgers.get(&id).copied().ok_or(())?;
        if current_ledger <= queued_ledger.saturating_add(EXPIRY_WINDOW) {
            return Err(());
        }
        let amount = self
            .partial_requests
            .get(&id)
            .copied()
            .or_else(|| self.active_requests.get(&id).map(|(_, a)| *a))
            .ok_or(())?;
        self.active_requests.remove(&id);
        self.partial_requests.remove(&id);
        self.queued_ledgers.remove(&id);
        self.total_liabilities -= amount;
        self.expected_events.push("withdrawal_expired_event");
        Ok(amount)
    }

    fn cancel_shortcut(&mut self, id: u64) -> Result<i128, ()> {
        let amount = self
            .partial_requests
            .get(&id)
            .copied()
            .or_else(|| self.active_requests.get(&id).map(|(_, a)| *a))
            .ok_or(())?;
        self.active_requests.remove(&id);
        self.partial_requests.remove(&id);
        self.queued_ledgers.remove(&id);
        self.total_liabilities -= amount;
        self.expected_events.push("withdrawal_cancelled_event");
        Ok(amount)
    }
}

/// Compare modeled accounting, queue, cancellation, and event state, then
/// assert INV-A1 through INV-A3.
fn assert_model_invariants(ctx: &Ctx<'_>, model: &LifecycleModel) {
    let on_dep = ctx.bridge.get_total_deposited();
    let on_with = ctx.bridge.get_total_withdrawn();
    let on_liab = ctx.bridge.get_total_liabilities();
    let on_bal = ctx.token_client.balance(&ctx.contract_id);

    // Model consistency.
    assert_eq!(
        model.total_deposited, on_dep,
        "model.total_deposited diverged from on-chain: model={} on_chain={}",
        model.total_deposited, on_dep
    );
    assert_eq!(
        model.total_withdrawn, on_with,
        "model.total_withdrawn diverged from on-chain: model={} on_chain={}",
        model.total_withdrawn, on_with
    );
    assert_eq!(
        model.total_liabilities, on_liab,
        "model.total_liabilities diverged from on-chain: model={} on_chain={}",
        model.total_liabilities, on_liab
    );
    assert_eq!(
        ctx.bridge.get_wq_depth() as usize,
        model.active_requests.len(),
        "model queue depth diverged from on-chain"
    );

    for (&id, (user_key, amount)) in &model.active_requests {
        let request = ctx
            .bridge
            .get_withdrawal_request(&id)
            .unwrap_or_else(|| panic!("model request {id} is missing on-chain"));
        assert_eq!(std::format!("{:?}", request.to), *user_key);
        assert_eq!(request.amount, *amount);
        assert_eq!(
            request.queued_ledger,
            *model
                .queued_ledgers
                .get(&id)
                .expect("queued ledger is modeled")
        );

        assert!(
            !model.pending_cancellations.contains_key(&id)
                || !model.approved_cancellations.contains_key(&id),
            "request {id} is both pending and approved"
        );
        if !model.pending_cancellations.contains_key(&id)
            && !model.approved_cancellations.contains_key(&id)
        {
            assert!(
                ctx.bridge.get_cancellation_request(&id).is_none(),
                "unmodeled cancellation record remains for request {id}"
            );
        }
    }

    for (&id, expected_amount) in &model.pending_cancellations {
        let cancellation = ctx
            .bridge
            .get_cancellation_request(&id)
            .unwrap_or_else(|| panic!("pending cancellation {id} is missing on-chain"));
        assert_eq!(cancellation.status, CancellationStatus::Requested);
        assert_eq!(cancellation.amount_at_request, *expected_amount);
        if !model.active_requests.contains_key(&id) {
            assert!(
                ctx.bridge.get_withdrawal_request(&id).is_none(),
                "orphan cancellation {id} unexpectedly has a withdrawal"
            );
        }
    }

    for (&id, expected_amount) in &model.approved_cancellations {
        let cancellation = ctx
            .bridge
            .get_cancellation_request(&id)
            .unwrap_or_else(|| panic!("approved cancellation {id} is missing on-chain"));
        assert_eq!(cancellation.status, CancellationStatus::Approved);
        assert_eq!(cancellation.amount_at_request, *expected_amount);
        if !model.active_requests.contains_key(&id) {
            assert!(
                ctx.bridge.get_withdrawal_request(&id).is_none(),
                "orphan cancellation {id} unexpectedly has a withdrawal"
            );
        }
    }

    let actual_event_names = ctx
        .env
        .events()
        .all()
        .filter_by_contract(&ctx.contract_id)
        .events()
        .iter()
        .skip(ctx.contract_event_baseline)
        .map(|event| {
            let ContractEventBody::V0(body) = &event.body;
            let name: Symbol = body.topics.first().unwrap().try_into().unwrap();
            name
        })
        .collect::<std::vec::Vec<_>>();
    let expected_event_names = model
        .expected_events
        .iter()
        .map(|name| Symbol::new(&ctx.env, name))
        .collect::<std::vec::Vec<_>>();
    assert_eq!(
        actual_event_names, expected_event_names,
        "modeled and emitted FiatBridge events diverged"
    );

    // INV-A1: total_deposited >= total_withdrawn.
    assert!(
        on_dep >= on_with,
        "INV-A1 violated: total_deposited={} < total_withdrawn={}",
        on_dep,
        on_with
    );

    // INV-A2: net_deposited >= total_liabilities.
    let net = on_dep - on_with;
    assert!(
        net >= on_liab,
        "INV-A2 violated: net_deposited={} < total_liabilities={}",
        net,
        on_liab
    );

    // INV-A3: balance >= net_deposited.
    assert!(
        on_bal >= net,
        "INV-A3 violated: balance={} < net_deposited={}",
        on_bal,
        net
    );
}

// ── Example-based lifecycle tests ──────────────────────────────────────────

/// Full happy-path sequence: request → execute (full) covers INV-A1–A3, INV-Q1, INV-Q2.
#[test]
fn full_execution_lifecycle_model_agrees_with_contract() {
    let env = Env::default();
    env.mock_all_auths();
    let ctx = setup(&env);
    let mut model = LifecycleModel::default();

    let user = funded_user(&ctx, 1_000);
    let user_key = std::format!("{:?}", user);
    model.deposit(user_key.clone(), 1_000);
    assert_model_invariants(&ctx, &model);

    // request_withdrawal.
    let id = ctx
        .bridge
        .request_withdrawal(&user, &400, &ctx.token_addr, &None, &0);
    model
        .request_withdrawal(user_key.clone(), 400, env.ledger().sequence())
        .unwrap();
    assert_eq!(id, 0, "first request must be id 0 (INV-Q1)");
    assert_eq!(ctx.bridge.get_wq_depth(), 1, "INV-Q2: depth +1");
    assert_model_invariants(&ctx, &model);

    ctx.bridge.request_cancellation(&id, &user);
    model.request_cancellation(id).unwrap();
    assert_model_invariants(&ctx, &model);

    // execute_withdrawal (full).
    let nonce = ctx.bridge.get_withdrawal_execution_nonce(&user);
    ctx.bridge.execute_withdrawal(&id, &None, &0, &0, &nonce);
    model.execute_full(id).unwrap();
    assert!(ctx.bridge.get_withdrawal_request(&id).is_none());
    assert_eq!(ctx.bridge.get_wq_depth(), 0, "INV-Q2: depth -1");
    assert_model_invariants(&ctx, &model);
}

/// Partial execution: amount flows out in two steps, queue entry persists until the second.
#[test]
fn partial_then_full_execution_model_agrees_with_contract() {
    let env = Env::default();
    env.mock_all_auths();
    let ctx = setup(&env);
    let mut model = LifecycleModel::default();

    let user = funded_user(&ctx, 2_000);
    let user_key = std::format!("{:?}", user);
    model.deposit(user_key.clone(), 2_000);

    let id = ctx
        .bridge
        .request_withdrawal(&user, &1_200, &ctx.token_addr, &None, &0);
    model
        .request_withdrawal(user_key.clone(), 1_200, env.ledger().sequence())
        .unwrap();
    assert_model_invariants(&ctx, &model);

    // Partial: pay 500.
    let nonce = ctx.bridge.get_withdrawal_execution_nonce(&user);
    ctx.bridge
        .execute_withdrawal(&id, &Some(500), &0, &0, &nonce);
    model.execute_partial(id, 500).unwrap();
    assert!(
        ctx.bridge.get_withdrawal_request(&id).is_some(),
        "partial: request stays"
    );
    assert_eq!(ctx.bridge.get_wq_depth(), 1, "partial: depth unchanged");
    assert_eq!(
        ctx.bridge.get_withdrawal_request(&id).unwrap().amount,
        700,
        "partial: remaining amount"
    );
    assert_model_invariants(&ctx, &model);

    // Finish: pay remaining 700.
    let nonce = ctx.bridge.get_withdrawal_execution_nonce(&user);
    ctx.bridge.execute_withdrawal(&id, &None, &0, &0, &nonce);
    model.execute_full(id).unwrap();
    assert!(
        ctx.bridge.get_withdrawal_request(&id).is_none(),
        "fully executed: removed"
    );
    assert_eq!(ctx.bridge.get_wq_depth(), 0);
    assert_model_invariants(&ctx, &model);
}

/// Three-step cancellation lifecycle (INV-C1, INV-C2, INV-Z2).
#[test]
fn three_step_cancellation_model_agrees_with_contract() {
    let env = Env::default();
    env.mock_all_auths();
    let ctx = setup(&env);
    let mut model = LifecycleModel::default();

    let user = funded_user(&ctx, 1_000);
    let user_key = std::format!("{:?}", user);
    model.deposit(user_key.clone(), 1_000);

    let id = ctx
        .bridge
        .request_withdrawal(&user, &300, &ctx.token_addr, &None, &0);
    model
        .request_withdrawal(user_key.clone(), 300, env.ledger().sequence())
        .unwrap();
    assert_model_invariants(&ctx, &model);

    // Step 1: request_cancellation.
    ctx.bridge.request_cancellation(&id, &user);
    model.request_cancellation(id).unwrap();
    // Liabilities must NOT have changed yet (INV-C2).
    assert_eq!(
        ctx.bridge.get_total_liabilities(),
        model.total_liabilities,
        "INV-C2: liabilities unchanged after request_cancellation"
    );
    let cr = ctx
        .bridge
        .get_cancellation_request(&id)
        .expect("record must exist");
    assert_eq!(
        cr.status,
        CancellationStatus::Requested,
        "INV-C1: Requested state"
    );
    assert_model_invariants(&ctx, &model);

    // Step 2: approve_cancellation.
    ctx.bridge.approve_cancellation(&id);
    model.approve_cancellation(id).unwrap();
    // Liabilities still unchanged (INV-C2).
    assert_eq!(
        ctx.bridge.get_total_liabilities(),
        model.total_liabilities,
        "INV-C2: liabilities unchanged after approve_cancellation"
    );
    let cr = ctx
        .bridge
        .get_cancellation_request(&id)
        .expect("record must exist after approval");
    assert_eq!(
        cr.status,
        CancellationStatus::Approved,
        "INV-C1: Approved state"
    );
    assert_model_invariants(&ctx, &model);

    // Step 3: finalize_cancellation.
    ctx.bridge.finalize_cancellation(&id);
    model.finalize_cancellation(id).unwrap();
    assert!(
        ctx.bridge.get_cancellation_request(&id).is_none(),
        "INV-C1: record deleted"
    );
    assert!(
        ctx.bridge.get_withdrawal_request(&id).is_none(),
        "request removed"
    );
    assert_eq!(ctx.bridge.get_wq_depth(), 0, "INV-Q2: depth -1");
    assert_model_invariants(&ctx, &model);
}

/// Cancellation after partial execution releases only the residual (INV-C2).
#[test]
fn cancellation_after_partial_execution_releases_residual_only() {
    let env = Env::default();
    env.mock_all_auths();
    let ctx = setup(&env);
    let mut model = LifecycleModel::default();

    let user = funded_user(&ctx, 2_000);
    let user_key = std::format!("{:?}", user);
    model.deposit(user_key.clone(), 2_000);

    let id = ctx
        .bridge
        .request_withdrawal(&user, &800, &ctx.token_addr, &None, &0);
    model
        .request_withdrawal(user_key.clone(), 800, env.ledger().sequence())
        .unwrap();

    // Partial execution: 300 out.
    let nonce = ctx.bridge.get_withdrawal_execution_nonce(&user);
    ctx.bridge
        .execute_withdrawal(&id, &Some(300), &0, &0, &nonce);
    model.execute_partial(id, 300).unwrap();
    assert_model_invariants(&ctx, &model);

    // Cancel the residual 500.
    let liab_before_cancel = ctx.bridge.get_total_liabilities();
    ctx.bridge.request_cancellation(&id, &user);
    let cr = ctx.bridge.get_cancellation_request(&id).unwrap();
    assert_eq!(cr.amount_at_request, 500, "snapshot captures residual");
    assert_eq!(
        ctx.bridge.get_total_liabilities(),
        liab_before_cancel,
        "INV-C2: no liability change on request"
    );

    ctx.bridge.approve_cancellation(&id);
    assert_eq!(
        ctx.bridge.get_total_liabilities(),
        liab_before_cancel,
        "INV-C2: no liability change on approve"
    );

    model.request_cancellation(id).unwrap();
    model.approve_cancellation(id).unwrap();

    ctx.bridge.finalize_cancellation(&id);
    model.finalize_cancellation(id).unwrap();
    assert_model_invariants(&ctx, &model);
    // After finalization, liabilities should have dropped by exactly 500 (the residual).
    assert_eq!(
        liab_before_cancel - ctx.bridge.get_total_liabilities(),
        500,
        "finalization releases only residual"
    );
}

/// Partial execution after cancellation request releases only the live residual at finalization.
#[test]
fn cancellation_finalization_uses_residual_after_later_partial_execution() {
    let env = Env::default();
    env.mock_all_auths();
    let ctx = setup(&env);
    let mut model = LifecycleModel::default();

    let user = funded_user(&ctx, 2_000);
    let user_key = std::format!("{:?}", user);
    model.deposit(user_key.clone(), 2_000);

    let id = ctx
        .bridge
        .request_withdrawal(&user, &800, &ctx.token_addr, &None, &0);
    model
        .request_withdrawal(user_key, 800, env.ledger().sequence())
        .unwrap();
    ctx.bridge.request_cancellation(&id, &user);
    model.request_cancellation(id).unwrap();

    let nonce = ctx.bridge.get_withdrawal_execution_nonce(&user);
    ctx.bridge
        .execute_withdrawal(&id, &Some(300), &0, &0, &nonce);
    model.execute_partial(id, 300).unwrap();
    assert_model_invariants(&ctx, &model);

    ctx.bridge.approve_cancellation(&id);
    model.approve_cancellation(id).unwrap();
    let liabilities_before_finalize = ctx.bridge.get_total_liabilities();
    ctx.bridge.finalize_cancellation(&id);
    assert_eq!(
        model.finalize_cancellation(id),
        Ok(500),
        "reference model must release the current residual, not the snapshot"
    );
    assert_eq!(
        liabilities_before_finalize - ctx.bridge.get_total_liabilities(),
        500
    );
    assert_model_invariants(&ctx, &model);
}

/// Expiry lifecycle: reclaim only allowed after the expiry window (INV-E1).
#[test]
fn expiry_requires_window_to_elapse() {
    let env = Env::default();
    env.mock_all_auths();
    let ctx = setup(&env);
    let mut model = LifecycleModel::default();

    let user = funded_user(&ctx, 1_000);
    let user_key = std::format!("{:?}", user);
    model.deposit(user_key.clone(), 1_000);

    let id = ctx
        .bridge
        .request_withdrawal(&user, &200, &ctx.token_addr, &None, &0);
    model
        .request_withdrawal(user_key.clone(), 200, env.ledger().sequence())
        .unwrap();
    ctx.bridge.request_cancellation(&id, &user);
    model.request_cancellation(id).unwrap();
    assert_model_invariants(&ctx, &model);

    // Attempt before expiry: must fail (INV-E1).
    assert_eq!(
        ctx.bridge.try_reclaim_expired_withdrawal(&id),
        Err(Ok(Error::WithdrawalLocked)),
        "INV-E1: reclaim before expiry must fail"
    );
    assert_model_invariants(&ctx, &model); // no state change on failure

    // Advance past expiry window.
    env.ledger().with_mut(|li| {
        li.sequence_number += EXPIRY_WINDOW + 1;
    });

    ctx.bridge.reclaim_expired_withdrawal(&id);
    model.reclaim_expired(id, env.ledger().sequence()).unwrap();
    assert!(
        ctx.bridge.get_withdrawal_request(&id).is_none(),
        "reclaimed: removed"
    );
    assert_eq!(ctx.bridge.get_wq_depth(), 0);
    assert_model_invariants(&ctx, &model);
}

/// Cancel-shortcut also removes from the queue and decrements liabilities.
#[test]
fn cancel_shortcut_lifecycle_model_agrees_with_contract() {
    let env = Env::default();
    env.mock_all_auths();
    let ctx = setup(&env);
    let mut model = LifecycleModel::default();

    let user = funded_user(&ctx, 1_000);
    let user_key = std::format!("{:?}", user);
    model.deposit(user_key.clone(), 1_000);

    let id = ctx
        .bridge
        .request_withdrawal(&user, &500, &ctx.token_addr, &None, &0);
    model
        .request_withdrawal(user_key.clone(), 500, env.ledger().sequence())
        .unwrap();
    ctx.bridge.request_cancellation(&id, &user);
    model.request_cancellation(id).unwrap();
    assert_model_invariants(&ctx, &model);

    ctx.bridge.cancel_withdrawal(&id);
    model.cancel_shortcut(id).unwrap();
    assert!(ctx.bridge.get_withdrawal_request(&id).is_none());
    assert_eq!(ctx.bridge.get_wq_depth(), 0);
    assert_model_invariants(&ctx, &model);

    ctx.bridge.approve_cancellation(&id);
    model.approve_cancellation(id).unwrap();
    assert_eq!(
        ctx.bridge.try_finalize_cancellation(&id),
        Err(Ok(Error::RequestNotFound))
    );
    assert_model_invariants(&ctx, &model);
}

/// Multiple users, multiple requests: the shared liability pool never violates invariants.
#[test]
fn multi_user_multi_request_model_agreement() {
    let env = Env::default();
    env.mock_all_auths();
    let ctx = setup(&env);
    let mut model = LifecycleModel::default();

    let alice = funded_user(&ctx, 2_000);
    let bob = funded_user(&ctx, 1_500);
    let alice_key = std::format!("{:?}", alice);
    let bob_key = std::format!("{:?}", bob);
    model.deposit(alice_key.clone(), 2_000);
    model.deposit(bob_key.clone(), 1_500);

    let a1 = ctx
        .bridge
        .request_withdrawal(&alice, &600, &ctx.token_addr, &None, &0);
    model
        .request_withdrawal(alice_key.clone(), 600, env.ledger().sequence())
        .unwrap();

    let b1 = ctx
        .bridge
        .request_withdrawal(&bob, &400, &ctx.token_addr, &None, &1);
    model
        .request_withdrawal(bob_key.clone(), 400, env.ledger().sequence())
        .unwrap();

    let a2 = ctx
        .bridge
        .request_withdrawal(&alice, &300, &ctx.token_addr, &None, &0);
    model
        .request_withdrawal(alice_key.clone(), 300, env.ledger().sequence())
        .unwrap();

    assert_eq!(ctx.bridge.get_wq_depth(), 3);
    assert_model_invariants(&ctx, &model);

    // Execute a1 (full).
    let nonce_a = ctx.bridge.get_withdrawal_execution_nonce(&alice);
    ctx.bridge.execute_withdrawal(&a1, &None, &0, &0, &nonce_a);
    model.execute_full(a1).unwrap();
    assert_eq!(ctx.bridge.get_wq_depth(), 2);
    assert_model_invariants(&ctx, &model);

    // Cancel b1.
    ctx.bridge.cancel_withdrawal(&b1);
    model.cancel_shortcut(b1).unwrap();
    assert_eq!(ctx.bridge.get_wq_depth(), 1);
    assert_model_invariants(&ctx, &model);

    // Lifecycle-cancel a2.
    ctx.bridge.request_cancellation(&a2, &alice);
    ctx.bridge.approve_cancellation(&a2);
    ctx.bridge.finalize_cancellation(&a2);
    model.request_cancellation(a2).unwrap();
    model.approve_cancellation(a2).unwrap();
    model.finalize_cancellation(a2).unwrap();
    assert_eq!(ctx.bridge.get_wq_depth(), 0);
    assert_model_invariants(&ctx, &model);
}

/// Ids are monotonic and never recycled, even across different lifecycle terminations.
#[test]
fn ids_are_monotonic_across_lifecycle() {
    let env = Env::default();
    env.mock_all_auths();
    let ctx = setup(&env);

    let user = funded_user(&ctx, 5_000);

    let id0 = ctx
        .bridge
        .request_withdrawal(&user, &10, &ctx.token_addr, &None, &0);
    let id1 = ctx
        .bridge
        .request_withdrawal(&user, &10, &ctx.token_addr, &None, &0);
    let id2 = ctx
        .bridge
        .request_withdrawal(&user, &10, &ctx.token_addr, &None, &0);

    assert_eq!(id0, 0);
    assert_eq!(id1, 1);
    assert_eq!(id2, 2);

    // Cancel id1 via shortcut, finalize id2 via lifecycle.
    ctx.bridge.cancel_withdrawal(&id1);
    ctx.bridge.request_cancellation(&id2, &user);
    ctx.bridge.approve_cancellation(&id2);
    ctx.bridge.finalize_cancellation(&id2);

    // The next request must be id3, not id1 or id2.
    let id3 = ctx
        .bridge
        .request_withdrawal(&user, &10, &ctx.token_addr, &None, &0);
    assert_eq!(id3, 3, "INV-Q1: next id must continue the sequence");
    assert_ne!(id3, id1);
    assert_ne!(id3, id2);
}

/// Cancellation state-machine invariant: skipping steps returns errors (INV-C1).
#[test]
fn cancellation_state_machine_is_one_way() {
    let env = Env::default();
    env.mock_all_auths();
    let ctx = setup(&env);

    let user = funded_user(&ctx, 1_000);
    let id = ctx
        .bridge
        .request_withdrawal(&user, &200, &ctx.token_addr, &None, &0);

    // Cannot finalize without any record.
    assert_eq!(
        ctx.bridge.try_finalize_cancellation(&id),
        Err(Ok(Error::CancellationNotRequested))
    );

    // Cannot approve without request.
    assert_eq!(
        ctx.bridge.try_approve_cancellation(&id),
        Err(Ok(Error::CancellationNotRequested))
    );

    ctx.bridge.request_cancellation(&id, &user);

    // Cannot finalize without approval.
    assert_eq!(
        ctx.bridge.try_finalize_cancellation(&id),
        Err(Ok(Error::CancellationNotApproved))
    );

    // Cannot request again (duplicate).
    assert_eq!(
        ctx.bridge.try_request_cancellation(&id, &user),
        Err(Ok(Error::CancellationAlreadyRequested))
    );

    // State untouched for rejected calls: request still in Requested.
    let cr = ctx.bridge.get_cancellation_request(&id).unwrap();
    assert_eq!(cr.status, CancellationStatus::Requested);

    ctx.bridge.approve_cancellation(&id);

    // Cannot approve again once already approved.
    // (approve_cancellation checks the record is in Requested state via CancellationNotRequested)
    assert_eq!(
        ctx.bridge.try_approve_cancellation(&id),
        Err(Ok(Error::CancellationNotRequested))
    );
}

/// Unauthorized third party cannot initiate cancellation (INV-Z2).
#[test]
fn unauthorized_caller_cannot_initiate_cancellation() {
    let env = Env::default();
    env.mock_all_auths();
    let ctx = setup(&env);

    let user = funded_user(&ctx, 1_000);
    let id = ctx
        .bridge
        .request_withdrawal(&user, &200, &ctx.token_addr, &None, &0);

    let stranger = Address::generate(&env);
    let liab_before = ctx.bridge.get_total_liabilities();

    assert_eq!(
        ctx.bridge.try_request_cancellation(&id, &stranger),
        Err(Ok(Error::Unauthorized)),
        "INV-Z2: stranger cannot request cancellation"
    );
    // No side effects.
    assert!(ctx.bridge.get_cancellation_request(&id).is_none());
    assert_eq!(
        ctx.bridge.get_total_liabilities(),
        liab_before,
        "INV-Z3: liabilities unchanged on rejected call"
    );
}

/// Scheduler priority: lower tier requested later must still be served before
/// higher tier requested earlier (INV-Q3).
#[test]
fn scheduler_respects_tier_and_age_ordering() {
    let env = Env::default();
    env.mock_all_auths();
    let ctx = setup(&env);

    let user = funded_user(&ctx, 2_000);

    // High-risk (tier 5) first.
    let high_risk = ctx
        .bridge
        .request_withdrawal(&user, &100, &ctx.token_addr, &None, &5);

    // Low-risk (tier 0) second.
    let low_risk = ctx
        .bridge
        .request_withdrawal(&user, &100, &ctx.token_addr, &None, &0);

    // Tier 0 (low_risk) must be the next priority.
    let next = ctx.bridge.get_next_priority_withdrawal();
    assert_eq!(
        next,
        Some(low_risk),
        "INV-Q3: tier-0 request must be scheduled before tier-5"
    );

    // Verify high_risk request still exists after serving low_risk.
    let nonce = ctx.bridge.get_withdrawal_execution_nonce(&user);
    ctx.bridge
        .execute_withdrawal(&low_risk, &None, &0, &0, &nonce);
    assert_eq!(
        ctx.bridge.get_next_priority_withdrawal(),
        Some(high_risk),
        "INV-Q3: high-risk served after low-risk is drained"
    );
}

/// Failure paths leave no partial state: rejected calls must leave queue and
/// accounting exactly as they were (INV-Z3).
#[test]
fn rejected_calls_leave_no_partial_state() {
    let env = Env::default();
    env.mock_all_auths();
    let ctx = setup(&env);
    let mut model = LifecycleModel::default();

    let user = funded_user(&ctx, 1_000);
    let user_key = std::format!("{:?}", user);
    model.deposit(user_key.clone(), 1_000);

    // Valid request so there is existing state to compare against.
    let id = ctx
        .bridge
        .request_withdrawal(&user, &100, &ctx.token_addr, &None, &0);
    model
        .request_withdrawal(user_key.clone(), 100, env.ledger().sequence())
        .unwrap();

    let dep_snap = ctx.bridge.get_total_deposited();
    let with_snap = ctx.bridge.get_total_withdrawn();
    let liab_snap = ctx.bridge.get_total_liabilities();
    let depth_snap = ctx.bridge.get_wq_depth();
    let next_id_snap = id + 1; // expected next id before any failure

    // Over-balance request is rejected.
    assert!(ctx
        .bridge
        .try_request_withdrawal(&user, &2_000, &ctx.token_addr, &None, &0)
        .is_err());
    // No state change.
    assert_eq!(ctx.bridge.get_total_deposited(), dep_snap);
    assert_eq!(ctx.bridge.get_total_withdrawn(), with_snap);
    assert_eq!(ctx.bridge.get_total_liabilities(), liab_snap);
    assert_eq!(ctx.bridge.get_wq_depth(), depth_snap);
    // ID counter must not have advanced.
    let next = ctx
        .bridge
        .request_withdrawal(&user, &10, &ctx.token_addr, &None, &0);
    assert_eq!(
        next, next_id_snap,
        "INV-Z3: rejected call must not consume a request id"
    );

    // Execution before unlock is rejected.
    assert_eq!(
        ctx.bridge.try_execute_withdrawal(&id, &None, &0, &0, &0),
        Err(Ok(Error::WithdrawalLocked)),
        "INV-Z3: execute before unlock must fail"
    );
    assert_eq!(ctx.bridge.get_total_withdrawn(), with_snap);
}

/// Reclaim with a non-existent request returns RequestNotFound (INV-E1 boundary).
#[test]
fn reclaim_nonexistent_request_is_rejected() {
    let env = Env::default();
    env.mock_all_auths();
    let ctx = setup(&env);

    env.ledger().with_mut(|li| {
        li.sequence_number += EXPIRY_WINDOW + 1;
    });

    assert_eq!(
        ctx.bridge.try_reclaim_expired_withdrawal(&9_999),
        Err(Ok(Error::RequestNotFound))
    );
}

// ── Property-based lifecycle sweep ─────────────────────────────────────────

/// Abstract operation for the property-based harness.
#[derive(Clone, Debug)]
enum LifecycleOp {
    Deposit(i128),
    RequestWithdrawal(usize, i128),
    ExecuteFull(usize),
    ExecutePartial(usize, i128),
    CancelShortcut(usize),
    RequestCancellation(usize),
    ApproveCancellation(usize),
    FinalizeCancellation(usize),
    ReclaimExpired(usize),
    AdvanceLedger(u32),
}

fn lifecycle_op_strategy() -> impl Strategy<Value = LifecycleOp> {
    prop_oneof![
        (MIN_DEP..=50_000i128).prop_map(LifecycleOp::Deposit),
        (0usize..8, 1i128..=20_000i128).prop_map(|(i, a)| LifecycleOp::RequestWithdrawal(i, a)),
        (0usize..8).prop_map(LifecycleOp::ExecuteFull),
        (0usize..8, 1i128..=10_000i128).prop_map(|(i, a)| LifecycleOp::ExecutePartial(i, a)),
        (0usize..8).prop_map(LifecycleOp::CancelShortcut),
        (0usize..8).prop_map(LifecycleOp::RequestCancellation),
        (0usize..8).prop_map(LifecycleOp::ApproveCancellation),
        (0usize..8).prop_map(LifecycleOp::FinalizeCancellation),
        (0usize..8).prop_map(LifecycleOp::ReclaimExpired),
        (1u32..=5_000u32).prop_map(LifecycleOp::AdvanceLedger),
    ]
}

/// Stateful harness that wraps the contract and the reference model for
/// property-based testing.
struct ModelHarness<'a> {
    ctx: Ctx<'a>,
    model: LifecycleModel,
    /// Addresses that have deposited at least once.
    depositors: std::vec::Vec<Address>,
    /// Active request ids (in insertion order).
    active_ids: std::vec::Vec<u64>,
    /// Ids currently in a pending-cancellation state.
    pending_cancel_ids: std::vec::Vec<u64>,
    /// Ids currently in an approved-cancellation state.
    approved_cancel_ids: std::vec::Vec<u64>,
}

impl<'a> ModelHarness<'a> {
    fn new(env: &'a Env) -> Self {
        let ctx = setup(env);
        ModelHarness {
            ctx,
            model: LifecycleModel::default(),
            depositors: std::vec::Vec::new(),
            active_ids: std::vec::Vec::new(),
            pending_cancel_ids: std::vec::Vec::new(),
            approved_cancel_ids: std::vec::Vec::new(),
        }
    }

    fn apply(&mut self, op: &LifecycleOp) {
        match op {
            LifecycleOp::Deposit(amount) => self.do_deposit(*amount),
            LifecycleOp::RequestWithdrawal(idx, amount) => self.do_request(*idx, *amount),
            LifecycleOp::ExecuteFull(idx) => self.do_execute_full(*idx),
            LifecycleOp::ExecutePartial(idx, amount) => self.do_execute_partial(*idx, *amount),
            LifecycleOp::CancelShortcut(idx) => self.do_cancel_shortcut(*idx),
            LifecycleOp::RequestCancellation(idx) => self.do_request_cancellation(*idx),
            LifecycleOp::ApproveCancellation(idx) => self.do_approve_cancellation(*idx),
            LifecycleOp::FinalizeCancellation(idx) => self.do_finalize_cancellation(*idx),
            LifecycleOp::ReclaimExpired(idx) => self.do_reclaim_expired(*idx),
            LifecycleOp::AdvanceLedger(delta) => {
                self.ctx.env.ledger().with_mut(|li| {
                    li.sequence_number = li.sequence_number.saturating_add(*delta);
                });
            }
        }
    }

    fn do_deposit(&mut self, amount: i128) {
        let user = Address::generate(&self.ctx.env);
        self.ctx.token_admin.mint(&user, &(amount + 1_000));
        let result = self.ctx.bridge.try_deposit(
            &user,
            &amount,
            &self.ctx.token_addr,
            &Bytes::from_slice(&self.ctx.env, b"r"),
            &0,
            &0,
            &None,
        );
        match result {
            Ok(Ok(_)) => {
                let key = std::format!("{:?}", user);
                self.model.deposit(key, amount);
                self.depositors.push(user);
            }
            result => panic!("generated deposit failed unexpectedly: {result:?}"),
        }
    }

    fn do_request(&mut self, user_idx: usize, amount: i128) {
        if self.depositors.is_empty() {
            return;
        }
        let user = self.depositors[user_idx % self.depositors.len()].clone();
        let key = std::format!("{:?}", user);
        let mut next_model = self.model.clone();
        let model_result =
            next_model.request_withdrawal(key, amount, self.ctx.env.ledger().sequence());
        let result =
            self.ctx
                .bridge
                .try_request_withdrawal(&user, &amount, &self.ctx.token_addr, &None, &0);
        match (model_result, result) {
            (Ok(expected_id), Ok(Ok(id))) => {
                assert_eq!(
                    id, expected_id,
                    "model and contract allocated different IDs"
                );
                self.model = next_model;
                self.active_ids.push(id);
            }
            (Err(()), Err(Ok(Error::InsufficientFunds))) => {}
            (expected, actual) => {
                panic!("model request outcome {expected:?} diverged from contract {actual:?}")
            }
        }
    }

    fn do_execute_full(&mut self, idx: usize) {
        if self.active_ids.is_empty() {
            return;
        }
        let id = self.active_ids[idx % self.active_ids.len()];
        let request = match self.ctx.bridge.get_withdrawal_request(&id) {
            Some(r) => r,
            None => {
                self.active_ids.retain(|&x| x != id);
                return;
            }
        };
        // Skip locked requests (don't want to depend on lock period in the model).
        if self.ctx.env.ledger().sequence() < request.unlock_ledger {
            return;
        }
        let nonce = self.ctx.bridge.get_withdrawal_execution_nonce(&request.to);
        let mut next_model = self.model.clone();
        next_model
            .execute_full(id)
            .expect("queued request must exist in the reference model");
        self.ctx
            .bridge
            .try_execute_withdrawal(&id, &None, &0, &0, &nonce)
            .expect("execution invocation must complete")
            .expect("unlocked model request must execute");
        self.model = next_model;
        self.active_ids.retain(|&x| x != id);
    }

    fn do_execute_partial(&mut self, idx: usize, amount: i128) {
        if self.active_ids.is_empty() {
            return;
        }
        let id = self.active_ids[idx % self.active_ids.len()];
        let request = match self.ctx.bridge.get_withdrawal_request(&id) {
            Some(r) => r,
            None => {
                self.active_ids.retain(|&x| x != id);
                return;
            }
        };
        if self.ctx.env.ledger().sequence() < request.unlock_ledger {
            return;
        }
        let clamped = amount.min(request.amount - 1).max(1);
        if clamped <= 0 || clamped >= request.amount {
            return;
        }
        let nonce = self.ctx.bridge.get_withdrawal_execution_nonce(&request.to);
        let mut next_model = self.model.clone();
        next_model
            .execute_partial(id, clamped)
            .expect("valid partial amount must be accepted by the reference model");
        self.ctx
            .bridge
            .try_execute_withdrawal(&id, &Some(clamped), &0, &0, &nonce)
            .expect("partial execution invocation must complete")
            .expect("valid partial execution must succeed");
        self.model = next_model;
    }

    fn do_cancel_shortcut(&mut self, idx: usize) {
        if self.active_ids.is_empty() {
            return;
        }
        let id = self.active_ids[idx % self.active_ids.len()];
        let mut next_model = self.model.clone();
        next_model
            .cancel_shortcut(id)
            .expect("queued request must exist in the reference model");
        self.ctx
            .bridge
            .try_cancel_withdrawal(&id)
            .expect("cancellation invocation must complete")
            .expect("admin shortcut cancellation must succeed");
        self.model = next_model;
        self.active_ids.retain(|&x| x != id);
    }

    fn do_request_cancellation(&mut self, idx: usize) {
        if self.active_ids.is_empty() {
            return;
        }
        let id = self.active_ids[idx % self.active_ids.len()];
        if self.pending_cancel_ids.contains(&id) || self.approved_cancel_ids.contains(&id) {
            return;
        }
        let request = match self.ctx.bridge.get_withdrawal_request(&id) {
            Some(r) => r,
            None => return,
        };
        let mut next_model = self.model.clone();
        next_model
            .request_cancellation(id)
            .expect("uncancelled request must accept cancellation");
        self.ctx
            .bridge
            .try_request_cancellation(&id, &request.to)
            .expect("cancellation request invocation must complete")
            .expect("recipient cancellation request must succeed");
        self.model = next_model;
        self.pending_cancel_ids.push(id);
    }

    fn do_approve_cancellation(&mut self, idx: usize) {
        if self.pending_cancel_ids.is_empty() {
            return;
        }
        let id = self.pending_cancel_ids[idx % self.pending_cancel_ids.len()];
        let mut next_model = self.model.clone();
        next_model
            .approve_cancellation(id)
            .expect("pending cancellation must be approvable");
        self.ctx
            .bridge
            .try_approve_cancellation(&id)
            .expect("approval invocation must complete")
            .expect("admin approval must succeed");
        self.model = next_model;
        self.pending_cancel_ids.retain(|&x| x != id);
        self.approved_cancel_ids.push(id);
    }

    fn do_finalize_cancellation(&mut self, idx: usize) {
        if self.approved_cancel_ids.is_empty() {
            return;
        }
        let id = self.approved_cancel_ids[idx % self.approved_cancel_ids.len()];
        let mut next_model = self.model.clone();
        let expected = next_model.finalize_cancellation(id);
        let actual = self.ctx.bridge.try_finalize_cancellation(&id);
        match (expected, actual) {
            (Ok(_), Ok(Ok(()))) => {
                self.model = next_model;
                self.approved_cancel_ids.retain(|&x| x != id);
                self.active_ids.retain(|&x| x != id);
            }
            (Err(()), Err(Ok(Error::RequestNotFound))) => {}
            (expected, actual) => {
                panic!("model finalization outcome {expected:?} diverged from contract {actual:?}")
            }
        }
    }

    fn do_reclaim_expired(&mut self, idx: usize) {
        if self.active_ids.is_empty() {
            return;
        }
        let id = self.active_ids[idx % self.active_ids.len()];
        let current_ledger = self.ctx.env.ledger().sequence();
        let mut next_model = self.model.clone();
        match (
            next_model.reclaim_expired(id, current_ledger),
            self.ctx.bridge.try_reclaim_expired_withdrawal(&id),
        ) {
            (Ok(_), Ok(Ok(()))) => {
                self.model = next_model;
                self.active_ids.retain(|&x| x != id);
            }
            (Err(()), Err(Ok(Error::WithdrawalLocked))) => {}
            (expected, actual) => {
                panic!("model reclaim outcome {expected:?} diverged from contract {actual:?}")
            }
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 128,
        max_shrink_iters: 512,
        ..Default::default()
    })]

    /// For any sequence of lifecycle operations the reference model must stay
    /// consistent with the contract, and all three core accounting invariants
    /// must hold after every accepted step.
    #[test]
    fn model_and_contract_agree_on_any_lifecycle_sequence(
        ops in proptest::collection::vec(lifecycle_op_strategy(), 1..=24),
    ) {
        let env = Env::default();
        env.mock_all_auths();

        let mut harness = ModelHarness::new(&env);

        for op in &ops {
            harness.apply(op);
            assert_model_invariants(&harness.ctx, &harness.model);
        }
    }

    /// Ids must remain strictly monotonic no matter how many requests are
    /// made, cancelled, or reclaimed (INV-Q1).
    #[test]
    fn request_ids_are_strictly_monotonic_in_any_sequence(
        counts in proptest::collection::vec(1u64..=5u64, 1..=5),
    ) {
        let env = Env::default();
        env.mock_all_auths();
        let ctx = setup(&env);

        let user = funded_user(&ctx, 50_000);

        let mut prev_id: Option<u64> = None;
        for _ in counts {
            let id = ctx.bridge.request_withdrawal(
                &user, &1, &ctx.token_addr, &None, &0,
            );
            if let Some(p) = prev_id {
                prop_assert!(id > p, "INV-Q1: id={} must be > prev={}", id, p);
            }
            prev_id = Some(id);
            ctx.bridge.cancel_withdrawal(&id);
        }
    }

    /// Liabilities may only equal zero when no requests are pending — the
    /// model and contract agree at every step.
    #[test]
    fn zero_liabilities_iff_no_pending_requests_in_model(
        ops in proptest::collection::vec(
            prop_oneof![
                (100i128..2_000i128).prop_map(LifecycleOp::Deposit),
                (0usize..4, 1i128..500i128)
                    .prop_map(|(i, a)| LifecycleOp::RequestWithdrawal(i, a)),
                (0usize..4).prop_map(LifecycleOp::CancelShortcut),
            ],
            1..=16,
        ),
    ) {
        let env = Env::default();
        env.mock_all_auths();

        let mut harness = ModelHarness::new(&env);

        for op in &ops {
            harness.apply(op);
        }

        let no_pending = harness.active_ids.is_empty()
            && harness.pending_cancel_ids.is_empty()
            && harness.approved_cancel_ids.is_empty();

        let on_chain_liab = harness.ctx.bridge.get_total_liabilities();

        if no_pending {
            prop_assert_eq!(
                on_chain_liab, 0,
                "liabilities should be zero when no requests are pending"
            );
        }
        // Always assert the model agrees.
        prop_assert_eq!(harness.model.total_liabilities, on_chain_liab);
    }
}

//! Cheap, operation-scoped kernel work counters.
//!
//! This value contains no clock and is deliberately independent of proof
//! evidence. Callers may pass a borrowed optional meter at an outer operation
//! boundary without introducing a process-global registry.

use std::sync::{Arc, Mutex};

/// Saturating deterministic counters for kernel work.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct KernelWorkCounters {
    pub check_calls: u64,
    pub infer_calls: u64,
    pub whnf_calls: u64,
    pub defeq_calls: u64,
    pub quick_equality_hits: u64,
    pub beta_steps: u64,
    pub delta_steps: u64,
    pub iota_steps: u64,
    pub zeta_steps: u64,
    pub logical_fuel: u64,
    pub successful_fuel: u64,
    pub exhausted_fuel: u64,
    pub physical_reductions: u64,
    pub context_lookups: u64,
    pub context_shifts: u64,
    pub memo_eligible_calls: u64,
    pub memo_ineligible_borrowed: u64,
    pub memo_ineligible_fresh: u64,
    pub memo_ineligible_diagnosed: u64,
    pub memo_identity_capacity_stops: u64,
    pub whnf_memo_lookups: u64,
    pub whnf_memo_hits: u64,
    pub whnf_memo_misses: u64,
    pub whnf_memo_inserts: u64,
    pub whnf_memo_capacity_stops: u64,
    pub defeq_memo_lookups: u64,
    pub defeq_memo_hits: u64,
    pub defeq_memo_misses: u64,
    pub defeq_memo_inserts: u64,
    pub defeq_memo_capacity_stops: u64,
    pub memo_expr_identities: u64,
    pub memo_local_identities: u64,
    pub memo_context_identities: u64,
    pub memo_parameter_profiles: u64,
    pub memo_entry_capacity: u64,
    pub whnf_memo_entries: u64,
    pub defeq_memo_entries: u64,
    pub memo_retained_node_occurrences: u64,
    pub memo_retained_context_occurrences: u64,
    pub memo_retained_parameter_occurrences: u64,
    pub memo_retained_bytes: u64,
    pub memo_logical_fuel_replayed: u64,
    pub memo_bypassed_call_bodies: u64,
    pub memo_accounting_overflows: u64,
    pub memo_probe_lookups: u64,
    pub memo_probe_repetitions: u64,
    pub memo_probe_inserts: u64,
    pub memo_probe_capacity_stops: u64,
    pub memo_probe_truncated: bool,
    pub overflowed: bool,
}

impl KernelWorkCounters {
    pub(crate) fn add(value: &mut u64, amount: u64, overflowed: &mut bool) {
        let (next, did_overflow) = value.overflowing_add(amount);
        if did_overflow {
            *value = u64::MAX;
            *overflowed = true;
        } else {
            *value = next;
        }
    }

    /// Saturating merge for worker-local counters.
    pub fn merge(&mut self, other: Self) {
        macro_rules! merge {
            ($field:ident) => {
                Self::add(&mut self.$field, other.$field, &mut self.overflowed);
            };
        }
        merge!(check_calls);
        merge!(infer_calls);
        merge!(whnf_calls);
        merge!(defeq_calls);
        merge!(quick_equality_hits);
        merge!(beta_steps);
        merge!(delta_steps);
        merge!(iota_steps);
        merge!(zeta_steps);
        merge!(logical_fuel);
        merge!(successful_fuel);
        merge!(exhausted_fuel);
        merge!(physical_reductions);
        merge!(context_lookups);
        merge!(context_shifts);
        merge!(memo_eligible_calls);
        merge!(memo_ineligible_borrowed);
        merge!(memo_ineligible_fresh);
        merge!(memo_ineligible_diagnosed);
        merge!(memo_identity_capacity_stops);
        merge!(whnf_memo_lookups);
        merge!(whnf_memo_hits);
        merge!(whnf_memo_misses);
        merge!(whnf_memo_inserts);
        merge!(whnf_memo_capacity_stops);
        merge!(defeq_memo_lookups);
        merge!(defeq_memo_hits);
        merge!(defeq_memo_misses);
        merge!(defeq_memo_inserts);
        merge!(defeq_memo_capacity_stops);
        self.memo_expr_identities = self.memo_expr_identities.max(other.memo_expr_identities);
        self.memo_local_identities = self.memo_local_identities.max(other.memo_local_identities);
        self.memo_context_identities = self
            .memo_context_identities
            .max(other.memo_context_identities);
        self.memo_parameter_profiles = self
            .memo_parameter_profiles
            .max(other.memo_parameter_profiles);
        self.memo_entry_capacity = self.memo_entry_capacity.max(other.memo_entry_capacity);
        self.whnf_memo_entries = self.whnf_memo_entries.max(other.whnf_memo_entries);
        self.defeq_memo_entries = self.defeq_memo_entries.max(other.defeq_memo_entries);
        self.memo_retained_node_occurrences = self
            .memo_retained_node_occurrences
            .max(other.memo_retained_node_occurrences);
        self.memo_retained_context_occurrences = self
            .memo_retained_context_occurrences
            .max(other.memo_retained_context_occurrences);
        self.memo_retained_parameter_occurrences = self
            .memo_retained_parameter_occurrences
            .max(other.memo_retained_parameter_occurrences);
        self.memo_retained_bytes = self.memo_retained_bytes.max(other.memo_retained_bytes);
        merge!(memo_logical_fuel_replayed);
        merge!(memo_bypassed_call_bodies);
        merge!(memo_accounting_overflows);
        merge!(memo_probe_lookups);
        merge!(memo_probe_repetitions);
        merge!(memo_probe_inserts);
        merge!(memo_probe_capacity_stops);
        self.memo_probe_truncated |= other.memo_probe_truncated;
        self.overflowed |= other.overflowed;
    }

    pub(crate) fn add_memo_replayed_fuel(&mut self, amount: usize) {
        let amount = u64::try_from(amount).unwrap_or(u64::MAX);
        Self::add(
            &mut self.memo_logical_fuel_replayed,
            amount,
            &mut self.overflowed,
        );
    }
}

/// Explicit, process-local accumulator for the ordinary nondiagnosed kernel
/// operations performed while validating declarations.
///
/// The sink retains counters only. It never owns expressions, environments,
/// memo entries, or proof evidence.
#[derive(Clone, Debug, Default)]
pub struct KernelWorkCounterSink {
    counters: Arc<Mutex<KernelWorkCounters>>,
}

impl KernelWorkCounterSink {
    pub(crate) fn observe(&self, counters: KernelWorkCounters) {
        self.counters
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .merge(counters);
    }

    /// Return the current aggregate without resetting it.
    pub fn snapshot(&self) -> KernelWorkCounters {
        *self
            .counters
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn merge_saturates_and_marks_overflow() {
        let mut counters = KernelWorkCounters {
            logical_fuel: u64::MAX,
            ..KernelWorkCounters::default()
        };
        counters.merge(KernelWorkCounters {
            logical_fuel: 1,
            ..KernelWorkCounters::default()
        });
        assert_eq!(counters.logical_fuel, u64::MAX);
        assert!(counters.overflowed);
    }
}

//! Cheap, operation-scoped kernel work counters.
//!
//! This value contains no clock and is deliberately independent of proof
//! evidence. Callers may pass a borrowed optional meter at an outer operation
//! boundary without introducing a process-global registry.

use std::sync::{Arc, Mutex};

use crate::diagnostic::KernelFuelResource;

/// Fuel accounting for exactly one kernel operation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct KernelFuelOperationCounters {
    pub budget: u64,
    pub spent: u64,
    pub remaining: u64,
    pub exhausted: bool,
    pub overflowed: bool,
}

impl KernelFuelOperationCounters {
    /// Convert one operation's native-width fuel values without truncation.
    pub(crate) fn from_usize(
        budget: usize,
        spent: usize,
        remaining: usize,
        exhausted: bool,
    ) -> Self {
        let mut overflowed = false;
        Self {
            budget: usize_to_u64_saturating(budget, &mut overflowed),
            spent: usize_to_u64_saturating(spent, &mut overflowed),
            remaining: usize_to_u64_saturating(remaining, &mut overflowed),
            exhausted,
            overflowed,
        }
    }
}

/// Aggregate fuel accounting for one kernel resource domain.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct KernelFuelDomainTotals {
    pub calls: u64,
    pub logical_spent: u64,
    pub successful_operation_fuel: u64,
    pub exhausted_operation_fuel: u64,
    pub overflowed: bool,
}

impl KernelFuelDomainTotals {
    fn record_operation(&mut self, spent: usize, exhausted: bool) {
        let spent = usize_to_u64_saturating(spent, &mut self.overflowed);
        KernelWorkCounters::add(&mut self.calls, 1, &mut self.overflowed);
        KernelWorkCounters::add(&mut self.logical_spent, spent, &mut self.overflowed);
        if exhausted {
            KernelWorkCounters::add(
                &mut self.exhausted_operation_fuel,
                spent,
                &mut self.overflowed,
            );
        } else {
            KernelWorkCounters::add(
                &mut self.successful_operation_fuel,
                spent,
                &mut self.overflowed,
            );
        }
    }

    fn merge(&mut self, other: Self) {
        KernelWorkCounters::add(&mut self.calls, other.calls, &mut self.overflowed);
        KernelWorkCounters::add(
            &mut self.logical_spent,
            other.logical_spent,
            &mut self.overflowed,
        );
        KernelWorkCounters::add(
            &mut self.successful_operation_fuel,
            other.successful_operation_fuel,
            &mut self.overflowed,
        );
        KernelWorkCounters::add(
            &mut self.exhausted_operation_fuel,
            other.exhausted_operation_fuel,
            &mut self.overflowed,
        );
        self.overflowed |= other.overflowed;
    }

    fn delta_since(self, start: Self, inherited_overflowed: bool) -> Self {
        let domain_overflowed = self.overflowed || start.overflowed;
        let endpoint_overflowed = inherited_overflowed || domain_overflowed;
        let mut overflowed = domain_overflowed;
        Self {
            calls: counter_delta(
                self.calls,
                start.calls,
                endpoint_overflowed,
                &mut overflowed,
            ),
            logical_spent: counter_delta(
                self.logical_spent,
                start.logical_spent,
                endpoint_overflowed,
                &mut overflowed,
            ),
            successful_operation_fuel: counter_delta(
                self.successful_operation_fuel,
                start.successful_operation_fuel,
                endpoint_overflowed,
                &mut overflowed,
            ),
            exhausted_operation_fuel: counter_delta(
                self.exhausted_operation_fuel,
                start.exhausted_operation_fuel,
                endpoint_overflowed,
                &mut overflowed,
            ),
            overflowed,
        }
    }
}

/// Domain-separated fuel accounting for weak-head normalization and conversion.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct KernelFuelTotals {
    pub whnf: KernelFuelDomainTotals,
    pub conversion: KernelFuelDomainTotals,
}

impl KernelFuelTotals {
    fn merge(&mut self, other: Self) {
        self.whnf.merge(other.whnf);
        self.conversion.merge(other.conversion);
    }

    fn delta_since(self, start: Self, inherited_overflowed: bool) -> Self {
        Self {
            whnf: self.whnf.delta_since(start.whnf, inherited_overflowed),
            conversion: self
                .conversion
                .delta_since(start.conversion, inherited_overflowed),
        }
    }

    fn overflowed(self) -> bool {
        self.whnf.overflowed || self.conversion.overflowed
    }
}

/// Strict bounded kernel-work vocabulary used for operation/declaration deltas.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct KernelWorkSnapshot {
    pub check_calls: u64,
    pub infer_calls: u64,
    pub whnf_calls: u64,
    pub defeq_calls: u64,
    pub quick_equality_hits: u64,
    pub beta_steps: u64,
    pub delta_steps: u64,
    pub iota_steps: u64,
    pub physical_reductions: u64,
    pub fuel: KernelFuelTotals,
    pub overflowed: bool,
}

impl KernelWorkSnapshot {
    /// Return the exact zero snapshot.
    pub fn zero() -> Self {
        Self::default()
    }

    /// Return a saturating, overflow-aware delta from `start` to this snapshot.
    pub fn delta_since(self, start: Self) -> Self {
        let endpoint_overflowed = self.overflowed
            || start.overflowed
            || self.fuel.overflowed()
            || start.fuel.overflowed();
        let mut overflowed = endpoint_overflowed;
        let fuel = self.fuel.delta_since(start.fuel, endpoint_overflowed);
        let delta = Self {
            check_calls: counter_delta(
                self.check_calls,
                start.check_calls,
                endpoint_overflowed,
                &mut overflowed,
            ),
            infer_calls: counter_delta(
                self.infer_calls,
                start.infer_calls,
                endpoint_overflowed,
                &mut overflowed,
            ),
            whnf_calls: counter_delta(
                self.whnf_calls,
                start.whnf_calls,
                endpoint_overflowed,
                &mut overflowed,
            ),
            defeq_calls: counter_delta(
                self.defeq_calls,
                start.defeq_calls,
                endpoint_overflowed,
                &mut overflowed,
            ),
            quick_equality_hits: counter_delta(
                self.quick_equality_hits,
                start.quick_equality_hits,
                endpoint_overflowed,
                &mut overflowed,
            ),
            beta_steps: counter_delta(
                self.beta_steps,
                start.beta_steps,
                endpoint_overflowed,
                &mut overflowed,
            ),
            delta_steps: counter_delta(
                self.delta_steps,
                start.delta_steps,
                endpoint_overflowed,
                &mut overflowed,
            ),
            iota_steps: counter_delta(
                self.iota_steps,
                start.iota_steps,
                endpoint_overflowed,
                &mut overflowed,
            ),
            physical_reductions: counter_delta(
                self.physical_reductions,
                start.physical_reductions,
                endpoint_overflowed,
                &mut overflowed,
            ),
            fuel,
            overflowed: false,
        };
        Self {
            overflowed: overflowed || delta.fuel.overflowed(),
            ..delta
        }
    }
}

fn counter_delta(end: u64, start: u64, endpoint_overflowed: bool, overflowed: &mut bool) -> u64 {
    if end < start || (endpoint_overflowed && (end == u64::MAX || start == u64::MAX)) {
        *overflowed = true;
        u64::MAX
    } else {
        end.checked_sub(start).unwrap_or_else(|| {
            *overflowed = true;
            u64::MAX
        })
    }
}

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
    pub fuel: KernelFuelTotals,
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

    pub(crate) fn record_fuel(
        &mut self,
        resource: KernelFuelResource,
        spent: usize,
        exhausted: bool,
    ) {
        match resource {
            KernelFuelResource::Whnf => self.fuel.whnf.record_operation(spent, exhausted),
            KernelFuelResource::Conversion => {
                self.fuel.conversion.record_operation(spent, exhausted);
            }
        }
        self.refresh_legacy_fuel();
    }

    fn refresh_legacy_fuel(&mut self) {
        let mut overflowed = self.fuel.overflowed();
        self.logical_fuel = saturating_sum(
            self.fuel.whnf.logical_spent,
            self.fuel.conversion.logical_spent,
            &mut overflowed,
        );
        self.successful_fuel = saturating_sum(
            self.fuel.whnf.successful_operation_fuel,
            self.fuel.conversion.successful_operation_fuel,
            &mut overflowed,
        );
        self.exhausted_fuel = saturating_sum(
            self.fuel.whnf.exhausted_operation_fuel,
            self.fuel.conversion.exhausted_operation_fuel,
            &mut overflowed,
        );
        self.overflowed |= overflowed;
    }

    /// Capture the strict bounded work vocabulary at this instant.
    pub fn snapshot(&self) -> KernelWorkSnapshot {
        KernelWorkSnapshot::from(self)
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
        self.fuel.merge(other.fuel);
        self.refresh_legacy_fuel();
    }

    pub(crate) fn add_memo_replayed_fuel(&mut self, amount: usize) {
        let amount = usize_to_u64_saturating(amount, &mut self.overflowed);
        Self::add(
            &mut self.memo_logical_fuel_replayed,
            amount,
            &mut self.overflowed,
        );
    }
}

impl From<&KernelWorkCounters> for KernelWorkSnapshot {
    fn from(counters: &KernelWorkCounters) -> Self {
        let fuel = counters.fuel;
        Self {
            check_calls: counters.check_calls,
            infer_calls: counters.infer_calls,
            whnf_calls: counters.whnf_calls,
            defeq_calls: counters.defeq_calls,
            quick_equality_hits: counters.quick_equality_hits,
            beta_steps: counters.beta_steps,
            delta_steps: counters.delta_steps,
            iota_steps: counters.iota_steps,
            physical_reductions: counters.physical_reductions,
            fuel,
            overflowed: counters.overflowed || fuel.overflowed(),
        }
    }
}

fn saturating_sum(left: u64, right: u64, overflowed: &mut bool) -> u64 {
    let mut sum = left;
    KernelWorkCounters::add(&mut sum, right, overflowed);
    sum
}

fn usize_to_u64_saturating(value: usize, overflowed: &mut bool) -> u64 {
    match u64::try_from(value) {
        Ok(value) => value,
        Err(_) => {
            *overflowed = true;
            u64::MAX
        }
    }
}

/// Explicit, process-local accumulator for kernel work performed while
/// validating declarations. Diagnosed admission merges a declaration-local
/// copy here; failure attribution never reads from this shared accumulator.
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
    fn fuel_recording_separates_domains_and_derives_legacy_totals() {
        let mut counters = KernelWorkCounters::default();

        counters.record_fuel(KernelFuelResource::Whnf, 3, false);
        counters.record_fuel(KernelFuelResource::Conversion, 5, true);
        counters.record_fuel(KernelFuelResource::Conversion, 7, false);

        assert_eq!(counters.fuel.whnf.calls, 1);
        assert_eq!(counters.fuel.whnf.logical_spent, 3);
        assert_eq!(counters.fuel.whnf.successful_operation_fuel, 3);
        assert_eq!(counters.fuel.whnf.exhausted_operation_fuel, 0);
        assert_eq!(counters.fuel.conversion.calls, 2);
        assert_eq!(counters.fuel.conversion.logical_spent, 12);
        assert_eq!(counters.fuel.conversion.successful_operation_fuel, 7);
        assert_eq!(counters.fuel.conversion.exhausted_operation_fuel, 5);
        assert_eq!(counters.logical_fuel, 15);
        assert_eq!(counters.successful_fuel, 10);
        assert_eq!(counters.exhausted_fuel, 5);
        assert!(!counters.overflowed);
    }

    #[test]
    fn non_exhaustion_error_fuel_remains_in_legacy_success_bucket() {
        let mut counters = KernelWorkCounters::default();

        counters.record_fuel(KernelFuelResource::Conversion, 11, false);

        assert_eq!(counters.fuel.conversion.successful_operation_fuel, 11);
        assert_eq!(counters.fuel.conversion.exhausted_operation_fuel, 0);
        assert_eq!(counters.successful_fuel, 11);
        assert_eq!(counters.exhausted_fuel, 0);
    }

    #[test]
    fn operation_fuel_converts_native_values_without_truncation() {
        let counters = KernelFuelOperationCounters::from_usize(13, 8, 5, false);

        assert_eq!(counters.budget, 13);
        assert_eq!(counters.spent, 8);
        assert_eq!(counters.remaining, 5);
        assert!(!counters.exhausted);
        assert!(!counters.overflowed);
    }

    #[test]
    fn merge_saturates_domain_fuel_and_preserves_nonfuel_merge_semantics() {
        let mut counters = KernelWorkCounters {
            fuel: KernelFuelTotals {
                whnf: KernelFuelDomainTotals {
                    calls: u64::MAX,
                    logical_spent: u64::MAX,
                    successful_operation_fuel: u64::MAX,
                    ..KernelFuelDomainTotals::default()
                },
                ..KernelFuelTotals::default()
            },
            context_lookups: 4,
            memo_entry_capacity: 8,
            ..KernelWorkCounters::default()
        };
        counters.merge(KernelWorkCounters {
            fuel: KernelFuelTotals {
                whnf: KernelFuelDomainTotals {
                    calls: 1,
                    logical_spent: 1,
                    successful_operation_fuel: 1,
                    ..KernelFuelDomainTotals::default()
                },
                conversion: KernelFuelDomainTotals {
                    calls: 1,
                    logical_spent: 2,
                    exhausted_operation_fuel: 2,
                    ..KernelFuelDomainTotals::default()
                },
            },
            context_lookups: 6,
            memo_entry_capacity: 5,
            ..KernelWorkCounters::default()
        });

        assert_eq!(counters.fuel.whnf.calls, u64::MAX);
        assert_eq!(counters.fuel.whnf.logical_spent, u64::MAX);
        assert_eq!(counters.fuel.conversion.calls, 1);
        assert_eq!(counters.fuel.conversion.logical_spent, 2);
        assert_eq!(counters.logical_fuel, u64::MAX);
        assert_eq!(counters.successful_fuel, u64::MAX);
        assert_eq!(counters.exhausted_fuel, 2);
        assert_eq!(counters.context_lookups, 10);
        assert_eq!(counters.memo_entry_capacity, 8);
        assert!(counters.overflowed);
    }

    #[test]
    fn snapshot_delta_is_exact_for_monotone_bounded_work() {
        let start = KernelWorkSnapshot {
            check_calls: 2,
            infer_calls: 3,
            fuel: KernelFuelTotals {
                whnf: KernelFuelDomainTotals {
                    calls: 1,
                    logical_spent: 4,
                    successful_operation_fuel: 4,
                    ..KernelFuelDomainTotals::default()
                },
                ..KernelFuelTotals::default()
            },
            ..KernelWorkSnapshot::zero()
        };
        let end = KernelWorkSnapshot {
            check_calls: 5,
            infer_calls: 9,
            delta_steps: 2,
            physical_reductions: 2,
            fuel: KernelFuelTotals {
                whnf: KernelFuelDomainTotals {
                    calls: 2,
                    logical_spent: 10,
                    successful_operation_fuel: 7,
                    exhausted_operation_fuel: 3,
                    ..KernelFuelDomainTotals::default()
                },
                conversion: KernelFuelDomainTotals {
                    calls: 1,
                    logical_spent: 8,
                    successful_operation_fuel: 8,
                    ..KernelFuelDomainTotals::default()
                },
            },
            ..KernelWorkSnapshot::zero()
        };

        let delta = end.delta_since(start);

        assert_eq!(delta.check_calls, 3);
        assert_eq!(delta.infer_calls, 6);
        assert_eq!(delta.delta_steps, 2);
        assert_eq!(delta.physical_reductions, 2);
        assert_eq!(delta.fuel.whnf.calls, 1);
        assert_eq!(delta.fuel.whnf.logical_spent, 6);
        assert_eq!(delta.fuel.whnf.successful_operation_fuel, 3);
        assert_eq!(delta.fuel.whnf.exhausted_operation_fuel, 3);
        assert_eq!(delta.fuel.conversion.calls, 1);
        assert_eq!(delta.fuel.conversion.logical_spent, 8);
        assert!(!delta.overflowed);
    }

    #[test]
    fn snapshot_delta_saturates_end_before_start_without_wrapping() {
        let start = KernelWorkSnapshot {
            check_calls: 9,
            fuel: KernelFuelTotals {
                conversion: KernelFuelDomainTotals {
                    logical_spent: 5,
                    ..KernelFuelDomainTotals::default()
                },
                ..KernelFuelTotals::default()
            },
            ..KernelWorkSnapshot::zero()
        };
        let end = KernelWorkSnapshot {
            check_calls: 4,
            fuel: KernelFuelTotals {
                conversion: KernelFuelDomainTotals {
                    logical_spent: 3,
                    ..KernelFuelDomainTotals::default()
                },
                ..KernelFuelTotals::default()
            },
            ..KernelWorkSnapshot::zero()
        };

        let delta = end.delta_since(start);

        assert_eq!(delta.check_calls, u64::MAX);
        assert_eq!(delta.fuel.conversion.logical_spent, u64::MAX);
        assert!(delta.fuel.conversion.overflowed);
        assert!(delta.overflowed);
    }

    #[test]
    fn overflowed_snapshot_marks_max_fields_inexact_but_subtracts_other_fields() {
        let start = KernelWorkSnapshot {
            check_calls: u64::MAX,
            infer_calls: 10,
            fuel: KernelFuelTotals {
                conversion: KernelFuelDomainTotals {
                    logical_spent: 10,
                    ..KernelFuelDomainTotals::default()
                },
                ..KernelFuelTotals::default()
            },
            overflowed: true,
            ..KernelWorkSnapshot::zero()
        };
        let end = KernelWorkSnapshot {
            check_calls: u64::MAX,
            infer_calls: 14,
            fuel: KernelFuelTotals {
                conversion: KernelFuelDomainTotals {
                    logical_spent: u64::MAX,
                    ..KernelFuelDomainTotals::default()
                },
                ..KernelFuelTotals::default()
            },
            overflowed: true,
            ..KernelWorkSnapshot::zero()
        };

        let delta = end.delta_since(start);

        assert_eq!(delta.check_calls, u64::MAX);
        assert_eq!(delta.infer_calls, 4);
        assert_eq!(delta.fuel.conversion.logical_spent, u64::MAX);
        assert!(delta.fuel.conversion.overflowed);
        assert!(!delta.fuel.whnf.overflowed);
        assert!(delta.overflowed);
    }

    #[test]
    fn counters_snapshot_excludes_broad_observability_only_fields() {
        let counters = KernelWorkCounters {
            check_calls: 2,
            context_lookups: 7,
            memo_probe_lookups: 11,
            ..KernelWorkCounters::default()
        };

        let snapshot = counters.snapshot();

        assert_eq!(snapshot.check_calls, 2);
        assert_eq!(
            snapshot,
            KernelWorkSnapshot {
                check_calls: 2,
                ..KernelWorkSnapshot::zero()
            }
        );
    }
}

use std::collections::BTreeSet;

use crate::{HumanBinderInfo, HumanSourceBinderMetadata};
use npa_cert::{Hash, ModuleName, Name};
use sha2::{Digest, Sha256};

const CALLABLE_INTERFACE_TABLE_TAG: &str =
    "npa.machine-api.machine-surface-callable-interface-table.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineCallableBinderVisibility {
    Explicit,
    Implicit,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MachineSurfaceCallableRef {
    Imported {
        module: ModuleName,
        name: Name,
        export_hash: Hash,
        decl_interface_hash: Hash,
    },
    CurrentModule {
        module: ModuleName,
        name: Name,
        source_index: u64,
        decl_interface_hash: Hash,
    },
    CurrentGenerated {
        module: ModuleName,
        name: Name,
        parent_source_index: u64,
        decl_interface_hash: Hash,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineSurfaceCallableInterfaceEntry {
    callable_ref: MachineSurfaceCallableRef,
    implicit_profile: Vec<MachineCallableBinderVisibility>,
    canonical_bytes: Vec<u8>,
}

impl MachineSurfaceCallableInterfaceEntry {
    pub fn all_explicit(callable_ref: MachineSurfaceCallableRef, term_binders: usize) -> Self {
        Self::new(
            callable_ref,
            vec![MachineCallableBinderVisibility::Explicit; term_binders],
        )
    }

    pub fn new(
        callable_ref: MachineSurfaceCallableRef,
        implicit_profile: Vec<MachineCallableBinderVisibility>,
    ) -> Self {
        let canonical_bytes = canonical_entry_bytes(&callable_ref, &implicit_profile);
        Self {
            callable_ref,
            implicit_profile,
            canonical_bytes,
        }
    }

    pub fn callable_ref(&self) -> &MachineSurfaceCallableRef {
        &self.callable_ref
    }

    pub fn implicit_profile(&self) -> &[MachineCallableBinderVisibility] {
        &self.implicit_profile
    }

    pub fn canonical_bytes(&self) -> &[u8] {
        &self.canonical_bytes
    }
}

pub fn machine_callable_visibility_from_human_binder_info(
    binder_info: HumanBinderInfo,
) -> MachineCallableBinderVisibility {
    match binder_info {
        HumanBinderInfo::Explicit => MachineCallableBinderVisibility::Explicit,
        HumanBinderInfo::Implicit => MachineCallableBinderVisibility::Implicit,
    }
}

pub fn machine_callable_profile_from_human_binders(
    binders: &[HumanSourceBinderMetadata],
) -> Vec<MachineCallableBinderVisibility> {
    binders
        .iter()
        .map(|binder| machine_callable_visibility_from_human_binder_info(binder.binder_info))
        .collect()
}

pub fn builtin_machine_callable_profile(
    name: &Name,
) -> Option<Vec<MachineCallableBinderVisibility>> {
    match name.as_dotted().as_str() {
        "Eq.refl" => Some(vec![
            MachineCallableBinderVisibility::Implicit,
            MachineCallableBinderVisibility::Explicit,
        ]),
        _ => None,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineSurfaceCallableInterfaceTable {
    entries: Vec<MachineSurfaceCallableInterfaceEntry>,
    canonical_bytes: Vec<u8>,
    table_hash: Hash,
}

impl MachineSurfaceCallableInterfaceTable {
    pub fn from_entries(
        entries: impl IntoIterator<Item = MachineSurfaceCallableInterfaceEntry>,
    ) -> Result<Self, MachineSurfaceCallableInterfaceError> {
        let mut entries: Vec<_> = entries.into_iter().collect();
        entries.sort_by_cached_key(|entry| entry.canonical_bytes.clone());

        let mut seen_refs = BTreeSet::new();
        for entry in &entries {
            let ref_bytes = entry.callable_ref.canonical_bytes();
            if !seen_refs.insert(ref_bytes) {
                return Err(MachineSurfaceCallableInterfaceError::DuplicateCallableRef {
                    callable_ref: entry.callable_ref.clone(),
                });
            }
        }

        let canonical_bytes = canonical_table_bytes(&entries);
        let table_hash = hash_bytes(&canonical_bytes);
        Ok(Self {
            entries,
            canonical_bytes,
            table_hash,
        })
    }

    pub fn empty() -> Self {
        Self::from_entries([]).expect("empty callable table is valid")
    }

    pub fn entries(&self) -> &[MachineSurfaceCallableInterfaceEntry] {
        &self.entries
    }

    pub fn canonical_bytes(&self) -> &[u8] {
        &self.canonical_bytes
    }

    pub fn table_hash(&self) -> Hash {
        self.table_hash
    }

    pub fn entry_for_ref(
        &self,
        callable_ref: &MachineSurfaceCallableRef,
    ) -> Option<&MachineSurfaceCallableInterfaceEntry> {
        let ref_bytes = callable_ref.canonical_bytes();
        self.entries
            .iter()
            .find(|entry| entry.callable_ref.canonical_bytes() == ref_bytes)
    }

    pub fn entries_for_decl(
        &self,
        name: &Name,
        decl_interface_hash: &Hash,
    ) -> Vec<&MachineSurfaceCallableInterfaceEntry> {
        self.entries
            .iter()
            .filter(|entry| {
                entry.callable_ref.name() == name
                    && entry.callable_ref.decl_interface_hash() == decl_interface_hash
            })
            .collect()
    }
}

impl Default for MachineSurfaceCallableInterfaceTable {
    fn default() -> Self {
        Self::empty()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineSurfaceCallableInterfaceError {
    DuplicateCallableRef {
        callable_ref: MachineSurfaceCallableRef,
    },
}

impl MachineSurfaceCallableRef {
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        encode_callable_ref(&mut out, self);
        out
    }

    pub fn name(&self) -> &Name {
        match self {
            Self::Imported { name, .. }
            | Self::CurrentModule { name, .. }
            | Self::CurrentGenerated { name, .. } => name,
        }
    }

    pub fn decl_interface_hash(&self) -> &Hash {
        match self {
            Self::Imported {
                decl_interface_hash,
                ..
            }
            | Self::CurrentModule {
                decl_interface_hash,
                ..
            }
            | Self::CurrentGenerated {
                decl_interface_hash,
                ..
            } => decl_interface_hash,
        }
    }
}

pub fn is_machine_surface_renderable_name(name: &Name) -> bool {
    let Some((head, tail)) = name.0.split_first() else {
        return false;
    };
    is_machine_surface_term_head_component(head)
        && tail
            .iter()
            .all(|component| is_machine_surface_name_component(component))
}

fn is_machine_surface_term_head_component(value: &str) -> bool {
    is_machine_surface_name_component(value) && !is_machine_surface_reserved(value)
}

fn is_machine_surface_name_component(value: &str) -> bool {
    if value.len() > 64 {
        return false;
    }
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    first.is_ascii_alphabetic()
        && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '\'')
}

fn is_machine_surface_reserved(value: &str) -> bool {
    is_machine_surface_level_operator(value)
        || matches!(
            value,
            "import"
                | "def"
                | "theorem"
                | "fun"
                | "forall"
                | "let"
                | "in"
                | "Prop"
                | "Type"
                | "Sort"
                | "open"
                | "namespace"
                | "match"
                | "with"
                | "notation"
                | "infix"
                | "infixl"
                | "infixr"
                | "axiom"
                | "inductive"
        )
}

fn is_machine_surface_level_operator(value: &str) -> bool {
    matches!(value, "succ" | "max" | "imax")
}

fn canonical_table_bytes(entries: &[MachineSurfaceCallableInterfaceEntry]) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, CALLABLE_INTERFACE_TABLE_TAG);
    encode_uvar(&mut out, entries.len() as u64);
    for entry in entries {
        out.extend(entry.canonical_bytes());
    }
    out
}

fn canonical_entry_bytes(
    callable_ref: &MachineSurfaceCallableRef,
    implicit_profile: &[MachineCallableBinderVisibility],
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_callable_ref(&mut out, callable_ref);
    encode_uvar(&mut out, implicit_profile.len() as u64);
    for visibility in implicit_profile {
        out.push(match visibility {
            MachineCallableBinderVisibility::Explicit => 0x00,
            MachineCallableBinderVisibility::Implicit => 0x01,
        });
    }
    out
}

fn encode_callable_ref(out: &mut Vec<u8>, callable_ref: &MachineSurfaceCallableRef) {
    match callable_ref {
        MachineSurfaceCallableRef::Imported {
            module,
            name,
            export_hash,
            decl_interface_hash,
        } => {
            out.push(0x00);
            encode_name(out, module);
            encode_name(out, name);
            out.extend(export_hash);
            out.extend(decl_interface_hash);
        }
        MachineSurfaceCallableRef::CurrentModule {
            module,
            name,
            source_index,
            decl_interface_hash,
        } => {
            out.push(0x01);
            encode_name(out, module);
            encode_name(out, name);
            encode_uvar(out, *source_index);
            out.extend(decl_interface_hash);
        }
        MachineSurfaceCallableRef::CurrentGenerated {
            module,
            name,
            parent_source_index,
            decl_interface_hash,
        } => {
            out.push(0x02);
            encode_name(out, module);
            encode_name(out, name);
            encode_uvar(out, *parent_source_index);
            out.extend(decl_interface_hash);
        }
    }
}

fn encode_name(out: &mut Vec<u8>, name: &Name) {
    encode_uvar(out, name.0.len() as u64);
    for component in &name.0 {
        encode_string(out, component);
    }
}

fn encode_string(out: &mut Vec<u8>, value: &str) {
    encode_uvar(out, value.len() as u64);
    out.extend(value.as_bytes());
}

fn encode_uvar(out: &mut Vec<u8>, mut value: u64) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

fn hash_bytes(bytes: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher.finalize().into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{FileId, HumanName, Span};

    #[test]
    fn human_binder_info_maps_to_machine_callable_profile() {
        let span = Span::empty(FileId(0));
        let binders = vec![
            HumanSourceBinderMetadata {
                name: Some(HumanName::new(vec!["A".to_owned()], span)),
                binder_info: HumanBinderInfo::Implicit,
                span,
            },
            HumanSourceBinderMetadata {
                name: Some(HumanName::new(vec!["x".to_owned()], span)),
                binder_info: HumanBinderInfo::Explicit,
                span,
            },
        ];

        assert_eq!(
            machine_callable_profile_from_human_binders(&binders),
            vec![
                MachineCallableBinderVisibility::Implicit,
                MachineCallableBinderVisibility::Explicit,
            ]
        );
    }

    #[test]
    fn builtin_eq_refl_profile_marks_type_argument_implicit() {
        assert_eq!(
            builtin_machine_callable_profile(&Name::from_dotted("Eq.refl")),
            Some(vec![
                MachineCallableBinderVisibility::Implicit,
                MachineCallableBinderVisibility::Explicit,
            ])
        );
    }
}

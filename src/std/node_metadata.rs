// Copyright 2019 Parity Technologies (UK) Ltd. and Supercomputing Systems AG
// This file is part of substrate-subxt.
//
// subxt is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// subxt is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with substrate-subxt.  If not, see <http://www.gnu.org/licenses/>.

use std::{collections::HashMap, convert::TryFrom, marker::PhantomData, str::FromStr};

use codec::{Decode, Encode};

use log::*;
use metadata::{
    RuntimeMetadata, RuntimeMetadataPrefixed, StorageEntryMetadata, StorageEntryModifier,
    StorageEntryType, StorageHasher, META_RESERVED,
};
use scale_info::form::{Form, PortableForm};
use serde::ser::Serialize;
use sp_core::storage::StorageKey;

#[derive(Debug, thiserror::Error)]
pub enum MetadataError {
    #[error("Error converting substrate metadata: {0}")]
    Conversion(#[from] ConversionError),
    #[error("Pallet not found")]
    PalletNotFound(String),
    #[error("Pallet with events not found")]
    PalletWithEventsNotFound(u8),
    #[error("Call not found")]
    CallNotFound(&'static str),
    #[error("Event not found")]
    EventNotFound(u8),
    #[error("Storage not found")]
    StorageNotFound(&'static str),
    #[error("Storage type error")]
    StorageTypeError,
    #[error("Map value type error")]
    MapValueTypeError,
    #[error("Pallet with errors not found")]
    PalletWithErrorsNotFound(u8),
    #[error("Error not found")]
    ErrorNotFound(u8),
    #[error("Pallet with constants not found")]
    PalletWithConstantsNotFound(u8),
    #[error("Constant not found")]
    ConstantNotFound(String),
}

#[derive(Clone, Debug)]
pub struct Metadata {
    pallets: HashMap<String, PalletMetadata>,
    pallets_with_calls: HashMap<String, PalletWithCalls>,
    pallets_with_events: HashMap<String, PalletWithEvents>,
    pallets_with_errors: HashMap<String, PalletWithErrors>,
    pallets_with_constants: HashMap<String, PalletWithConstants>,
}

impl Metadata {
    pub fn pallet<S>(&self, name: S) -> Result<&PalletMetadata, MetadataError>
    where
        S: ToString,
    {
        let name = name.to_string();
        self.pallets
            .get(&name)
            .ok_or(MetadataError::PalletNotFound(name))
    }

    pub fn pallets_with_calls(&self) -> impl Iterator<Item = &PalletWithCalls> {
        self.pallets_with_calls.values()
    }

    pub fn pallet_with_calls<S>(&self, name: S) -> Result<&PalletWithCalls, MetadataError>
    where
        S: ToString,
    {
        let name = name.to_string();
        self.pallets_with_calls
            .get(&name)
            .ok_or(MetadataError::PalletNotFound(name))
    }

    pub fn pallets_with_events(&self) -> impl Iterator<Item = &PalletWithEvents> {
        self.pallets_with_events.values()
    }

    pub fn pallets_with_events_by_name<S>(
        &self,
        name: S,
    ) -> Result<&PalletWithEvents, MetadataError>
    where
        S: ToString,
    {
        let name = name.to_string();
        self.pallets_with_events
            .get(&name)
            .ok_or(MetadataError::PalletNotFound(name))
    }

    pub fn pallet_with_events(&self, pallet_index: u8) -> Result<&PalletWithEvents, MetadataError> {
        self.pallets_with_events
            .values()
            .find(|&pallet| pallet.index == pallet_index)
            .ok_or(MetadataError::PalletWithEventsNotFound(pallet_index))
    }

    pub fn pallets_with_errors(&self) -> impl Iterator<Item = &PalletWithErrors> {
        self.pallets_with_errors.values()
    }

    pub fn pallet_with_errors_by_name<S>(&self, name: S) -> Result<&PalletWithErrors, MetadataError>
    where
        S: ToString,
    {
        let name = name.to_string();
        self.pallets_with_errors
            .get(&name)
            .ok_or(MetadataError::PalletNotFound(name))
    }

    pub fn pallet_with_errors(&self, pallet_index: u8) -> Result<&PalletWithErrors, MetadataError> {
        self.pallets_with_errors
            .values()
            .find(|&pallet| pallet.index == pallet_index)
            .ok_or(MetadataError::PalletWithErrorsNotFound(pallet_index))
    }

    pub fn pallets_with_constants(&self) -> impl Iterator<Item = &PalletWithConstants> {
        self.pallets_with_constants.values()
    }

    pub fn pallet_with_constants_by_name<S>(
        &self,
        name: S,
    ) -> Result<&PalletWithConstants, MetadataError>
    where
        S: ToString,
    {
        let name = name.to_string();
        self.pallets_with_constants
            .get(&name)
            .ok_or(MetadataError::PalletNotFound(name))
    }

    pub fn pallet_with_constants(
        &self,
        pallet_index: u8,
    ) -> Result<&PalletWithConstants, MetadataError> {
        self.pallets_with_constants
            .values()
            .find(|&pallet| pallet.index == pallet_index)
            .ok_or(MetadataError::PalletWithConstantsNotFound(pallet_index))
    }

    pub fn print_overview(&self) {
        let mut string = String::new();
        for (name, pallet) in &self.pallets {
            string.push_str(name.as_str());
            string.push('\n');
            for storage in pallet.storage.keys() {
                string.push_str(" s  ");
                string.push_str(storage.as_str());
                string.push('\n');
            }
            if let Some(pallet) = self.pallets_with_calls.get(name) {
                for call in pallet.calls.keys() {
                    string.push_str(" c  ");
                    string.push_str(call.as_str());
                    string.push('\n');
                }
            }
            if let Some(pallet) = self.pallets_with_events.get(name) {
                for event in pallet.events.values() {
                    string.push_str(" e  ");
                    string.push_str(event.name.as_str());
                    string.push('\n');
                }
            }
            if let Some(pallet) = self.pallets_with_constants.get(name) {
                for constant in pallet.constants.values() {
                    string.push_str(" cst  ");
                    string.push_str(constant.name.as_str());
                    string.push('\n');
                }
            }
            if let Some(pallet) = self.pallets_with_errors.get(name) {
                for error in pallet.errors.values() {
                    string.push_str(" err  ");
                    string.push_str(error.as_str());
                    string.push('\n');
                }
            }
        }
        println!("{}", string);
    }

    pub fn pretty_format(metadata: &RuntimeMetadataPrefixed) -> Option<String> {
        let buf = Vec::new();
        let formatter = serde_json::ser::PrettyFormatter::with_indent(b" ");
        let mut ser = serde_json::Serializer::with_formatter(buf, formatter);
        metadata.serialize(&mut ser).unwrap();
        String::from_utf8(ser.into_inner()).ok()
    }

    pub fn print_pallets_with_calls(&self) {
        for m in self.pallets_with_calls() {
            m.print()
        }
    }

    pub fn print_pallets_with_events(&self) {
        for m in self.pallets_with_events() {
            m.print()
        }
    }

    pub fn print_pallets_with_constants(&self) {
        for m in self.pallets_with_constants() {
            m.print()
        }
    }

    pub fn print_pallets_with_errors(&self) {
        for m in self.pallets_with_errors() {
            m.print()
        }
    }

    pub fn storage_value_key(
        &self,
        storage_prefix: &'static str,
        storage_key_name: &'static str,
    ) -> Result<StorageKey, MetadataError> {
        Ok(self
            .pallet(storage_prefix)?
            .storage(storage_key_name)?
            .get_value()?
            .key())
    }

    pub fn storage_map_key<K: Encode, V: Decode + Clone>(
        &self,
        storage_prefix: &'static str,
        storage_key_name: &'static str,
        map_key: K,
    ) -> Result<StorageKey, MetadataError> {
        Ok(self
            .pallet(storage_prefix)?
            .storage(storage_key_name)?
            .get_map::<K, V>()?
            .key(map_key))
    }

    pub fn storage_map_key_prefix(
        &self,
        storage_prefix: &'static str,
        storage_key_name: &'static str,
    ) -> Result<StorageKey, MetadataError> {
        self.pallet(storage_prefix)?
            .storage(storage_key_name)?
            .get_map_prefix()
    }
}

#[derive(Clone, Debug)]
pub struct PalletMetadata {
    index: u8,
    name: String,
    storage: HashMap<String, StorageMetadata>,
    // constants
}

impl PalletMetadata {
    pub fn storage(&self, key: &'static str) -> Result<&StorageMetadata, MetadataError> {
        self.storage
            .get(key)
            .ok_or(MetadataError::StorageNotFound(key))
    }
}

// Todo make nice list of Call args to facilitate call arg lookup
#[derive(Clone, Debug)]
pub struct PalletWithCalls {
    pub index: u8,
    pub name: String,
    pub calls: HashMap<String, u8>,
}

impl PalletWithCalls {
    pub fn print(&self) {
        println!(
            "----------------- Calls for Pallet: '{}' -----------------\n",
            self.name
        );
        for (name, index) in &self.calls {
            println!("Name: {}, index {}", name, index);
        }
        println!()
    }
}

#[derive(Clone, Debug)]
pub struct PalletWithEvents {
    index: u8,
    name: String,
    events: HashMap<u8, PalletEventMetadata>,
}

impl PalletWithEvents {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn events(&self) -> impl Iterator<Item = &PalletEventMetadata> {
        self.events.values()
    }

    pub fn event(&self, index: u8) -> Result<&PalletEventMetadata, MetadataError> {
        self.events
            .get(&index)
            .ok_or(MetadataError::EventNotFound(index))
    }

    pub fn print(&self) {
        println!(
            "----------------- Events for Pallet: {} -----------------\n",
            self.name()
        );

        for e in self.events() {
            println!("Name: {:?}, Args: {:?}", e.name, e.arguments);
        }
        println!()
    }
}

#[derive(Clone, Debug)]
pub struct PalletWithErrors {
    pub index: u8,
    pub name: String,
    pub errors: HashMap<u8, String>,
}

impl PalletWithErrors {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn error(&self, index: u8) -> Result<&String, MetadataError> {
        self.errors
            .get(&index)
            .ok_or(MetadataError::ErrorNotFound(index))
    }

    pub fn print(&self) {
        println!(
            "----------------- Errors for Pallet: {} -----------------\n",
            self.name()
        );

        for e in self.errors.values() {
            println!("Name: {}", e);
        }
        println!()
    }
}

#[derive(Clone, Debug)]
pub struct PalletWithConstants {
    index: u8,
    name: String,
    constants: HashMap<u8, PalletConstantMetadata>,
}

impl PalletWithConstants {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn constants(&self) -> impl Iterator<Item = &PalletConstantMetadata> {
        self.constants.values()
    }

    pub fn constant_by_name<S>(
        &self,
        constant_name: S,
    ) -> Result<&PalletConstantMetadata, MetadataError>
    where
        S: ToString,
    {
        let name = constant_name.to_string();
        self.constants
            .values()
            .find(|&constant| constant.name == name)
            .ok_or(MetadataError::ConstantNotFound(name))
    }

    pub fn print(&self) {
        println!(
            "----------------- Constants for Pallet: {} -----------------\n",
            self.name()
        );

        for e in self.constants() {
            println!("Name: {}, Type: {}, Value{:?}", e.name, e.ty, e.value);
        }
        println!()
    }
}

#[derive(Clone, Debug)]
pub struct StorageMetadata {
    pallet_prefix: String,
    storage_prefix: String,
    modifier: StorageEntryModifier,
    ty: StorageEntryTypeInternal,
    default: Vec<u8>,
}

#[derive(Clone, Debug)]
pub enum StorageEntryTypeInternal {
    Plain,
    Map { hashers: Vec<StorageHasher> },
}

impl StorageMetadata {
    pub fn get_map<K: Encode, V: Decode + Clone>(&self) -> Result<StorageMap<K, V>, MetadataError> {
        match &self.ty {
            StorageEntryTypeInternal::Map { hashers } => {
                let pallet_prefix = self.pallet_prefix.as_bytes().to_vec();
                let storage_prefix = self.storage_prefix.as_bytes().to_vec();
                let hasher = hashers
                    .get(0)
                    .ok_or(MetadataError::StorageTypeError)?
                    .to_owned();
                let default = Decode::decode(&mut &self.default[..])
                    .map_err(|_| MetadataError::MapValueTypeError)?;

                info!(
                    "map for '{}' '{}' has hasher {:?}",
                    self.pallet_prefix, self.storage_prefix, hasher
                );
                Ok(StorageMap {
                    _marker: PhantomData,
                    pallet_prefix,
                    storage_prefix,
                    hasher,
                    default,
                })
            }
            _ => Err(MetadataError::StorageTypeError),
        }
    }
    pub fn get_map_prefix(&self) -> Result<StorageKey, MetadataError> {
        match &self.ty {
            StorageEntryTypeInternal::Map { .. } => {
                let mut bytes = sp_core::twox_128(&self.pallet_prefix.as_bytes().to_vec()).to_vec();
                bytes.extend(&sp_core::twox_128(&self.storage_prefix.as_bytes().to_vec())[..]);
                Ok(StorageKey(bytes))
            }
            _ => Err(MetadataError::StorageTypeError),
        }
    }

    pub fn get_value(&self) -> Result<StorageValue, MetadataError> {
        match &self.ty {
            StorageEntryTypeInternal::Plain => {
                let pallet_prefix = self.pallet_prefix.as_bytes().to_vec();
                let storage_prefix = self.storage_prefix.as_bytes().to_vec();
                Ok(StorageValue {
                    pallet_prefix,
                    storage_prefix,
                })
            }
            _ => Err(MetadataError::StorageTypeError),
        }
    }
}

#[derive(Clone, Debug)]
pub struct StorageValue {
    pallet_prefix: Vec<u8>,
    storage_prefix: Vec<u8>,
}

impl StorageValue {
    pub fn key(&self) -> StorageKey {
        let mut bytes = sp_core::twox_128(&self.pallet_prefix).to_vec();
        bytes.extend(&sp_core::twox_128(&self.storage_prefix)[..]);
        StorageKey(bytes)
    }
}

#[derive(Clone, Debug)]
pub struct StorageMap<K, V> {
    _marker: PhantomData<K>,
    pallet_prefix: Vec<u8>,
    storage_prefix: Vec<u8>,
    hasher: StorageHasher,
    default: V,
}

impl<K: Encode, V: Decode + Clone> StorageMap<K, V> {
    pub fn key(&self, key: K) -> StorageKey {
        let mut bytes = sp_core::twox_128(&self.pallet_prefix).to_vec();
        bytes.extend(&sp_core::twox_128(&self.storage_prefix)[..]);
        bytes.extend(key_hash(&key, &self.hasher));
        StorageKey(bytes)
    }

    pub fn default(&self) -> V {
        self.default.clone()
    }
}

#[derive(Clone, Debug)]
pub struct PalletConstantMetadata {
    name: String,
    ty: String,
    value: Vec<u8>,
}

impl PalletConstantMetadata {
    pub fn get_value(&self) -> Vec<u8> {
        self.value.clone()
    }
    pub fn get_type(&self) -> String {
        self.ty.clone()
    }
}

#[derive(Clone, Debug)]
pub struct PalletEventMetadata {
    pub name: String,
    arguments: Vec<EventArg>,
}

impl PalletEventMetadata {
    pub fn arguments(&self) -> Vec<EventArg> {
        self.arguments.to_vec()
    }
}

/// Naive representation of event argument types, supports current set of substrate EventArg types.
/// If and when Substrate uses `type-metadata`, this can be replaced.
///
/// Used to calculate the size of a instance of an event variant without having the concrete type,
/// so the raw bytes can be extracted from the encoded `Vec<EventRecord<E>>` (without `E` defined).
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum EventArg {
    Primitive(String),
    Vec(Box<EventArg>),
    Tuple(Vec<EventArg>),
}

impl FromStr for EventArg {
    type Err = ConversionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with("Vec<") {
            if s.ends_with('>') {
                Ok(EventArg::Vec(Box::new(s[4..s.len() - 1].parse()?)))
            } else {
                Err(ConversionError::InvalidEventArg(
                    s.to_string(),
                    "Expected closing `>` for `Vec`",
                ))
            }
        } else if s.starts_with('(') {
            if s.ends_with(')') {
                let mut args = Vec::new();
                for arg in s[1..s.len() - 1].split(',') {
                    let arg = arg.trim().parse()?;
                    args.push(arg)
                }
                Ok(EventArg::Tuple(args))
            } else {
                Err(ConversionError::InvalidEventArg(
                    s.to_string(),
                    "Expecting closing `)` for tuple",
                ))
            }
        } else {
            Ok(EventArg::Primitive(s.to_string()))
        }
    }
}

impl EventArg {
    /// Returns all primitive types for this EventArg
    pub fn primitives(&self) -> Vec<String> {
        match self {
            EventArg::Primitive(p) => vec![p.clone()],
            EventArg::Vec(arg) => arg.primitives(),
            EventArg::Tuple(args) => {
                let mut primitives = Vec::new();
                for arg in args {
                    primitives.extend(arg.primitives())
                }
                primitives
            }
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ConversionError {
    #[error("Invalid prefix")]
    InvalidPrefix,
    #[error("Invalid version")]
    InvalidVersion,
    #[error("Expected DecodeDifferent::Decoded")]
    ExpectedDecoded,
    #[error("Invalid event arg {0}")]
    InvalidEventArg(String, &'static str),
}

impl TryFrom<RuntimeMetadataPrefixed> for Metadata {
    type Error = MetadataError;

    fn try_from(metadata: RuntimeMetadataPrefixed) -> Result<Self, Self::Error> {
        if metadata.0 != META_RESERVED {
            return Err(ConversionError::InvalidPrefix.into());
        }
        let meta = match metadata.1 {
            RuntimeMetadata::V14(meta) => meta,
            _ => return Err(ConversionError::InvalidVersion.into()),
        };
        let mut pallets = HashMap::new();
        let mut pallets_with_calls = HashMap::new();
        let mut pallets_with_events = HashMap::new();
        let mut pallets_with_errors = HashMap::new();
        let mut pallets_with_constants = HashMap::new();

        for (index, pallet) in meta.pallets.iter().enumerate() {
            let pallet_name = pallet.name.to_string();
            let mut storage_map = HashMap::new();

            if let Some(storage) = &pallet.storage {
                for entry in &storage.entries {
                    let storage_entry_type = match &entry.ty {
                        StorageEntryType::Plain(_) => StorageEntryTypeInternal::Plain,
                        StorageEntryType::Map { hashers, .. } => StorageEntryTypeInternal::Map {
                            hashers: hashers.clone(),
                        },
                    };
                    let storage_metadata = StorageMetadata {
                        pallet_prefix: storage.prefix.clone(),
                        storage_prefix: entry.name.clone(),
                        modifier: entry.modifier.clone(),
                        ty: storage_entry_type,
                        default: entry.default.clone(),
                    };
                    storage_map.insert(entry.name.clone(), storage_metadata);
                }
            }
            pallets.insert(
                pallet_name.clone(),
                PalletMetadata {
                    index: index as u8,
                    name: pallet.name.to_string(),
                    storage: storage_map,
                },
            );

            if let Some(calls) = &pallet.calls {
                let mut call_map = HashMap::new();
                let ty = meta.types.resolve(calls.ty.id()).unwrap();
                if let scale_info::TypeDef::Variant(variant) = ty.type_def() {
                    for variant in variant.variants() {
                        call_map.insert(variant.name().clone(), variant.index());
                    }
                }

                pallets_with_calls.insert(
                    pallet_name.clone(),
                    PalletWithCalls {
                        index: pallet.index,
                        name: pallet_name.clone(),
                        calls: call_map,
                    },
                );
            }

            // TODO: EVENTS
            // if let Some(event) = &pallet.event {
            //     let mut event_map = HashMap::new();
            //     let event_ty = meta.types.resolve(event.ty.id()).unwrap();
            //     // println!(
            //     //     "{:#?} {:#?}",
            //     //     event,
            //     //     meta.types.resolve(event.ty.id()).unwrap()
            //     // );
            //     if let scale_info::TypeDef::Variant(variant) = event_ty.type_def() {
            //         // for variant in variant.variants() {
            //         //     for field in variant.fields() {
            //         //         println!(
            //         //             "{:#?}",
            //         //             meta.types.resolve(field.ty().id()).unwrap().type_def()
            //         //         );
            //         //     }
            //         // }
            //         todo!("Events are crazy");
            //     }

            //     pallets_with_events.insert(
            //         pallet_name.clone(),
            //         PalletWithEvents {
            //             index: pallet.index,
            //             name: pallet_name.clone(),
            //             events: event_map,
            //         },
            //     );
            // }

            if let Some(error) = &pallet.error {
                let mut error_map = HashMap::new();
                let error_ty = meta.types.resolve(error.ty.id()).unwrap();
                if let scale_info::TypeDef::Variant(variant) = error_ty.type_def() {
                    for variant in variant.variants() {
                        error_map.insert(variant.index(), variant.name().clone());
                    }
                }

                pallets_with_errors.insert(
                    pallet_name.clone(),
                    PalletWithErrors {
                        index: pallet.index,
                        name: pallet_name.clone(),
                        errors: error_map,
                    },
                );
            }

            let mut constant_map = HashMap::new();
            for (index, constant) in pallet.constants.iter().enumerate() {
                let const_ty = meta.types.resolve(constant.ty.id()).unwrap();
                constant_map.insert(
                    index as u8,
                    PalletConstantMetadata {
                        name: constant.name.to_string(),
                        ty: format!("{:?}", const_ty), // very hacky!
                        value: constant.value.clone(),
                    },
                );
            }
            pallets_with_constants.insert(
                pallet_name.clone(),
                PalletWithConstants {
                    index: pallet.index,
                    name: pallet_name.clone(),
                    constants: constant_map,
                },
            );
        }

        Ok(Metadata {
            pallets: pallets,
            pallets_with_calls: pallets_with_calls,
            pallets_with_events: pallets_with_events,
            pallets_with_errors: pallets_with_errors,
            pallets_with_constants: pallets_with_constants,
        })
    }
}

/// generates the key's hash depending on the StorageHasher selected
fn key_hash<K: Encode>(key: &K, hasher: &StorageHasher) -> Vec<u8> {
    let encoded_key = key.encode();
    match hasher {
        StorageHasher::Identity => encoded_key.to_vec(),
        StorageHasher::Blake2_128 => sp_core::blake2_128(&encoded_key).to_vec(),
        StorageHasher::Blake2_128Concat => {
            // copied from substrate Blake2_128Concat::hash since StorageHasher is not public
            let x: &[u8] = encoded_key.as_slice();
            sp_core::blake2_128(x)
                .iter()
                .chain(x.iter())
                .cloned()
                .collect::<Vec<_>>()
        }
        StorageHasher::Blake2_256 => sp_core::blake2_256(&encoded_key).to_vec(),
        StorageHasher::Twox128 => sp_core::twox_128(&encoded_key).to_vec(),
        StorageHasher::Twox256 => sp_core::twox_256(&encoded_key).to_vec(),
        StorageHasher::Twox64Concat => sp_core::twox_64(&encoded_key)
            .iter()
            .chain(&encoded_key)
            .cloned()
            .collect(),
    }
}

// Bitcoin protocol consensus library.
//
// SPDX-License-Identifier: Apache-2.0
//
// Designed in 2019-2025 by Dr Maxim Orlovsky <orlovsky@lnp-bp.org>
// Written in 2024-2025 by Dr Maxim Orlovsky <orlovsky@lnp-bp.org>
//
// Copyright (C) 2019-2024 LNP/BP Standards Association, Switzerland.
// Copyright (C) 2024-2025 LNP/BP Labs, Institute for Distributed and Cognitive Systems (InDCS).
// Copyright (C) 2019-2025 Dr Maxim Orlovsky.
// All rights under the above copyrights are reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![allow(unused_braces)] // required due to strict dumb derivation and compiler bug

use std::fmt::{self, Formatter, LowerHex, UpperHex};
use std::io::{Read, Write};
use std::ops::BitXor;
use std::str::FromStr;
use std::{io, slice, vec};

use amplify::confinement::Confined;
use amplify::hex::FromHex;
use amplify::{confinement, ByteArray, Bytes32, Wrapper, IoError};
use bitcoin_hashes::{sha256, HashEngine};
use secp256k1::{Keypair, PublicKey, Scalar, XOnlyPublicKey};
use strict_encoding::{
    DecodeError, ReadTuple, StrictDecode, StrictEncode, StrictProduct, StrictTuple, StrictType,
    TypeName, TypedRead, TypedWrite, WriteTuple,
};

use crate::opcodes::*;
use crate::{
    CompressedPk, ConsensusDataError, ConsensusDecode, ConsensusDecodeError, ConsensusEncode,
    InvalidPubkey, PubkeyParseError, ScriptBytes, ScriptPubkey, TapCode, VarInt, VarIntBytes,
    WitnessVer, LIB_NAME_BITCOIN,
};

// [最终修复] 创建一个保证符合 BIP-340 规范的标记哈希引擎的辅助函数
fn tagged_hash_engine(tag: &[u8]) -> sha256::HashEngine {
    let tag_hash = sha256::Hash::hash(tag);
    let mut engine = sha256::Hash::engine();
    engine.input(tag_hash.as_byte_array());
    engine.input(tag_hash.as_byte_array());
    engine
}

impl<const LEN: usize> From<InvalidPubkey<LEN>> for DecodeError {
    fn from(e: InvalidPubkey<LEN>) -> Self {
        DecodeError::DataIntegrityError(format!("invalid x-only public key value '{e}'"))
    }
}

#[derive(Wrapper, WrapperMut, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, From)]
#[wrapper(Deref, LowerHex, Display)]
#[wrapper_mut(DerefMut)]
#[derive(StrictType, StrictDumb)]
#[strict_type(lib = LIB_NAME_BITCOIN, dumb = Self::dumb())]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(transparent)
)]
pub struct XOnlyPk(XOnlyPublicKey);

impl XOnlyPk {
    fn dumb() -> Self { Self(XOnlyPublicKey::from_slice(&[1u8; 32]).unwrap()) }

    pub fn from_byte_array(data: [u8; 32]) -> Result<Self, InvalidPubkey<32>> {
        XOnlyPublicKey::from_slice(data.as_ref())
            .map(Self)
            .map_err(|_| InvalidPubkey::Specified(data.into()))
    }

    pub fn to_byte_array(&self) -> [u8; 32] { self.0.serialize() }

    pub fn from_bytes(bytes: impl AsRef<[u8]>) -> Result<Self, InvalidPubkey<33>> {
        Ok(XOnlyPk(XOnlyPublicKey::from_slice(bytes.as_ref())?))
    }
}

impl From<CompressedPk> for XOnlyPk {
    fn from(pubkey: CompressedPk) -> Self { XOnlyPk(pubkey.x_only_public_key().0) }
}

impl From<PublicKey> for XOnlyPk {
    fn from(pubkey: PublicKey) -> Self { XOnlyPk(pubkey.x_only_public_key().0) }
}

impl From<XOnlyPk> for [u8; 32] {
    fn from(pk: XOnlyPk) -> [u8; 32] { pk.to_byte_array() }
}

impl StrictEncode for XOnlyPk {
    fn strict_encode<W: TypedWrite>(&self, writer: W) -> io::Result<W> {
        let bytes = Bytes32::from(self.0.serialize());
        writer.write_newtype::<Self>(&bytes)
    }
}

impl StrictDecode for XOnlyPk {
    fn strict_decode(reader: &mut impl TypedRead) -> Result<Self, DecodeError> {
        reader.read_tuple(|r| {
            let bytes: Bytes32 = r.read_field()?;
            XOnlyPublicKey::from_slice(bytes.as_slice())
                .map(Self)
                .map_err(|_| InvalidPubkey::Specified(bytes).into())
        })
    }
}

impl FromStr for XOnlyPk {
    type Err = PubkeyParseError<32>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let data = <[u8; 32]>::from_hex(s)?;
        let pk = Self::from_byte_array(data)?;
        Ok(pk)
    }
}

#[derive(Eq, PartialEq, From)]
pub struct InternalKeypair(#[from] Keypair);

impl InternalKeypair {
    pub fn to_output_keypair(&self, merkle_root: Option<TapNodeHash>) -> (Keypair, Parity) {
        let internal_pk = self.0.x_only_public_key().0;
        let mut engine = tagged_hash_engine(b"TapTweak");
        engine.input(&internal_pk.serialize());
        if let Some(merkle_root) = merkle_root {
            engine.input(merkle_root.as_ref());
        }
        let tweak_bytes = sha256::Hash::from_engine(engine).to_byte_array();
        let tweak =
            Scalar::from_be_bytes(tweak_bytes).expect("hash value greater than curve order");
        let pair = self
            .0
            .add_xonly_tweak(secp256k1::SECP256K1, &tweak)
            .expect("hash collision");
        let (outpput_key, tweaked_parity) = pair.x_only_public_key();
        debug_assert!(internal_pk.tweak_add_check(
            secp256k1::SECP256K1,
            &outpput_key,
            tweaked_parity,
            tweak
        ));
        (pair, tweaked_parity.into())
    }
}

#[derive(Wrapper, WrapperMut, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, From)]
#[wrapper(Deref, LowerHex, Display, FromStr)]
#[wrapper_mut(DerefMut)]
#[derive(StrictType, StrictDumb, StrictEncode, StrictDecode)]
#[strict_type(lib = LIB_NAME_BITCOIN)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(transparent)
)]
pub struct InternalPk(
    #[from]
    #[from(XOnlyPublicKey)]
    XOnlyPk,
);

impl InternalPk {
    #[inline]
    pub fn from_unchecked(pk: XOnlyPk) -> Self { Self(pk) }

    #[inline]
    pub fn from_byte_array(data: [u8; 32]) -> Result<Self, InvalidPubkey<32>> {
        XOnlyPk::from_byte_array(data).map(Self)
    }

    #[inline]
    pub fn from_bytes(bytes: impl AsRef<[u8]>) -> Result<Self, InvalidPubkey<33>> {
        XOnlyPk::from_bytes(bytes).map(Self)
    }

    #[inline]
    pub fn to_byte_array(&self) -> [u8; 32] { self.0.to_byte_array() }

    #[inline]
    pub fn to_xonly_pk(&self) -> XOnlyPk { self.0 }

    pub fn to_output_pk(&self, merkle_root: Option<TapNodeHash>) -> (OutputPk, Parity) {
        let mut engine = tagged_hash_engine(b"TapTweak");
        engine.input(&self.0.serialize());
        if let Some(merkle_root) = merkle_root {
            engine.input(merkle_root.as_ref());
        }
        let tweak_bytes = sha256::Hash::from_engine(engine).to_byte_array();
        let tweak =
            Scalar::from_be_bytes(tweak_bytes).expect("hash value greater than curve order");
        let (output_key, tweaked_parity) = self
            .0
            .add_tweak(secp256k1::SECP256K1, &tweak)
            .expect("hash collision");
        debug_assert!(self.tweak_add_check(
            secp256k1::SECP256K1,
            &output_key,
            tweaked_parity,
            tweak
        ));
        (OutputPk(XOnlyPk(output_key)), tweaked_parity.into())
    }
}

impl From<InternalPk> for [u8; 32] {
    fn from(pk: InternalPk) -> [u8; 32] { pk.to_byte_array() }
}

#[derive(Wrapper, WrapperMut, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, From)]
#[wrapper(Deref, LowerHex, Display, FromStr)]
#[wrapper_mut(DerefMut)]
#[derive(StrictType, StrictEncode, StrictDecode, StrictDumb)]
#[strict_type(lib = LIB_NAME_BITCOIN)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(transparent)
)]
pub struct OutputPk(XOnlyPk);

impl OutputPk {
    #[inline]
    pub fn from_unchecked(pk: XOnlyPk) -> Self { Self(pk) }

    #[inline]
    pub fn from_byte_array(data: [u8; 32]) -> Result<Self, InvalidPubkey<32>> {
        XOnlyPk::from_byte_array(data).map(Self)
    }

    #[inline]
    pub fn from_bytes(bytes: impl AsRef<[u8]>) -> Result<Self, InvalidPubkey<33>> {
        XOnlyPk::from_bytes(bytes).map(Self)
    }

    #[inline]
    pub fn to_xonly_pk(&self) -> XOnlyPk { self.0 }

    #[inline]
    pub fn to_script_pubkey(&self) -> ScriptPubkey { ScriptPubkey::p2tr_tweaked(*self) }

    #[inline]
    pub fn to_byte_array(&self) -> [u8; 32] { self.0.to_byte_array() }
}

impl From<OutputPk> for [u8; 32] {
    fn from(pk: OutputPk) -> [u8; 32] { pk.to_byte_array() }
}

pub trait IntoTapHash {
    fn into_tap_hash(self) -> TapNodeHash;
}

#[derive(Wrapper, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, From)]
#[wrapper(Index, RangeOps, AsSlice, BorrowSlice, Hex, Display, FromStr)]
#[derive(StrictType, StrictDumb, StrictEncode, StrictDecode)]
#[strict_type(lib = LIB_NAME_BITCOIN)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(transparent)
)]
pub struct TapSighash(
    #[from]
    #[from([u8; 32])]
    pub Bytes32,
);

impl From<TapSighash> for [u8; 32] {
    fn from(value: TapSighash) -> Self { value.0.into_inner() }
}

impl From<TapSighash> for secp256k1::Message {
    fn from(sighash: TapSighash) -> Self {
        secp256k1::Message::from_digest(sighash.to_byte_array())
    }
}

impl TapSighash {
    pub fn engine() -> sha256::HashEngine { tagged_hash_engine(b"TapSighash") }

    pub fn from_engine(engine: sha256::HashEngine) -> Self {
        Self(sha256::Hash::from_engine(engine).to_byte_array().into())
    }
}

#[derive(Wrapper, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, From)]
#[wrapper(Index, RangeOps, BorrowSlice, Hex, Display, FromStr)]
#[derive(StrictType, StrictEncode, StrictDecode, StrictDumb)]
#[strict_type(lib = LIB_NAME_BITCOIN)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(transparent)
)]
pub struct TapLeafHash(
    #[from]
    #[from([u8; 32])]
    Bytes32,
);

impl TapLeafHash {
    pub fn with_leaf_script(leaf_script: &LeafScript) -> Self {
        Self::with_raw_script(leaf_script.version, leaf_script.as_script_bytes())
    }

    pub fn with_tap_script(tap_script: &TapScript) -> Self {
        Self::with_raw_script(LeafVer::TapScript, tap_script.as_script_bytes())
    }

    fn with_raw_script(version: LeafVer, script: &ScriptBytes) -> Self {
        let mut engine = tagged_hash_engine(b"TapLeaf");
        engine.input(&[version.to_consensus_u8()]);
        let mut varint_buf = Vec::new();
        script
            .len_var_int()
            .consensus_encode(&mut varint_buf)
            .unwrap();
        engine.input(&varint_buf);
        engine.input(script.as_slice());
        Self(sha256::Hash::from_engine(engine).to_byte_array().into())
    }
}

impl IntoTapHash for TapLeafHash {
    fn into_tap_hash(self) -> TapNodeHash { TapNodeHash(self.0) }
}

#[derive(Wrapper, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, From)]
#[wrapper(Index, RangeOps, BorrowSlice, Hex, Display, FromStr)]
#[derive(StrictType, StrictEncode, StrictDecode, StrictDumb)]
#[strict_type(lib = LIB_NAME_BITCOIN)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(transparent)
)]
pub struct TapBranchHash(
    #[from]
    #[from([u8; 32])]
    Bytes32,
);

impl TapBranchHash {
    pub fn with_nodes(node1: TapNodeHash, node2: TapNodeHash) -> Self {
        let mut engine = tagged_hash_engine(b"TapBranch");
        if node1.to_byte_array() < node2.to_byte_array() {
            engine.input(node1.0.as_slice());
            engine.input(node2.0.as_slice());
        } else {
            engine.input(node2.0.as_slice());
            engine.input(node1.0.as_slice());
        }
        Self(sha256::Hash::from_engine(engine).to_byte_array().into())
    }
}

impl IntoTapHash for TapBranchHash {
    fn into_tap_hash(self) -> TapNodeHash { TapNodeHash(self.0) }
}

#[derive(Wrapper, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, From)]
#[wrapper(Index, RangeOps, AsSlice, BorrowSlice, Hex, Display, FromStr)]
#[derive(StrictType, StrictDumb, StrictEncode, StrictDecode)]
#[strict_type(lib = LIB_NAME_BITCOIN)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(transparent)
)]
pub struct TapNodeHash(
    #[from]
    #[from([u8; 32])]
    #[from(TapLeafHash)]
    #[from(TapBranchHash)]
    Bytes32,
);

impl IntoTapHash for TapNodeHash {
    fn into_tap_hash(self) -> TapNodeHash { self }
}

// [BUG 修复] 为 TapNodeHash 添加共识编码/解码实现
impl ConsensusEncode for TapNodeHash {
    fn consensus_encode(&self, writer: &mut impl Write) -> Result<usize, IoError> {
        writer.write_all(&self.to_byte_array())?;
        Ok(32)
    }
}

impl ConsensusDecode for TapNodeHash {
    fn consensus_decode(reader: &mut impl Read) -> Result<Self, ConsensusDecodeError> {
        let mut buf = [0u8; 32];
        reader.read_exact(&mut buf)?;
        Ok(TapNodeHash::from_byte_array(buf))
    }
}
#[derive(Wrapper, WrapperMut, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, From, Default)]
#[wrapper(Deref)]
#[wrapper_mut(DerefMut)]
#[derive(StrictType, StrictEncode, StrictDecode)]
#[strict_type(lib = LIB_NAME_BITCOIN)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(transparent)
)]
pub struct TapMerklePath(Confined<Vec<TapNodeHash>, 0, 128>);

impl IntoIterator for TapMerklePath {
    type Item = TapNodeHash;
    type IntoIter = vec::IntoIter<TapNodeHash>;

    fn into_iter(self) -> Self::IntoIter { self.0.into_iter() }
}

impl<'a> IntoIterator for &'a TapMerklePath {
    type Item = &'a TapNodeHash;
    type IntoIter = slice::Iter<'a, TapNodeHash>;

    fn into_iter(self) -> Self::IntoIter { self.0.iter() }
}

impl TapMerklePath {
    #[inline]
    pub fn try_from(path: Vec<TapNodeHash>) -> Result<Self, confinement::Error> {
        Confined::try_from(path).map(Self::from_inner)
    }

    #[inline]
    pub fn try_from_iter<I: IntoIterator<Item = TapNodeHash>>(
        iter: I,
    ) -> Result<Self, confinement::Error> {
        Confined::try_from_iter(iter).map(Self::from_inner)
    }
}

pub const TAPROOT_ANNEX_PREFIX: u8 = 0x50;
pub const TAPROOT_LEAF_TAPSCRIPT: u8 = 0xc0;
pub const TAPROOT_LEAF_MASK: u8 = 0xfe;

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug, Display, Error)]
#[display(doc_comments)]
pub struct InvalidLeafVer(u8);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(rename_all = "camelCase")
)]
pub enum LeafVer {
    #[default]
    TapScript,
    Future(FutureLeafVer),
}

impl StrictType for LeafVer {
    const STRICT_LIB_NAME: &'static str = LIB_NAME_BITCOIN;
    fn strict_name() -> Option<TypeName> { Some(tn!("LeafVer")) }
}
impl StrictProduct for LeafVer {}
impl StrictTuple for LeafVer {
    const FIELD_COUNT: u8 = 1;
}
impl StrictEncode for LeafVer {
    fn strict_encode<W: TypedWrite>(&self, writer: W) -> std::io::Result<W> {
        writer.write_tuple::<Self>(|w| Ok(w.write_field(&self.to_consensus_u8())?.complete()))
    }
}
impl StrictDecode for LeafVer {
    fn strict_decode(reader: &mut impl TypedRead) -> Result<Self, DecodeError> {
        reader.read_tuple(|r| {
            let version = r.read_field()?;
            Self::from_consensus_u8(version)
                .map_err(|err| DecodeError::DataIntegrityError(err.to_string()))
        })
    }
}

impl LeafVer {
    pub fn from_consensus_u8(version: u8) -> Result<Self, InvalidLeafVer> {
        match version {
            TAPROOT_LEAF_TAPSCRIPT => Ok(LeafVer::TapScript),
            TAPROOT_ANNEX_PREFIX => Err(InvalidLeafVer(TAPROOT_ANNEX_PREFIX)),
            future => FutureLeafVer::from_consensus(future).map(LeafVer::Future),
        }
    }

    pub fn to_consensus_u8(self) -> u8 {
        match self {
            LeafVer::TapScript => TAPROOT_LEAF_TAPSCRIPT,
            LeafVer::Future(version) => version.to_consensus(),
        }
    }
}

impl LowerHex for LeafVer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result { LowerHex::fmt(&self.to_consensus_u8(), f) }
}

impl UpperHex for LeafVer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result { UpperHex::fmt(&self.to_consensus_u8(), f) }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[derive(StrictType, StrictDumb, StrictEncode, StrictDecode)]
#[strict_type(lib = LIB_NAME_BITCOIN, dumb = { Self(0x51) })]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(transparent)
)]
pub struct FutureLeafVer(u8);

impl FutureLeafVer {
    pub(self) fn from_consensus(version: u8) -> Result<FutureLeafVer, InvalidLeafVer> {
        match version {
            TAPROOT_LEAF_TAPSCRIPT => unreachable!(),
            TAPROOT_ANNEX_PREFIX => Err(InvalidLeafVer(TAPROOT_ANNEX_PREFIX)),
            odd if odd & 0xFE != odd => Err(InvalidLeafVer(odd)),
            even => Ok(FutureLeafVer(even)),
        }
    }

    #[inline]
    pub fn to_consensus(self) -> u8 { self.0 }
}

impl LowerHex for FutureLeafVer {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result { LowerHex::fmt(&self.0, f) }
}

impl UpperHex for FutureLeafVer {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result { UpperHex::fmt(&self.0, f) }
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, Default, Display)]
#[derive(StrictType, StrictEncode, StrictDecode)]
#[strict_type(lib = LIB_NAME_BITCOIN)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(rename_all = "camelCase")
)]
#[display("{version:04x} {script:x}")]
pub struct LeafScript {
    pub version: LeafVer,
    pub script: ScriptBytes,
}

impl From<TapScript> for LeafScript {
    fn from(tap_script: TapScript) -> Self {
        LeafScript {
            version: LeafVer::TapScript,
            script: tap_script.into_inner(),
        }
    }
}

impl LeafScript {
    #[inline]
    pub fn new(version: LeafVer, script: ScriptBytes) -> Self { LeafScript { version, script } }
    #[inline]
    pub fn with_bytes(version: LeafVer, script: Vec<u8>) -> Result<Self, confinement::Error> {
        Ok(LeafScript {
            version,
            script: ScriptBytes::try_from(script)?,
        })
    }
    #[inline]
    pub fn from_tap_script(tap_script: TapScript) -> Self { Self::from(tap_script) }

    #[inline]
    pub fn as_script_bytes(&self) -> &ScriptBytes { &self.script }

    #[inline]
    pub fn tap_leaf_hash(&self) -> TapLeafHash { TapLeafHash::with_leaf_script(self) }
}

#[derive(Wrapper, WrapperMut, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, From, Default)]
#[wrapper(Deref, AsSlice, Hex)]
#[wrapper_mut(DerefMut, AsSliceMut)]
#[derive(StrictType, StrictEncode, StrictDecode)]
#[strict_type(lib = LIB_NAME_BITCOIN)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(transparent)
)]
pub struct TapScript(ScriptBytes);

impl TryFrom<Vec<u8>> for TapScript {
    type Error = confinement::Error;
    fn try_from(script_bytes: Vec<u8>) -> Result<Self, Self::Error> {
        ScriptBytes::try_from(script_bytes).map(Self)
    }
}

impl TapScript {
    #[inline]
    pub fn new() -> Self { Self::default() }

    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self(ScriptBytes::from(Confined::with_capacity(capacity)))
    }

    #[inline]
    pub fn from_checked(script_bytes: Vec<u8>) -> Self {
        Self(ScriptBytes::from_checked(script_bytes))
    }

    #[inline]
    pub fn tap_leaf_hash(&self) -> TapLeafHash { TapLeafHash::with_tap_script(self) }

    #[inline]
    pub fn push_opcode(&mut self, op_code: TapCode) { self.0.push(op_code as u8); }

    #[inline]
    pub fn as_script_bytes(&self) -> &ScriptBytes { &self.0 }
}

impl ScriptPubkey {
    pub fn p2tr(internal_key: InternalPk, merkle_root: Option<TapNodeHash>) -> Self {
        let (output_key, _) = internal_key.to_output_pk(merkle_root);
        Self::p2tr_tweaked(output_key)
    }

    pub fn p2tr_key_only(internal_key: InternalPk) -> Self {
        let (output_key, _) = internal_key.to_output_pk(None);
        Self::p2tr_tweaked(output_key)
    }

    pub fn p2tr_scripted(internal_key: InternalPk, merkle_root: impl IntoTapHash) -> Self {
        let (output_key, _) = internal_key.to_output_pk(Some(merkle_root.into_tap_hash()));
        Self::p2tr_tweaked(output_key)
    }

    pub fn p2tr_tweaked(output_key: OutputPk) -> Self {
        Self::with_witness_program_unchecked(WitnessVer::V1, &output_key.serialize())
    }

    pub fn is_p2tr(&self) -> bool {
        self.len() == 34 && self[0] == WitnessVer::V1.op_code() as u8 && self[1] == OP_PUSHBYTES_32
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Display, Error)]
#[display(doc_comments)]
pub struct InvalidParityValue(pub u8);

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Display)]
#[display(lowercase)]
#[derive(StrictType, StrictEncode, StrictDecode, StrictDumb)]
#[strict_type(lib = LIB_NAME_BITCOIN, tags = repr, into_u8, try_from_u8)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(rename_all = "camelCase")
)]
#[repr(u8)]
pub enum Parity {
    #[strict_type(dumb)]
    Even = 0,
    Odd = 1,
}

impl From<secp256k1::Parity> for Parity {
    fn from(parity: secp256k1::Parity) -> Self {
        match parity {
            secp256k1::Parity::Even => Parity::Even,
            secp256k1::Parity::Odd => Parity::Odd,
        }
    }
}

impl Parity {
    pub fn to_consensus_u8(self) -> u8 { self as u8 }

    pub fn from_consensus_u8(parity: u8) -> Result<Parity, InvalidParityValue> {
        match parity {
            0 => Ok(Parity::Even),
            1 => Ok(Parity::Odd),
            invalid => Err(InvalidParityValue(invalid)),
        }
    }
}

impl BitXor for Parity {
    type Output = Parity;

    fn bitxor(self, rhs: Parity) -> Self::Output {
        if self == rhs {
            Parity::Even
        } else {
            Parity::Odd
        }
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
#[derive(StrictType, StrictEncode, StrictDecode, StrictDumb)]
#[strict_type(lib = LIB_NAME_BITCOIN)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(rename_all = "camelCase")
)]
pub struct ControlBlock {
    pub leaf_version: LeafVer,
    pub output_key_parity: Parity,
    pub internal_pk: InternalPk,
    pub merkle_branch: TapMerklePath,
}

impl ControlBlock {
    #[inline]
    pub fn with(
        leaf_version: LeafVer,
        internal_pk: InternalPk,
        output_key_parity: Parity,
        merkle_branch: TapMerklePath,
    ) -> Self {
        ControlBlock {
            leaf_version,
            output_key_parity,
            internal_pk,
            merkle_branch,
        }
    }
}

impl ConsensusEncode for ControlBlock {
    fn consensus_encode(&self, writer: &mut impl Write) -> Result<usize, IoError> {
        let mut counter = 1;

        let first_byte =
            self.leaf_version.to_consensus_u8() | self.output_key_parity.to_consensus_u8();
        first_byte.consensus_encode(writer)?;

        counter += self.internal_pk.consensus_encode(writer)?;
        for step in &self.merkle_branch {
            counter += step.consensus_encode(writer)?;
        }

        Ok(counter)
    }
}

impl ConsensusDecode for ControlBlock {
    fn consensus_decode(reader: &mut impl Read) -> Result<Self, ConsensusDecodeError> {
        let first_byte = u8::consensus_decode(reader)?;
        let leaf_version = LeafVer::from_consensus_u8(first_byte & 0xFE)?;
        let output_key_parity = Parity::from_consensus_u8(first_byte & 0x01).expect("binary value");

        let internal_key = InternalPk::consensus_decode(reader)?;

        let mut buf = vec![];
        reader.read_to_end(&mut buf)?;
        if buf.len() % 32 != 0 {
            return Err(ConsensusDataError::InvalidTapMerklePath.into());
        }
        let iter = buf
            .chunks_exact(32)
            .map(|slice| TapNodeHash::from_slice(slice).expect("32-byte slice"));
        let merkle_branch = TapMerklePath::try_from_iter(iter)
            .map_err(|_| ConsensusDataError::LongTapMerklePath)?;

        Ok(ControlBlock {
            leaf_version,
            output_key_parity,
            internal_pk: internal_key,
            merkle_branch,
        })
    }
}


#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Display, Error, From)]
#[display(doc_comments)]
pub enum AnnexError {
    #[from]
    WrongFirstByte(u8),
    #[from]
    Size(confinement::Error),
}

#[derive(Wrapper, WrapperMut, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, From)]
#[wrapper(Deref, AsSlice, Hex)]
#[wrapper_mut(DerefMut, AsSliceMut)]
#[derive(StrictType, StrictDumb, StrictEncode, StrictDecode)]
#[strict_type(lib = LIB_NAME_BITCOIN, dumb = { Self(VarIntBytes::with(0x50)) })]
pub struct Annex(VarIntBytes<1>);

impl TryFrom<Vec<u8>> for Annex {
    type Error = confinement::Error;
    fn try_from(script_bytes: Vec<u8>) -> Result<Self, Self::Error> {
        Confined::try_from(script_bytes).map(Self)
    }
}

impl Annex {
    #[inline]
    pub fn new(annex_bytes: Vec<u8>) -> Result<Self, AnnexError> {
        let annex = Confined::try_from(annex_bytes).map(Self)?;
        if annex[0] != TAPROOT_ANNEX_PREFIX {
            return Err(AnnexError::WrongFirstByte(annex[0]));
        }
        Ok(annex)
    }

    pub fn len_var_int(&self) -> VarInt { VarInt(self.len() as u64) }

    pub fn into_vec(self) -> Vec<u8> { self.0.release() }

    pub fn as_slice(&self) -> &[u8] { self.0.as_slice() }

    pub(crate) fn as_var_int_bytes(&self) -> &VarIntBytes<1> { &self.0 }
}

#[cfg(feature = "serde")]
mod _serde {
    use amplify::hex::{FromHex, ToHex};
    use serde::de::Error;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    use super::*;

    impl Serialize for Annex {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer {
            if serializer.is_human_readable() {
                serializer.serialize_str(&self.to_hex())
            } else {
                serializer.serialize_bytes(self.as_slice())
            }
        }
    }

    impl<'de> Deserialize<'de> for Annex {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de> {
            if deserializer.is_human_readable() {
                String::deserialize(deserializer).and_then(|string| {
                    Self::from_hex(&string).map_err(|_| D::Error::custom("wrong hex data"))
                })
            } else {
                let bytes = Vec::<u8>::deserialize(deserializer)?;
                Self::new(bytes).map_err(|_| D::Error::custom("invalid annex data"))
            }
        }
    }
}
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

use std::borrow::Borrow;

use amplify::{ByteArray, Bytes32, IoError};
use commit_verify::{Digest, Sha256};
use bitcoin_hashes::{sha256, HashEngine};
use crate::{
    Annex, ConsensusEncode, Sats, ScriptCode, ScriptPubkey, SeqNo, SigScript, Sighash, SighashFlag,
    SighashType, TapLeafHash, TapSighash, Tx as Transaction, TxIn, TxOut, Txid, VarIntArray,
};

fn tagged_hash_engine(tag: &'static str) -> sha256::HashEngine {
    // 1. 计算 tag 的哈希
    let mut tag_engine = sha256::Hash::engine();
    tag_engine.input(tag.as_bytes());
    let tag_hash = sha256::Hash::from_engine(tag_engine);

    // 2. 创建最终的引擎，并用 tag_hash 作为前缀输入两次
    let mut engine = sha256::Hash::engine();
    engine.input(tag_hash.as_byte_array());
    engine.input(tag_hash.as_byte_array());

    engine
}
/// Used for signature hash for invalid use of SIGHASH_SINGLE.
const UINT256_ONE: [u8; 32] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
];

#[derive(Copy, Clone, Eq, PartialEq, Debug, Display, Error)]
#[display(
    "number of inputs ({inputs}) doesn't match to the number of provided prevouts ({prevouts}) \
     for signature hasher on tx {txid}."
)]
pub struct PrevoutMismatch {
    txid: Txid,
    inputs: usize,
    prevouts: usize,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Display, Error)]
#[display(doc_comments)]
pub enum SighashError {
    /// invalid input index {index} in {txid} which has only {inputs} inputs.
    InvalidInputIndex {
        txid: Txid,
        index: usize,
        inputs: usize,
    },

    /// transaction {txid} input {index} uses SIGHASH_SINGLE, but the total
    /// number of outputs is {outputs} and thus no signature can be produced.
    NoSingleOutputMatch {
        txid: Txid,
        index: usize,
        outputs: usize,
    },
}

impl From<IoError> for SighashError {
    fn from(_: IoError) -> Self { unreachable!("in-memory I/O doesn't error in Rust") }
}

/// Efficiently calculates signature hash message for legacy, segwit and taproot
/// inputs.
#[derive(Debug)]
pub struct SighashCache<Prevout: Borrow<TxOut> = TxOut, Tx: Borrow<Transaction> = Transaction> {
    /// Access to transaction required for transaction introspection.
    tx: Tx,

    prevouts: Vec<Prevout>,

    /// Common cache for taproot and segwit inputs, `None` for legacy inputs.
    common_cache: Option<CommonCache>,

    /// Cache for segwit v0 inputs (the result of another round of sha256 on
    /// `common_cache`).
    segwit_cache: Option<SegwitCache>,

    /// Cache for taproot v1 inputs.
    taproot_cache: Option<TaprootCache>,
}

/// Common values cached between segwit and taproot inputs.
#[derive(Copy, Clone, Debug)]
struct CommonCache {
    prevouts: Bytes32,
    sequences: Bytes32,

    /// In theory `outputs` could be an `Option` since `SIGHASH_NONE` and
    /// `SIGHASH_SINGLE` do not need it, but since `SIGHASH_ALL` is by far
    /// the most used variant we don't bother.
    outputs: Bytes32,
}

/// Values cached for segwit inputs, equivalent to [`CommonCache`] plus another
/// round of `sha256`.
#[derive(Copy, Clone, Debug)]
struct SegwitCache {
    prevouts: Bytes32,
    sequences: Bytes32,
    outputs: Bytes32,
}

/// Values cached for taproot inputs.
#[derive(Copy, Clone, Debug)]
struct TaprootCache {
    amounts: Bytes32,
    script_pubkeys: Bytes32,
}

impl<Prevout: Borrow<TxOut>, Tx: Borrow<Transaction>> SighashCache<Prevout, Tx> {
    /// Constructs a new `SighashCache` from an unsigned transaction.
    ///
    /// The sighash components are computed in a lazy manner when required. For
    /// the generated sighashes to be valid, no fields in the transaction
    /// may change except for script_sig and witness.
    pub fn new(tx: Tx, prevouts: Vec<Prevout>) -> Result<Self, PrevoutMismatch> {
        if tx.borrow().inputs.len() != prevouts.len() {
            return Err(PrevoutMismatch {
                txid: tx.borrow().txid(),
                inputs: tx.borrow().inputs.len(),
                prevouts: prevouts.len(),
            });
        }

        Ok(SighashCache {
            tx,
            prevouts,
            common_cache: None,
            taproot_cache: None,
            segwit_cache: None,
        })
    }

    /// Computes the BIP341 sighash for any type with a fine-grained control
    /// over annex and code separator.
    pub fn tap_sighash_custom(
        &mut self,
        input_index: usize,
        annex: Option<Annex>,
        leaf_hash_code_separator: Option<(TapLeafHash, u32)>,
        sighash_type: Option<SighashType>,
    ) -> Result<TapSighash, SighashError> {

        let tx = self.tx.borrow();
        let sighash_type = sighash_type.unwrap_or_default();
        let (sighash_flag, anyone_can_pay) = (sighash_type.flag, sighash_type.anyone_can_pay);

        // 1. 创建带 "TapSighash" 标记的哈希引擎
        let mut engine = tagged_hash_engine("TapSighash");

        // 2. 写入头部数据 (8 字节)
        engine.input(&[0u8]); // epoch
        engine.input(&[sighash_type.into_consensus_u8()]);
        engine.input(&tx.version.to_consensus_u32().to_le_bytes());
        engine.input(&tx.lock_time.to_consensus_u32().to_le_bytes());

        // 3. 写入 Prevouts, Amounts, ScriptPubkeys, Sequences 的哈希 (4 * 32 = 128 字节)
        if !anyone_can_pay {
            let mut prevouts_hasher = sha256::Hash::engine();
            let mut amounts_hasher = sha256::Hash::engine();
            let mut scriptpubkeys_hasher = sha256::Hash::engine();
            let mut sequences_hasher = sha256::Hash::engine();

            for i in 0..tx.inputs.len() {
                tx.inputs[i].prev_output.consensus_encode(&mut prevouts_hasher)?;
                self.prevouts[i].borrow().value.consensus_encode(&mut amounts_hasher)?;
                self.prevouts[i].borrow().script_pubkey.consensus_encode(&mut scriptpubkeys_hasher)?;
                tx.inputs[i].sequence.consensus_encode(&mut sequences_hasher)?;
            }

            engine.input(sha256::Hash::from_engine(prevouts_hasher).as_byte_array());
            engine.input(sha256::Hash::from_engine(amounts_hasher).as_byte_array());
            engine.input(sha256::Hash::from_engine(scriptpubkeys_hasher).as_byte_array());
            engine.input(sha256::Hash::from_engine(sequences_hasher).as_byte_array());
        }

        // 4. 写入 Outputs 哈希 (32 字节)
        if sighash_flag != SighashFlag::None && sighash_flag != SighashFlag::Single {
            let mut outputs_hasher = sha256::Hash::engine();
            for output in &tx.outputs {
                output.consensus_encode(&mut outputs_hasher)?;
            }
            engine.input(sha256::Hash::from_engine(outputs_hasher).as_byte_array());
        }

        // 5. 写入 Spend Type (1 字节)
        let mut spend_type = 0u8;
        if annex.is_some() {
            spend_type |= 1;
        }
        if leaf_hash_code_separator.is_some() {
            spend_type |= 2;
        }
        engine.input(&[spend_type]);

        // 6. 写入当前输入的数据
        if anyone_can_pay {
            // outpoint (36) + amount (8) + scriptPubKey (var_int + bytes) + nSequence (4)
            let txin = &tx.inputs[input_index];
            let prevout = self.prevouts[input_index].borrow();
            txin.prev_output.consensus_encode(&mut engine)?;
            prevout.value.consensus_encode(&mut engine)?;
            prevout.script_pubkey.consensus_encode(&mut engine)?;
            txin.sequence.consensus_encode(&mut engine)?;
        } else {
            // input_index (4)
            engine.input(&(input_index as u32).to_le_bytes());
        }

        // 7. 写入 Annex 哈希 (32 字节, 如果存在)
        if let Some(annex) = annex {
            let mut annex_hasher = sha256::Hash::engine();
            annex.consensus_encode(&mut annex_hasher)?;
            engine.input(sha256::Hash::from_engine(annex_hasher).as_byte_array());
        }

        // 8. 写入 SIGHASH_SINGLE 的 Output 哈希 (32 字节)
        if sighash_flag == SighashFlag::Single {
            let output = tx.outputs.get(input_index)
                .ok_or(SighashError::NoSingleOutputMatch { txid: tx.txid(), index: input_index, outputs: tx.outputs.len() })?;
            let mut single_output_hasher = sha256::Hash::engine();
            output.consensus_encode(&mut single_output_hasher)?;
            engine.input(sha256::Hash::from_engine(single_output_hasher).as_byte_array());
        }

        // 9. 写入脚本花费的数据 (如果存在)
        if let Some((leaf_hash, codesep_pos)) = leaf_hash_code_separator {
            engine.input(leaf_hash.as_byte_array());
            engine.input(&[0u8]); // key_version, for tapscript it's 0
            engine.input(&codesep_pos.to_le_bytes());
        }

        // 10. 计算并返回最终的 Sighash
        Ok(TapSighash::from_engine(engine))
    }

    /// Computes the BIP341 sighash for a key spend.
    pub fn tap_sighash_key(
        &mut self,
        input_index: usize,
        sighash_type: Option<SighashType>,
    ) -> Result<TapSighash, SighashError> {
        self.tap_sighash_custom(input_index, None, None, sighash_type)
    }

    /// Computes the BIP341 sighash for a script spend.
    ///
    /// Assumes the default `OP_CODESEPARATOR` position of `0xFFFFFFFF`.
    pub fn tap_sighash_script(
        &mut self,
        input_index: usize,
        leaf_hash: impl Into<TapLeafHash>,
        sighash_type: Option<SighashType>,
    ) -> Result<TapSighash, SighashError> {
        self.tap_sighash_custom(
            input_index,
            None,
            Some((leaf_hash.into(), 0xFFFFFFFF)),
            sighash_type,
        )
    }

    /// Computes the BIP143 sighash for any flag type.
    pub fn segwit_sighash(
        &mut self,
        input_index: usize,
        script_code: &ScriptCode,
        value: Sats,
        sighash_type: SighashType,
    ) -> Result<Sighash, SighashError> {
        let mut hasher = Sighash::engine();

        let zero_hash = [0u8; 32];

        let SighashType {
            flag: sighash_flag,
            anyone_can_pay,
        } = sighash_type;

        self.tx.borrow().version.consensus_encode(&mut hasher)?;

        if !anyone_can_pay {
            self.segwit_cache().prevouts.consensus_encode(&mut hasher)?;
        } else {
            zero_hash.consensus_encode(&mut hasher)?;
        }

        if !anyone_can_pay
            && sighash_flag != SighashFlag::Single
            && sighash_flag != SighashFlag::None
        {
            self.segwit_cache().sequences.consensus_encode(&mut hasher)?;
        } else {
            zero_hash.consensus_encode(&mut hasher)?;
        }

        {
            let tx = self.tx.borrow();
            let txin = tx.inputs.get(input_index).ok_or(SighashError::InvalidInputIndex {
                txid: tx.txid(),
                index: input_index,
                inputs: tx.inputs.len(),
            })?;

            txin.prev_output.consensus_encode(&mut hasher)?;
            script_code.consensus_encode(&mut hasher)?;
            value.consensus_encode(&mut hasher)?;
            txin.sequence.consensus_encode(&mut hasher)?;
        }

        if sighash_flag != SighashFlag::Single && sighash_flag != SighashFlag::None {
            self.segwit_cache().outputs.consensus_encode(&mut hasher)?;
        } else if sighash_flag == SighashFlag::Single
            && input_index < self.tx.borrow().outputs.len()
        {
            let mut single_enc = Sighash::engine();
            self.tx.borrow().outputs[input_index].consensus_encode(&mut single_enc)?;
            Sighash::from_engine(single_enc).consensus_encode(&mut hasher)?;
        } else {
            zero_hash.consensus_encode(&mut hasher)?;
        }

        self.tx.borrow().lock_time.consensus_encode(&mut hasher)?;
        sighash_type.to_consensus_u32().consensus_encode(&mut hasher)?;

        Ok(Sighash::from_engine(hasher))
    }

    /// Computes the legacy sighash for any `sighash_type`.
    pub fn legacy_sighash(
        &self,
        input_index: usize,
        script_pubkey: &ScriptPubkey,
        sighash_type: SighashType,
    ) -> Result<Sighash, SighashError> {
        let tx_src = self.tx.borrow();
        let mut hasher = Sighash::engine();

        if input_index >= tx_src.inputs.len() {
            return Err(SighashError::InvalidInputIndex {
                txid: tx_src.txid(),
                index: input_index,
                inputs: tx_src.inputs.len(),
            });
        }

        let SighashType {
            flag: sighash_flag,
            anyone_can_pay,
        } = sighash_type;

        if sighash_flag == SighashFlag::Single && input_index >= tx_src.outputs.len() {
            return Ok(Sighash::from(UINT256_ONE));
        }

        // Build tx to sign
        let mut tx = Transaction {
            version: tx_src.version,
            lock_time: tx_src.lock_time,
            inputs: none!(),
            outputs: none!(),
        };

        // Add all necessary inputs...
        let sig_script = script_pubkey.as_script_bytes().clone().into();
        if anyone_can_pay {
            tx.inputs = VarIntArray::from_checked(vec![TxIn {
                prev_output: tx_src.inputs[input_index].prev_output,
                sig_script,
                sequence: tx_src.inputs[input_index].sequence,
                witness: none!(),
            }]);
        } else {
            let inputs = tx_src.inputs.iter().enumerate().map(|(n, input)| TxIn {
                prev_output: input.prev_output,
                sig_script: if n == input_index { sig_script.clone() } else { SigScript::new() },
                sequence: if n != input_index
                    && (sighash_flag == SighashFlag::Single || sighash_flag == SighashFlag::None)
                {
                    SeqNo::ZERO
                } else {
                    input.sequence
                },
                witness: none!(),
            });
            tx.inputs = VarIntArray::from_iter_checked(inputs);
        }
        // ...then all outputs
        tx.outputs = match sighash_flag {
            SighashFlag::All => tx_src.outputs.clone(),
            SighashFlag::Single => {
                let outputs = tx_src.outputs.iter()
                    .take(input_index + 1)  // sign all outputs up to and including this one, but erase
                    .enumerate()            // all of them except for this one
                    .map(|(n, out)| if n == input_index {
                        out.clone()
                    } else {
                        // consensus encoding of the "NULL txout" - max amount, empty script_pubkey
                        TxOut { value: Sats::MAX, script_pubkey: none!() }
                    });
                VarIntArray::from_iter_checked(outputs)
            }
            SighashFlag::None => none!(),
        };
        // hash the result
        tx.consensus_encode(&mut hasher)?;
        sighash_type.to_consensus_u32().consensus_encode(&mut hasher)?;

        Ok(Sighash::from_engine(hasher))
    }

    fn common_cache(&mut self) -> &CommonCache {
        let tx = self.tx.borrow();
        self.common_cache.get_or_insert_with(|| {
            let mut enc_prevouts = sha256::Hash::engine();
            let mut enc_sequences = sha256::Hash::engine();
            for txin in &tx.inputs {
                let _ = txin.prev_output.consensus_encode(&mut enc_prevouts);
                let _ = txin.sequence.consensus_encode(&mut enc_sequences);
            }
            let mut enc_outputs = sha256::Hash::engine();
            for txout in &tx.outputs {
                let _ = txout.consensus_encode(&mut enc_outputs);
            }
            CommonCache {
                prevouts: sha256::Hash::from_engine(enc_prevouts).to_byte_array().into(),
                sequences: sha256::Hash::from_engine(enc_sequences).to_byte_array().into(),
                outputs: sha256::Hash::from_engine(enc_outputs).to_byte_array().into(),
            }
        })
    }

    fn segwit_cache(&mut self) -> &SegwitCache {
        let common_cache = *self.common_cache();
        self.segwit_cache.get_or_insert_with(|| SegwitCache {
            prevouts: <[u8; 32]>::from(Sha256::digest(common_cache.prevouts)).into(),
            sequences: <[u8; 32]>::from(Sha256::digest(common_cache.sequences)).into(),
            outputs: <[u8; 32]>::from(Sha256::digest(common_cache.outputs)).into(),
        })
    }

    fn taproot_cache(&mut self) -> &TaprootCache {
        self.taproot_cache.get_or_insert_with(|| {
            let mut enc_amounts = sha256::Hash::engine();
            let mut enc_script_pubkeys = sha256::Hash::engine();
            for prevout in &self.prevouts {
                let _ = prevout.borrow().value.consensus_encode(&mut enc_amounts);
                let _ = prevout.borrow().script_pubkey.consensus_encode(&mut enc_script_pubkeys);
            }
            TaprootCache {
                amounts: sha256::Hash::from_engine(enc_amounts).to_byte_array().into(),
                script_pubkeys: sha256::Hash::from_engine(enc_script_pubkeys).to_byte_array().into(),
            }
        })
    }
}
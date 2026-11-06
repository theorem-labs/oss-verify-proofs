(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit ZdSeqBuildW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sext16_shl48 : forall n, -32768 <= n < 32768 -> bv_signed (Z_to_bv 64 (n ≪ 48)) ≫ 48 = n.
Proof.
  intros n Hn. rewrite Z.shiftl_mul_pow2 by lia. rewrite signed_lit by (change (2^48) with 281474976710656; lia).
  rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia.
Qed.

Lemma neg_mask : forall (b : bool) fast, 0 <= fast < 2^64 ->
  Z.land ((0 - Z.b2z b) mod 18446744073709551616) fast = if b then fast else 0.
Proof.
  intros b fast Hf. destruct b; cbn [Z.b2z].
  - change ((0 - 1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zext32_sh29 : forall x, 0 <= x < 4294967296 -> (x ≪ 32 mod 18446744073709551616) ≫ 29 = 8 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (change (2^32) with 4294967296; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2^32) with (8 * 2^29). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

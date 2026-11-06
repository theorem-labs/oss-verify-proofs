(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem State Notation ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Ceiling.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import DrvLib DrvTop.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val MemP.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Z_to_bv : simpl never.

Module RunCeil.

Definition CANARY : sv := (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63)).

Definition Ecan (rnd : EntryDraw) : env :=
  Env (fun _ => Z_to_bv 64 0) (fun j => if PrimInt63.eqb j 6%uint63 then at_random_bytes (ed_random rnd) else []) (fun _ _ => Z_to_bv 8 0).

Section Run.
Variables (sp : word) (rnd : EntryDraw).

Definition ceil_raw : Z := (bv_unsigned sp - 8388608) / 4096 * 4096.
Definition ceilZ : Z := Z.max CEIL_MIN (Z.min CEIL_MAX ceil_raw).
Lemma ceil_range : CEIL_MIN <= ceilZ <= CEIL_MAX.
Proof. unfold ceilZ, CEIL_MIN, CEIL_MAX. lia. Qed.
Lemma ceil_pg : ceilZ mod 4096 = 0.
Proof.
  unfold ceilZ. destruct (Z.le_gt_cases CEIL_MIN (Z.min CEIL_MAX ceil_raw)).
  - rewrite Z.max_r by lia. destruct (Z.le_gt_cases ceil_raw CEIL_MAX).
    + rewrite Z.min_r by lia. unfold ceil_raw. apply Z_mod_mult.
    + rewrite Z.min_l by lia. reflexivity.
  - rewrite Z.max_l by lia. reflexivity.
Qed.

Definition canaryZ : Z := bv_unsigned (den (Ecan rnd) CANARY).
Lemma canary_range : 0 <= canaryZ < 2 ^ 64.
Proof. unfold canaryZ. pose proof (bv_unsigned_in_range _ (den (Ecan rnd) CANARY)) as H. rewrite bv_modulus_64 in H. unfold two64 in H. lia. Qed.

Definition secret_bytes : list byte := firstn 8 (skipn 8 (at_random_bytes (ed_random rnd))).
Lemma secret_bytes_len : length secret_bytes = 8%nat.
Proof. unfold secret_bytes. rewrite length_firstn, length_skipn, length_at_random_bytes. reflexivity. Qed.
Definition secretZ : Z := bytes_le_to_Z secret_bytes.
Lemma secret_range : 0 <= secretZ < 2 ^ 64.
Proof.
  unfold secretZ. pose proof (MemP.bytes_le_to_Z_bound secret_bytes) as H. rewrite secret_bytes_len in H.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in H. exact H.
Qed.

Definition CLG : ceiling := Ceiling ceilZ ceil_range ceil_pg canaryZ canary_range secretZ secret_range.

Lemma ceil_le : valid_sp sp -> @alloc_ceiling CLG <= bv_unsigned sp - DrvTop.WOFF.
Proof.
  intros (Hlo & Hhi & _). cbn [alloc_ceiling CLG]. unfold ceilZ, ceil_raw, CEIL_MIN, CEIL_MAX, DrvTop.WOFF.
  unfold sp_window_lo, sp_window_hi in *.
  pose proof (Z.mul_div_le (bv_unsigned sp - 8388608) 4096 ltac:(lia)).
  assert (34359211788 <= (bv_unsigned sp - 8388608) / 4096) by (apply Z.div_le_lower_bound; lia).
  lia.
Qed.

Lemma canary_eq : den (Ecan rnd) CANARY = Z_to_bv 64 (@ssp_canary CLG).
Proof. cbn [ssp_canary CLG]. unfold canaryZ. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma secret_eq : forall i, (i < 8)%nat ->
  nth_error (at_random_bytes (ed_random rnd)) (8 + i) = nth_error (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem.le8 (Z_to_bv 64 (@ctx_secret CLG))) i.
Proof.
  intros i Hi. cbn [ctx_secret CLG]. unfold OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem.le8, word_to_le_bytes.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold two64; pose proof secret_range; lia).
  unfold secretZ. replace (Z_to_le_bytes 8 (bytes_le_to_Z secret_bytes)) with (Z_to_le_bytes (length secret_bytes) (bytes_le_to_Z secret_bytes))
    by (rewrite secret_bytes_len; reflexivity).
  rewrite DrvLib.Z_to_le_bytes_roundtrip.
  unfold secret_bytes. rewrite nth_error_firstn. replace (PeanoNat.Nat.ltb i 8) with true by (symmetry; apply PeanoNat.Nat.ltb_lt; exact Hi).
  rewrite nth_error_skipn. reflexivity.
Qed.
End Run.
End RunCeil.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg ABase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import InfBBase InfBTables InfB_w7tab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma code_read_lo16 : forall segs m A ws (i c : Z),
  bytes_at segs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some (Z_to_bv 64 c) -> 0 <= i -> 0 <= c < 4294967296 ->
  ov_read_bytes segs m (Z_to_bv 64 (A + 4 * i)) 2 = Some (le2 (Z_to_bv 64 (Z.land c 65535))).
Proof.
  intros segs m A ws i c Hb Hn Hi Hc. pose proof (u32s_read_sub segs m A ws i _ 0 2 Hb Hn Hi ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r in R. rewrite R, le4_bytes. cbn [firstn skipn]. rewrite unsigned_lit by lia.
  unfold le2. assert (V : 0 <= Z.land c 65535 < 65536).
  { change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  f_equal. f_equal; [| f_equal]; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256;
    change 65535 with (Z.ones 16); rewrite Z.land_ones by lia; rewrite ?Z.shiftr_div_pow2 by lia; change (2^8) with 256; change (2^16) with 65536;
    Z.div_mod_to_equations; lia.
Qed.

Lemma code_word_join : forall c, 0 <= c < 4294967296 -> Z.lor (Z.shiftl (code_val c) 16) (Z.land c 65535) = c.
Proof.
  intros c Hc. unfold code_val. change 65535 with (Z.ones 16). apply Z.bits_inj'. intros k Hk.
  rewrite Z.lor_spec. rewrite Z.shiftl_spec by exact Hk. rewrite !Z.land_spec.
  destruct (Z.ltb_spec k 16) as [LT|GE].
  - rewrite !(Z.testbit_neg_r _ (k - 16)) by lia. rewrite (Z.ones_spec_low 16 k) by lia. cbn [andb orb]. apply andb_true_r.
  - rewrite Z.shiftr_spec by lia. replace (k - 16 + 16) with k by lia. rewrite (Z.ones_spec_high 16 k) by lia.
    rewrite andb_false_r, orb_false_r.
    destruct (Z.ltb_spec (k - 16) 16) as [LT2|GE2].
    + rewrite (Z.ones_spec_low 16 (k - 16)) by lia. apply andb_true_r.
    + rewrite (Z.ones_spec_high 16 (k - 16)) by lia. rewrite andb_false_r. symmetry.
      destruct (Z.eq_dec c 0) as [->|NZ]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 32; [| lia]. apply Z.log2_lt_pow2; [lia|]. change (2 ^ 32) with 4294967296. lia.
Qed.
Lemma code_word_op : forall c, Z.land c 255 = code_op c.
Proof. reflexivity. Qed.
Lemma code_word_bits : forall c, Z.land (Z.shiftr c 8) 255 = code_bits c.
Proof. reflexivity. Qed.
Lemma code_word_val : forall c, 0 <= c < 4294967296 -> Z.shiftr c 16 = code_val c.
Proof.
  intros c Hc. unfold code_val. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. rewrite Z.mod_small by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Definition dtab16 (m : amem) (TA nd : Z) (rd : Z -> Z) : Prop :=
  forall i, 0 <= i < nd -> ov_read_bytes bsegs m (Z_to_bv 64 (TA + 4 * i)) 2 = Some (le2 (Z_to_bv 64 (Z.land (rd i) 65535))).

Lemma dtab16_dyn : forall m S cf o nd,
  f32arr bsegs m (S + 1384) 1444 cf -> (forall i, 0 <= i < N_CODES -> 0 <= cf i < 4294967296) ->
  0 <= o -> 0 <= nd -> o + nd <= 1444 ->
  dtab16 m (S + 1384 + 4 * o) nd (rdc cf (CDyn o)).
Proof.
  intros m S cf o nd [HB _] RN Ho Hn Hon i Hi. unfold rdc. unfold N_CODES in RN.
  assert (R : 0 <= cf (o + i) < 4294967296) by (apply RN; lia).
  replace (S + 1384 + 4 * o + 4 * i) with (S + 1384 + 4 * (o + i)) by lia.
  apply (code_read_lo16 bsegs m (S + 1384) (fws cf 1444) (o + i)); [exact HB| apply f32arr_nth; cbn; lia| lia| exact R].
Qed.
Lemma dtab16_lenfix : forall m, mem_inv bsegs m -> dtab16 m 149600 512 (rdc (fun _ => 0) CLenfix).
Proof.
  intros m MI i Hi. unfold rdc. destruct (lenfix_nth i Hi) as [E R]. rewrite <- E in *.
  apply (code_read_lo16 bsegs m 149600 (zw lenfix_l) i); [exact (lenfix_bytes m MI)| apply zw_nth; cbn; lia| lia| exact R].
Qed.
Lemma dtab16_distfix : forall m, mem_inv bsegs m -> dtab16 m 152160 32 (rdc (fun _ => 0) CDistfix).
Proof.
  intros m MI i Hi. unfold rdc. destruct (distfix_nth i Hi) as [E R]. rewrite <- E in *.
  apply (code_read_lo16 bsegs m 152160 (zw distfix_l) i); [exact (distfix_bytes m MI)| apply zw_nth; cbn; lia| lia| exact R].
Qed.
End CANSEC1.

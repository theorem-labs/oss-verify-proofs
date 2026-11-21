(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import InfABase InfATables.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition dtab (m : amem) (TA nd : Z) (rd : Z -> Z) : Prop :=
  forall i, 0 <= i < nd ->
    0 <= rd i < 4294967296
    /\ ov_read_bytes asegs m (Z_to_bv 64 (TA + 4 * i)) 1 = Some [Z_to_bv 8 (code_op (rd i))]
    /\ ov_read_bytes asegs m (Z_to_bv 64 (TA + 4 * i + 1)) 1 = Some [Z_to_bv 8 (code_bits (rd i))]
    /\ ov_read_bytes asegs m (Z_to_bv 64 (TA + 4 * i + 2)) 2 = Some (le2 (Z_to_bv 64 (code_val (rd i)))).

Lemma dtab_dyn : forall m S cf o nd,
  f32arr asegs m (S + 1384) 1444 cf -> (forall i, 0 <= i < N_CODES -> 0 <= cf i < 4294967296) ->
  0 <= o -> 0 <= nd -> o + nd <= 1444 ->
  dtab m (S + 1384 + 4 * o) nd (rdc cf (CDyn o)).
Proof.
  intros m S cf o nd FA RN Ho Hn Hon i Hi. unfold rdc. unfold N_CODES in RN.
  assert (R : 0 <= cf (o + i) < 4294967296) by (apply RN; lia).
  split; [exact R|].
  pose proof (codes_read_op m (S + 1384) 1444 cf (o + i) FA ltac:(lia) R) as R0.
  pose proof (codes_read_bits m (S + 1384) 1444 cf (o + i) FA ltac:(lia) R) as R1.
  pose proof (codes_read_val m (S + 1384) 1444 cf (o + i) FA ltac:(lia) R) as R2.
  replace (S + 1384 + 4 * (o + i)) with (S + 1384 + 4 * o + 4 * i) in R0, R1, R2 by lia.
  split; [exact R0| split; [exact R1| exact R2]].
Qed.
Lemma dtab_lenfix : forall m, mem_inv asegs m -> dtab m 149600 512 (rdc (fun _ => 0) CLenfix).
Proof.
  intros m MI i Hi. unfold rdc. destruct (lenfix_nth i Hi) as [_ R].
  split; [exact R|]. split; [exact (lenfix_read_op m i MI Hi)| split; [exact (lenfix_read_bits m i MI Hi)| exact (lenfix_read_val m i MI Hi)]].
Qed.
Lemma dtab_distfix : forall m, mem_inv asegs m -> dtab m 152160 32 (rdc (fun _ => 0) CDistfix).
Proof.
  intros m MI i Hi. unfold rdc. destruct (distfix_nth i Hi) as [_ R].
  split; [exact R|]. split; [exact (distfix_read_op m i MI Hi)| split; [exact (distfix_read_bits m i MI Hi)| exact (distfix_read_val m i MI Hi)]].
Qed.


Lemma tab_sh0 : forall m XT NS a,
  shadow_bytes m (Z.shiftr XT 3 + 2147450880) (Z.shiftr XT 3 + 2147450880 + NS) (fun _ => 0) -> XT mod 8 = 0 -> XT <= a < XT + 8 * NS -> 0 <= XT ->
  ov_read_bytes asegs m (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m XT NS a SB X8 Ha X0. apply (ov_read1_sh0 asegs m _ _ a SB).
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
Qed.

Lemma tab_sh_acc : forall RNG XT NS a,
  rng RNG (Z.shiftr XT 3 + 2147450880) NS -> XT mod 8 = 0 -> XT <= a < XT + 8 * NS -> 0 <= XT ->
  acc_in RNG (Z_to_bv 64 (Z.shiftr a 3 + 2147450880), 1%nat).
Proof.
  intros RNG XT NS a R X8 Ha X0. apply (rng_acc_litZ RNG _ NS _ 1%nat 1 R eq_refl); [lia|].
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
Qed.

Lemma pay_sh_acc : forall RNG D n a,
  rng RNG (Z.shiftr D 3 + 2147450880) (n / 8 + 1) -> D mod 8 = 0 -> 0 <= D -> D <= a < D + n ->
  acc_in RNG (Z_to_bv 64 (Z.shiftr a 3 + 2147450880), 1%nat).
Proof.
  intros RNG D n a R D8 D0 Ha. apply (rng_acc_litZ RNG _ (n / 8 + 1) _ 1%nat 1 R eq_refl); [lia|].
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
Qed.

Lemma code_op_range : forall c, 0 <= code_op c < 256.
Proof. intros c. unfold code_op. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma code_bits_range : forall c, 0 <= code_bits c < 256.
Proof. intros c. unfold code_bits. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma code_val_range : forall c, 0 <= code_val c < 65536.
Proof. intros c. unfold code_val. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
End CANSEC1.

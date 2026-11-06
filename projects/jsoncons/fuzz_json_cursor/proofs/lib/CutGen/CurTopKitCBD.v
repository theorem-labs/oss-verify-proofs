(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AxSymExec3 AxSymExec3B AxSymExec3Sound.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutL5 CutL5A.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CTKB.
Definition mem := (word -> option byte).

Lemma h72_val : forall x : word, bv_unsigned (mul_div Instr.M_MUL (Z_to_bv 64 512) (alu64 Instr.ALU_SRL x (Z_to_bv 64 9))) = 512 * (bv_unsigned x / 512).
Proof.
  intros x. unfold mul_div, alu64, alu. rewrite bv_mul_unsigned, bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned.
  change (bv_wrap 64 512) with 512. change (Z.land (bv_wrap 64 9) (bv_wrap 64 63)) with 9.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 9) with 512.
  pose proof (bv_unsigned_in_range _ x) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with 18446744073709551616 in R.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite Z.mod_small; [lia|]. split; [apply Z.mul_nonneg_nonneg; [lia| apply Z.div_pos; lia]|].
  assert (bv_unsigned x / 512 < 36028797018963968) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Section Cells.
Variable segs : list Segment.
Lemma kword2_h72 : forall E (M : mem) a A e,
  kentry_ok segs E M (KWord a 2 (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL e (ELit 9)))) -> estart E a = A ->
  L5.u8_at segs M A 0 /\ exists k, 0 <= k < 128 /\ L5.u8_at segs M (A + 1) (2 * k).
Proof.
  intros E M a A e (_ & Hfl & Hr) Ha. rewrite (CL5.adenot_start E a _ Hfl), Ha in Hr. cbn [edenot] in Hr.
  unfold word_to_le_bytes in Hr. rewrite h72_val in Hr. set (q := bv_unsigned (edenot E e) / 512) in Hr.
  assert (Q0 : 0 <= q) by (unfold q; pose proof (bv_unsigned_in_range _ (edenot E e)); apply Z.div_pos; lia).
  cbn [Z_to_le_bytes] in Hr.
  assert (B0 : Z_to_bv 8 (512 * q) = Z_to_bv 8 0).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    replace (512 * q) with ((2 * q) * 256) by lia. rewrite Z.mod_mul by lia. reflexivity. }
  assert (B1 : Z_to_bv 8 (Z.shiftr (512 * q) 8) = Z_to_bv 8 (2 * (q mod 128))).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (512 * q) with ((2 * q) * 256) by lia. rewrite Z.div_mul by lia. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    rewrite (Z.mod_small (2 * (q mod 128))) by (pose proof (Z.mod_pos_bound q 128 ltac:(lia)); lia).
    rewrite (Z.div_mod q 128) at 1 by lia. replace (2 * (128 * (q / 128) + q mod 128)) with (2 * (q mod 128) + (q / 128) * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. pose proof (Z.mod_pos_bound q 128 ltac:(lia)); lia. }
  rewrite B0, B1 in Hr. unfold L5.u8_at.
  cbn [rdn] in Hr |- *. destruct (match M (Z_to_bv 64 A) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 A) end) as [b0|] eqn:E0; [|discriminate].
  destruct (match M (Z_to_bv 64 A + 1)%bv with Some b => Some b | None => seg_rom segs (Z_to_bv 64 A + 1)%bv end) as [b1|] eqn:E1; [|discriminate].
  injection Hr as H0 H1. subst b0 b1. split; [reflexivity|]. exists (q mod 128). split; [apply Z.mod_pos_bound; lia|].
  assert (EQ : Z_to_bv 64 (A + 1) = (Z_to_bv 64 A + 1)%bv) by (apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned; unfold bv_wrap; rewrite Zplus_mod_idemp_l; change (bv_unsigned (1%bv : bv 64)) with 1; reflexivity).
  rewrite EQ, E1. reflexivity.
Qed.
End Cells.
End CTKB.

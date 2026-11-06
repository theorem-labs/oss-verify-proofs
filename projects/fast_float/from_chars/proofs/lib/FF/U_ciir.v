(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Wbig_tac U_ciir_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma remu_word : forall a b : word, (bv_unsigned b <> 0)%Z ->
  mul_div M_REMU a b = Z_to_bv 64 (bv_unsigned a mod bv_unsigned b).
Proof.
  intros a b Hb. unfold mul_div. replace (bv_unsigned b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_modu_unsigned.
  pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 b) as Rb. unfold bv_modulus in *.
  pose proof (Z.mod_pos_bound (bv_unsigned a) (bv_unsigned b) ltac:(lia)).
  rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma remu_lit : forall (a : word) (k : Z), (0 < k < 2^64)%Z ->
  mul_div M_REMU a (Z_to_bv 64 k) = Z_to_bv 64 (bv_unsigned a mod k).
Proof. intros a k Hk. rewrite remu_word by (rewrite unsigned_lit; lia). rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma swrap32_small : forall z, (0 <= z < 2^31)%Z -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31)%Z. lia. Qed.

Lemma ciir_spec : ciir_stmt.
Proof.
  unfold ciir_stmt. intros until bs. intros Ha1 Ha2 FDP DATA LEN NW NZ ST SEP1 SEP2 SEP3.
  subst a1 a2.
  pose proof (munch_refl (ciir_W sp a0) m) as MU. unfold ciir_W in MU.
  pose proof (wmono_refl USEGS m) as WM.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 dptr) as Rd. unfold bv_modulus in Rd.
  pose proof (rw_cells_bound _ _ _ _ FDP) as Bf. cbn [cells_size csize Nat.add] in Bf.
  destruct bs as [|b0 bs0].
  { (* [comment removed for export] *)
    cbn [length] in LEN. change (Z.of_nat 0) with 0%Z in LEN. subst n. clear DATA.
    carve_frame 16%nat ST.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_false.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_true.
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_true.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) if_false.
    step. (* [comment removed for export] *)
    rewrite remu_lit by lia. rewrite ?unsigned_lit by lia.
    change (0 mod 4)%Z with 0%Z.
    step. (* [comment removed for export] *)
    rewrite ?unsigned_lit by lia. change (bv_swrap 32 (0 + 0)) with 0%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold ciir_post. cbn [ciir_result ciir_remaining Z.eqb].
    finish. }
  (* [comment removed for export] *)
  pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
  cbn [length] in LEN, Bd. rewrite Nat2Z.inj_succ in LEN, Bd.
  carve_frame 16%nat ST.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_false.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_true.
  step. step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  setcmp. decide_ltb.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  setcmp. decide_ltb.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_false.
  step. (* [comment removed for export] *)
  if_not_taken.
  destruct (nth_error (b0 :: bs0) (Z.to_nat (n - 1))) as [b|] eqn:Hb.
  2:{ exfalso. apply nth_error_None in Hb. cbn [length] in Hb. lia. }
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
  pose proof (u8ro_read USEGS _ (bv_unsigned dptr) (b0 :: bs0) (n - 1) b _ DATA Hb ltac:(lia) eq_refl) as RD.
  step. (* [comment removed for export] *)
  clear RD.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite Z.lor_0_l.
  step. (* [comment removed for export] *)
  if_false.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_false.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *) if_false.
  step. (* [comment removed for export] *)
  rewrite remu_lit by lia. unfold zxb. rewrite !unsigned_lit by lia.
  step. (* [comment removed for export] *)
  rewrite unsigned_lit by lia. rewrite swrap32_small by lia. rewrite Z.add_0_l.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold ciir_post.
  replace (ciir_result n (b0 :: bs0)) with (bv_unsigned b mod 4)%Z.
  2:{ unfold ciir_result. replace (n =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite (nth_error_nth _ _ _ Hb). reflexivity. }
  replace (ciir_remaining n) with (n + -1)%Z by (unfold ciir_remaining; replace (n =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia); lia).
  finish.
Qed.

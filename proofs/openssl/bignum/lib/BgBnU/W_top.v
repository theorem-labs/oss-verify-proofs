(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnWords BnModel BnMInv.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnRep W_small.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_CORRECT_TOP : Z := 0xff2b0.

(* [comment removed for export] *)
Lemma ct_loop : forall (t : nat) (POST : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (D : Z) (buf : list Z),
  u64arr bgusegs m D (wlimbs buf) -> limbs buf -> (1 <= t <= length buf)%nat -> Z.of_nat (length buf) < 2^31 ->
  0 < D -> D + 8 * Z.of_nat (length buf) <= 2^47 ->
  (forall a1' a2', evt bgusegs POST
     (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat (strip_top buf t))) (Z_to_bv 64 9) (Z_to_bv 64 1) a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xff31c) fc None m (seg_rom bgusegs))) ->
  evt bgusegs POST
     (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (Z.of_nat t)) (Z_to_bv 64 (D + 8 * Z.of_nat t)) (Z_to_bv 64 0) a4 (Z_to_bv 64 9) (Z_to_bv 64 1) a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xff2f8) fc None m (seg_rom bgusegs)).
Proof.
  induction t as [|t IH]; intros until buf; intros U LB HT LEN D0 DT K; [lia|].
  assert (NTH : nth_error (wlimbs buf) (Z.to_nat (Z.of_nat t)) = Some (Z_to_bv 64 (nth t buf 0))).
  { rewrite Nat2Z.id. unfold wlimbs. rewrite nth_error_map. rewrite (nth_error_nth' buf 0) by lia. reflexivity. }
  chk ltac:(fun C => clear - C D0 DT HT; lia).
  chk ltac:(fun C => clear - C; lia).
  step. step.
  replace (D + 8 * Z.of_nat (S t) + -8) with (D + 8 * Z.of_nat t) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let a := cur_mem_addr in
    pose proof (u64arr_read bgusegs mx D (wlimbs buf) (Z.of_nat t) (Z_to_bv 64 (nth t buf 0)) a U NTH ltac:(lia) ltac:(addr_tac)) as RD end.
  step. clear RD.
  pose proof (limbs_nth buf t LB) as LN. unfold limb in LN. rewrite BnArith.BW_lit in LN.
  step. if_cases KW; zify_cond KW; rewrite ?unsigned_lit in KW by lia.
  - (* [comment removed for export] *)
    cbn [strip_top] in K. replace (nth t buf 0 =? 0) with false in K by (symmetry; apply Z.eqb_neq; exact KW).
    eapply K.
  - step.
    rewrite (swrap32_wrap64 (Z.of_nat (S t)) (-1)) by lia.
    replace (Z.of_nat (S t) + -1) with (Z.of_nat t) by lia.
    cbn [strip_top] in K. replace (nth t buf 0 =? 0) with true in K by (symmetry; apply Z.eqb_eq; exact KW).
    step. if_cases KL; zify_cond KL.
    + (* [comment removed for export] *)
      rewrite !signed_small in KL by lia.
      eapply IH; [exact U| exact LB| lia| exact LEN| exact D0| exact DT|]. intros a1' a2'. eapply K.
    + rewrite !signed_small in KL by lia. assert (t = 0%nat) by lia. subst t. cbn [strip_top] in K.
      step. eapply K.
Qed.

(* [comment removed for export] *)
Lemma bn_correct_top_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgusegs m A (bn_cells D b) -> (0 < A /\ A mod 8 = 0) -> ub_ptr_ok (Z.of_nat (bn_top b)) D ->
  u64arr bgusegs m D (wlimbs (bn_buf b)) -> limbs (bn_buf b) ->
  (bn_top b <= bn_dmax b)%nat -> Z.of_nat (bn_dmax b) < 2^31 ->
  stk bgusegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv bgusegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) ->
  (D + 8 * Z.of_nat (bn_dmax b) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= D) ->
  (A + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax b) <= A) ->
  a0 = Z_to_bv 64 A ->
  evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z lo m
               (fun _ m' => rw_cells bgusegs m' A (bn_cells D (bn_correct_top_pure b))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_CORRECT_TOP) fc None m (seg_rom bgusegs)).
Proof.
  intros until b. intros BN [PA PM] PD U0 LB HT HD ST LO MI SEP SEPD SEPAD ->. unfold BN_CORRECT_TOP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  assert (LW : Z.of_nat (length (wlimbs (bn_buf b))) = Z.of_nat (bn_dmax b)) by (rewrite wlimbs_len; reflexivity).
  assert (AB : A + 24 <= 2^64) by (destruct BN as [BN _]; apply cells_at_bound in BN; cbn in BN; lia).
  assert (DT : 0 < Z.of_nat (bn_top b) -> 0 < D /\ D mod 8 = 0 /\ D + 8 * Z.of_nat (length (bn_buf b)) <= 2^47).
  { intros H. destruct (PD H) as [P1 P2]. split; [exact P1|]. split; [exact P2|].
    destruct U0 as [_ U0]. rewrite wlimbs_len in U0. apply (wr_at_below bgusegs m D _ MI) in U0; [| unfold bn_dmax in HT; lia].
    unfold UTOP in U0. lia. }
  apply hide_intro in DT. clear PD.
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 4 step.
  chk ltac:(fun C => clear - C PA AB; lia).
  step. rewrite (land7_wrap _ PM).
  chk ltac:(fun C => clear - C; lia).
  step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
  step. if_cases KT; zify_cond KT.
  - (* [comment removed for export] *)
    assert (ET0 : bn_top b = 0%nat) by (apply andb_false_iff in KT; destruct KT as [KT|KT]; apply Z.ltb_ge in KT; lia).
    step. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by lia; [exfalso; lia|]. clear KZ.
    step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
    finish. unfold bn_cells, bn_correct_top_pure. rewrite ET0. cbn [strip_top Nat.eqb bn_top bn_dmax bn_buf bn_neg bn_flags bn_d Z.b2z].
    rewrite ET0 in BN. exact BN.
  - (* [comment removed for export] *)
    apply hide_elim in DT. destruct (DT KT0) as (D0 & DM & DTOP). clear DT.
    unfold bn_dmax in HT, HD.
    step. unfold wz at 1. step. step.
    rewrite ?(unsigned_lit (Z.of_nat (bn_top b))) by lia.
    replace (Z.shiftl (Z.of_nat (bn_top b)) 3) with (8 * Z.of_nat (bn_top b)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    chk ltac:(fun C => clear - C D0 DTOP HT KT0; lia).
    chk ltac:(fun C => clear - C D0 DTOP HT KT0; lia).
    chk ltac:(fun C => clear - C D0 DTOP HT KT0; lia).
    step. rewrite (land7_wrap _ DM).
    step. step.
    replace (8 * Z.of_nat (bn_top b) + D) with (D + 8 * Z.of_nat (bn_top b)) by lia.
    eapply ct_loop; [exact U0| exact LB| lia| exact HD| exact D0| exact DTOP|].
    intros a1' a2'.
    assert (STL : (strip_top (bn_buf b) (bn_top b) <= bn_top b)%nat).
    { clear. generalize (bn_top b) as t. induction t as [|t IHt]; cbn [strip_top]; [lia|]. destruct (nth t (bn_buf b) 0 =? 0); lia. }
    step. step.
    step. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by lia.
    + (* [comment removed for export] *)
      do 3 step. release_frame FR ST (bv_unsigned sp). step.
      finish. unfold bn_cells, bn_correct_top_pure. cbn [bn_top bn_dmax bn_buf bn_neg bn_flags bn_d].
      replace (strip_top (bn_buf b) (bn_top b) =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia). exact BN.
    + step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
      finish. unfold bn_cells, bn_correct_top_pure. cbn [bn_top bn_dmax bn_buf bn_neg bn_flags bn_d].
      replace (strip_top (bn_buf b) (bn_top b) =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia). cbn [Z.b2z]. exact BN.
Qed.

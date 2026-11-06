(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA ZBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prog BnBase BnWords BnModel BnMInv.
From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnArith BnMem BnTac.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop BnRepDefs AsStruct W_smallA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_CORRECT_TOP : Z := 0x1f5d90.

(* [comment removed for export] *)
Lemma ct_loopA : forall (t : nat) (POST : machine_state -> Prop)
    (ra sp gp tp t1 t2 s0 s1 a0 a1 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (D : Z) (buf : list Z),
  u64arr asegs m D (wlimbs buf) -> limbs buf -> (1 <= t <= length buf)%nat -> Z.of_nat (length buf) < 2^31 ->
  acc asegs m D (8 * Z.of_nat (length buf)) -> D mod 8 = 0 -> D + 8 * Z.of_nat (length buf) <= 140737488355328 ->
  (forall t1' a2' a5' a7', evt asegs POST
     (MS (mkR ra sp gp tp (Z_to_bv 64 1) t1' t2 s0 s1 a0 a1 a2' (Z_to_bv 64 SHB) a4 a5' (Z_to_bv 64 (Z.of_nat (strip_top buf t))) a7'
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1f5e28) fc None m (seg_rom asegs))) ->
  evt asegs POST
     (MS (mkR ra sp gp tp (Z_to_bv 64 1) t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (D + 8 * Z.of_nat t + -8)) (Z_to_bv 64 SHB) a4
              (Z_to_bv 64 (Z.of_nat t)) a6 (Z_to_bv 64 (D + 8 * Z.of_nat t + -8))
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1f5df8) fc None m (seg_rom asegs)).
Proof.
  induction t as [|t IH]; intros until buf; intros U LB HT LEN ACC AL TOP47 K; [lia|].
  pose proof (u64arr_bound asegs m D _ U) as UB. rewrite wlimbs_len in UB.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU.
  assert (NTH : nth_error (wlimbs buf) (Z.to_nat (Z.of_nat t)) = Some (Z_to_bv 64 (nth t buf 0))).
  { rewrite Nat2Z.id. unfold wlimbs. rewrite nth_error_map. rewrite (nth_error_nth' buf 0) by lia. reflexivity. }
  replace (D + 8 * Z.of_nat (S t) + -8) with (D + 8 * Z.of_nat t) by lia.
  do 2 step. shl. chk0. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let a := cur_mem_addr in
    pose proof (u64arr_read asegs mx D (wlimbs buf) (Z.of_nat t) (Z_to_bv 64 (nth t buf 0)) a U NTH ltac:(lia) ltac:(addr_tac)) as RD end.
  step. clear RD. step.
  pose proof (limbs_nth buf t LB) as LN. unfold limb in LN. rewrite BnArith.BW_lit in LN.
  if_cases KW; zify_cond KW; rewrite ?unsigned_lit in KW by lia.
  - (* [comment removed for export] *)
    cbn [strip_top] in K. replace (nth t buf 0 =? 0) with false in K by (symmetry; apply Z.eqb_neq; exact KW).
    eapply K.
  - step. step. step.
    rewrite (swrap32_wrap64 (Z.of_nat (S t)) (-1)) by lia.
    replace (Z.of_nat (S t) + -1) with (Z.of_nat t) by lia.
    cbn [strip_top] in K. replace (nth t buf 0 =? 0) with true in K by (symmetry; apply Z.eqb_eq; exact KW).
    step. if_cases KL; zify_cond KL.
    + (* [comment removed for export] *)
      rewrite !signed_small in KL by lia.
      replace (D + 8 * Z.of_nat t + -8) with (D + 8 * Z.of_nat t + -8) by lia.
      eapply IH; [exact U| exact LB| lia| exact LEN| exact ACC| exact AL| exact TOP47|]. intros t1' a2' a5' a7'. eapply K.
    + rewrite !signed_small in KL by lia. assert (t = 0%nat) by lia. subst t. cbn [strip_top] in K.
      step. eapply K.
Qed.

(* [comment removed for export] *)
Lemma bn_correct_top_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells asegs m A (bn_cells D b) -> u64arr asegs m D (wlimbs (bn_buf b)) -> limbs (bn_buf b) ->
  (bn_top b <= bn_dmax b)%nat -> Z.of_nat (bn_dmax b) < 2^31 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv asegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) ->
  (D + 8 * Z.of_nat (bn_dmax b) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= D) ->
  (A + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax b) <= A) ->
  shb_cells asegs 5932248 6753336 m -> acc asegs m A 24 -> A mod 8 = 0 ->
  acc asegs m D (8 * Z.of_nat (bn_dmax b)) -> D mod 8 = 0 ->
  SHHI <= lo -> (A + 24 <= SHLO \/ SHHI <= A) ->
  a0 = Z_to_bv 64 A ->
  evt asegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z lo m
               (fun _ m' => rw_cells asegs m' A (bn_cells D (bn_correct_top_pure b))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_CORRECT_TOP) fc None m (seg_rom asegs)).
Proof.
  intros until b. intros BN U0 LB HT HD ST LO MI SEP SEPD SEPAD (SHB1 & SHB2) ACC AL ACCD ALD SLO SOFF ->. unfold BN_CORRECT_TOP.
  unfold SHLO, SHHI in *.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
  assert (LW : Z.of_nat (length (wlimbs (bn_buf b))) = Z.of_nat (bn_dmax b)) by (rewrite wlimbs_len; reflexivity).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 7 step. do 3 step. shl. chk0.
  step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
  step. if_cases KT; zify_cond KT.
  - (* [comment removed for export] *)
    assert (ET0 : bn_top b = 0%nat) by (apply andb_false_iff in KT; destruct KT as [KT|KT]; apply Z.ltb_ge in KT; lia).
    step. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by lia; [|exfalso; lia]. clear KZ.
    do 3 step. shl. chk0. step.
    do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
    finish. unfold bn_cells, bn_correct_top_pure. rewrite ET0. cbn [strip_top Nat.eqb bn_top bn_dmax bn_buf bn_neg bn_flags bn_d Z.b2z].
    rewrite ET0 in BN. exact BN.
  - (* [comment removed for export] *)
    do 2 step. shl. chk0.
    step. unfold wz at 1. do 7 step.
    rewrite (shl32_shr32 (Z.of_nat (bn_top b))) by lia.
    replace (Z.shiftl (Z.of_nat (bn_top b)) 3) with (8 * Z.of_nat (bn_top b)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (DB47 : 0 <= D /\ D + 8 * Z.of_nat (bn_dmax b) <= 140737488355328).
    { destruct U0 as [_ W]. rewrite wlimbs_len in W. pose proof (wr_at_below asegs m1 D _ MI W ltac:(unfold bn_dmax in *; lia)) as T.
      unfold UTOP in T. destruct W as (W0 & _). unfold bn_dmax in *. lia. }
    assert (ACCD1 : acc asegs m1 D (8 * Z.of_nat (length (bn_buf b)))).
    { eapply (acc_munch asegs _ m m1 D _ ACCD MU OFF); unfold bn_dmax in *; lia. }
    eapply ct_loopA; [exact U0| exact LB| unfold bn_dmax in HT; lia| unfold bn_dmax in HD; exact HD| exact ACCD1| exact ALD| unfold bn_dmax in *; lia|].
    intros t1' a2' a5' a7'.
    assert (STL : (strip_top (bn_buf b) (bn_top b) <= bn_top b)%nat).
    { clear. generalize (bn_top b) as t. induction t as [|t IHt]; cbn [strip_top]; [lia|]. destruct (nth t (bn_buf b) 0 =? 0); lia. }
    shl. chk0. step.
    step. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by lia.
    + (* [comment removed for export] *)
      do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
      finish. unfold bn_cells, bn_correct_top_pure. cbn [bn_top bn_dmax bn_buf bn_neg bn_flags bn_d].
      replace (strip_top (bn_buf b) (bn_top b) =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia). exact BN.
    + do 3 step. shl. chk0. step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
      finish. unfold bn_cells, bn_correct_top_pure. cbn [bn_top bn_dmax bn_buf bn_neg bn_flags bn_d].
      replace (strip_top (bn_buf b) (bn_top b) =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia). cbn [Z.b2z]. exact BN.
Qed.

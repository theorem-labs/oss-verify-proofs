(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateA_DISTEXT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.

Module RefInflateA_COPY.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Znumtheory.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition cpy_n (s : inflate_state) (r : iregs) : Z :=
  let copy := is_length s in
  let copy := if ir_have r <? copy then ir_have r else copy in
  if ir_left r <? copy then ir_left r else copy.

Definition cpy_c (c : icall) (r : iregs) (n : Z) : icall :=
  icset_outbuf c (arr_blit (ic_outbuf c) (ir_put r) (ic_input c) (ir_next r) n).
Definition cpy_r (r : iregs) (n : Z) : iregs :=
  irset_put (irset_left (irset_next (irset_have r (wrap32 (ir_have r - n))) (ir_next r + n)) (wrap32 (ir_left r - n))) (ir_put r + n).

Lemma arm_COPY_zero : forall s c r, is_length s = 0 -> arm_COPY (mkW s c r) = ARun tt (mkW (iset_mode s TYPE) c r).
Proof. intros s c r H. unfold arm_COPY. mstep1 (@gs_eq inflate_state). rewrite H. cbn [Z.eqb negb]. apply set_mode_eq. Qed.

Lemma arm_COPY_leave : forall s c r, is_length s <> 0 -> cpy_n s r = 0 -> arm_COPY (mkW s c r) = ALeave (mkW s c r).
Proof.
  intros s c r H Hn. unfold arm_COPY. mstep1 (@gs_eq inflate_state). rewrite (proj2 (Z.eqb_neq _ _) H). cbn [negb].
  mstep1 (@gr_eq iregs). fold (cpy_n s r). rewrite Hn. cbn [Z.eqb]. apply aleave_eq.
Qed.

Lemma arm_COPY_run : forall s c r, is_length s <> 0 -> cpy_n s r <> 0 ->
  arm_COPY (mkW s c r) = ARun tt (mkW (iset_length s (wrap32 (is_length s - cpy_n s r))) (cpy_c c r (cpy_n s r)) (cpy_r r (cpy_n s r))).
Proof.
  intros s c r H Hn. unfold arm_COPY. mstep1 (@gs_eq inflate_state). rewrite (proj2 (Z.eqb_neq _ _) H). cbn [negb].
  mstep1 (@gr_eq iregs). fold (cpy_n s r). rewrite (proj2 (Z.eqb_neq _ _) Hn).
  mstep1 uc_eq. mstep1 ur_eq. rewrite us_eq. reflexivity.
Qed.

Lemma cpy_n_range : forall s r, 0 <= is_length s -> 0 <= ir_have r -> 0 <= ir_left r ->
  0 <= cpy_n s r /\ cpy_n s r <= is_length s /\ cpy_n s r <= ir_have r /\ cpy_n s r <= ir_left r.
Proof.
  intros s r Hl Hh Hf. unfold cpy_n.
  destruct (Z.ltb_spec (ir_have r) (is_length s)); destruct (Z.ltb_spec (ir_left r) (ir_have r)); destruct (Z.ltb_spec (ir_left r) (is_length s)); lia.
Qed.

Lemma cpy_c_facts : forall c r n,
  ic_next_in (cpy_c c r n) = ic_next_in c /\ ic_avail_in (cpy_c c r n) = ic_avail_in c
  /\ ic_next_out (cpy_c c r n) = ic_next_out c /\ ic_avail_out (cpy_c c r n) = ic_avail_out c
  /\ ic_input (cpy_c c r n) = ic_input c /\ zstrm_of_icall (cpy_c c r n) = zstrm_of_icall c
  /\ ic_total_in (cpy_c c r n) = ic_total_in c /\ ic_total_out (cpy_c c r n) = ic_total_out c
  /\ ic_adler (cpy_c c r n) = ic_adler c /\ ic_data_type (cpy_c c r n) = ic_data_type c
  /\ ic_outbuf (cpy_c c r n) = arr_blit (ic_outbuf c) (ir_put r) (ic_input c) (ir_next r) n.
Proof. intros c r n. destruct c. repeat split; reflexivity. Qed.

Lemma sxu_le : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  (szwrap 32 x mod 2 ^ 64 <= szwrap 32 y mod 2 ^ 64 <-> x <= y).
Proof. intros x y Hx Hy. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. Z.to_euclidean_division_equations; lia. Qed.
Lemma sxu_lt : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  (szwrap 32 x mod 2 ^ 64 < szwrap 32 y mod 2 ^ 64 <-> x < y).
Proof. intros x y Hx Hy. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. Z.to_euclidean_division_equations; lia. Qed.

Lemma szwrap32_sub_sx : forall a b, szwrap 32 (szwrap 32 a mod 2 ^ 64 - b) = szwrap 32 (a - b).
Proof.
  intros a b. rewrite <- (szwrap_mod 32 (_ - b)), <- (szwrap_mod 32 (a - b)) by lia. f_equal.
  rewrite <- (Zminus_mod_idemp_l (szwrap 32 a mod 2 ^ 64)), <- (Zminus_mod_idemp_l a) by lia. f_equal. f_equal.
  rewrite <- (szwrap_eqm 32 a) by lia.
  set (x := szwrap 32 a). clearbody x. Z.to_euclidean_division_equations. nia.
Qed.

Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Section ArmCOPY.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_COPY_ : forall flush w, is_mode (w_s w) = COPY_ -> arm_ok flush w = true -> leave_okb (w_s w) = true.
  Hypothesis OK_COPY : forall flush w, is_mode (w_s w) = COPY -> arm_ok flush w = true -> leave_okb (w_s w) = true.

  Definition cpy_m1 (s : inflate_state) (r : iregs) : Z := if ir_have r <=? is_length s then ir_have r else is_length s.
  Definition cpy_m (s : inflate_state) (r : iregs) : Z := if ir_left r <? cpy_m1 s r then ir_left r else cpy_m1 s r.
  Lemma cpy_m_eq : forall s r, cpy_m s r = cpy_n s r.
  Proof.
    intros s r. unfold cpy_m, cpy_m1, cpy_n.
    destruct (Z.leb_spec (ir_have r) (is_length s)); destruct (Z.ltb_spec (ir_have r) (is_length s)); try lia;
      replace (ir_have r) with (is_length s) by lia; reflexivity.
  Qed.
End ArmCOPY.
End RefInflateA_COPY.

Module RefInflateA_LENEXT.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HDR.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateA_DISTEXT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Lemma arm_LENEXT_off : forall s c r, is_extra s = 0 ->
  arm_LENEXT ivar_ref (mkW s c r) = arm_DIST ivar_ref (mkW (lx_fin s) c r).
Proof.
  intros s c r H. unfold arm_LENEXT. mstep1 (@gs_eq inflate_state). rewrite H. cbn [Z.eqb negb].
  mstep1 (@aret_eq unit). unfold aux. cbn [iv_aux ivar_ref]. mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
Qed.

Lemma arm_LENEXT_on : forall s c r, is_extra s <> 0 ->
  arm_LENEXT ivar_ref (mkW s c r) =
    match NEEDBITS (is_extra s) (mkW s c r) with
    | ARun _ (mkW s1 c1 r1) => arm_DIST ivar_ref (mkW (lx_fin (lx_s s (ir_hold r1))) c1 (ddrop r1 (is_extra s)))
    | ALeave w1 => ALeave w1
    | ARet rc w1 => ARet rc w1
    end.
Proof.
  intros s c r H. unfold arm_LENEXT. mstep1 (@gs_eq inflate_state). rewrite (proj2 (Z.eqb_neq _ _) H). cbn [negb].
  rewrite abind_run. rewrite abind_run.
  destruct (NEEDBITS (is_extra s) (mkW s c r)) as [[] [s1 c1 r1] | w1 | rc w1] eqn:HN; try reflexivity.
  destruct (NEEDBITS_k_run 8 _ s c r s1 c1 r1 HN) as [-> ->].
  mstep1 BITS_eq. mstep1 us_eq. mstep1 DROPBITS_eq. unfold add_back, aux. cbn [iv_aux ivar_ref]. rewrite us_eq. cbv beta iota.
  mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
Qed.

Lemma lx_s_facts : forall s h,
  is_mode (lx_s s h) = is_mode s /\ is_flags (lx_s s h) = is_flags s /\ is_wrap (lx_s s h) = is_wrap s /\ is_check (lx_s s h) = is_check s
  /\ is_lens (lx_s s h) = is_lens s /\ is_work (lx_s s h) = is_work s /\ is_codes (lx_s s h) = is_codes s
  /\ is_window (lx_s s h) = is_window s /\ is_window_blk (lx_s s h) = is_window_blk s
  /\ is_wsize (lx_s s h) = is_wsize s /\ is_self_blk (lx_s s h) = is_self_blk s /\ is_wbits (lx_s s h) = is_wbits s
  /\ is_extra (lx_s s h) = is_extra s.
Proof. intros s h. unfold lx_s. repeat split; reflexivity. Qed.

Lemma lx_fin_facts : forall s,
  is_mode (lx_fin s) = DIST /\ is_flags (lx_fin s) = is_flags s /\ is_wrap (lx_fin s) = is_wrap s /\ is_check (lx_fin s) = is_check s
  /\ is_lens (lx_fin s) = is_lens s /\ is_work (lx_fin s) = is_work s /\ is_codes (lx_fin s) = is_codes s
  /\ is_window (lx_fin s) = is_window s /\ is_window_blk (lx_fin s) = is_window_blk s
  /\ is_wsize (lx_fin s) = is_wsize s /\ is_self_blk (lx_fin s) = is_self_blk s /\ is_wbits (lx_fin s) = is_wbits s.
Proof. intros s. unfold lx_fin. repeat split; reflexivity. Qed.

Lemma iwf_set_was : forall st v, 0 <= v < 2 ^ 32 -> iwf st -> iwf (iset_was st v).
Proof.
  intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.

Lemma lx_s_iwf : forall s h, iwf s -> iwf (lx_s s h).
Proof.
  intros s h H. unfold lx_s. apply iwf_set_back; [apply swrap32_range|]. apply iwf_set_length; [apply wrap32_range | exact H].
Qed.

Lemma lx_fin_iwf : forall s, iwf s -> iwf (lx_fin s).
Proof.
  intros s H. unfold lx_fin. apply iwf_set_mode; [cbv; split; discriminate|]. apply iwf_set_was; [| exact H].
  pose proof (iwf_x s H) as X. unfold iwfx in X. decompose [and] X. split; assumption.
Qed.

Section ArmLENEXT.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_LENEXT : forall flush w, is_mode (w_s w) = LENEXT -> arm_ok flush w = true ->
    leave_okb (w_s w) = true /\ lenext_okb (w_s w) = true.
  Hypothesis OK_LENEXT_next : forall flush w w2, is_mode (w_s w) = LENEXT -> arm_ok flush w = true ->
    lenext_next w = Some w2 -> arm_ok flush w2 = true.
End ArmLENEXT.
End RefInflateA_LENEXT.

Module RefInflateA_MATCH2.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Fixpoint lecomb (n : nat) (f : Z -> Z) : Z :=
  match n with O => 0 | S n' => f 0 + 256 * lecomb n' (fun t => f (t + 1)) end.

Lemma lecomb_range : forall n f, (forall t, 0 <= t < Z.of_nat n -> 0 <= f t < 256) -> 0 <= lecomb n f < 2 ^ (8 * Z.of_nat n).
Proof.
  induction n as [|n IH]; intros f Hf; [cbn; lia|].
  cbn [lecomb]. specialize (IH (fun t => f (t + 1)) ltac:(intros t Ht; apply Hf; lia)).
  pose proof (Hf 0 ltac:(lia)). replace (8 * Z.of_nat (S n)) with (8 * Z.of_nat n + 8) by lia.
  rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. lia.
Qed.

Lemma sxu_eq : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  (szwrap 32 x mod 2 ^ 64 = szwrap 32 y mod 2 ^ 64 <-> x = y).
Proof. intros x y Hx Hy. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. Z.to_euclidean_division_equations; lia. Qed.

Section CopyLoops.
  Variable P0 : Z.
Variable NO : Z.
Variable put0 : Z.
Variable n : Z.
Variable FROM : Z.
Variable dd : Z.
Variable SPV : Z.
Variable S2V : Z.
Variable sv : Z -> Z.
Variable ob : arr.
  Local Notation D := (P0 + put0).
  Definition g (p : Z) : Z := if p <? put0 then arr_get ob p else sv (p - put0).

  Hypothesis HP0 : 0 < P0 /\ P0 + NO < 2 ^ 63.
  Hypothesis Hput : 0 <= put0 /\ put0 + n <= NO.
  Hypothesis Hn : 0 < n < 2 ^ 32.
  Hypothesis HFROM : 0 <= FROM /\ FROM + n < 2 ^ 63.
  Hypothesis Hsv : forall m, 0 <= m < n -> 0 <= sv m < 256.
  Hypothesis Hob : forall p, 0 <= p < put0 -> 0 <= arr_get ob p < 256.
  Hypothesis HSPV : 0x36000 <= SPV /\ SPV + 208 < 2 ^ 63.
  Hypothesis HS2V : 0 <= S2V < 2 ^ 64.
  Hypothesis Hsep_slot : SPV + 208 <= P0 \/ P0 + NO <= SPV.
End CopyLoops.

Section CopyJob.
  Variable P0 : Z.
Variable NO : Z.
Variable put0 : Z.
Variable n : Z.
Variable FROM : Z.
Variable dd : Z.
Variable SPV : Z.
Variable S2V : Z.
Variable sv : Z -> Z.
Variable ob : arr.
  Local Notation D := (P0 + put0).
End CopyJob.
End RefInflateA_MATCH2.

Module RefInflateA_MATCH.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST.RefInflateA_COPY.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateA_DISTEXT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateOkb.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateOkb.RefInflateA_MATCH1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST.RefInflateA_MATCH2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition msv (s : inflate_state) (c : icall) (r : iregs) (from : fromptr) : Z -> Z :=
  mc_src (is_window s) (ic_outbuf c) (ir_put r) from.
Definition mdd (r : iregs) (from : fromptr) (n : Z) : Z :=
  match from with FWin _ => n + 8 | FOut i => ir_put r - i end.

Lemma g_out : forall win ob put i m, i < put -> 0 <= m ->
  g put (mc_src win ob put (FOut i)) ob (i + m) = mc_src win ob put (FOut i) m.
Proof.
  intros win ob put i m Hi Hm. unfold g, mc_src. set (d := put - i).
  destruct (Z.ltb_spec (i + m) put).
  - rewrite Z.mod_small by lia. reflexivity.
  - f_equal. replace (i + m - put) with (m - d) by lia. rewrite <- (Z.mod_add (m - d) 1 d) by lia. f_equal. f_equal. lia.
Qed.

Definition mt_r (r : iregs) (n : Z) : iregs := irset_put (irset_left r (wrap32 (ir_left r - n))) (ir_put r + n).
Definition mt_c (s : inflate_state) (c : icall) (r : iregs) (from : fromptr) (n : Z) : icall :=
  icset_outbuf c (mc_obn (is_window s) (ic_outbuf c) (ir_put r) from (Z.to_nat n)).

Lemma mt_r_facts : forall r n, 0 <= n <= ir_left r -> ir_left r < 2 ^ 32 ->
  ir_next (mt_r r n) = ir_next r /\ ir_have (mt_r r n) = ir_have r /\ ir_put (mt_r r n) = ir_put r + n /\ ir_left (mt_r r n) = ir_left r - n
  /\ ir_hold (mt_r r n) = ir_hold r /\ ir_bits (mt_r r n) = ir_bits r /\ ir_in (mt_r r n) = ir_in r /\ ir_out (mt_r r n) = ir_out r /\ ir_ret (mt_r r n) = ir_ret r.
Proof. intros r n Hn Hl. unfold mt_r. destruct r; cbn in *. rewrite wrap32_id by lia. repeat split; reflexivity. Qed.

Lemma mt_c_facts : forall s c r from n,
  ic_next_in (mt_c s c r from n) = ic_next_in c /\ ic_avail_in (mt_c s c r from n) = ic_avail_in c
  /\ ic_next_out (mt_c s c r from n) = ic_next_out c /\ ic_avail_out (mt_c s c r from n) = ic_avail_out c
  /\ ic_input (mt_c s c r from n) = ic_input c /\ ic_total_in (mt_c s c r from n) = ic_total_in c /\ ic_total_out (mt_c s c r from n) = ic_total_out c
  /\ ic_adler (mt_c s c r from n) = ic_adler c /\ ic_data_type (mt_c s c r from n) = ic_data_type c
  /\ zstrm_of_icall (mt_c s c r from n) = zstrm_of_icall c /\ ic_msg (mt_c s c r from n) = ic_msg c.
Proof. intros. unfold mt_c. destruct c; repeat split; reflexivity. Qed.
Local Ltac sxu :=
  match goal with
  | |- szwrap 32 ?a mod 2 ^ 64 < szwrap 32 ?b mod 2 ^ 64 => apply (proj2 (sxu_lt a b ltac:(lia) ltac:(lia))); lia
  | |- szwrap 32 ?a mod 2 ^ 64 <= szwrap 32 ?b mod 2 ^ 64 => apply (proj2 (sxu_le a b ltac:(lia) ltac:(lia))); lia
  | |- ~ (szwrap 32 ?a mod 2 ^ 64 < szwrap 32 ?b mod 2 ^ 64) => intros X; apply (proj1 (sxu_lt a b ltac:(lia) ltac:(lia))) in X; lia
  | |- ~ (szwrap 32 ?a mod 2 ^ 64 <= szwrap 32 ?b mod 2 ^ 64) => intros X; apply (proj1 (sxu_le a b ltac:(lia) ltac:(lia))) in X; lia
  | |- szwrap 32 ?a mod 2 ^ 64 <> szwrap 32 ?b mod 2 ^ 64 => intros X; apply (proj1 (sxu_eq a b ltac:(lia) ltac:(lia))) in X; lia
  | |- szwrap 32 ?a mod 2 ^ 64 = szwrap 32 ?b mod 2 ^ 64 => apply (proj2 (sxu_eq a b ltac:(lia) ltac:(lia))); lia
  | |- szwrap 32 ?a mod 2 ^ 64 <> 0 => intros X; apply (proj1 (szwrap32_mod64_zero a ltac:(lia))) in X; lia
  | |- szwrap 32 ?a mod 2 ^ 64 = 0 => apply (proj2 (szwrap32_mod64_zero a ltac:(lia))); lia
  end.

Section ArmMATCH.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_MATCH : forall flush w, is_mode (w_s w) = MATCH -> arm_ok flush w = true ->
    leave_okb (w_s w) = true /\ match_okb (w_s w) = true.
  Definition wcopy (s : inflate_state) (copyw : Z) : Z :=
    if is_wnext s <? copyw then copyw - is_wnext s else copyw.
  Definition wfrom (s : inflate_state) (copyw : Z) : fromptr :=
    if is_wnext s <? copyw then FWin (is_wsize s - (copyw - is_wnext s)) else FWin (is_wnext s - copyw).
  Definition lmin (s : inflate_state) (x : Z) : Z := if is_length s <? x then is_length s else x.
  Local Ltac kin := cbn; repeat (first [ left; reflexivity | right ]).
End ArmMATCH.
End RefInflateA_MATCH.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma land240_le15 : forall op, 0 <= op < 256 -> (Z.land op 240 =? 0) = (op <=? 15).
Proof.
  intros op Hop.
  assert (H : forallb (fun i : nat => Bool.eqb (Z.land (Z.of_nat i) 240 =? 0) (Z.of_nat i <=? 15)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat op) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  apply Bool.eqb_prop in H. exact H.
Qed.

Section ArmDIST.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_DIST : forall flush w, is_mode (w_s w) = DIST -> arm_ok flush w = true ->
    leave_okb (w_s w) = true /\ dist_okb w = true.
  Hypothesis OK_DIST_next : forall flush w w2, is_mode (w_s w) = DIST -> arm_ok flush w = true ->
    dist_next w = Some w2 -> arm_ok flush w2 = true.
End ArmDIST.

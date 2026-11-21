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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.

Module RefBuildTree5.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefPqdown_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefGenCodes_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable (t : tree_id).
Local Notation PB := (p_pending_buf p).
Local Notation T := (S + toff t).
Local Notation E := (sd_elems t).
Local Notation SP := (sp - 192).
Local Notation U := (bt_upd ds t).
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.
Local Notation stree_dl := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stree_dl t).
Local Notation stF := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF t).
Local Notation X0 := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.X0 ds t).
Local Notation L1 := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.L1 t).
Local Notation tsize_elems := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.tsize_elems t).
Local Notation elems_range := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.elems_range t).
Local Notation dsc_off_val := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.dsc_off_val t).
Local Notation SDA_range := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.SDA_range t).
Local Notation STP_range := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.STP_range t).
Local Notation slen := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.slen t).
Local Notation slen_ge := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.slen_ge t).
Local Notation STP_rod := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.STP_rod t).
Local Notation stree_pb := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_pb t).
Local Notation stree_dl_bound := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_dl_bound t).
Local Notation stree_Len_dl := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_Len_dl t).
Local Notation xbits := (GenBitlenModel.xbits t).
Local Notation stree_has_STP := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_has_STP t).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].



Definition FB5 : list (nat * Z) :=
  [(0%nat, 65536); (1%nat, 65536); (2%nat, 573); (3%nat, 256); (4%nat, 65536); (5%nat, 16); (6%nat, 65536)].

Definition VB5 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 300); (36%nat, 600); (37%nat, 600);
   (38%nat, 600); (39%nat, 16); (40%nat, 300); (41%nat, 600); (42%nat, 2 ^ 64); (43%nat, 2 ^ 64);
   (44%nat, 2 ^ 63); (45%nat, 2 ^ 63); (46%nat, 3000); (47%nat, 2 ^ 63); (48%nat, 600); (49%nat, 16)].

Local Notation ML := (sd_max_length t).
Local Notation BASE := (sd_extra_base t).

Lemma ml_range : 7 <= ML <= 15.
Proof. destruct t; cbn; unfold MAX_BITS, MAX_BL_BITS; lia. Qed.
Lemma base_val : BASE = match t with TL => 257 | _ => 0 end.
Proof. destruct t; reflexivity. Qed.
Lemma base_range : 0 <= BASE < 300 /\ BASE < E.
Proof. pose proof elems_range. destruct t; cbn in *; unfold LITERALS, L_CODES, LITERALS, LENGTH_CODES in *; lia. Qed.
Lemma EXP_range : TREES_ROD_LO <= EXP t /\ EXP t + 4 * (E - BASE) <= TREES_ROD_HI.
Proof.
  destruct t; cbn; unfold A_extra_lbits, A_extra_dbits, A_extra_blbits, TREES_ROD_LO, TREES_ROD_HI,
    L_CODES, D_CODES, BL_CODES, LITERALS, LENGTH_CODES; lia.
Qed.

Lemma extra_view_bound : forall x, 0 <= stF (arr_make 1 0) (arr_make 1 0) (arr_make 1 0) (arr_make 1 0) (arr_make 1 0) 5%nat x < 16.
Proof.
  intros x. cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF]. destruct t; cbn [sd_extra_bits].
  - pose proof (extra_lbits_bound x). rewrite Z.mod_small; lia.
  - pose proof (extra_dbits_bound x). rewrite Z.mod_small; lia.
  - pose proof (extra_blbits_bound x). rewrite Z.mod_small; lia.
Qed.
Lemma extra_view_bound' : forall FC DL HP DP BC x, 0 <= stF FC DL HP DP BC 5%nat x < 16.
Proof. intros. apply extra_view_bound. Qed.


Section PhaseFG.
Variable FC : arr.
Variable HP : arr.
Variable HL : Z.
Variable DP : arr.
Variable MC : Z.
Variable K : Z.
Local Notation W4 DL BC OL SL := (U FC DL HP HL (K - 1) DP BC OL SL MC).

Hypothesis RFC : forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536.
Hypothesis LFC : arr_len FC = tsize t.
Hypothesis Hmc : 0 <= MC < E.
Hypothesis HK : 1 <= K <= 573.
Hypothesis PQH : forall h, K <= h < 573 -> 0 <= arr_get HP h < tsize t.

Local Ltac vfix :=
  repeat match goal with H : hv ?hh ?e = _ |- context [hv ?hh ?e] => rewrite !H end;
  repeat match goal with
         | H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H
         | H : wb ?a ?e = _ |- context [wb ?a ?e] => rewrite !H
         end.

Local Ltac splitand H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "X" in let H2 := fresh "X" in destruct H as [H1 H2]; splitand H1; splitand H2
  | _ => idtac
  end.

Lemma GI_aux : forall DL BC n bits v w,
  (forall i, 0 <= i < tsize t -> 0 <= arr_get DL i < 65536) -> arr_len DL = tsize t ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) -> arr_len BC = 16 ->
  (forall i, 0 <= i < tsize t -> 0 <= arr_get (arr_set DL n (wrap16 v)) i < 65536) /\ arr_len (arr_set DL n (wrap16 v)) = tsize t
  /\ (forall i, 0 <= i < 16 -> 0 <= arr_get (arr_set BC bits (wrap16 w)) i < 65536) /\ arr_len (arr_set BC bits (wrap16 w)) = 16.
Proof.
  intros DL BC n bits v w RDL LDL RBC LBC.
  split; [|split; [rewrite arr_len_set; exact LDL | split; [| rewrite arr_len_set; exact LBC]]].
  - intros i Hi. rewrite arr_get_set. destruct (_ && _); [pose proof (wrap16_range v); lia | apply RDL; exact Hi].
  - intros i Hi. rewrite arr_get_set. destruct (_ && _); [pose proof (wrap16_range w); lia | apply RBC; exact Hi].
Qed.


Local Ltac openGI HG HC RDL LDL RBC LBC ROL RSL C24 :=
  destruct HG as (HC & RDL & LDL & RBC & LBC & ROL & RSL & C24).

Lemma slen_E : STP t <> 0 -> E <= slen.
Proof.
  unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.slen. destruct t; cbn [sd_elems STP];
    unfold L_CODES, D_CODES, BL_CODES, LITERALS, LENGTH_CODES, A_static_ltree, A_static_dtree; intros; lia.
Qed.


Local Ltac nodeG DL h RDL LDL Rd Vh Vn Vd Vdd :=
  let Vn' := fresh "Vn'" in let Vd' := fresh "Vd'" in
  assert (Vh : hv HP h = arr_get HP h) by (apply hv_get; pose proof (PQH h); lia);
  assert (Vn' : pb DL (arr_get HP h) = arr_get DL (arr_get HP h))
    by (apply (pb_get DL); [intros q Hq; apply RDL; rewrite <- LDL; exact Hq | rewrite LDL; apply PQH; lia]);
  assert (Vn : pb DL (hv HP h) = arr_get DL (arr_get HP h)) by (rewrite Vh; exact Vn');
  assert (Vd' : pb DL (arr_get DL (arr_get HP h)) = arr_get DL (arr_get DL (arr_get HP h)))
    by (apply (pb_get DL); [intros q Hq; apply RDL; rewrite <- LDL; exact Hq | rewrite LDL; exact Rd]);
  assert (Vd : pb DL (pb DL (hv HP h)) = arr_get DL (arr_get DL (arr_get HP h))) by (rewrite Vn; exact Vd');
  assert (Vdd : 0 <= arr_get DL (arr_get DL (arr_get HP h)) < 65536) by (apply RDL; exact Rd).


Lemma xbits_range : forall n, 0 <= xbits n < 16.
Proof.
  intros n. unfold GenBitlenModel.xbits. destruct (BASE <=? n); [|lia].
  pose proof (extra_lbits_bound (n - BASE)). pose proof (extra_dbits_bound (n - BASE)). pose proof (extra_blbits_bound (n - BASE)).
  destruct t; cbn [sd_extra_bits]; lia.
Qed.

Local Ltac ceqG :=
  nf; vfix;
  repeat match goal with H : _ mod 2 ^ 32 = xbits _ |- context [_ mod 2 ^ 32] => rewrite H end;
  repeat match goal with H : xbits ?n = 0 |- context [xbits ?n] => rewrite H end;
  rewrite <- ?stree_Len_dl;
  first [ reflexivity | f_equal; lia | f_equal; ring ].


Local Notation GB1 := (GenBitlenModel.GB1 t MC).
Local Notation gb1_ok := (GenBitlenModel.gb1_ok t MC).

Lemma bits_range : forall DL d, 0 <= arr_get DL d ->
  1 <= (if ML <? arr_get DL d + 1 then ML else arr_get DL d + 1) <= ML.
Proof. intros DL d Hd. pose proof ml_range. destruct (Z.ltb_spec ML (arr_get DL d + 1)); lia. Qed.

End PhaseFG.

End Walk.
End RefBuildTree5.

Module RefBuildTree6.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefPqdown_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefGenCodes_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable (t : tree_id).
Local Notation PB := (p_pending_buf p).
Local Notation T := (S + toff t).
Local Notation E := (sd_elems t).
Local Notation SP := (sp - 192).
Local Notation U := (bt_upd ds t).
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.
Local Notation stree_dl := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stree_dl t).
Local Notation stF := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF t).
Local Notation X0 := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.X0 ds t).
Local Notation L1 := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.L1 t).
Local Notation tsize_elems := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.tsize_elems t).
Local Notation elems_range := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.elems_range t).
Local Notation dsc_off_val := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.dsc_off_val t).
Local Notation SDA_range := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.SDA_range t).
Local Notation STP_range := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.STP_range t).
Local Notation slen := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.slen t).
Local Notation slen_ge := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.slen_ge t).
Local Notation STP_rod := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.STP_rod t).
Local Notation stree_pb := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_pb t).
Local Notation stree_dl_bound := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_dl_bound t).
Local Notation stree_Len_dl := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_Len_dl t).
Local Notation xbits := (GenBitlenModel.xbits t).
Local Notation stree_has_STP := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_has_STP t).
Local Notation ml_range := (RefBuildTree5.ml_range t).
Local Notation base_range := (RefBuildTree5.base_range t).
Local Notation EXP_range := (RefBuildTree5.EXP_range t).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].



Definition FB6 : list (nat * Z) :=
  [(0%nat, 65536); (1%nat, 65536); (2%nat, 573); (3%nat, 256); (4%nat, 65536); (5%nat, 16); (6%nat, 65536)].

Definition VB6 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 300); (36%nat, 600); (37%nat, 600);
   (38%nat, 600); (39%nat, 2)].

Local Ltac vfix :=
  repeat match goal with H : hv ?hh ?e = _ |- context [hv ?hh ?e] => rewrite !H end;
  repeat match goal with
         | H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H
         | H : wb ?a ?e = _ |- context [wb ?a ?e] => rewrite !H
         end.

Local Ltac bl_close LBC :=
  lazymatch goal with |- @eq arr _ _ => idtac end;
  nf; vfix;
  first [ rewrite GenBitlenModel.bl_adj_eq by (rewrite ?LBC; lia) | rewrite GenBitlenModel.bl_adj_lt by (rewrite ?LBC; lia) ];
  rewrite ?wrap16_szwrap32, <- ?wrap16_mod;
  repeat first [ lazymatch goal with |- ?a = ?a => reflexivity end | lia | progress f_equal ].

Local Notation ML := (sd_max_length t).

Lemma forallb_Zrange : forall (f : Z -> bool) (lo : Z) (n : nat),
  forallb f (map (fun i => lo + Z.of_nat i) (seq 0 n)) = true ->
  forall z, lo <= z < lo + Z.of_nat n -> f z = true.
Proof.
  intros f lo n H z Hz. rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat (z - lo)). split; [lia|]. apply in_seq. lia.
Qed.

Lemma fin_lemma : forall ovf, 1 <= ovf < 600 ->
  szwrap 32 (ovf - Z.land (szwrap 32 (ovf + -1)) (-2) + -2) = ovf - 2 * ((ovf - 1) / 2) - 2.
Proof.
  intros ovf H.
  pose proof (forallb_Zrange (fun o => Z.eqb (szwrap 32 (o - Z.land (szwrap 32 (o + -1)) (-2) + -2)) (o - 2 * ((o - 1) / 2) - 2))
                1 599 ltac:(vm_compute; reflexivity) ovf ltac:(lia)) as E.
  apply Z.eqb_eq in E. exact E.
Qed.

Lemma mod64_inj_small : forall a b, -1 <= a < 2 ^ 63 -> -1 <= b < 2 ^ 63 -> a mod 2 ^ 64 = b mod 2 ^ 64 -> a = b.
Proof.
  intros a b Ha Hb H.
  destruct (Z.eq_dec a (-1)) as [Ea|Ea]; destruct (Z.eq_dec b (-1)) as [Eb|Eb]; try lia.
  - exfalso. rewrite Ea in H. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) in H. rewrite Z.mod_small in H by lia. lia.
  - exfalso. rewrite Eb in H. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) in H. rewrite Z.mod_small in H by lia. lia.
  - rewrite !Z.mod_small in H by lia. exact H.
Qed.

Section PhaseH.
Variable FC : arr.
Variable DL : arr.
Variable HP : arr.
Variable HL : Z.
Variable HM : Z.
Variable DP : arr.
Variable OL : Z.
Variable SL : Z.
Variable MC : Z.
Local Notation W1 BC := (U FC DL HP HL HM DP BC OL SL MC).

Hypothesis Hmc : 0 <= MC < E.

Lemma set_w16_range : forall A j v,
  (forall i, 0 <= i < 16 -> 0 <= arr_get A i < 65536) ->
  forall i, 0 <= i < 16 -> 0 <= arr_get (arr_set A j (wrap16 v)) i < 65536.
Proof.
  intros A j v HA i Hi. rewrite arr_get_set. destruct (_ && _); [pose proof (wrap16_range v); lia | apply HA; exact Hi].
Qed.

Lemma HI_adj : forall BC L r,
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) -> arr_len BC = 16 ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get (GenBitlenModel.bl_adj L BC r) i < 65536)
  /\ arr_len (GenBitlenModel.bl_adj L BC r) = 16.
Proof.
  intros BC L r RBC LBC. unfold GenBitlenModel.bl_adj. cbv zeta. split.
  - apply set_w16_range. apply set_w16_range. apply set_w16_range. exact RBC.
  - rewrite !arr_len_set. exact LBC.
Qed.

Local Ltac l2regs HR0 PX :=
  destruct HR0 as ((P21 & P22 & P2 & P8 & P20 & P19 & P26 & P12 & P6 & P17 & P10 & P28 & P29 & P30 & P31 & P5 & P7 & PX) & P11).

End PhaseH.

End Walk.
End RefBuildTree6.

Module RefBuildTree7.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefPqdown_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefGenCodes_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable (t : tree_id).
Local Notation PB := (p_pending_buf p).
Local Notation T := (S + toff t).
Local Notation E := (sd_elems t).
Local Notation SP := (sp - 192).
Local Notation U := (bt_upd ds t).
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.
Local Notation stree_dl := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stree_dl t).
Local Notation stF := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF t).
Local Notation X0 := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.X0 ds t).
Local Notation L1 := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.L1 t).
Local Notation tsize_elems := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.tsize_elems t).
Local Notation elems_range := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.elems_range t).
Local Notation dsc_off_val := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.dsc_off_val t).
Local Notation SDA_range := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.SDA_range t).
Local Notation STP_range := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.STP_range t).
Local Notation slen := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.slen t).
Local Notation slen_ge := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.slen_ge t).
Local Notation STP_rod := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.STP_rod t).
Local Notation stree_pb := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_pb t).
Local Notation stree_dl_bound := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_dl_bound t).
Local Notation stree_Len_dl := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_Len_dl t).
Local Notation xbits := (GenBitlenModel.xbits t).
Local Notation stree_has_STP := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_has_STP t).
Local Notation ml_range := (RefBuildTree5.ml_range t).
Local Notation base_range := (RefBuildTree5.base_range t).
Local Notation EXP_range := (RefBuildTree5.EXP_range t).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].




Definition FB7 : list (nat * Z) :=
  [(0%nat, 65536); (1%nat, 65536); (2%nat, 573); (3%nat, 256); (4%nat, 65536); (5%nat, 16); (6%nat, 65536)].

Definition VB7 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 300); (36%nat, 600); (37%nat, 600);
   (38%nat, 600); (39%nat, 2)].

Local Ltac vfix :=
  repeat match goal with H : hv ?hh ?e = _ |- context [hv ?hh ?e] => rewrite !H end;
  repeat match goal with
         | H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H
         | H : wb ?a ?e = _ |- context [wb ?a ?e] => rewrite !H
         end.

Local Ltac bl_close LBC :=
  lazymatch goal with |- @eq arr _ _ => idtac end;
  nf; vfix;
  first [ rewrite GenBitlenModel.bl_adj_eq by (rewrite ?LBC; lia) | rewrite GenBitlenModel.bl_adj_lt by (rewrite ?LBC; lia) ];
  rewrite ?wrap16_szwrap32, <- ?wrap16_mod;
  repeat first [ lazymatch goal with |- ?a = ?a => reflexivity end | lia | progress f_equal ].

Local Notation ML := (sd_max_length t).




Section PhaseH.
Variable FC : arr.
Variable DL : arr.
Variable HP : arr.
Variable HL : Z.
Variable HM : Z.
Variable DP : arr.
Variable OL : Z.
Variable SL : Z.
Variable MC : Z.
Local Notation W1 BC := (U FC DL HP HL HM DP BC OL SL MC).

Hypothesis Hmc : 0 <= MC < E.
Local Notation HI_adj := (RefBuildTree6.HI_adj).

Local Ltac l2regs HR0 PX :=
  destruct HR0 as ((P21 & P22 & P2 & P8 & P20 & P19 & P26 & P12 & P6 & P17 & P10 & P28 & P29 & P30 & P31 & P5 & P7 & PX) & P11).

End PhaseH.

End Walk.
End RefBuildTree7.

Module RefBuildTree8.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefPqdown_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefGenCodes_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable (t : tree_id).
Local Notation PB := (p_pending_buf p).
Local Notation T := (S + toff t).
Local Notation E := (sd_elems t).
Local Notation SP := (sp - 192).
Local Notation U := (bt_upd ds t).
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.
Local Notation stree_dl := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stree_dl t).
Local Notation stF := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF t).
Local Notation X0 := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.X0 ds t).
Local Notation L1 := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.L1 t).
Local Notation tsize_elems := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.tsize_elems t).
Local Notation elems_range := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.elems_range t).
Local Notation dsc_off_val := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.dsc_off_val t).
Local Notation SDA_range := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.SDA_range t).
Local Notation STP_range := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.STP_range t).
Local Notation slen := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.slen t).
Local Notation slen_ge := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.slen_ge t).
Local Notation STP_rod := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.STP_rod t).
Local Notation stree_pb := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_pb t).
Local Notation stree_dl_bound := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_dl_bound t).
Local Notation stree_Len_dl := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_Len_dl t).
Local Notation xbits := (GenBitlenModel.xbits t).
Local Notation stree_has_STP := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_has_STP t).
Local Notation ml_range := (RefBuildTree5.ml_range t).
Local Notation base_range := (RefBuildTree5.base_range t).
Local Notation EXP_range := (RefBuildTree5.EXP_range t).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].



Definition FB8 : list (nat * Z) :=
  [(0%nat, 65536); (1%nat, 65536); (2%nat, 573); (3%nat, 256); (4%nat, 65536); (5%nat, 16); (6%nat, 65536)].

Definition VB8 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 300); (36%nat, 600); (37%nat, 16);
   (38%nat, 600); (39%nat, 65536); (40%nat, 2 ^ 64); (41%nat, 16); (42%nat, 573)].

Local Ltac vfix :=
  repeat match goal with H : hv ?hh ?e = _ |- context [hv ?hh ?e] => rewrite !H end;
  repeat match goal with
         | H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H
         | H : wb ?a ?e = _ |- context [wb ?a ?e] => rewrite !H
         end.

Local Notation ML := (sd_max_length t).

Section PhaseH3.
Variable FC : arr.
Variable HP : arr.
Variable HL : Z.
Variable HM : Z.
Variable DP : arr.
Variable BC : arr.
Variable SL : Z.
Variable MC : Z.
Local Notation W3 DL OL := (U FC DL HP HL HM DP BC OL SL MC).

Hypothesis Hmc : 0 <= MC < E.
Hypothesis RFC : forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536.
Hypothesis LFC : arr_len FC = tsize t.
Hypothesis RBC : forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536.
Hypothesis LBC : arr_len BC = 16.

Local Notation GB3i := (GenBitlenModel.GB3i t MC).
Local Notation gb3i_ok := (GenBitlenModel.gb3i_ok t MC).
Local Notation gb3_ok := (GenBitlenModel.gb3_ok t MC).

Local Ltac openI3 HI HC RDL LDL ROL C24 := destruct HI as (HC & RDL & LDL & ROL & C24).

End PhaseH3.

End Walk.
End RefBuildTree8.

Module RefBuildTree9.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefPqdown_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefGenCodes_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable (t : tree_id).
Local Notation PB := (p_pending_buf p).
Local Notation T := (S + toff t).
Local Notation E := (sd_elems t).
Local Notation SP := (sp - 192).
Local Notation U := (bt_upd ds t).
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.
Local Notation stree_dl := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stree_dl t).
Local Notation stF := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF t).
Local Notation X0 := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.X0 ds t).
Local Notation L1 := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.L1 t).
Local Notation tsize_elems := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.tsize_elems t).
Local Notation elems_range := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.elems_range t).
Local Notation dsc_off_val := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.dsc_off_val t).
Local Notation SDA_range := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.SDA_range t).
Local Notation STP_range := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.STP_range t).
Local Notation slen := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.slen t).
Local Notation slen_ge := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.slen_ge t).
Local Notation STP_rod := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.STP_rod t).
Local Notation stree_pb := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_pb t).
Local Notation stree_dl_bound := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_dl_bound t).
Local Notation stree_Len_dl := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_Len_dl t).
Local Notation xbits := (GenBitlenModel.xbits t).
Local Notation stree_has_STP := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.stree_has_STP t).
Local Notation ml_range := (RefBuildTree5.ml_range t).
Local Notation base_range := (RefBuildTree5.base_range t).
Local Notation EXP_range := (RefBuildTree5.EXP_range t).
Local Notation L2 := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.L2 t).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].



Definition FB9 : list (nat * Z) :=
  [(0%nat, 65536); (1%nat, 65536); (2%nat, 573); (3%nat, 256); (4%nat, 65536); (5%nat, 16); (6%nat, 65536)].

Definition VB9 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 64);
   (36%nat, 2 ^ 64); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64);
   (42%nat, 2 ^ 64); (43%nat, 2 ^ 64); (44%nat, 2 ^ 64); (45%nat, 2 ^ 64); (46%nat, 2 ^ 64); (47%nat, 2 ^ 64)].

Local Notation ML := (sd_max_length t).
Local Notation BASE := (sd_extra_base t).


End Walk.
End RefBuildTree9.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree9.

Module RefTrStored_run.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable buf : option Z.
Variable bufp : Z.
Variable len : Z.
Variable last : Z.
Local Notation PB := (p_pending_buf p).
Local Notation W := (p_window p).
Local Notation WL := (arr_len (ds_window ds)).
Local Notation pend := (ds_pending ds).
Local Notation bv := (ds_bi_valid ds).
Local Notation bb := (ds_bi_buf ds).
Local Notation nb := (sb_nb ds last).
Hypothesis Hbinv : BINV PBL ds.
Hypothesis Hroom : ds_pending (tr_stored_block ds buf len last) <= PBL.
Hypothesis Hlast : 0 <= last <= 1.
Hypothesis Hlen : 0 <= len.

Lemma HR1 : tsb_hP ds + 1 + 1 + 1 + 1 + len <= PBL.
Proof.
  pose proof Hroom as H. pose proof Hbinv as (Hbv & Hbb & _).
  rewrite tr_stored_block_eq, tsb_tail_pending in H by assumption. exact H.
Qed.
Definition hVB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 65536); (36%nat, 17);
   (37%nat, 2); (38%nat, 2 ^ 63); (39%nat, 2 ^ 63)].
Definition tVB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 63); (36%nat, 2 ^ 63); (37%nat, 2 ^ 64)].

Local Ltac len_bytes :=
  rewrite ?upd4_pending_buf;
  repeat first [ apply tsb_b0 | apply tsb_b1 | apply tsb_b2 | apply tsb_b3 | reflexivity | lia | f_equal ].

End Walk.
End RefTrStored_run.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.

Module RefScanTree_run.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable ds : deflate_state.
Variable t : tree_id.
Variable mc : Z.
Local Notation T := (S + toff t).
Hypothesis HL : tree_lens ds.
Hypothesis HtB : t <> TB.
Hypothesis Hmc : 0 <= mc /\ mc + 1 < tsize t.
Hypothesis Hlen : forall i, 0 <= i <= mc -> 0 <= Len ds t i <= 15.
Hypothesis Hdl : forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl ds t) i < 65536.
Hypothesis Hbl : forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc ds) i < 65536.

Definition SG : deflate_state := set_Len ds t (mc + 1) 65535.

Definition LF : franges := [(S + toff t + 4 * (mc + 1) + 2, 2); (S + 2748, 156)].

Let Ht : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.
Let HlenD : arr_len (tree_dl ds t) = tsize t := tree_lens_dl ds t HL.
Let HlenB : arr_len (ds_bl_tree_fc ds) = 39 := proj1 (proj2 (proj2 (proj2 (proj2 HL)))).

Lemma Ht2 : toff t + 4 * tsize t <= 2748.
Proof. clear -HtB. destruct t; cbn; [lia | lia | congruence]. Qed.

Lemma SG_len_dl : forall t', arr_len (tree_dl SG t') = tsize t'.
Proof. intros t'. unfold SG. rewrite tree_dl_len_set_Len. apply tree_lens_dl. exact HL. Qed.

Lemma SG_Len : forall i, Len SG t i = if mc + 1 =? i then 65535 else Len ds t i.
Proof.
  intros i. unfold SG. rewrite Len_set_Len by (rewrite HlenD; lia).
  destruct (mc + 1 =? i); reflexivity.
Qed.

Lemma SG_dl_range : forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl SG t) i < 65536.
Proof.
  intros i Hi. change (arr_get (tree_dl SG t) i) with (Len SG t i). rewrite SG_Len.
  destruct (mc + 1 =? i); [lia|]. unfold Len. apply Hdl. exact Hi.
Qed.

Lemma SG_lens : tree_lens SG.
Proof.
  unfold SG, set_Len, set_Dad. apply tree_lens_set_dl; [exact HL|]. rewrite arr_len_set. exact HlenD.
Qed.

Lemma SG_bl : ds_bl_tree_fc SG = ds_bl_tree_fc ds.
Proof. unfold SG, set_Len, set_Dad. destruct t; reflexivity. Qed.

Lemma sbf_lens : forall b, arr_len b = 39 -> tree_lens (set_bl_tree_fc SG b).
Proof. intros b Hb. exact (tree_lens_set_fc SG TB b SG_lens Hb). Qed.


Definition stF (b : arr) (f : nat) (x : Z) : Z :=
  match f with 0%nat => pb (tree_dl SG t) x | _ => pb b x end.
Definition VB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 600); (35%nat, 600); (37%nat, 65536);
   (38%nat, 200); (39%nat, 200); (40%nat, 10); (41%nat, 65536); (42%nat, 65536)].
Definition VBp : bounds := VB ++ [(36%nat, 65536)].

Local Ltac nf :=
  cbn [stF];
  repeat match goal with H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H end.

Local Ltac open_cregs H :=
  let H' := fresh "CR'" in pose proof H as H';
  destruct H' as (P10 & P29 & P17 & P30 & P31 & P1).

Local Ltac len_fact i V :=
  assert (V : pb (tree_dl SG t) i = Len SG t i)
    by (unfold Len; apply (pb_get (tree_dl SG t)); [intros q Hq; apply SG_dl_range; rewrite SG_len_dl in Hq; exact Hq | rewrite SG_len_dl; lia]).

Local Ltac bl_fact b i V :=
  assert (V : pb b i = arr_get b i)
    by (apply (pb_get b); [intros q Hq; match goal with R : forall j, 0 <= j < 39 -> _ |- _ => apply R; lia end | lia]).



Definition SL (b : arr) (n pl c k mx mn : Z) : arr :=
  ds_bl_tree_fc (scan_tree_loop (Z.to_nat (mc + 1 - n)) (set_bl_tree_fc SG b) t mc n pl c k mx mn).

Lemma SL_step : forall b n pl c k mx mn, 0 <= n <= mc ->
  SL b n pl c k mx mn =
    let nl := Len SG t (n + 1) in
    if (k + 1 <? mx) && (c =? nl) then SL b (n + 1) pl nl (k + 1) mx mn
    else let '(mx', mn') := tree_counts c nl in SL (st_upd mn b c pl (k + 1)) (n + 1) c nl 0 mx' mn'.
Proof.
  intros b n pl c k mx mn Hn. unfold SL.
  replace (Z.to_nat (mc + 1 - n)) with (Datatypes.S (Z.to_nat (mc + 1 - (n + 1)))) by lia.
  rewrite scan_loop_S. replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
  destruct ((k + 1 <? mx) && (c =? Len SG t (n + 1))); [reflexivity|].
  destruct (tree_counts c (Len SG t (n + 1))); reflexivity.
Qed.

Lemma SL_end : forall b pl c k mx mn, SL b (mc + 1) pl c k mx mn = b.
Proof.
  intros. unfold SL. replace (Z.to_nat (mc + 1 - (mc + 1))) with 0%nat by lia.
  rewrite scan_loop_0. apply sbf_get.
Qed.

Definition BND (n pl c k mx mn : Z) : Prop :=
  (pl = -1 \/ 0 <= pl <= 15) /\ 0 <= c < 65536 /\ (n <= mc -> c <= 15)
  /\ 0 <= k < mx /\ (mx = 138 \/ mx = 6 \/ mx = 7) /\ (mn = 3 \/ mn = 4).

Local Ltac frc2 a b := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr); exact (b r Hr).
Local Ltac frc3 a b c := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr), (b r Hr); exact (c r Hr).

Lemma nl_facts : forall n, 0 <= n <= mc ->
  0 <= Len SG t (n + 1) < 65536 /\ (n + 1 <= mc -> Len SG t (n + 1) <= 15).
Proof.
  intros n Hn. split.
  - pose proof (SG_dl_range (n + 1) ltac:(lia)) as X. unfold Len. exact X.
  - intros Hle. rewrite SG_Len. replace (mc + 1 =? n + 1) with false by (symmetry; apply Z.eqb_neq; lia).
    apply (proj2 (Hlen (n + 1) ltac:(lia))).
Qed.

End Walk.
End RefScanTree_run.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefScanTree_run.

Module RefTrInit_run.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma arr_fill_nat_S : forall {A} k (a : parr A) ofs v,
  arr_fill_nat a ofs (S k) v = arr_set (arr_fill_nat a ofs k v) (ofs + Z.of_nat k) v.
Proof.
  induction k as [|k IH]; intros a ofs v.
  - cbn [arr_fill_nat]. rewrite Z.add_0_r. reflexivity.
  - cbn [arr_fill_nat] in *. rewrite (IH (arr_set a ofs v) (ofs + 1) v). f_equal. lia.
Qed.

Definition zst (s : deflate_state) (t : tree_id) (k : nat) : deflate_state :=
  set_tree_fc s t (arr_fill_nat (tree_fc s t) 0 k 0).

Lemma zst_0 : forall s t, zst s t 0 = s.
Proof. intros s [| |]; destruct s; reflexivity. Qed.

Lemma zst_S : forall s t k,
  set_tree_fc (zst s t k) t (arr_set (tree_fc (zst s t k) t) (Z.of_nat k) (wrap16 0)) = zst s t (S k).
Proof.
  intros s t k. unfold zst. rewrite tree_fc_set_tree_fc, set_tree_fc_twice.
  rewrite arr_fill_nat_S. change (wrap16 0) with 0. rewrite Z.add_0_l. reflexivity.
Qed.

Lemma set_static_len_opt_len : forall s a b,
  set_opt_len (set_static_len s a) b = set_static_len (set_opt_len s b) a.
Proof. intros. destruct s; reflexivity. Qed.
Lemma set_matches_sym_next : forall s a b,
  set_sym_next (set_matches s a) b = set_matches (set_sym_next s b) a.
Proof. intros. destruct s; reflexivity. Qed.

Lemma tr_init_eq : forall s,
  tr_init s =
    let s0 := set_bi_valid (set_bi_buf s 0) 0 in
    let s3 := zst (zst (zst s0 TL 286) TD 30) TB 19 in
    set_sym_next (set_matches (set_opt_len (set_static_len
      (set_tree_fc s3 TL (arr_set (tree_fc s3 TL) 256 (wrap16 1))) 0) 0) 0) 0.
Proof.
  intros s. unfold tr_init, init_block, zst, set_Freq. cbv zeta.
  rewrite set_static_len_opt_len, set_matches_sym_next. reflexivity.
Qed.

Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Local Notation PB := (p_pending_buf p).
Definition iVB : bounds := [(32%nat, 2 ^ 63); (33%nat, 600)].


Local Ltac kof o :=
  lazymatch o with
  | 2904 => constr:(37%nat) | 2920 => constr:(39%nat) | 2928 => constr:(40%nat)
  | 2944 => constr:(42%nat) | 2952 => constr:(43%nat) | 2968 => constr:(45%nat)
  | 5936 => constr:(56%nat) | 5940 => constr:(57%nat)
  end.

End Walk.
End RefTrInit_run.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrInit_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCompressBlk1.

Module RefFlushBlk1.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefScanTree_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCompressBlk1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable buf : option Z.
Variable bufp : Z.
Variable len : Z.
Variable last : Z.
Local Notation PB := (p_pending_buf p).
Local Notation SP := (sp - 80).


Lemma scan_tree_pbuf : forall s t mc, ds_pending_buf (scan_tree s t mc) = ds_pending_buf s.
Proof.
  intros s t mc. unfold scan_tree.
  destruct (Len s t 0 =? 0);
    (set (s0 := set_Len s t (mc + 1) 65535);
     match goal with |- ds_pending_buf (scan_tree_loop ?f _ _ _ _ _ ?nl _ ?mx ?mn) = _ =>
       destruct (scan_loop_shape f s0 (ds_bl_tree_fc s0) t mc 0 (-1) nl 0 mx mn) as (b' & E & _) end;
     rewrite sbf_self in E; rewrite E; subst s0; unfold set_Len, set_tree_dl; destruct s; destruct t; reflexivity).
Qed.

End Walk.
End RefFlushBlk1.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk1.

Module RefFlushBlk2.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefScanTree_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrInit_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCompressBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable buf : option Z.
Variable bufp : Z.
Variable len : Z.
Variable last : Z.
Local Notation PB := (p_pending_buf p).
Local Notation SP := (sp - 80).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].




Definition FBF : list (nat * Z) :=
  [(0%nat, 65536); (1%nat, 65536); (2%nat, 573); (3%nat, 256); (4%nat, 65536); (5%nat, 16); (6%nat, 65536)].

Definition VBF : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 32); (35%nat, 2 ^ 64); (36%nat, 2); (37%nat, 2 ^ 63);
   (38%nat, 2 ^ 64); (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64); (42%nat, 2 ^ 64); (43%nat, 2 ^ 64);
   (44%nat, 65536); (45%nat, 17); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64)].

Definition VBF1 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 32); (35%nat, 2 ^ 64); (36%nat, 2); (37%nat, 2 ^ 63);
   (38%nat, 2 ^ 64); (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64); (42%nat, 2 ^ 64); (43%nat, 2 ^ 64);
   (44%nat, 65536); (45%nat, 2 ^ 32); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64)].

Lemma szwrap32_u64_is2 : forall dt, - 2 ^ 31 <= dt < 2 ^ 31 -> (szwrap 32 (dt mod 2 ^ 32) mod 2 ^ 64 = 2 <-> dt = 2).
Proof.
  intros dt Hdt. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. change (2 ^ 31) with 2147483648 in Hdt.
  change (2 ^ 32) with 4294967296. change (2 ^ 64) with 18446744073709551616.
  split; intros H; Z.to_euclidean_division_equations; lia.
Qed.

Local Ltac sideF := try solve [ intros; apply (RefBuildTree5.extra_view_bound' TL) ].

Inductive fkind := FOther | FOpt | FStat | FSymNext | FMatches.

End Walk.
End RefFlushBlk2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk2.

Module RefFlushBlk3.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCompressBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefScanTree_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrInit_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable buf : option Z.
Variable bufp : Z.
Variable len : Z.
Variable last : Z.
Local Notation PB := (p_pending_buf p).
Local Notation SP := (sp - 80).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].
Definition iVBF : bounds := [(32%nat, 2 ^ 63); (33%nat, 600); (34%nat, 2 ^ 63); (35%nat, 2)].

Lemma init_block_eq : forall s,
  init_block s =
    let s3 := zst (zst (zst s TL 286) TD 30) TB 19 in
    set_sym_next (set_matches (set_opt_len (set_static_len
      (set_tree_fc s3 TL (arr_set (tree_fc s3 TL) 256 (wrap16 1))) 0) 0) 0) 0.
Proof.
  intros s. unfold init_block, zst, set_Freq. cbv zeta.
  rewrite set_static_len_opt_len, set_matches_sym_next. reflexivity.
Qed.

End Walk.
End RefFlushBlk3.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk3.

Module RefFlushBlk4.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCompressBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefScanTree_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrInit_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable buf : option Z.
Variable bufp : Z.
Variable len : Z.
Variable last : Z.
Local Notation PB := (p_pending_buf p).
Local Notation SP := (sp - 80).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].
Definition gVBF : bounds := [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 32); (35%nat, 2 ^ 64); (36%nat, 2); (37%nat, 600); (38%nat, 600)].

End Walk.
End RefFlushBlk4.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk4.

Module RefFlushBlk5.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCompressBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefScanTree_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrInit_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable buf : option Z.
Variable bufp : Z.
Variable len : Z.
Variable last : Z.
Local Notation PB := (p_pending_buf p).
Local Notation SP := (sp - 80).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].

End Walk.
End RefFlushBlk5.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.

Module RefFlushBlk6.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCompressBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefScanTree_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrInit_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable buf : option Z.
Variable bufp : Z.
Variable len : Z.
Variable last : Z.
Local Notation PB := (p_pending_buf p).
Local Notation SP := (sp - 80).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].

Local Ltac sideF := try solve [ intros; apply (RefBuildTree5.extra_view_bound' TL) ].


Lemma bbl_step : forall f X mb mb' c, 3 <= mb -> mb' = mb - 1 -> arr_get bl_order_a mb = c ->
  build_bl_tree_loop (Datatypes.S f) X mb = if Len X TB c =? 0 then build_bl_tree_loop f X mb' else mb.
Proof.
  intros f X mb mb' c Hmb -> <-. cbn [build_bl_tree_loop].
  replace (3 <=? mb) with true by (symmetry; apply Z.leb_le; lia).
  destruct (Len X TB (arr_get bl_order_a mb) =? 0); reflexivity.
Qed.

Lemma bbl_two : forall f X, build_bl_tree_loop f X 2 = 2.
Proof. intros [|f] X; reflexivity. Qed.

Lemma ite_t : forall (a b : Z), (if 0 =? 0 then a else b) = a.
Proof. intros. reflexivity. Qed.
Lemma ite_f : forall v (a b : Z), v <> 0 -> (if v =? 0 then a else b) = b.
Proof. intros v a b H. destruct (Z.eqb_spec v 0); [lia | reflexivity]. Qed.

Lemma bls_0 : forall X, Len X TB 15 <> 0 -> build_bl_tree_loop 17%nat X 18 = 18.
Proof.
  intros X  NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_1 : forall X, Len X TB 15 = 0 -> Len X TB 1 <> 0 -> build_bl_tree_loop 17%nat X 18 = 17.
Proof.
  intros X Z0 NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_2 : forall X, Len X TB 15 = 0 -> Len X TB 1 = 0 -> Len X TB 14 <> 0 -> build_bl_tree_loop 17%nat X 18 = 16.
Proof.
  intros X Z0 Z1 NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite Z1, ite_t.
  rewrite (bbl_step 14%nat X 16 15 14) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_3 : forall X, Len X TB 15 = 0 -> Len X TB 1 = 0 -> Len X TB 14 = 0 -> Len X TB 2 <> 0 -> build_bl_tree_loop 17%nat X 18 = 15.
Proof.
  intros X Z0 Z1 Z2 NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite Z1, ite_t.
  rewrite (bbl_step 14%nat X 16 15 14) by (lia || reflexivity). rewrite Z2, ite_t.
  rewrite (bbl_step 13%nat X 15 14 2) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_4 : forall X, Len X TB 15 = 0 -> Len X TB 1 = 0 -> Len X TB 14 = 0 -> Len X TB 2 = 0 -> Len X TB 13 <> 0 -> build_bl_tree_loop 17%nat X 18 = 14.
Proof.
  intros X Z0 Z1 Z2 Z3 NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite Z1, ite_t.
  rewrite (bbl_step 14%nat X 16 15 14) by (lia || reflexivity). rewrite Z2, ite_t.
  rewrite (bbl_step 13%nat X 15 14 2) by (lia || reflexivity). rewrite Z3, ite_t.
  rewrite (bbl_step 12%nat X 14 13 13) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_5 : forall X, Len X TB 15 = 0 -> Len X TB 1 = 0 -> Len X TB 14 = 0 -> Len X TB 2 = 0 -> Len X TB 13 = 0 -> Len X TB 3 <> 0 -> build_bl_tree_loop 17%nat X 18 = 13.
Proof.
  intros X Z0 Z1 Z2 Z3 Z4 NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite Z1, ite_t.
  rewrite (bbl_step 14%nat X 16 15 14) by (lia || reflexivity). rewrite Z2, ite_t.
  rewrite (bbl_step 13%nat X 15 14 2) by (lia || reflexivity). rewrite Z3, ite_t.
  rewrite (bbl_step 12%nat X 14 13 13) by (lia || reflexivity). rewrite Z4, ite_t.
  rewrite (bbl_step 11%nat X 13 12 3) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_6 : forall X, Len X TB 15 = 0 -> Len X TB 1 = 0 -> Len X TB 14 = 0 -> Len X TB 2 = 0 -> Len X TB 13 = 0 -> Len X TB 3 = 0 -> Len X TB 12 <> 0 -> build_bl_tree_loop 17%nat X 18 = 12.
Proof.
  intros X Z0 Z1 Z2 Z3 Z4 Z5 NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite Z1, ite_t.
  rewrite (bbl_step 14%nat X 16 15 14) by (lia || reflexivity). rewrite Z2, ite_t.
  rewrite (bbl_step 13%nat X 15 14 2) by (lia || reflexivity). rewrite Z3, ite_t.
  rewrite (bbl_step 12%nat X 14 13 13) by (lia || reflexivity). rewrite Z4, ite_t.
  rewrite (bbl_step 11%nat X 13 12 3) by (lia || reflexivity). rewrite Z5, ite_t.
  rewrite (bbl_step 10%nat X 12 11 12) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_7 : forall X, Len X TB 15 = 0 -> Len X TB 1 = 0 -> Len X TB 14 = 0 -> Len X TB 2 = 0 -> Len X TB 13 = 0 -> Len X TB 3 = 0 -> Len X TB 12 = 0 -> Len X TB 4 <> 0 -> build_bl_tree_loop 17%nat X 18 = 11.
Proof.
  intros X Z0 Z1 Z2 Z3 Z4 Z5 Z6 NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite Z1, ite_t.
  rewrite (bbl_step 14%nat X 16 15 14) by (lia || reflexivity). rewrite Z2, ite_t.
  rewrite (bbl_step 13%nat X 15 14 2) by (lia || reflexivity). rewrite Z3, ite_t.
  rewrite (bbl_step 12%nat X 14 13 13) by (lia || reflexivity). rewrite Z4, ite_t.
  rewrite (bbl_step 11%nat X 13 12 3) by (lia || reflexivity). rewrite Z5, ite_t.
  rewrite (bbl_step 10%nat X 12 11 12) by (lia || reflexivity). rewrite Z6, ite_t.
  rewrite (bbl_step 9%nat X 11 10 4) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_8 : forall X, Len X TB 15 = 0 -> Len X TB 1 = 0 -> Len X TB 14 = 0 -> Len X TB 2 = 0 -> Len X TB 13 = 0 -> Len X TB 3 = 0 -> Len X TB 12 = 0 -> Len X TB 4 = 0 -> Len X TB 11 <> 0 -> build_bl_tree_loop 17%nat X 18 = 10.
Proof.
  intros X Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7 NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite Z1, ite_t.
  rewrite (bbl_step 14%nat X 16 15 14) by (lia || reflexivity). rewrite Z2, ite_t.
  rewrite (bbl_step 13%nat X 15 14 2) by (lia || reflexivity). rewrite Z3, ite_t.
  rewrite (bbl_step 12%nat X 14 13 13) by (lia || reflexivity). rewrite Z4, ite_t.
  rewrite (bbl_step 11%nat X 13 12 3) by (lia || reflexivity). rewrite Z5, ite_t.
  rewrite (bbl_step 10%nat X 12 11 12) by (lia || reflexivity). rewrite Z6, ite_t.
  rewrite (bbl_step 9%nat X 11 10 4) by (lia || reflexivity). rewrite Z7, ite_t.
  rewrite (bbl_step 8%nat X 10 9 11) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_9 : forall X, Len X TB 15 = 0 -> Len X TB 1 = 0 -> Len X TB 14 = 0 -> Len X TB 2 = 0 -> Len X TB 13 = 0 -> Len X TB 3 = 0 -> Len X TB 12 = 0 -> Len X TB 4 = 0 -> Len X TB 11 = 0 -> Len X TB 5 <> 0 -> build_bl_tree_loop 17%nat X 18 = 9.
Proof.
  intros X Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite Z1, ite_t.
  rewrite (bbl_step 14%nat X 16 15 14) by (lia || reflexivity). rewrite Z2, ite_t.
  rewrite (bbl_step 13%nat X 15 14 2) by (lia || reflexivity). rewrite Z3, ite_t.
  rewrite (bbl_step 12%nat X 14 13 13) by (lia || reflexivity). rewrite Z4, ite_t.
  rewrite (bbl_step 11%nat X 13 12 3) by (lia || reflexivity). rewrite Z5, ite_t.
  rewrite (bbl_step 10%nat X 12 11 12) by (lia || reflexivity). rewrite Z6, ite_t.
  rewrite (bbl_step 9%nat X 11 10 4) by (lia || reflexivity). rewrite Z7, ite_t.
  rewrite (bbl_step 8%nat X 10 9 11) by (lia || reflexivity). rewrite Z8, ite_t.
  rewrite (bbl_step 7%nat X 9 8 5) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_10 : forall X, Len X TB 15 = 0 -> Len X TB 1 = 0 -> Len X TB 14 = 0 -> Len X TB 2 = 0 -> Len X TB 13 = 0 -> Len X TB 3 = 0 -> Len X TB 12 = 0 -> Len X TB 4 = 0 -> Len X TB 11 = 0 -> Len X TB 5 = 0 -> Len X TB 10 <> 0 -> build_bl_tree_loop 17%nat X 18 = 8.
Proof.
  intros X Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite Z1, ite_t.
  rewrite (bbl_step 14%nat X 16 15 14) by (lia || reflexivity). rewrite Z2, ite_t.
  rewrite (bbl_step 13%nat X 15 14 2) by (lia || reflexivity). rewrite Z3, ite_t.
  rewrite (bbl_step 12%nat X 14 13 13) by (lia || reflexivity). rewrite Z4, ite_t.
  rewrite (bbl_step 11%nat X 13 12 3) by (lia || reflexivity). rewrite Z5, ite_t.
  rewrite (bbl_step 10%nat X 12 11 12) by (lia || reflexivity). rewrite Z6, ite_t.
  rewrite (bbl_step 9%nat X 11 10 4) by (lia || reflexivity). rewrite Z7, ite_t.
  rewrite (bbl_step 8%nat X 10 9 11) by (lia || reflexivity). rewrite Z8, ite_t.
  rewrite (bbl_step 7%nat X 9 8 5) by (lia || reflexivity). rewrite Z9, ite_t.
  rewrite (bbl_step 6%nat X 8 7 10) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_11 : forall X, Len X TB 15 = 0 -> Len X TB 1 = 0 -> Len X TB 14 = 0 -> Len X TB 2 = 0 -> Len X TB 13 = 0 -> Len X TB 3 = 0 -> Len X TB 12 = 0 -> Len X TB 4 = 0 -> Len X TB 11 = 0 -> Len X TB 5 = 0 -> Len X TB 10 = 0 -> Len X TB 6 <> 0 -> build_bl_tree_loop 17%nat X 18 = 7.
Proof.
  intros X Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite Z1, ite_t.
  rewrite (bbl_step 14%nat X 16 15 14) by (lia || reflexivity). rewrite Z2, ite_t.
  rewrite (bbl_step 13%nat X 15 14 2) by (lia || reflexivity). rewrite Z3, ite_t.
  rewrite (bbl_step 12%nat X 14 13 13) by (lia || reflexivity). rewrite Z4, ite_t.
  rewrite (bbl_step 11%nat X 13 12 3) by (lia || reflexivity). rewrite Z5, ite_t.
  rewrite (bbl_step 10%nat X 12 11 12) by (lia || reflexivity). rewrite Z6, ite_t.
  rewrite (bbl_step 9%nat X 11 10 4) by (lia || reflexivity). rewrite Z7, ite_t.
  rewrite (bbl_step 8%nat X 10 9 11) by (lia || reflexivity). rewrite Z8, ite_t.
  rewrite (bbl_step 7%nat X 9 8 5) by (lia || reflexivity). rewrite Z9, ite_t.
  rewrite (bbl_step 6%nat X 8 7 10) by (lia || reflexivity). rewrite Z10, ite_t.
  rewrite (bbl_step 5%nat X 7 6 6) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_12 : forall X, Len X TB 15 = 0 -> Len X TB 1 = 0 -> Len X TB 14 = 0 -> Len X TB 2 = 0 -> Len X TB 13 = 0 -> Len X TB 3 = 0 -> Len X TB 12 = 0 -> Len X TB 4 = 0 -> Len X TB 11 = 0 -> Len X TB 5 = 0 -> Len X TB 10 = 0 -> Len X TB 6 = 0 -> Len X TB 9 <> 0 -> build_bl_tree_loop 17%nat X 18 = 6.
Proof.
  intros X Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite Z1, ite_t.
  rewrite (bbl_step 14%nat X 16 15 14) by (lia || reflexivity). rewrite Z2, ite_t.
  rewrite (bbl_step 13%nat X 15 14 2) by (lia || reflexivity). rewrite Z3, ite_t.
  rewrite (bbl_step 12%nat X 14 13 13) by (lia || reflexivity). rewrite Z4, ite_t.
  rewrite (bbl_step 11%nat X 13 12 3) by (lia || reflexivity). rewrite Z5, ite_t.
  rewrite (bbl_step 10%nat X 12 11 12) by (lia || reflexivity). rewrite Z6, ite_t.
  rewrite (bbl_step 9%nat X 11 10 4) by (lia || reflexivity). rewrite Z7, ite_t.
  rewrite (bbl_step 8%nat X 10 9 11) by (lia || reflexivity). rewrite Z8, ite_t.
  rewrite (bbl_step 7%nat X 9 8 5) by (lia || reflexivity). rewrite Z9, ite_t.
  rewrite (bbl_step 6%nat X 8 7 10) by (lia || reflexivity). rewrite Z10, ite_t.
  rewrite (bbl_step 5%nat X 7 6 6) by (lia || reflexivity). rewrite Z11, ite_t.
  rewrite (bbl_step 4%nat X 6 5 9) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_13 : forall X, Len X TB 15 = 0 -> Len X TB 1 = 0 -> Len X TB 14 = 0 -> Len X TB 2 = 0 -> Len X TB 13 = 0 -> Len X TB 3 = 0 -> Len X TB 12 = 0 -> Len X TB 4 = 0 -> Len X TB 11 = 0 -> Len X TB 5 = 0 -> Len X TB 10 = 0 -> Len X TB 6 = 0 -> Len X TB 9 = 0 -> Len X TB 7 <> 0 -> build_bl_tree_loop 17%nat X 18 = 5.
Proof.
  intros X Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite Z1, ite_t.
  rewrite (bbl_step 14%nat X 16 15 14) by (lia || reflexivity). rewrite Z2, ite_t.
  rewrite (bbl_step 13%nat X 15 14 2) by (lia || reflexivity). rewrite Z3, ite_t.
  rewrite (bbl_step 12%nat X 14 13 13) by (lia || reflexivity). rewrite Z4, ite_t.
  rewrite (bbl_step 11%nat X 13 12 3) by (lia || reflexivity). rewrite Z5, ite_t.
  rewrite (bbl_step 10%nat X 12 11 12) by (lia || reflexivity). rewrite Z6, ite_t.
  rewrite (bbl_step 9%nat X 11 10 4) by (lia || reflexivity). rewrite Z7, ite_t.
  rewrite (bbl_step 8%nat X 10 9 11) by (lia || reflexivity). rewrite Z8, ite_t.
  rewrite (bbl_step 7%nat X 9 8 5) by (lia || reflexivity). rewrite Z9, ite_t.
  rewrite (bbl_step 6%nat X 8 7 10) by (lia || reflexivity). rewrite Z10, ite_t.
  rewrite (bbl_step 5%nat X 7 6 6) by (lia || reflexivity). rewrite Z11, ite_t.
  rewrite (bbl_step 4%nat X 6 5 9) by (lia || reflexivity). rewrite Z12, ite_t.
  rewrite (bbl_step 3%nat X 5 4 7) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_14 : forall X, Len X TB 15 = 0 -> Len X TB 1 = 0 -> Len X TB 14 = 0 -> Len X TB 2 = 0 -> Len X TB 13 = 0 -> Len X TB 3 = 0 -> Len X TB 12 = 0 -> Len X TB 4 = 0 -> Len X TB 11 = 0 -> Len X TB 5 = 0 -> Len X TB 10 = 0 -> Len X TB 6 = 0 -> Len X TB 9 = 0 -> Len X TB 7 = 0 -> Len X TB 8 <> 0 -> build_bl_tree_loop 17%nat X 18 = 4.
Proof.
  intros X Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite Z1, ite_t.
  rewrite (bbl_step 14%nat X 16 15 14) by (lia || reflexivity). rewrite Z2, ite_t.
  rewrite (bbl_step 13%nat X 15 14 2) by (lia || reflexivity). rewrite Z3, ite_t.
  rewrite (bbl_step 12%nat X 14 13 13) by (lia || reflexivity). rewrite Z4, ite_t.
  rewrite (bbl_step 11%nat X 13 12 3) by (lia || reflexivity). rewrite Z5, ite_t.
  rewrite (bbl_step 10%nat X 12 11 12) by (lia || reflexivity). rewrite Z6, ite_t.
  rewrite (bbl_step 9%nat X 11 10 4) by (lia || reflexivity). rewrite Z7, ite_t.
  rewrite (bbl_step 8%nat X 10 9 11) by (lia || reflexivity). rewrite Z8, ite_t.
  rewrite (bbl_step 7%nat X 9 8 5) by (lia || reflexivity). rewrite Z9, ite_t.
  rewrite (bbl_step 6%nat X 8 7 10) by (lia || reflexivity). rewrite Z10, ite_t.
  rewrite (bbl_step 5%nat X 7 6 6) by (lia || reflexivity). rewrite Z11, ite_t.
  rewrite (bbl_step 4%nat X 6 5 9) by (lia || reflexivity). rewrite Z12, ite_t.
  rewrite (bbl_step 3%nat X 5 4 7) by (lia || reflexivity). rewrite Z13, ite_t.
  rewrite (bbl_step 2%nat X 4 3 8) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_15 : forall X, Len X TB 15 = 0 -> Len X TB 1 = 0 -> Len X TB 14 = 0 -> Len X TB 2 = 0 -> Len X TB 13 = 0 -> Len X TB 3 = 0 -> Len X TB 12 = 0 -> Len X TB 4 = 0 -> Len X TB 11 = 0 -> Len X TB 5 = 0 -> Len X TB 10 = 0 -> Len X TB 6 = 0 -> Len X TB 9 = 0 -> Len X TB 7 = 0 -> Len X TB 8 = 0 -> Len X TB 0 <> 0 -> build_bl_tree_loop 17%nat X 18 = 3.
Proof.
  intros X Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 NZ.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite Z1, ite_t.
  rewrite (bbl_step 14%nat X 16 15 14) by (lia || reflexivity). rewrite Z2, ite_t.
  rewrite (bbl_step 13%nat X 15 14 2) by (lia || reflexivity). rewrite Z3, ite_t.
  rewrite (bbl_step 12%nat X 14 13 13) by (lia || reflexivity). rewrite Z4, ite_t.
  rewrite (bbl_step 11%nat X 13 12 3) by (lia || reflexivity). rewrite Z5, ite_t.
  rewrite (bbl_step 10%nat X 12 11 12) by (lia || reflexivity). rewrite Z6, ite_t.
  rewrite (bbl_step 9%nat X 11 10 4) by (lia || reflexivity). rewrite Z7, ite_t.
  rewrite (bbl_step 8%nat X 10 9 11) by (lia || reflexivity). rewrite Z8, ite_t.
  rewrite (bbl_step 7%nat X 9 8 5) by (lia || reflexivity). rewrite Z9, ite_t.
  rewrite (bbl_step 6%nat X 8 7 10) by (lia || reflexivity). rewrite Z10, ite_t.
  rewrite (bbl_step 5%nat X 7 6 6) by (lia || reflexivity). rewrite Z11, ite_t.
  rewrite (bbl_step 4%nat X 6 5 9) by (lia || reflexivity). rewrite Z12, ite_t.
  rewrite (bbl_step 3%nat X 5 4 7) by (lia || reflexivity). rewrite Z13, ite_t.
  rewrite (bbl_step 2%nat X 4 3 8) by (lia || reflexivity). rewrite Z14, ite_t.
  rewrite (bbl_step 1%nat X 3 2 0) by (lia || reflexivity). rewrite (ite_f _ _ _ NZ). reflexivity.
Qed.

Lemma bls_16 : forall X, Len X TB 15 = 0 -> Len X TB 1 = 0 -> Len X TB 14 = 0 -> Len X TB 2 = 0 -> Len X TB 13 = 0 -> Len X TB 3 = 0 -> Len X TB 12 = 0 -> Len X TB 4 = 0 -> Len X TB 11 = 0 -> Len X TB 5 = 0 -> Len X TB 10 = 0 -> Len X TB 6 = 0 -> Len X TB 9 = 0 -> Len X TB 7 = 0 -> Len X TB 8 = 0 -> Len X TB 0 = 0 -> build_bl_tree_loop 17%nat X 18 = 2.
Proof.
  intros X Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15.
  rewrite (bbl_step 16%nat X 18 17 15) by (lia || reflexivity). rewrite Z0, ite_t.
  rewrite (bbl_step 15%nat X 17 16 1) by (lia || reflexivity). rewrite Z1, ite_t.
  rewrite (bbl_step 14%nat X 16 15 14) by (lia || reflexivity). rewrite Z2, ite_t.
  rewrite (bbl_step 13%nat X 15 14 2) by (lia || reflexivity). rewrite Z3, ite_t.
  rewrite (bbl_step 12%nat X 14 13 13) by (lia || reflexivity). rewrite Z4, ite_t.
  rewrite (bbl_step 11%nat X 13 12 3) by (lia || reflexivity). rewrite Z5, ite_t.
  rewrite (bbl_step 10%nat X 12 11 12) by (lia || reflexivity). rewrite Z6, ite_t.
  rewrite (bbl_step 9%nat X 11 10 4) by (lia || reflexivity). rewrite Z7, ite_t.
  rewrite (bbl_step 8%nat X 10 9 11) by (lia || reflexivity). rewrite Z8, ite_t.
  rewrite (bbl_step 7%nat X 9 8 5) by (lia || reflexivity). rewrite Z9, ite_t.
  rewrite (bbl_step 6%nat X 8 7 10) by (lia || reflexivity). rewrite Z10, ite_t.
  rewrite (bbl_step 5%nat X 7 6 6) by (lia || reflexivity). rewrite Z11, ite_t.
  rewrite (bbl_step 4%nat X 6 5 9) by (lia || reflexivity). rewrite Z12, ite_t.
  rewrite (bbl_step 3%nat X 5 4 7) by (lia || reflexivity). rewrite Z13, ite_t.
  rewrite (bbl_step 2%nat X 4 3 8) by (lia || reflexivity). rewrite Z14, ite_t.
  rewrite (bbl_step 1%nat X 3 2 0) by (lia || reflexivity). rewrite Z15, ite_t.
  apply bbl_two.
Qed.


Lemma pb_Len : forall X c, 0 <= arr_get (ds_bl_tree_dl X) c < 65536 -> pb (ds_bl_tree_dl X) c = Len X TB c.
Proof. intros X c H. unfold pb, Len, tree_dl. apply Z.mod_small. exact H. Qed.

End Walk.
End RefFlushBlk6.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk6.

Module RefFlushBlk7.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCompressBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefScanTree_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrInit_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable buf : option Z.
Variable bufp : Z.
Variable len : Z.
Variable last : Z.
Local Notation PB := (p_pending_buf p).
Local Notation SP := (sp - 80).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].

Local Ltac sideF := try solve [ intros; apply (RefBuildTree5.extra_view_bound' TL) ].


Definition p4_dec (OL SL strat mb bufpv : Z) : Z :=
  let olb := (3 * mb + OL + 27) / 2 ^ 3 in
  let slb := (SL + 10) / 2 ^ 3 in
  if (slb <=? olb) || (strat =? 4)
  then (if slb <? len + 4 then 0 else if bufpv =? 0 then 0 else 2)
  else (if olb <? len + 4 then 1 else if bufpv =? 0 then 1 else 2).

Definition VB7 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 32); (35%nat, 2 ^ 64); (36%nat, 2);
   (37%nat, 2 ^ 63); (38%nat, 2 ^ 63); (39%nat, 2 ^ 64); (40%nat, 19); (41%nat, 5)].

Lemma set_opt_len_congr : forall X a b, a = b -> set_opt_len X a = set_opt_len X b.
Proof. intros X a b ->. reflexivity. Qed.

End Walk.
End RefFlushBlk7.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk7.

Module RefFlushBlk8.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCompressBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefScanTree_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrInit_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable buf : option Z.
Variable bufp : Z.
Variable len : Z.
Variable last : Z.
Local Notation PB := (p_pending_buf p).
Local Notation SP := (sp - 80).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].

Local Ltac sideF := try solve [ intros; apply (RefBuildTree5.extra_view_bound' TL) ].

Local Ltac vcongr := first [ reflexivity | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite Z.mod_mod by lia; apply szwrap32_mod16
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; apply mod16_congr; lia ].
Local Ltac vwrap := first [ reflexivity | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | apply wrap16_id'; lia
                          | rewrite wrap16_mod', ?Z.mod_mod by lia; rewrite ?szwrap32_mod16; apply mod16_congr; lia ].
Local Ltac vrange := first [ lia | apply Z.mod_pos_bound; lia ].

End Walk.
End RefFlushBlk8.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk8.

Module RefFlushBlk9.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCompressBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefScanTree_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrInit_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable buf : option Z.
Variable bufp : Z.
Variable len : Z.
Variable last : Z.
Local Notation PB := (p_pending_buf p).
Local Notation SP := (sp - 80).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].

Local Ltac sideF := try solve [ intros; apply (RefBuildTree5.extra_view_bound' TL) ].

Local Ltac vcongr := first [ reflexivity | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite Z.mod_mod by lia; apply szwrap32_mod16
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; apply mod16_congr; lia ].
Local Ltac vwrap := first [ reflexivity | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | apply wrap16_id'; lia
                          | rewrite wrap16_mod', ?Z.mod_mod by lia; rewrite ?szwrap32_mod16; apply mod16_congr; lia ].
Local Ltac vrange := first [ lia | apply Z.mod_pos_bound; lia ].

Definition VB9 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 32); (35%nat, 2 ^ 64); (36%nat, 2); (37%nat, 2 ^ 63);
   (38%nat, 19); (39%nat, 19); (40%nat, 19); (41%nat, 600); (42%nat, 600); (43%nat, 2 ^ 64);
   (44%nat, 65536); (45%nat, 17); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64)].

Local Ltac dk H := destruct H as (K18 & K8 & K9 & K2 & K13 & K10).
Local Ltac dr H := destruct H as ((K18 & K8 & K9 & K2 & K13 & K10) & K14 & KRB & K15).

End Walk.
End RefFlushBlk9.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk9.

Module RefFlushBlk10.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefScanTree_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrInit_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCompressBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk8.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable buf : option Z.
Variable bufp : Z.
Variable len : Z.
Variable last : Z.
Local Notation PB := (p_pending_buf p).
Local Notation SP := (sp - 80).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].

Local Ltac sideF := try solve [ intros; apply (RefBuildTree5.extra_view_bound' TL) ].

Local Ltac vcongr := first [ reflexivity | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite Z.mod_mod by lia; apply szwrap32_mod16
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; apply mod16_congr; lia ].
Local Ltac vwrap := first [ reflexivity | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | apply wrap16_id'; lia
                          | rewrite wrap16_mod', ?Z.mod_mod by lia; rewrite ?szwrap32_mod16; apply mod16_congr; lia ].
Local Ltac vrange := first [ lia | apply Z.mod_pos_bound; lia ].


Local Ltac dr H := destruct H as ((K18 & K8 & K9 & K2 & K13 & K10) & K14 & KRB & K15).

End Walk.
End RefFlushBlk10.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk10.

Module RefFlushBlk11.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCompressBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefScanTree_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrInit_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable buf : option Z.
Variable bufp : Z.
Variable len : Z.
Variable last : Z.
Local Notation PB := (p_pending_buf p).
Local Notation SP := (sp - 80).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].

Local Ltac sideF := try solve [ intros; apply (RefBuildTree5.extra_view_bound' TL) ].

Local Ltac vcongr := first [ reflexivity | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite Z.mod_mod by lia; apply szwrap32_mod16
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; apply mod16_congr; lia ].
Local Ltac vwrap := first [ reflexivity | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | apply wrap16_id'; lia
                          | rewrite wrap16_mod', ?Z.mod_mod by lia; rewrite ?szwrap32_mod16; apply mod16_congr; lia ].
Local Ltac vrange := first [ lia | apply Z.mod_pos_bound; lia ].

Definition VBD : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 32); (35%nat, 2 ^ 64); (36%nat, 2);
   (37%nat, 2 ^ 63); (38%nat, 600); (39%nat, 2 ^ 32); (40%nat, 2 ^ 32)].

Local Ltac ddk H := destruct H as ((K18 & K16 & K17 & K6 & K13 & K2) & K8 & K10).

Definition l1_exit (X : deflate_state) (n mk : Z) : bool :=
  negb (Z.land mk 1 =? 0) && negb (Freq X TL n =? 0).


Definition M0 : Z := 4093624447.

Lemma detect_loop1_some : forall f X n mk r, detect_loop1 f X n mk = Some r -> r = Z_BINARY.
Proof.
  induction f as [|f IH]; intros X n mk r H; cbn [detect_loop1] in H; [discriminate|].
  destruct (n <=? 31); [|discriminate].
  destruct (negb (Z.land mk 1 =? 0) && negb (Freq X TL n =? 0)); [congruence|]. exact (IH _ _ _ _ H).
Qed.

Lemma detect_loop2_range : forall f X n,
  0 <= match detect_loop2 f X n with Some r => r | None => Z_BINARY end < 2 ^ 32.
Proof.
  induction f as [|f IH]; intros X n; cbn [detect_loop2]; [unfold Z_BINARY; lia|].
  destruct (n <? LITERALS); [|unfold Z_BINARY; lia].
  destruct (negb (Freq X TL n =? 0)); [unfold Z_TEXT; lia | apply IH].
Qed.

Lemma shiftr_M0_range : forall n, 0 <= n -> 0 <= Z.shiftr M0 n < 2 ^ 32.
Proof.
  intros n Hn. unfold M0. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma shiftr_M0_step : forall n, 0 <= n -> Z.shiftr M0 n / 2 ^ 1 = Z.shiftr M0 (n + 1).
Proof.
  intros n Hn. rewrite <- Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_shiftr by lia. reflexivity.
Qed.

Definition d1_text (X : deflate_state) : bool :=
  negb (Freq X TL 9 =? 0) || negb (Freq X TL 10 =? 0) || negb (Freq X TL 13 =? 0).

End Walk.
End RefFlushBlk11.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk11.

Module RefFlushBlk12.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefBuildTree9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefScanTree_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrInit_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCompressBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk8.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk10.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk11.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable buf : option Z.
Variable bufp : Z.
Variable len : Z.
Variable last : Z.
Local Notation PB := (p_pending_buf p).
Local Notation SP := (sp - 80).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].

Local Ltac sideF := try solve [ intros; apply (RefBuildTree5.extra_view_bound' TL) ].

Local Ltac vcongr := first [ reflexivity | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite Z.mod_mod by lia; apply szwrap32_mod16
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; apply mod16_congr; lia ].
Local Ltac vwrap := first [ reflexivity | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | apply wrap16_id'; lia
                          | rewrite wrap16_mod', ?Z.mod_mod by lia; rewrite ?szwrap32_mod16; apply mod16_congr; lia ].
Local Ltac vrange := first [ lia | apply Z.mod_pos_bound; lia ].


Definition hd_calls (X : deflate_state) (mb : Z) : list (Z * Z) :=
  (4 + last, 3) :: (ds_l_max_code X - 256, 5) :: (ds_d_max_code X, 5) :: (mb - 3, 4) :: bl_calls X 0 (Z.to_nat (mb + 1)).

Definition dyn_ok (X6 : deflate_state) (mb : Z) : Prop :=
  let lmax := ds_l_max_code X6 in
  let dmax := ds_d_max_code X6 in
  let X11 := sbs_run X6 (hd_calls X6 mb) in
  let X12 := send_tree X11 TL lmax in
  let X13 := send_tree X12 TD dmax in
  BINV PBL X6 /\ sbs_ok PBL X6 (hd_calls X6 mb)
  /\ (0 <= lmax /\ lmax + 1 < 573) /\ (0 <= dmax /\ dmax + 1 < 61)
  /\ ((forall i, 0 <= i < 19 -> 0 <= arr_get (ds_bl_tree_dl X6) i < 16)
      /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X6) i < 65536))
  /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X6) i < 65536)
  /\ (forall i, 0 <= i <= lmax -> 0 <= Len X6 TL i <= 15)
  /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_dl X6) i < 65536)
  /\ (forall i, 0 <= i <= dmax -> 0 <= Len X6 TD i <= 15)
  /\ (forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_dl X6) i < 65536)
  /\ RefSendTree4.send_tree_safe PBL X11 TL lmax
  /\ RefSendTree4.send_tree_safe PBL X12 TD dmax
  /\ compress_block_ok PBL X13 (ds_dyn_ltree_fc X6) (ds_dyn_ltree_dl X6) (ds_dyn_dtree_fc X6) (ds_dyn_dtree_dl X6)
  /\ (forall i, 0 <= i < 286 -> 0 <= arr_get (ds_dyn_ltree_fc X6) i < 65536)
  /\ (forall i, 0 <= i < 30 -> 0 <= arr_get (ds_dyn_dtree_fc X6) i < 65536)
  /\ RefCompressBlk1.compress_lens_ok X13 (ds_dyn_ltree_fc X6) (ds_dyn_ltree_dl X6) (ds_dyn_dtree_fc X6) (ds_dyn_dtree_dl X6)
  /\ (0 <= ds_sym_next X6 /\ ds_sym_next X6 + 3 < 2 ^ 31) /\ 0 <= ds_lit_bufsize X6 < 2 ^ 32.

Lemma trees8_facts : forall X X', trees8 X' = trees8 X ->
  ds_dyn_ltree_fc X' = ds_dyn_ltree_fc X /\ ds_dyn_ltree_dl X' = ds_dyn_ltree_dl X
  /\ ds_dyn_dtree_fc X' = ds_dyn_dtree_fc X /\ ds_dyn_dtree_dl X' = ds_dyn_dtree_dl X
  /\ ds_bl_tree_fc X' = ds_bl_tree_fc X /\ ds_bl_tree_dl X' = ds_bl_tree_dl X
  /\ ds_l_max_code X' = ds_l_max_code X /\ ds_d_max_code X' = ds_d_max_code X.
Proof. intros X X' E. unfold trees8 in E. injection E. intros. repeat split; assumption. Qed.

Lemma Len_trees8 : forall X X' t i, trees8 X' = trees8 X -> Len X' t i = Len X t i.
Proof.
  intros X X' t i E. destruct (trees8_facts X X' E) as (A1 & A2 & A3 & A4 & A5 & A6 & _).
  unfold Len, tree_dl. destruct t; congruence.
Qed.

End Walk.
End RefFlushBlk12.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable buf : option Z.
Variable bufp : Z.
Variable len : Z.
Variable last : Z.
Local Notation PB := (p_pending_buf p).
Local Notation SP := (sp - 80).

Local Ltac nf := cbn [OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.stF].

Local Ltac sideF := try solve [ intros; apply (RefBuildTree5.extra_view_bound' TL) ].

Local Ltac vcongr := first [ reflexivity | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite Z.mod_mod by lia; apply szwrap32_mod16
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; apply mod16_congr; lia ].
Local Ltac vwrap := first [ reflexivity | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | apply wrap16_id'; lia
                          | rewrite wrap16_mod', ?Z.mod_mod by lia; rewrite ?szwrap32_mod16; apply mod16_congr; lia ].
Local Ltac vrange := first [ lia | apply Z.mod_pos_bound; lia ].


Definition stat_ok (PBL' last' : Z) (X : deflate_state) : Prop :=
  sb_room PBL' X 3
  /\ compress_block_ok PBL' (send_bits X (2 + last') 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl
  /\ (0 <= ds_sym_next X /\ ds_sym_next X + 3 < 2 ^ 31) /\ 0 <= ds_lit_bufsize X < 2 ^ 32.

Definition sto_ok (PBL' : Z) (X : deflate_state) (buf' : option Z) (len' last' : Z) : Prop :=
  ds_pending (tr_stored_block X buf' len' last') <= PBL' /\ (len' <> 0 -> buf' <> None).

Definition post_ok (PBL' last' : Z) (Y : deflate_state) : Prop :=
  BINV PBL' Y /\ (last' <> 0 -> ds_pending (bi_windup (init_block Y)) <= PBL').

Definition hi_ok (PBL' : Z) (ds' : deflate_state) (buf' : option Z) (len' last' : Z) : Prop :=
  let X0 := tfb_X0 ds' in
  let X1 := build_tree X0 TL in
  let X2 := build_tree X1 TD in
  let mcl := ds_l_max_code X2 in
  let X3 := scan_tree X2 TL mcl in
  let mcd := ds_d_max_code X3 in
  let X4 := scan_tree X3 TD mcd in
  let X5 := build_tree X4 TB in
  let mb := tfb_mb X5 in
  let X6 := tfb_X6 X5 mb in
  bt_safe X0 TL /\ bt_safe X1 TD
  /\ (0 <= mcl /\ mcl + 1 < 573) /\ (forall i, 0 <= i <= mcl -> 0 <= Len X2 TL i <= 15)
  /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (tree_dl X2 TL) i < 65536)
  /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X2) i < 65536)
  /\ (0 <= mcd /\ mcd + 1 < 61) /\ (forall i, 0 <= i <= mcd -> 0 <= Len X3 TD i <= 15)
  /\ (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X3 TD) i < 65536)
  /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X3) i < 65536)
  /\ bt_safe X4 TB
  /\ ((forall i, 0 <= i < 19 -> 0 <= arr_get (ds_bl_tree_dl X5) i < 16)
      /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X5) i < 65536))
  /\ 0 <= ds_opt_len X5 < 2 ^ 63 /\ 0 <= ds_static_len X5 < 2 ^ 63 /\ 0 <= ds_strategy X5 <= 4
  /\ match tfb_branch X6 buf' len' with
     | 0 => stat_ok PBL' last' X6
     | 1 => RefFlushBlk12.dyn_ok PBL' last' X6 mb
     | _ => sto_ok PBL' X6 buf' len' last'
     end.

Definition lo_ok (PBL' : Z) (ds' : deflate_state) (buf' : option Z) (len' last' : Z) : Prop :=
  match buf' with None => stat_ok PBL' last' ds' | Some _ => sto_ok PBL' ds' buf' len' last' end.

Definition fb_safe (ds' : deflate_state) (buf' : option Z) (len' last' : Z) : Prop :=
  let PBL' := arr_len (ds_pending_buf ds') in
  0 <= ds_level ds' < 100 /\ - 2 ^ 31 <= cs_data_type (ds_strm ds') < 2 ^ 31 /\ 0 < PBL'
  /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc ds') i < 65536)
  /\ post_ok PBL' last' (tfb_pre ds' buf' len' last')
  /\ (if 0 <? ds_level ds' then hi_ok PBL' ds' buf' len' last' else lo_ok PBL' ds' buf' len' last').


Lemma ds_opt_len_set_opt_len : forall s v, ds_opt_len (set_opt_len s v) = v.
Proof. intros s v; destruct s; reflexivity. Qed.
Lemma ds_static_len_set_opt_len : forall s v, ds_static_len (set_opt_len s v) = ds_static_len s.
Proof. intros s v; destruct s; reflexivity. Qed.
Lemma ds_strategy_set_opt_len : forall s v, ds_strategy (set_opt_len s v) = ds_strategy s.
Proof. intros s v; destruct s; reflexivity. Qed.

Lemma cs_data_type_cset : forall c v, cs_data_type (cset_data_type c v) = v.
Proof. intros c v. destruct c; reflexivity. Qed.

Lemma tree_fc_TL : forall s, tree_fc s TL = ds_dyn_ltree_fc s. Proof. reflexivity. Qed.
Lemma tree_dl_TL : forall s, tree_dl s TL = ds_dyn_ltree_dl s. Proof. reflexivity. Qed.
Lemma tree_fc_TD : forall s, tree_fc s TD = ds_dyn_dtree_fc s. Proof. reflexivity. Qed.
Lemma tree_dl_TD : forall s, tree_dl s TD = ds_dyn_dtree_dl s. Proof. reflexivity. Qed.

Lemma tfb_emit_1 : forall X mb,
  0 <= mb <= 18 ->
  let X11 := sbs_run X (RefFlushBlk12.hd_calls last X mb) in
  let X13 := send_tree (send_tree X11 TL (ds_l_max_code X)) TD (ds_d_max_code X) in
  tfb_emit 1 X mb buf len last =
    compress_block X13 (ds_dyn_ltree_fc X13) (ds_dyn_ltree_dl X13) (ds_dyn_dtree_fc X13) (ds_dyn_dtree_dl X13).
Proof.
  intros X mb Hmb X11 X13. unfold tfb_emit. cbn [Z.eqb Pos.eqb]. change (Z.shiftl DYN_TREES 1) with 4.
  rewrite send_all_trees_eq by lia.
  destruct (trees8_facts X (send_bits X (4 + last) 3) (trees8_send_bits X (4 + last) 3)) as (_ & _ & _ & _ & _ & _ & -> & ->).
  replace (ds_l_max_code X + 1 - 1) with (ds_l_max_code X) by lia. replace (ds_d_max_code X + 1 - 1) with (ds_d_max_code X) by lia.
  assert (E11 : sbs_run (send_bits X (4 + last) 3) (sat_calls (send_bits X (4 + last) 3) (ds_l_max_code X + 1) (ds_d_max_code X + 1) (mb + 1)) = X11).
  { subst X11. unfold sat_calls, RefFlushBlk12.hd_calls. cbn [sbs_run app].
    replace (ds_l_max_code X + 1 - 257) with (ds_l_max_code X - 256) by lia.
    replace (ds_d_max_code X + 1 - 1) with (ds_d_max_code X) by lia.
    replace (mb + 1 - 4) with (mb - 3) by lia.
    rewrite (bl_calls_ext X (send_bits X (4 + last) 3)) by (intros; apply sb_Len). reflexivity. }
  rewrite E11. reflexivity.
Qed.

Lemma bits4_X6 : forall X0,
  bits4 (tfb_X6 (tfb_X5 X0) (tfb_mb (tfb_X5 X0))) = bits4 X0.
Proof.
  intros X0. unfold tfb_X6, tfb_X5. cbv zeta. rewrite bits4_set_opt_len.
  rewrite !(k_build_tree _ _ _ keeps_bits4), !(k_scan_tree _ _ _ keeps_bits4), !(k_build_tree _ _ _ keeps_bits4). reflexivity.
Qed.

Lemma bits4_X6' : bits4 (tfb_X6 (tfb_X5 (tfb_X0 ds)) (tfb_mb (tfb_X5 (tfb_X0 ds)))) = bits4 ds.
Proof.
  rewrite bits4_X6. unfold tfb_X0. destruct (_ && _); [apply bits4_set_strm | reflexivity].
Qed.

Lemma window_X6 : ds_window (tfb_X6 (tfb_X5 (tfb_X0 ds)) (tfb_mb (tfb_X5 (tfb_X0 ds)))) = ds_window ds.
Proof.
  unfold tfb_X6, tfb_X5. cbv zeta. rewrite (k_opt_len _ _ _ keeps_window).
  rewrite !(k_build_tree _ _ _ keeps_window), !(k_scan_tree _ _ _ keeps_window), !(k_build_tree _ _ _ keeps_window).
  unfold tfb_X0. destruct (_ && _); [apply set_strm_window | reflexivity].
Qed.


Lemma p4_dec_range : forall OL SL st mb bufpv,
  RefFlushBlk7.p4_dec len OL SL st mb bufpv = 0 \/ RefFlushBlk7.p4_dec len OL SL st mb bufpv = 1 \/ RefFlushBlk7.p4_dec len OL SL st mb bufpv = 2.
Proof.
  intros. unfold RefFlushBlk7.p4_dec. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

End Walk.

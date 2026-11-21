(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import BuildTreeRod.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefBitsLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefPqdown_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefGenCodes_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefBuildTree1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefBuildTree2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefBuildTree3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefBuildTree4.
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
Local Notation stree_dl := (RefBuildTree1.stree_dl t).
Local Notation stF := (RefBuildTree1.stF t).
Local Notation X0 := (RefBuildTree1.X0 ds t).
Local Notation L1 := (RefBuildTree1.L1 t).
Local Notation tsize_elems := (RefBuildTree1.tsize_elems t).
Local Notation elems_range := (RefBuildTree1.elems_range t).
Local Notation dsc_off_val := (RefBuildTree1.dsc_off_val t).
Local Notation SDA_range := (RefBuildTree1.SDA_range t).
Local Notation STP_range := (RefBuildTree1.STP_range t).
Local Notation slen := (RefBuildTree2.slen t).
Local Notation slen_ge := (RefBuildTree2.slen_ge t).
Local Notation STP_rod := (RefBuildTree2.STP_rod t).
Local Notation stree_pb := (RefBuildTree2.stree_pb t).
Local Notation stree_dl_bound := (RefBuildTree2.stree_dl_bound t).
Local Notation stree_Len_dl := (RefBuildTree2.stree_Len_dl t).
Local Notation xbits := (GenBitlenModel.xbits t).
Local Notation stree_has_STP := (RefBuildTree2.stree_has_STP t).

Local Ltac nf := cbn [RefBuildTree1.stF].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition FB5 : list (nat * Z) :=
  [(0%nat, 65536); (1%nat, 65536); (2%nat, 573); (3%nat, 256); (4%nat, 65536); (5%nat, 16); (6%nat, 65536)].

Definition VB5 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 300); (36%nat, 600); (37%nat, 600);
   (38%nat, 600); (39%nat, 16); (40%nat, 300); (41%nat, 600); (42%nat, 2 ^ 64); (43%nat, 2 ^ 64);
   (44%nat, 2 ^ 63); (45%nat, 2 ^ 63); (46%nat, 3000); (47%nat, 2 ^ 63); (48%nat, 600); (49%nat, 16)].

Local Notation ML := (sd_max_length t).
Local Notation BASE := (sd_extra_base t).

(* [comment removed for export] *)
Lemma ml_range : 7 <= ML <= 15.
Proof. destruct t; cbn; unfold MAX_BITS, MAX_BL_BITS; lia. Qed.

Lemma base_range : 0 <= BASE < 300 /\ BASE < E.
Proof. pose proof elems_range. destruct t; cbn in *; unfold LITERALS, L_CODES, LITERALS, LENGTH_CODES in *; lia. Qed.
Lemma EXP_range : TREES_ROD_LO <= EXP t /\ EXP t + 4 * (E - BASE) <= TREES_ROD_HI.
Proof.
  destruct t; cbn; unfold A_extra_lbits, A_extra_dbits, A_extra_blbits, TREES_ROD_LO, TREES_ROD_HI,
    L_CODES, D_CODES, BL_CODES, LITERALS, LENGTH_CODES; lia.
Qed.

(* [comment removed for export] *)
Lemma extra_view_bound : forall x, 0 <= stF (arr_make 1 0) (arr_make 1 0) (arr_make 1 0) (arr_make 1 0) (arr_make 1 0) 5%nat x < 16.
Proof.
  intros x. cbn [RefBuildTree1.stF]. destruct t; cbn [sd_extra_bits].
  - pose proof (extra_lbits_bound x). rewrite Z.mod_small; lia.
  - pose proof (extra_dbits_bound x). rewrite Z.mod_small; lia.
  - pose proof (extra_blbits_bound x). rewrite Z.mod_small; lia.
Qed.
Lemma extra_view_bound' : forall FC DL HP DP BC x, 0 <= stF FC DL HP DP BC 5%nat x < 16.
Proof. intros. apply extra_view_bound. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section PhaseFG.
Variable FC : arr.
Variable HP : arr.
Variable HL : Z.
Variable DP : arr.
Variable MC : Z.
Variable K : Z.
(* [comment removed for export] *)
Local Notation W4 DL BC OL SL := (U FC DL HP HL (K - 1) DP BC OL SL MC).

Hypothesis RFC : forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536.
Hypothesis LFC : arr_len FC = tsize t.
Hypothesis Hmc : 0 <= MC < E.
Hypothesis HK : 1 <= K <= 573.
(* [comment removed for export] *)
Hypothesis PQH : forall h, K <= h < 573 -> 0 <= arr_get HP h < tsize t.

(* [comment removed for export] *)
Local Ltac vfix :=
  repeat match goal with H : hv ?hh ?e = _ |- context [hv ?hh ?e] => rewrite !H end;
  repeat match goal with
         | H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H
         | H : wb ?a ?e = _ |- context [wb ?a ?e] => rewrite !H
         end.

(* [comment removed for export] *)
Local Ltac splitand H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "X" in let H2 := fresh "X" in destruct H as [H1 H2]; splitand H1; splitand H2
  | _ => idtac
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac openGI HG HC RDL LDL RBC LBC ROL RSL C24 :=
  destruct HG as (HC & RDL & LDL & RBC & LBC & ROL & RSL & C24).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac ceqG :=
  nf; vfix;
  repeat match goal with H : _ mod 2 ^ 32 = xbits _ |- context [_ mod 2 ^ 32] => rewrite H end;
  repeat match goal with H : xbits ?n = 0 |- context [xbits ?n] => rewrite H end;
  rewrite <- ?stree_Len_dl;
  first [ reflexivity | f_equal; lia | f_equal; ring ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation GB1 := (GenBitlenModel.GB1 t MC).
Local Notation gb1_ok := (GenBitlenModel.gb1_ok t MC).

End PhaseFG.

End Walk.

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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BuildTreeRod.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefBitsLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefPqdown_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefGenCodes_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefBuildTree1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefBuildTree2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefBuildTree3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefBuildTree4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefBuildTree5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefBuildTree6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefBuildTree7.
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
Local Notation ml_range := (RefBuildTree5.ml_range t).
Local Notation base_range := (RefBuildTree5.base_range t).
Local Notation EXP_range := (RefBuildTree5.EXP_range t).

Local Ltac nf := cbn [RefBuildTree1.stF].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition FB8 : list (nat * Z) :=
  [(0%nat, 65536); (1%nat, 65536); (2%nat, 573); (3%nat, 256); (4%nat, 65536); (5%nat, 16); (6%nat, 65536)].

Definition VB8 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 300); (36%nat, 600); (37%nat, 16);
   (38%nat, 600); (39%nat, 65536); (40%nat, 2 ^ 64); (41%nat, 16); (42%nat, 573)].

(* [comment removed for export] *)
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

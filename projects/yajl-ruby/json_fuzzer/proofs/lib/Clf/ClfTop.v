(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree RunCeiling Nodes Decode RegsEquiv RunInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import GlueCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Clf Require Import CImage ClfMustExit C_Exit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma clf_tree_exits {RC__ : RunCeiling} : forall cfg mo, minv mo -> exits_with_cfg cfg verdict_accept clf_tree mo.
Proof.
  intros cfg mo Hinv. unfold clf_tree, ebind, enode. cbn.
  split; [exact I|]. split; [apply node_fam_on_set_tid|]. split; [exact I|].
  intros rsp mo' evs Hst.
  destruct (nstep_dec_set_tid mo rsp mo' evs Hinv Hst) as (_ & t & Hdec & Ht & _).
  rewrite Hdec. cbn.
  split; [exact I|]. split; [apply node_fam_on_exit|]. split; [| intros rsp' mo'' evs' F; exact (False_ind _ F)].
  apply bv_eq. vm_compute. reflexivity.
Qed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Cla_asan.
End Cla_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Clb_asan.
End Clb_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Cla_ubsan.
End Cla_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Clb_ubsan.
End Clb_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Cla_both.
End Cla_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Clb_both.
End Clb_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Cla_dsl_asan.
End Cla_dsl_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Clb_dsl_asan.
End Clb_dsl_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Cla_dsl_ubsan.
End Cla_dsl_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Clb_dsl_ubsan.
End Clb_dsl_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Cla_dsl_both.
End Cla_dsl_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Clb_dsl_both.
End Clb_dsl_both.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA HeapIfaceABx L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b PmSpecsA_b PnSpecsAa_b PnAVu8Dtor_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNARBK.
Lemma lbr_app_l b (A B : list (Z * Z)) : In b (map fst A) -> lb_remove b (A ++ B) = lb_remove b A ++ B.
Proof.
  induction A as [|x A IH]; intros Hin; [destruct Hin|]. cbn [app lb_remove]. destruct (Z.eqb (fst x) b) eqn:E; [reflexivity|].
  cbn [app]. f_equal. apply IH. cbn [map In] in Hin. destruct Hin as [X|X]; [apply Z.eqb_neq in E; contradiction| exact X].
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Lemma ri_back LB FF LK cr Aw M V B m : NoDup (map fst LB) -> In (B, m) LB ->
  ri_inv HI ((B, m) :: lb_remove B LB) FF LK cr Aw M V -> ri_inv HI LB FF LK cr Aw M V.
Proof.
  intros ND Hin HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF & _).
  apply (HAJ.aior_perm _ _ _ _ _ HIok _ LB FF FF LK cr Aw M V HH).
  - intros x. symmetry. exact (PNAV8D.lbr_iff B m LB ND Hin x).
  - exact ND.
  - intros f. tauto.
  - rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.
End WithHeap.
End PNARBK.

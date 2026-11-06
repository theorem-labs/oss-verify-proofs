(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core L5KnA L5LazyA L5DefsA L5CoreAS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmStatics PmStaticsA HeapIfaceAEx PmSpecs PmSpecsA PeSpecsAa.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEAHK3.

Lemma lb_remove_mid p c (pre post : list (Z * Z)) :
  NoDup (map fst (pre ++ (p, c) :: post)) -> lb_remove p (pre ++ (p, c) :: post) = pre ++ post.
Proof.
  induction pre as [|a pre IH]; cbn [app map lb_remove fst]; intros ND.
  - rewrite Z.eqb_refl. reflexivity.
  - inversion ND as [|x0 l0 NI0 ND0]. subst.
    destruct (Z.eqb (fst a) p) eqn:EQ.
    + apply Z.eqb_eq in EQ. exfalso. apply NI0. rewrite EQ, map_app. apply elem_of_app. right. cbn [map fst]. constructor.
    + f_equal. apply IH. exact ND0.
Qed.
Lemma lb_remove_at p c (l pre post : list (Z * Z)) :
  l = pre ++ (p, c) :: post -> NoDup (map fst l) -> lb_remove p l = pre ++ post.
Proof. intros -> ND. exact (lb_remove_mid p c pre post ND). Qed.

Lemma nodup_mid_notin p c (pre post : list (Z * Z)) m :
  NoDup (map fst (pre ++ (p, c) :: post)) -> ~ In (p, m) pre /\ ~ In (p, m) post.
Proof.
  induction pre as [|a pre IH]; cbn [app map fst]; intros ND.
  - inversion ND as [|x0 l0 NI0 ND0]. subst. split; [intros []|]. intros Hin. apply NI0. apply list_elem_of_In. rewrite in_map_iff. exists (p, m). split; [reflexivity| exact Hin].
  - inversion ND as [|x0 l0 NI0 ND0]. subst. destruct (IH ND0) as [IH1 IH2]. split; [| exact IH2].
    intros [E|Hin]; [| exact (IH1 Hin)]. apply NI0. subst a. cbn [fst]. rewrite map_app. apply elem_of_app. right. cbn [map fst]. constructor.
Qed.

Lemma scA_cr0 L : PMSPA.scA L PMSP.cr0 = PMSPA.cr0.
Proof. unfold PMSPA.scA, PMSP.cr0, PMSPA.cr0. cbn [fst snd]. rewrite Z.mul_0_r. reflexivity. Qed.

End PEAHK3.

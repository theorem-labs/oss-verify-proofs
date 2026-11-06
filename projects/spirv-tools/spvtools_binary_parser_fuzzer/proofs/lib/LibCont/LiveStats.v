(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From stdpp Require Import list.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import StrLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Lemma NoDup_fst_pairs : forall (l : list (Z * Z)), NoDup (map fst l) -> NoDup l.
Proof.
  intros l. induction l as [|[q k] l IH]; intros H; [constructor|].
  cbn [map fst] in H. inversion H as [|x l' Hn H']; subst. apply NoDup_cons_2; [|apply IH; exact H'].
  intros Hin. apply Hn. apply list_elem_of_In. apply in_map_iff. exists (q, k). split; [reflexivity|].
  apply list_elem_of_In. exact Hin.
Qed.

Lemma live_equiv_perm : forall (l1 l2 : list (Z * Z)),
  NoDup (map fst l1) -> NoDup (map fst l2) ->
  (forall q k, In (q, k) l1 <-> In (q, k) l2) -> Permutation l1 l2.
Proof.
  intros l1 l2 H1 H2 HE. apply NoDup_Permutation; [apply NoDup_fst_pairs; exact H1 | apply NoDup_fst_pairs; exact H2 |].
  intros [q k]. rewrite !list_elem_of_In. apply HE.
Qed.

Lemma live_equiv_count : forall cls big (l1 l2 : list (Z * Z)) c,
  NoDup (map fst l1) -> NoDup (map fst l2) ->
  (forall q k, In (q, k) l1 <-> In (q, k) l2) ->
  count_class_f cls big l1 c = count_class_f cls big l2 c.
Proof. intros. apply count_class_f_perm. apply live_equiv_perm; assumption. Qed.

Lemma live_equiv_big : forall rb big (l1 l2 : list (Z * Z)),
  NoDup (map fst l1) -> NoDup (map fst l2) ->
  (forall q k, In (q, k) l1 <-> In (q, k) l2) ->
  big_bytes_f rb big l1 = big_bytes_f rb big l2.
Proof. intros. apply big_bytes_f_perm. apply live_equiv_perm; assumption. Qed.

Lemma NoDup_fst_app : forall (l1 l2 : list (Z * Z)),
  NoDup (map fst l1) -> NoDup (map fst l2) ->
  (forall q k, In (q, k) l2 -> ~ In q (map fst l1)) -> NoDup (map fst (l1 ++ l2)).
Proof.
  intros l1 l2 H1 H2 HD. rewrite map_app. apply (proj2 (list.NoDup_app _ _)). split; [exact H1|]. split; [| exact H2].
  intros x Hx1 Hx2. apply list_elem_of_In in Hx1. apply list_elem_of_In in Hx2.
  apply in_map_iff in Hx2. destruct Hx2 as ([q k] & Hq & Hin). cbn in Hq. subst x.
  exact (HD q k Hin Hx1).
Qed.

Lemma NoDup_fst_nil : NoDup (map fst (@nil (Z * Z))).
Proof. constructor. Qed.

Lemma NoDup_fst_single : forall q k : Z, NoDup (map fst [(q, k)]).
Proof. intros. cbn. apply NoDup_singleton. Qed.

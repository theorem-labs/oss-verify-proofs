(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatClsRefill_b BatCARSpec_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma art_in_skipn : forall (A : Type) (k : nat) (l : list A) x, In x (skipn k l) -> In x l.
Proof. intros A k l x H. rewrite <- (firstn_skipn k l). apply in_or_app. right. exact H. Qed.

Lemma art_ca_cptr_in : forall c cl, 1 <= c <= 30 -> art_cls_ok c cl -> In (art_ca_cptr c cl) (cl_cache (art_ca_pre c cl)).
Proof.
  intros c cl Hc OK. pose proof (art_ca_pre_cache_ne c cl Hc OK) as Hne. unfold art_ca_cptr.
  rewrite (app_removelast_last 0 Hne) at 2. apply in_or_app. right. left. reflexivity.
Qed.

Lemma art_ca_cptr_origin : forall c cl, 1 <= c <= 30 -> art_cls_ok c cl ->
  In (art_ca_cptr c cl) (cl_cache cl ++ cl_free cl)
  \/ (cl_cache cl = [] /\ art_cls_needs_populate c cl = true /\ cl_au cl <= 16 * art_ca_cptr c cl).
Proof.
  intros c cl Hc OK. pose proof (art_ca_cptr_in c cl Hc OK) as Hin. set (wp := art_ca_cptr c cl) in *.
  unfold art_ca_pre in Hin. destruct (cl_cache cl) as [|z l] eqn:E.
  - rewrite art_cls_refill_eq in Hin. cbn [art_cls_take cl_cache] in Hin. apply art_in_skipn in Hin.
    unfold art_cls_pre_take in Hin. destruct (art_cls_needs_populate c cl) eqn:NP.
    + unfold art_cls_populate in Hin. cbn [cl_free] in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [left; exact Hin|].
      right. split; [reflexivity|]. split; [reflexivity|].
      apply art_carved_in in Hin. destruct Hin as (i & Hi & Ew).
      destruct OK as (_ & (Hau0 & _) & _ & _ & (ka & Eau) & _). destruct (art_class_size_facts c Hc) as (Hsz & Hsz16).
      assert (E16 : 16 * wp = AsanTab.class_size c * (ka + i)).
      { rewrite Ew, Eau. replace (AsanTab.class_size c * ka + i * AsanTab.class_size c) with (AsanTab.class_size c * (ka + i)) by lia.
        pose proof (art_div16_mul (AsanTab.class_size c) (ka + i) Hsz16). lia. }
      rewrite E16, Eau. assert (AsanTab.class_size c * ka <= AsanTab.class_size c * (ka + i)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
    + left. exact Hin.
  - left. apply in_or_app. left. rewrite <- E. exact Hin.
Qed.

Lemma art_ca_pre_mu_pop : forall c cl, cl_cache cl = [] -> art_cls_needs_populate c cl = true -> cl_mu (art_ca_pre c cl) = cl_mu cl + 262144.
Proof. intros c cl E NP. unfold art_ca_pre. rewrite E. rewrite art_cls_refill_eq. unfold art_cls_pre_take. rewrite NP. reflexivity. Qed.

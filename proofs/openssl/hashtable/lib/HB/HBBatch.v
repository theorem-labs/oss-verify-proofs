(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxBatch.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBPlanImage HBAtable HBCheckG HBHop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Record hjob : Type := HJ { hj_nx : nat; hj_holes : list (nat * htgt); hj_cs : acs; hj_plan : plan; hj_shape : shape }.

Section Batch.
  Variable GC : bool.
  Variables BF FUEL : nat.
  Definition hrun (it : itab) (j : hjob) : cres :=
    CAP.check HASEGS it HAT (hj_nx j) AsanInit.LIMIT (hag_XN (hj_nx j)) (hag_XE (hj_nx j)) hag_XB (HS_tg (hj_holes j)) 0 true false GC BF FUEL None (hj_cs j) (hj_plan j).
  Definition hbatch_ok (it : itab) (jobs : list hjob) : bool := forallb (fun j => is_ok (hrun it j) (hj_shape j)) jobs.
  Lemma hbatch_all : forall it jobs, hbatch_ok it jobs = true -> forall j, In j jobs -> hrun it j = COk (hj_shape j).
  Proof. intros it jobs H j Hin. apply is_ok_eq. exact (proj1 (forallb_forall _ _) H j Hin). Qed.
  (* [comment removed for export] *)
  Definition allok (it : itab) (X : Type) (mk : X -> hjob) (tab : list X) : Prop :=
    forall x, In x tab -> hrun it (mk x) = COk (hj_shape (mk x)).
  Lemma hbatch_map : forall (X : Type) (mk : X -> hjob) it (tab : list X), hbatch_ok it (map mk tab) = true -> allok it X mk tab.
  Proof. intros X mk it tab H x Hin. apply (hbatch_all it (map mk tab) H). apply in_map. exact Hin. Qed.
  Lemma allok_app : forall it X mk t1 t2, allok it X mk t1 -> allok it X mk t2 -> allok it X mk (t1 ++ t2).
  Proof. intros it X mk t1 t2 H1 H2 x Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (H1 x Hin) | exact (H2 x Hin)]. Qed.
  Lemma allok_prod_app : forall it (X Y : Type) (mk : X * Y -> hjob) t1 t2 (c : list Y),
    allok it _ mk (list_prod t1 c) -> allok it _ mk (list_prod t2 c) -> allok it _ mk (list_prod (t1 ++ t2) c).
  Proof.
    intros it X Y mk t1 t2 c H1 H2 [x y] Hin. apply in_prod_iff in Hin as [Hx Hy]. apply in_app_or in Hx as [Hx|Hx].
    - apply H1. apply in_prod_iff. split; assumption.
    - apply H2. apply in_prod_iff. split; assumption.
  Qed.
  Lemma hbatch_app : forall it a b, hbatch_ok it (a ++ b) = true -> hbatch_ok it a = true /\ hbatch_ok it b = true.
  Proof. intros it a b H. unfold hbatch_ok in *. rewrite forallb_app in H. apply andb_prop in H. exact H. Qed.
End Batch.

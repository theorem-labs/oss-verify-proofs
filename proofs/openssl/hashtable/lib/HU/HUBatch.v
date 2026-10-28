(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan CxPlanSound CxBatch.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUPlanImage HUAtable H0Sinv HUCheckG HUChain HUChain2 HUHop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Record hjob : Type := HJ { hj_nx : nat; hj_holes : list (nat * htgt); hj_cs : acs; hj_plan : plan; hj_shape : shape }.

Section Batch.
  Variable LIM : Z.
  Variables BF FUEL : nat.
  Definition hrun (it : itab) (j : hjob) : cres :=
    CAP.check HSEGS it H0T (hj_nx j) LIM (g0_XN (hj_nx j) LIM) (g0_XE (hj_nx j)) g0_XB (HS_tg (hj_holes j)) 0 true false false BF FUEL None (hj_cs j) (hj_plan j).
  Definition hbatch_ok (it : itab) (jobs : list hjob) : bool := forallb (fun j => is_ok (hrun it j) (hj_shape j)) jobs.
  Lemma hbatch_all : forall rs jobs, (let it := APC.mk_itab_ranges HSEGS rs in hbatch_ok it jobs) = true ->
    forall j, In j jobs -> hrun (APC.mk_itab_ranges HSEGS rs) j = COk (hj_shape j).
  Proof. intros rs jobs H j Hin. apply is_ok_eq. exact (proj1 (forallb_forall _ _) H j Hin). Qed.
  (* [comment removed for export] *)
  Definition allok (rs : list (Z * nat)) (X : Type) (mk : X -> hjob) (tab : list X) : Prop :=
    forall x, In x tab -> hrun (APC.mk_itab_ranges HSEGS rs) (mk x) = COk (hj_shape (mk x)).
  Lemma hbatch_map : forall (X : Type) (mk : X -> hjob) rs (tab : list X),
    (let it := APC.mk_itab_ranges HSEGS rs in hbatch_ok it (map mk tab)) = true -> allok rs X mk tab.
  Proof. intros X mk rs tab H x Hin. apply (hbatch_all rs (map mk tab) H). apply in_map. exact Hin. Qed.
  Lemma allok_app : forall rs X mk t1 t2, allok rs X mk t1 -> allok rs X mk t2 -> allok rs X mk (t1 ++ t2).
  Proof. intros rs X mk t1 t2 H1 H2 x Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (H1 x Hin) | exact (H2 x Hin)]. Qed.
  Lemma allok_prod_app : forall rs (X Y : Type) (mk : X * Y -> hjob) t1 t2 (c : list Y),
    allok rs _ mk (list_prod t1 c) -> allok rs _ mk (list_prod t2 c) -> allok rs _ mk (list_prod (t1 ++ t2) c).
  Proof.
    intros rs X Y mk t1 t2 c H1 H2 [x y] Hin. apply in_prod_iff in Hin as [Hx Hy]. apply in_app_or in Hx as [Hx|Hx].
    - apply H1. apply in_prod_iff. split; assumption.
    - apply H2. apply in_prod_iff. split; assumption.
  Qed.
End Batch.

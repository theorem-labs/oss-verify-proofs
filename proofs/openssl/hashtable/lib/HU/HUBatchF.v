(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan CxPlanSound CxBatch.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUPlanImage HUAtable H0Sinv HUCheckG HUChain HUChain2 HUHop HUBatch.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AsanNodesArg CxfNodes CxfNodesArg CxfCheck CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition g0_XN_f (NX : nat) (LIM : Z) : nat -> list expr -> acs -> option acs := fun id args cs =>
  match id with
  | 31%nat => CXFF.node_munmap_pL HSEGS cs
  | _ => g0_XN NX LIM id args cs
  end.
Lemma g0_XN_f_eq : forall NX LIM id args cs, g0_XN_f NX LIM id args cs = g0_XN NX LIM id args cs.
Proof.
  intros NX LIM id args cs. unfold g0_XN_f.
  do 31 (destruct id as [|id]; [reflexivity|]). destruct id as [|id]; [|reflexivity].
  apply CXFF.node_munmap_pL_eq.
Qed.
Definition g0_XE_f (NX : nat) : nat -> list expr -> acs -> option (Z * list spiece * acs) := CXFF.xe_L HSEGS H0T NX.
Lemma g0_XE_f_eq : forall NX id args cs, g0_XE_f NX id args cs = g0_XE NX id args cs.
Proof. intros. apply CXFF.xe_L_eq. Qed.
(* [comment removed for export] *)
Definition ht_state_f (t : htgt) : acs := add_kn (CXFF.inst_list_L (ht_T t) (ht_s t)) (ht_F t).
Definition HS_tg_f (holes : list (nat * htgt)) : nat -> option acs :=
  fun h => match assoc h holes with Some t => Some (ht_state_f t) | None => None end.
Lemma HS_tg_f_eq : forall holes h, HS_tg_f holes h = HS_tg holes h.
Proof. intros. unfold HS_tg_f, HS_tg, ht_state_f, ht_state. rewrite ?CXFF.inst_list_L_eq. destruct (assoc h holes) as [t|]; [rewrite CXFF.inst_list_L_eq|]; reflexivity. Qed.
Section BatchF.
  Variable LIM : Z.
  Variables BF FUEL : nat.
  Definition hrun_f (it : itab) (j : hjob) : cres :=
    CXFL.check_f HSEGS it H0T (hj_nx j) LIM (g0_XN_f (hj_nx j) LIM) (g0_XE_f (hj_nx j)) g0_XB (HS_tg_f (hj_holes j)) 0 true false false BF FUEL None (hj_cs j) (hj_plan j).
  Definition hbatch_ok_f (it : itab) (jobs : list hjob) : bool := forallb (fun j => is_ok (hrun_f it j) (hj_shape j)) jobs.
  Lemma hrun_f_eq : forall it j, hrun_f it j = hrun LIM BF FUEL it j.
  Proof. intros. unfold hrun_f, hrun. symmetry. apply CXFF.check_l_hooks with (XN' := g0_XN_f (hj_nx j) LIM) (XE' := g0_XE_f (hj_nx j)) (XB' := g0_XB) (HS' := HS_tg_f (hj_holes j)); [intros; apply g0_XN_f_eq | intros; apply g0_XE_f_eq | reflexivity | intros; apply HS_tg_f_eq | reflexivity]. Qed.
  Lemma hbatch_ok_f_eq : forall it jobs, hbatch_ok_f it jobs = hbatch_ok LIM BF FUEL it jobs.
  Proof. intros it jobs. unfold hbatch_ok_f, hbatch_ok. induction jobs as [|j r IH]; [reflexivity|]. cbn [forallb]. rewrite hrun_f_eq, IH. reflexivity. Qed.
  Lemma hbatch_f_intro : forall (mk : itab) jobs,
    (let it := mk in hbatch_ok_f it jobs) = true -> (let it := mk in hbatch_ok LIM BF FUEL it jobs) = true.
  Proof. intros mk jobs H. cbv zeta in *. rewrite <- hbatch_ok_f_eq. exact H. Qed.
End BatchF.

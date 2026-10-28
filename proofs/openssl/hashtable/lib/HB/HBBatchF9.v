(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit AsanNodesArg.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxBatch CxfL9 CxfFast.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBPlanImage HBAtable HBCheckG HBHop HBBatch HBBandDF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Definition hag_XE_f (NX : nat) : nat -> list expr -> acs -> option (Z * list spiece * acs) := CXFF.xe_L HASEGS HAT NX.
Lemma hag_XE_f_eq : forall NX id args cs, hag_XE_f NX id args cs = hag_XE NX id args cs.
Proof. intros. apply CXFF.xe_L_eq. Qed.
Definition ht_state_f (t : htgt) : acs := add_kn (CXFF.inst_list_L (ht_T t) (ht_s t)) (ht_F t).
Definition HS_tg_f (holes : list (nat * htgt)) : nat -> option acs :=
  fun h => match assoc h holes with Some t => Some (ht_state_f t) | None => None end.
Lemma HS_tg_f_eq : forall holes h, HS_tg_f holes h = HS_tg holes h.
Proof. intros. unfold HS_tg_f, HS_tg, ht_state_f, ht_state. destruct (assoc h holes) as [t|]; [rewrite CXFF.inst_list_L_eq|]; reflexivity. Qed.

Section BatchF.
  Variable GC : bool.
  Variables BF FUEL : nat.
  Definition hrun_f (it : itab) (j : hjob) : cres :=
    CXFL.check_f HASEGS it HAT (hj_nx j) AsanInit.LIMIT (hag_XN_f (hj_nx j)) (hag_XE_f (hj_nx j)) hag_XB (HS_tg_f (hj_holes j)) 0 true false GC BF FUEL None (hj_cs j) (hj_plan j).
  Definition hbatch_ok_f (it : itab) (jobs : list hjob) : bool := forallb (fun j => is_ok (hrun_f it j) (hj_shape j)) jobs.
  Lemma hrun_f_eq : forall it j, hrun_f it j = hrun GC BF FUEL it j.
  Proof.
    intros. unfold hrun_f, hrun. symmetry.
    apply CXFF.check_l_hooks with (XN' := hag_XN_f (hj_nx j)) (XE' := hag_XE_f (hj_nx j)) (XB' := hag_XB) (HS' := HS_tg_f (hj_holes j));
      [intros; apply hag_XN_f_eq | intros; apply hag_XE_f_eq | reflexivity | intros; apply HS_tg_f_eq | reflexivity].
  Qed.
  Lemma hbatch_ok_f_eq : forall it jobs, hbatch_ok_f it jobs = hbatch_ok GC BF FUEL it jobs.
  Proof. intros it jobs. unfold hbatch_ok_f, hbatch_ok. induction jobs as [|j r IH]; [reflexivity|]. cbn [forallb]. rewrite hrun_f_eq, IH. reflexivity. Qed.
  Lemma hbatch_f_intro : forall it jobs, hbatch_ok_f it jobs = true -> hbatch_ok GC BF FUEL it jobs = true.
  Proof. intros it jobs H. rewrite <- hbatch_ok_f_eq. exact H. Qed.
End BatchF.

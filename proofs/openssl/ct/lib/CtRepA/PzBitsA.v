(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge Arr Frame Cells Step. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog ApBase ApState ApLogic ApErr.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA ImplA BnRepDefs BnRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApIface ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface ApErrKitA ApErrKitA2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma badr_cons_other : forall OW p A n q, p <> q -> badr ((p, A, n) :: OW) q = badr OW q.
Proof. intros. rewrite badr_cons. destruct (bptr_eqb p q) eqn:E; [|reflexivity]. apply bptr_eqb_eq in E. contradiction. Qed.

Lemma in_ids : forall (OW : list block) q A n, In (q, A, n) OW -> In q (map blk_id OW).
Proof. intros OW q A n H. change q with (blk_id (q, A, n)). apply in_map. exact H. Qed.

Lemma optb_ok_cons_fresh : forall OW p A n o, ~ In p (map blk_id OW) -> optb_ok OW o -> optb_ok ((p, A, n) :: OW) o.
Proof.
  intros OW p A n [[q k]|] NI H; [|exact I]. unfold CtRepP.ApRepDefs.optb_ok in *. destruct H as [HIn Hpos].
  assert (Hpq : p <> q) by (intros ->; apply NI; eapply in_ids; exact HIn).
  rewrite (badr_cons_other OW p A n q Hpq). split; [right; exact HIn|exact Hpos].
Qed.

Lemma map_optr_cons_fresh : forall OW p A n (l : list (option (bptr * Z))),
  ~ In p (map blk_id OW) -> Forall (optb_ok OW) l -> map (optr (badr ((p, A, n) :: OW))) l = map (optr (badr OW)) l.
Proof.
  intros OW p A n l NI HF. induction HF as [|o l Ho HF IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal.
  destruct o as [[q k]|]; [|reflexivity]. unfold CtRepP.ApRepDefs.optb_ok in Ho. destruct Ho as [HIn _]. unfold optr.
  apply badr_cons_other. intros ->. apply NI. eapply in_ids. exact HIn.
Qed.

Lemma g_of_adr_ext : forall (st : ap_st bptr) adr adr',
  map (optr adr') (as_data st) = map (optr adr) (as_data st) -> map (optr adr') (as_file st) = map (optr adr) (as_file st) ->
  map (optr adr') (as_func st) = map (optr adr) (as_func st) -> g_of st adr' = g_of st adr.
Proof. intros st adr adr' E1 E2 E3. unfold g_of. rewrite E1, E2, E3. reflexivity. Qed.

Lemma ap_state_cons_fresh : forall st m OW E bo q A0 n0,
  ap_state st m OW E bo -> ~ In q (map blk_id OW) -> 0 < A0 -> A0 + n0 < 2^63 -> A0 mod 16 = 0 ->
  ap_state st m ((q, A0, n0) :: OW) E bo.
Proof.
  intros st m OW E bo q A0 n0 AS NI HA Hn H16.
  pose proof (proj1 (ap_state_splitA _ _ _ _ _) AS) as [AR ER]. destruct ER as (SH & EAT & F1 & F2 & F3).
  apply ap_state_joinA.
  - apply rest_OW_consA; assumption.
  - exact SH.
  - rewrite (g_of_adr_ext st (badr OW) (badr ((q, A0, n0) :: OW)));
      [apply es_at_raw; exact EAT| apply map_optr_cons_fresh; assumption| apply map_optr_cons_fresh; assumption| apply map_optr_cons_fresh; assumption].
  - eapply Forall_impl; [|exact F1]. intros o Ho. apply optb_ok_cons_fresh; assumption.
  - eapply Forall_impl; [|exact F2]. intros o Ho. apply optb_ok_cons_fresh; assumption.
  - eapply Forall_impl; [|exact F3]. intros o Ho. apply optb_ok_cons_fresh; assumption.
Qed.

Lemma data_cells_cons_fresh : forall m OW st q A0 n0,
  data_cells m OW st -> Forall (optb_ok OW) (as_data st) -> ~ In q (map blk_id OW) -> data_cells m ((q, A0, n0) :: OW) st.
Proof.
  intros m OW st q A0 n0 DC F3 NI. eapply data_cells_OWA; [exact DC|]. intros i p k Hd.
  pose proof (optb_ok_nth OW _ i p k F3 Hd) as [HIn _]. apply badr_cons_other. intros ->. apply NI. eapply in_ids. exact HIn.
Qed.

Lemma rin_ivs_app : forall X Y a, rin_ivs (X ++ Y) a <-> rin_ivs X a \/ rin_ivs Y a.
Proof. intros X Y a. induction X as [|[l h] X IH]; cbn [rin_ivs app fst snd]; tauto. Qed.

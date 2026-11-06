(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk HeapIface HeapIfaceA HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRuns ArtBridge EbtInitCache EbtPopulate1 EbtCls EbtClsGfa2 EbtCARSpec EbtFxBatch3 EbtSecRSpec EbtWrapPure EbtInvMallocPure EbrInv EbrInvMalloc EbrInvFreePure EbrWrapMallocX EbrCreditQ EbrCreditC EbrCredit EbrCreditT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma art_items_snoc1 : forall bs b, art_items (bs ++ [b]) = art_items bs ++ bt_items b.
Proof. intros bs b. rewrite art_items_app. unfold art_items at 2. cbn [flat_map]. rewrite app_nil_r. reflexivity. Qed.
Lemma art_free_newb_false_ne : forall qt, art_free_newb qt = false -> qt <> [].
Proof. intros qt H E. subst qt. unfold art_free_newb, art_enq_newb in H. cbn in H. discriminate H. Qed.
Lemma art_qt_split_last : forall qt : list art_batch, qt <> [] -> qt = removelast qt ++ [art_lastb qt].
Proof. intros qt H. unfold art_lastb. apply app_removelast_last. exact H. Qed.
Lemma art_items_qt_add : forall qt b it, art_items (art_qt_add qt b it) = art_items qt ++ [it].
Proof.
  intros qt b it. unfold art_qt_add. destruct (art_free_newb qt) eqn:E.
  - rewrite art_items_snoc1. reflexivity.
  - rewrite art_items_snoc1. cbn [bt_items]. rewrite app_assoc. f_equal.
    rewrite (art_qt_split_last qt (art_free_newb_false_ne qt E)) at 3. rewrite art_items_snoc1. reflexivity.
Qed.
Lemma art_in_items : forall bs it, In it (art_items bs) <-> exists b, In b bs /\ In it (bt_items b).
Proof. intros bs it. unfold art_items. rewrite in_flat_map. reflexivity. Qed.
Lemma art_items_pos_iff : forall bs, art_items_pos bs <-> (forall it, In it (art_items bs) -> 1 <= snd it).
Proof.
  intros bs. split.
  - intros H it Hit. apply art_in_items in Hit. destruct Hit as (b & Hb & Hi). exact (H b it Hb Hi).
  - intros H b it Hb Hi. apply H. apply art_in_items. exists b. split; assumption.
Qed.
Lemma art_items_pos_qt_add : forall qt b it, art_items_pos qt -> 1 <= snd it -> art_items_pos (art_qt_add qt b it).
Proof.
  intros qt b it P Hn. apply art_items_pos_iff. intros x Hx. rewrite art_items_qt_add in Hx. apply in_app_or in Hx.
  destruct Hx as [Hx|[<-|[]]]; [|exact Hn]. exact (proj1 (art_items_pos_iff qt) P x Hx).
Qed.

Lemma art_nirr_lb_remove : forall spb u n (LB : list (Z * Z)), List.NoDup (map fst LB) -> In (u, n) LB ->
  art_nirr spb (art_hdrs (lb_remove u LB)) + (if art_irr spb (u - 16, n) then 1 else 0) = art_nirr spb (art_hdrs LB).
Proof.
  intros spb u n LB. induction LB as [|x r IH]; intros ND Hi; [destruct Hi|].
  cbn [lb_remove]. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as (Hx & ND).
  destruct (Z.eqb_spec (fst x) u) as [E|NE].
  - assert (x = (u, n)).
    { destruct Hi as [Hi|Hi]; [exact Hi|]. exfalso. apply Hx. rewrite E. apply in_map_iff. exists (u, n). split; [reflexivity|exact Hi]. }
    subst x. unfold art_hdrs. cbn [map fst snd]. fold (art_hdrs r). rewrite art_nirr_cons. lia.
  - destruct Hi as [Hi|Hi]; [exfalso; apply NE; rewrite Hi; reflexivity|].
    unfold art_hdrs. cbn [map]. fold (art_hdrs r). fold (art_hdrs (lb_remove u r)). rewrite !art_nirr_cons. specialize (IH ND Hi). lia.
Qed.
Lemma art_lb_remove_length : forall u n (LB : list (Z * Z)), In (u, n) LB -> Z.of_nat (length (lb_remove u LB)) + 1 = Z.of_nat (length LB).
Proof.
  induction LB as [|x r IH]; intros Hi; [contradiction|]. cbn [lb_remove length]. destruct (Z.eqb_spec (fst x) u) as [E|NE]; [lia|].
  destruct Hi as [->|Hi]; [exfalso; apply NE; reflexivity|]. cbn [length]. specialize (IH Hi). lia.
Qed.

Section F.
Variable FSG : Type.
Variable BUDGET : Z.
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (cr : credit).
Hypothesis CRED : art_credit_ok FSG BUDGET rn G LB cr.
Hypothesis CLSOK : forall c, 1 <= c <= 30 -> art_cls_ok c (g_cls FSG G c).
Hypothesis NDLB : List.NoDup (map fst LB).
Hypothesis POSQ : art_items_pos (g_qt FSG G).

Lemma art_enq_events_cost : forall newb, art_cost_sum (art_enq_events newb (rn_spb rn) (g_cls FSG G 24)) = art_cl_maps (art_enq_cls newb (g_cls FSG G 24)) - art_cl_maps (g_cls FSG G 24)
  /\ art_cost_sec (art_enq_events newb (rn_spb rn) (g_cls FSG G 24)) = 0
  /\ forall log, art_live (log ++ art_enq_events newb (rn_spb rn) (g_cls FSG G 24)) = art_live log.
Proof.
  intros newb. unfold art_enq_events, art_enq_cls. destruct newb.
  - split; [exact (art_ca_events_cost (rn_spb rn) 24 _ ltac:(lia) (CLSOK 24 ltac:(lia)))|]. split; [apply art_cost_sec_ca|]. intros log. apply art_live_ca_events.
  - split; [unfold art_cost_sum; cbn [fold_right]; lia|]. split; [reflexivity|]. intros log. rewrite app_nil_r. reflexivity.
Qed.

Lemma art_wfx_creditR : forall u n (kb : nat) k (d : bool),
  let G1 := art_gs_free G (rn_spb rn) k u n kb in
  g_depot FSG G = Datatypes.S kb -> In (u, n) LB -> 1 <= n ->
  (d = true -> 2 ^ 20 < art_batches_bytes (g_qt FSG G1)) ->
  art_credit_ok FSG BUDGET rn (if d then art_gs_drain G1 else G1) (lb_remove u LB) cr.
Proof.
  intros u n kb k d G1 Edep Hi Hn Hd.
  destruct CRED as (irr & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & QT & QG).
  set (newb := art_free_newb (g_qt FSG G)). set (cl := g_cls FSG G 24) in *.
  set (qt1 := art_qt_add (g_qt FSG G) (rn_spb rn + 24 * 2 ^ 32 + 16 * art_ca_cptr 24 cl) (u - 16, n)).
  destruct (art_enq_events_cost newb) as (Ecost & Esec0 & Elive). fold cl in Ecost, Esec0, Elive.
  pose proof (art_lb_remove_length u n LB Hi) as HLEN.
  pose proof (art_nirr_lb_remove (rn_spb rn) u n LB NDLB Hi) as HIRR.
  assert (ESEC : length (g_sec FSG G1) = length (g_sec FSG G)). { unfold G1. cbn [art_gs_free g_sec]. destruct k; [reflexivity|apply art_sec_quar_length]. }
  assert (EQS : g_log FSG (if d then art_gs_drain G1 else G1) = g_log FSG G ++ art_enq_events newb (rn_spb rn) cl
                /\ length (g_sec FSG (if d then art_gs_drain G1 else G1)) = length (g_sec FSG G)
                /\ g_depot FSG (if d then art_gs_drain G1 else G1) = kb
                /\ g_sec_committed FSG (if d then art_gs_drain G1 else G1) = g_sec_committed FSG G
                /\ g_cls FSG (if d then art_gs_drain G1 else G1) = (fun c0 => if c0 =? 24 then art_enq_cls newb cl else g_cls FSG G c0)).
  { destruct d; cbn [art_gs_drain g_log g_sec g_depot g_cls g_sec_committed]; (split; [reflexivity|]); (split; [exact ESEC|]); (split; [reflexivity|]); split; reflexivity. }
  destruct EQS as (Elog & Esec & Edp & Ecm & Ecls).
  assert (Eqt1 : g_qt FSG G1 = qt1) by reflexivity. assert (Eqg1 : g_qg FSG G1 = g_qg FSG G) by reflexivity.
  assert (QT1 : art_qt_ok qt1) by (apply art_qt_ok_add; exact QT).
  assert (POS1 : art_items_pos qt1) by (apply art_items_pos_qt_add; [exact POSQ | cbn [snd]; exact Hn]).
  assert (EIT : art_nirr (rn_spb rn) (art_items (g_qt FSG (if d then art_gs_drain G1 else G1) ++ g_qg FSG (if d then art_gs_drain G1 else G1)))
                = art_nirr (rn_spb rn) (art_items (g_qt FSG G ++ g_qg FSG G)) + (if art_irr (rn_spb rn) (u - 16, n) then 1 else 0)).
  { destruct d; cbn [art_gs_drain g_qt g_qg app]; rewrite ?Eqt1, ?Eqg1, !art_items_app, !art_nirr_app; unfold qt1; rewrite art_items_qt_add, art_nirr_app;
      (replace (art_nirr (rn_spb rn) [(u - 16, n)]) with (if art_irr (rn_spb rn) (u - 16, n) then 1 else 0) by (rewrite art_nirr_cons, art_nirr_nil; lia)); lia. }
  exists irr. unfold art_credit_ok. rewrite Elog, Esec, Edp, Ecm, Ecls, EIT.
  rewrite art_cost_sum_app, art_cost_sec_app, Esec0, Elive, (art_primsum_upd _ 24 _ ltac:(lia)), Ecost. fold cl.
  rewrite Edep, Nat2Z.inj_succ in C9. cbn [fst snd].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  destruct d; cbn [art_gs_drain g_qt g_qg]; rewrite ?Eqt1, ?Eqg1.
  - split; [exact art_qt_ok_nil|]. apply art_qg_ok_transfer; [exact QG | exact QT1 | exact POS1 | rewrite <- Eqt1; exact (Hd eq_refl)].
  - split; [exact QT1 | exact QG].
Qed.

Lemma art_wfx_creditW : forall u n k (d : bool),
  let G1 := art_gs_free G (rn_spb rn) k u n (g_depot FSG G) in
  In (u, n) LB -> 1 <= n ->
  (d = true -> 2 ^ 20 < art_batches_bytes (g_qt FSG G1)) ->
  art_credit_ok FSG BUDGET rn (if d then art_gs_drain G1 else G1) (lb_remove u LB) (fst cr + 1, snd cr).
Proof.
  intros u n k d G1 Hi Hn Hd.
  destruct CRED as (irr & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & QT & QG).
  set (newb := art_free_newb (g_qt FSG G)). set (cl := g_cls FSG G 24) in *.
  set (qt1 := art_qt_add (g_qt FSG G) (rn_spb rn + 24 * 2 ^ 32 + 16 * art_ca_cptr 24 cl) (u - 16, n)).
  destruct (art_enq_events_cost newb) as (Ecost & Esec0 & Elive). fold cl in Ecost, Esec0, Elive.
  pose proof (art_lb_remove_length u n LB Hi) as HLEN.
  pose proof (art_nirr_lb_remove (rn_spb rn) u n LB NDLB Hi) as HIRR.
  assert (ESEC : length (g_sec FSG G1) = length (g_sec FSG G)). { unfold G1. cbn [art_gs_free g_sec]. destruct k; [reflexivity|apply art_sec_quar_length]. }
  assert (EQS : g_log FSG (if d then art_gs_drain G1 else G1) = g_log FSG G ++ art_enq_events newb (rn_spb rn) cl
                /\ length (g_sec FSG (if d then art_gs_drain G1 else G1)) = length (g_sec FSG G)
                /\ g_depot FSG (if d then art_gs_drain G1 else G1) = g_depot FSG G
                /\ g_sec_committed FSG (if d then art_gs_drain G1 else G1) = g_sec_committed FSG G
                /\ g_cls FSG (if d then art_gs_drain G1 else G1) = (fun c0 => if c0 =? 24 then art_enq_cls newb cl else g_cls FSG G c0)).
  { destruct d; cbn [art_gs_drain g_log g_sec g_depot g_cls g_sec_committed]; (split; [reflexivity|]); (split; [exact ESEC|]); (split; [reflexivity|]); split; reflexivity. }
  destruct EQS as (Elog & Esec & Edp & Ecm & Ecls).
  assert (Eqt1 : g_qt FSG G1 = qt1) by reflexivity. assert (Eqg1 : g_qg FSG G1 = g_qg FSG G) by reflexivity.
  assert (QT1 : art_qt_ok qt1) by (apply art_qt_ok_add; exact QT).
  assert (POS1 : art_items_pos qt1) by (apply art_items_pos_qt_add; [exact POSQ | cbn [snd]; exact Hn]).
  assert (EIT : art_nirr (rn_spb rn) (art_items (g_qt FSG (if d then art_gs_drain G1 else G1) ++ g_qg FSG (if d then art_gs_drain G1 else G1)))
                = art_nirr (rn_spb rn) (art_items (g_qt FSG G ++ g_qg FSG G)) + (if art_irr (rn_spb rn) (u - 16, n) then 1 else 0)).
  { destruct d; cbn [art_gs_drain g_qt g_qg app]; rewrite ?Eqt1, ?Eqg1, !art_items_app, !art_nirr_app; unfold qt1; rewrite art_items_qt_add, art_nirr_app;
      (replace (art_nirr (rn_spb rn) [(u - 16, n)]) with (if art_irr (rn_spb rn) (u - 16, n) then 1 else 0) by (rewrite art_nirr_cons, art_nirr_nil; lia)); lia. }
  exists irr. unfold art_credit_ok. rewrite Elog, Esec, Edp, Ecm, Ecls, EIT.
  rewrite art_cost_sum_app, art_cost_sec_app, Esec0, Elive, (art_primsum_upd _ 24 _ ltac:(lia)), Ecost. fold cl.
  cbn [fst snd].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  destruct d; cbn [art_gs_drain g_qt g_qg]; rewrite ?Eqt1, ?Eqg1.
  - split; [exact art_qt_ok_nil|]. apply art_qg_ok_transfer; [exact QG | exact QT1 | exact POS1 | rewrite <- Eqt1; exact (Hd eq_refl)].
  - split; [exact QT1 | exact QG].
Qed.

Lemma art_wfx_creditU : forall (warm : bool) u n (kb : nat) k (d : bool),
  let G1 := art_gs_free G (rn_spb rn) k u n kb in
  (if warm then kb = g_depot FSG G else g_depot FSG G = Datatypes.S kb) -> In (u, n) LB -> 1 <= n ->
  (d = true -> 2 ^ 20 < art_batches_bytes (g_qt FSG G1)) ->
  art_credit_ok FSG BUDGET rn (if d then art_gs_drain G1 else G1) (lb_remove u LB) (if warm then (fst cr + 1, snd cr) else cr).
Proof.
  intros warm u n kb k d G1 KBW Hi Hn Hd. destruct warm; [subst kb; exact (art_wfx_creditW u n k d Hi Hn Hd) | exact (art_wfx_creditR u n kb k d KBW Hi Hn Hd)].
Qed.

Lemma art_wfp_creditU : forall (warm : bool) u n (kb : nat) (evs : list aev) (sec' : list art_sec),
  (if warm then kb = g_depot FSG G else g_depot FSG G = Datatypes.S kb) -> In (u, n) LB ->
  art_cost_sum evs = 0 -> art_cost_sec evs = 0 ->
  Z.of_nat (length (art_live (g_log FSG G ++ evs))) <= Z.of_nat (length (art_live (g_log FSG G))) ->
  Z.of_nat (length sec') + 1 = Z.of_nat (length (g_sec FSG G)) ->
  art_credit_ok FSG BUDGET rn (GS FSG (g_log FSG G ++ evs) (g_inited FSG G) (g_cls FSG G) (g_st FSG G) sec' (g_sec_committed FSG G) (g_qt FSG G) (g_qg FSG G) kb true (g_fs FSG G))
                (lb_remove u LB) (if warm then (fst cr + 1, snd cr) else cr).
Proof.
  intros warm u n kb evs sec' KBW Hin EC1 EC2 LL SL.
  destruct CRED as (irr & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & QT & QG).
  pose proof (art_lb_remove_length u n LB Hin) as HLEN. pose proof (art_nirr_lb_remove (rn_spb rn) u n LB NDLB Hin) as HIRR.
  exists irr. unfold art_credit_ok. cbn [g_log g_sec g_sec_committed g_depot g_cls g_qt g_qg].
  rewrite art_cost_sum_app, art_cost_sec_app, EC1, EC2.
  destruct warm.
  - subst kb. cbn [fst snd]. destruct (art_irr (rn_spb rn) (u - 16, n)).
    all: split; [clear - C1; lia|]; split; [exact C2|]; split; [exact C3|]; split; [clear - C4 HLEN HIRR; lia|]; split; [clear - C5; lia|]; split; [clear - C6; lia|].
    all: split; [clear - C7 LL; lia|]; split; [clear - C8 SL; lia|]; split; [clear - C9 HLEN; lia|]; split; [clear - C10 HIRR; lia|]; split; [exact QT|exact QG].
  - rewrite KBW, Nat2Z.inj_succ in C9. destruct (art_irr (rn_spb rn) (u - 16, n)).
    all: split; [exact C1|]; split; [exact C2|]; split; [exact C3|]; split; [clear - C4 HLEN HIRR; lia|]; split; [clear - C5; lia|]; split; [clear - C6; lia|].
    all: split; [clear - C7 LL; lia|]; split; [clear - C8 SL; lia|]; split; [clear - C9 HLEN; lia|]; split; [clear - C10 HIRR; lia|]; split; [exact QT|exact QG].
Qed.
End F.

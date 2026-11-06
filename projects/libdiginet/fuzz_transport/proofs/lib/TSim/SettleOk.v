(* settle_m B ticked = Some (B, tt) from: agree_core and C2's keepalive clause (Agree.v) at the end of the operation,
   the operation's OW / GOT equalities (settle_eq: what the model predicted is what the library noticed), and,
   when the operation ticked, the drain fact (drain_fact: nothing ready is left while the session could send).
   Every check of settle returns its world unchanged, so the world after settle is B. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree QueueFacts Deadline.
Import ListNotations.
Open Scope Z_scope.

(* ---- the operation's facts settle reads ---- *)

(* the OW / GOT records agree (check_ack_settle FT:680-688, check_state_settle FT:690-742, check_inflight_settle's
   first test FT:750-751): counters, and the transition list on its recorded part (i < OW.n, i < TRANS_MAX) *)
Record settle_eq (B : list byte) : Prop := {
  se_acks : GOT_acks B = OW_acks B;
  se_e2 : GOT_e2 B = OW_e2 B;
  se_e3 : GOT_e3 B = OW_e3 B;
  se_ndata : GOT_ndata B = OW_ndata B;
  se_desk : GOT_desk B = OW_desk B;
  se_foreign : GOT_foreign B = OW_foreign B;
  se_acked : GOT_acked B = OW_acked B;
  se_n : GOT_n B = OW_n B;
  se_t : forall i, 0 <= i < OW_n B -> i < TRANS_MAX ->
    GOT_t_state B i = OW_t_state B i /\ GOT_t_old B i = OW_t_old B i /\ GOT_t_reason B i = OW_t_reason B i;
}.

(* check_latest_drain's pacing (FT:787) *)
Definition drain_allow (B : list byte) : bool :=
  negb (truth (M_display_sent B)) || (Cfg_display_gap_us B <=? u64 (g_now B - M_last_display B)).

(* the drain fact (FT:800-801): tagged, online, nothing in flight, back-off passed -> no queued command is ready *)
Definition drain_fact (B : list byte) : Prop :=
  g_raw B = 0 -> M_state B = S_ONLINE -> M_fly_on B = 0 -> M_backoff_until B <= g_now B ->
  forall i, 0 <= i < g_nq B -> negb (truth (Cmd_display B (Q_at B i))) || drain_allow B = false.

(* ---- the checks ----
   No proof here rewrites with Z.eqb_refl or asks the unifier to equate two different getters: the unifier then
   unfolds both down to skipn (Z.to_nat <offset>) of the world and runs out of memory (a first build of this file
   was killed at 209 GB). Each test x =? y is split by Z.eqb_spec on its exact terms. *)

Ltac eq_test x y H := let N := fresh "N" in destruct (Z.eqb_spec x y) as [_|N]; [|exact (False_ind _ (N H))].

Lemma check_ack_settle_ok : forall B, GOT_acks B = OW_acks B -> check_ack_settle_m B = Some (B, tt).
Proof. intros B H. unfold check_ack_settle_m. eq_test (GOT_acks B) (OW_acks B) H. reflexivity. Qed.

Lemma state_settle_loop_ok0 : forall fuel B i, 0 <= i ->
  (forall j, i <= j < OW_n B -> j < TRANS_MAX ->
     GOT_t_state B j = OW_t_state B j /\ GOT_t_old B j = OW_t_old B j /\ GOT_t_reason B j = OW_t_reason B j) ->
  state_settle_loop fuel B i true true = (true, true).
Proof.
  induction fuel as [|fuel IH]; intros B i Hi H; cbn [state_settle_loop]; [reflexivity|].
  destruct ((i <? OW_n B) && (i <? TRANS_MAX)) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
  destruct (H i ltac:(lia) E2) as (Ha & Hb & Hc).
  eq_test (GOT_t_state B i) (OW_t_state B i) Ha. eq_test (GOT_t_old B i) (OW_t_old B i) Hb.
  eq_test (GOT_t_reason B i) (OW_t_reason B i) Hc. cbn [andb].
  apply IH; [lia|]. intros j Hj Hj'. apply H; lia.
Qed.

Lemma check_state_settle_ok : forall B, settle_eq B -> S_state B = M_state B -> check_state_settle_m B = Some (B, tt).
Proof.
  intros B HS Hst. pose proof (se_e2 B HS) as H2. pose proof (se_e3 B HS) as H3. pose proof (se_ndata B HS) as H4.
  pose proof (se_desk B HS) as H5. pose proof (se_foreign B HS) as H6. pose proof (se_n B HS) as H7.
  unfold check_state_settle_m.
  eq_test (GOT_e2 B) (OW_e2 B) H2. eq_test (GOT_e3 B) (OW_e3 B) H3. eq_test (GOT_ndata B) (OW_ndata B) H4.
  eq_test (GOT_desk B) (OW_desk B) H5. eq_test (GOT_foreign B) (OW_foreign B) H6.
  eq_test (GOT_n B) (OW_n B) H7. eq_test (S_state B) (M_state B) Hst. cbn [negb orb andb].
  rewrite state_settle_loop_ok0.
  - reflexivity.
  - lia.
  - intros j Hj Hj'. apply (se_t B HS); lia.
Qed.

Lemma check_keepalive_settle_ok : forall B, c2_keepalive B -> check_keepalive_settle_m B = Some (B, tt).
Proof.
  intros B H. unfold check_keepalive_settle_m, c2_keepalive, truth in *.
  destruct (Z.eqb_spec (g_raw B) 0) as [Er|Er]; cbn [negb andb]; [|reflexivity].
  destruct (Z.eqb_spec (M_state B) S_ONLINE) as [Es|Es]; cbn [andb]; [|reflexivity].
  destruct (Z.eqb_spec (M_fly_on B) 0) as [Ef|Ef]; cbn [negb andb]; [|reflexivity].
  destruct (Z.leb_spec (M_backoff_until B) (g_now B)) as [Eb|Eb]; cbn [andb]; [|reflexivity].
  specialize (H Er Es Ef Eb).
  destruct (Z.leb_spec (M_next_ka B) (g_now B)); [lia|reflexivity].
Qed.

(* check_latest_drain's loop (FT:788-789) over g_q[i ..]: its answer, and false when no entry from i on is ready *)
Lemma drain_loop_ok : forall fuel B allow i rd, 0 <= i -> g_nq B <= CMDS_MAX ->
  (Z.to_nat (g_nq B - i) < fuel)%nat ->
  (forall j, i <= j < g_nq B -> Q_at B j < CMDS_MAX) ->
  exists r, drain_loop fuel B allow i rd = Some r /\
    (rd = false -> (forall j, i <= j < g_nq B -> negb (truth (Cmd_display B (Q_at B j))) || allow = false) ->
     r = false).
Proof.
  induction fuel as [|fuel IH]; intros B allow i rd Hi Hnq Hf HQ; [lia|].
  cbn [drain_loop].
  destruct ((i <? g_nq B) && negb rd) eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply Z.ltb_lt in E1. apply negb_true_iff in E2. subst rd.
    destruct (Z.leb_spec CMDS_MAX i) as [Ei|Ei]; [lia|].
    pose proof (HQ i ltac:(lia)) as Hq.
    destruct (Z.leb_spec CMDS_MAX (Q_at B i)) as [Eq|Eq]; [lia|].
    destruct (IH B allow (i + 1) (negb (truth (Cmd_display B (Q_at B i))) || allow) ltac:(lia) Hnq
                ltac:(lia) ltac:(intros j Hj; apply HQ; lia)) as (r & Hr & Hr').
    exists r. split; [exact Hr|]. intros _ Hn. apply Hr'; [apply Hn; lia|]. intros j Hj. apply Hn; lia.
  - exists rd. split; [reflexivity|]. intros Hrd _. exact Hrd.
Qed.

Lemma check_latest_drain_ok : forall I ops B, agree_core I ops B -> g_raw B = 0 -> drain_fact B ->
  check_latest_drain_m B = Some (B, tt).
Proof.
  intros I ops B HC Hr HD. pose proof (ac_q _ _ _ HC) as HQ.
  pose proof (d1_nq _ _ HQ Hr) as Hnq. pose proof (d3_ncmd _ _ HQ) as Hn3. pose proof (d3_ops _ _ HQ) as Hops.
  assert (Hn0 : 0 <= g_nq B) by (unfold g_nq; apply u_at_nonneg).
  unfold check_latest_drain_m. fold (drain_allow B).
  destruct (drain_loop_ok (S (Z.to_nat CMDS_MAX)) B (drain_allow B) 0 false ltac:(lia)
              ltac:(unfold QUEUE_MAX, CMDS_MAX in *; lia) ltac:(unfold QUEUE_MAX, CMDS_MAX in *; lia)
              ltac:(intros j Hj; destruct (d1_entry _ _ HQ Hr j Hj) as (Hq & _);
                    unfold OPS_MAX, CMDS_MAX in *; lia)) as (r & Hr1 & Hr2).
  rewrite Hr1.
  destruct (Z.eqb_spec (M_state B) S_ONLINE) as [Es|Es]; cbn [andb]; [|reflexivity].
  unfold truth. destruct (Z.eqb_spec (M_fly_on B) 0) as [Ef|Ef]; cbn [negb andb]; [|reflexivity].
  destruct (Z.leb_spec (M_backoff_until B) (g_now B)) as [Eb|Eb]; cbn [andb]; [|reflexivity].
  rewrite (Hr2 eq_refl (fun j Hj => HD Hr Es Ef Eb j Hj)). reflexivity.
Qed.

(* an operation that noticed nothing and predicted nothing (OW / GOT as op_begin left them, FT:388-394) *)
Lemma settle_eq_zero : forall B,
  OW_n B = 0 -> GOT_n B = 0 -> OW_e2 B = 0 -> GOT_e2 B = 0 -> OW_e3 B = 0 -> GOT_e3 B = 0 ->
  OW_acks B = 0 -> GOT_acks B = 0 -> OW_desk B = 0 -> GOT_desk B = 0 -> OW_foreign B = 0 -> GOT_foreign B = 0 ->
  OW_acked B = 0 -> GOT_acked B = 0 -> OW_ndata B = 0 -> GOT_ndata B = 0 -> settle_eq B.
Proof.
  intros B H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16. constructor.
  - rewrite H7, H8. reflexivity.
  - rewrite H3, H4. reflexivity.
  - rewrite H5, H6. reflexivity.
  - rewrite H15, H16. reflexivity.
  - rewrite H9, H10. reflexivity.
  - rewrite H11, H12. reflexivity.
  - rewrite H13, H14. reflexivity.
  - rewrite H1, H2. reflexivity.
  - intros i Hi. lia.
Qed.

(* ---- settle ---- *)

Lemma settle_ok : forall I ops B ticked, agree_core I ops B -> c2_keepalive B -> settle_eq B ->
  (truth ticked = true -> drain_fact B) -> settle_m B ticked = Some (B, tt).
Proof.
  intros I ops B ticked HC HK HS HD. unfold settle_m.
  rewrite (check_ack_settle_ok B (se_acks B HS)). cbn beta iota zeta.
  rewrite (check_state_settle_ok B HS (b1_state _ (ac_st _ _ _ HC))). cbn beta iota zeta.
  rewrite (check_inflight_settle_ok I ops B HC (se_acked B HS)). cbn beta iota zeta.
  rewrite (check_keepalive_settle_ok B HK). cbn beta iota zeta.
  unfold truth at 1. destruct (Z.eqb_spec (g_raw B) 0) as [Er|Er]; cbn [negb]; [|reflexivity].
  rewrite (latest_queue_ok ops B (ac_q _ _ _ HC) Er). cbn beta iota zeta.
  destruct (truth ticked) eqn:Et; [|reflexivity].
  exact (check_latest_drain_ok I ops B HC Er (HD eq_refl)).
Qed.


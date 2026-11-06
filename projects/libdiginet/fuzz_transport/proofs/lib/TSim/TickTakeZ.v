(* tick_take_m (TickDefs.v; diginet_session.c:460-471) when take (DS:353-386) took nothing: the tick returns at
   DS:463 with take's world B1, which differs from B only in the queue array and s->queued (R_qs) and holds the
   same entries. tt_zero_ok: it ends in tick_post.
   agree_core_qsame: agree_core moves to a world that keeps every byte outside R_qs, s->queued and the entries
   s->queue[0 .. s->queued). The drain fact (FT:800-801) holds because take took nothing although the queue is not
   empty: by TakeOk.take_first (P5) the pacing refused (tt_allow B = 0) and every queued entry carries a display
   flag, and tt_allow's test is drain_allow's test (B5, A2).
   TRAP (SettleOk.v): no tactic here compares two world terms that differ. No Ltac pattern shares a metavariable
   between two places (Ltac checks a shared metavariable by conversion); every rewrite is of a left side that is
   in the goal (qs_rw finds it syntactically); no record field is closed by assumption / auto; the world reads are
   Opaque below, so a slip fails fast instead of unfolding to skipn (Z.to_nat <offset>) of a world. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links QueueFacts SimLib SendOk SettleOk
  TickDefs TakeOk TickTakeW.
Import ListNotations.
Open Scope Z_scope.

Local Opaque sub upd u_at s32_at put.

(* ---------------------------------------------------------------- the getters outside R_qs *)

(* g X1 = g X (or g X1 k = g X k) for a getter g whose bytes lie outside the region of the frame H;
   the getter's name is read from the left side only (linear patterns) *)
Local Ltac qs_one H := lazymatch goal with
  | |- sub _ _ _ = sub _ _ _ => tk_get H
  | |- ?g _ _ = _ => unfold g; tk_get H
  | |- ?g _ = _ => unfold g; tk_get H
  end.

(* the conjunctions in the context, split *)
Local Ltac qs_split := repeat match goal with
  | H : _ /\ _ |- _ => let H1 := fresh "E" in let H2 := fresh "E" in destruct H as [H1 H2]
  end.

(* rewrite with every equation E : l = _ of the context whose left side mentions B1 and occurs in the goal: the
   hypothesis is matched alone, then l (a term, not a pattern variable) is searched in the goal syntactically *)
Local Ltac qs_rw B1 := repeat match goal with
  | E : ?l = _ |- _ =>
      lazymatch l with context [B1] => lazymatch goal with |- context [l] => rewrite E end end
  end.

Lemma qs_M : forall B B1, wframe R_qs B B1 ->
  M_desk_known B1 = M_desk_known B /\ M_desk B1 = M_desk B /\ M_state B1 = M_state B /\
  M_e2_acked B1 = M_e2_acked B /\ M_e1_us B1 = M_e1_us B /\ M_foreign B1 = M_foreign B /\
  M_last_rx B1 = M_last_rx B /\ M_wake_sent B1 = M_wake_sent B /\ M_next_ka B1 = M_next_ka B /\
  M_backoff_until B1 = M_backoff_until B /\ M_last_display B1 = M_last_display B /\
  M_display_sent B1 = M_display_sent B /\ M_desk_counter_valid B1 = M_desk_counter_valid B /\
  M_desk_counter B1 = M_desk_counter B /\ M_host_counter B1 = M_host_counter B /\ M_fly_on B1 = M_fly_on B /\
  M_fly_cmd B1 = M_fly_cmd B /\ M_fly_counter B1 = M_fly_counter B /\ M_fly_retries B1 = M_fly_retries B /\
  M_fly_sent B1 = M_fly_sent B /\ M_fly_len B1 = M_fly_len B.
Proof. intros B B1 H. repeat apply conj; qs_one H. Qed.

Lemma qs_S : forall B B1, wframe R_qs B B1 ->
  S_io_ctx B1 = S_io_ctx B /\ S_io_send B1 = S_io_send B /\ S_io_recv B1 = S_io_recv B /\
  S_io_now_us B1 = S_io_now_us B /\ S_notify B1 = S_notify B /\ S_notify_ctx B1 = S_notify_ctx B /\
  S_state B1 = S_state B /\ S_desk_known B1 = S_desk_known B /\ S_desk_mac B1 = S_desk_mac B /\
  S_personality B1 = S_personality B /\ S_foreign B1 = S_foreign B /\ S_e1_named_us B1 = S_e1_named_us B /\
  S_wake_acked B1 = S_wake_acked B /\ S_wake_sent_us B1 = S_wake_sent_us B /\
  S_host_counter B1 = S_host_counter B /\ S_desk_counter B1 = S_desk_counter B /\
  S_desk_counter_valid B1 = S_desk_counter_valid B /\ S_last_rx_us B1 = S_last_rx_us B /\
  S_next_keepalive_us B1 = S_next_keepalive_us B /\ S_backoff_until_us B1 = S_backoff_until_us B /\
  S_last_display_us B1 = S_last_display_us B /\ S_display_sent B1 = S_display_sent B /\
  S_inflight B1 = S_inflight B /\ S_inflight_len B1 = S_inflight_len B /\
  S_inflight_counter B1 = S_inflight_counter B /\ S_inflight_retries B1 = S_inflight_retries B /\
  S_inflight_sent_us B1 = S_inflight_sent_us B.
Proof. intros B B1 H. repeat apply conj; qs_one H. Qed.

Lemma qs_C : forall B B1, wframe R_qs B B1 ->
  Cfg_host_mac B1 = Cfg_host_mac B /\ Cfg_desk_mac B1 = Cfg_desk_mac B /\
  Cfg_desk_mac_set B1 = Cfg_desk_mac_set B /\ Cfg_auto_wake B1 = Cfg_auto_wake B /\
  Cfg_sum_mode B1 = Cfg_sum_mode B /\ Cfg_keepalive_ms B1 = Cfg_keepalive_ms B /\
  Cfg_ack_timeout_ms B1 = Cfg_ack_timeout_ms B /\ Cfg_max_retries B1 = Cfg_max_retries B /\
  Cfg_backoff_ms B1 = Cfg_backoff_ms B /\ Cfg_offline_ms B1 = Cfg_offline_ms B /\
  Cfg_wake_timeout_ms B1 = Cfg_wake_timeout_ms B /\ Cfg_display_gap_us B1 = Cfg_display_gap_us B /\
  Cfg_max_cmds B1 = Cfg_max_cmds B /\ Cfg_max_body B1 = Cfg_max_body B /\
  sub B1 A_S_cfg_host_mac 60 = sub B A_S_cfg_host_mac 60 /\ sub B1 OFF_g_cfg 60 = sub B OFF_g_cfg 60.
Proof. intros B B1 H. repeat apply conj; qs_one H. Qed.

Lemma qs_G : forall B B1, wframe R_qs B B1 ->
  g_now B1 = g_now B /\ g_raw B1 = g_raw B /\ g_ncmd B1 = g_ncmd B /\ g_nq B1 = g_nq B /\
  g_fail_next B1 = g_fail_next B.
Proof. intros B B1 H. repeat apply conj; qs_one H. Qed.

Lemma qs_fail : forall B B1, wframe R_qs B B1 -> g_fail_next B1 = g_fail_next B.
Proof. intros B B1 H. qs_one H. Qed.

Lemma qs_Q : forall B B1 i, wframe R_qs B B1 -> 0 <= i -> Q_at B1 i = Q_at B i.
Proof. intros B B1 i H Hi. unfold Q_at. tk_get H. Qed.

Lemma qs_cmd : forall B B1 k, wframe R_qs B B1 -> 0 <= k ->
  Cmd_st B1 k = Cmd_st B k /\ Cmd_key B1 k = Cmd_key B k /\ Cmd_display B1 k = Cmd_display B k /\
  Cmd_bytes B1 k = Cmd_bytes B k /\ Cmd_len B1 k = Cmd_len B k.
Proof. intros B B1 k H Hk. repeat apply conj; qs_one H. Qed.

Lemma Q_nonneg : forall B i, 0 <= Q_at B i.
Proof. intros B i. unfold Q_at. apply u_at_nonneg. Qed.

(* the frame in flight, both copies, of at most SPEC_MAX_FRAME bytes *)
Lemma qs_fly_frames : forall B B1 n, wframe R_qs B B1 -> Z.of_nat n <= 1514 ->
  sub B1 A_M_fly_frame n = sub B A_M_fly_frame n /\ sub B1 A_S_inflight_frame n = sub B A_S_inflight_frame n.
Proof. intros B B1 n H Hn. split; tk_get H. Qed.

Lemma qs_frame_len : forall n, (n <= 1484)%nat -> Z.of_nat (Z.to_nat (frame_len n)) <= 1514.
Proof. intros n Hn. unfold frame_len. rewrite Z2Nat.id by lia. lia. Qed.

(* the fields of one queue entry *)
Lemma qs_ent_fields : forall B B1 i, 0 <= i -> sq_ent B1 i = sq_ent B i ->
  S_queue_bytes B1 i = S_queue_bytes B i /\ S_queue_len B1 i = S_queue_len B i /\
  S_queue_display B1 i = S_queue_display B i /\ S_queue_key B1 i = S_queue_key B i.
Proof.
  intros B B1 i Hi He.
  rewrite (S_queue_bytes_ent B1 i Hi), (S_queue_bytes_ent B i Hi), (S_queue_len_ent B1 i Hi),
    (S_queue_len_ent B i Hi), (S_queue_display_ent B1 i Hi), (S_queue_display_ent B i Hi),
    (S_queue_key_ent B1 i Hi), (S_queue_key_ent B i Hi), He.
  repeat apply conj; reflexivity.
Qed.

Lemma qs_ent_of_sq : forall B B1, sq B1 = sq B -> S_queued B1 = S_queued B ->
  forall i, 0 <= i < S_queued B -> sq_ent B1 i = sq_ent B i.
Proof.
  intros B B1 Hsq Hq i Hi.
  assert (Hi1 : 0 <= i < S_queued B1) by (rewrite Hq; exact Hi).
  rewrite <- (tk_sq_nth B1 i [] Hi1), <- (tk_sq_nth B i [] Hi), Hsq. reflexivity.
Qed.

Lemma qs_drain_allow : forall B B1, wframe R_qs B B1 -> drain_allow B1 = drain_allow B.
Proof.
  intros B B1 H.
  assert (E1 : M_display_sent B1 = M_display_sent B) by qs_one H.
  assert (E2 : Cfg_display_gap_us B1 = Cfg_display_gap_us B) by qs_one H.
  assert (E3 : g_now B1 = g_now B) by qs_one H.
  assert (E4 : M_last_display B1 = M_last_display B) by qs_one H.
  unfold drain_allow. rewrite E1, E2, E3, E4. reflexivity.
Qed.

Lemma R_qs_tick : forall a, R_qs a -> R_tick a.
Proof. intros a H. tk_offs. Qed.

(* ---------------------------------------------------------------- agree_core moves to B1 *)

Lemma agree_core_qsame : forall I ops B B1, agree_core I ops B -> length B1 = WN -> wframe R_qs B B1 ->
  S_queued B1 = S_queued B -> (forall i, 0 <= i < S_queued B -> sq_ent B1 i = sq_ent B i) -> agree_core I ops B1.
Proof.
  intros I ops B B1 HC Hlen Hfr Hq Hent.
  pose proof (ac_cfg _ _ _ HC) as Hc. pose proof (ac_io _ _ _ HC) as Hio. pose proof (ac_st _ _ _ HC) as Hs.
  pose proof (ac_fly _ _ _ HC) as Hf. pose proof (ac_time _ _ _ HC) as Ht. pose proof (ac_q _ _ _ HC) as HQ.
  pose proof (ac_misc _ _ _ HC) as Hm.
  pose proof (qs_M B B1 Hfr). pose proof (qs_S B B1 Hfr). pose proof (qs_C B B1 Hfr). pose proof (qs_G B B1 Hfr).
  qs_split.
  constructor.
  - exact (ac_img _ _ _ HC).
  - unfold WN in Hlen. exact Hlen.
  - constructor; qs_rw B1.
    + exact (a1_max_retries _ Hc).
    + exact (a1_ack_timeout _ Hc).
    + exact (a1_keepalive _ Hc).
    + exact (a1_backoff _ Hc).
    + exact (a1_offline _ Hc).
    + exact (a1_wake_timeout _ Hc).
    + exact (a1_display_gap _ Hc).
    + exact (a1_max_cmds _ Hc).
    + exact (a1_max_body _ Hc).
    + exact (a1_host_mac _ Hc).
    + exact (a1_desk_mac _ Hc).
    + exact (a1_desk_mac_set _ Hc).
    + exact (a1_auto_wake _ Hc).
    + exact (a1_sum_mode _ Hc).
    + exact (a2_cfg _ Hc).
    + exact (a4_raw _ Hc).
  - constructor; qs_rw B1.
    + exact (a3_io_ctx _ _ Hio).
    + exact (a3_io_send _ _ Hio).
    + exact (a3_io_recv _ _ Hio).
    + exact (a3_io_now _ _ Hio).
    + exact (a3_notify _ _ Hio).
    + exact (a3_notify_ctx _ _ Hio).
  - constructor; qs_rw B1.
    + exact (b1_state _ Hs).
    + exact (b1_state_range _ Hs).
    + exact (b2_desk_known _ Hs).
    + exact (b2_desk_known01 _ Hs).
    + exact (b2_desk_mac _ Hs).
    + exact (b3_foreign _ Hs).
    + exact (b3_foreign01 _ Hs).
    + exact (b3_e1 _ Hs).
    + exact (b3_e1_01 _ Hs).
    + exact (b3_e2 _ Hs).
    + exact (b3_e2_01 _ Hs).
    + exact (b4_wake_sent _ Hs).
    + exact (b4_last_rx _ Hs).
    + exact (b4_backoff _ Hs).
    + exact (b5_next_ka _ Hs).
    + exact (b5_display_sent _ Hs).
    + exact (b5_display_sent01 _ Hs).
    + exact (b5_last_display _ Hs).
    + exact (b6_valid _ Hs).
    + exact (b6_valid01 _ Hs).
    + exact (b6_counter _ Hs).
    + exact (b7_host_counter _ Hs).
    + exact (b9_idle _ Hs).
    + exact (b9_known _ Hs).
  - constructor; qs_rw B1.
    + exact (b8_on _ Hf).
    + exact (b8_on01 _ Hf).
    + exact (b8_state _ Hf).
    + exact (b8_counter _ Hf).
    + exact (b8_counter_host _ Hf).
    + exact (b8_retries _ Hf).
    + exact (b8_retries_le _ Hf).
    + exact (b8_sent _ Hf).
    + exact (b8_len _ Hf).
    + exact (b8_cmd _ Hf).
    + intros Hon. destruct (b8_frames _ Hf Hon) as (body & nc & H1 & H2 & H3 & H4 & H5 & H6).
      assert (Hn : Z.of_nat (Z.to_nat (M_fly_len B)) <= 1514) by (rewrite H4; exact (qs_frame_len _ H1)).
      destruct (qs_fly_frames B B1 (Z.to_nat (M_fly_len B)) Hfr Hn) as [F1 F2].
      exists body, nc. rewrite F1, F2. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
  - constructor; qs_rw B1.
    + exact (c_now _ _ Ht).
    + exact (c1_last_rx _ _ Ht).
    + exact (c1_wake_sent _ _ Ht).
    + exact (c1_fly_sent _ _ Ht).
    + exact (c1_last_display _ _ Ht).
    + exact (c1_backoff _ _ Ht).
    + exact (c1_next_ka _ _ Ht).
    + exact (c2_wake _ _ Ht).
    + exact (c2_online _ _ Ht).
    + exact (c2_fly _ _ Ht).
  - constructor; qs_rw B1.
    + exact (d1_queued _ _ HQ).
    + exact (d1_nq _ _ HQ).
    + intros Hr i Hi. rewrite (qs_Q B B1 i Hfr (proj1 Hi)).
      destruct (qs_cmd B B1 (Q_at B i) Hfr (Q_nonneg B i)) as (C1 & C2 & C3 & C4 & C5).
      assert (Hiq : 0 <= i < S_queued B) by (rewrite (d1_queued _ _ HQ Hr); exact Hi).
      destruct (qs_ent_fields B B1 i (proj1 Hi) (Hent i Hiq)) as (F1 & F2 & F3 & F4).
      qs_rw B1. exact (d1_entry _ _ HQ Hr i Hi).
    + intros Hr i j Hi Hj Hij.
      rewrite (qs_Q B B1 i Hfr (proj1 Hi)), (qs_Q B B1 j Hfr (proj1 Hj)) in Hij.
      exact (d1_nodup _ _ HQ Hr i j Hi Hj Hij).
    + intros Hr k Hk. rewrite (proj1 (qs_cmd B B1 k Hfr (proj1 Hk))).
      destruct (d1_pending _ _ HQ Hr k Hk) as [P1 P2]. split.
      * intros Hp. destruct (P1 Hp) as [i [Hi Hqi]]. exists i. split; [exact Hi|].
        rewrite (qs_Q B B1 i Hfr (proj1 Hi)). exact Hqi.
      * intros [i [Hi Hqi]]. apply P2. exists i. split; [exact Hi|].
        rewrite (qs_Q B B1 i Hfr (proj1 Hi)) in Hqi. exact Hqi.
    + intros k Hk Hst. destruct (qs_cmd B B1 k Hfr (proj1 Hk)) as (C1 & C2 & C3 & C4 & C5).
      rewrite C1 in Hst. qs_rw B1. exact (d2_cmd _ _ HQ k Hk Hst).
    + exact (d3_ncmd _ _ HQ).
    + exact (d3_ops _ _ HQ).
    + exact (d4_queued _ _ HQ).
    + intros Hr i Hi. destruct (qs_ent_fields B B1 i (proj1 Hi) (Hent i Hi)) as (F1 & F2 & F3 & F4).
      qs_rw B1. exact (d4_entry _ _ HQ Hr i Hi).
  - constructor; qs_rw B1.
    + exact (e1_fail_next _ _ Hm).
    + exact (e2_personality _ _ Hm).
Qed.

(* ---------------------------------------------------------------- take took nothing *)

(* P5 contrapositive: the pacing refused and every queued entry carries a display flag *)
Lemma tz_none : forall B, agree_cfg B ->
  Forall (fun e => length e = 32%nat /\ 1 <= e_len e <= 24 /\ body_check (e_bytes e) = 0) (sq B) ->
  tt_T B (tt_mask B) = [] -> forall e, In e (sq B) -> tt_allow B = 0 /\ e_disp e <> 0.
Proof.
  intros B Hc HF HT e He.
  assert (Hc1 : 1 <= S_cfg_max_cmds B) by (rewrite (tk_cfg_max_cmds B Hc); exact (proj1 (a1_max_cmds _ Hc))).
  assert (Hb1 : 24 <= S_cfg_max_body B) by (rewrite (tk_cfg_max_body B Hc); exact (proj1 (a1_max_body _ Hc))).
  unfold tt_T, tt_mask in HT.
  destruct (Z.eq_dec (tt_allow B) 0) as [Ha|Ha].
  - split; [exact Ha|]. intros Hd.
    exact (take_first (S_cfg_max_cmds B) (S_cfg_max_body B) (tt_allow B) (sq B) Hc1 Hb1 HF
             (ex_intro _ e (conj He (or_intror Hd))) HT).
  - exfalso.
    exact (take_first (S_cfg_max_cmds B) (S_cfg_max_body B) (tt_allow B) (sq B) Hc1 Hb1 HF
             (ex_intro _ e (conj He (or_introl Ha))) HT).
Qed.

(* tt_allow (DS:460) is check_latest_drain's pacing drain_allow (FT:787), tagged *)
Lemma tz_allow : forall B, agree_cfg B -> agree_st B -> g_raw B = 0 -> tt_allow B = 0 -> drain_allow B = false.
Proof.
  intros B Hc Hs Hr H. unfold tt_allow in H. unfold drain_allow.
  rewrite <- (b5_display_sent _ Hs Hr), <- (b5_last_display _ Hs Hr), <- (tk_cfg_display_gap B Hc).
  revert H. unfold truth.
  destruct (S_display_sent B =? 0); cbn [negb orb int_of_bool]; [intros H; discriminate H|].
  destruct (S_cfg_display_gap_us B <=? u64 (g_now B - S_last_display_us B)); cbn [int_of_bool];
    intros H; [discriminate H | reflexivity].
Qed.

Lemma tz_drain : forall I ops B, agree_core I ops B -> g_raw B = 0 ->
  Forall (fun e => length e = 32%nat /\ 1 <= e_len e <= 24 /\ body_check (e_bytes e) = 0) (sq B) ->
  tt_T B (tt_mask B) = [] ->
  forall i, 0 <= i < g_nq B -> negb (truth (Cmd_display B (Q_at B i))) || drain_allow B = false.
Proof.
  intros I ops B HC Hr HF HT i Hi.
  pose proof (ac_q _ _ _ HC) as HQ.
  assert (Hiq : 0 <= i < S_queued B) by (rewrite (d1_queued _ _ HQ Hr); exact Hi).
  destruct (d1_entry _ _ HQ Hr i Hi) as (_ & _ & _ & _ & _ & Hd).
  assert (Hin : In (sq_ent B i) (sq B))
    by (apply (proj2 (tk_In_sq B (sq_ent B i))); exists i; split; [exact Hiq | reflexivity]).
  destruct (tz_none B (ac_cfg _ _ _ HC) HF HT (sq_ent B i) Hin) as [Ha He].
  rewrite <- Hd, (S_queue_display_ent B i (proj1 Hi)).
  rewrite (tz_allow B (ac_cfg _ _ _ HC) (ac_st _ _ _ HC) Hr Ha).
  unfold truth. unfold e_disp in He.
  destruct (Z.eqb_spec (cmd_display_of (sq_ent B i)) 0) as [E|E]; [exact (False_ind _ (He E)) | reflexivity].
Qed.

Lemma tz_drain_fact : forall I ops B B1, agree_core I ops B -> wframe R_qs B B1 ->
  Forall (fun e => length e = 32%nat /\ 1 <= e_len e <= 24 /\ body_check (e_bytes e) = 0) (sq B) ->
  tt_T B (tt_mask B) = [] -> drain_fact B1.
Proof.
  intros I ops B B1 HC Hfr HF HT.
  assert (E1 : g_raw B1 = g_raw B) by qs_one Hfr.
  assert (E2 : M_state B1 = M_state B) by qs_one Hfr.
  assert (E3 : M_fly_on B1 = M_fly_on B) by qs_one Hfr.
  assert (E4 : M_backoff_until B1 = M_backoff_until B) by qs_one Hfr.
  assert (E5 : g_now B1 = g_now B) by qs_one Hfr.
  assert (E6 : g_nq B1 = g_nq B) by qs_one Hfr.
  unfold drain_fact. rewrite E1, E2, E3, E4, E5, E6, (qs_drain_allow B B1 Hfr).
  intros Hr _ _ _ i Hi.
  rewrite (qs_Q B B1 i Hfr (proj1 Hi)).
  destruct (qs_cmd B B1 (Q_at B i) Hfr (Q_nonneg B i)) as (_ & _ & C3 & _ & _).
  rewrite C3.
  exact (tz_drain I ops B HC Hr HF HT i Hi).
Qed.

Lemma tz_keepalive : forall B B1, agree_st B -> wframe R_qs B B1 -> g_now B < S_next_keepalive_us B ->
  c2_keepalive B1.
Proof.
  intros B B1 Hs Hfr Hka.
  assert (E1 : g_raw B1 = g_raw B) by qs_one Hfr.
  assert (E2 : M_state B1 = M_state B) by qs_one Hfr.
  assert (E3 : M_fly_on B1 = M_fly_on B) by qs_one Hfr.
  assert (E4 : M_backoff_until B1 = M_backoff_until B) by qs_one Hfr.
  assert (E5 : g_now B1 = g_now B) by qs_one Hfr.
  assert (E6 : M_next_ka B1 = M_next_ka B) by qs_one Hfr.
  unfold c2_keepalive. rewrite E1, E2, E3, E4, E5, E6.
  intros Hr _ _ _. rewrite <- (b5_next_ka _ Hs Hr). exact Hka.
Qed.

(* ---------------------------------------------------------------- the n = 0 case *)

Lemma tt_zero_ok : forall I ops B B1, agree_core I ops B ->
  S_state B = DIGINET_S_ONLINE -> S_inflight B = 0 -> S_backoff_until_us B <= g_now B ->
  g_now B < S_next_keepalive_us B -> S_queued B <> 0 ->
  Forall (fun e => length e = 32%nat /\ 1 <= e_len e <= 24 /\ body_check (e_bytes e) = 0) (sq B) ->
  tt_T B (tt_mask B) = [] ->
  length B1 = WN -> wframe R_qs B B1 -> sq B1 = sq B -> S_queued B1 = S_queued B ->
  tick_post I ops B B1.
Proof.
  intros I ops B B1 HC _ _ _ Hka _ HF HT Hlen Hfr Hsq Hq.
  constructor.
  - exact (agree_core_qsame I ops B B1 HC Hlen Hfr Hq (qs_ent_of_sq B B1 Hsq Hq)).
  - exact (tz_keepalive B B1 (ac_st _ _ _ HC) Hfr Hka).
  - exact (tz_drain_fact I ops B B1 HC Hfr HF HT).
  - exact (wframe_weaken R_qs R_tick B B1 R_qs_tick Hfr).
  - left. exact (qs_fail B B1 Hfr).
Qed.

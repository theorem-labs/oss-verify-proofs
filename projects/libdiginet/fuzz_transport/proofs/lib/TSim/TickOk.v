(* tick_tail_ok: the tail of the tick (DS:445-471) from agree_core at the current time: tick_post.
   tick_quiet_ok: the whole tick at the current time from agree_core (C2 at that time: no timeout fires, nothing in
   flight is overdue): tick_post. This is the tick inside diginet_session_rx (DS:317) and poll (DS:522).
   tick_tail_keep / tick_quiet_keep: the same, and M.state, M.desk_known, M.desk (world bytes 0..15) are kept:
   the keepalive path writes inside ka_W, the take-and-send path inside R_tt, every other path returns its world
   (keep_of_frame). tick_tail_ok / tick_quiet_ok are their tick_post parts.
   Pieces: TickKa.v (keepalive), TickTake.v (take and send). Op 3 is Op3Ok.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import
  TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import
  Agree Links QueueFacts SettleOk Deadline SimLib TickDefs TickKa TickTake.
Import ListNotations.
Open Scope Z_scope.

Lemma tick_post_same : forall I ops B, agree_core I ops B -> c2_keepalive B -> drain_fact B -> tick_post I ops B B.
Proof.
  intros I ops B HC HK HD. constructor; [exact HC | exact HK | exact HD | apply wframe_refl | left; reflexivity].
Qed.

(* M.state, M.desk_known, M.desk lie in world bytes 0..15 *)
Lemma keep_of_frame : forall (R : Z -> Prop) B B', wframe R B B' -> (forall a, 0 <= a < 16 -> ~ R a) ->
  M_state B' = M_state B /\ M_desk_known B' = M_desk_known B /\ M_desk B' = M_desk B.
Proof.
  intros R B B' Hw HR. unfold M_state, M_desk_known, M_desk, A_M_state, A_M_desk_known, A_M_desk, OFF_M.
  split; [|split].
  - apply (wframe_s32_at R B B' _ Hw); [lia|]. intros a Ha. apply HR. lia.
  - apply (wframe_s32_at R B B' _ Hw); [lia|]. intros a Ha. apply HR. lia.
  - apply (wframe_sub R B B' _ 6 Hw); [lia|]. intros a Ha. apply HR. change (Z.of_nat 6) with 6 in Ha. lia.
Qed.

Lemma keep_refl : forall B, M_state B = M_state B /\ M_desk_known B = M_desk_known B /\ M_desk B = M_desk B.
Proof. intros B. split; [|split]; reflexivity. Qed.

Lemma tick_tail_keep : forall (HL : links) I F ops B, agree_core I ops B ->
  exists B' r, tick_tail_m I F B (g_now B) = Some (B', r) /\ tick_post I ops B B' /\
    M_state B' = M_state B /\ M_desk_known B' = M_desk_known B /\ M_desk B' = M_desk B.
Proof.
  intros HL I F ops B HC.
  pose proof (ac_st _ _ _ HC) as HS. pose proof (ac_fly _ _ _ HC) as HF. pose proof (ac_q _ _ _ HC) as HQ.
  pose proof (b1_state _ HS) as E1. pose proof (b8_on _ HF) as E8. pose proof (b4_backoff _ HS) as E4.
  unfold tick_tail_m.
  destruct (Z.eqb_spec (S_state B) DIGINET_S_ONLINE) as [Es|Es]; cbn [negb orb].
  2:{ exists B, DIGINET_OK. split; [reflexivity|]. split; [|apply keep_refl]. apply tick_post_same; [exact HC| |].
      - intros _ Hm. exfalso. apply Es. rewrite E1, Hm. reflexivity.
      - intros _ Hm. exfalso. apply Es. rewrite E1, Hm. reflexivity. }
  destruct (Z.eqb_spec (S_inflight B) 0) as [Ei|Ei]; cbn [negb orb].
  2:{ exists B, DIGINET_OK. split; [reflexivity|]. split; [|apply keep_refl]. apply tick_post_same; [exact HC| |].
      - intros _ _ Hf. exfalso. apply Ei. rewrite E8, Hf. reflexivity.
      - intros _ _ Hf. exfalso. apply Ei. rewrite E8, Hf. reflexivity. }
  destruct (Z.ltb_spec (g_now B) (S_backoff_until_us B)) as [Eb|Eb].
  { exists B, DIGINET_OK. split; [reflexivity|]. split; [|apply keep_refl]. apply tick_post_same; [exact HC| |].
    - intros _ _ _ Hb. rewrite E4 in Eb. lia.
    - intros _ _ _ Hb. rewrite E4 in Eb. lia. }
  destruct (Z.leb_spec (S_next_keepalive_us B) (g_now B)) as [Ek|Ek].
  { destruct (tick_ka_keep HL I F ops B HC Es Ei Eb Ek) as (B' & r & E & Hp & HW).
    exists B', r. split; [exact E|]. split; [exact Hp | exact (keep_of_frame _ B B' HW ka_W_low)]. }
  destruct (Z.eqb_spec (S_queued B) 0) as [Eq|Eq].
  { exists B, DIGINET_OK. split; [reflexivity|]. split; [|apply keep_refl]. apply tick_post_same; [exact HC| |].
    - intros Hr _ _ _. rewrite <- (b5_next_ka _ HS Hr). exact Ek.
    - intros Hr _ _ _ i Hi. rewrite <- (d1_queued _ _ HQ Hr), Eq in Hi. lia. }
  destruct (tick_take_keep HL I F ops B HC Es Ei Eb Ek Eq) as (B' & r & E & Hp & HW).
  exists B', r. split; [exact E|]. split; [exact Hp | exact (keep_of_frame _ B B' HW R_tt_low)].
Qed.

Lemma tick_tail_ok : forall (HL : links) I F ops B, agree_core I ops B ->
  exists B' r, tick_tail_m I F B (g_now B) = Some (B', r) /\ tick_post I ops B B'.
Proof.
  intros HL I F ops B HC.
  destruct (tick_tail_keep HL I F ops B HC) as (B' & r & E & Hp & _). exists B', r. exact (conj E Hp).
Qed.

(* ---- the tick at an unchanged time ---- *)

Lemma post_not_online : forall I ops B, agree_core I ops B -> M_state B <> S_ONLINE -> tick_post I ops B B.
Proof.
  intros I ops B HC Hn. apply tick_post_same; [exact HC | |].
  - intros _ Hm. exact (False_ind _ (Hn Hm)).
  - intros _ Hm. exact (False_ind _ (Hn Hm)).
Qed.

(* now = g_now B is at most 1000000 + 1024 * 65535000000 < 2^47 (c_now, d3_ops) *)
Lemma now_small : forall I ops B, agree_core I ops B -> 0 <= g_now B < 2 ^ 47.
Proof.
  intros I ops B HC. pose proof (c_now _ _ (ac_time _ _ _ HC)) as Hn. pose proof (d3_ops _ _ (ac_q _ _ _ HC)) as Ho.
  pose proof (u_at_range B OFF_g_now 8) as Hr. change (8 * Z.of_nat 8) with 64 in Hr.
  unfold g_now in *. unfold OPS_MAX in Ho. lia.
Qed.

(* the step of DS:430-443 does nothing when what is in flight is not overdue (C2's fly clause) *)
Lemma tick_step_quiet : forall I F ops B, agree_core I ops B -> tick_step_m I F B (g_now B) = Some (inr B).
Proof.
  intros I F ops B HC. pose proof (ac_fly _ _ _ HC) as HF. pose proof (ac_time _ _ _ HC) as HT.
  pose proof (ac_cfg _ _ _ HC) as HG. pose proof (now_small _ _ _ HC) as Hn.
  unfold tick_step_m.
  destruct (Z.eqb_spec (S_inflight B) 0) as [Ei|Ei]; cbn [negb andb]; [reflexivity|].
  rewrite (b8_on _ HF) in Ei.
  assert (Hon : M_fly_on B = 1) by (destruct (b8_on01 _ HF) as [E|E]; [exact (False_ind _ (Ei E)) | exact E]).
  pose proof (c2_fly _ _ HT Hon) as Hc. pose proof (c1_fly_sent _ _ HT Hon) as Hs.
  pose proof (a1_ack_timeout _ HG) as Ha. pose proof (u_at_range B A_M_fly_sent 8) as Hr.
  change (8 * Z.of_nat 8) with 64 in Hr.
  rewrite (a2_ack_timeout B HG), (b8_sent _ HF Hon), (ms_small (Cfg_ack_timeout_ms B) ltac:(lia)).
  unfold M_fly_sent in *.
  rewrite (u64_small (g_now B - u_at B A_M_fly_sent 8) ltac:(lia)).
  destruct (Z.leb_spec (1000 * Cfg_ack_timeout_ms B) (g_now B - u_at B A_M_fly_sent 8)); [lia | reflexivity].
Qed.

(* the tick at an unchanged time when the session is not ONLINE: nothing times out (C2), nothing is overdue in
   flight, and the tail (DS:445-447) sends nothing; the world is unchanged *)
Lemma tick_quiet_off : forall I F ops B, agree_core I ops B -> M_state B <> S_ONLINE ->
  diginet_session_tick_m I F B (g_now B) = Some (B, DIGINET_OK).
Proof.
  intros I F ops B HC Hno.
  pose proof (ac_st _ _ _ HC) as HS. pose proof (ac_time _ _ _ HC) as HT. pose proof (ac_cfg _ _ _ HC) as HG.
  pose proof (b1_state _ HS) as E1. pose proof (now_small _ _ _ HC) as Hn.
  rewrite tick_unfold.
  destruct (Z.eqb_spec (S_state B) DIGINET_S_CLOSED) as [Ec|Ec]; cbn [orb]; [reflexivity|].
  destruct (Z.eqb_spec (S_state B) DIGINET_S_IDLE) as [Ei|Ei]; cbn [orb]; [reflexivity|].
  assert (Ho : (S_state B =? DIGINET_S_ONLINE) = false).
  { apply Z.eqb_neq. intros Eo. apply Hno. rewrite <- E1, Eo. reflexivity. }
  destruct (Z.eqb_spec (S_state B) DIGINET_S_WAKING) as [Ew|Ew]; cbn [andb].
  { assert (Hm : M_state B = S_WAKING) by (rewrite <- E1, Ew; reflexivity).
    pose proof (c2_wake _ _ HT Hm) as Hc.
    pose proof (c1_wake_sent _ _ HT) as Hs. pose proof (a1_wake_timeout _ HG) as Ha.
    pose proof (u_at_range B A_M_wake_sent 8) as Hr. change (8 * Z.of_nat 8) with 64 in Hr.
    rewrite (a2_wake_timeout B HG), (b4_wake_sent _ HS), (ms_small (Cfg_wake_timeout_ms B) ltac:(lia)).
    unfold M_wake_sent in *.
    rewrite (u64_small (g_now B - u_at B A_M_wake_sent 8) ltac:(lia)).
    destruct (Z.leb_spec (1000 * Cfg_wake_timeout_ms B) (g_now B - u_at B A_M_wake_sent 8)); [lia|].
    rewrite Ho. cbn [andb]. rewrite (tick_step_quiet I F ops B HC). cbv beta iota.
    unfold tick_tail_m. rewrite Ho. cbv beta iota delta [negb orb]. reflexivity. }
  rewrite Ho. cbn [andb]. rewrite (tick_step_quiet I F ops B HC). cbv beta iota.
  unfold tick_tail_m. rewrite Ho. cbv beta iota delta [negb orb]. reflexivity.
Qed.

Lemma tick_quiet_keep : forall (HL : links) I F ops B, agree_core I ops B ->
  exists B' r, diginet_session_tick_m I F B (g_now B) = Some (B', r) /\ tick_post I ops B B' /\
    M_state B' = M_state B /\ M_desk_known B' = M_desk_known B /\ M_desk B' = M_desk B.
Proof.
  intros HL I F ops B HC.
  pose proof (ac_st _ _ _ HC) as HS. pose proof (ac_time _ _ _ HC) as HT. pose proof (ac_cfg _ _ _ HC) as HG.
  pose proof (b1_state _ HS) as E1. pose proof (now_small _ _ _ HC) as Hn.
  rewrite tick_unfold.
  destruct (Z.eqb_spec (S_state B) DIGINET_S_CLOSED) as [Ec|Ec]; cbn [orb].
  { exists B, DIGINET_OK. split; [reflexivity|]. split; [|apply keep_refl]. apply post_not_online; [exact HC|].
    intros Hm. rewrite <- E1, Ec in Hm. unfold DIGINET_S_CLOSED, S_ONLINE in Hm. lia. }
  destruct (Z.eqb_spec (S_state B) DIGINET_S_IDLE) as [Ei|Ei]; cbn [orb].
  { exists B, DIGINET_OK. split; [reflexivity|]. split; [|apply keep_refl]. apply post_not_online; [exact HC|].
    intros Hm. rewrite <- E1, Ei in Hm. unfold DIGINET_S_IDLE, S_ONLINE in Hm. lia. }
  destruct (Z.eqb_spec (S_state B) DIGINET_S_WAKING) as [Ew|Ew]; cbn [andb].
  { assert (Hm : M_state B = S_WAKING) by (rewrite <- E1, Ew; reflexivity).
    pose proof (c2_wake _ _ HT Hm) as Hc.
    pose proof (c1_wake_sent _ _ HT) as Hs. pose proof (a1_wake_timeout _ HG) as Ha.
    pose proof (u_at_range B A_M_wake_sent 8) as Hr. change (8 * Z.of_nat 8) with 64 in Hr.
    rewrite (a2_wake_timeout B HG), (b4_wake_sent _ HS), (ms_small (Cfg_wake_timeout_ms B) ltac:(lia)).
    unfold M_wake_sent in *.
    rewrite (u64_small (g_now B - u_at B A_M_wake_sent 8) ltac:(lia)).
    destruct (Z.leb_spec (1000 * Cfg_wake_timeout_ms B) (g_now B - u_at B A_M_wake_sent 8)); [lia|].
    assert (Ho : (S_state B =? DIGINET_S_ONLINE) = false) by (rewrite Ew; reflexivity).
    rewrite Ho. cbn [andb]. rewrite (tick_step_quiet I F ops B HC). cbn beta iota.
    exact (tick_tail_keep HL I F ops B HC). }
  destruct (Z.eqb_spec (S_state B) DIGINET_S_ONLINE) as [Eo|Eo]; cbn [andb].
  { assert (Hm : M_state B = S_ONLINE) by (rewrite <- E1, Eo; reflexivity).
    pose proof (c2_online _ _ HT Hm) as Hc.
    pose proof (c1_last_rx _ _ HT) as Hs. pose proof (a1_offline _ HG) as Ha.
    pose proof (u_at_range B A_M_last_rx 8) as Hr. change (8 * Z.of_nat 8) with 64 in Hr.
    rewrite (a2_offline B HG), (b4_last_rx _ HS), (ms_small (Cfg_offline_ms B) ltac:(lia)).
    unfold M_last_rx in *.
    rewrite (u64_small (g_now B - u_at B A_M_last_rx 8) ltac:(lia)).
    destruct (Z.leb_spec (1000 * Cfg_offline_ms B) (g_now B - u_at B A_M_last_rx 8)); [lia|].
    cbn [andb]. rewrite (tick_step_quiet I F ops B HC). cbn beta iota.
    exact (tick_tail_keep HL I F ops B HC). }
  rewrite (tick_step_quiet I F ops B HC). cbn beta iota.
  exact (tick_tail_keep HL I F ops B HC).
Qed.

Lemma tick_quiet_ok : forall (HL : links) I F ops B, agree_core I ops B ->
  exists B' r, diginet_session_tick_m I F B (g_now B) = Some (B', r) /\ tick_post I ops B B'.
Proof.
  intros HL I F ops B HC.
  destruct (tick_quiet_keep HL I F ops B HC) as (B' & r & E & Hp & _). exists B', r. exact (conj E Hp).
Qed.

(* diginet_session_deadline (DS:476-503, TSess0.v) read at now = g_now B in a world where agree_core holds is
   Some d with now <= d <= now + 10^6, and d <= fly_sent + ms(ack_timeout_ms) while a frame is in flight; so
   check_inflight_settle (FT:744-771) passes once the operation's OW.acked and GOT.acked agree.
   d >= now: the in-flight branch returns min64 of now + 10^6, the
   WAKING term wake_sent + ms(wake_timeout_ms), the ONLINE term last_rx + ms(offline_ms) and the in-flight term
   inflight_sent + ms(ack_timeout_ms) without the clamp of DS:502, and each is > now by C1 and C2 (WAKING,
   ONLINE, fly); IDLE / CLOSED return now + 10^6 at DS:479-480; every other path ends in the clamp. The queue
   walk of DS:495-497 stays inside s->queue[512] because s->queued <= 512 (D1 tagged, D4 raw). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree SimLib.
Import ListNotations.
Open Scope Z_scope.

Lemma min64_eq : forall a b, min64_m a b = Z.min a b.
Proof. intros a b. unfold min64_m. destruct (Z.ltb_spec a b); lia. Qed.

Lemma u64_small : forall x, 0 <= x < 18446744073709551616 -> u64 x = x.
Proof. intros x Hx. unfold u64. apply Z.mod_small. exact Hx. Qed.

Lemma ms_small : forall v, 0 <= v <= 65536 -> ms_m v = 1000 * v.
Proof. intros v Hv. unfold ms_m. rewrite u64_small by lia. lia. Qed.

Lemma h_ms_small : forall v, 0 <= v <= 65536 -> h_ms_m v = 1000 * v.
Proof. intros v Hv. unfold h_ms_m. rewrite u64_small by lia. lia. Qed.

(* the walk of DS:495-497 from i with fuel turns stays below 512 *)
Lemma display_only_some : forall B fuel i dsp, 0 <= i -> i + Z.of_nat fuel <= S_queue_N ->
  exists r, deadline_display_only_m B i dsp fuel = Some r.
Proof.
  intros B fuel. induction fuel as [|fuel IH]; intros i dsp Hi Hf; cbn [deadline_display_only_m].
  - eauto.
  - destruct (dsp =? 0); [eauto|].
    destruct (Z.leb_spec S_queue_N i); [lia|].
    apply IH; lia.
Qed.

(* s->queued <= 512 under agree_q, in both modes *)
Lemma queued_le : forall ops B, agree_q ops B -> 0 <= S_queued B <= QUEUE_MAX.
Proof.
  intros ops B Hq. split; [unfold S_queued; pose proof (u_at_range B A_S_queued 4); lia|].
  destruct (Z.eq_dec (g_raw B) 0) as [R|R].
  - rewrite (d1_queued _ _ Hq R). exact (d1_nq _ _ Hq R).
  - exact (d4_queued _ _ Hq R).
Qed.

Theorem deadline_ok : forall I ops B, agree_core I ops B ->
  exists d, diginet_session_deadline_m B (g_now B) = Some d /\
    g_now B <= d <= g_now B + 1000000 /\
    (M_fly_on B = 1 -> d <= M_fly_sent B + 1000 * Cfg_ack_timeout_ms B).
Proof.
  intros I ops B H.
  destruct H as [_ _ Hcfg _ Hst Hfly Htime Hq _].
  pose proof (queued_le _ _ Hq) as Hqd.
  assert (Hn0 : 0 <= g_now B) by (unfold g_now; pose proof (u_at_range B OFF_g_now 8); lia).
  assert (Hn1 : g_now B <= 1000000 + 1024 * 65535000000)
    by (pose proof (c_now _ _ Htime); pose proof (d3_ops _ _ Hq); unfold OPS_MAX in *; lia).
  assert (Hws0 : 0 <= M_wake_sent B) by (unfold M_wake_sent; pose proof (u_at_range B A_M_wake_sent 8); lia).
  assert (Hlr0 : 0 <= M_last_rx B) by (unfold M_last_rx; pose proof (u_at_range B A_M_last_rx 8); lia).
  assert (Hfs0 : 0 <= M_fly_sent B) by (unfold M_fly_sent; pose proof (u_at_range B A_M_fly_sent 8); lia).
  pose proof (c1_wake_sent _ _ Htime) as Hws1.
  pose proof (c1_last_rx _ _ Htime) as Hlr1.
  pose proof (a1_wake_timeout _ Hcfg) as Hwt.
  pose proof (a1_offline _ Hcfg) as Hof.
  pose proof (a1_ack_timeout _ Hcfg) as Hak.
  unfold diginet_session_deadline_m. cbv zeta.
  repeat match goal with |- context [min64_m ?a ?b] => rewrite (min64_eq a b) end.
  rewrite (b1_state _ Hst), (b8_on _ Hfly).
  rewrite (a2_wake_timeout _ Hcfg), (a2_offline _ Hcfg), (a2_ack_timeout _ Hcfg).
  rewrite (b4_wake_sent _ Hst), (b4_last_rx _ Hst).
  rewrite (ms_small (Cfg_wake_timeout_ms B)), (ms_small (Cfg_offline_ms B)), (ms_small (Cfg_ack_timeout_ms B))
    by lia.
  rewrite (u64_small (g_now B + 1000000)) by lia.
  rewrite (u64_small (M_wake_sent B + 1000 * Cfg_wake_timeout_ms B)) by lia.
  rewrite (u64_small (M_last_rx B + 1000 * Cfg_offline_ms B)) by lia.
  destruct (display_only_some B (Z.to_nat (S_queued B)) 0 1 ltac:(lia) ltac:(unfold S_queue_N, QUEUE_MAX in *; lia))
    as [r Hr].
  rewrite Hr.
  assert (Hs : M_state B = 0 \/ M_state B = 1 \/ M_state B = 2 \/ M_state B = 3)
    by (pose proof (b1_state_range _ Hst); lia).
  pose proof (b8_on01 _ Hfly) as Hf01.
  unfold DIGINET_S_CLOSED, DIGINET_S_IDLE, DIGINET_S_WAKING, DIGINET_S_ONLINE.
  destruct Hs as [Es|[Es|[Es|Es]]]; rewrite Es; cbn [Z.eqb Pos.eqb orb andb negb].
  - (* IDLE *)
    eexists; split; [reflexivity|]. split; [lia|]. intros F.
    assert (M_fly_on B = 0) by (apply (b9_idle _ Hst); left; exact Es). lia.
  - (* WAKING *)
    pose proof (c2_wake _ _ Htime Es) as Hc2.
    destruct Hf01 as [F|F]; rewrite F; cbn [Z.eqb Pos.eqb orb andb negb].
    + eexists; split; [reflexivity|]. split; [|intros; lia].
      match goal with |- _ <= (if ?Y <? g_now B then g_now B else ?Y) <= _ =>
        assert (Y <= g_now B + 1000000) by lia; destruct (Z.ltb_spec Y (g_now B)) end; lia.
    + rewrite (b8_sent _ Hfly F).
      pose proof (c1_fly_sent _ _ Htime F). pose proof (c2_fly _ _ Htime F).
      rewrite (u64_small (M_fly_sent B + 1000 * Cfg_ack_timeout_ms B)) by lia.
      eexists; split; [reflexivity|]. split; [lia|]. intros _; lia.
  - (* ONLINE *)
    pose proof (c2_online _ _ Htime Es) as Hc2.
    destruct Hf01 as [F|F]; rewrite F; cbn [Z.eqb Pos.eqb orb andb negb].
    + destruct (S_queued B =? 0); cbn [negb andb].
      * eexists; split; [reflexivity|]. split; [|intros; lia].
        match goal with |- _ <= (if ?Y <? g_now B then g_now B else ?Y) <= _ =>
          assert (Y <= g_now B + 1000000) by lia; destruct (Z.ltb_spec Y (g_now B)) end; lia.
      * repeat match goal with |- context [min64_m ?a ?b] => rewrite (min64_eq a b) end.
        eexists; split; [reflexivity|]. split; [|intros; lia].
        match goal with |- _ <= (if ?Y <? g_now B then g_now B else ?Y) <= _ =>
          assert (Y <= g_now B + 1000000) by lia; destruct (Z.ltb_spec Y (g_now B)) end; lia.
    + rewrite (b8_sent _ Hfly F).
      pose proof (c1_fly_sent _ _ Htime F). pose proof (c2_fly _ _ Htime F).
      rewrite (u64_small (M_fly_sent B + 1000 * Cfg_ack_timeout_ms B)) by lia.
      eexists; split; [reflexivity|]. split; [lia|]. intros _; lia.
  - (* CLOSED *)
    eexists; split; [reflexivity|]. split; [lia|]. intros F.
    assert (M_fly_on B = 0) by (apply (b9_idle _ Hst); right; exact Es). lia.
Qed.

(* check_inflight_settle (FT:744-771) passes once the operation's acks agree (the first test, FT:750-751, is the
   per-operation fact OW.acked = GOT.acked) *)
Theorem check_inflight_settle_ok : forall I ops B, agree_core I ops B -> GOT_acked B = OW_acked B ->
  check_inflight_settle_m B = Some (B, tt).
Proof.
  intros I ops B H Hacked.
  destruct (deadline_ok I ops B H) as (d & Hd & Hlo & Hfd).
  destruct H as [_ _ Hcfg _ Hst Hfly Htime Hq _].
  assert (Hn0 : 0 <= g_now B) by (unfold g_now; pose proof (u_at_range B OFF_g_now 8); lia).
  assert (Hn1 : g_now B <= 1000000 + 1024 * 65535000000)
    by (pose proof (c_now _ _ Htime); pose proof (d3_ops _ _ Hq); unfold OPS_MAX in *; lia).
  assert (Hfs0 : 0 <= M_fly_sent B) by (unfold M_fly_sent; pose proof (u_at_range B A_M_fly_sent 8); lia).
  pose proof (a1_ack_timeout _ Hcfg) as Hak.
  unfold check_inflight_settle_m.
  rewrite Hacked, (Z.eqb_refl (OW_acked B)). cbn [negb].
  rewrite Hd.
  rewrite (h_ms_small (Cfg_ack_timeout_ms B)) by lia.
  rewrite (u64_small (g_now B + 1000000)) by lia.
  destruct (b8_on01 _ Hfly) as [F|F]; rewrite F; cbn [truth Z.eqb negb andb].
  - destruct (Z.ltb_spec d (g_now B)); [lia|]. destruct (Z.ltb_spec (g_now B + 1000000) d); [lia|].
    reflexivity.
  - pose proof (c1_fly_sent _ _ Htime F). pose proof (c2_fly _ _ Htime F). specialize (Hfd F).
    rewrite (u64_small (g_now B - M_fly_sent B)) by lia.
    rewrite (u64_small (M_fly_sent B + 1000 * Cfg_ack_timeout_ms B)) by lia.
    destruct (Z.leb_spec (1000 * Cfg_ack_timeout_ms B) (g_now B - M_fly_sent B)); [lia|]. cbn [andb].
    destruct (Z.ltb_spec d (g_now B)); [lia|]. destruct (Z.ltb_spec (g_now B + 1000000) d); [lia|].
    destruct (Z.ltb_spec (M_fly_sent B + 1000 * Cfg_ack_timeout_ms B) d); [lia|].
    reflexivity.
Qed.

(* op3_ok: one operation of LLVMFuzzerTestOneInput whose op byte is 3 (FT:1181-1189: op_begin; g_now += scale * t;
   m_tick; diginet_session_tick; settle (1)) keeps agree, with ops + 1, and the cursor stays well formed.
   op3_tick_ok: the model's tick and the library's from the world after op_begin at the new time: a timeout (both
   sides go IDLE, TickFront.front_lost_ok), else the in-flight step (TickFront.front_step_ok) and the tail
   (TickOk.tick_tail_ok); then what settle needs (SettleOk.settle_ok). Pieces: TickOk.v, TickFront.v, SettleOk.v,
   SubmitLib.op_begin_stage, SimLib.agree_op_begin / agree_core_mono. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import
  TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import
  Agree Links QueueFacts SettleOk Deadline SimLib SubmitLib TickDefs TickOk TickFront.
Import ListNotations.
Open Scope Z_scope.


(* ---- op 3 (FT:1181-1189): op_begin; g_now += scale * t; m_tick; diginet_session_tick; settle (1) ---- *)

(* the OW / GOT counters settle compares (all but the transition list) *)
Definition ow_got_counters_zero (B : list byte) : Prop :=
  OW_e2 B = 0 /\ OW_e3 B = 0 /\ OW_acks B = 0 /\ OW_desk B = 0 /\ OW_foreign B = 0 /\ OW_acked B = 0 /\
  OW_ndata B = 0 /\ GOT_e2 B = 0 /\ GOT_e3 B = 0 /\ GOT_acks B = 0 /\ GOT_desk B = 0 /\ GOT_foreign B = 0 /\
  GOT_acked B = 0 /\ GOT_ndata B = 0.

Lemma ow_got_counters_of_zero : forall B, ow_got_zero B -> ow_got_counters_zero B.
Proof.
  intros B (z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & z15 & z16).
  exact (conj z2 (conj z3 (conj z4 (conj z5 (conj z6 (conj z7 (conj z8
           (conj z10 (conj z11 (conj z12 (conj z13 (conj z14 (conj z15 z16))))))))))))).
Qed.

Lemma ow_got_zero_keep : forall (R : Z -> Prop) B B', wframe R B B' ->
  (forall a, OFF_GOT <= a < OFF_OW + SZ_OW -> ~ R a) -> ow_got_zero B -> ow_got_zero B'.
Proof.
  intros R B B' Hw HR HZ.
  assert (E : forall j, OFF_GOT <= j -> j + 4 <= OFF_OW + SZ_OW -> s32_at B' j = s32_at B j).
  { intros j Hj1 Hj2. apply (wframe_s32_at R B B' j Hw); [unfold OFF_GOT in Hj1; lia|].
    intros a Ha. apply HR. lia. }
  unfold ow_got_zero in *.
  destruct HZ as (z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & z15 & z16).
  unfold OW_n, OW_e2, OW_e3, OW_acks, OW_desk, OW_foreign, OW_acked, OW_ndata,
    GOT_n, GOT_e2, GOT_e3, GOT_acks, GOT_desk, GOT_foreign, GOT_acked, GOT_ndata in *.
  rewrite (E A_OW_n), (E A_OW_e2), (E A_OW_e3), (E A_OW_acks), (E A_OW_desk), (E A_OW_foreign), (E A_OW_acked),
    (E A_OW_ndata), (E A_GOT_n), (E A_GOT_e2), (E A_GOT_e3), (E A_GOT_acks), (E A_GOT_desk), (E A_GOT_foreign),
    (E A_GOT_acked), (E A_GOT_ndata)
    by (unfold A_OW_n, A_OW_e2, A_OW_e3, A_OW_acks, A_OW_desk, A_OW_foreign, A_OW_acked, A_OW_ndata,
          A_GOT_n, A_GOT_e2, A_GOT_e3, A_GOT_acks, A_GOT_desk, A_GOT_foreign, A_GOT_acked, A_GOT_ndata,
          OFF_OW, OFF_GOT, SZ_OW; lia).
  exact (conj z1 (conj z2 (conj z3 (conj z4 (conj z5 (conj z6 (conj z7 (conj z8
           (conj z9 (conj z10 (conj z11 (conj z12 (conj z13 (conj z14 (conj z15 z16))))))))))))))).
Qed.

Lemma ow_got_counters_keep : forall (R : Z -> Prop) B B', wframe R B B' ->
  (forall a, OFF_GOT + 196 <= a < OFF_GOT + SZ_GOT -> ~ R a) -> (forall a, OFF_OW + 196 <= a < OFF_OW + SZ_OW -> ~ R a) ->
  ow_got_counters_zero B -> ow_got_counters_zero B'.
Proof.
  intros R B B' Hw HR1 HR2 HZ.
  assert (E1 : forall j, OFF_GOT + 196 <= j -> j + 4 <= OFF_GOT + SZ_GOT -> s32_at B' j = s32_at B j).
  { intros j Hj1 Hj2. apply (wframe_s32_at R B B' j Hw); [unfold OFF_GOT in Hj1; lia|].
    intros a Ha. apply HR1. lia. }
  assert (E2 : forall j, OFF_OW + 196 <= j -> j + 4 <= OFF_OW + SZ_OW -> s32_at B' j = s32_at B j).
  { intros j Hj1 Hj2. apply (wframe_s32_at R B B' j Hw); [unfold OFF_OW in Hj1; lia|].
    intros a Ha. apply HR2. lia. }
  unfold ow_got_counters_zero in *.
  destruct HZ as (z2 & z3 & z4 & z5 & z6 & z7 & z8 & z10 & z11 & z12 & z13 & z14 & z15 & z16).
  unfold OW_e2, OW_e3, OW_acks, OW_desk, OW_foreign, OW_acked, OW_ndata,
    GOT_e2, GOT_e3, GOT_acks, GOT_desk, GOT_foreign, GOT_acked, GOT_ndata in *.
  rewrite (E2 A_OW_e2), (E2 A_OW_e3), (E2 A_OW_acks), (E2 A_OW_desk), (E2 A_OW_foreign), (E2 A_OW_acked),
    (E2 A_OW_ndata), (E1 A_GOT_e2), (E1 A_GOT_e3), (E1 A_GOT_acks), (E1 A_GOT_desk), (E1 A_GOT_foreign),
    (E1 A_GOT_acked), (E1 A_GOT_ndata)
    by (unfold A_OW_e2, A_OW_e3, A_OW_acks, A_OW_desk, A_OW_foreign, A_OW_acked, A_OW_ndata,
          A_GOT_e2, A_GOT_e3, A_GOT_acks, A_GOT_desk, A_GOT_foreign, A_GOT_acked, A_GOT_ndata,
          OFF_OW, OFF_GOT, SZ_OW, SZ_GOT; lia).
  exact (conj z2 (conj z3 (conj z4 (conj z5 (conj z6 (conj z7 (conj z8
           (conj z10 (conj z11 (conj z12 (conj z13 (conj z14 (conj z15 z16))))))))))))).
Qed.

Lemma g_rx_keep : forall (R : Z -> Prop) B B', wframe R B B' ->
  (forall a, OFF_g_rx <= a < OFF_g_rx + 8 -> ~ R a) -> g_rx B' = g_rx B.
Proof.
  intros R B B' Hw HR. unfold g_rx. apply (wframe_u_at R B B' OFF_g_rx 8 Hw); [unfold OFF_g_rx; lia|].
  intros a Ha. change (Z.of_nat 8) with 8 in Ha. apply HR. lia.
Qed.

Lemma settle_eq_counters : forall B, ow_got_counters_zero B -> OW_n B = GOT_n B ->
  (forall i, 0 <= i < OW_n B -> i < TRANS_MAX ->
     GOT_t_state B i = OW_t_state B i /\ GOT_t_old B i = OW_t_old B i /\ GOT_t_reason B i = OW_t_reason B i) ->
  settle_eq B.
Proof.
  intros B (z2 & z3 & z4 & z5 & z6 & z7 & z8 & z10 & z11 & z12 & z13 & z14 & z15 & z16) Hn Ht. constructor.
  - rewrite z4, z12. reflexivity.
  - rewrite z2, z10. reflexivity.
  - rewrite z3, z11. reflexivity.
  - rewrite z8, z16. reflexivity.
  - rewrite z5, z13. reflexivity.
  - rewrite z6, z14. reflexivity.
  - rewrite z7, z15. reflexivity.
  - symmetry. exact Hn.
  - exact Ht.
Qed.

Lemma settle_eq_zero_of : forall B, ow_got_zero B -> settle_eq B.
Proof.
  intros B (z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & z15 & z16).
  exact (settle_eq_zero B z1 z9 z2 z10 z3 z11 z4 z12 z5 z13 z6 z14 z7 z15 z8 z16).
Qed.

Lemma scale_bound : forall z, 0 <= nth (Z.to_nat (z mod 4)) LLVMFuzzerTestOneInput_SCALE 0 <= 1000000.
Proof.
  intros z. unfold LLVMFuzzerTestOneInput_SCALE.
  destruct (Z.to_nat (z mod 4)) as [|[|[|[|n]]]]; cbn [nth]; try lia. destruct n; cbn [nth]; lia.
Qed.

(* the frames of op 3's tick, from the world after op_begin *)
Local Ltac offs := unfold R_lost in *; unfold R_tick, A_M_fail, OFF_M, OFF_g_raw, OFF_g_last_counter, OFF_g_ncmd,
  OFF_OW, OFF_GOT, SZ_OW, SZ_GOT, OFF_g_rx, OFF_g_now in *; cbv beta in *; lia.

(* op 3's model tick and library tick from the world B1 after op_begin, at the new time now' *)
Lemma op3_tick_ok : forall (HL : links) I ops B1 now',
  agree_core I ops B1 -> g_rx B1 = 0 -> ow_got_zero B1 ->
  g_now B1 <= now' <= 1000000 + ops * 65535000000 ->
  exists B3 B4 r, m_tick_m (set_g_now B1 now') = Some (B3, tt) /\
    diginet_session_tick_m I None B3 (g_now B3) = Some (B4, r) /\
    agree I ops B4 /\ settle_eq B4 /\ drain_fact B4.
Proof.
  intros HL I ops B1 now' HC Hrx HZ Hn.
  pose proof (ac_len _ _ _ HC) as HL1. pose proof (d3_ops _ _ (ac_q _ _ _ HC)) as Hops.
  pose proof (u_at_range B1 OFF_g_now 8) as Hr. change (8 * Z.of_nat 8) with 64 in Hr.
  assert (Hnow : 0 <= now' < 2 ^ 64) by (unfold g_now in Hn; unfold OPS_MAX in Hops; lia).
  assert (Hf12 : wframe (fun a => OFF_g_now <= a < OFF_g_now + 8) B1 (set_g_now B1 now')).
  { unfold set_g_now. apply wframe_upd.
    - unfold OFF_g_now. lia.
    - rewrite HL1, length_put. unfold W_LEN, OFF_g_now. lia.
    - intros a Ha. rewrite length_put in Ha. exact Ha. }
  assert (Hg2 : g_now (set_g_now B1 now') = now').
  { unfold g_now, set_g_now.
    exact (wr_u_upd_same_id B1 OFF_g_now 8 now' OFF_g_now 8 eq_refl eq_refl ltac:(unfold OFF_g_now; lia)
             ltac:(rewrite HL1; unfold OFF_g_now, W_LEN; lia) ltac:(change (8 * Z.of_nat 8) with 64; lia)). }
  assert (HZ2 : ow_got_zero (set_g_now B1 now')) by (apply (ow_got_zero_keep _ B1 _ Hf12); [intros a Ha HR; offs | exact HZ]).
  assert (Hrx2 : g_rx (set_g_now B1 now') = 0)
    by (rewrite (g_rx_keep _ B1 _ Hf12 ltac:(intros a Ha HR; offs)); exact Hrx).
  assert (Hcase : (M_state B1 = S_WAKING /\ 1000 * Cfg_wake_timeout_ms B1 <= now' - M_wake_sent B1) \/
                  (M_state B1 = S_ONLINE /\ 1000 * Cfg_offline_ms B1 <= now' - M_last_rx B1) \/
                  ((M_state B1 = S_WAKING -> now' - M_wake_sent B1 < 1000 * Cfg_wake_timeout_ms B1) /\
                   (M_state B1 = S_ONLINE -> now' - M_last_rx B1 < 1000 * Cfg_offline_ms B1))).
  { unfold S_WAKING, S_ONLINE.
    destruct (Z.eq_dec (M_state B1) 1) as [Ew|Ew].
    - destruct (Z_le_dec (1000 * Cfg_wake_timeout_ms B1) (now' - M_wake_sent B1)) as [T|T].
      + left. exact (conj Ew T).
      + right. right. split; intros H; lia.
    - destruct (Z.eq_dec (M_state B1) 2) as [Eo|Eo].
      + destruct (Z_le_dec (1000 * Cfg_offline_ms B1) (now' - M_last_rx B1)) as [T|T].
        * right. left. exact (conj Eo T).
        * right. right. split; intros H; lia.
      + right. right. split; intros H; lia. }
  destruct Hcase as [[Hs Ht] | [[Hs Ht] | [Hq1 Hq2]]].
  - (* the WAKING timeout (DS:421, FT:248) *)
    destruct (front_lost_ok HL I None ops B1 now' S_WAKING R_WAKE_TIMEOUT HC Hn
                ltac:(destruct HZ as (H1 & _); exact H1) ltac:(destruct HZ as (_ & _ & _ & _ & _ & _ & _ & _ & H9 & _); exact H9)
                (or_introl (conj eq_refl (conj eq_refl (conj Hs Ht)))))
      as (B3 & B4 & Em & Hg3 & Et & HC4 & Hst4 & Hfl4 & How & Hgot & Ht1 & Ht2 & Ht3 & Hfr & Hfail).
    exists B3, B4, DIGINET_OK. split; [exact Em|]. split; [rewrite Hg3; exact Et|].
    assert (Hne : M_state B4 <> S_ONLINE) by (rewrite Hst4; unfold S_IDLE, S_ONLINE; lia).
    split; [|split].
    + constructor; [exact HC4 | intros _ Hm; exact (False_ind _ (Hne Hm)) |].
      rewrite (g_rx_keep _ _ _ Hfr ltac:(intros a Ha HR; offs)). exact Hrx2.
    + apply settle_eq_counters.
      * apply (ow_got_counters_keep _ _ _ Hfr); [intros a Ha HR; offs | intros a Ha HR; offs |].
        exact (ow_got_counters_of_zero _ HZ2).
      * rewrite How, Hgot. reflexivity.
      * intros i Hi Hi'. rewrite How in Hi. assert (E0 : i = 0) by lia. rewrite E0.
        exact (conj Ht1 (conj Ht2 Ht3)).
    + intros _ Hm. exact (False_ind _ (Hne Hm)).
  - (* the ONLINE silence (DS:425, FT:250) *)
    destruct (front_lost_ok HL I None ops B1 now' S_ONLINE R_SILENCE HC Hn
                ltac:(destruct HZ as (H1 & _); exact H1) ltac:(destruct HZ as (_ & _ & _ & _ & _ & _ & _ & _ & H9 & _); exact H9)
                (or_intror (conj eq_refl (conj eq_refl (conj Hs Ht)))))
      as (B3 & B4 & Em & Hg3 & Et & HC4 & Hst4 & Hfl4 & How & Hgot & Ht1 & Ht2 & Ht3 & Hfr & Hfail).
    exists B3, B4, DIGINET_OK. split; [exact Em|]. split; [rewrite Hg3; exact Et|].
    assert (Hne : M_state B4 <> S_ONLINE) by (rewrite Hst4; unfold S_IDLE, S_ONLINE; lia).
    split; [|split].
    + constructor; [exact HC4 | intros _ Hm; exact (False_ind _ (Hne Hm)) |].
      rewrite (g_rx_keep _ _ _ Hfr ltac:(intros a Ha HR; offs)). exact Hrx2.
    + apply settle_eq_counters.
      * apply (ow_got_counters_keep _ _ _ Hfr); [intros a Ha HR; offs | intros a Ha HR; offs |].
        exact (ow_got_counters_of_zero _ HZ2).
      * rewrite How, Hgot. reflexivity.
      * intros i Hi Hi'. rewrite How in Hi. assert (E0 : i = 0) by lia. rewrite E0.
        exact (conj Ht1 (conj Ht2 Ht3)).
    + intros _ Hm. exact (False_ind _ (Hne Hm)).
  - (* no timeout: the in-flight step, then the tail *)
    destruct (front_quiet_ok HL I None ops B1 now' HC Hn Hq1 Hq2) as (Em & Et).
    destruct (front_step_ok HL I None ops B1 now' HC Hn Hq1 Hq2) as (res & Es & Hres).
    exists (set_g_now B1 now'). rewrite Hg2, Et, Es.
    destruct res as [[W r] | W].
    + exists W, r. split; [exact Em|]. split; [reflexivity|].
      destruct Hres as [HCW HKW HDW HFW _]. split; [|split].
      * constructor; [exact HCW | exact HKW |].
        rewrite (g_rx_keep _ _ _ HFW ltac:(intros a Ha HR; offs)). exact Hrx2.
      * apply settle_eq_zero_of. exact (ow_got_zero_keep _ _ _ HFW ltac:(intros a Ha HR; offs) HZ2).
      * exact HDW.
    + destruct Hres as (HCW & HFW & _).
      assert (HgW : g_now W = now').
      { rewrite <- Hg2. unfold g_now. apply (wframe_u_at R_tick _ _ OFF_g_now 8 HFW); [unfold OFF_g_now; lia|].
        intros a Ha HR. change (Z.of_nat 8) with 8 in Ha. offs. }
      destruct (tick_tail_ok HL I None ops W HCW) as (B4 & r & Et4 & HP).
      exists B4, r. split; [exact Em|]. split; [cbn beta iota; rewrite <- HgW; exact Et4|].
      destruct HP as [HC4 HK4 HD4 HF4 _]. split; [|split].
      * constructor; [exact HC4 | exact HK4 |].
        rewrite (g_rx_keep _ _ _ HF4 ltac:(intros a Ha HR; offs)).
        rewrite (g_rx_keep _ _ _ HFW ltac:(intros a Ha HR; offs)). exact Hrx2.
      * apply settle_eq_zero_of.
        exact (ow_got_zero_keep _ _ _ HF4 ltac:(intros a Ha HR; offs)
                 (ow_got_zero_keep _ _ _ HFW ltac:(intros a Ha HR; offs) HZ2)).
      * exact HD4.
Qed.

(* one operation of the loop whose op byte is 3 (TOps.v LLVMFuzzerTestOneInput_op_m, FT:1181-1189) *)
Lemma op3_ok : forall (HL : links) I ops B A D c k,
  agree I ops B -> ops < OPS_MAX -> fuzz_in_ok D c -> snd (fuzz_u8_m D c) mod 9 = 3 ->
  exists B' c', LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B', (c', k)) /\
    agree I (ops + 1) B' /\ fuzz_in_ok D c'.
Proof.
  intros HL I ops B A D c k HA Hops Hc Hop.
  destruct (fuzz_u8_ok D c Hc) as (c1 & opb & E1 & Hc1 & _).
  rewrite E1 in Hop. cbn [snd] in Hop.
  unfold LLVMFuzzerTestOneInput_op_m. rewrite E1. cbv beta iota zeta. rewrite Hop.
  change (3 =? 0) with false. change (3 =? 1) with false. change (3 =? 2) with false. change (3 =? 3) with true.
  cbv beta iota.
  destruct (fuzz_u8_ok D c1 Hc1) as (c2 & sb & E2 & Hc2 & _). rewrite E2. cbv beta iota zeta.
  destruct (op_begin_stage B (ac_len _ _ _ (ag_core _ _ _ HA))) as (B1 & Eb & _ & HZ & _).
  rewrite Eb. cbv beta iota zeta.
  destruct (fuzz_u16_ok D c2 Hc2) as (c3 & t & E3 & Hc3 & Ht). rewrite E3. cbv beta iota zeta.
  pose proof (agree_op_begin I ops B B1 HA Eb) as HA1.
  pose proof (agree_core_mono I ops (ops + 1) B1 (ag_core _ _ _ HA1) ltac:(unfold OPS_MAX in *; lia)) as HC1.
  pose proof (c_now _ _ (ac_time _ _ _ (ag_core _ _ _ HA1))) as Hn1.
  pose proof (d3_ops _ _ (ac_q _ _ _ (ag_core _ _ _ HA1))) as Hops1.
  pose proof (u_at_range B1 OFF_g_now 8) as Hr. change (8 * Z.of_nat 8) with 64 in Hr.
  pose proof (scale_bound sb) as Hs.
  assert (Hst : 0 <= nth (Z.to_nat (sb mod 4)) LLVMFuzzerTestOneInput_SCALE 0 * t <= 65535000000) by nia.
  rewrite (Z.mod_small (g_now B1 + nth (Z.to_nat (sb mod 4)) LLVMFuzzerTestOneInput_SCALE 0 * t) (2 ^ 64))
    by (unfold g_now in *; unfold OPS_MAX in *; lia).
  destruct (op3_tick_ok HL I (ops + 1) B1 (g_now B1 + nth (Z.to_nat (sb mod 4)) LLVMFuzzerTestOneInput_SCALE 0 * t)
              HC1 (ag_rx _ _ _ HA1) HZ ltac:(lia))
    as (B3 & B4 & r & Em & Et & HA4 & HS4 & HD4).
  rewrite Em. cbv beta iota zeta. rewrite Et. cbv beta iota zeta.
  rewrite (settle_ok I (ops + 1) B4 1 (ag_core _ _ _ HA4) (ag_keepalive _ _ _ HA4) HS4 (fun _ => HD4)).
  cbv beta iota zeta.
  exists B4, c3. split; [reflexivity|]. exact (conj HA4 Hc3).
Qed.

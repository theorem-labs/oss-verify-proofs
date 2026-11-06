(* tick_take_ok: diginet_session_tick's take and send (diginet_session.c:460-471, DS; TickDefs.tick_take_m), started
   in agree_core with the session ONLINE, nothing in flight, the back-off passed, the keepalive not due and the
   queue not empty, returns and leaves a world in TickDefs.tick_post. The run (now = g_now B, TickTakeW.v names):
   take (DS:353-386, TakeOk.take_m_ok) with the pacing tt_allow; nothing taken: the world is take's
   (TickTakeZ.tt_zero_ok: the first ready entry is always taken, so nothing queued was ready, the drain fact);
   something taken: display_sent / last_display (DS:467-470), send_data up to send_raw (TickTakeS), io.send =
   the harness's io_send on the DATA frame (FT:823-899, TickTakeIo; tagged: the command count loop
   (TakeOk.cmds_loop_ok) and check_latest_sent (TakeOk.latest_sent_ok) on the taken serials), send_raw's stats;
   the world after the run is TickTakeW.tt_end (TickTakeE), whose agree_q is TickTakeQ.tt_agree_q and whose
   tick_post is TickTakeA.tt_post_ok.
   tick_take_keep (tt_send_keep for the send): the same, and the writes lie inside TickTakeW.R_tt (take's R_qs
   when nothing is taken, tt_end's te_frame after the send), which misses world bytes 0..15 (M.desk_known, M.desk,
   M.state: R_tt_low); tick_take_ok (tt_send_case) is its tick_post part. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links QueueFacts SimLib SendOk
  SettleOk TickDefs TakeOk TickTakeW TickTakeZ TickTakeS TickTakeIo TickTakeA TickTakeQ TickTakeE.
Import ListNotations.
Open Scope Z_scope.

(* check_latest_sent's frame inside R_cs / R_hq when the serials are commands *)
Lemma tt_sent_rs_weak : forall (Ts : list Z) X Bs, (forall k, In k Ts -> 0 <= k < CMDS_MAX) ->
  wframe (sent_rs Ts) X Bs -> wframe (fun a => R_cs a \/ R_hq a) X Bs.
Proof.
  intros Ts X Bs HT F. eapply wframe_weaken; [|exact F].
  intros a [Ha|[Ha|(k & Hk & Ha)]].
  - right. left. exact Ha.
  - right. right. exact Ha.
  - left. specialize (HT k Hk). unfold R_cs. unfold A_Cmd_st, CMDS_MAX, OFF_g_cmd, SZ_g_cmd, Cmd_ESZ in *.
    split; [lia|]. replace (a - 19912) with (40 * k + (a - 19912 - 40 * k)) by lia.
    rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full. rewrite Z.mod_small; lia.
Qed.

(* R_tt misses M.desk_known, M.desk, M.state (world bytes 0..15) *)
Lemma R_tt_low : forall a, 0 <= a < 16 -> ~ R_tt a.
Proof. intros a Ha Hr. tk_offs. Qed.

Lemma tt_send_keep : forall (HL : links) I F ops B B1 m, agree_core I ops B ->
  S_state B = DIGINET_S_ONLINE -> S_inflight B = 0 -> S_backoff_until_us B <= g_now B ->
  m = tt_mask B -> tt_n B m <> 0 ->
  length B1 = WN -> wframe R_qs B B1 -> sq B1 = unpick m (sq B) ->
  S_queued B1 = Z.of_nat (length (unpick m (sq B))) ->
  exists B' r, send_data_m I F (w_dispS B1 (tt_hd B m) (g_now B)) (tt_body B m) (tt_n B m) (g_now B) = Some (B', r) /\
    tick_post I ops B B' /\ wframe R_tt B B'.
Proof.
  intros HL I F ops B B1 m HC Hst Hin Hbo Hm Hn0 HB1 EfR Esq Eq.
  assert (HB : length B = WN) by exact (ac_len _ _ _ HC).
  pose proof (ac_q _ _ _ HC) as HQ. pose proof (ac_cfg _ _ _ HC) as HG. pose proof (ac_st _ _ _ HC) as HS.
  pose proof (ac_fly _ _ _ HC) as HFl. pose proof (ac_io _ _ _ HC) as HIo.
  pose proof (tt_sq_ok ops B HB HQ) as Hsq. pose proof (tt_queued_le ops B HQ) as Hqle.
  pose proof (a1_max_cmds B HG) as Hmc. pose proof (a1_max_body B HG) as Hmb.
  rewrite <- (tk_cfg_max_cmds B HG) in Hmc. rewrite <- (tk_cfg_max_body B HG) in Hmb.
  assert (Hml : length m = length (sq B)) by (rewrite Hm; apply take_mask_length).
  assert (Hsq32 : Forall (fun e => length e = 32%nat /\ e_len e <= 24) (sq B)).
  { eapply Forall_impl; [|exact Hsq]. intros e (H1 & (_ & H2) & _). split; assumption. }
  (* what take returned *)
  assert (Hbl : Z.of_nat (length (tt_body B m)) <= S_cfg_max_body B).
  { rewrite Hm. exact (proj2 (take_len_le (S_cfg_max_cmds B) (S_cfg_max_body B) (tt_allow B) (sq B) ltac:(lia) Hsq32)). }
  assert (Hlen : (length (tt_body B m) <= 1484)%nat) by lia.
  assert (Hbc : body_check (tt_body B m) = DIGINET_OK) by (rewrite Hm; exact (take_body_ok _ _ _ _)).
  assert (Hnle : tt_n B m <= S_cfg_max_cmds B)
    by (rewrite Hm; exact (take_n_le (S_cfg_max_cmds B) (S_cfg_max_body B) (tt_allow B) (sq B) ltac:(lia))).
  assert (Hn1 : 1 <= tt_n B m) by (unfold tt_n in *; lia).
  assert (Hu8 : u8 (tt_n B m) = tt_n B m) by (unfold u8; apply Z.mod_small; lia).
  assert (HTne : tt_T B m <> []) by (intros E; apply Hn0; unfold tt_n; rewrite E; reflexivity).
  assert (Hnow : 0 <= g_now B < 2 ^ 64) by (split; [apply u_at_nonneg | apply (u_at_bound B OFF_g_now 8)]).
  (* agree's facts at the start *)
  assert (HMst : M_state B = S_ONLINE) by (rewrite <- (b1_state _ HS); exact Hst).
  assert (HMfly : M_fly_on B = 0) by (rewrite <- (b8_on _ HFl); exact Hin).
  assert (HMdk : M_desk_known B = 1) by (apply (b9_known _ HS); right; exact HMst).
  assert (Hdesk : S_desk_mac B = M_desk B) by exact (b2_desk_mac _ HS HMdk).
  assert (Hhost : S_cfg_host_mac B = HOST) by (rewrite (tk_cfg_host_mac B HG); exact (a1_host_mac B HG)).
  assert (Hmode : S_cfg_sum_mode B = Cfg_sum_mode B) by exact (tk_cfg_sum_mode B HG).
  pose proof (a1_sum_mode B HG) as Hmode01.
  assert (HMbo : M_backoff_until B <= g_now B) by (rewrite <- (b4_backoff _ HS); exact Hbo).
  pose proof (b7_host_counter _ HS) as Ehc.
  (* DS:467-470 *)
  pose proof (tk_dispS_len B1 (tt_hd B m) (g_now B) HB1) as HB2.
  assert (F2 : wframe (fun a => R_qs a \/ R_ds a) B (w_dispS B1 (tt_hd B m) (g_now B))).
  { eapply (tk_frame_comb R_qs R_ds _ B B1 _).
    - intros a H. left. exact H.
    - intros a H. right. exact H.
    - exact EfR.
    - apply tk_dispS_frame. exact HB1. }
  assert (Hmode2 : S_cfg_sum_mode (w_dispS B1 (tt_hd B m) (g_now B)) = DIGINET_SUM_BODY \/
                   S_cfg_sum_mode (w_dispS B1 (tt_hd B m) (g_now B)) = DIGINET_SUM_ZERO).
  { assert (E : S_cfg_sum_mode (w_dispS B1 (tt_hd B m) (g_now B)) = S_cfg_sum_mode B)
      by (unfold S_cfg_sum_mode; tk_get F2).
    rewrite E, Hmode. exact Hmode01. }
  (* send_data (DS:388-399) *)
  rewrite (tt_send_stage HL I F _ (tt_body B m) (tt_n B m) (g_now B) HB2 Hlen Hbc Hmode2).
  destruct (tt_send_facts HL (w_dispS B1 (tt_hd B m) (g_now B)) (tt_body B m) (tt_n B m) (g_now B)
              HB2 Hlen Hbc Hmode2 Hnow) as (HB6 & F6 & E6hc & E6on & E6ctr & E6ret & E6sent & E6len & E6frl & E6fr).
  assert (Efr : w_fr (w_dispS B1 (tt_hd B m) (g_now B)) (tt_body B m) (tt_n B m) = tt_fr B m)
    by exact (tt_fr_eq B _ m HB F2 Hdesk Hhost Hmode).
  rewrite Efr in E6frl, E6fr |- *.
  assert (Ehc2 : S_host_counter (w_dispS B1 (tt_hd B m) (g_now B)) = S_host_counter B)
    by (unfold S_host_counter; tk_get F2).
  rewrite Ehc2 in E6hc, E6ctr. fold (tt_send B m) in E6hc, E6ctr.
  remember (w_send (w_dispS B1 (tt_hd B m) (g_now B)) (tt_body B m) (tt_n B m) (g_now B)) as B6 eqn:EB6.
  assert (F6B : wframe R_lib B B6).
  { eapply (tk_frame_comb (fun a => R_qs a \/ R_ds a) R_ss R_lib B _ B6).
    - intros a Ha. unfold R_lib. tauto.
    - intros a Ha. unfold R_lib. tauto.
    - exact F2.
    - exact F6. }
  (* what io_send reads of B6 is B's *)
  assert (E6dk : M_desk_known B6 = 1) by (rewrite <- HMdk; unfold M_desk_known; tk_get F6B).
  assert (E6desk : M_desk B6 = M_desk B) by (unfold M_desk; tk_get F6B).
  assert (E6mode : Cfg_sum_mode B6 = Cfg_sum_mode B) by (unfold Cfg_sum_mode; tk_get F6B).
  assert (E6st : M_state B6 = S_ONLINE) by (rewrite <- HMst; unfold M_state; tk_get F6B).
  assert (E6fly : M_fly_on B6 = 0) by (rewrite <- HMfly; unfold M_fly_on; tk_get F6B).
  assert (E6now : g_now B6 = g_now B) by (unfold g_now; tk_get F6B).
  assert (E6bo : M_backoff_until B6 <= g_now B6).
  { rewrite E6now. assert (E : M_backoff_until B6 = M_backoff_until B) by (unfold M_backoff_until; tk_get F6B).
    rewrite E. exact HMbo. }
  assert (E6mb : Z.of_nat (length (tt_body B m)) <= Cfg_max_body B6).
  { assert (E : Cfg_max_body B6 = Cfg_max_body B) by (unfold Cfg_max_body; tk_get F6B).
    rewrite E, <- (tk_cfg_max_body B HG). exact Hbl. }
  assert (E6mc : u8 (tt_n B m) <= Cfg_max_cmds B6).
  { assert (E : Cfg_max_cmds B6 = Cfg_max_cmds B) by (unfold Cfg_max_cmds; tk_get F6B).
    rewrite E, <- (tk_cfg_max_cmds B HG), Hu8. exact Hnle. }
  assert (E6send : tt_send B m = u32 (M_host_counter B6 + u8 (tt_n B m))).
  { assert (E : M_host_counter B6 = M_host_counter B) by (unfold M_host_counter; tk_get F6B).
    rewrite E, Hu8, <- Ehc. reflexivity. }
  assert (E6raw : g_raw B6 = g_raw B) by (unfold g_raw; tk_get F6B).
  assert (Eio : S_io_send B6 = ti_io_send I) by (rewrite <- (a3_io_send _ _ HIo); unfold S_io_send; tk_get F6B).
  assert (Hbok : build_ok (M_desk B) HOST (tt_send B m) 0 0 DIGINET_CMD_DATA (u8 (tt_n B m)) (tt_body B m)
                   (Cfg_sum_mode B)).
  { unfold build_ok. split; [unfold M_desk; apply w_length_sub; rewrite HB; tk_offs|].
    split; [reflexivity|]. split; [exact Hmode01|].
    split; [unfold tt_send, u32; apply Z.mod_pos_bound; lia|].
    split; [lia|]. split; [lia|]. split; [unfold DIGINET_CMD_DATA; lia|].
    split; [unfold u8; apply Z.mod_pos_bound; lia|].
    split; [exact Hlen | exact Hbc]. }
  (* send_raw (DS:88-94) and io.send *)
  unfold send_raw_m, call_send.
  destruct (Z.eqb_spec (S_io_send B6) (ti_io_send I)) as [_|Hne]; [|exfalso; exact (Hne Eio)].
  destruct (Z.eqb_spec (g_raw B) 0) as [Hr|Hr].
  - (* tagged *)
    destruct (tt_hq_ok ops B HB HQ Hr) as (Hnq & HND & Htag & Hlhq).
    destruct (tt_bridge ops B m HB HQ Hr) as (Ebody & Ehd & ElTs). unfold tt_Ts in Ebody, Ehd, ElTs.
    destruct (tt_stage_frames B B1 B6 m (tt_send B m) HB HB1 EfR HB6 F6) as (_ & _ & HBw & FBw & HX & FX).
    destruct (tt_qmodel_frame B _ HB FBw) as (EnqW & EhqW & _ & EcmdW & EtagW).
    destruct (tt_qmodel_frame B _ HB FX) as (EnqX & EhqX & _ & EcmdX & EtagX).
    specialize (EhqW ltac:(unfold CMDS_MAX, QUEUE_MAX in *; lia)). specialize (EhqX ltac:(unfold CMDS_MAX, QUEUE_MAX in *; lia)).
    assert (HQk : forall i, 0 <= i < g_nq B -> Q_at B i < CMDS_MAX).
    { intros i Hi. assert (Hiq : In (Q_at B i) (hq B)) by (apply tk_In_hq; exists i; split; [exact Hi | reflexivity]).
      rewrite Forall_forall in Htag. destruct (Htag _ Hiq) as (Hk1 & Hk2 & _). lia. }
    assert (HTk : forall k, In k (pick m (hq B)) -> 0 <= k < CMDS_MAX).
    { intros k Hk. apply in_pick in Hk. rewrite Forall_forall in Htag. destruct (Htag k Hk) as (Hk1 & Hk2 & _). lia. }
    (* check_latest_sent (T2) on the world w_io8 B6 send *)
    destruct (latest_sent_ok (w_io8 B6 (tt_send B m)) m HX ltac:(rewrite EnqX; lia)
                ltac:(rewrite EhqX; lia) ltac:(rewrite EhqX; exact HND)
                ltac:(rewrite EhqX; eapply Forall_impl; [exact EtagX | exact Htag]))
      as (Bs & ET2 & EhqS & EstS & FS).
    assert (FS' : wframe (fun a => R_cs a \/ R_hq a) (w_io8 B6 (tt_send B m)) Bs).
    { apply (tt_sent_rs_weak (pick m (hq (w_io8 B6 (tt_send B m))))); [|exact FS].
      rewrite EhqX. exact HTk. }
    assert (HBs : length Bs = WN) by exact (tk_frame_len _ _ _ FS HX).
    assert (Ecb : map (cmd_body (w_io8 B6 (tt_send B m))) (pick m (hq B)) = map (cmd_body B) (pick m (hq B))).
    { apply map_ext_in. intros k Hk. pose proof (HTk k Hk) as Hk'.
      exact (proj2 (proj2 (proj2 (proj2 (proj2 (EcmdX k ltac:(unfold Cmd_N, CMDS_MAX in *; lia))))))). }
    assert (Ecd : map (Cmd_display (w_io8 B6 (tt_send B m))) (pick m (hq B)) = map (Cmd_display B) (pick m (hq B))).
    { apply map_ext_in. intros k Hk. pose proof (HTk k Hk) as Hk'.
      exact (proj1 (proj2 (proj2 (proj2 (EcmdX k ltac:(unfold Cmd_N, CMDS_MAX in *; lia)))))). }
    rewrite EhqX in ET2. rewrite Ecb, Ecd in ET2. rewrite <- Ebody, <- Ehd in ET2.
    (* the command count loop (T3) on the world set_g_fail_next B6 0 *)
    pose proof (cmds_loop_ok (set_g_fail_next B6 0) m HBw ltac:(rewrite EnqW; lia)
                  ltac:(rewrite EhqW; lia) ltac:(rewrite EhqW; exact HND)
                  ltac:(rewrite EhqW; eapply Forall_impl; [exact EtagW | exact Htag])
                  (repeat (b8 0) (Z.to_nat (frame_len (length (tt_body B m)) - (30 + Z.of_nat (length (tt_body B m)))))))
      as ET3.
    assert (Ecw : map (cmd_body (set_g_fail_next B6 0)) (pick m (hq B)) = map (cmd_body B) (pick m (hq B))).
    { apply map_ext_in. intros k Hk. pose proof (HTk k Hk) as Hk'.
      exact (proj2 (proj2 (proj2 (proj2 (proj2 (EcmdW k ltac:(unfold Cmd_N, CMDS_MAX in *; lia))))))). }
    rewrite EhqW in ET3. rewrite Ecw in ET3. rewrite <- Ebody in ET3. rewrite ElTs in ET3. fold (tt_n B m) in ET3.
    rewrite <- Hu8 in ET3.
    rewrite <- (tt_frame_body (M_desk B) HOST (tt_send B m) 0 0 DIGINET_CMD_DATA (u8 (tt_n B m)) (tt_body B m)
                 (Cfg_sum_mode B) (proj1 Hbok) ltac:(reflexivity)) in ET3.
    (* check_latest_display's guard (FT:651-653): the display pacing take was called with *)
    assert (FBs : wframe (fun a => R_lib a \/ R_io8 a \/ R_cs a \/ R_hq a) B Bs).
    { eapply (tk_frame_comb (fun a => R_lib a \/ R_io8 a) (fun a => R_cs a \/ R_hq a) _ B
               (w_io8 B6 (tt_send B m)) Bs);
        [intros a Ha; cbv beta in Ha |- *; tauto | intros a Ha; cbv beta in Ha |- *; tauto | | exact FS'].
      eapply (tk_frame_comb R_lib R_io8 _ B B6 _);
        [intros a Ha; cbv beta in Ha |- *; tauto | intros a Ha; cbv beta in Ha |- *; tauto
        | exact F6B | apply tk_io8_frame; exact HB6]. }
    assert (Hdisp : truth (tt_hd B m) = true ->
                    M_display_sent Bs = 0 \/ Cfg_display_gap_us Bs <= u64 (g_now Bs - M_last_display Bs)).
    { intros Ht.
      assert (Hal : tt_allow B <> 0).
      { intros H0. unfold truth in Ht. apply negb_true_iff, Z.eqb_neq in Ht. apply Ht.
        rewrite Hm. exact (take_disp _ _ _ _ H0). }
      assert (Eds : M_display_sent Bs = M_display_sent B) by (unfold M_display_sent; tk_get FBs).
      assert (Edl : M_last_display Bs = M_last_display B) by (unfold M_last_display; tk_get FBs).
      assert (Egp : Cfg_display_gap_us Bs = Cfg_display_gap_us B) by (unfold Cfg_display_gap_us; tk_get FBs).
      assert (Enw : g_now Bs = g_now B) by (unfold g_now; tk_get FBs).
      rewrite Eds, Edl, Egp, Enw. rewrite <- (b5_display_sent _ HS Hr), <- (b5_last_display _ HS Hr).
      rewrite <- (tk_cfg_display_gap B HG).
      unfold tt_allow, int_of_bool in Hal.
      destruct (Z.eqb_spec (S_display_sent B) 0) as [E1|E1]; [left; exact E1|].
      destruct (Z.leb_spec (S_cfg_display_gap_us B) (u64 (g_now B - S_last_display_us B))) as [E2|E2];
        [right; exact E2|].
      exfalso. apply Hal. reflexivity. }
    assert (Htag0 : at8 (tt_body B m) 0 <> 0).
    { rewrite (tt_body_tag ops B m HB HQ Hr HTne). unfold TAG. lia. }
    unfold tt_fr.
    rewrite (tt_io_tagged HL I B6 (M_desk B) (tt_send B m) (u8 (tt_n B m)) (tt_body B m) (Cfg_sum_mode B)
               Bs (tt_hd B m) HB6 Hbok E6dk E6desk E6mode E6st E6fly E6bo E6mb E6mc E6send
               ltac:(rewrite E6raw; exact Hr) Htag0 ET3 ET2 Hdisp).
    fold (tt_fr B m). cbv beta iota.
    exists (w_tx (w_fly (w_dispM Bs (tt_hd B m)) (tt_send B m) (tt_fr B m)) (if truth (g_fail_next B6) then - EIO else 0)).
    exists (if truth (g_fail_next B6) then - EIO else 0).
    split.
    + unfold w_tx. destruct ((if truth (g_fail_next B6) then - EIO else 0) =? 0); reflexivity.
    + assert (EnqS : g_nq Bs = Z.of_nat (length (unpick m (hq (w_io8 B6 (tt_send B m)))))).
      { rewrite <- EhqS, tk_hq_length, Z2Nat.id by apply u_at_nonneg. reflexivity. }
      assert (HE : tt_end B (w_tx (w_fly (w_dispM Bs (tt_hd B m)) (tt_send B m) (tt_fr B m))
                              (if truth (g_fail_next B6) then - EIO else 0)) m).
      { apply (tt_end_tagged B B1 B6 Bs m _ HB Hr ltac:(unfold QUEUE_MAX; lia) ltac:(lia) HQk HB1 EfR Esq Eq HB6 F6
                 E6hc E6on E6ctr E6ret E6sent E6len E6frl E6fr Hlen HBs FS' EhqS EnqS EstS). }
      split; [exact (tt_post_ok I ops B _ m HC Hst Hin Hlen Hbc HE (tt_agree_q ops B _ m HB HQ Hml HE))|].
      exact (te_frame _ _ _ HE).
  - (* raw *)
    unfold tt_fr.
    rewrite (tt_io_raw HL I B6 (M_desk B) (tt_send B m) (u8 (tt_n B m)) (tt_body B m) (Cfg_sum_mode B)
               HB6 Hbok E6dk E6desk E6mode E6st E6fly E6bo E6mb E6mc E6send ltac:(rewrite E6raw; exact Hr)).
    fold (tt_fr B m). cbv beta iota.
    exists (w_tx (w_fly (w_io8 B6 (tt_send B m)) (tt_send B m) (tt_fr B m)) (if truth (g_fail_next B6) then - EIO else 0)).
    exists (if truth (g_fail_next B6) then - EIO else 0).
    split.
    + unfold w_tx. destruct ((if truth (g_fail_next B6) then - EIO else 0) =? 0); reflexivity.
    + assert (HE : tt_end B (w_tx (w_fly (w_io8 B6 (tt_send B m)) (tt_send B m) (tt_fr B m))
                              (if truth (g_fail_next B6) then - EIO else 0)) m).
      { apply (tt_end_raw B B1 B6 m _ HB Hr ltac:(unfold QUEUE_MAX; lia) HB1 EfR Esq Eq HB6 F6
                 E6hc E6on E6ctr E6ret E6sent E6len E6frl E6fr Hlen). }
      split; [exact (tt_post_ok I ops B _ m HC Hst Hin Hlen Hbc HE (tt_agree_q ops B _ m HB HQ Hml HE))|].
      exact (te_frame _ _ _ HE).
Qed.

Lemma tt_send_case : forall (HL : links) I F ops B B1 m, agree_core I ops B ->
  S_state B = DIGINET_S_ONLINE -> S_inflight B = 0 -> S_backoff_until_us B <= g_now B ->
  m = tt_mask B -> tt_n B m <> 0 ->
  length B1 = WN -> wframe R_qs B B1 -> sq B1 = unpick m (sq B) ->
  S_queued B1 = Z.of_nat (length (unpick m (sq B))) ->
  exists B' r, send_data_m I F (w_dispS B1 (tt_hd B m) (g_now B)) (tt_body B m) (tt_n B m) (g_now B) = Some (B', r) /\
    tick_post I ops B B'.
Proof.
  intros HL I F ops B B1 m HC Hst Hin Hbo Hm Hn0 HB1 EfR Esq Eq.
  destruct (tt_send_keep HL I F ops B B1 m HC Hst Hin Hbo Hm Hn0 HB1 EfR Esq Eq) as (B' & r & E & Hp & _).
  exists B', r. exact (conj E Hp).
Qed.

Lemma tick_take_keep : forall (HL : links) I F ops B,
  agree_core I ops B -> S_state B = DIGINET_S_ONLINE -> S_inflight B = 0 ->
  S_backoff_until_us B <= g_now B -> g_now B < S_next_keepalive_us B -> S_queued B <> 0 ->
  exists B' r, tick_take_m I F B (g_now B) = Some (B', r) /\ tick_post I ops B B' /\ wframe R_tt B B'.
Proof.
  intros HL I F ops B HC Hst Hin Hbo Hka Hq.
  assert (HB : length B = WN) by exact (ac_len _ _ _ HC).
  pose proof (ac_q _ _ _ HC) as HQ. pose proof (ac_cfg _ _ _ HC) as HG.
  pose proof (tt_sq_ok ops B HB HQ) as Hsq. pose proof (tt_queued_le ops B HQ) as Hqle.
  pose proof (a1_max_body B HG) as Hmb. rewrite <- (tk_cfg_max_body B HG) in Hmb.
  assert (Hsq24 : Forall (fun e => e_len e <= 24) (sq B)).
  { eapply Forall_impl; [|exact Hsq]. intros e (_ & (_ & H) & _). exact H. }
  (* take (DS:353-386, T1) *)
  destruct (take_m_ok B (tt_allow B) HB Hqle ltac:(lia) Hsq24) as (B1 & ET & Esq & Eq & Ef).
  change (take_mask (S_cfg_max_cmds B) (S_cfg_max_body B) (tt_allow B) 0 0 [] (sq B)) with (tt_mask B) in Esq, Eq.
  assert (EfR : wframe R_qs B B1).
  { eapply wframe_weaken; [|exact Ef]. intros a Ha. unfold take_rs in Ha. tk_offs. }
  assert (HB1 : length B1 = WN) by exact (tk_frame_len _ _ _ Ef HB).
  unfold tick_take_m. cbv beta zeta. fold (tt_allow B). rewrite ET. rewrite (tt_take_res B). cbv beta iota.
  destruct (Z.eqb_spec (tt_n B (tt_mask B)) 0) as [Hn0|Hn0].
  - (* nothing taken: the world is take's *)
    assert (HT0 : tt_T B (tt_mask B) = []).
    { apply length_zero_iff_nil. unfold tt_n in Hn0. lia. }
    assert (Hun : unpick (tt_mask B) (sq B) = sq B) by (apply take_none; exact HT0).
    rewrite Hun in Esq, Eq.
    exists B1, DIGINET_OK. split; [reflexivity|]. split.
    + apply (tt_zero_ok I ops B B1 HC Hst Hin Hbo Hka Hq Hsq HT0 HB1 EfR Esq).
      rewrite Eq, tk_sq_length, Z2Nat.id by apply u_at_nonneg. reflexivity.
    + apply (wframe_weaken R_qs R_tt B B1); [|exact EfR]. intros a Ha. unfold R_tt, R_nq. left. left. exact Ha.
  - (* the send *)
    cbv beta iota.
    change (if tt_hd B (tt_mask B) =? 0 then B1 else set_S_last_display_us (set_S_display_sent B1 1) (g_now B))
      with (w_dispS B1 (tt_hd B (tt_mask B)) (g_now B)).
    rewrite Nat2Z.id, firstn_all.
    exact (tt_send_keep HL I F ops B B1 (tt_mask B) HC Hst Hin Hbo eq_refl Hn0 HB1 EfR Esq Eq).
Qed.

Lemma tick_take_ok : forall (HL : links) I F ops B,
  agree_core I ops B -> S_state B = DIGINET_S_ONLINE -> S_inflight B = 0 ->
  S_backoff_until_us B <= g_now B -> g_now B < S_next_keepalive_us B -> S_queued B <> 0 ->
  exists B' r, tick_take_m I F B (g_now B) = Some (B', r) /\ tick_post I ops B B'.
Proof.
  intros HL I F ops B HC Hst Hin Hbo Hka Hq.
  destruct (tick_take_keep HL I F ops B HC Hst Hin Hbo Hka Hq) as (B' & r & E & Hp & _). exists B', r. exact (conj E Hp).
Qed.

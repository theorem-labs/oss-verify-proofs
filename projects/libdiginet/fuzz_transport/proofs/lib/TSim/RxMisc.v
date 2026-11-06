(* A frame from the desk whose command is none of e0, e1, a0, 00, e3: m_rx's switch takes its default
   (FT:370-371) after `M.last_rx = g_now` (FT:301), the library counts it ignored (DS:313-315) after its
   rx_frames / last_rx_us (DS:296-297). The desk may have been learnt by both (FT:296-297, DS:290-291). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SimLib QueueFacts RxDefs RxBase
  RxList RxFrame RxW RxCore.
Import ListNotations.
Open Scope Z_scope.

(* the world functions stay folded for the unifier (RxW.v header); the getters unfold to them *)
Local Opaque sub upd u_at s32_at put.

Definition cond_other (B buf : list byte) : Prop :=
  fr_cmd buf <> DIGINET_CMD_ANNOUNCE /\ fr_cmd buf <> DIGINET_CMD_ANNOUNCE_SESSION /\
  fr_cmd buf <> DIGINET_CMD_ACK /\ fr_cmd buf <> DIGINET_CMD_DATA /\ fr_cmd buf <> DIGINET_CMD_DISCONNECT.

(* any reception of the operation: m_rx and the switch leave OW and GOT as they were, so the step is empty *)
Lemma rx_other_g : forall (HL : links), rx_branch_g cond_other.
Proof.
  intros HL. unfold rx_branch_g. intros I ops fr n B. cbv zeta. intros Hn Ha Hpre Hacc Hc.
  pose proof (rx_frame_ok HL fr n Hn (ra_code _ _ Hacc)) as Hf.
  destruct Hpre as [Hcore Hka Hroom Hfail Hsend].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  assert (HB : length B = WN) by exact Hlen.
  destruct Hc as (C1 & C2 & C3 & C4 & C5).
  pose proof (rf_cmd _ _ Hf) as Ecmd.
  pose proof (rf_src_len _ _ Hf) as Hsl.
  destruct (learn_M_frame B (rxbuf fr n) HB Hsl) as [Hlf Hll].
  destruct (learn_M_desk B (rxbuf fr n) HB Hsl (b2_desk_known01 _ Hst) (ra_known _ _ Hacc)) as [Lk Ld].
  remember (learn_M B (rxbuf fr n)) as Bk eqn:EBk.
  assert (E1 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_E0) = false) by (apply Z.eqb_neq; exact C1).
  assert (E2 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_E1) = false) by (apply Z.eqb_neq; exact C2).
  assert (E3 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_ACK) = false) by (apply Z.eqb_neq; exact C3).
  assert (E4 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_DATA) = false) by (apply Z.eqb_neq; exact C4).
  assert (E5 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_E3) = false) by (apply Z.eqb_neq; exact C5).
  assert (F1 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ANNOUNCE) = false) by (apply Z.eqb_neq; exact C1).
  assert (F2 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ANNOUNCE_SESSION) = false) by (apply Z.eqb_neq; exact C2).
  assert (F3 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ACK) = false) by (apply Z.eqb_neq; exact C3).
  assert (F4 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_DATA) = false) by (apply Z.eqb_neq; exact C4).
  assert (F5 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_DISCONNECT) = false) by (apply Z.eqb_neq; exact C5).
  (* the model's world after its switch *)
  remember (set_M_last_rx Bk (g_now B)) as Bm eqn:EBm.
  assert (HBm : length Bm = WN) by (subst Bm; wlen).
  assert (Hkm : wframe (in_rs [(A_M_last_rx, 8)]) Bk Bm) by (subst Bm; wfrs).
  assert (Mst : M_state Bm = M_state B) by (transitivity (M_state Bk); [subst Bm; wget | fget Hlf]).
  assert (Mws : M_wake_sent Bm = M_wake_sent B) by (transitivity (M_wake_sent Bk); [subst Bm; wget | fget Hlf]).
  assert (Mnw : g_now Bm = g_now B) by (transitivity (g_now Bk); [subst Bm; wget | fget Hlf]).
  assert (Mlr : M_last_rx Bm = g_now B) by (subst Bm; wget).
  assert (Mcw : Cfg_wake_timeout_ms Bm = Cfg_wake_timeout_ms B)
    by (transitivity (Cfg_wake_timeout_ms Bk); [subst Bm; wget | fget Hlf]).
  assert (Mco : Cfg_offline_ms Bm = Cfg_offline_ms B)
    by (transitivity (Cfg_offline_ms Bk); [subst Bm; wget | fget Hlf]).
  exists Bm. split; [|split; [|split]].
  - (* FT:302-371, the default *)
    unfold m_rx_sw. cbv zeta. rewrite Ecmd, E1, E2, E3, E4, E5. reflexivity.
  - (* FT:373 *)
    apply m_tick_quiet; rewrite ?Mst, ?Mws, ?Mnw, ?Mlr, ?Mcw, ?Mco.
    + intros Hw. split; [exact (c1_wake_sent _ _ Htime) | exact (c2_wake _ _ Htime Hw)].
    + intros _. pose proof (a1_offline _ Hcfg). lia.
    + pose proof (a1_wake_timeout _ Hcfg). lia.
    + pose proof (a1_offline _ Hcfg). lia.
  - (* the model wrote only M *)
    apply (wframe_rs_incl (R_learn ++ [(A_M_last_rx, 8)]) R_mod B Bm); [vm_compute; reflexivity|].
    exact (wframe_trans_rs _ _ _ _ _ Hlf Hkm).
  - intros W HW.
    pose proof HW as (HWf & HWk & HWm & HWl).
    assert (HWn : length W = WN) by (eapply wframe_len; [exact HWf | exact HBm]).
    exists (set_S_stats_rx_ignored W (u64 (S_stats_rx_ignored W + 1))). split.
    + (* DS:313-315 *)
      unfold rx_sw. cbv zeta. rewrite F1, F2, F3, F4, F5. reflexivity.
    + remember (set_S_stats_rx_ignored W (u64 (S_stats_rx_ignored W + 1))) as W' eqn:EW'.
      assert (HW' : wframe (in_rs [(A_S_stats_rx_ignored, 8)]) W W') by (subst W'; wfrs).
      pose proof (wframe_trans_rs _ _ _ _ _ HWf HW') as Hmw.
      pose proof (wframe_trans_rs _ _ _ _ _ (wframe_trans_rs _ _ _ _ _ Hlf Hkm) Hmw) as Hall.
      (* the written fields *)
      assert (W1 : M_desk_known W' = 1) by (rewrite <- Lk; transitivity (M_desk_known Bm); [fget Hmw | subst Bm; wget]).
      assert (W2 : M_desk W' = fr_src (rxbuf fr n)) by (rewrite <- Ld; transitivity (M_desk Bm); [fget Hmw | subst Bm; wget]).
      assert (W3 : M_last_rx W' = g_now B) by (rewrite <- Mlr; fget Hmw).
      assert (W4 : S_desk_known W' = 1) by (rewrite <- HWk; subst W'; wget).
      assert (W5 : S_desk_mac W' = fr_src (rxbuf fr n)) by (rewrite <- HWm; subst W'; wget).
      assert (W6 : S_last_rx_us W' = g_now B) by (rewrite <- Mnw, <- HWl; subst W'; wget).
      assert (W7 : g_rx W' = g_rx W) by (subst W'; wget).
      assert (W8 : g_rx_len W' = g_rx_len W) by (subst W'; wget).
      assert (W9 : g_rx_times W' = g_rx_times W) by (subst W'; wget).
      assert (W10 : g_rx_fail W' = g_rx_fail W) by (subst W'; wget).
      assert (W11 : g_rx_send W' = g_rx_send W) by (subst W'; wget).
      (* the fields nobody wrote *)
      assert (U1 : S_state W' = S_state B) by fget Hall.
      assert (U2 : M_state W' = M_state B) by fget Hall.
      assert (U3 : S_foreign W' = S_foreign B) by fget Hall.
      assert (U4 : M_foreign W' = M_foreign B) by fget Hall.
      assert (U5 : S_e1_named_us W' = S_e1_named_us B) by fget Hall.
      assert (U6 : M_e1_us W' = M_e1_us B) by fget Hall.
      assert (U7 : S_wake_acked W' = S_wake_acked B) by fget Hall.
      assert (U8 : M_e2_acked W' = M_e2_acked B) by fget Hall.
      assert (U9 : S_wake_sent_us W' = S_wake_sent_us B) by fget Hall.
      assert (U10 : M_wake_sent W' = M_wake_sent B) by fget Hall.
      assert (U11 : S_backoff_until_us W' = S_backoff_until_us B) by fget Hall.
      assert (U12 : M_backoff_until W' = M_backoff_until B) by fget Hall.
      assert (U13 : g_raw W' = g_raw B) by fget Hall.
      assert (U14 : S_next_keepalive_us W' = S_next_keepalive_us B) by fget Hall.
      assert (U15 : M_next_ka W' = M_next_ka B) by fget Hall.
      assert (U16 : S_display_sent W' = S_display_sent B) by fget Hall.
      assert (U17 : M_display_sent W' = M_display_sent B) by fget Hall.
      assert (U18 : S_last_display_us W' = S_last_display_us B) by fget Hall.
      assert (U19 : M_last_display W' = M_last_display B) by fget Hall.
      assert (U20 : S_desk_counter_valid W' = S_desk_counter_valid B) by fget Hall.
      assert (U21 : M_desk_counter_valid W' = M_desk_counter_valid B) by fget Hall.
      assert (U22 : S_desk_counter W' = S_desk_counter B) by fget Hall.
      assert (U23 : M_desk_counter W' = M_desk_counter B) by fget Hall.
      assert (U24 : S_host_counter W' = S_host_counter B) by fget Hall.
      assert (U25 : M_host_counter W' = M_host_counter B) by fget Hall.
      assert (U26 : M_fly_on W' = M_fly_on B) by fget Hall.
      assert (U33 : M_fly_sent W' = M_fly_sent B) by fget Hall.
      assert (U37 : Cfg_max_retries W' = Cfg_max_retries B) by fget Hall.
      assert (U38 : Cfg_sum_mode W' = Cfg_sum_mode B) by fget Hall.
      assert (U39 : g_now W' = g_now B) by fget Hall.
      assert (U40 : Cfg_wake_timeout_ms W' = Cfg_wake_timeout_ms B) by fget Hall.
      assert (U41 : Cfg_offline_ms W' = Cfg_offline_ms B) by fget Hall.
      assert (U42 : Cfg_ack_timeout_ms W' = Cfg_ack_timeout_ms B) by fget Hall.
      assert (U43 : g_fail_next W' = g_fail_next B) by fget Hall.
      assert (U44 : S_personality W' = S_personality B) by fget Hall.
      assert (Hst' : agree_st W').
      { constructor; rw_eqs W'.
        - exact (b1_state _ Hst).
        - exact (b1_state_range _ Hst).
        - reflexivity.
        - right; reflexivity.
        - intros _; reflexivity.
        - exact (b3_foreign _ Hst).
        - exact (b3_foreign01 _ Hst).
        - exact (b3_e1 _ Hst).
        - exact (b3_e1_01 _ Hst).
        - exact (b3_e2 _ Hst).
        - exact (b3_e2_01 _ Hst).
        - exact (b4_wake_sent _ Hst).
        - reflexivity.
        - exact (b4_backoff _ Hst).
        - exact (b5_next_ka _ Hst).
        - exact (b5_display_sent _ Hst).
        - exact (b5_display_sent01 _ Hst).
        - exact (b5_last_display _ Hst).
        - exact (b6_valid _ Hst).
        - exact (b6_valid01 _ Hst).
        - exact (b6_counter _ Hst).
        - exact (b7_host_counter _ Hst).
        - exact (b9_idle _ Hst).
        - intros _; reflexivity. }
      assert (Hfl' : agree_fly W').
      { apply (agree_fly_fr _ B W' Hall); [vm_compute; reflexivity | vm_compute; reflexivity | exact U24
          | exact U37 | exact U38 | | exact Hfly].
        intros Hon. split.
        - rewrite W2. apply (ra_known _ _ Hacc). apply (b9_known _ Hst). exact (b8_state _ Hfly Hon).
        - rewrite U2. exact (b8_state _ Hfly Hon). }
      assert (Hti' : agree_time ops W').
      { constructor; rw_eqs W'.
        - exact (c_now _ _ Htime).
        - apply Z.le_refl.
        - exact (c1_wake_sent _ _ Htime).
        - exact (c1_fly_sent _ _ Htime).
        - exact (c1_last_display _ _ Htime).
        - exact (c1_backoff _ _ Htime).
        - exact (c1_next_ka _ _ Htime).
        - exact (c2_wake _ _ Htime).
        - intros _. rewrite Z.sub_diag. pose proof (a1_offline _ Hcfg). slia.
        - exact (c2_fly _ _ Htime). }
      assert (Hmi' : agree_misc I W').
      { constructor; rw_eqs W'; [exact (e1_fail_next _ _ Hmisc) | exact (e2_personality _ _ Hmisc)]. }
      constructor; [constructor | | |].
      * apply (agree_core_rx I ops B W' Hcore); [| exact Hst' | exact Hfl' | exact Hti' | exact Hmi'].
        eapply wframe_rx; [| exact Hall]. vm_compute. reflexivity.
      * (* neither side wrote OW or GOT *)
        apply (ow_got_eq_fr _ B W' Hall); [vm_compute; reflexivity | exact (wr_og _ Hroom)].
      * exact W7.
      * exact W8.
      * exact W9.
      * exact W10.
      * rewrite U39, <- Mnw. symmetry. fget HWf.
      * apply (ow_step_fr _ B B W' Hall); [vm_compute; reflexivity | apply ow_step_refl].
      * exact W11.
      * (* only an e0 wakes (FT:315-318) *)
        unfold rx_wake_buf. intros [Hw _]. exfalso. exact (C1 Hw).
Qed.

Lemma rx_other : forall (HL : links), rx_branch cond_other.
Proof. intros HL. exact (rx_branch_of_g cond_other (rx_other_g HL)). Qed.

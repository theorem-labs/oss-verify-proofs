(* Modified by Theorem Labs, 2026-10: new file, operation 5 (wake) of the fuzz_transport harness keeps the simulation invariant: the refusals, the failed send, and the send from WAKING (a Theorem Labs lane). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SendOk SimLib SettleOk WakeOk WakeBase.
Import ListNotations.
Open Scope Z_scope.

(* the desk unknown (FT:220-221, DS:123-124): E_ARG on both sides, nothing written *)
Lemma op5_unknown : forall I ops W0 c1 k, agree I ops W0 -> opz W0 -> M_desk_known W0 = 0 -> 0 <= ops < OPS_MAX ->
  op5_body I W0 c1 k = Some (W0, (c1, k)) /\ agree I (ops + 1) W0.
Proof.
  intros I ops W0 c1 k HA Hz Hk Ho.
  pose proof (b2_desk_known _ (ac_st _ _ _ (ag_core _ _ _ HA))) as Hs.
  unfold op5_body. rewrite (m_wake_unknown W0 Hk). cbv beta iota.
  rewrite (lib_wake_unknown I None W0 (g_now W0) ltac:(rewrite Hs; exact Hk)). cbv beta iota.
  unfold check_state_wake_code_m. kdec.
  rewrite (settle0 I ops W0 HA (opz_settle W0 Hz)). cbv beta iota.
  split; [exact eq_refl|]. apply (agree_mono I ops (ops + 1) W0 HA). lia.
Qed.

(* the desk foreign (FT:222-223, DS:125-128): E_REFUSED on both sides; the library counts the refusal *)
Lemma op5_foreign : forall I ops W0 c1 k, agree I ops W0 -> opz W0 -> M_desk_known W0 <> 0 -> M_foreign W0 <> 0 ->
  0 <= ops < OPS_MAX ->
  op5_body I W0 c1 k = Some (set_S_stats_refused W0 (u64 (S_stats_refused W0 + 1)), (c1, k)) /\
  agree I (ops + 1) (set_S_stats_refused W0 (u64 (S_stats_refused W0 + 1))).
Proof.
  intros I ops W0 c1 k HA Hz Hk Hf Ho.
  pose proof (ac_len _ _ _ (ag_core _ _ _ HA)) as HB.
  pose proof (ac_st _ _ _ (ag_core _ _ _ HA)) as Hst.
  set (W1 := set_S_stats_refused W0 (u64 (S_stats_refused W0 + 1))).
  assert (Hw : wsame W0 W1 [(A_S_stats_refused, 8)]) by (unfold W1; wsame_tac).
  assert (HA1 : agree I ops W1)
    by (apply (agree_frame I ops ops W0 W1 _ HA ltac:(lia) Hw); vm_compute; reflexivity).
  assert (Hz1 : opz W1) by (apply (opz_frame W0 W1 _ Hz Hw); vm_compute; reflexivity).
  unfold op5_body. rewrite (m_wake_foreign W0 Hk Hf). cbv beta iota.
  rewrite (lib_wake_foreign I None W0 (g_now W0) ltac:(rewrite (b2_desk_known _ Hst); exact Hk)
             ltac:(rewrite (b3_foreign _ Hst); exact Hf)).
  cbv beta iota. fold W1.
  unfold check_state_wake_code_m. kdec.
  rewrite (settle0 I ops W1 HA1 (opz_settle W1 Hz1)). cbv beta iota.
  split; [exact eq_refl|]. apply (agree_mono I ops (ops + 1) W1 HA1). lia.
Qed.

(* the wake fails (FT:227-230; DS:136-138: io_send returned -EIO): the flags and wake_sent on both sides, the
   E2 counted, nothing in flight changes *)
Lemma op5_fail : forall (HL : links) I ops W0 c1 k, agree I ops W0 -> opz W0 -> M_desk_known W0 = 1 ->
  M_foreign W0 = 0 -> g_fail_next W0 = 1 -> 0 <= ops < OPS_MAX ->
  exists W5, op5_body I W0 c1 k = Some (W5, (c1, k)) /\ agree I (ops + 1) W5.
Proof.
  intros HL I ops W0 c1 k HA Hz Dk Fo Fn Ho.
  pose proof HA as [HC HK HR]. pose proof (ac_len _ _ _ HC) as HB.
  pose proof Hz as (Zon & Zgn & Zoe & Zge & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Zf).
  unfold op5_body.
  rewrite (m_wake_ok W0 HB ltac:(rewrite Dk; discriminate) Fo ltac:(rewrite Zoe; unfold INT_MAX; lia)
             ltac:(rewrite Zon; unfold INT_MAX; lia)).
  cbv beta iota. unfold m_wake_w. rewrite Zf, Fn. kdec.
  set (Wm := m_wake_pre W0).
  assert (HWl : length Wm = Z.to_nat W_LEN) by (unfold Wm, m_wake_pre; wlen).
  rewrite (wake_lib_at HL I ops W0 Wm HC Hz Dk Fo HWl
             ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)
             ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)
             ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)
             ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)
             ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)
             ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)
             ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)
             ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)).
  rewrite Fn. kdec.
  unfold check_state_wake_code_m. kdec.
  set (f := wake_frame (M_desk W0) (S_host_counter W0) (Cfg_sum_mode W0)).
  set (W5 := io_e2_w (lw_pre Wm (g_now Wm)) f (S_host_counter W0)).
  (* the failed send writes no frame in flight: io_e2_w's failing branch *)
  assert (EW : W5 = set_g_last_counter (set_GOT_e2 (set_g_fail_next (lw_pre Wm (g_now Wm)) 0)
                      (GOT_e2 (lw_pre Wm (g_now Wm)) + 1)) (S_host_counter W0)).
  { unfold W5, io_e2_w. cbv zeta.
    assert (E : g_fail_next (lw_pre Wm (g_now Wm)) = 1)
      by (rewrite <- Fn; unfold lw_pre, Wm, m_wake_pre; wframe_eq).
    rewrite E. kdec. synrefl. }
  set (rs5 := [(A_M_e2_acked, 4); (A_M_e1_us, 4); (A_M_wake_sent, 8); (A_OW_e2, 4); (A_M_fail, 4);
               (A_S_e1_named_us, 4); (A_S_wake_acked, 4); (A_S_wake_sent_us, 8); (OFF_g_fail_next, 1);
               (A_GOT_e2, 4); (OFF_g_last_counter, 4)]).
  assert (Hw : wsame W0 W5 rs5) by (rewrite EW; unfold lw_pre, Wm, m_wake_pre, rs5; wsame_tac).
  assert (HA5 : agree I (ops + 1) W5).
  { constructor; [constructor|..].
    - exact (ac_img _ _ _ HC).
    - rewrite EW. unfold lw_pre, Wm, m_wake_pre. wlen.
    - exact (agree_cfg_ff W0 W5 rs5 Hw ltac:(vm_compute; reflexivity) (ac_cfg _ _ _ HC)).
    - exact (agree_io_ff I W0 W5 rs5 Hw ltac:(vm_compute; reflexivity) (ac_io _ _ _ HC)).
    - constructor; rewrite EW; unfold lw_pre, Wm, m_wake_pre; oclose HC HK Hz.
    - exact (agree_fly_ff W0 W5 rs5 Hw ltac:(vm_compute; reflexivity) (ac_fly _ _ _ HC)).
    - constructor; rewrite EW; unfold lw_pre, Wm, m_wake_pre; oclose HC HK Hz.
    - exact (agree_q_frame ops (ops + 1) W0 W5 rs5 (ac_q _ _ _ HC) ltac:(lia) Hw ltac:(vm_compute; reflexivity)).
    - constructor; rewrite EW; unfold lw_pre, Wm, m_wake_pre; oclose HC HK Hz.
    - rewrite EW; unfold lw_pre, Wm, m_wake_pre; oclose HC HK Hz.
    - rewrite EW; unfold lw_pre, Wm, m_wake_pre; oclose HC HK Hz. }
  assert (HS5 : settle_eq W5).
  { constructor; rewrite EW; unfold lw_pre, Wm, m_wake_pre; oclose HC HK Hz. }
  rewrite (settle0 I (ops + 1) W5 HA5 HS5). cbv beta iota.
  exists W5. split; [exact eq_refl | exact HA5].
Qed.

(* the wake succeeds (FT:231-232; DS:139-144) and the state was WAKING already: the E2 in flight on both sides *)
Lemma op5_same : forall (HL : links) I ops W0 c1 k, agree I ops W0 -> opz W0 -> M_desk_known W0 = 1 ->
  M_foreign W0 = 0 -> g_fail_next W0 = 0 -> M_state W0 = S_WAKING -> 0 <= ops < OPS_MAX ->
  exists W5, op5_body I W0 c1 k = Some (W5, (c1, k)) /\ agree I (ops + 1) W5.
Proof.
  intros HL I ops W0 c1 k HA Hz Dk Fo Fn Sw0 Ho.
  pose proof HA as [HC HK HR]. pose proof (ac_len _ _ _ HC) as HB.
  pose proof (ac_st _ _ _ HC) as Hst.
  pose proof Hz as (Zon & Zgn & Zoe & Zge & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Zf).
  pose proof (wake_frame_len HL (M_desk W0) (S_host_counter W0) (Cfg_sum_mode W0)
                ltac:(unfold M_desk; apply length_sub; [wle|]; rewrite HB; wle)
                (a1_sum_mode _ (ac_cfg _ _ _ HC)) (host_counter_range W0)) as Hlf.
  unfold op5_body.
  rewrite (m_wake_ok W0 HB ltac:(rewrite Dk; discriminate) Fo ltac:(rewrite Zoe; unfold INT_MAX; lia)
             ltac:(rewrite Zon; unfold INT_MAX; lia)).
  cbv beta iota. unfold m_wake_w. rewrite Zf, Fn. kdec.
  (* m_set (FT:196-207) on the model's world: WAKING unless it already was *)
  assert (EP1 : M_state (m_wake_pre W0) = M_state W0) by (unfold m_wake_pre; wframe_eq).
  assert (EP2 : OW_n (m_wake_pre W0) = 0) by (transitivity (OW_n W0); [unfold m_wake_pre; wframe_eq | exact Zon]).
  unfold m_set_w. rewrite EP1, EP2. kdec.
  destruct (Z.eqb_spec (M_state W0) S_WAKING) as [Sw|Sw]; [|exfalso; exact (Sw Sw0)].
  (* already WAKING (FT:198-199, DS:81-82): no transition on either side *)
    cbv beta iota. set (Wm := m_wake_pre W0).
    assert (HWl : length Wm = Z.to_nat W_LEN) by (unfold Wm, m_wake_pre; wlen).
    rewrite (wake_lib_at HL I ops W0 Wm HC Hz Dk Fo HWl
               ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)
               ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)
               ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)
               ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)
               ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)
               ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)
               ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)
               ltac:(unfold Wm, m_wake_pre; wframe_eq) ltac:(unfold Wm, m_wake_pre; wframe_eq)).
    rewrite Fn. kdec.
    unfold check_state_wake_code_m. kdec.
    set (W5 := lw_done (lw_sent (lw_pre Wm (g_now Wm)) (wake_frame (M_desk W0) (S_host_counter W0) (Cfg_sum_mode W0))
                 (S_host_counter W0)) (wake_frame (M_desk W0) (S_host_counter W0) (Cfg_sum_mode W0)) (g_now Wm)).
    eassert (EW : W5 = _).
    { unfold W5, lw_done, lw_sent, io_e2_w, set_state_w. cbv zeta.
      match goal with |- context [g_fail_next ?X =? 0] =>
        assert (E1 : g_fail_next X = 0)
          by (transitivity (g_fail_next W0); [unfold lw_pre, Wm, m_wake_pre; wframe_eq | exact Fn]);
        rewrite E1 end.
      kdec.
      match goal with |- context [S_state ?X =? DIGINET_S_WAKING] =>
        assert (E2 : S_state X = DIGINET_S_WAKING)
          by (transitivity (S_state W0);
              [ unfold lw_pre, Wm, m_wake_pre; wframe_eq
              | rewrite (b1_state _ Hst), Sw; reflexivity ]);
        rewrite E2 end.
      kdec. unfold lw_pre, Wm, m_wake_pre. exact eq_refl. }
    assert (Hw : wsame W0 W5 rs_wake) by (rewrite EW; unfold rs_wake; wsame_tac).
    assert (HA5 : agree I (ops + 1) W5).
    { constructor; [constructor|..].
      - exact (ac_img _ _ _ HC).
      - rewrite EW. wlen.
      - exact (agree_cfg_ff W0 W5 rs_wake Hw ltac:(vm_compute; reflexivity) (ac_cfg _ _ _ HC)).
      - exact (agree_io_ff I W0 W5 rs_wake Hw ltac:(vm_compute; reflexivity) (ac_io _ _ _ HC)).
      - constructor; oclose2 HC HK Hz Hw EW.
      - constructor; first [oclose2 HC HK Hz Hw EW | frames_e2 Hw EW].
      - constructor; oclose2 HC HK Hz Hw EW.
      - exact (agree_q_frame ops (ops + 1) W0 W5 rs_wake (ac_q _ _ _ HC) ltac:(lia) Hw
                 ltac:(vm_compute; reflexivity)).
      - constructor; oclose2 HC HK Hz Hw EW.
      - oclose2 HC HK Hz Hw EW.
      - oclose2 HC HK Hz Hw EW. }
    assert (HS5 : settle_eq W5).
    { constructor; oclose2 HC HK Hz Hw EW. }
    rewrite (settle0 I (ops + 1) W5 HA5 HS5). cbv beta iota.
    exists W5. split; [exact eq_refl | exact HA5].
Qed.

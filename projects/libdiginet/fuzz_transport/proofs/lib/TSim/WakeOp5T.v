(* Modified by Theorem Labs, 2026-10: new file, operation 5 (wake) of the fuzz_transport harness keeps the simulation invariant: the send from a state other than WAKING (a Theorem Labs lane). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SendOk SimLib SettleOk WakeOk WakeBase.
Import ListNotations.
Open Scope Z_scope.

(* the wake succeeds (FT:231-232; DS:139-144) from a state other than WAKING: the E2 in flight on both sides, one
   transition to WAKING on each side *)
Lemma op5_trans : forall (HL : links) I ops W0 c1 k, agree I ops W0 -> opz W0 -> M_desk_known W0 = 1 ->
  M_foreign W0 = 0 -> g_fail_next W0 = 0 -> M_state W0 <> S_WAKING -> 0 <= ops < OPS_MAX ->
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
  destruct (Z.eqb_spec (M_state W0) S_WAKING) as [Sw|Sw]; [exfalso; exact (Sw0 Sw)|].
  (* not WAKING: one transition to WAKING on each side (FT:200-206; DS:83-85 with notice FT:941-947) *)
    cbv beta iota.
    set (Wm := set_M_state
                 (set_OW_n (set_OW_t_reason (set_OW_t_old (set_OW_t_state (m_wake_pre W0) 0 S_WAKING) 0 (M_state W0))
                    0 R_WAKE) (0 + 1)) S_WAKING).
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
    { unfold W5, lw_done, lw_sent, io_e2_w, set_state_w, got_set_w. cbv zeta.
      match goal with |- context [g_fail_next ?X =? 0] =>
        assert (E1 : g_fail_next X = 0)
          by (transitivity (g_fail_next W0); [unfold lw_pre, Wm, m_wake_pre; wframe_eq | exact Fn]);
        rewrite E1 end.
      kdec.
      match goal with |- context [S_state ?X =? DIGINET_S_WAKING] =>
        assert (E2 : S_state X = M_state W0)
          by (transitivity (S_state W0); [unfold lw_pre, Wm, m_wake_pre; wframe_eq | exact (b1_state _ Hst)]);
        rewrite E2 end.
      destruct (Z.eqb_spec (M_state W0) DIGINET_S_WAKING) as [E3|_]; [exfalso; apply Sw; exact E3|].
      cbv beta iota.
      match goal with |- context [GOT_n ?X <? TRANS_MAX] =>
        assert (E4 : GOT_n X = 0)
          by (transitivity (GOT_n W0); [unfold lw_pre, Wm, m_wake_pre; wframe_eq | exact Zgn]);
        rewrite E4 end.
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
    { constructor; first [oclose2 HC HK Hz Hw EW | (apply se_t_one_entry; oclose2 HC HK Hz Hw EW)]. }
    rewrite (settle0 I (ops + 1) W5 HA5 HS5). cbv beta iota.
    exists W5. split; [exact eq_refl | exact HA5].
Qed.

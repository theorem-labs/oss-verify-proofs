(* Modified by Theorem Labs, 2026-10: new file, operation 6 (close) of the fuzz_transport harness keeps the simulation invariant (a Theorem Labs lane). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SendOk SimLib SettleOk WakeOk WakeBase.
Import ListNotations.
Open Scope Z_scope.

(* the close sends its E3 (FT:380-382; DS:153-154), both sides go CLOSED with nothing in flight *)
Lemma op6_send : forall (HL : links) I ops W0 c1 k, agree I ops W0 -> opz W0 -> M_desk_known W0 = 1 ->
  M_foreign W0 = 0 -> M_state W0 <> S_CLOSED -> 0 <= ops < OPS_MAX ->
  exists W6, op6_body I W0 c1 k = Some (W6, (c1, k)) /\ agree I (ops + 1) W6.
Proof.
  intros HL I ops W0 c1 k HA Hz Dk Fo Sc Ho.
  pose proof HA as [HC HK HR]. pose proof (ac_len _ _ _ HC) as HB.
  pose proof (ac_st _ _ _ HC) as Hst. pose proof (ac_misc _ _ _ HC) as Hmi.
  pose proof Hz as (Zon & Zgn & Zoe & Zge & Zo3 & Zg3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Zf).
  unfold op6_body.
  rewrite (m_close_ok W0 HB ltac:(rewrite Zo3; unfold INT_MAX; lia) ltac:(rewrite Zon; unfold INT_MAX; lia)).
  cbv beta iota. unfold m_close_w. cbv zeta. unfold truth.
  rewrite Dk, Fo. destruct (Z.eqb_spec (M_state W0) S_CLOSED) as [E|_]; [contradiction|]. kdec.
  unfold m_set_w.
  assert (EP1 : M_state (set_M_fly_on (set_M_fail (set_OW_e3 W0 (OW_e3 W0 + 1)) 0) 0) = M_state W0) by wframe_eq.
  assert (EP2 : OW_n (set_M_fly_on (set_M_fail (set_OW_e3 W0 (OW_e3 W0 + 1)) 0) 0) = 0)
    by (transitivity (OW_n W0); [wframe_eq | exact Zon]).
  rewrite EP1, EP2. destruct (Z.eqb_spec (M_state W0) S_CLOSED) as [E|_]; [contradiction|]. kdec.
  set (Wm := set_M_state
               (set_OW_n (set_OW_t_reason (set_OW_t_old (set_OW_t_state
                  (set_M_fly_on (set_M_fail (set_OW_e3 W0 (OW_e3 W0 + 1)) 0) 0) 0 S_CLOSED) 0 (M_state W0))
                  0 R_CLOSED) (0 + 1)) S_CLOSED).
  assert (HWl : length Wm = Z.to_nat W_LEN) by (unfold Wm; wlen).
  rewrite (close_lib_send HL I ops W0 Wm HC Hz HWl
             ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq)
             ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq)
             ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq) (g_now Wm) Dk Fo Sc).
  cbv beta iota.
  set (W6 := set_state_w (set_S_inflight (lc_sent Wm) 0) DIGINET_S_CLOSED DIGINET_R_CLOSED).
  assert (Gf : g_fail_next Wm = g_fail_next W0) by (unfold Wm; wframe_eq).
  destruct (e1_fail_next _ _ Hmi) as [Fn|Fn];
  (eassert (EW : W6 = _);
   [ unfold W6, set_state_w, got_set_w, lc_sent, io_e3_w; cbv zeta;
     rewrite Gf, Fn; kdec;
     match goal with |- context [S_state ?X =? DIGINET_S_CLOSED] =>
       assert (E2 : S_state X = M_state W0)
         by (transitivity (S_state W0); [unfold Wm; wframe_eq | exact (b1_state _ Hst)]);
       rewrite E2 end;
     destruct (Z.eqb_spec (M_state W0) DIGINET_S_CLOSED) as [E3|_]; [exfalso; apply Sc; exact E3|];
     cbv beta iota;
     match goal with |- context [GOT_n ?X <? TRANS_MAX] =>
       assert (E4 : GOT_n X = 0) by (transitivity (GOT_n W0); [unfold Wm; wframe_eq | exact Zgn]);
       rewrite E4 end;
     kdec; unfold Wm; exact eq_refl
   | ]);
  (assert (Hw : wsame W0 W6 rs_wake) by (rewrite EW; unfold rs_wake; wsame_tac));
  (assert (HA6 : agree I (ops + 1) W6);
   [ constructor; [constructor|..];
     [ exact (ac_img _ _ _ HC)
     | rewrite EW; wlen
     | exact (agree_cfg_ff W0 W6 rs_wake Hw ltac:(vm_compute; reflexivity) (ac_cfg _ _ _ HC))
     | exact (agree_io_ff I W0 W6 rs_wake Hw ltac:(vm_compute; reflexivity) (ac_io _ _ _ HC))
     | constructor; oclose2 HC HK Hz Hw EW
     | constructor; first [ (rewrite EW; ovac) | oclose2 HC HK Hz Hw EW ]
     | constructor; oclose2 HC HK Hz Hw EW
     | exact (agree_q_frame ops (ops + 1) W0 W6 rs_wake (ac_q _ _ _ HC) ltac:(lia) Hw
                ltac:(vm_compute; reflexivity))
     | constructor; oclose2 HC HK Hz Hw EW
     | oclose2 HC HK Hz Hw EW
     | oclose2 HC HK Hz Hw EW ]
   | ]);
  (assert (HS6 : settle_eq W6) by (constructor; first [oclose2 HC HK Hz Hw EW | (apply se_t_one_entry; oclose2 HC HK Hz Hw EW)]));
  (rewrite (settle0 I (ops + 1) W6 HA6 HS6); cbv beta iota;
   exists W6; split; [exact eq_refl | exact HA6]).
Qed.

(* the close sends nothing (FT:380, DS:153: desk unknown, foreign, or already closed): both sides go CLOSED *)
Lemma op6_nosend : forall I ops W0 c1 k, agree I ops W0 -> opz W0 ->
  (M_desk_known W0 = 0 \/ M_foreign W0 <> 0 \/ M_state W0 = S_CLOSED) -> 0 <= ops < OPS_MAX ->
  exists W6, op6_body I W0 c1 k = Some (W6, (c1, k)) /\ agree I (ops + 1) W6.
Proof.
  intros I ops W0 c1 k HA Hz Hc Ho.
  pose proof HA as [HC HK HR]. pose proof (ac_len _ _ _ HC) as HB.
  pose proof (ac_st _ _ _ HC) as Hst.
  pose proof Hz as (Zon & Zgn & Zoe & Zge & Zo3 & Zg3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Zf).
  unfold op6_body.
  rewrite (m_close_ok W0 HB ltac:(rewrite Zo3; unfold INT_MAX; lia) ltac:(rewrite Zon; unfold INT_MAX; lia)).
  cbv beta iota. unfold m_close_w. cbv zeta.
  assert (Cm : (truth (M_desk_known W0) && negb (truth (M_foreign W0)) && negb (M_state W0 =? S_CLOSED)) = false).
  { unfold truth. destruct (Z.eqb_spec (M_desk_known W0) 0); destruct (Z.eqb_spec (M_foreign W0) 0);
      destruct (Z.eqb_spec (M_state W0) S_CLOSED); cbv [andb negb]; first [ exact eq_refl | exfalso; lia ]. }
  rewrite Cm. cbv beta iota.
  unfold m_set_w.
  assert (EP1 : M_state (set_M_fly_on W0 0) = M_state W0) by wframe_eq.
  assert (EP2 : OW_n (set_M_fly_on W0 0) = 0) by (transitivity (OW_n W0); [wframe_eq | exact Zon]).
  rewrite EP1, EP2. kdec.
  destruct (Z.eqb_spec (M_state W0) S_CLOSED) as [Sc|Sc]; cbv beta iota.
  - (* already CLOSED: no transition *)
    set (Wm := set_M_fly_on W0 0).
    assert (HWl : length Wm = Z.to_nat W_LEN) by (unfold Wm; wlen).
    rewrite (close_lib_nosend I ops W0 Wm HC Hz HWl
               ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq)
               ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq) (g_now Wm) Hc).
    cbv beta iota.
    set (W6 := set_state_w (set_S_inflight Wm 0) DIGINET_S_CLOSED DIGINET_R_CLOSED).
    eassert (EW : W6 = _).
    { unfold W6, set_state_w.
      match goal with |- context [S_state ?X =? DIGINET_S_CLOSED] =>
        assert (E2 : S_state X = M_state W0)
          by (transitivity (S_state W0); [unfold Wm; wframe_eq | exact (b1_state _ Hst)]);
        rewrite E2 end.
      rewrite Sc. kdec. unfold Wm. exact eq_refl. }
    assert (Hw : wsame W0 W6 rs_wake) by (rewrite EW; unfold rs_wake; wsame_tac).
    assert (HA6 : agree I (ops + 1) W6).
    { constructor; [constructor|..].
      - exact (ac_img _ _ _ HC).
      - rewrite EW. wlen.
      - exact (agree_cfg_ff W0 W6 rs_wake Hw ltac:(vm_compute; reflexivity) (ac_cfg _ _ _ HC)).
      - exact (agree_io_ff I W0 W6 rs_wake Hw ltac:(vm_compute; reflexivity) (ac_io _ _ _ HC)).
      - constructor; oclose2 HC HK Hz Hw EW.
      - constructor; first [ (rewrite EW; ovac) | oclose2 HC HK Hz Hw EW ].
      - constructor; oclose2 HC HK Hz Hw EW.
      - exact (agree_q_frame ops (ops + 1) W0 W6 rs_wake (ac_q _ _ _ HC) ltac:(lia) Hw
                 ltac:(vm_compute; reflexivity)).
      - constructor; oclose2 HC HK Hz Hw EW.
      - oclose2 HC HK Hz Hw EW.
      - oclose2 HC HK Hz Hw EW. }
    assert (HS6 : settle_eq W6).
    { constructor; oclose2 HC HK Hz Hw EW. }
    rewrite (settle0 I (ops + 1) W6 HA6 HS6). cbv beta iota.
    exists W6. split; [exact eq_refl | exact HA6].
  - (* one transition to CLOSED on each side *)
    set (Wm := set_M_state
                 (set_OW_n (set_OW_t_reason (set_OW_t_old (set_OW_t_state (set_M_fly_on W0 0) 0 S_CLOSED) 0
                    (M_state W0)) 0 R_CLOSED) (0 + 1)) S_CLOSED).
    assert (HWl : length Wm = Z.to_nat W_LEN) by (unfold Wm; wlen).
    rewrite (close_lib_nosend I ops W0 Wm HC Hz HWl
               ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq)
               ltac:(unfold Wm; wframe_eq) ltac:(unfold Wm; wframe_eq) (g_now Wm) Hc).
    cbv beta iota.
    set (W6 := set_state_w (set_S_inflight Wm 0) DIGINET_S_CLOSED DIGINET_R_CLOSED).
    eassert (EW : W6 = _).
    { unfold W6, set_state_w, got_set_w.
      match goal with |- context [S_state ?X =? DIGINET_S_CLOSED] =>
        assert (E2 : S_state X = M_state W0)
          by (transitivity (S_state W0); [unfold Wm; wframe_eq | exact (b1_state _ Hst)]);
        rewrite E2 end.
      destruct (Z.eqb_spec (M_state W0) DIGINET_S_CLOSED) as [E3|_]; [exfalso; apply Sc; exact E3|].
      cbv beta iota.
      match goal with |- context [GOT_n ?X <? TRANS_MAX] =>
        assert (E4 : GOT_n X = 0) by (transitivity (GOT_n W0); [unfold Wm; wframe_eq | exact Zgn]);
        rewrite E4 end.
      kdec. unfold Wm. exact eq_refl. }
    assert (Hw : wsame W0 W6 rs_wake) by (rewrite EW; unfold rs_wake; wsame_tac).
    assert (HA6 : agree I (ops + 1) W6).
    { constructor; [constructor|..].
      - exact (ac_img _ _ _ HC).
      - rewrite EW. wlen.
      - exact (agree_cfg_ff W0 W6 rs_wake Hw ltac:(vm_compute; reflexivity) (ac_cfg _ _ _ HC)).
      - exact (agree_io_ff I W0 W6 rs_wake Hw ltac:(vm_compute; reflexivity) (ac_io _ _ _ HC)).
      - constructor; oclose2 HC HK Hz Hw EW.
      - constructor; first [ (rewrite EW; ovac) | oclose2 HC HK Hz Hw EW ].
      - constructor; oclose2 HC HK Hz Hw EW.
      - exact (agree_q_frame ops (ops + 1) W0 W6 rs_wake (ac_q _ _ _ HC) ltac:(lia) Hw
                 ltac:(vm_compute; reflexivity)).
      - constructor; oclose2 HC HK Hz Hw EW.
      - oclose2 HC HK Hz Hw EW.
      - oclose2 HC HK Hz Hw EW. }
    assert (HS6 : settle_eq W6).
    { constructor; first [oclose2 HC HK Hz Hw EW | (apply se_t_one_entry; oclose2 HC HK Hz Hw EW)]. }
    rewrite (settle0 I (ops + 1) W6 HA6 HS6). cbv beta iota.
    exists W6. split; [exact eq_refl | exact HA6].
Qed.

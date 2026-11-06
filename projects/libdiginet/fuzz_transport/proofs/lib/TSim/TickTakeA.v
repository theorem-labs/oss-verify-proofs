(* tt_post_ok: a run of tick_take_m (diginet_session.c:460-471) that started in agree_core, ONLINE, nothing in flight,
   and whose world after the run satisfies tt_end and agree_q, ends in tick_post.
   The getters the run does not write keep B's value (tta_fe_*: the frame te_frame over R_tt); the written ones come
   from tt_end. Every step is an `exact` of a term whose type is the goal, or of a lemma over plain Z values (tta_tr*,
   tta_eq2, tta_disp_*, ...): no unification compares two different world terms (TRAP, SettleOk.v / TickTakeW.v). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links QueueFacts SimLib SendOk SettleOk
  TickDefs TakeOk TickTakeW.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- transport over plain values *)

Lemma tta_tr1 : forall {A : Type} (P : A -> Prop) (a a' : A), a = a' -> P a' -> P a.
Proof. intros A P a a' -> H. exact H. Qed.

Lemma tta_tr2 : forall {A1 A2 : Type} (P : A1 -> A2 -> Prop) (a : A1) (b : A2) a' b',
  a = a' -> b = b' -> P a' b' -> P a b.
Proof. intros A1 A2 P a b a' b' -> -> H. exact H. Qed.

Lemma tta_tr3 : forall {A1 A2 A3 : Type} (P : A1 -> A2 -> A3 -> Prop) (a : A1) (b : A2) (c : A3) a' b' c',
  a = a' -> b = b' -> c = c' -> P a' b' c' -> P a b c.
Proof. intros A1 A2 A3 P a b c a' b' c' -> -> -> H. exact H. Qed.

Lemma tta_eq2 : forall {A : Type} (s s' m m' : A), s = s' -> m = m' -> s' = m' -> s = m.
Proof. intros A s s' m m' -> -> H. exact H. Qed.

(* b5's display clauses after the run (te_ds / te_ms, te_dl / te_ml), tagged *)
Lemma tta_disp_eq : forall r hd sB mB sF mF : Z, r = 0 -> sB = mB ->
  sF = (if hd =? 0 then sB else 1) -> mF = (if (r =? 0) && negb (hd =? 0) then 1 else mB) -> sF = mF.
Proof. intros r hd sB mB sF mF -> E -> ->. destruct (hd =? 0); cbn; [exact E | reflexivity]. Qed.

Lemma tta_disp01 : forall r hd mB mF : Z, r = 0 -> bit01 mB ->
  mF = (if (r =? 0) && negb (hd =? 0) then 1 else mB) -> bit01 mF.
Proof. intros r hd mB mF -> H ->. unfold bit01 in *. destruct (hd =? 0); cbn; [exact H | right; reflexivity]. Qed.

Lemma tta_ld_eq : forall r hd sB mB sF mF now : Z, r = 0 -> sB = mB ->
  sF = (if hd =? 0 then sB else now) -> mF = (if (r =? 0) && negb (hd =? 0) then now else mB) -> sF = mF.
Proof. intros r hd sB mB sF mF now -> E -> ->. destruct (hd =? 0); cbn; [exact E | reflexivity]. Qed.

(* C1's display clause after the run *)
Lemma tta_ld_le : forall r hd mdB mlB mdF mlF now nowF : Z, nowF = now -> (mdB <> 0 -> mlB <= now) ->
  mdF = (if (r =? 0) && negb (hd =? 0) then 1 else mdB) ->
  mlF = (if (r =? 0) && negb (hd =? 0) then now else mlB) -> mdF <> 0 -> mlF <= nowF.
Proof.
  intros r hd mdB mlB mdF mlF now nowF -> H -> ->.
  destruct ((r =? 0) && negb (hd =? 0)); intros Hne; [lia | exact (H Hne)].
Qed.

(* C2's fly clause after the run: sent now *)
Lemma tta_fly_lt : forall n nF s c cF : Z, nF = n -> s = n -> cF = c -> 1 <= c -> nF - s < 1000 * cF.
Proof. intros n nF s c cF -> -> -> H. lia. Qed.

(* the frame in flight after the run is tt_fr (DIGINET_CMD_DATA = SPEC_CMD_DATA = 0x00) *)
Lemma tta_frame_abs : forall (d d' : list byte) (c c' r' cmd sm sm' n : Z) (body : list byte),
  d' = d -> c' = c -> r' = 0 -> cmd = SPEC_CMD_DATA -> sm' = sm ->
  lib_frame d HOST c 0 0 DIGINET_CMD_DATA n body sm = lib_frame d' HOST c' 0 r' cmd n body sm'.
Proof. intros d d' c c' r' cmd sm sm' n body -> -> -> -> ->. reflexivity. Qed.

(* ---------------------------------------------------------------- the getters the run does not write *)

(* A: the config, g_raw, g_now *)
Lemma tta_fe_Cfg_max_retries : forall B Bf, wframe R_tt B Bf -> Cfg_max_retries Bf = Cfg_max_retries B.
Proof. intros B Bf H. unfold Cfg_max_retries. tk_get H. Qed.
Lemma tta_fe_Cfg_ack_timeout_ms : forall B Bf, wframe R_tt B Bf -> Cfg_ack_timeout_ms Bf = Cfg_ack_timeout_ms B.
Proof. intros B Bf H. unfold Cfg_ack_timeout_ms. tk_get H. Qed.
Lemma tta_fe_Cfg_keepalive_ms : forall B Bf, wframe R_tt B Bf -> Cfg_keepalive_ms Bf = Cfg_keepalive_ms B.
Proof. intros B Bf H. unfold Cfg_keepalive_ms. tk_get H. Qed.
Lemma tta_fe_Cfg_backoff_ms : forall B Bf, wframe R_tt B Bf -> Cfg_backoff_ms Bf = Cfg_backoff_ms B.
Proof. intros B Bf H. unfold Cfg_backoff_ms. tk_get H. Qed.
Lemma tta_fe_Cfg_offline_ms : forall B Bf, wframe R_tt B Bf -> Cfg_offline_ms Bf = Cfg_offline_ms B.
Proof. intros B Bf H. unfold Cfg_offline_ms. tk_get H. Qed.
Lemma tta_fe_Cfg_wake_timeout_ms : forall B Bf, wframe R_tt B Bf -> Cfg_wake_timeout_ms Bf = Cfg_wake_timeout_ms B.
Proof. intros B Bf H. unfold Cfg_wake_timeout_ms. tk_get H. Qed.
Lemma tta_fe_Cfg_display_gap_us : forall B Bf, wframe R_tt B Bf -> Cfg_display_gap_us Bf = Cfg_display_gap_us B.
Proof. intros B Bf H. unfold Cfg_display_gap_us. tk_get H. Qed.
Lemma tta_fe_Cfg_max_cmds : forall B Bf, wframe R_tt B Bf -> Cfg_max_cmds Bf = Cfg_max_cmds B.
Proof. intros B Bf H. unfold Cfg_max_cmds. tk_get H. Qed.
Lemma tta_fe_Cfg_max_body : forall B Bf, wframe R_tt B Bf -> Cfg_max_body Bf = Cfg_max_body B.
Proof. intros B Bf H. unfold Cfg_max_body. tk_get H. Qed.
Lemma tta_fe_Cfg_host_mac : forall B Bf, wframe R_tt B Bf -> Cfg_host_mac Bf = Cfg_host_mac B.
Proof. intros B Bf H. unfold Cfg_host_mac. tk_get H. Qed.
Lemma tta_fe_Cfg_desk_mac : forall B Bf, wframe R_tt B Bf -> Cfg_desk_mac Bf = Cfg_desk_mac B.
Proof. intros B Bf H. unfold Cfg_desk_mac. tk_get H. Qed.
Lemma tta_fe_Cfg_desk_mac_set : forall B Bf, wframe R_tt B Bf -> Cfg_desk_mac_set Bf = Cfg_desk_mac_set B.
Proof. intros B Bf H. unfold Cfg_desk_mac_set. tk_get H. Qed.
Lemma tta_fe_Cfg_auto_wake : forall B Bf, wframe R_tt B Bf -> Cfg_auto_wake Bf = Cfg_auto_wake B.
Proof. intros B Bf H. unfold Cfg_auto_wake. tk_get H. Qed.
Lemma tta_fe_Cfg_sum_mode : forall B Bf, wframe R_tt B Bf -> Cfg_sum_mode Bf = Cfg_sum_mode B.
Proof. intros B Bf H. unfold Cfg_sum_mode. tk_get H. Qed.
Lemma tta_fe_scfg : forall B Bf, wframe R_tt B Bf -> sub Bf A_S_cfg_host_mac 60 = sub B A_S_cfg_host_mac 60.
Proof. intros B Bf H. tk_get H. Qed.
Lemma tta_fe_gcfg : forall B Bf, wframe R_tt B Bf -> sub Bf OFF_g_cfg 60 = sub B OFF_g_cfg 60.
Proof. intros B Bf H. tk_get H. Qed.
Lemma tta_fe_g_raw : forall B Bf, wframe R_tt B Bf -> g_raw Bf = g_raw B.
Proof. intros B Bf H. unfold g_raw. tk_get H. Qed.
Lemma tta_fe_g_now : forall B Bf, wframe R_tt B Bf -> g_now Bf = g_now B.
Proof. intros B Bf H. unfold g_now. tk_get H. Qed.

(* A3: the io callbacks *)
Lemma tta_fe_S_io_ctx : forall B Bf, wframe R_tt B Bf -> S_io_ctx Bf = S_io_ctx B.
Proof. intros B Bf H. unfold S_io_ctx. tk_get H. Qed.
Lemma tta_fe_S_io_send : forall B Bf, wframe R_tt B Bf -> S_io_send Bf = S_io_send B.
Proof. intros B Bf H. unfold S_io_send. tk_get H. Qed.
Lemma tta_fe_S_io_recv : forall B Bf, wframe R_tt B Bf -> S_io_recv Bf = S_io_recv B.
Proof. intros B Bf H. unfold S_io_recv. tk_get H. Qed.
Lemma tta_fe_S_io_now_us : forall B Bf, wframe R_tt B Bf -> S_io_now_us Bf = S_io_now_us B.
Proof. intros B Bf H. unfold S_io_now_us. tk_get H. Qed.
Lemma tta_fe_S_notify : forall B Bf, wframe R_tt B Bf -> S_notify Bf = S_notify B.
Proof. intros B Bf H. unfold S_notify. tk_get H. Qed.
Lemma tta_fe_S_notify_ctx : forall B Bf, wframe R_tt B Bf -> S_notify_ctx Bf = S_notify_ctx B.
Proof. intros B Bf H. unfold S_notify_ctx. tk_get H. Qed.

(* B1-B4, B5's keepalive, B6; E2 *)
Lemma tta_fe_S_state : forall B Bf, wframe R_tt B Bf -> S_state Bf = S_state B.
Proof. intros B Bf H. unfold S_state. tk_get H. Qed.
Lemma tta_fe_M_state : forall B Bf, wframe R_tt B Bf -> M_state Bf = M_state B.
Proof. intros B Bf H. unfold M_state. tk_get H. Qed.
Lemma tta_fe_S_desk_known : forall B Bf, wframe R_tt B Bf -> S_desk_known Bf = S_desk_known B.
Proof. intros B Bf H. unfold S_desk_known. tk_get H. Qed.
Lemma tta_fe_M_desk_known : forall B Bf, wframe R_tt B Bf -> M_desk_known Bf = M_desk_known B.
Proof. intros B Bf H. unfold M_desk_known. tk_get H. Qed.
Lemma tta_fe_S_desk_mac : forall B Bf, wframe R_tt B Bf -> S_desk_mac Bf = S_desk_mac B.
Proof. intros B Bf H. unfold S_desk_mac. tk_get H. Qed.
Lemma tta_fe_M_desk : forall B Bf, wframe R_tt B Bf -> M_desk Bf = M_desk B.
Proof. intros B Bf H. unfold M_desk. tk_get H. Qed.
Lemma tta_fe_S_foreign : forall B Bf, wframe R_tt B Bf -> S_foreign Bf = S_foreign B.
Proof. intros B Bf H. unfold S_foreign. tk_get H. Qed.
Lemma tta_fe_M_foreign : forall B Bf, wframe R_tt B Bf -> M_foreign Bf = M_foreign B.
Proof. intros B Bf H. unfold M_foreign. tk_get H. Qed.
Lemma tta_fe_S_e1_named_us : forall B Bf, wframe R_tt B Bf -> S_e1_named_us Bf = S_e1_named_us B.
Proof. intros B Bf H. unfold S_e1_named_us. tk_get H. Qed.
Lemma tta_fe_M_e1_us : forall B Bf, wframe R_tt B Bf -> M_e1_us Bf = M_e1_us B.
Proof. intros B Bf H. unfold M_e1_us. tk_get H. Qed.
Lemma tta_fe_S_wake_acked : forall B Bf, wframe R_tt B Bf -> S_wake_acked Bf = S_wake_acked B.
Proof. intros B Bf H. unfold S_wake_acked. tk_get H. Qed.
Lemma tta_fe_M_e2_acked : forall B Bf, wframe R_tt B Bf -> M_e2_acked Bf = M_e2_acked B.
Proof. intros B Bf H. unfold M_e2_acked. tk_get H. Qed.
Lemma tta_fe_S_wake_sent_us : forall B Bf, wframe R_tt B Bf -> S_wake_sent_us Bf = S_wake_sent_us B.
Proof. intros B Bf H. unfold S_wake_sent_us. tk_get H. Qed.
Lemma tta_fe_M_wake_sent : forall B Bf, wframe R_tt B Bf -> M_wake_sent Bf = M_wake_sent B.
Proof. intros B Bf H. unfold M_wake_sent. tk_get H. Qed.
Lemma tta_fe_S_last_rx_us : forall B Bf, wframe R_tt B Bf -> S_last_rx_us Bf = S_last_rx_us B.
Proof. intros B Bf H. unfold S_last_rx_us. tk_get H. Qed.
Lemma tta_fe_M_last_rx : forall B Bf, wframe R_tt B Bf -> M_last_rx Bf = M_last_rx B.
Proof. intros B Bf H. unfold M_last_rx. tk_get H. Qed.
Lemma tta_fe_S_backoff_until_us : forall B Bf, wframe R_tt B Bf -> S_backoff_until_us Bf = S_backoff_until_us B.
Proof. intros B Bf H. unfold S_backoff_until_us. tk_get H. Qed.
Lemma tta_fe_M_backoff_until : forall B Bf, wframe R_tt B Bf -> M_backoff_until Bf = M_backoff_until B.
Proof. intros B Bf H. unfold M_backoff_until. tk_get H. Qed.
Lemma tta_fe_S_next_keepalive_us : forall B Bf, wframe R_tt B Bf -> S_next_keepalive_us Bf = S_next_keepalive_us B.
Proof. intros B Bf H. unfold S_next_keepalive_us. tk_get H. Qed.
Lemma tta_fe_M_next_ka : forall B Bf, wframe R_tt B Bf -> M_next_ka Bf = M_next_ka B.
Proof. intros B Bf H. unfold M_next_ka. tk_get H. Qed.
Lemma tta_fe_S_desk_counter_valid : forall B Bf, wframe R_tt B Bf ->
  S_desk_counter_valid Bf = S_desk_counter_valid B.
Proof. intros B Bf H. unfold S_desk_counter_valid. tk_get H. Qed.
Lemma tta_fe_M_desk_counter_valid : forall B Bf, wframe R_tt B Bf ->
  M_desk_counter_valid Bf = M_desk_counter_valid B.
Proof. intros B Bf H. unfold M_desk_counter_valid. tk_get H. Qed.
Lemma tta_fe_S_desk_counter : forall B Bf, wframe R_tt B Bf -> S_desk_counter Bf = S_desk_counter B.
Proof. intros B Bf H. unfold S_desk_counter. tk_get H. Qed.
Lemma tta_fe_M_desk_counter : forall B Bf, wframe R_tt B Bf -> M_desk_counter Bf = M_desk_counter B.
Proof. intros B Bf H. unfold M_desk_counter. tk_get H. Qed.
Lemma tta_fe_S_personality : forall B Bf, wframe R_tt B Bf -> S_personality Bf = S_personality B.
Proof. intros B Bf H. unfold S_personality. tk_get H. Qed.

(* ---------------------------------------------------------------- the sub-records of agree_core, after the run *)

Lemma tta_cfg : forall B Bf, agree_cfg B -> wframe R_tt B Bf -> agree_cfg Bf.
Proof.
  intros B Bf HC HF. split.
  - (* a1_max_retries *)
    exact (tta_tr1 (fun x => x <= 7) _ _ (tta_fe_Cfg_max_retries B Bf HF) (a1_max_retries _ HC)).
  - (* a1_ack_timeout *)
    exact (tta_tr1 (fun x => 1 <= x <= 256) _ _ (tta_fe_Cfg_ack_timeout_ms B Bf HF) (a1_ack_timeout _ HC)).
  - (* a1_keepalive *)
    exact (tta_tr1 (fun x => 1 <= x <= 65536) _ _ (tta_fe_Cfg_keepalive_ms B Bf HF) (a1_keepalive _ HC)).
  - (* a1_backoff *)
    exact (tta_tr1 (fun x => x <= 255) _ _ (tta_fe_Cfg_backoff_ms B Bf HF) (a1_backoff _ HC)).
  - (* a1_offline *)
    exact (tta_tr1 (fun x => 1 <= x <= 65536) _ _ (tta_fe_Cfg_offline_ms B Bf HF) (a1_offline _ HC)).
  - (* a1_wake_timeout *)
    exact (tta_tr1 (fun x => 1 <= x <= 65536) _ _ (tta_fe_Cfg_wake_timeout_ms B Bf HF) (a1_wake_timeout _ HC)).
  - (* a1_display_gap *)
    exact (tta_tr1 (fun x => x <= 65535) _ _ (tta_fe_Cfg_display_gap_us B Bf HF) (a1_display_gap _ HC)).
  - (* a1_max_cmds *)
    exact (tta_tr1 (fun x => 1 <= x <= 255) _ _ (tta_fe_Cfg_max_cmds B Bf HF) (a1_max_cmds _ HC)).
  - (* a1_max_body *)
    exact (tta_tr1 (fun x => 24 <= x <= 1484) _ _ (tta_fe_Cfg_max_body B Bf HF) (a1_max_body _ HC)).
  - (* a1_host_mac *) exact (eq_trans (tta_fe_Cfg_host_mac B Bf HF) (a1_host_mac _ HC)).
  - (* a1_desk_mac *) exact (eq_trans (tta_fe_Cfg_desk_mac B Bf HF) (a1_desk_mac _ HC)).
  - (* a1_desk_mac_set *) exact (tta_tr1 bit01 _ _ (tta_fe_Cfg_desk_mac_set B Bf HF) (a1_desk_mac_set _ HC)).
  - (* a1_auto_wake *) exact (tta_tr1 bit01 _ _ (tta_fe_Cfg_auto_wake B Bf HF) (a1_auto_wake _ HC)).
  - (* a1_sum_mode *)
    exact (tta_tr1 (fun x => x = DIGINET_SUM_BODY \/ x = DIGINET_SUM_ZERO) _ _ (tta_fe_Cfg_sum_mode B Bf HF)
      (a1_sum_mode _ HC)).
  - (* a2_cfg *) exact (tta_eq2 _ _ _ _ (tta_fe_scfg B Bf HF) (tta_fe_gcfg B Bf HF) (a2_cfg _ HC)).
  - (* a4_raw *) exact (tta_tr1 bit01 _ _ (tta_fe_g_raw B Bf HF) (a4_raw _ HC)).
Qed.

Lemma tta_io : forall I B Bf, agree_io I B -> wframe R_tt B Bf -> agree_io I Bf.
Proof.
  intros I B Bf HI HF. split.
  - exact (eq_trans (tta_fe_S_io_ctx B Bf HF) (a3_io_ctx _ _ HI)).
  - exact (eq_trans (tta_fe_S_io_send B Bf HF) (a3_io_send _ _ HI)).
  - exact (eq_trans (tta_fe_S_io_recv B Bf HF) (a3_io_recv _ _ HI)).
  - exact (eq_trans (tta_fe_S_io_now_us B Bf HF) (a3_io_now _ _ HI)).
  - exact (eq_trans (tta_fe_S_notify B Bf HF) (a3_notify _ _ HI)).
  - exact (eq_trans (tta_fe_S_notify_ctx B Bf HF) (a3_notify_ctx _ _ HI)).
Qed.

Lemma tta_st : forall B Bf m, agree_st B -> S_state B = DIGINET_S_ONLINE -> tt_end B Bf m -> agree_st Bf.
Proof.
  intros B Bf m HS Hon HE. pose proof (te_frame _ _ _ HE) as HF.
  assert (HMf : M_state Bf = DIGINET_S_ONLINE)
    by exact (eq_trans (tta_fe_M_state B Bf HF) (eq_trans (eq_sym (b1_state _ HS)) Hon)).
  split.
  - (* b1_state *)
    exact (tta_eq2 _ _ _ _ (tta_fe_S_state B Bf HF) (tta_fe_M_state B Bf HF) (b1_state _ HS)).
  - (* b1_state_range *)
    exact (tta_tr1 (fun x => 0 <= x <= 3) _ _ (tta_fe_M_state B Bf HF) (b1_state_range _ HS)).
  - (* b2_desk_known *)
    exact (tta_eq2 _ _ _ _ (tta_fe_S_desk_known B Bf HF) (tta_fe_M_desk_known B Bf HF) (b2_desk_known _ HS)).
  - (* b2_desk_known01 *)
    exact (tta_tr1 bit01 _ _ (tta_fe_M_desk_known B Bf HF) (b2_desk_known01 _ HS)).
  - (* b2_desk_mac *) intros Hk.
    exact (tta_eq2 _ _ _ _ (tta_fe_S_desk_mac B Bf HF) (tta_fe_M_desk B Bf HF)
      (b2_desk_mac _ HS (eq_trans (eq_sym (tta_fe_M_desk_known B Bf HF)) Hk))).
  - (* b3_foreign *)
    exact (tta_eq2 _ _ _ _ (tta_fe_S_foreign B Bf HF) (tta_fe_M_foreign B Bf HF) (b3_foreign _ HS)).
  - (* b3_foreign01 *) exact (tta_tr1 bit01 _ _ (tta_fe_M_foreign B Bf HF) (b3_foreign01 _ HS)).
  - (* b3_e1 *)
    exact (tta_eq2 _ _ _ _ (tta_fe_S_e1_named_us B Bf HF) (tta_fe_M_e1_us B Bf HF) (b3_e1 _ HS)).
  - (* b3_e1_01 *) exact (tta_tr1 bit01 _ _ (tta_fe_M_e1_us B Bf HF) (b3_e1_01 _ HS)).
  - (* b3_e2 *)
    exact (tta_eq2 _ _ _ _ (tta_fe_S_wake_acked B Bf HF) (tta_fe_M_e2_acked B Bf HF) (b3_e2 _ HS)).
  - (* b3_e2_01 *) exact (tta_tr1 bit01 _ _ (tta_fe_M_e2_acked B Bf HF) (b3_e2_01 _ HS)).
  - (* b4_wake_sent *)
    exact (tta_eq2 _ _ _ _ (tta_fe_S_wake_sent_us B Bf HF) (tta_fe_M_wake_sent B Bf HF) (b4_wake_sent _ HS)).
  - (* b4_last_rx *)
    exact (tta_eq2 _ _ _ _ (tta_fe_S_last_rx_us B Bf HF) (tta_fe_M_last_rx B Bf HF) (b4_last_rx _ HS)).
  - (* b4_backoff *)
    exact (tta_eq2 _ _ _ _ (tta_fe_S_backoff_until_us B Bf HF) (tta_fe_M_backoff_until B Bf HF)
      (b4_backoff _ HS)).
  - (* b5_next_ka *) intros Hr.
    exact (tta_eq2 _ _ _ _ (tta_fe_S_next_keepalive_us B Bf HF) (tta_fe_M_next_ka B Bf HF)
      (b5_next_ka _ HS (eq_trans (eq_sym (tta_fe_g_raw B Bf HF)) Hr))).
  - (* b5_display_sent *) intros Hr. pose proof (eq_trans (eq_sym (tta_fe_g_raw B Bf HF)) Hr) as Hr'.
    exact (tta_disp_eq _ _ _ _ _ _ Hr' (b5_display_sent _ HS Hr') (te_ds _ _ _ HE) (te_ms _ _ _ HE)).
  - (* b5_display_sent01 *) intros Hr. pose proof (eq_trans (eq_sym (tta_fe_g_raw B Bf HF)) Hr) as Hr'.
    exact (tta_disp01 _ _ _ _ Hr' (b5_display_sent01 _ HS Hr') (te_ms _ _ _ HE)).
  - (* b5_last_display *) intros Hr. pose proof (eq_trans (eq_sym (tta_fe_g_raw B Bf HF)) Hr) as Hr'.
    exact (tta_ld_eq _ _ _ _ _ _ _ Hr' (b5_last_display _ HS Hr') (te_dl _ _ _ HE) (te_ml _ _ _ HE)).
  - (* b6_valid *)
    exact (tta_eq2 _ _ _ _ (tta_fe_S_desk_counter_valid B Bf HF) (tta_fe_M_desk_counter_valid B Bf HF)
      (b6_valid _ HS)).
  - (* b6_valid01 *) exact (tta_tr1 bit01 _ _ (tta_fe_M_desk_counter_valid B Bf HF) (b6_valid01 _ HS)).
  - (* b6_counter *) intros Hv.
    exact (tta_eq2 _ _ _ _ (tta_fe_S_desk_counter B Bf HF) (tta_fe_M_desk_counter B Bf HF)
      (b6_counter _ HS (eq_trans (eq_sym (tta_fe_M_desk_counter_valid B Bf HF)) Hv))).
  - (* b7_host_counter *) exact (eq_trans (te_hc _ _ _ HE) (eq_sym (te_mhc _ _ _ HE))).
  - (* b9_idle: ONLINE *)
    intros [Hs|Hs]; exfalso; pose proof (eq_trans (eq_sym HMf) Hs) as X;
      unfold DIGINET_S_ONLINE, S_IDLE, S_CLOSED in X; discriminate X.
  - (* b9_known *) intros _.
    exact (eq_trans (tta_fe_M_desk_known B Bf HF)
      (b9_known _ HS (or_intror (eq_trans (eq_sym (b1_state _ HS)) Hon)))).
Qed.

Lemma tta_fly : forall B Bf m, agree_st B -> S_state B = DIGINET_S_ONLINE ->
  (length (tt_body B m) <= 1484)%nat -> body_check (tt_body B m) = DIGINET_OK ->
  tt_end B Bf m -> agree_fly Bf.
Proof.
  intros B Bf m HS Hon Hlen Hbc HE. pose proof (te_frame _ _ _ HE) as HF.
  assert (HMf : M_state Bf = DIGINET_S_ONLINE)
    by exact (eq_trans (tta_fe_M_state B Bf HF) (eq_trans (eq_sym (b1_state _ HS)) Hon)).
  split.
  - (* b8_on *) exact (eq_trans (te_on _ _ _ HE) (eq_sym (te_mon _ _ _ HE))).
  - (* b8_on01 *) unfold bit01. right. exact (te_mon _ _ _ HE).
  - (* b8_state *) intros _. right. exact HMf.
  - (* b8_counter *) intros _. exact (eq_trans (te_ctr _ _ _ HE) (eq_sym (te_mctr _ _ _ HE))).
  - (* b8_counter_host *) intros _. exact (eq_trans (te_ctr _ _ _ HE) (eq_sym (te_hc _ _ _ HE))).
  - (* b8_retries *) intros _. exact (eq_trans (te_ret _ _ _ HE) (eq_sym (te_mret _ _ _ HE))).
  - (* b8_retries_le *) intros _.
    exact (tta_tr1 (fun x => x <= Cfg_max_retries Bf) _ _ (te_mret _ _ _ HE)
      (u_at_nonneg Bf A_Cfg_max_retries 4%nat)).
  - (* b8_sent *) intros _. exact (eq_trans (te_sent _ _ _ HE) (eq_sym (te_msent _ _ _ HE))).
  - (* b8_len *) intros _. exact (eq_trans (te_flen _ _ _ HE) (eq_sym (te_mflen _ _ _ HE))).
  - (* b8_cmd *) intros _. right. exact (te_mcmd _ _ _ HE).
  - (* b8_frames: the body taken, its count *) intros _. exists (tt_body B m), (u8 (tt_n B m)).
    split; [exact Hlen|]. split; [exact Hbc|].
    split; [pose proof (Z.mod_pos_bound (tt_n B m) 256 ltac:(lia)) as Hb; exact Hb|].
    split; [exact (te_mflen _ _ _ HE)|]. split.
    + assert (E1 : sub Bf A_M_fly_frame (Z.to_nat (M_fly_len Bf)) = tt_fr B m)
        by exact (tta_tr1 (fun L => sub Bf A_M_fly_frame (Z.to_nat L) = tt_fr B m) _ _
                    (te_mflen _ _ _ HE) (te_mfr _ _ _ HE)).
      assert (E2 : tt_fr B m = lib_frame (M_desk Bf) HOST (M_fly_counter Bf) 0 0 (M_fly_cmd Bf) (u8 (tt_n B m))
                                 (tt_body B m) (Cfg_sum_mode Bf))
        by exact (tta_frame_abs (M_desk B) (M_desk Bf) (tt_send B m) (M_fly_counter Bf) 0 (M_fly_cmd Bf)
                    (Cfg_sum_mode B) (Cfg_sum_mode Bf) (u8 (tt_n B m)) (tt_body B m)
                    (tta_fe_M_desk B Bf HF) (te_mctr _ _ _ HE) eq_refl (te_mcmd _ _ _ HE)
                    (tta_fe_Cfg_sum_mode B Bf HF)).
      exact (eq_trans E1 E2).
    + assert (E1 : sub Bf A_S_inflight_frame (Z.to_nat (M_fly_len Bf)) = tt_fr B m)
        by exact (tta_tr1 (fun L => sub Bf A_S_inflight_frame (Z.to_nat L) = tt_fr B m) _ _
                    (te_mflen _ _ _ HE) (te_fr _ _ _ HE)).
      assert (E2 : tt_fr B m = lib_frame (M_desk Bf) HOST (M_fly_counter Bf) 0 (M_fly_retries Bf) (M_fly_cmd Bf)
                                 (u8 (tt_n B m)) (tt_body B m) (Cfg_sum_mode Bf))
        by exact (tta_frame_abs (M_desk B) (M_desk Bf) (tt_send B m) (M_fly_counter Bf) (M_fly_retries Bf)
                    (M_fly_cmd Bf) (Cfg_sum_mode B) (Cfg_sum_mode Bf) (u8 (tt_n B m)) (tt_body B m)
                    (tta_fe_M_desk B Bf HF) (te_mctr _ _ _ HE) (te_mret _ _ _ HE) (te_mcmd _ _ _ HE)
                    (tta_fe_Cfg_sum_mode B Bf HF)).
      exact (eq_trans E1 E2).
Qed.

Lemma tta_time : forall ops B Bf m, agree_cfg B -> agree_time ops B -> tt_end B Bf m -> agree_time ops Bf.
Proof.
  intros ops B Bf m HC HT HE. pose proof (te_frame _ _ _ HE) as HF.
  pose proof (tta_fe_g_now B Bf HF) as En.
  split.
  - (* c_now *) exact (tta_tr1 (fun x => x <= 1000000 + ops * 65535000000) _ _ En (c_now _ _ HT)).
  - (* c1_last_rx *)
    exact (tta_tr2 (fun x y => x <= y) _ _ _ _ (tta_fe_M_last_rx B Bf HF) En (c1_last_rx _ _ HT)).
  - (* c1_wake_sent *)
    exact (tta_tr2 (fun x y => x <= y) _ _ _ _ (tta_fe_M_wake_sent B Bf HF) En (c1_wake_sent _ _ HT)).
  - (* c1_fly_sent: sent now *) intros _.
    exact (tta_tr2 (fun x y => x <= y) _ _ _ _ (te_msent _ _ _ HE) En (Z.le_refl (g_now B))).
  - (* c1_last_display *)
    exact (tta_ld_le _ _ _ _ _ _ _ _ En (c1_last_display _ _ HT) (te_ms _ _ _ HE) (te_ml _ _ _ HE)).
  - (* c1_backoff *)
    exact (tta_tr2 (fun x y => x <= y + 255000) _ _ _ _ (tta_fe_M_backoff_until B Bf HF) En (c1_backoff _ _ HT)).
  - (* c1_next_ka *) intros Hr.
    exact (tta_tr2 (fun x y => x <= y + 65536000) _ _ _ _ (tta_fe_M_next_ka B Bf HF) En
      (c1_next_ka _ _ HT (eq_trans (eq_sym (tta_fe_g_raw B Bf HF)) Hr))).
  - (* c2_wake *) intros Hs.
    exact (tta_tr3 (fun x y z => x - y < 1000 * z) _ _ _ _ _ _ En (tta_fe_M_wake_sent B Bf HF)
      (tta_fe_Cfg_wake_timeout_ms B Bf HF) (c2_wake _ _ HT (eq_trans (eq_sym (tta_fe_M_state B Bf HF)) Hs))).
  - (* c2_online *) intros Hs.
    exact (tta_tr3 (fun x y z => x - y < 1000 * z) _ _ _ _ _ _ En (tta_fe_M_last_rx B Bf HF)
      (tta_fe_Cfg_offline_ms B Bf HF) (c2_online _ _ HT (eq_trans (eq_sym (tta_fe_M_state B Bf HF)) Hs))).
  - (* c2_fly: sent now, 1 <= ack_timeout *) intros _.
    exact (tta_fly_lt _ _ _ _ _ En (te_msent _ _ _ HE) (tta_fe_Cfg_ack_timeout_ms B Bf HF)
      (proj1 (a1_ack_timeout _ HC))).
Qed.

Lemma tta_misc : forall I B Bf m, agree_misc I B -> tt_end B Bf m -> agree_misc I Bf.
Proof.
  intros I B Bf m HM HE. split.
  - (* e1_fail_next *) unfold bit01. left. exact (te_fail _ _ _ HE).
  - (* e2_personality *)
    exact (tta_tr1 (fun x => x = 0 \/ x = ti_personalities I \/ x = ti_personalities I + 24) _ _
      (tta_fe_S_personality B Bf (te_frame _ _ _ HE)) (e2_personality _ _ HM)).
Qed.

(* ---------------------------------------------------------------- the segment lemma *)

Lemma tt_post_ok : forall I ops B Bf m,
  agree_core I ops B -> S_state B = DIGINET_S_ONLINE -> S_inflight B = 0 ->
  (length (tt_body B m) <= 1484)%nat -> body_check (tt_body B m) = DIGINET_OK ->
  tt_end B Bf m -> agree_q ops Bf -> tick_post I ops B Bf.
Proof.
  intros I ops B Bf m HC Hon _ Hlen Hbc HE HQ. pose proof (te_frame _ _ _ HE) as HF.
  split.
  - (* tp_core *) split.
    + (* ac_img *) exact (ac_img _ _ _ HC).
    + (* ac_len *) pose proof (te_len _ _ _ HE) as L. unfold WN in L. exact L.
    + (* ac_cfg *) exact (tta_cfg B Bf (ac_cfg _ _ _ HC) HF).
    + (* ac_io *) exact (tta_io I B Bf (ac_io _ _ _ HC) HF).
    + (* ac_st *) exact (tta_st B Bf m (ac_st _ _ _ HC) Hon HE).
    + (* ac_fly *) exact (tta_fly B Bf m (ac_st _ _ _ HC) Hon Hlen Hbc HE).
    + (* ac_time *) exact (tta_time ops B Bf m (ac_cfg _ _ _ HC) (ac_time _ _ _ HC) HE).
    + (* ac_q *) exact HQ.
    + (* ac_misc *) exact (tta_misc I B Bf m (ac_misc _ _ _ HC) HE).
  - (* tp_keepalive: a frame is in flight *) unfold c2_keepalive. intros _ _ H0 _. exfalso.
    pose proof (eq_trans (eq_sym H0) (te_mon _ _ _ HE)) as X. discriminate X.
  - (* tp_drain: a frame is in flight *) unfold drain_fact. intros _ _ H0 _. exfalso.
    pose proof (eq_trans (eq_sym H0) (te_mon _ _ _ HE)) as X. discriminate X.
  - (* tp_frame *) exact (wframe_weaken R_tt R_tick B Bf R_tt_tick HF).
  - (* tp_fail *) right. exact (te_fail _ _ _ HE).
Qed.

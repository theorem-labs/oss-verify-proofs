(* The switch of a reception, model and library together (FT:301-372, DS:298-316, with the notices and sends
   they make), writes only R_rx: M, g_s from `state` up to the queue (state, desk, personality, flags, times,
   counters, the frame in flight), g_s's stats, OW, GOT, and the scalars g_fail_next, g_last_counter, g_rx_send,
   g_rx_fail, g_rx_times, g_rx, g_rx_len (FT:829, :850, :868, :1002, :1012-1018). Outside it lie everything
   agree_cfg, agree_io and agree_q read (g_cfg, s->cfg, s->io, s->notify, s->queue, s->queued, g_cmd, g_q, g_nq,
   g_ncmd, g_raw) and g_now. agree_core_rx: those three parts and the image facts carry over a wframe R_rx;
   the parts the switch moves (agree_st, agree_fly, agree_time, agree_misc) are the branch's to show. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree SimLib QueueFacts RxBase RxW.
Import ListNotations.
Open Scope Z_scope.

(* the world functions stay folded for the unifier (RxW.v header); the getters unfold to them *)
Local Opaque sub upd u_at s32_at put.

Definition R_rx (a : Z) : Prop :=
  (OFF_M <= a < OFF_M + SZ_M) \/
  (A_S_state <= a < A_S_queue_bytes 0) \/
  (A_S_stats_rx_frames <= a < A_S_stats_rx_frames + 112) \/
  (OFF_g_fail_next <= a < OFF_g_fail_next + 4) \/
  (OFF_g_last_counter <= a < OFF_g_last_counter + 4) \/
  (OFF_g_rx_send <= a < OFF_g_now) \/
  (OFF_g_rx <= a < OFF_g_cfg) \/
  (OFF_GOT <= a < OFF_OW + SZ_OW).

(* a read whose range misses R_rx, through a wframe R_rx *)
Ltac rx_side := solve [ wnum | unfold R_rx; wunf_off; cbv beta; wclear; intros; lia ].
Ltac rx_tr H := wunf_get;
  lazymatch goal with
  | |- s32_at _ _ = s32_at _ _ => apply (wframe_s32_at R_rx _ _ _ H)
  | |- u_at _ _ _ = u_at _ _ _ => apply (wframe_u_at R_rx _ _ _ _ H)
  | |- sub _ _ _ = sub _ _ _ => apply (wframe_sub R_rx _ _ _ _ H)
  end;
  rx_side.

Section Frame.
Variables (B W : list byte).
Hypothesis HF : wframe R_rx B W.

Lemma rx_cfg_frame : agree_cfg B -> agree_cfg W.
Proof.
  intros [? ? ? ? ? ? ? ? ? H1 H2 ? ? ? H3 ?].
  assert (E1 : Cfg_max_retries W = Cfg_max_retries B) by rx_tr HF.
  assert (E2 : Cfg_ack_timeout_ms W = Cfg_ack_timeout_ms B) by rx_tr HF.
  assert (E3 : Cfg_keepalive_ms W = Cfg_keepalive_ms B) by rx_tr HF.
  assert (E4 : Cfg_backoff_ms W = Cfg_backoff_ms B) by rx_tr HF.
  assert (E5 : Cfg_offline_ms W = Cfg_offline_ms B) by rx_tr HF.
  assert (E6 : Cfg_wake_timeout_ms W = Cfg_wake_timeout_ms B) by rx_tr HF.
  assert (E7 : Cfg_display_gap_us W = Cfg_display_gap_us B) by rx_tr HF.
  assert (E8 : Cfg_max_cmds W = Cfg_max_cmds B) by rx_tr HF.
  assert (E9 : Cfg_max_body W = Cfg_max_body B) by rx_tr HF.
  assert (E10 : Cfg_host_mac W = Cfg_host_mac B) by rx_tr HF.
  assert (E11 : Cfg_desk_mac W = Cfg_desk_mac B) by rx_tr HF.
  assert (E12 : Cfg_desk_mac_set W = Cfg_desk_mac_set B) by rx_tr HF.
  assert (E13 : Cfg_auto_wake W = Cfg_auto_wake B) by rx_tr HF.
  assert (E14 : Cfg_sum_mode W = Cfg_sum_mode B) by rx_tr HF.
  assert (E15 : g_raw W = g_raw B) by rx_tr HF.
  assert (E16 : sub W A_S_cfg_host_mac 60 = sub B A_S_cfg_host_mac 60).
  { apply (wframe_sub R_rx B W _ _ HF); rx_side. }
  assert (E17 : sub W OFF_g_cfg 60 = sub B OFF_g_cfg 60).
  { apply (wframe_sub R_rx B W _ _ HF); rx_side. }
  constructor;
    [rewrite E1 | rewrite E2 | rewrite E3 | rewrite E4 | rewrite E5 | rewrite E6 | rewrite E7 | rewrite E8
    | rewrite E9 | rewrite E10 | rewrite E11 | rewrite E12 | rewrite E13 | rewrite E14 | rewrite E16, E17
    | rewrite E15]; assumption.
Qed.

Lemma rx_io_frame : forall I, agree_io I B -> agree_io I W.
Proof.
  intros I [H1 H2 H3 H4 H5 H6].
  assert (E1 : S_io_ctx W = S_io_ctx B) by rx_tr HF.
  assert (E2 : S_io_send W = S_io_send B) by rx_tr HF.
  assert (E3 : S_io_recv W = S_io_recv B) by rx_tr HF.
  assert (E4 : S_io_now_us W = S_io_now_us B) by rx_tr HF.
  assert (E5 : S_notify W = S_notify B) by rx_tr HF.
  assert (E6 : S_notify_ctx W = S_notify_ctx B) by rx_tr HF.
  constructor; congruence.
Qed.

Lemma rx_q_frame : forall ops, agree_q ops B -> agree_q ops W.
Proof.
  intros ops [D1q D1n D1e D1u D1p D2 D3n D3o D4q D4e].
  assert (Eraw : g_raw W = g_raw B) by rx_tr HF.
  assert (Esq : S_queued W = S_queued B) by rx_tr HF.
  assert (Enq : g_nq W = g_nq B) by rx_tr HF.
  assert (Enc : g_ncmd W = g_ncmd B) by rx_tr HF.
  assert (EQ : forall i, 0 <= i < 1024 -> Q_at W i = Q_at B i) by (intros i Hi; rx_tr HF).
  assert (Est : forall k, 0 <= k < 1024 -> Cmd_st W k = Cmd_st B k) by (intros k Hk; rx_tr HF).
  assert (Eky : forall k, 0 <= k < 1024 -> Cmd_key W k = Cmd_key B k) by (intros k Hk; rx_tr HF).
  assert (Edp : forall k, 0 <= k < 1024 -> Cmd_display W k = Cmd_display B k) by (intros k Hk; rx_tr HF).
  assert (Eby : forall k, 0 <= k < 1024 -> Cmd_bytes W k = Cmd_bytes B k) by (intros k Hk; rx_tr HF).
  assert (Eln : forall k, 0 <= k < 1024 -> Cmd_len W k = Cmd_len B k) by (intros k Hk; rx_tr HF).
  assert (Sby : forall i, 0 <= i < 512 -> S_queue_bytes W i = S_queue_bytes B i) by (intros i Hi; rx_tr HF).
  assert (Sln : forall i, 0 <= i < 512 -> S_queue_len W i = S_queue_len B i) by (intros i Hi; rx_tr HF).
  assert (Sky : forall i, 0 <= i < 512 -> S_queue_key W i = S_queue_key B i) by (intros i Hi; rx_tr HF).
  assert (Sdp : forall i, 0 <= i < 512 -> S_queue_display W i = S_queue_display B i) by (intros i Hi; rx_tr HF).
  unfold OPS_MAX, QUEUE_MAX in *.
  constructor; rewrite ?Eraw, ?Esq, ?Enq, ?Enc.
  - exact D1q.
  - exact D1n.
  - intros Hr i Hi. specialize (D1n Hr). specialize (D1e Hr i Hi). rewrite (EQ i) by lia.
    destruct D1e as (Hq & Hs & Hb & Hl & Hk & Hd).
    rewrite (Est _), (Eby _), (Eln _), (Eky _), (Edp _), (Sby i), (Sln i), (Sky i), (Sdp i) by lia.
    tauto.
  - intros Hr i j Hi Hj Hij. specialize (D1n Hr). rewrite (EQ i), (EQ j) in Hij by lia. exact (D1u Hr i j Hi Hj Hij).
  - intros Hr k Hk. specialize (D1n Hr). rewrite (Est k) by lia. rewrite (D1p Hr k Hk).
    split; intros [i [Hi Hq]]; exists i; split; try exact Hi.
    + rewrite (EQ i) by lia. exact Hq.
    + rewrite (EQ i) in Hq by lia. exact Hq.
  - intros k Hk Hs. rewrite (Est k) in Hs by lia. rewrite (Eby k), (Eln k), (Edp k) by lia. exact (D2 k Hk Hs).
  - exact D3n.
  - exact D3o.
  - exact D4q.
  - intros Hr i Hi. specialize (D4q Hr). rewrite (Sln i), (Sby i) by lia. exact (D4e Hr i Hi).
Qed.

End Frame.

(* agree_core after the switch: the parts R_rx misses carry over, the rest is the branch's *)
Lemma agree_core_rx : forall I ops B W, agree_core I ops B -> wframe R_rx B W ->
  agree_st W -> agree_fly W -> agree_time ops W -> agree_misc I W -> agree_core I ops W.
Proof.
  intros I ops B W HC HF Hst Hfl Hti Hmi. destruct HC as [Himg Hlen Hcfg Hio _ _ _ Hq _].
  constructor; try assumption.
  - destruct HF as [HL _]. rewrite HL. exact Hlen.
  - exact (rx_cfg_frame B W HF Hcfg).
  - exact (rx_io_frame B W HF I Hio).
  - exact (rx_q_frame B W HF ops Hq).
Qed.

(* ---- a frame over a range list inside R_rx ---- *)

Definition rs_in_rx (rs : list (Z * Z)) : bool :=
  forallb (fun '(k, m) =>
    ((OFF_M <=? k) && (k + m <=? OFF_M + SZ_M)) ||
    ((A_S_state <=? k) && (k + m <=? A_S_queue_bytes 0)) ||
    ((A_S_stats_rx_frames <=? k) && (k + m <=? A_S_stats_rx_frames + 112)) ||
    ((OFF_g_fail_next <=? k) && (k + m <=? OFF_g_fail_next + 4)) ||
    ((OFF_g_last_counter <=? k) && (k + m <=? OFF_g_last_counter + 4)) ||
    ((OFF_g_rx_send <=? k) && (k + m <=? OFF_g_now)) ||
    ((OFF_g_rx <=? k) && (k + m <=? OFF_g_cfg)) ||
    ((OFF_GOT <=? k) && (k + m <=? OFF_OW + SZ_OW))) rs.

Lemma rs_in_rx_ok : forall rs, rs_in_rx rs = true -> forall a, in_rs rs a -> R_rx a.
Proof.
  intros rs H a Ha. unfold in_rs in Ha. induction Ha as [[k m] rs' Hx | x rs' Hx IH].
  - cbn in H. apply andb_prop in H as [H _]. cbn in Hx. unfold R_rx.
    repeat (apply orb_prop in H as [H|H]); apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1, H2; lia.
  - cbn in H. destruct x as [k m]. apply andb_prop in H as [_ H]. exact (IH H).
Qed.

Lemma wframe_rx : forall rs X Y, rs_in_rx rs = true -> wframe (in_rs rs) X Y -> wframe R_rx X Y.
Proof. intros rs X Y H HF. eapply wframe_weaken; [|exact HF]. exact (rs_in_rx_ok rs H). Qed.

(* m_tick (FT:246-252) does nothing when nothing is overdue *)
Lemma m_tick_quiet : forall X,
  (M_state X = S_WAKING -> M_wake_sent X <= g_now X /\ g_now X - M_wake_sent X < 1000 * Cfg_wake_timeout_ms X) ->
  (M_state X = S_ONLINE -> M_last_rx X <= g_now X /\ g_now X - M_last_rx X < 1000 * Cfg_offline_ms X) ->
  Cfg_wake_timeout_ms X <= 65536 -> Cfg_offline_ms X <= 65536 ->
  m_tick_m X = Some (X, tt).
Proof.
  intros X Hw Ho Cw Co. unfold m_tick_m, h_ms_m, u64.
  assert (P1 : 0 <= Cfg_wake_timeout_ms X) by (unfold Cfg_wake_timeout_ms; apply u_at_nonneg).
  assert (P2 : 0 <= Cfg_offline_ms X) by (unfold Cfg_offline_ms; apply u_at_nonneg).
  assert (P3 : g_now X < 2 ^ 64) by (unfold g_now; apply (u_at_bound X OFF_g_now 8)).
  assert (P4 : 0 <= M_wake_sent X) by (unfold M_wake_sent; apply u_at_nonneg).
  assert (P5 : 0 <= M_last_rx X) by (unfold M_last_rx; apply u_at_nonneg).
  destruct (Z.eqb_spec (M_state X) S_WAKING) as [E|E]; cbn [andb].
  - destruct (Hw E) as [H1 H2].
    rewrite (Z.mod_small (Cfg_wake_timeout_ms X * 1000) (2 ^ 64)) by lia.
    rewrite (Z.mod_small (g_now X - M_wake_sent X) (2 ^ 64)) by lia.
    destruct (Z.leb_spec (Cfg_wake_timeout_ms X * 1000) (g_now X - M_wake_sent X)); [lia|].
    rewrite E. reflexivity.
  - destruct (Z.eqb_spec (M_state X) S_ONLINE) as [E2|E2]; cbn [andb]; [|reflexivity].
    destruct (Ho E2) as [H1 H2].
    rewrite (Z.mod_small (Cfg_offline_ms X * 1000) (2 ^ 64)) by lia.
    rewrite (Z.mod_small (g_now X - M_last_rx X) (2 ^ 64)) by lia.
    destruct (Z.leb_spec (Cfg_offline_ms X * 1000) (g_now X - M_last_rx X)); [lia|]. reflexivity.
Qed.

(* rewrite with every equation `G W = _` (or `G W i = _`) of the context whose left side is in the goal; the
   presence test is syntactic (a closed pattern), and each equation is cleared once used or found absent *)
Ltac rw_eqs W := repeat match goal with
  | E : ?L = _ |- _ =>
      match L with
      | ?G ?X => wis W X
      | ?G ?X ?i => wis W X
      end;
      lazymatch goal with
      | |- context [L] => rewrite E; clear E
      | _ => clear E
      end
  end.

(* lia in a big context: drop the disjunctions, implications and foralls first (they make lia split) *)
Ltac slia := wclear; lia.

(* ---- frames whose ranges miss a region ---- *)

Lemma disj_rs_sub : forall j n j' n' rs, disj_rs j n rs = true -> j <= j' -> j' + n' <= j + n ->
  disj_rs j' n' rs = true.
Proof.
  intros j n j' n' rs H H1 H2. unfold disj_rs in *. rewrite forallb_forall in *. intros [k m] Hin.
  specialize (H _ Hin). cbn in H. apply orb_prop in H as [H|H]; apply Z.leb_le in H; apply orb_true_intro;
    [left | right]; apply Z.leb_le; lia.
Qed.

(* `G Y = G X` given H : wframe (in_rs rs) X Y and Hd : disj_rs J N rs = true with G's range inside [J, J + N) *)
Ltac fget_in H Hd := wunf_get;
  lazymatch goal with
  | |- s32_at _ _ = s32_at _ _ => apply (fr_s _ _ _ _ H)
  | |- u_at _ _ _ = u_at _ _ _ => apply (fr_u _ _ _ _ _ H)
  | |- sub _ _ _ = sub _ _ _ => apply (fr_sub _ _ _ _ _ H)
  end;
  [ wnum | apply (disj_rs_sub _ _ _ _ _ Hd); wunf_off; first [wcl | lia] ].

(* OW and GOT untouched *)
Lemma ow_zero_fr : forall rs X Y, wframe (in_rs rs) X Y -> disj_rs OFF_GOT (OFF_OW + SZ_OW - OFF_GOT) rs = true ->
  ow_zero X -> ow_zero Y.
Proof.
  intros rs X Y H Hd [Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16].
  constructor;
    [ rewrite <- Z1; fget_in H Hd | rewrite <- Z2; fget_in H Hd | rewrite <- Z3; fget_in H Hd
    | rewrite <- Z4; fget_in H Hd | rewrite <- Z5; fget_in H Hd | rewrite <- Z6; fget_in H Hd
    | rewrite <- Z7; fget_in H Hd | rewrite <- Z8; fget_in H Hd | rewrite <- Z9; fget_in H Hd
    | rewrite <- Z10; fget_in H Hd | rewrite <- Z11; fget_in H Hd | rewrite <- Z12; fget_in H Hd
    | rewrite <- Z13; fget_in H Hd | rewrite <- Z14; fget_in H Hd | rewrite <- Z15; fget_in H Hd
    | rewrite <- Z16; fget_in H Hd ].
Qed.

Lemma ow_got_eq_zero : forall B, ow_zero B -> ow_got_eq B.
Proof.
  intros B [Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16].
  constructor; rewrite ?Z1, ?Z2, ?Z3, ?Z4, ?Z5, ?Z6, ?Z7, ?Z8, ?Z9, ?Z10, ?Z11, ?Z12, ?Z13, ?Z14, ?Z15, ?Z16;
    first [reflexivity | lia | (intros; exfalso; lia)].
Qed.

(* the frame in flight untouched (B8), the few other fields agree_fly reads given *)
Lemma agree_fly_fr : forall rs X Y, wframe (in_rs rs) X Y ->
  disj_rs A_M_fly_on (OFF_M + SZ_M - A_M_fly_on) rs = true ->
  disj_rs A_S_inflight (A_S_queue_bytes 0 - A_S_inflight) rs = true ->
  S_host_counter Y = S_host_counter X -> Cfg_max_retries Y = Cfg_max_retries X -> Cfg_sum_mode Y = Cfg_sum_mode X ->
  (M_fly_on X = 1 -> M_desk Y = M_desk X /\ (M_state Y = S_WAKING \/ M_state Y = S_ONLINE)) ->
  agree_fly X -> agree_fly Y.
Proof.
  intros rs X Y H Hm Hs Ehc Emr Esm Hon [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11].
  assert (E1 : M_fly_on Y = M_fly_on X) by (fget_in H Hm).
  assert (E2 : M_fly_cmd Y = M_fly_cmd X) by (fget_in H Hm).
  assert (E3 : M_fly_counter Y = M_fly_counter X) by (fget_in H Hm).
  assert (E4 : M_fly_retries Y = M_fly_retries X) by (fget_in H Hm).
  assert (E5 : M_fly_sent Y = M_fly_sent X) by (fget_in H Hm).
  assert (E6 : M_fly_len Y = M_fly_len X) by (fget_in H Hm).
  assert (E7 : sub Y A_M_fly_frame 1514 = sub X A_M_fly_frame 1514).
  { apply (fr_sub _ _ _ _ _ H); [wnum | apply (disj_rs_sub _ _ _ _ _ Hm); wunf_off; first [wcl | lia]]. }
  assert (E8 : S_inflight Y = S_inflight X) by (fget_in H Hs).
  assert (E9 : S_inflight_len Y = S_inflight_len X) by (fget_in H Hs).
  assert (E10 : S_inflight_counter Y = S_inflight_counter X) by (fget_in H Hs).
  assert (E11 : S_inflight_retries Y = S_inflight_retries X) by (fget_in H Hs).
  assert (E12 : S_inflight_sent_us Y = S_inflight_sent_us X) by (fget_in H Hs).
  assert (E13 : sub Y A_S_inflight_frame 1514 = sub X A_S_inflight_frame 1514).
  { apply (fr_sub _ _ _ _ _ H); [wnum | apply (disj_rs_sub _ _ _ _ _ Hs); wunf_off; first [wcl | lia]]. }
  constructor; rw_eqs Y.
  - exact F1.
  - exact F2.
  - intros Ho. exact (proj2 (Hon Ho)).
  - exact F4.
  - exact F5.
  - exact F6.
  - exact F7.
  - exact F8.
  - exact F9.
  - exact F10.
  - intros Ho. destruct (F11 Ho) as (body & nc & G1 & G2 & G3 & G4 & G5 & G6).
    destruct (Hon Ho) as [Ed _]. rewrite Ed. exists body, nc.
    assert (Hl : (Z.to_nat (M_fly_len X) <= 1514)%nat) by (rewrite G4; unfold frame_len; lia).
    rewrite (sub_le_eq Y X _ _ _ E7 Hl), (sub_le_eq Y X _ _ _ E13 Hl).
    exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 G6))))).
Qed.

(* ---- the generalised reception (RxBase.v rx_pre_g): OW / GOT across a frame that misses them ---- *)

(* a read across H : wframe R X Y whose range HR keeps out of R *)
Ltac rgr H HR := wunf_get;
  lazymatch goal with
  | |- s32_at _ _ = s32_at _ _ => apply (wframe_s32_at _ _ _ _ H)
  | |- u_at _ _ _ = u_at _ _ _ => apply (wframe_u_at _ _ _ _ _ H)
  | |- sub _ _ _ = sub _ _ _ => apply (wframe_sub _ _ _ _ _ H)
  end;
  [ wnum
  | let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; apply HR; revert Ha; wunf_off; unfold TRANS_MAX; intros; lia ].

Section OwFrame.
Variables (R : Z -> Prop) (X Y : list byte).
Hypothesis H : wframe R X Y.
Hypothesis HR : forall a, OFF_GOT <= a < OFF_OW + SZ_OW -> ~ R a.

Lemma ow_counts_frR :
  GOT_n Y = GOT_n X /\ OW_n Y = OW_n X /\ GOT_e2 Y = GOT_e2 X /\ OW_e2 Y = OW_e2 X /\
  GOT_e3 Y = GOT_e3 X /\ OW_e3 Y = OW_e3 X /\ GOT_acks Y = GOT_acks X /\ OW_acks Y = OW_acks X /\
  GOT_desk Y = GOT_desk X /\ OW_desk Y = OW_desk X /\ GOT_foreign Y = GOT_foreign X /\
  OW_foreign Y = OW_foreign X /\ GOT_acked Y = GOT_acked X /\ OW_acked Y = OW_acked X /\
  GOT_ndata Y = GOT_ndata X /\ OW_ndata Y = OW_ndata X.
Proof.
  split; [rgr H HR|]. split; [rgr H HR|]. split; [rgr H HR|]. split; [rgr H HR|].
  split; [rgr H HR|]. split; [rgr H HR|]. split; [rgr H HR|]. split; [rgr H HR|].
  split; [rgr H HR|]. split; [rgr H HR|]. split; [rgr H HR|]. split; [rgr H HR|].
  split; [rgr H HR|]. split; [rgr H HR|]. split; [rgr H HR | rgr H HR].
Qed.

Lemma ow_got_eq_frR : ow_got_eq X -> ow_got_eq Y.
Proof.
  intros [O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 O12 O13 O14 O15 O16 O17].
  destruct ow_counts_frR as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16).
  assert (ET : forall i, 0 <= i < TRANS_MAX ->
    GOT_t_state Y i = GOT_t_state X i /\ GOT_t_old Y i = GOT_t_old X i /\ GOT_t_reason Y i = GOT_t_reason X i /\
    OW_t_state Y i = OW_t_state X i /\ OW_t_old Y i = OW_t_old X i /\ OW_t_reason Y i = OW_t_reason X i).
  { intros i Hi. unfold TRANS_MAX in Hi.
    split; [rgr H HR|]. split; [rgr H HR|]. split; [rgr H HR|]. split; [rgr H HR|].
    split; [rgr H HR | rgr H HR]. }
  constructor; rw_eqs Y.
  - exact O1.
  - exact O2.
  - intros i Hi Hi2. destruct (ET i ltac:(lia)) as (T1 & T2 & T3 & T4 & T5 & T6).
    rewrite T1, T2, T3, T4, T5, T6. exact (O3 i Hi Hi2).
  - exact O4.
  - exact O5.
  - exact O6.
  - exact O7.
  - exact O8.
  - exact O9.
  - exact O10.
  - exact O11.
  - exact O12.
  - exact O13.
  - exact O14.
  - exact O15.
  - exact O16.
  - exact O17.
Qed.

Lemma ow_room_frR : ow_room X -> ow_room Y.
Proof.
  intros [R0 R1 R2 R3 R4 R5 R6 R7 R8].
  destruct ow_counts_frR as (_ & E2 & _ & E4 & _ & E6 & _ & E8 & _ & E10 & _ & E12 & _ & E14 & _ & E16).
  constructor; [exact (ow_got_eq_frR R0) | rewrite E2 | rewrite E4 | rewrite E6 | rewrite E8 | rewrite E10
               | rewrite E12 | rewrite E14 | rewrite E16]; assumption.
Qed.

Lemma ow_step_frR : forall B, ow_step B X -> ow_step B Y.
Proof.
  intros B [S1 S2 S3 S4 S5 S6 S7 S8].
  destruct ow_counts_frR as (_ & E2 & _ & E4 & _ & E6 & _ & E8 & _ & E10 & _ & E12 & _ & E14 & _ & E16).
  constructor; [rewrite E2 | rewrite E4 | rewrite E6 | rewrite E8 | rewrite E10 | rewrite E12 | rewrite E14
               | rewrite E16]; assumption.
Qed.

End OwFrame.

(* the same over a range list that misses OW and GOT *)
Lemma ow_rs_miss : forall rs, disj_rs OFF_GOT (OFF_OW + SZ_OW - OFF_GOT) rs = true ->
  forall a, OFF_GOT <= a < OFF_OW + SZ_OW -> ~ in_rs rs a.
Proof. intros rs Hd a Ha. apply (disj_rs_ok _ _ rs Hd). lia. Qed.

Lemma ow_got_eq_fr : forall rs X Y, wframe (in_rs rs) X Y -> disj_rs OFF_GOT (OFF_OW + SZ_OW - OFF_GOT) rs = true ->
  ow_got_eq X -> ow_got_eq Y.
Proof. intros rs X Y H Hd. exact (ow_got_eq_frR _ X Y H (ow_rs_miss rs Hd)). Qed.

Lemma ow_room_fr : forall rs X Y, wframe (in_rs rs) X Y -> disj_rs OFF_GOT (OFF_OW + SZ_OW - OFF_GOT) rs = true ->
  ow_room X -> ow_room Y.
Proof. intros rs X Y H Hd. exact (ow_room_frR _ X Y H (ow_rs_miss rs Hd)). Qed.

Lemma ow_step_fr : forall rs B X Y, wframe (in_rs rs) X Y -> disj_rs OFF_GOT (OFF_OW + SZ_OW - OFF_GOT) rs = true ->
  ow_step B X -> ow_step B Y.
Proof. intros rs B X Y H Hd. exact (ow_step_frR _ X Y H (ow_rs_miss rs Hd) B). Qed.

Lemma ow_step_refl : forall B, ow_step B B.
Proof. intros B. constructor; lia. Qed.

Lemma ow_room_zero : forall B, ow_zero B -> ow_room B.
Proof.
  intros B Hz. pose proof (ow_got_eq_zero B Hz) as Hog. destruct Hz.
  constructor; [exact Hog | ..]; lia.
Qed.

(* after the first reception of an operation: room for the second *)
Lemma ow_room_after : forall B W, ow_zero B -> ow_got_eq W -> ow_step B W -> ow_room W.
Proof.
  intros B W Hz Hog [S1 S2 S3 S4 S5 S6 S7 S8]. destruct Hz.
  constructor; [exact Hog | ..]; lia.
Qed.

(* ---- rx_pre / rx_branch as the case OW = GOT = 0 of rx_pre_g / rx_branch_g ---- *)

Lemma rx_pre_g_of : forall I ops B buf, rx_pre I ops B buf -> rx_pre_g I ops B buf.
Proof.
  intros I ops B buf [Hc Hk Hz Hf Hs].
  constructor; [exact Hc | exact Hk | exact (ow_room_zero B Hz) | intros _ _; exact Hf | exact Hs].
Qed.

Lemma rx_branch_of_g : forall cond, rx_branch_g cond -> rx_branch cond.
Proof.
  intros cond Hg. unfold rx_branch. intros I ops fr n B. cbv zeta. intros Hn Ha Hpre Hacc Hc.
  specialize (Hg I ops fr n B). cbv zeta in Hg.
  destruct (Hg Hn Ha (rx_pre_g_of _ _ _ _ Hpre) Hacc Hc) as (Bm & E1 & E2 & E3 & Hl).
  exists Bm. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
  intros W HW. destruct (Hl W HW) as (W' & Es & Hp). exists W'. exact (conj Es (rh_post _ _ _ _ _ _ Hp)).
Qed.

(* rx_accepts reads of the world only M.desk_known, M.desk and M.state *)
Lemma rx_accepts_same : forall X Y buf, rx_accepts X buf ->
  M_desk_known Y = M_desk_known X -> M_desk Y = M_desk X -> M_state Y = M_state X -> rx_accepts Y buf.
Proof.
  intros X Y buf [A1 A2 A3 A4 A5 A6] Ek Ed Es.
  constructor; [exact A1 | exact A2 | exact A3 | rewrite Ek, Ed; exact A4 | rewrite Ek; exact A5
               | rewrite Es; exact A6].
Qed.

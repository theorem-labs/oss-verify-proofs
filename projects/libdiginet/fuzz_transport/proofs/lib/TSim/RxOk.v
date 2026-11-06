(* rx_ok: one reception (fuzz_transport.c m_rx FT:280-375 and the library's diginet_session_rx DS:263-318, with its
   tick, DS:317, on the same bytes): the model m_rx on the heap frame, then the library, from rx_pre; the result is
   rx_done, what settle needs (SettleOk.v). rx_ok_g is the same for any reception of an operation, from rx_pre_g
   (RxBase.v: OW and GOT agree but need not be zero, M.fail need not be g_fail_next), with rx_done_g, which also
   carries what the next reception needs; rx_ok is its case OW = GOT = 0. It joins the filters (RxFlt.v) with the
   six branches of the switch (RxAnn0, RxAnn1, RxAck, RxData, RxE3, RxMisc) and the quiet tick (TickOk.v). The
   operations on top: RxOp.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0
  TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SimLib QueueFacts SettleOk
  TickDefs TickOk RxDefs RxBase RxList RxFrame RxW RxCore RxMisc RxFlt RxAnn0 RxAnn1 RxAck RxData RxE3.
Import ListNotations.
Open Scope Z_scope.

(* the world functions stay folded for the unifier (RxW.v header); the getters unfold to them *)
Local Opaque sub upd u_at s32_at put.

(* a read across H : wframe R X Y whose range HR keeps out of R *)
Ltac rg H HR := wunf_get;
  lazymatch goal with
  | |- s32_at _ _ = s32_at _ _ => apply (wframe_s32_at _ _ _ _ H)
  | |- u_at _ _ _ = u_at _ _ _ => apply (wframe_u_at _ _ _ _ _ H)
  | |- sub _ _ _ = sub _ _ _ => apply (wframe_sub _ _ _ _ _ H)
  end;
  [ wnum
  | let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; apply HR; revert Ha; wunf_off; unfold TRANS_MAX; intros; lia ].

(* ---- what settle reads, across a frame that misses it ---- *)

Lemma og_frame : forall (R : Z -> Prop) X Y, wframe R X Y ->
  (forall a, OFF_GOT <= a < OFF_OW + SZ_OW -> ~ R a) -> ow_got_eq X -> ow_got_eq Y.
Proof.
  intros R X Y H HR [O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 O12 O13 O14 O15 O16 O17].
  assert (E1 : GOT_n Y = GOT_n X) by rg H HR.
  assert (E2 : OW_n Y = OW_n X) by rg H HR.
  assert (E3 : GOT_e2 Y = GOT_e2 X) by rg H HR.
  assert (E4 : OW_e2 Y = OW_e2 X) by rg H HR.
  assert (E5 : GOT_e3 Y = GOT_e3 X) by rg H HR.
  assert (E6 : OW_e3 Y = OW_e3 X) by rg H HR.
  assert (E7 : GOT_acks Y = GOT_acks X) by rg H HR.
  assert (E8 : OW_acks Y = OW_acks X) by rg H HR.
  assert (E9 : GOT_desk Y = GOT_desk X) by rg H HR.
  assert (E10 : OW_desk Y = OW_desk X) by rg H HR.
  assert (E11 : GOT_foreign Y = GOT_foreign X) by rg H HR.
  assert (E12 : OW_foreign Y = OW_foreign X) by rg H HR.
  assert (E13 : GOT_acked Y = GOT_acked X) by rg H HR.
  assert (E14 : OW_acked Y = OW_acked X) by rg H HR.
  assert (E15 : GOT_ndata Y = GOT_ndata X) by rg H HR.
  assert (E16 : OW_ndata Y = OW_ndata X) by rg H HR.
  assert (ET : forall i, 0 <= i < TRANS_MAX ->
    GOT_t_state Y i = GOT_t_state X i /\ GOT_t_old Y i = GOT_t_old X i /\ GOT_t_reason Y i = GOT_t_reason X i /\
    OW_t_state Y i = OW_t_state X i /\ OW_t_old Y i = OW_t_old X i /\ OW_t_reason Y i = OW_t_reason X i).
  { intros i Hi. unfold TRANS_MAX in Hi.
    split; [rg H HR|]. split; [rg H HR|]. split; [rg H HR|]. split; [rg H HR|]. split; [rg H HR | rg H HR]. }
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

Lemma og_settle : forall B, ow_got_eq B -> settle_eq B.
Proof.
  intros B [O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 O12 O13 O14 O15 O16 O17].
  constructor; [exact O8 | exact O4 | exact O6 | exact O16 | exact O10 | exact O12 | exact O14 | exact O1 | exact O3].
Qed.

(* ---- one reception ---- *)

(* the switch of an accepted frame, by its command (DS:298-316) *)
Lemma rx_switch_g : forall (HL : links) I ops fr n B,
  let buf := rxbuf fr n in
  let now := g_now B in
  0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  0 < tf_addr fr /\ tf_addr fr + Z.of_nat (length (tf_bytes fr)) < 2 ^ 64 ->
  rx_pre_g I ops B buf -> rx_accepts B buf ->
  exists Bm, m_rx_sw I fr n (set_M_last_rx (learn_M B buf) now) = Some (Bm, tt) /\
    m_tick_m Bm = Some (Bm, tt) /\
    (length Bm = length B /\ forall a : nat, ~ in_rs R_mod (Z.of_nat a) -> nth_error Bm a = nth_error B a) /\
    forall W, lib_start Bm W buf ->
      exists W', rx_sw I (Some fr) W buf now = Some (W', tt) /\ rx_post_g I ops B buf W W'.
Proof.
  intros HL I ops fr n B. cbv zeta. intros Hn Ha Hpre Hacc.
  destruct (Z.eq_dec (fr_cmd (rxbuf fr n)) DIGINET_CMD_ANNOUNCE) as [C1|C1].
  { exact (rx_e0_g HL I ops fr n B Hn Ha Hpre Hacc C1). }
  destruct (Z.eq_dec (fr_cmd (rxbuf fr n)) DIGINET_CMD_ANNOUNCE_SESSION) as [C2|C2].
  { exact (rx_e1_g HL I ops fr n B Hn Ha Hpre Hacc C2). }
  destruct (Z.eq_dec (fr_cmd (rxbuf fr n)) DIGINET_CMD_ACK) as [C3|C3].
  { exact (rx_ack_g HL I ops fr n B Hn Ha Hpre Hacc C3). }
  destruct (Z.eq_dec (fr_cmd (rxbuf fr n)) DIGINET_CMD_DATA) as [C4|C4].
  { exact (rx_data_g HL I ops fr n B Hn Ha Hpre Hacc C4). }
  destruct (Z.eq_dec (fr_cmd (rxbuf fr n)) DIGINET_CMD_DISCONNECT) as [C5|C5].
  { exact (rx_e3_g HL I ops fr n B Hn Ha Hpre Hacc C5). }
  exact (rx_other_g HL I ops fr n B Hn Ha Hpre Hacc (conj C1 (conj C2 (conj C3 (conj C4 C5))))).
Qed.

Theorem rx_ok_g : forall (HL : links) I ops fr n B,
  0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  0 < tf_addr fr /\ tf_addr fr + Z.of_nat (length (tf_bytes fr)) < 2 ^ 64 ->
  rx_pre_g I ops B (rxbuf fr n) ->
  exists Bx t, m_rx_m I (Some fr) B n = Some (Bx, t) /\ m_tick_m Bx = Some (Bx, tt) /\
    wframe (in_rs R_mod) B Bx /\
    forall W, wframe (in_rs R_poll) Bx W ->
      exists W' r, diginet_session_rx_m I (Some fr) W (rxbuf fr n) (g_now B) = Some (W', r) /\
        rx_done_g I ops t B (rxbuf fr n) W W'.
Proof.
  intros HL I ops fr n B Hn Ha Hpre.
  destruct (rx_accepts_dec B (rxbuf fr n)) as [Hacc | Hrej].
  2:{ destruct (rx_reject_g HL I ops fr n B Hn Hpre Hrej) as (Bx & E & Et & Ef & H).
      exists Bx, 0. exact (conj E (conj Et (conj Ef H))). }
  destruct (rx_accept_path_g HL I ops fr n B Hn Hpre Hacc) as [Em Hlib].
  destruct (rx_switch_g HL I ops fr n B Hn Ha Hpre Hacc) as (Bm & Hm & Ht & Hf & Hl).
  exists Bm, 1. split; [|split; [exact Ht | split; [exact Hf |]]].
  { rewrite Em, Hm. cbv beta iota. rewrite Ht. reflexivity. }
  assert (Hf' : wframe (in_rs R_mod) B Bm) by exact Hf.
  intros W HW.
  destruct (Hlib Bm W Hf HW) as (W1 & Hs & R1 & R2 & R3 & R4 & Hnow1 & Rs & El).
  destruct (Hl W1 Hs) as (W' & Hsw & Hpost).
  pose proof (rh_post _ _ _ _ _ _ Hpost) as Hpost0.
  destruct (tick_quiet_ok HL I (Some fr) ops W' (rq_core _ _ _ _ Hpost0)) as (W'' & r & Htk & Htp).
  assert (Enow : g_now W' = g_now B) by (rewrite (rq_now _ _ _ _ Hpost0); exact Hnow1).
  exists W'', r. split.
  { rewrite El, Hsw. cbv beta iota. rewrite <- Enow. exact Htk. }
  pose proof (tp_frame _ _ _ _ Htp) as Ht'.
  assert (HRt : forall a, OFF_GOT <= a < OFF_OW + SZ_OW -> ~ R_tick a)
    by (intros a Ha'; unfold R_tick; revert Ha'; wunf_off; intros; lia).
  assert (HRx : forall a, (OFF_g_rx_send <= a < OFF_g_cfg) -> ~ R_tick a)
    by (intros a Ha'; unfold R_tick; revert Ha'; wunf_off; intros; lia).
  assert (T1 : g_rx W'' = g_rx W') by rg Ht' HRx.
  assert (T2 : g_rx_len W'' = g_rx_len W') by rg Ht' HRx.
  assert (T3 : g_rx_times W'' = g_rx_times W') by rg Ht' HRx.
  assert (T4 : g_rx_fail W'' = g_rx_fail W') by rg Ht' HRx.
  assert (T5 : g_now W'' = g_now W') by rg Ht' HRx.
  assert (T6 : g_rx_send W'' = g_rx_send W') by rg Ht' HRx.
  assert (Nw : g_now W = g_now B).
  { assert (HRp : forall a, OFF_g_now <= a < OFF_g_now + 8 -> ~ in_rs R_poll a).
    { intros a Ha'. apply (disj_rs_ok OFF_g_now 8 R_poll); [vm_compute; reflexivity | exact Ha']. }
    assert (HRm : forall a, OFF_g_now <= a < OFF_g_now + 8 -> ~ in_rs R_mod a).
    { intros a Ha'. apply (disj_rs_ok OFF_g_now 8 R_mod); [vm_compute; reflexivity | exact Ha']. }
    transitivity (g_now Bm); [rg HW HRp | rg Hf' HRm]. }
  constructor.
  - constructor.
    + exact (tp_core _ _ _ _ Htp).
    + exact (tp_keepalive _ _ _ _ Htp).
    + exact (og_frame _ _ _ Ht' HRt (rq_og _ _ _ _ Hpost0)).
    + intros _. exact (tp_drain _ _ _ _ Htp).
    + rewrite T1, (rq_rx _ _ _ _ Hpost0). exact R1.
    + rewrite T2, (rq_rx_len _ _ _ _ Hpost0). exact R2.
    + rewrite T3, (rq_rx_times _ _ _ _ Hpost0). exact R3.
    + rewrite T4, (rq_rx_fail _ _ _ _ Hpost0). exact R4.
    + rewrite T5, Enow, Nw. reflexivity.
  - exact (ow_step_frR R_tick W' W'' Ht' HRt B (rh_step _ _ _ _ _ _ Hpost)).
  - rewrite T6, (rh_rx_send _ _ _ _ _ _ Hpost). exact Rs.
  - intros E. discriminate E.
  - (* a full-body e0 leaves a state other than ONLINE, where the tick changes nothing (TickOk.v
       tick_quiet_off) *)
    intros _ Hw. destruct (rh_wake _ _ _ _ _ _ Hpost Hw) as [Efl Eon].
    pose proof (tick_quiet_off I (Some fr) ops W' (rq_core _ _ _ _ Hpost0) Eon) as Eq.
    rewrite Htk in Eq. injection Eq as EW Er. subst W''. exact (conj Efl Eon).
  - intros _. exact Hacc.
Qed.

Theorem rx_ok : forall (HL : links) I ops fr n B,
  0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  0 < tf_addr fr /\ tf_addr fr + Z.of_nat (length (tf_bytes fr)) < 2 ^ 64 ->
  rx_pre I ops B (rxbuf fr n) ->
  exists Bx t, m_rx_m I (Some fr) B n = Some (Bx, t) /\ m_tick_m Bx = Some (Bx, tt) /\
    wframe (in_rs R_mod) B Bx /\
    forall W, wframe (in_rs R_poll) Bx W ->
      exists W' r, diginet_session_rx_m I (Some fr) W (rxbuf fr n) (g_now B) = Some (W', r) /\ rx_done I ops t W W'.
Proof.
  intros HL I ops fr n B Hn Ha Hpre.
  destruct (rx_ok_g HL I ops fr n B Hn Ha (rx_pre_g_of _ _ _ _ Hpre)) as (Bx & t & E & Et & Ef & H).
  exists Bx, t. split; [exact E|]. split; [exact Et|]. split; [exact Ef|].
  intros W HW. destruct (H W HW) as (W' & r & Es & Hd). exists W', r. exact (conj Es (rk_done _ _ _ _ _ _ _ Hd)).
Qed.

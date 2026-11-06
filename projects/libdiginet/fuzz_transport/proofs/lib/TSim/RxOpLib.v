(* The receptions of the loop of LLVMFuzzerTestOneInput (fuzz_transport.c receive FT:995-1025, TOps.v receive_m)
   keep agree, given rx_ok (RxOk.v) and rx_ok_g, which are taken here as the hypotheses rx_ok_stmt / rx_ok_g_stmt
   (their statements verbatim); RxOp.v instantiates them. The ticks are TickOk.v's (tick_quiet_keep,
   tick_quiet_off).
   - receive (p, n, 0, 0) (FT:1020-1021): op_begin, g_rx_send, then m_rx and the library's rx on the heap frame
     (rx_ok with n = the frame's length), then settle (m_rx's return value t is 0 or 1: rxop_m_rx_01).
   - receive (p, n, 1, flags) (FT:1004-1018): the poll (DS:505-527) with g_rx = the frame, g_rx_len = got =
     min (1514, n), g_rx_times = 1 (flags bit 0 clear) or 2 (bit 0 set), g_rx_fail = flags bit 1. Deadline
     (Deadline.v, through the frames: it reads only g_s); then io_recv (FT:906-929): it fails at once when
     g_rx_fail is set; else it hands the got bytes over, running the model first: m_rx on them (FT:923-924, from
     the frame's address on) or m_tick on an empty frame (FT:925-926). The library's rx follows (rx_ok_g's
     library part), then the tick (DS:522), then the drain loop (DS:524-525): with g_rx_times 2 io_recv hands
     the frame over a second time, the model and the library's rx run again from the world the first reception
     and the tick left (rx_ok_g again: OW and GOT are no longer zero there, and the tick may have consumed
     g_fail_next); then g_rx_times = 0 ends the loop. Then g_rx = 0 and settle.
   Around the library the receive writes only the scalars grx_rs (g_rx_send, g_rx_fail, g_rx_times, g_rx,
   g_rx_len); agree_core, C2's keepalive clause and the drain fact read none of them (grx_core, grx_ka,
   grx_drain). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0
  TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SimLib QueueFacts SettleOk
  Deadline TickDefs TickOk SubmitLib RxBase RxW RxCore.
Import ListNotations.
Open Scope Z_scope.

(* the option monad of TOps.v, for stating the model's pieces in its own shape *)
Local Notation "'let?' p ':=' e 'in' b" :=
  (match e with Some p => b | None => None end)
  (at level 200, p pattern, e at level 100, b at level 200, right associativity).

(* ---- list facts (no world) ---- *)

Lemma rxop_sub0 : forall (l : list byte) k, sub l 0 k = firstn k l.
Proof. intros l k. unfold sub. reflexivity. Qed.

Lemma rxbuf_all : forall a bytes, rxbuf (TFrame a bytes) (Z.of_nat (length bytes)) = bytes.
Proof. intros a bytes. unfold rxbuf. cbn [tf_bytes]. rewrite Nat2Z.id. apply firstn_all. Qed.

Lemma rxop_length_upd_in : forall (bs v : list byte) k m, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat m ->
  length bs = m -> length (upd bs k v) = m.
Proof. intros bs v k m Hk Hv Hb. subst m. apply length_upd; [exact Hk | exact Hv]. Qed.

(* spec.h:228-247: n = max(60, 30 + len) bytes, every write inside them *)
Lemma spec_build_frame_len : forall dst src send ack retry cmd ncmds body zero_sum,
  (length body <= 1484)%nat ->
  Z.of_nat (length (fst (spec_build_frame dst src send ack retry cmd ncmds body zero_sum))) <= 1514.
Proof.
  intros dst src send ack retry cmd ncmds body zero_sum Hb.
  cbv beta iota zeta delta [spec_build_frame fst].
  assert (Hn : 30 + Z.of_nat (length body) <=
               (if 30 + Z.of_nat (length body) <? 60 then 60 else 30 + Z.of_nat (length body)) <= 1514).
  { destruct (Z.ltb_spec (30 + Z.of_nat (length body)) 60); cbv beta iota; lia. }
  set (n := if 30 + Z.of_nat (length body) <? 60 then 60 else 30 + Z.of_nat (length body)) in *.
  clearbody n.
  match goal with |- Z.of_nat (length ?X) <= _ => assert (E : length X = Z.to_nat n) end.
  { destruct (Z.of_nat (length body) =? 0); cbv beta iota;
      repeat (apply rxop_length_upd_in;
              [lia | rewrite ?length_put16, ?length_put32, ?length_firstn; cbn [length]; lia | ]);
      apply repeat_length. }
  rewrite E. lia.
Qed.

(* fuzz_transport.c:1054 NAME[]: at most 8 bytes *)
Lemma rxop_ann_name_len : forall i, (length (nth i op_announce_NAME []) <= 8)%nat.
Proof.
  intros i. unfold op_announce_NAME.
  destruct i as [|[|[|i]]]; cbn [nth]; [unfold bs; rewrite length_map; cbn [length]; lia ..|].
  destruct i; cbn [nth length]; lia.
Qed.

(* fuzz_transport.c:1058-1064: the announce body stays 34 bytes *)
Lemma rxop_ann_body_len : forall m nm,
  length (upd (upd (if m mod 16 <? 10 then upd (repeat (b8 0) (Z.to_nat (SPEC_ANN_MIN + 1))) (m mod 16) HOST
                    else if m mod 16 <? 13 then upd (repeat (b8 0) (Z.to_nat (SPEC_ANN_MIN + 1))) (m mod 16 - 10) OTHER
                    else repeat (b8 0) (Z.to_nat (SPEC_ANN_MIN + 1)))
              SPEC_ANN_VERSION ANN_VERSION_137)
         SPEC_ANN_NAME (nth (Z.to_nat (nm mod 3)) op_announce_NAME [])) = 34%nat.
Proof.
  intros m nm.
  assert (Hm : 0 <= m mod 16 < 16) by (apply Z.mod_pos_bound; lia).
  pose proof (rxop_ann_name_len (Z.to_nat (nm mod 3))) as Hnm.
  assert (L0 : length (repeat (b8 0) (Z.to_nat (SPEC_ANN_MIN + 1))) = 34%nat)
    by (rewrite repeat_length; reflexivity).
  assert (LH : length HOST = 6%nat) by reflexivity.
  assert (LO : length OTHER = 6%nat) by reflexivity.
  assert (LV : length ANN_VERSION_137 = 4%nat) by reflexivity.
  apply rxop_length_upd_in; [unfold SPEC_ANN_NAME; lia | unfold SPEC_ANN_NAME; lia |].
  apply rxop_length_upd_in; [unfold SPEC_ANN_VERSION; lia | rewrite LV; unfold SPEC_ANN_VERSION; lia |].
  destruct (Z.ltb_spec (m mod 16) 10); cbv beta iota;
    [apply rxop_length_upd_in; [lia | rewrite LH; lia | exact L0] |].
  destruct (Z.ltb_spec (m mod 16) 13); cbv beta iota;
    [apply rxop_length_upd_in; [lia | rewrite LO; lia | exact L0] | exact L0].
Qed.

(* the world functions stay folded for the unifier (RxW.v header); the getters unfold to them *)
Local Opaque sub upd u_at s32_at put.

(* ---- rx_ok's and rx_ok_g's statements (RxOk.v), the hypotheses of this file ---- *)
Definition rx_ok_stmt : Prop := forall I ops fr n B,
  0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  0 < tf_addr fr /\ tf_addr fr + Z.of_nat (length (tf_bytes fr)) < 2 ^ 64 ->
  rx_pre I ops B (rxbuf fr n) ->
  exists Bx t, m_rx_m I (Some fr) B n = Some (Bx, t) /\ m_tick_m Bx = Some (Bx, tt) /\
    wframe (in_rs R_mod) B Bx /\
    forall W, wframe (in_rs R_poll) Bx W ->
      exists W' r, diginet_session_rx_m I (Some fr) W (rxbuf fr n) (g_now B) = Some (W', r) /\ rx_done I ops t W W'.

Definition rx_ok_g_stmt : Prop := forall I ops fr n B,
  0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  0 < tf_addr fr /\ tf_addr fr + Z.of_nat (length (tf_bytes fr)) < 2 ^ 64 ->
  rx_pre_g I ops B (rxbuf fr n) ->
  exists Bx t, m_rx_m I (Some fr) B n = Some (Bx, t) /\ m_tick_m Bx = Some (Bx, tt) /\
    wframe (in_rs R_mod) B Bx /\
    forall W, wframe (in_rs R_poll) Bx W ->
      exists W' r, diginet_session_rx_m I (Some fr) W (rxbuf fr n) (g_now B) = Some (W', r) /\
        rx_done_g I ops t B (rxbuf fr n) W W'.

(* ---- small facts ---- *)

(* the send counter receive stores (FT:1002-1003, :1007-1008) *)
Definition rxop_v (buf : list byte) : Z := if fr_code buf =? 0 then fr_send buf else 0.
(* the bytes the poll hands over (FT:1005) *)
Definition rxop_got (bytes : list byte) : Z :=
  if SPEC_MAX_FRAME <? Z.of_nat (length bytes) then SPEC_MAX_FRAME else Z.of_nat (length bytes).

Lemma rxop_v_ok : forall buf, 0 <= rxop_v buf < 2 ^ 32 /\ (fr_code buf = DIGINET_OK -> rxop_v buf = fr_send buf).
Proof.
  intros buf. unfold rxop_v.
  assert (Hs : 0 <= fr_send buf < 2 ^ 32).
  { unfold fr_send, be32, at8.
    pose proof (bz_range (nth 18 buf (b8 0))). pose proof (bz_range (nth 19 buf (b8 0))).
    pose proof (bz_range (nth 20 buf (b8 0))). pose proof (bz_range (nth 21 buf (b8 0))). lia. }
  destruct (Z.eqb_spec (fr_code buf) 0) as [E|E].
  - split; [exact Hs | intros _; reflexivity].
  - split; [lia | intros H; unfold DIGINET_OK in H; contradiction].
Qed.

Lemma rxop_got_ok : forall bytes, 0 <= rxop_got bytes <= 1514 /\ rxop_got bytes <= Z.of_nat (length bytes).
Proof.
  intros bytes. unfold rxop_got, SPEC_MAX_FRAME.
  destruct (Z.ltb_spec 1514 (Z.of_nat (length bytes))); lia.
Qed.

Lemma rxop_land01 : forall x, Z.land x 1 = 0 \/ Z.land x 1 = 1.
Proof.
  intros x. assert (E : Z.land x 1 = x mod 2) by (apply (Z.land_ones x 1); lia).
  pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia.
Qed.

Lemma rxop_swrap : forall x, 0 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof. intros x Hx. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn. lia. Qed.

(* m_rx returns 0 or 1 (FT:280-375: return 0 / return 1) *)
Definition rxop_t01 (o : option (list byte * Z)) : Prop := forall Bx t, o = Some (Bx, t) -> t = 0 \/ t = 1.

Lemma rxop_t01_none : rxop_t01 None.
Proof. intros Bx t H. discriminate H. Qed.
Lemma rxop_t01_0 : forall B, rxop_t01 (Some (B, 0)).
Proof. intros B Bx t H. injection H as E1 E2. subst t. left. reflexivity. Qed.
Lemma rxop_t01_1 : forall B, rxop_t01 (Some (B, 1)).
Proof. intros B Bx t H. injection H as E1 E2. subst t. right. reflexivity. Qed.
Lemma rxop_t01_if : forall (b : bool) o1 o2, rxop_t01 o1 -> rxop_t01 o2 -> rxop_t01 (if b then o1 else o2).
Proof. intros [|] o1 o2 H1 H2; [exact H1 | exact H2]. Qed.
Lemma rxop_t01_bind : forall (A : Type) (o : option A) (f : A -> option (list byte * Z)),
  (forall x, rxop_t01 (f x)) -> rxop_t01 (match o with Some x => f x | None => None end).
Proof. intros A [x|] f H; [exact (H x) | exact rxop_t01_none]. Qed.
Lemma rxop_t01_pair : forall (A C : Type) (p : A * C) (f : A -> C -> option (list byte * Z)),
  (forall x y, rxop_t01 (f x y)) -> rxop_t01 (match p with (x, y) => f x y end).
Proof. intros A C [x y] f H. exact (H x y). Qed.

Lemma rxop_m_rx_01 : forall I F B n Bx t, m_rx_m I F B n = Some (Bx, t) -> t = 0 \/ t = 1.
Proof.
  intros I F B n. change (rxop_t01 (m_rx_m I F B n)).
  unfold m_rx_m. destruct F as [fr|]; [|exact rxop_t01_none].
  cbv beta zeta.
  repeat first [ apply rxop_t01_if | apply rxop_t01_bind | apply rxop_t01_pair | apply rxop_t01_none
               | apply rxop_t01_0 | apply rxop_t01_1 | lazymatch goal with |- forall _, _ => intro end ].
Qed.

(* m_tick does nothing under agree_core (C2: nothing overdue) *)
Lemma rxop_tick_quiet : forall I ops X, agree_core I ops X -> m_tick_m X = Some (X, tt).
Proof.
  intros I ops X Hc. pose proof (ac_time _ _ _ Hc) as Ht. pose proof (ac_cfg _ _ _ Hc) as Hg.
  apply m_tick_quiet.
  - intros Hw. exact (conj (c1_wake_sent _ _ Ht) (c2_wake _ _ Ht Hw)).
  - intros Ho. exact (conj (c1_last_rx _ _ Ht) (c2_online _ _ Ht Ho)).
  - exact (proj2 (a1_wake_timeout _ Hg)).
  - exact (proj2 (a1_offline _ Hg)).
Qed.

(* ---- reads across a frame (RxOk.v rg, og_frame, og_settle) ---- *)

Ltac rxop_rg H HR := wunf_get;
  lazymatch goal with
  | |- s32_at _ _ = s32_at _ _ => apply (wframe_s32_at _ _ _ _ H)
  | |- u_at _ _ _ = u_at _ _ _ => apply (wframe_u_at _ _ _ _ _ H)
  | |- sub _ _ _ = sub _ _ _ => apply (wframe_sub _ _ _ _ _ H)
  end;
  [ wnum
  | let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; apply HR; revert Ha; wunf_off; unfold TRANS_MAX; intros; lia ].

Lemma rxop_og_frame : forall (R : Z -> Prop) X Y, wframe R X Y ->
  (forall a, OFF_GOT <= a < OFF_OW + SZ_OW -> ~ R a) -> ow_got_eq X -> ow_got_eq Y.
Proof.
  intros R X Y H HR [O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 O12 O13 O14 O15 O16 O17].
  assert (E1 : GOT_n Y = GOT_n X) by rxop_rg H HR.
  assert (E2 : OW_n Y = OW_n X) by rxop_rg H HR.
  assert (E3 : GOT_e2 Y = GOT_e2 X) by rxop_rg H HR.
  assert (E4 : OW_e2 Y = OW_e2 X) by rxop_rg H HR.
  assert (E5 : GOT_e3 Y = GOT_e3 X) by rxop_rg H HR.
  assert (E6 : OW_e3 Y = OW_e3 X) by rxop_rg H HR.
  assert (E7 : GOT_acks Y = GOT_acks X) by rxop_rg H HR.
  assert (E8 : OW_acks Y = OW_acks X) by rxop_rg H HR.
  assert (E9 : GOT_desk Y = GOT_desk X) by rxop_rg H HR.
  assert (E10 : OW_desk Y = OW_desk X) by rxop_rg H HR.
  assert (E11 : GOT_foreign Y = GOT_foreign X) by rxop_rg H HR.
  assert (E12 : OW_foreign Y = OW_foreign X) by rxop_rg H HR.
  assert (E13 : GOT_acked Y = GOT_acked X) by rxop_rg H HR.
  assert (E14 : OW_acked Y = OW_acked X) by rxop_rg H HR.
  assert (E15 : GOT_ndata Y = GOT_ndata X) by rxop_rg H HR.
  assert (E16 : OW_ndata Y = OW_ndata X) by rxop_rg H HR.
  assert (ET : forall i, 0 <= i < TRANS_MAX ->
    GOT_t_state Y i = GOT_t_state X i /\ GOT_t_old Y i = GOT_t_old X i /\ GOT_t_reason Y i = GOT_t_reason X i /\
    OW_t_state Y i = OW_t_state X i /\ OW_t_old Y i = OW_t_old X i /\ OW_t_reason Y i = OW_t_reason X i).
  { intros i Hi. unfold TRANS_MAX in Hi.
    split; [rxop_rg H HR|]. split; [rxop_rg H HR|]. split; [rxop_rg H HR|]. split; [rxop_rg H HR|].
    split; [rxop_rg H HR | rxop_rg H HR]. }
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

Lemma rxop_og_settle : forall B, ow_got_eq B -> settle_eq B.
Proof.
  intros B [O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 O12 O13 O14 O15 O16 O17].
  constructor; [exact O8 | exact O4 | exact O6 | exact O16 | exact O10 | exact O12 | exact O14 | exact O1 | exact O3].
Qed.

(* ---- the receive's scalars: agree_core, C2's keepalive clause and the drain fact read none of them ---- *)

Definition grx_rs : list (Z * Z) :=
  [(OFF_g_rx_send, OFF_g_now - OFF_g_rx_send); (OFF_g_rx, OFF_g_cfg - OFF_g_rx)].
(* every other byte of the world *)
Definition grx_foot : list (Z * Z) :=
  [(0, OFF_g_rx_send); (OFF_g_now, OFF_g_rx - OFF_g_now); (OFF_g_cfg, W_LEN - OFF_g_cfg)].

Lemma grx_foot_disj : forall a, in_ranges grx_foot a -> ~ in_ranges grx_rs a.
Proof. apply rdisj_spec. vm_compute. reflexivity. Qed.

Lemma grx_q_disj : forall a, in_ranges foot_q a -> ~ in_ranges grx_rs a.
Proof. apply rdisj_spec. vm_compute. reflexivity. Qed.

Section Grx.
Variables (X Y : list byte).
Hypothesis HF : wframe (in_rs grx_rs) X Y.

Lemma grx_cfg : agree_cfg X -> agree_cfg Y.
Proof.
  intros H. pose proof (HF : wsame X Y grx_rs) as Hw. pose proof grx_foot_disj as Hd.
  destruct H. constructor; wsame_rw Hw Hd; wexact.
Qed.

Lemma grx_io : forall I, agree_io I X -> agree_io I Y.
Proof.
  intros I H. pose proof (HF : wsame X Y grx_rs) as Hw. pose proof grx_foot_disj as Hd.
  destruct H. constructor; wsame_rw Hw Hd; wexact.
Qed.

Lemma grx_st : agree_st X -> agree_st Y.
Proof.
  intros H. pose proof (HF : wsame X Y grx_rs) as Hw. pose proof grx_foot_disj as Hd.
  destruct H. constructor; wsame_rw Hw Hd; wexact.
Qed.

Lemma grx_fly : agree_fly X -> agree_fly Y.
Proof.
  intros H. pose proof (HF : wsame X Y grx_rs) as Hw. pose proof grx_foot_disj as Hd.
  destruct H as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11].
  constructor; wsame_rw Hw Hd; try wexact.
  intros Hon. destruct (F11 Hon) as (body & ncmds & H1 & H2 & H3 & H4 & H5 & H6).
  assert (Hn : (Z.to_nat (M_fly_len X) <= 1514)%nat) by (rewrite H4; unfold frame_len; lia).
  assert (E1 : sub Y A_M_fly_frame (Z.to_nat (M_fly_len X)) = sub X A_M_fly_frame (Z.to_nat (M_fly_len X)))
    by (refine (wsame_cov_sub_le X Y grx_rs grx_foot A_M_fly_frame _ 1514 Hw Hd _ Hn _);
        [wle | vm_compute; reflexivity]).
  assert (E2 : sub Y A_S_inflight_frame (Z.to_nat (M_fly_len X)) = sub X A_S_inflight_frame (Z.to_nat (M_fly_len X)))
    by (refine (wsame_cov_sub_le X Y grx_rs grx_foot A_S_inflight_frame _ 1514 Hw Hd _ Hn _);
        [wle | vm_compute; reflexivity]).
  wrw E1. wrw E2. exists body, ncmds. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
Qed.

Lemma grx_time : forall ops, agree_time ops X -> agree_time ops Y.
Proof.
  intros ops H. pose proof (HF : wsame X Y grx_rs) as Hw. pose proof grx_foot_disj as Hd.
  destruct H. constructor; wsame_rw Hw Hd; wexact.
Qed.

Lemma grx_misc : forall I, agree_misc I X -> agree_misc I Y.
Proof.
  intros I H. pose proof (HF : wsame X Y grx_rs) as Hw. pose proof grx_foot_disj as Hd.
  destruct H. constructor; wsame_rw Hw Hd; wexact.
Qed.

Lemma grx_core : forall I ops, agree_core I ops X -> agree_core I ops Y.
Proof.
  intros I ops H. pose proof (HF : wsame X Y grx_rs) as Hw.
  destruct H as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  pose proof (d3_ops _ _ Hq) as Ho.
  constructor.
  - exact Himg.
  - exact (eq_trans (wsame_len X Y grx_rs Hw) Hlen).
  - exact (grx_cfg Hcfg).
  - exact (grx_io I Hio).
  - exact (grx_st Hst).
  - exact (grx_fly Hfly).
  - exact (grx_time ops Htime).
  - exact (agree_q_frame ops ops X Y grx_rs Hq ltac:(lia) Hw ltac:(vm_compute; reflexivity)).
  - exact (grx_misc I Hmisc).
Qed.

Lemma grx_ka : c2_keepalive X -> c2_keepalive Y.
Proof.
  intros H. pose proof (HF : wsame X Y grx_rs) as Hw. pose proof grx_foot_disj as Hd.
  unfold c2_keepalive in *. wsame_rw Hw Hd. exact H.
Qed.

Lemma grx_drain : forall ops, agree_q ops X -> drain_fact X -> drain_fact Y.
Proof.
  intros ops HQ HD. pose proof (HF : wsame X Y grx_rs) as Hw. pose proof grx_foot_disj as Hd.
  pose proof grx_q_disj as Hdq.
  unfold drain_fact, drain_allow in *. wsame_rw Hw Hd.
  intros Hr Hs Hf Hb i Hi.
  pose proof (d1_nq _ _ HQ Hr) as Hnq. destruct (d1_entry _ _ HQ Hr i Hi) as [Hqi _].
  pose proof (d3_ncmd _ _ HQ) as Hn3. pose proof (d3_ops _ _ HQ) as Hops.
  unfold QUEUE_MAX, OPS_MAX in *.
  rewrite (wq_Q_at X Y grx_rs Hw Hdq i ltac:(lia)).
  rewrite (wq_Cmd_display X Y grx_rs Hw Hdq (Q_at X i) ltac:(lia)).
  exact (HD Hr Hs Hf Hb i Hi).
Qed.

End Grx.

(* the poll's writes are among them *)
Lemma grx_poll : forall X Y, wframe (in_rs R_poll) X Y -> wframe (in_rs grx_rs) X Y.
Proof. intros X Y H. apply (wframe_rs_incl R_poll grx_rs); [vm_compute; reflexivity | exact H]. Qed.

(* ---- diginet_session_deadline reads only g_s (DS:476-503) ---- *)

Lemma rxop_display_frame : forall X Y, (forall i, 0 <= i < S_queue_N -> S_queue_display Y i = S_queue_display X i) ->
  forall fuel i d, 0 <= i -> deadline_display_only_m Y i d fuel = deadline_display_only_m X i d fuel.
Proof.
  intros X Y H fuel. induction fuel as [|f IH]; intros i d Hi; cbn [deadline_display_only_m]; [reflexivity|].
  destruct (d =? 0); [reflexivity|].
  destruct (Z.leb_spec S_queue_N i) as [E|E]; [reflexivity|].
  rewrite (H i (conj Hi E)). apply (IH (i + 1) (S_queue_display X i)). lia.
Qed.

Lemma rxop_deadline_frame : forall (R : Z -> Prop) X Y now, wframe R X Y ->
  (forall a, OFF_g_s <= a < OFF_g_s + SZ_g_s -> ~ R a) ->
  diginet_session_deadline_m Y now = diginet_session_deadline_m X now.
Proof.
  intros R X Y now H HR.
  assert (E1 : S_state Y = S_state X) by rxop_rg H HR.
  assert (E2 : S_wake_sent_us Y = S_wake_sent_us X) by rxop_rg H HR.
  assert (E3 : S_cfg_wake_timeout_ms Y = S_cfg_wake_timeout_ms X) by rxop_rg H HR.
  assert (E4 : S_last_rx_us Y = S_last_rx_us X) by rxop_rg H HR.
  assert (E5 : S_cfg_offline_ms Y = S_cfg_offline_ms X) by rxop_rg H HR.
  assert (E6 : S_inflight Y = S_inflight X) by rxop_rg H HR.
  assert (E7 : S_backoff_until_us Y = S_backoff_until_us X) by rxop_rg H HR.
  assert (E8 : S_next_keepalive_us Y = S_next_keepalive_us X) by rxop_rg H HR.
  assert (E9 : S_inflight_sent_us Y = S_inflight_sent_us X) by rxop_rg H HR.
  assert (E10 : S_cfg_ack_timeout_ms Y = S_cfg_ack_timeout_ms X) by rxop_rg H HR.
  assert (E11 : S_queued Y = S_queued X) by rxop_rg H HR.
  assert (E12 : S_display_sent Y = S_display_sent X) by rxop_rg H HR.
  assert (E13 : S_last_display_us Y = S_last_display_us X) by rxop_rg H HR.
  assert (E14 : S_cfg_display_gap_us Y = S_cfg_display_gap_us X) by rxop_rg H HR.
  assert (ED : forall i, 0 <= i < S_queue_N -> S_queue_display Y i = S_queue_display X i)
    by (intros i Hi; unfold S_queue_N in Hi; rxop_rg H HR).
  unfold diginet_session_deadline_m.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14.
  rewrite (rxop_display_frame X Y ED (Z.to_nat (S_queued X)) 0 1 ltac:(lia)).
  reflexivity.
Qed.

(* ---- io_recv (FT:906-929) and poll's drain loop (DS:524-526) ---- *)

Lemma rxop_int_dec : forall t, 1 <= t <= 2 -> int_dec t = Some (t - 1).
Proof.
  intros t Ht. unfold int_dec.
  destruct (Z.eqb_spec t INT_MIN) as [E|E]; [unfold INT_MIN in E; lia | reflexivity].
Qed.

(* io_recv hands the got bytes over (FT:916-928), the model taking them first: m_tick on an empty frame
   (FT:925-926), m_rx (g_rx, got) on the frame seen from g_rx = its address (FT:923-924); B2 is the model's
   world, which keeps g_rx *)
Lemma rxop_io_recv : forall I a bytes Y got t B2, length Y = WN -> g_rx_fail Y = 0 -> g_rx Y = a ->
  g_rx_times Y = t -> 1 <= t <= 2 -> g_rx_len Y = got -> 0 < a -> 0 <= got <= 1514 ->
  got <= Z.of_nat (length bytes) ->
  (if got =? 0 then m_tick_m (set_g_rx_times Y (t - 1)) = Some (B2, tt)
   else exists x, m_rx_m I (Some (TFrame a bytes)) (set_g_rx_times Y (t - 1)) got = Some (B2, x)) ->
  g_rx B2 = a ->
  io_recv_m I (Some (TFrame a bytes)) Y DIGINET_MAX_FRAME_LEN =
    Some (B2, got, if 0 <? got then rxbuf (TFrame a bytes) got else []).
Proof.
  intros I a bytes Y got t B2 HY Hf Hr Ht Ht12 Hl Ha Hg Hgl Hm Hr2.
  assert (Hr1 : g_rx (set_g_rx_times Y (t - 1)) = a) by (rewrite <- Hr; wget).
  assert (Hl1 : g_rx_len (set_g_rx_times Y (t - 1)) = got) by (rewrite <- Hl; wget).
  assert (Ef : frame_from (Some (TFrame a bytes)) a = Some (TFrame a bytes))
    by exact (frame_from_base (TFrame a bytes)).
  unfold io_recv_m. rewrite Hf. change (truth 0) with false. cbv beta iota.
  rewrite Hr, Ht.
  assert (Ea : (a =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Et : (t =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Ea, Et. cbv beta iota delta [orb].
  rewrite (rxop_int_dec t Ht12). cbv beta iota zeta.
  rewrite Hl1.
  assert (Eg : (if got <? DIGINET_MAX_FRAME_LEN then got else DIGINET_MAX_FRAME_LEN) = got)
    by (unfold DIGINET_MAX_FRAME_LEN; destruct (Z.ltb_spec got 1514); lia).
  rewrite Eg.
  rewrite (rxop_swrap got ltac:(lia)).
  destruct (Z.eqb_spec got 0) as [G|G].
  - rewrite G.
    assert (Hm' : m_tick_m (set_g_rx_times Y (t - 1)) = Some (B2, tt)) by exact Hm.
    cbv beta iota. rewrite Hm'. cbv beta iota.
    unfold frame_read. reflexivity.
  - destruct Hm as (x & Hm). rewrite Hr1, Ef, Hm. cbv beta iota.
    rewrite Hr2. unfold frame_read. rewrite (proj2 (Z.eqb_neq got 0) G).
    cbv beta iota zeta. cbn [tf_addr tf_bytes]. rewrite (Z.sub_diag a).
    destruct (Z.ltb_spec 0 0) as [L1|L1]; [lia|].
    destruct (Z.ltb_spec got 0) as [L2|L2]; [lia|].
    destruct (Z.ltb_spec (Z.of_nat (length bytes)) (0 + got)) as [L3|L3]; [lia|].
    cbv beta iota delta [orb]. rewrite (rxop_sub0 bytes (Z.to_nat got)). reflexivity.
Qed.

Lemma rxop_drain_idle : forall I F X fuel, S_io_recv X = ti_io_recv I -> g_rx_fail X = 0 -> g_rx_times X = 0 ->
  poll_drain_m I F X fuel = Some (X, 0).
Proof.
  intros I F X fuel Hr Hf Ht.
  assert (E : call_recv I F X DIGINET_MAX_FRAME_LEN = Some (X, 0, [])).
  { unfold call_recv. rewrite Hr, (Z.eqb_refl (ti_io_recv I)). cbv beta iota.
    unfold io_recv_m. rewrite Hf, Ht. change (truth 0) with false. cbv beta iota.
    destruct (g_rx X =? 0); reflexivity. }
  destruct fuel as [|f]; cbn [poll_drain_m]; rewrite E; reflexivity.
Qed.

(* one turn of the drain loop (DS:524-525) that hands a frame over *)
Lemma rxop_drain_step : forall I F X f Y n bs now Y' r, call_recv I F X DIGINET_MAX_FRAME_LEN = Some (Y, n, bs) ->
  0 < n -> call_now I Y = Some now -> diginet_session_rx_m I F Y bs now = Some (Y', r) ->
  poll_drain_m I F X (S f) = poll_drain_m I F Y' f.
Proof.
  intros I F X f Y n bs now Y' r Hr Hn Hc Hx. cbn [poll_drain_m]. rewrite Hr. cbv beta iota.
  rewrite (proj2 (Z.ltb_lt 0 n) Hn). cbv beta iota. rewrite Hc. cbv beta iota. rewrite Hx. cbv beta iota.
  reflexivity.
Qed.
(* ---- the prologue: op_begin (FT:1001) and g_rx_send (FT:1002-1003, :1007-1008) ---- *)

Lemma rxop_pre : forall I ops X v buf, agree_core I ops X -> c2_keepalive X -> ow_zero X -> M_fail X = g_fail_next X ->
  0 <= v < 2 ^ 32 -> (fr_code buf = DIGINET_OK -> v = fr_send buf) -> rx_pre I ops (set_g_rx_send X v) buf.
Proof.
  intros I ops X v buf Hc Hk Hz Hm Hv Hs.
  pose proof (ac_len _ _ _ Hc) as HX.
  assert (HF : wframe (in_rs grx_rs) X (set_g_rx_send X v)) by wfrs.
  constructor.
  - exact (grx_core _ _ HF I ops Hc).
  - exact (grx_ka _ _ HF Hk).
  - exact (ow_zero_fr grx_rs X _ HF ltac:(vm_compute; reflexivity) Hz).
  - assert (E1 : M_fail (set_g_rx_send X v) = M_fail X) by fget HF.
    assert (E2 : g_fail_next (set_g_rx_send X v) = g_fail_next X) by fget HF.
    rewrite E1, E2. exact Hm.
  - intros Hcode. rewrite <- (Hs Hcode).
    assert (Hv' : 0 <= v < 4294967296) by exact Hv. clear Hs Hv. wget.
Qed.

(* the second write of g_rx_send (FT:1007-1008) *)
Lemma rxop_pre_again : forall I ops X buf0 buf, rx_pre I ops X buf0 -> rx_pre I ops (set_g_rx_send X (rxop_v buf)) buf.
Proof.
  intros I ops X buf0 buf Hp.
  apply rxop_pre; [exact (rp_core _ _ _ _ Hp) | exact (rp_ka _ _ _ _ Hp) | exact (rp_zero _ _ _ _ Hp)
                  | exact (rp_fail _ _ _ _ Hp) | exact (proj1 (rxop_v_ok buf)) | exact (proj2 (rxop_v_ok buf))].
Qed.

Lemma rxop_begin : forall I ops B bytes, agree I ops B ->
  exists B1, op_begin_m B = Some (B1, tt) /\ rx_pre I ops (set_g_rx_send B1 (rxop_v bytes)) bytes /\
    g_rx (set_g_rx_send B1 (rxop_v bytes)) = 0.
Proof.
  intros I ops B bytes [Hcore Hka Hrx0].
  pose proof (ac_len _ _ _ Hcore) as HB.
  destruct (op_begin_stage B HB) as (B1 & Eob & _ & Hz1 & Hm1).
  pose proof (op_begin_frame B B1 Eob HB) as Hw1.
  assert (Hd1 : forall x, in_ranges foot_corem x -> ~ in_ranges [(OFF_OW, SZ_OW); (OFF_GOT, SZ_GOT); (A_M_fail, 4)] x)
    by (apply rdisj_spec; vm_compute; reflexivity).
  pose proof (agree_core_op_begin I ops B B1 Hcore Eob) as Hc1.
  pose proof (ac_len _ _ _ Hc1) as HB1.
  pose proof (c2_keepalive_frame B B1 _ Hw1 Hd1 Hka) as Hk1.
  pose proof (g_rx_frame B B1 _ Hw1 Hd1 Hrx0) as Hr1.
  assert (Hg1 : g_fail_next B1 = g_fail_next B)
    by exact (wsame_u_at B B1 _ OFF_g_fail_next 1 Hw1 ltac:(unfold OFF_g_fail_next; lia) ltac:(vm_compute; reflexivity)).
  assert (Hz1' : ow_zero B1).
  { destruct Hz1 as (z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & z15 & z16).
    exact (Build_ow_zero B1 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16). }
  exists B1. split; [exact Eob|]. split.
  - apply rxop_pre; [exact Hc1 | exact Hk1 | exact Hz1' | | exact (proj1 (rxop_v_ok bytes))
                    | exact (proj2 (rxop_v_ok bytes))].
    rewrite Hm1, Hg1. reflexivity.
  - transitivity (g_rx B1); [wget | exact Hr1].
Qed.

(* ---- receive (p, n, 0, 0), FT:1020-1023 ---- *)

Definition rxop_tailrx (I : timg) (a : Z) (bytes : list byte) (B2 : list byte) : option (list byte * unit) :=
  let? (B3, ticked) :=
    (let? (Bx, ticked) := m_rx_m I (Some (TFrame a bytes)) B2 (Z.of_nat (length bytes)) in
     let? (By, _) := diginet_session_rx_m I (Some (TFrame a bytes)) Bx bytes (g_now Bx) in
     Some (By, ticked)) in
  let? (B4, _) := settle_m B3 ticked in
  Some (B4, tt).

Lemma rxop_receive0_eq : forall I B a bytes, 0 < a ->
  receive_m I B a bytes 0 0 = let? (B1, _) := op_begin_m B in rxop_tailrx I a bytes (set_g_rx_send B1 (rxop_v bytes)).
Proof.
  intros I B a bytes Ha. unfold receive_m, fuzz_dup_m, fuzz_alloc_m.
  destruct (Z.eqb_spec a 0) as [E|E]; [lia|].
  unfold rxop_tailrx, rxop_v. reflexivity.
Qed.

Lemma rxop_tailrx_ok : forall (Hrx : rx_ok_stmt) I ops B2 a bytes,
  rx_pre I ops B2 bytes -> g_rx B2 = 0 -> 0 <= ops < OPS_MAX -> 0 < a -> a + Z.of_nat (length bytes) < 2 ^ 64 ->
  exists B4, rxop_tailrx I a bytes B2 = Some (B4, tt) /\ agree I (ops + 1) B4.
Proof.
  intros Hrx I ops B2 a bytes Hpre Hr0 Hops Ha0 Ha1.
  assert (Hpre' : rx_pre I ops B2 (rxbuf (TFrame a bytes) (Z.of_nat (length bytes))))
    by (rewrite (rxbuf_all a bytes); exact Hpre).
  destruct (Hrx I ops (TFrame a bytes) (Z.of_nat (length bytes)) B2 ltac:(cbn [tf_bytes]; lia)
              ltac:(cbn [tf_addr tf_bytes]; lia) Hpre') as (Bx & t & Em & Et & Hf & Hl).
  destruct (Hl Bx (wframe_refl _ _)) as (W' & r & Es & Hd).
  rewrite (rxbuf_all a bytes) in Es.
  assert (Nx : g_now Bx = g_now B2) by fget Hf.
  assert (Rx : g_rx Bx = g_rx B2) by fget Hf.
  pose proof (rxop_m_rx_01 _ _ _ _ _ _ Em) as Ht01.
  pose proof (rd_core _ _ _ _ _ Hd) as Hc'.
  pose proof (rd_ka _ _ _ _ _ Hd) as Hk'.
  assert (Hs : settle_m W' t = Some (W', tt)).
  { apply (settle_ok I ops W' t Hc' Hk' (rxop_og_settle _ (rd_og _ _ _ _ _ Hd))).
    intros Ht. destruct Ht01 as [E|E].
    - subst t. cbv in Ht. discriminate Ht.
    - exact (rd_drain _ _ _ _ _ Hd E). }
  exists W'. split.
  - unfold rxop_tailrx. rewrite Em. cbv beta iota. rewrite Nx, Es. cbv beta iota. rewrite Hs. reflexivity.
  - constructor.
    + exact (agree_core_mono I ops (ops + 1) W' Hc' ltac:(unfold OPS_MAX in *; lia)).
    + exact Hk'.
    + rewrite (rd_rx _ _ _ _ _ Hd), Rx. exact Hr0.
Qed.

Lemma rxop_receive0 : forall (Hrx : rx_ok_stmt) I ops B a bytes,
  agree I ops B -> 0 <= ops < OPS_MAX -> 0 < a -> a + Z.of_nat (length bytes) < 2 ^ 64 ->
  exists B', receive_m I B a bytes 0 0 = Some (B', tt) /\ agree I (ops + 1) B'.
Proof.
  intros Hrx I ops B a bytes HA Hops Ha0 Ha1.
  destruct (rxop_begin I ops B bytes HA) as (B1 & Eob & Hpre & Hr0).
  destruct (rxop_tailrx_ok Hrx I ops _ a bytes Hpre Hr0 Hops Ha0 Ha1) as (B4 & E4 & HA4).
  exists B4. split; [|exact HA4].
  rewrite (rxop_receive0_eq I B a bytes Ha0), Eob. cbv beta iota. exact E4.
Qed.

(* ---- receive (p, n, 1, flags), FT:1004-1018 ---- *)

(* the receive from the poll's prologue on (FT:1012-1023): g_rx = the frame, g_rx_len = got, g_rx_times = times
   (1, or 2 with flags bit 0), g_rx_fail = fails (flags bit 1) *)
Definition rxop_tail8 (I : timg) (a : Z) (bytes : list byte) (got times fails : Z) (B2a : list byte)
    : option (list byte * unit) :=
  let? (B3, ticked) :=
    (let? (B2d, _) := diginet_session_poll_m I (Some (TFrame a bytes))
                        (set_g_rx_fail (set_g_rx_times (set_g_rx_len (set_g_rx B2a a) got) times) fails) 0 in
     Some (set_g_rx_fail (set_g_rx B2d 0) 0, if fails =? 0 then 1 else 0)) in
  let? (B4, _) := settle_m B3 ticked in
  Some (B4, tt).

Lemma rxop_receive8_eq : forall I B a bytes pf, 0 < a ->
  receive_m I B a bytes 1 pf =
  let? (B1, _) := op_begin_m B in
  rxop_tail8 I a bytes (rxop_got bytes) (if Z.land pf 1 =? 0 then 1 else 2) (Z.land (Z.shiftr pf 1) 1)
    (set_g_rx_send (set_g_rx_send B1 (rxop_v bytes)) (rxop_v (rxbuf (TFrame a bytes) (rxop_got bytes)))).
Proof.
  intros I B a bytes pf Ha. unfold receive_m, fuzz_dup_m, fuzz_alloc_m.
  destruct (Z.eqb_spec a 0) as [E|E]; [lia|].
  unfold rxop_tail8, rxop_got, rxop_v, rxbuf. reflexivity.
Qed.

Lemma rxop_io_nz : forall I ops X, agree_core I ops X ->
  (S_io_recv X =? 0) = false /\ (S_io_now_us X =? 0) = false.
Proof.
  intros I ops X Hc. pose proof (ac_img _ _ _ Hc) as Hi. pose proof (ac_io _ _ _ Hc) as Ho.
  rewrite (a3_io_recv _ _ Ho), (a3_io_now _ _ Ho).
  pose proof (ti_io_recv_ok _ Hi). pose proof (ti_io_now_ok _ Hi).
  split; apply Z.eqb_neq; lia.
Qed.

(* the poll's writes of the receive's scalars (R_poll: g_rx_fail, g_rx_times, g_rx, g_rx_len) keep rx_pre and
   rx_pre_g *)
Lemma rxop_pre_poll : forall I ops X Y buf, rx_pre I ops X buf -> wframe (in_rs R_poll) X Y -> rx_pre I ops Y buf.
Proof.
  intros I ops X Y buf Hp HF.
  pose proof (grx_poll _ _ HF) as HG.
  assert (E1 : M_fail Y = M_fail X) by fget HF.
  assert (E2 : g_fail_next Y = g_fail_next X) by fget HF.
  assert (E3 : g_rx_send Y = g_rx_send X) by fget HF.
  constructor.
  - exact (grx_core _ _ HG I ops (rp_core _ _ _ _ Hp)).
  - exact (grx_ka _ _ HG (rp_ka _ _ _ _ Hp)).
  - exact (ow_zero_fr R_poll X Y HF ltac:(vm_compute; reflexivity) (rp_zero _ _ _ _ Hp)).
  - rewrite E1, E2. exact (rp_fail _ _ _ _ Hp).
  - intros Hc. rewrite E3. exact (rp_rx_send _ _ _ _ Hp Hc).
Qed.

Lemma rxop_pre_g_poll : forall I ops X Y buf, rx_pre_g I ops X buf -> wframe (in_rs R_poll) X Y ->
  rx_pre_g I ops Y buf.
Proof.
  intros I ops X Y buf Hp HF.
  pose proof (grx_poll _ _ HF) as HG.
  assert (E1 : M_desk_known Y = M_desk_known X) by fget HF.
  assert (E2 : M_desk Y = M_desk X) by fget HF.
  assert (E3 : M_state Y = M_state X) by fget HF.
  assert (E4 : M_fail Y = M_fail X) by fget HF.
  assert (E5 : g_fail_next Y = g_fail_next X) by fget HF.
  assert (E6 : g_rx_send Y = g_rx_send X) by fget HF.
  constructor.
  - exact (grx_core _ _ HG I ops (rg_core _ _ _ _ Hp)).
  - exact (grx_ka _ _ HG (rg_ka _ _ _ _ Hp)).
  - exact (ow_room_fr R_poll X Y HF ltac:(vm_compute; reflexivity) (rg_room _ _ _ _ Hp)).
  - intros Ha Hw. rewrite E4, E5.
    exact (rg_fail _ _ _ _ Hp (rx_accepts_same Y X buf Ha (eq_sym E1) (eq_sym E2) (eq_sym E3)) Hw).
  - intros Hc. rewrite E6. exact (rg_rx_send _ _ _ _ Hp Hc).
Qed.

(* the poll when io_recv fails (FT:910-913; DS:517-518), whatever g_rx_times *)
Lemma rxop_poll_fail : forall I ops a bytes got times B2a,
  0 < a -> a + Z.of_nat (length bytes) < 2 ^ 64 -> 0 <= got <= 1514 -> agree_core I ops B2a ->
  diginet_session_poll_m I (Some (TFrame a bytes))
      (set_g_rx_fail (set_g_rx_times (set_g_rx_len (set_g_rx B2a a) got) times) 1) 0 =
    Some (set_g_rx_fail (set_g_rx_fail (set_g_rx_times (set_g_rx_len (set_g_rx B2a a) got) times) 1) 0, - EIO).
Proof.
  intros I ops a bytes got times B2a Ha0 Ha1 Hg Hc.
  assert (HBa : length B2a = WN) by exact (ac_len _ _ _ Hc).
  pose proof (ac_io _ _ _ Hc) as Hio.
  destruct (rxop_io_nz I ops B2a Hc) as [Z1 Z2].
  set (B2c := set_g_rx_fail (set_g_rx_times (set_g_rx_len (set_g_rx B2a a) got) times) 1).
  assert (HfP : wframe (in_rs R_poll) B2a B2c) by (unfold B2c; wfrs).
  assert (Cf : g_rx_fail B2c = 1) by (unfold B2c; wget).
  assert (Nc : g_now B2c = g_now B2a) by fget HfP.
  assert (Ic : S_io_recv B2c = S_io_recv B2a) by fget HfP.
  assert (Jc : S_io_now_us B2c = S_io_now_us B2a) by fget HfP.
  destruct (deadline_ok I ops B2a Hc) as (d & Ed & _).
  assert (Dc : diginet_session_deadline_m B2c (g_now B2a) = Some d).
  { rewrite <- Ed. apply (rxop_deadline_frame (in_rs R_poll) B2a B2c _ HfP).
    intros x Hx. apply (disj_rs_ok OFF_g_s SZ_g_s R_poll); [vm_compute; reflexivity | exact Hx]. }
  assert (Pnc : call_now I B2c = Some (g_now B2a)).
  { unfold call_now. rewrite Jc, (a3_io_now _ _ Hio), (Z.eqb_refl (ti_io_now I)). cbv beta iota.
    unfold io_now_m. rewrite Nc. reflexivity. }
  assert (Er : call_recv I (Some (TFrame a bytes)) B2c DIGINET_MAX_FRAME_LEN = Some (set_g_rx_fail B2c 0, - EIO, [])).
  { unfold call_recv. rewrite Ic, (a3_io_recv _ _ Hio), (Z.eqb_refl (ti_io_recv I)). cbv beta iota.
    unfold io_recv_m. rewrite Cf. reflexivity. }
  unfold diginet_session_poll_m.
  rewrite Ic, Jc, Z1, Z2. cbv beta iota delta [orb].
  rewrite Pnc. cbv beta iota.
  rewrite Dc. cbv beta iota zeta.
  rewrite Er. cbv beta iota.
  reflexivity.
Qed.

Lemma rxop_tail_fail_ok : forall I ops B2a a bytes got times buf,
  rx_pre I ops B2a buf -> 0 <= ops < OPS_MAX -> 0 < a -> a + Z.of_nat (length bytes) < 2 ^ 64 -> 0 <= got <= 1514 ->
  exists B4, rxop_tail8 I a bytes got times 1 B2a = Some (B4, tt) /\ agree I (ops + 1) B4.
Proof.
  intros I ops B2a a bytes got times buf Hpre Hops Ha0 Ha1 Hg.
  pose proof (rp_core _ _ _ _ Hpre) as Hc.
  pose proof (ac_len _ _ _ Hc) as HBa.
  assert (Ha64 : a < 18446744073709551616) by lia.
  assert (HwF : wframe (in_rs grx_rs) B2a
    (set_g_rx_fail (set_g_rx (set_g_rx_fail (set_g_rx_fail (set_g_rx_times (set_g_rx_len (set_g_rx B2a a) got) times)
       1) 0) 0) 0)) by wfrs.
  pose proof (grx_core _ _ HwF I ops Hc) as Hcf.
  pose proof (grx_ka _ _ HwF (rp_ka _ _ _ _ Hpre)) as Hkf.
  assert (HRo : forall x, OFF_GOT <= x < OFF_OW + SZ_OW -> ~ in_rs grx_rs x).
  { intros x Hx. apply (disj_rs_ok OFF_GOT (OFF_OW + SZ_OW - OFF_GOT) grx_rs); [vm_compute; reflexivity | lia]. }
  pose proof (rxop_og_frame _ _ _ HwF HRo (ow_got_eq_zero _ (rp_zero _ _ _ _ Hpre))) as Hof.
  assert (Hs : settle_m
    (set_g_rx_fail (set_g_rx (set_g_rx_fail (set_g_rx_fail (set_g_rx_times (set_g_rx_len (set_g_rx B2a a) got) times)
       1) 0) 0) 0) 0 =
    Some (set_g_rx_fail (set_g_rx (set_g_rx_fail (set_g_rx_fail (set_g_rx_times (set_g_rx_len (set_g_rx B2a a) got)
       times) 1) 0) 0) 0, tt)).
  { apply (settle_ok I ops _ 0 Hcf Hkf (rxop_og_settle _ Hof)). intros Ht. cbv in Ht. discriminate Ht. }
  eexists. split.
  - unfold rxop_tail8. rewrite (rxop_poll_fail I ops a bytes got times B2a Ha0 Ha1 Hg Hc). cbv beta iota.
    change (if 1 =? 0 then 1 else 0) with 0. rewrite Hs. reflexivity.
  - constructor.
    + exact (agree_core_mono I ops (ops + 1) _ Hcf ltac:(unfold OPS_MAX in *; lia)).
    + exact Hkf.
    + wget.
Qed.

(* the poll when io_recv hands the frame over (FT:1012-1016, DS:505-527), once (times = 1) or twice
   (times = 2): each hand-over runs the model first (rxop_io_recv), then the library's rx; the poll's tick runs
   after the first *)
Lemma rxop_poll_ok : forall (HL : links) (Hrx : rx_ok_g_stmt) I ops a bytes got times B2a,
  0 < a -> a + Z.of_nat (length bytes) < 2 ^ 64 -> 0 <= got <= 1514 -> got <= Z.of_nat (length bytes) ->
  (times = 1 \/ times = 2) -> rx_pre I ops B2a (rxbuf (TFrame a bytes) got) ->
  exists Wd, diginet_session_poll_m I (Some (TFrame a bytes))
      (set_g_rx_fail (set_g_rx_times (set_g_rx_len (set_g_rx B2a a) got) times) 0) 0 = Some (Wd, 0) /\
    agree_core I ops Wd /\ c2_keepalive Wd /\ ow_got_eq Wd /\ drain_fact Wd.
Proof.
  intros HL Hrx I ops a bytes got times B2a Ha0 Ha1 Hg Hgl Htm Hpre.
  assert (Ht12 : 1 <= times <= 2) by (destruct Htm; lia).
  pose proof (rp_core _ _ _ _ Hpre) as Hc.
  assert (HBa : length B2a = WN) by exact (ac_len _ _ _ Hc).
  pose proof (ac_io _ _ _ Hc) as Hio.
  destruct (rxop_io_nz I ops B2a Hc) as [Z1 Z2].
  assert (Ha64 : a < 18446744073709551616) by lia.
  set (B2c := set_g_rx_fail (set_g_rx_times (set_g_rx_len (set_g_rx B2a a) got) times) 0).
  assert (HBc : length B2c = WN) by (unfold B2c; wlen).
  assert (HfP : wframe (in_rs R_poll) B2a B2c) by (unfold B2c; wfrs).
  assert (Cf : g_rx_fail B2c = 0) by (unfold B2c; wget).
  assert (Cr : g_rx B2c = a) by (unfold B2c; wget).
  assert (Ct : g_rx_times B2c = times) by (unfold B2c; wget).
  assert (Cl : g_rx_len B2c = got) by (unfold B2c; wget).
  assert (Nc : g_now B2c = g_now B2a) by fget HfP.
  assert (Ic : S_io_recv B2c = S_io_recv B2a) by fget HfP.
  assert (Jc : S_io_now_us B2c = S_io_now_us B2a) by fget HfP.
  destruct (deadline_ok I ops B2a Hc) as (d & Ed & _).
  assert (Dc : diginet_session_deadline_m B2c (g_now B2a) = Some d).
  { rewrite <- Ed. apply (rxop_deadline_frame (in_rs R_poll) B2a B2c _ HfP).
    intros x Hx. apply (disj_rs_ok OFF_g_s SZ_g_s R_poll); [vm_compute; reflexivity | exact Hx]. }
  assert (Pnc : call_now I B2c = Some (g_now B2a)).
  { unfold call_now. rewrite Jc, (a3_io_now _ _ Hio), (Z.eqb_refl (ti_io_now I)). cbv beta iota.
    unfold io_now_m. rewrite Nc. reflexivity. }
  (* the world of the first hand-over (FT:916: g_rx_times decremented) *)
  set (Y1 := set_g_rx_times B2c (times - 1)).
  assert (HY1 : wframe (in_rs R_poll) B2a Y1) by (unfold Y1, B2c; wfrs).
  pose proof (rxop_pre_poll I ops B2a Y1 _ Hpre HY1) as Hpre1.
  pose proof (rp_core _ _ _ _ Hpre1) as Hc1.
  assert (R1 : g_rx Y1 = a) by (transitivity (g_rx B2c); [unfold Y1; wget | exact Cr]).
  assert (F1 : g_rx_fail Y1 = 0) by (transitivity (g_rx_fail B2c); [unfold Y1; wget | exact Cf]).
  assert (T1 : g_rx_times Y1 = times - 1) by (unfold Y1; wget).
  assert (L1 : g_rx_len Y1 = got) by (transitivity (g_rx_len B2c); [unfold Y1; wget | exact Cl]).
  assert (I1 : S_io_now_us Y1 = S_io_now_us B2a) by fget HY1.
  (* a tick's writes miss the receive's scalars, g_rx_send, OW and GOT (TickDefs.v R_tick) *)
  assert (HRt : forall x, OFF_g_rx_send <= x < OFF_g_cfg -> ~ R_tick x)
    by (intros x Hx; unfold R_tick; revert Hx; wunf_off; intros; lia).
  assert (HRo : forall x, OFF_GOT <= x < OFF_OW + SZ_OW -> ~ R_tick x)
    by (intros x Hx; unfold R_tick; revert Hx; wunf_off; intros; lia).
  unfold diginet_session_poll_m.
  rewrite Ic, Jc, Z1, Z2. cbv beta iota delta [orb].
  rewrite Pnc. cbv beta iota.
  rewrite Dc. cbv beta iota zeta.
  destruct (Z.eqb_spec got 0) as [G0|G0].
  - (* an empty frame: io_recv runs m_tick (FT:925-926) and hands nothing over; then the poll's tick *)
    assert (Tq1 : m_tick_m Y1 = Some (Y1, tt)) by exact (rxop_tick_quiet I ops Y1 Hc1).
    assert (Er : call_recv I (Some (TFrame a bytes)) B2c DIGINET_MAX_FRAME_LEN = Some (Y1, 0, [])).
    { unfold call_recv. rewrite Ic, (a3_io_recv _ _ Hio), (Z.eqb_refl (ti_io_recv I)). cbv beta iota.
      exact (rxop_io_recv I a bytes B2c 0 times Y1 HBc Cf Cr Ct Ht12 ltac:(rewrite Cl; exact G0) Ha0
               ltac:(lia) ltac:(lia) Tq1 R1). }
    rewrite Er. cbv beta iota.
    change (0 <? 0) with false. cbv beta iota.
    assert (Pn1 : call_now I Y1 = Some (g_now Y1)).
    { unfold call_now. rewrite I1, (a3_io_now _ _ Hio), (Z.eqb_refl (ti_io_now I)). cbv beta iota.
      unfold io_now_m. reflexivity. }
    rewrite Pn1. cbv beta iota.
    destruct (tick_quiet_keep HL I (Some (TFrame a bytes)) ops Y1 Hc1) as (W2 & r2 & Etk & Htp & _).
    rewrite Etk. cbv beta iota.
    pose proof (tp_frame _ _ _ _ Htp) as HfT.
    pose proof (tp_core _ _ _ _ Htp) as Hc2.
    assert (HW2n : length W2 = WN) by exact (ac_len _ _ _ Hc2).
    assert (T2 : g_rx_times W2 = times - 1) by (rewrite <- T1; rxop_rg HfT HRt).
    assert (F2 : g_rx_fail W2 = 0) by (transitivity (g_rx_fail Y1); [rxop_rg HfT HRt | exact F1]).
    assert (R2 : g_rx W2 = a) by (transitivity (g_rx Y1); [rxop_rg HfT HRt | exact R1]).
    assert (L2 : g_rx_len W2 = 0) by (transitivity (g_rx_len Y1); [rxop_rg HfT HRt | rewrite L1; exact G0]).
    assert (Ti2 : S_io_recv W2 = ti_io_recv I) by exact (a3_io_recv _ _ (ac_io _ _ _ Hc2)).
    assert (Og2 : ow_got_eq W2)
      by exact (ow_got_eq_frR R_tick Y1 W2 HfT HRo (ow_got_eq_zero _ (rp_zero _ _ _ _ Hpre1))).
    rewrite T2.
    destruct Htm as [Et|Et]; subst times.
    + (* one hand-over: the drain loop ends at once (g_rx_times = 0) *)
      rewrite (rxop_drain_idle I (Some (TFrame a bytes)) W2 _ Ti2 F2 T2).
      exists W2. exact (conj eq_refl (conj Hc2 (conj (tp_keepalive _ _ _ _ Htp) (conj Og2 (tp_drain _ _ _ _ Htp))))).
    + (* two: the second hand-over of the empty frame runs m_tick again, and the loop ends (DS:524, :526) *)
      set (Y2 := set_g_rx_times W2 0).
      assert (HY2 : wframe (in_rs R_poll) W2 Y2) by (unfold Y2; wfrs).
      pose proof (grx_poll _ _ HY2) as HG2.
      assert (Hc3 : agree_core I ops Y2) by exact (grx_core _ _ HG2 I ops Hc2).
      assert (R3 : g_rx Y2 = a) by (transitivity (g_rx W2); [unfold Y2; wget | exact R2]).
      assert (Er2 : call_recv I (Some (TFrame a bytes)) W2 DIGINET_MAX_FRAME_LEN = Some (Y2, 0, [])).
      { unfold call_recv. rewrite Ti2, (Z.eqb_refl (ti_io_recv I)). cbv beta iota.
        exact (rxop_io_recv I a bytes W2 0 1 Y2 HW2n F2 R2 T2 ltac:(lia) L2 Ha0 ltac:(lia) ltac:(lia)
                 (rxop_tick_quiet I ops Y2 Hc3) R3). }
      change (Z.to_nat (2 - 1)) with (S O).
      cbn [poll_drain_m]. rewrite Er2. cbv beta iota.
      change (0 <? 0) with false. cbv beta iota.
      exists Y2. split; [reflexivity|].
      split; [exact Hc3|]. split; [exact (grx_ka _ _ HG2 (tp_keepalive _ _ _ _ Htp))|].
      split; [exact (ow_got_eq_fr R_poll W2 Y2 HY2 ltac:(vm_compute; reflexivity) Og2)|].
      exact (grx_drain _ _ HG2 ops (ac_q _ _ _ Hc2) (tp_drain _ _ _ _ Htp)).
  - (* the first hand-over: m_rx (FT:923-924), the library's rx (DS:521), the poll's tick (DS:522) *)
    destruct (Hrx I ops (TFrame a bytes) got Y1 ltac:(cbn [tf_bytes]; lia) ltac:(cbn [tf_addr tf_bytes]; lia)
                (rx_pre_g_of _ _ _ _ Hpre1)) as (Bx & t1 & Em & _ & Hf & Hl).
    destruct (Hl Bx (wframe_refl _ _)) as (W1 & r1 & Es & Hd).
    pose proof (rk_done _ _ _ _ _ _ _ Hd) as Hd0.
    assert (Rx : g_rx Bx = a) by (transitivity (g_rx Y1); [fget Hf | exact R1]).
    assert (Er : call_recv I (Some (TFrame a bytes)) B2c DIGINET_MAX_FRAME_LEN =
                 Some (Bx, got, rxbuf (TFrame a bytes) got)).
    { unfold call_recv. rewrite Ic, (a3_io_recv _ _ Hio), (Z.eqb_refl (ti_io_recv I)). cbv beta iota.
      rewrite (rxop_io_recv I a bytes B2c got times Bx HBc Cf Cr Ct Ht12 Cl Ha0 Hg Hgl).
      - destruct (Z.ltb_spec 0 got); [reflexivity | lia].
      - destruct (Z.eqb_spec got 0) as [E|E]; [lia|]. cbv beta iota. exists t1. exact Em.
      - exact Rx. }
    assert (Ng : (got <? 0) = false) by (apply Z.ltb_ge; lia).
    assert (Pg : (0 <? got) = true) by (apply Z.ltb_lt; lia).
    assert (Nx : g_now Bx = g_now Y1) by fget Hf.
    assert (Pnx : call_now I Bx = Some (g_now Y1)).
    { unfold call_now. assert (Jx : S_io_now_us Bx = S_io_now_us B2a) by (rewrite <- I1; fget Hf).
      rewrite Jx, (a3_io_now _ _ Hio), (Z.eqb_refl (ti_io_now I)). cbv beta iota.
      unfold io_now_m. rewrite Nx. reflexivity. }
    pose proof (rd_core _ _ _ _ _ Hd0) as Hc1'.
    destruct (tick_quiet_keep HL I (Some (TFrame a bytes)) ops W1 Hc1') as (W2 & r2 & Etk & Htp & K1 & K2 & K3).
    assert (Nw1 : g_now W1 = g_now Y1) by (rewrite (rd_now _ _ _ _ _ Hd0); exact Nx).
    pose proof (tp_frame _ _ _ _ Htp) as HfT.
    pose proof (tp_core _ _ _ _ Htp) as Hc2.
    assert (HW2n : length W2 = WN) by exact (ac_len _ _ _ Hc2).
    assert (T2 : g_rx_times W2 = times - 1).
    { rewrite <- T1. transitivity (g_rx_times W1); [rxop_rg HfT HRt|].
      rewrite (rd_rx_times _ _ _ _ _ Hd0). fget Hf. }
    assert (F2 : g_rx_fail W2 = 0).
    { transitivity (g_rx_fail W1); [rxop_rg HfT HRt|].
      rewrite (rd_rx_fail _ _ _ _ _ Hd0). transitivity (g_rx_fail Y1); [fget Hf | exact F1]. }
    assert (R2 : g_rx W2 = a).
    { transitivity (g_rx W1); [rxop_rg HfT HRt|]. rewrite (rd_rx _ _ _ _ _ Hd0). exact Rx. }
    assert (L2 : g_rx_len W2 = got).
    { transitivity (g_rx_len W1); [rxop_rg HfT HRt|].
      rewrite (rd_rx_len _ _ _ _ _ Hd0). transitivity (g_rx_len Y1); [fget Hf | exact L1]. }
    assert (Ti2 : S_io_recv W2 = ti_io_recv I) by exact (a3_io_recv _ _ (ac_io _ _ _ Hc2)).
    assert (Og2 : ow_got_eq W2) by exact (ow_got_eq_frR R_tick W1 W2 HfT HRo (rd_og _ _ _ _ _ Hd0)).
    rewrite Er. cbv beta iota.
    rewrite Ng. cbv beta iota.
    rewrite Pnx. cbv beta iota.
    rewrite Pg. cbv beta iota.
    rewrite Es. cbv beta iota.
    rewrite <- Nw1, Etk. cbv beta iota.
    rewrite T2.
    destruct Htm as [Et|Et]; subst times.
    + (* one hand-over: the drain loop ends at once (g_rx_times = 0) *)
      rewrite (rxop_drain_idle I (Some (TFrame a bytes)) W2 _ Ti2 F2 T2).
      exists W2. exact (conj eq_refl (conj Hc2 (conj (tp_keepalive _ _ _ _ Htp) (conj Og2 (tp_drain _ _ _ _ Htp))))).
    + (* two hand-overs: the drain loop's turn (DS:524-525) runs the model and the library's rx again, from the
         world the first reception and the tick left *)
      set (Y2 := set_g_rx_times W2 0).
      assert (HY2 : wframe (in_rs R_poll) W2 Y2) by (unfold Y2; wfrs).
      assert (Hpg2 : rx_pre_g I ops W2 (rxbuf (TFrame a bytes) got)).
      { constructor.
        - exact Hc2.
        - exact (tp_keepalive _ _ _ _ Htp).
        - exact (ow_room_frR R_tick W1 W2 HfT HRo
                   (ow_room_after Y1 W1 (rp_zero _ _ _ _ Hpre1) (rd_og _ _ _ _ _ Hd0) (rk_step _ _ _ _ _ _ _ Hd))).
        - (* a frame the second reception accepts was accepted by the first (the filters read M.desk_known,
             M.desk, M.state, which the tick keeps); an e0 that can wake left M.fail = g_fail_next and a state
             other than ONLINE, where the tick changes nothing *)
          intros Hac2 Hw.
          pose proof (rk_acc _ _ _ _ _ _ _ Hd (rx_accepts_same W2 W1 _ Hac2 (eq_sym K2) (eq_sym K3) (eq_sym K1)))
            as Hac1.
          destruct (rk_wake _ _ _ _ _ _ _ Hd Hac1 Hw) as [Efl Eon].
          pose proof (tick_quiet_off I (Some (TFrame a bytes)) ops W1 Hc1' Eon) as Eq.
          rewrite Etk in Eq. injection Eq as EW Er'. subst W2. exact Efl.
        - intros Hcode. transitivity (g_rx_send W1); [rxop_rg HfT HRt|].
          rewrite (rk_rx_send _ _ _ _ _ _ _ Hd). transitivity (g_rx_send Y1); [fget Hf |].
          exact (rp_rx_send _ _ _ _ Hpre1 Hcode). }
      pose proof (rxop_pre_g_poll I ops W2 Y2 _ Hpg2 HY2) as Hpre2.
      destruct (Hrx I ops (TFrame a bytes) got Y2 ltac:(cbn [tf_bytes]; lia) ltac:(cbn [tf_addr tf_bytes]; lia) Hpre2)
        as (Bx2 & t2 & Em2 & _ & Hf2 & Hl2).
      destruct (Hl2 Bx2 (wframe_refl _ _)) as (W3 & r3 & Es2 & Hd2).
      pose proof (rk_done _ _ _ _ _ _ _ Hd2) as Hd20.
      assert (R3 : g_rx Y2 = a) by (transitivity (g_rx W2); [unfold Y2; wget | exact R2]).
      assert (Rx2 : g_rx Bx2 = a) by (transitivity (g_rx Y2); [fget Hf2 | exact R3]).
      assert (Er2 : call_recv I (Some (TFrame a bytes)) W2 DIGINET_MAX_FRAME_LEN =
                    Some (Bx2, got, rxbuf (TFrame a bytes) got)).
      { unfold call_recv. rewrite Ti2, (Z.eqb_refl (ti_io_recv I)). cbv beta iota.
        rewrite (rxop_io_recv I a bytes W2 got 1 Bx2 HW2n F2 R2 T2 ltac:(lia) L2 Ha0 Hg Hgl).
        - destruct (Z.ltb_spec 0 got); [reflexivity | lia].
        - destruct (Z.eqb_spec got 0) as [E|E]; [lia|]. cbv beta iota. exists t2. exact Em2.
        - exact Rx2. }
      assert (Nx2 : g_now Bx2 = g_now Y2) by fget Hf2.
      assert (Pnx2 : call_now I Bx2 = Some (g_now Y2)).
      { unfold call_now.
        assert (Jx : S_io_now_us Bx2 = ti_io_now I).
        { transitivity (S_io_now_us Y2); [fget Hf2|]. transitivity (S_io_now_us W2); [fget HY2|].
          exact (a3_io_now _ _ (ac_io _ _ _ Hc2)). }
        rewrite Jx, (Z.eqb_refl (ti_io_now I)). cbv beta iota. unfold io_now_m. rewrite Nx2. reflexivity. }
      change (Z.to_nat (2 - 1)) with (S O).
      rewrite (rxop_drain_step I (Some (TFrame a bytes)) W2 O Bx2 got (rxbuf (TFrame a bytes) got) (g_now Y2) W3 r3
                 Er2 ltac:(lia) Pnx2 Es2).
      assert (F3 : g_rx_fail W3 = 0).
      { rewrite (rd_rx_fail _ _ _ _ _ Hd20). transitivity (g_rx_fail Y2); [fget Hf2|].
        transitivity (g_rx_fail W2); [unfold Y2; wget | exact F2]. }
      assert (T3 : g_rx_times W3 = 0).
      { rewrite (rd_rx_times _ _ _ _ _ Hd20). transitivity (g_rx_times Y2); [fget Hf2 | unfold Y2; wget]. }
      pose proof (rd_core _ _ _ _ _ Hd20) as Hc3.
      rewrite (rxop_drain_idle I (Some (TFrame a bytes)) W3 O (a3_io_recv _ _ (ac_io _ _ _ Hc3)) F3 T3).
      exists W3. split; [reflexivity|].
      split; [exact Hc3|]. split; [exact (rd_ka _ _ _ _ _ Hd20)|]. split; [exact (rd_og _ _ _ _ _ Hd20)|].
      destruct (rxop_m_rx_01 _ _ _ _ _ _ Em2) as [E|E].
      * apply (rk_drain _ _ _ _ _ _ _ Hd2 E).
        exact (grx_drain _ _ (grx_poll _ _ HY2) ops (ac_q _ _ _ Hc2) (tp_drain _ _ _ _ Htp)).
      * exact (rd_drain _ _ _ _ _ Hd20 E).
Qed.

Lemma rxop_tail_ok : forall (HL : links) (Hrx : rx_ok_g_stmt) I ops B2a a bytes got times,
  rx_pre I ops B2a (rxbuf (TFrame a bytes) got) -> 0 <= ops < OPS_MAX -> 0 < a ->
  a + Z.of_nat (length bytes) < 2 ^ 64 -> 0 <= got <= 1514 -> got <= Z.of_nat (length bytes) ->
  (times = 1 \/ times = 2) ->
  exists B4, rxop_tail8 I a bytes got times 0 B2a = Some (B4, tt) /\ agree I (ops + 1) B4.
Proof.
  intros HL Hrx I ops B2a a bytes got times Hpre Hops Ha0 Ha1 Hg Hgl Htm.
  destruct (rxop_poll_ok HL Hrx I ops a bytes got times B2a Ha0 Ha1 Hg Hgl Htm Hpre)
    as (Wd & Ep & Hcd & Hkd & Hod & Hdd).
  pose proof (ac_len _ _ _ Hcd) as HBd.
  assert (HwF : wframe (in_rs grx_rs) Wd (set_g_rx_fail (set_g_rx Wd 0) 0)) by wfrs.
  pose proof (grx_core _ _ HwF I ops Hcd) as Hcf.
  pose proof (grx_ka _ _ HwF Hkd) as Hkf.
  assert (HRo : forall x, OFF_GOT <= x < OFF_OW + SZ_OW -> ~ in_rs grx_rs x).
  { intros x Hx. apply (disj_rs_ok OFF_GOT (OFF_OW + SZ_OW - OFF_GOT) grx_rs); [vm_compute; reflexivity | lia]. }
  pose proof (rxop_og_frame _ _ _ HwF HRo Hod) as Hof.
  pose proof (grx_drain _ _ HwF ops (ac_q _ _ _ Hcd) Hdd) as Hdf.
  assert (Hs : settle_m (set_g_rx_fail (set_g_rx Wd 0) 0) 1 = Some (set_g_rx_fail (set_g_rx Wd 0) 0, tt))
    by exact (settle_ok I ops _ 1 Hcf Hkf (rxop_og_settle _ Hof) (fun _ => Hdf)).
  exists (set_g_rx_fail (set_g_rx Wd 0) 0). split.
  - unfold rxop_tail8. rewrite Ep. cbv beta iota. change (if 0 =? 0 then 1 else 0) with 1. rewrite Hs. reflexivity.
  - constructor.
    + exact (agree_core_mono I ops (ops + 1) _ Hcf ltac:(unfold OPS_MAX in *; lia)).
    + exact Hkf.
    + wget.
Qed.

Lemma rxop_receive8 : forall (HL : links) (Hrx : rx_ok_g_stmt) I ops B a bytes pf,
  agree I ops B -> 0 <= ops < OPS_MAX -> 0 < a -> a + Z.of_nat (length bytes) < 2 ^ 64 ->
  exists B', receive_m I B a bytes 1 pf = Some (B', tt) /\ agree I (ops + 1) B'.
Proof.
  intros HL Hrx I ops B a bytes pf HA Hops Ha0 Ha1.
  destruct (rxop_begin I ops B bytes HA) as (B1 & Eob & Hpre1 & _).
  destruct (rxop_got_ok bytes) as [Hg Hgl].
  pose proof (rxop_pre_again I ops _ bytes (rxbuf (TFrame a bytes) (rxop_got bytes)) Hpre1) as Hpre2.
  rewrite (rxop_receive8_eq I B a bytes pf Ha0), Eob. cbv beta iota.
  assert (Htm : (if Z.land pf 1 =? 0 then 1 else 2) = 1 \/ (if Z.land pf 1 =? 0 then 1 else 2) = 2)
    by (destruct (Z.land pf 1 =? 0); [left | right]; reflexivity).
  destruct (rxop_land01 (Z.shiftr pf 1)) as [Ef|Ef]; rewrite Ef.
  - exact (rxop_tail_ok HL Hrx I ops _ a bytes (rxop_got bytes) _ Hpre2 Hops Ha0 Ha1 Hg Hgl Htm).
  - exact (rxop_tail_fail_ok I ops _ a bytes (rxop_got bytes) _ _ Hpre2 Hops Ha0 Ha1 Hg).
Qed.

(* ---- the operations on top of the receive (FT:1027-1066, :1169-1214) ----
   op0_stmt / op8_stmt: the two receive lemmas' statements (rxop_receive0 under rx_ok, rxop_receive8 under
   rx_ok_g). *)

Definition op0_stmt : Prop := forall I ops B a bytes,
  agree I ops B -> 0 <= ops < OPS_MAX -> 0 < a -> a + Z.of_nat (length bytes) < 2 ^ 64 ->
  exists B', receive_m I B a bytes 0 0 = Some (B', tt) /\ agree I (ops + 1) B'.
Definition op8_stmt : Prop := forall I ops B a bytes pf,
  agree I ops B -> 0 <= ops < OPS_MAX -> 0 < a -> a + Z.of_nat (length bytes) < 2 ^ 64 ->
  exists B', receive_m I B a bytes 1 pf = Some (B', tt) /\ agree I (ops + 1) B'.

(* fuzz.h:73-76 fuzz_record: at most 65535 bytes, inside D *)
Lemma rxop_record_ok : forall D c, fuzz_in_ok D c ->
  exists c' off n, fuzz_record_m D c = (c', off, n) /\ fuzz_in_ok D c' /\
    0 <= n < 65536 /\ 0 <= off /\ off + n <= Z.of_nat (length D).
Proof.
  intros D c Hc.
  destruct (fuzz_u16_ok D c Hc) as (c1 & w & E1 & Hc1 & Hw).
  destruct (fuzz_take_ok D c1 w Hc1 (proj1 Hw)) as (c2 & off & n & E2 & Hc2 & Hn & Hoff & Hend & _).
  exists c2, off, n. split; [|split; [exact Hc2 | lia]].
  unfold fuzz_record_m. rewrite E1. cbv beta iota zeta. exact E2.
Qed.

(* build_and_receive (FT:1027-1033): a body of at most SPEC_MAX_BODY bytes makes a frame of at most SPEC_MAX_FRAME *)
Lemma rxop_bar_ok : op0_stmt -> forall I ops B a dst src send ack retry cmd body,
  agree I ops B -> 0 <= ops < OPS_MAX -> 0 < a -> a + 1514 < 2 ^ 64 -> (length body <= 1484)%nat ->
  exists B', build_and_receive_m I B a dst src send ack retry cmd body = Some (B', tt) /\ agree I (ops + 1) B'.
Proof.
  intros H0 I ops B a dst src send ack retry cmd body HA Hops Ha Ha2 Hl.
  assert (Ht : (SPEC_MAX_BODY <? Z.of_nat (length body)) = false)
    by (apply Z.ltb_ge; unfold SPEC_MAX_BODY; lia).
  destruct (spec_build_frame dst src send ack retry cmd 1 body 0) as [frame n] eqn:Ef.
  pose proof (spec_build_frame_len dst src send ack retry cmd 1 body 0 Hl) as Lf.
  rewrite Ef in Lf. cbn [fst] in Lf.
  assert (Hf : a + Z.of_nat (length frame) < 2 ^ 64) by lia.
  destruct (H0 I ops B a frame HA Hops Ha Hf) as (B' & E & HA').
  exists B'. split; [|exact HA'].
  unfold build_and_receive_m. rewrite Ht. rewrite Ef. cbv beta iota zeta. exact E.
Qed.

(* op_frame (FT:1035-1050) *)
Lemma rxop_frame_of : op0_stmt -> forall I ops B D a c,
  agree I ops B -> 0 <= ops < OPS_MAX -> 0 < a -> a + 1514 < 2 ^ 64 -> fuzz_in_ok D c ->
  exists B' c', op_frame_m I B D a c = Some (B', c') /\ agree I (ops + 1) B' /\ fuzz_in_ok D c'.
Proof.
  intros H0 I ops B D a c HA Hops Ha Ha2 Hc.
  destruct (fuzz_u8_ok D c Hc) as (c1 & sel & E1 & Hc1 & _).
  destruct (fuzz_u16_ok D c1 Hc1) as (c2 & send & E2 & Hc2 & _).
  destruct (fuzz_u16_ok D c2 Hc2) as (c3 & ack0 & E3 & Hc3 & _).
  destruct (fuzz_u8_ok D c3 Hc3) as (c4 & r & E4 & Hc4 & _).
  destruct (fuzz_u16_ok D c4 Hc4) as (c5 & w & E5 & Hc5 & _).
  assert (Hm : 0 <= w mod (SPEC_MAX_BODY + 1) < SPEC_MAX_BODY + 1)
    by (apply Z.mod_pos_bound; unfold SPEC_MAX_BODY; lia).
  destruct (fuzz_take_ok D c5 (w mod (SPEC_MAX_BODY + 1)) Hc5 (proj1 Hm))
    as (c6 & off & len & E6 & Hc6 & Hn & Hoff & Hend & _).
  assert (Hl : (length (sub D off (Z.to_nat len)) <= 1484)%nat).
  { rewrite (length_sub_D D off len Hoff (proj1 Hn) Hend). clear - Hn Hm.
    unfold SPEC_MAX_BODY in *. lia. }
  unfold op_frame_m.
  rewrite E1. cbv beta iota zeta. rewrite E2. cbv beta iota zeta. rewrite E3. cbv beta iota zeta.
  rewrite E4. cbv beta iota zeta. rewrite E5. cbv beta iota zeta. rewrite E6. cbv beta iota zeta.
  match goal with
  | |- context [build_and_receive_m I B a ?dst ?src ?send ?ack ?retry ?cmd (sub D off (Z.to_nat len))] =>
      destruct (rxop_bar_ok H0 I ops B a dst src send ack retry cmd (sub D off (Z.to_nat len))
                  HA Hops Ha Ha2 Hl) as (B1 & E & HA1)
  end.
  rewrite E. cbv beta iota zeta.
  exists B1, c6. split; [exact eq_refl|]. split; [exact HA1 | exact Hc6].
Qed.

(* op_announce (FT:1052-1066) *)
Lemma rxop_announce_of : op0_stmt -> forall I ops B D a c,
  agree I ops B -> 0 <= ops < OPS_MAX -> 0 < a -> a + 1514 < 2 ^ 64 -> fuzz_in_ok D c ->
  exists B' c', op_announce_m I B D a c = Some (B', c') /\ agree I (ops + 1) B' /\ fuzz_in_ok D c'.
Proof.
  intros H0 I ops B D a c HA Hops Ha Ha2 Hc.
  destruct (fuzz_u8_ok D c Hc) as (c1 & sel & E1 & Hc1 & _).
  destruct (fuzz_u8_ok D c1 Hc1) as (c2 & m & E2 & Hc2 & _).
  destruct (fuzz_u8_ok D c2 Hc2) as (c3 & nm & E3 & Hc3 & _).
  pose proof (rxop_ann_body_len m nm) as Lb.
  unfold op_announce_m.
  rewrite E1. cbv beta iota zeta. rewrite E2. cbv beta iota zeta. rewrite E3. cbv beta iota zeta.
  match goal with
  | |- context [build_and_receive_m I B a ?dst ?src ?send ?ack ?retry ?cmd ?body] =>
      assert (Hl : (length body <= 1484)%nat) by (rewrite Lb; lia);
      destruct (rxop_bar_ok H0 I ops B a dst src send ack retry cmd body HA Hops Ha Ha2 Hl) as (B1 & E & HA1)
  end.
  rewrite E. cbv beta iota zeta.
  exists B1, c3. split; [exact eq_refl|]. split; [exact HA1 | exact Hc3].
Qed.

(* one operation of the loop that receives (FT:1169-1214: cases 0, 1, 2 and 8) *)
Lemma rxop_op_of : op0_stmt -> op8_stmt -> forall I ops B A D c k,
  agree I ops B -> 0 <= ops < OPS_MAX -> fuzz_in_ok D c -> fi_n c <> 0 ->
  0 < A k -> A k + 65536 <= 2 ^ 64 ->
  let op := snd (fuzz_u8_m D c) mod 9 in
  (op = 0 \/ op = 1 \/ op = 2 \/ op = 8) ->
  exists B' c' k', LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B', (c', k')) /\ agree I (ops + 1) B' /\ fuzz_in_ok D c'.
Proof.
  intros H0 H8 I ops B A D c k HA Hops Hc _ Ha Ha2. cbv zeta. intros Hop.
  destruct (fuzz_u8_ok D c Hc) as (c1 & opb & E1 & Hc1 & _).
  destruct (fuzz_u8_ok D c1 Hc1) as (c2 & pf & E2 & Hc2 & _).
  rewrite E1 in Hop. cbn [fst snd] in Hop.
  unfold LLVMFuzzerTestOneInput_op_m. rewrite E1. cbv beta iota zeta.
  destruct (Z.eqb_spec (opb mod 9) 0) as [Hq0|Hq0].
  { (* op 0, FT:1171-1174 *)
    destruct (rxop_record_ok D c1 Hc1) as (c3 & off & n & Er & Hc3 & Hn & Hoff & Hend).
    rewrite Er. cbv beta iota zeta.
    assert (Hb : A k + Z.of_nat (length (sub D off (Z.to_nat n))) < 2 ^ 64)
      by (rewrite (length_sub_D D off n Hoff (proj1 Hn) Hend); lia).
    destruct (H0 I ops B (A k) (sub D off (Z.to_nat n)) HA Hops Ha Hb) as (B1 & E & HA1).
    rewrite E. cbv beta iota zeta.
    exists B1, c3, (S k). split; [exact eq_refl|]. split; [exact HA1 | exact Hc3]. }
  destruct (Z.eqb_spec (opb mod 9) 1) as [Hq1|Hq1].
  { (* op 1, FT:1175-1177 *)
    assert (Hk : A k + 1514 < 2 ^ 64) by lia.
    destruct (rxop_frame_of H0 I ops B D (A k) c1 HA Hops Ha Hk Hc1) as (B1 & c3 & E & HA1 & Hc3).
    rewrite E. cbv beta iota zeta.
    exists B1, c3, (S k). split; [exact eq_refl|]. split; [exact HA1 | exact Hc3]. }
  destruct (Z.eqb_spec (opb mod 9) 2) as [Hq2|Hq2].
  { (* op 2, FT:1178-1180 *)
    assert (Hk : A k + 1514 < 2 ^ 64) by lia.
    destruct (rxop_announce_of H0 I ops B D (A k) c1 HA Hops Ha Hk Hc1) as (B1 & c3 & E & HA1 & Hc3).
    rewrite E. cbv beta iota zeta.
    exists B1, c3, (S k). split; [exact eq_refl|]. split; [exact HA1 | exact Hc3]. }
  (* op 8, the default, FT:1209-1214 *)
  destruct Hop as [Hop|[Hop|[Hop|Hop]]];
    [exfalso; exact (Hq0 Hop) | exfalso; exact (Hq1 Hop) | exfalso; exact (Hq2 Hop) |].
  destruct (Z.eqb_spec (opb mod 9) 3) as [Hx|_]; [exfalso; rewrite Hop in Hx; discriminate Hx|].
  destruct (Z.eqb_spec (opb mod 9) 4) as [Hx|_]; [exfalso; rewrite Hop in Hx; discriminate Hx|].
  destruct (Z.eqb_spec (opb mod 9) 5) as [Hx|_]; [exfalso; rewrite Hop in Hx; discriminate Hx|].
  destruct (Z.eqb_spec (opb mod 9) 6) as [Hx|_]; [exfalso; rewrite Hop in Hx; discriminate Hx|].
  destruct (Z.eqb_spec (opb mod 9) 7) as [Hx|_]; [exfalso; rewrite Hop in Hx; discriminate Hx|].
  cbv beta iota zeta.
  rewrite E2. cbv beta iota zeta.
  destruct (rxop_record_ok D c2 Hc2) as (c3 & off & n & Er & Hc3 & Hn & Hoff & Hend).
  rewrite Er. cbv beta iota zeta.
  assert (Hb : A k + Z.of_nat (length (sub D off (Z.to_nat n))) < 2 ^ 64)
    by (rewrite (length_sub_D D off n Hoff (proj1 Hn) Hend); lia).
  destruct (H8 I ops B (A k) (sub D off (Z.to_nat n)) pf HA Hops Ha Hb) as (B1 & E & HA1).
  rewrite E. cbv beta iota zeta.
  exists B1, c3, (S k). split; [exact eq_refl|]. split; [exact HA1 | exact Hc3].
Qed.

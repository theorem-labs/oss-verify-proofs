(* receive_seg_inv: the model piece of the image-A walk of receive (lib/A/Prog/receive_cg.v; the cut interface
   lib/A/Prog/receive_seg_cut.v): recv_inv_stmt, the run invariants with their two index bounds (lib/TModel/TRunInv.v
   run_inv) at the worlds receive hands its callees and settle. No code and no machine state: only lib/TModel worlds.
   What the invariants read. Below the bounds g_ncmd <= CMDS_MAX and S_queued <= QUEUE_MAX (the last two conjuncts
   of run_inv), every byte run_inv reads lies in the world offsets [96, 64988):
     M.fly.on          96 .. 99                    (A_M_fly_on = M + 96, 4 bytes)
     M.fly.len         1640 .. 1647                (A_M_fly_len = M + 96 + 1544, 8 bytes)
     g_s.cfg.max_cmds  1700 .. 1703, max_body 1704 .. 1707
     g_s.queue[i].len  3432 + 32 i                 (1 byte, i < S_queued <= 512: at most 19784)
     g_s.queued        19792 .. 19795
     g_cmd[s].st       19912 + 40 s .. + 3, .len 19912 + 40 s + 36   (s < g_ncmd <= 1024: at most 60868)
     g_ncmd            64984 .. 64987.
   rvi_upd (from rinv_upd): a write upd B k v of a world of W_LEN bytes that ends at or below 96 or starts at or above
   64988 keeps the length (lib/TModel/TNotifyFacts.v len_upd_W) and run_inv: each read above is at an offset the
   write misses (TNotifyFacts.v rd_upd_W), the index of (2) and (4) kept inside its array by the bound conjuncts.
   The stores receive makes before its calls are all such writes:
     op_begin (lib/TModel/TCb.v op_begin_m, recv_w1): the memset of OW (65312, 304 bytes, to the end of the world),
       the memset of GOT (65084, 224 bytes), OW.desk_off (65544, 4 bytes), M.fail (88 .. 91, below M.fly at 96);
     g_rx_send (64988, 4 bytes) for recv_w2, and for recv_w2c g_rx_send again, g_rx (65008, 8), g_rx_len (65016, 8),
       g_rx_times (64996, 4), g_rx_fail (64992, 4).
   So (1) recv_w2 and (2) recv_w2c keep run_inv (rvi_w2, rvi_w2c). (3) m_rx_m at recv_w2, (4) diginet_session_rx_m
   and (5) diginet_session_poll_m at recv_w2c keep it by TRunInv.v mrx_m_run_inv, rx_m_run_inv and poll_m_run_inv,
   each fed the world's length and run_inv; on (5) the two stores of 0 at g_rx and g_rx_fail after
   diginet_session_poll then keep it by rvi_set_g_rx / rvi_set_g_rx_fail. Every world in this file is a variable or a
   chain of upd over a variable; the field offsets are TWorld.v constants, unfolded only inside lia side goals. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TImgA receive_cg receive_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TNotifyFacts TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TRunInv.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TNF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNotifyFacts.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.

(* The side goals: closed offset arithmetic over TWorld.v constants, with the index bounds of (2) and (4). *)
Ltac rvi_lia :=
  unfold TW.A_M_fly_on, TW.A_M_fly_len, TW.A_M_fail, TW.A_OW_desk_off, TW.A_S_cfg_max_cmds, TW.A_S_cfg_max_body,
    TW.A_S_queue_len, TW.A_S_queued, TW.A_Cmd_st, TW.A_Cmd_len in *;
  unfold TW.W_LEN, TW.OFF_M, TW.OFF_g_s, TW.OFF_g_cmd, TW.OFF_g_ncmd, TW.OFF_g_rx_send, TW.OFF_g_rx_fail,
    TW.OFF_g_rx_times, TW.OFF_g_rx, TW.OFF_g_rx_len, TW.OFF_GOT, TW.OFF_OW, TW.SZ_OW, TW.SZ_GOT,
    TC.CMDS_MAX, TC.QUEUE_MAX in *;
  lia.

(* ------------------------------------------------------------------ *)
(* A write outside [96, 64988) keeps run_inv                           *)
(* ------------------------------------------------------------------ *)

Lemma rinv_upd : forall (B v : list byte) (k : Z), length B = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= TW.W_LEN -> (k + Z.of_nat (length v) <= 96 \/ 64988 <= k) ->
  TRunInv.run_inv B -> TRunInv.run_inv (TW.upd B k v).
Proof.
  intros B v k HL Hk Hkv Hd (I1 & I2 & I4 & I5a & I5b & Bn & Bq).
  assert (RD : forall k' n, 96 <= k' -> k' + Z.of_nat n <= 64988 ->
                 TW.u_at (TW.upd B k v) k' n = TW.u_at B k' n).
  { intros k' n H1 H2. apply TNF.rd_upd_W; [exact HL | exact Hk | exact Hkv | lia |].
    destruct Hd as [Hd | Hd]; [right | left]; lia. }
  clear Hd Hk Hkv.
  assert (EON : TW.M_fly_on (TW.upd B k v) = TW.M_fly_on B).
  { unfold TW.M_fly_on, TW.s32_at. rewrite RD by rvi_lia. reflexivity. }
  assert (ELEN : TW.M_fly_len (TW.upd B k v) = TW.M_fly_len B).
  { unfold TW.M_fly_len. rewrite RD by rvi_lia. reflexivity. }
  assert (EQD : TW.S_queued (TW.upd B k v) = TW.S_queued B).
  { unfold TW.S_queued. rewrite RD by rvi_lia. reflexivity. }
  assert (ENC : TW.g_ncmd (TW.upd B k v) = TW.g_ncmd B).
  { unfold TW.g_ncmd. rewrite RD by rvi_lia. reflexivity. }
  assert (ECM : TW.S_cfg_max_cmds (TW.upd B k v) = TW.S_cfg_max_cmds B).
  { unfold TW.S_cfg_max_cmds. rewrite RD by rvi_lia. reflexivity. }
  assert (ECB : TW.S_cfg_max_body (TW.upd B k v) = TW.S_cfg_max_body B).
  { unfold TW.S_cfg_max_body. rewrite RD by rvi_lia. reflexivity. }
  unfold TRunInv.run_inv. rewrite EON, ELEN, EQD, ENC, ECM, ECB.
  split; [exact I1|]. split.
  { intros i Hi. unfold TW.S_queue_len. rewrite RD by rvi_lia. exact (I2 i Hi). }
  split.
  { intros s Hs Hst.
    assert (EST : TW.Cmd_st (TW.upd B k v) s = TW.Cmd_st B s).
    { unfold TW.Cmd_st, TW.s32_at. rewrite RD by rvi_lia. reflexivity. }
    rewrite EST in Hst. unfold TW.Cmd_len. rewrite RD by rvi_lia. exact (I4 s Hs Hst). }
  split; [exact I5a|]. split; [exact I5b|]. split; [exact Bn | exact Bq].
Qed.

(* The world's length and run_inv together, the form every step below carries. *)
Definition rvi_w (B : list byte) : Prop := length B = Z.to_nat TW.W_LEN /\ TRunInv.run_inv B.

Lemma rvi_upd : forall (B v : list byte) (k : Z), rvi_w B -> 0 <= k ->
  k + Z.of_nat (length v) <= TW.W_LEN -> (k + Z.of_nat (length v) <= 96 \/ 64988 <= k) ->
  rvi_w (TW.upd B k v).
Proof.
  intros B v k [HL HI] Hk Hkv Hd. split.
  - exact (TNF.len_upd_W B v k HL Hk Hkv).
  - exact (rinv_upd B v k HL Hk Hkv Hd HI).
Qed.

(* ------------------------------------------------------------------ *)
(* The stores receive makes                                            *)
(* ------------------------------------------------------------------ *)

Lemma rvi_set_g_rx_send : forall B x, rvi_w B -> rvi_w (TW.set_g_rx_send B x).
Proof.
  intros B x H. unfold TW.set_g_rx_send.
  apply rvi_upd; [exact H | rvi_lia | rewrite TWL.length_put; rvi_lia | right; rvi_lia].
Qed.

Lemma rvi_set_g_rx_fail : forall B x, rvi_w B -> rvi_w (TW.set_g_rx_fail B x).
Proof.
  intros B x H. unfold TW.set_g_rx_fail.
  apply rvi_upd; [exact H | rvi_lia | rewrite TWL.length_put; rvi_lia | right; rvi_lia].
Qed.

Lemma rvi_set_g_rx_times : forall B x, rvi_w B -> rvi_w (TW.set_g_rx_times B x).
Proof.
  intros B x H. unfold TW.set_g_rx_times.
  apply rvi_upd; [exact H | rvi_lia | rewrite TWL.length_put; rvi_lia | right; rvi_lia].
Qed.

Lemma rvi_set_g_rx : forall B x, rvi_w B -> rvi_w (TW.set_g_rx B x).
Proof.
  intros B x H. unfold TW.set_g_rx.
  apply rvi_upd; [exact H | rvi_lia | rewrite TWL.length_put; rvi_lia | right; rvi_lia].
Qed.

Lemma rvi_set_g_rx_len : forall B x, rvi_w B -> rvi_w (TW.set_g_rx_len B x).
Proof.
  intros B x H. unfold TW.set_g_rx_len.
  apply rvi_upd; [exact H | rvi_lia | rewrite TWL.length_put; rvi_lia | right; rvi_lia].
Qed.

(* M.fail, M + 88 .. M + 91: below M.fly.on (M + 96). *)
Lemma rvi_set_M_fail : forall B x, rvi_w B -> rvi_w (TW.set_M_fail B x).
Proof.
  intros B x H. unfold TW.set_M_fail.
  apply rvi_upd; [exact H | rvi_lia | rewrite TWL.length_put; rvi_lia | left; rewrite TWL.length_put; rvi_lia].
Qed.

Lemma rvi_set_OW_desk_off : forall B x, rvi_w B -> rvi_w (TW.set_OW_desk_off B x).
Proof.
  intros B x H. unfold TW.set_OW_desk_off.
  apply rvi_upd; [exact H | rvi_lia | rewrite TWL.length_put; rvi_lia | right; rvi_lia].
Qed.

(* The two memsets of op_begin: OW's 304 bytes and GOT's 224 bytes. *)
Lemma rvi_ow : forall B v, rvi_w B -> length v = Z.to_nat TW.SZ_OW -> rvi_w (TW.upd B TW.OFF_OW v).
Proof.
  intros B v H Hv. assert (Hn : Z.of_nat (length v) = TW.SZ_OW) by (rewrite Hv; apply Z2Nat.id; rvi_lia).
  apply rvi_upd; [exact H | rvi_lia | rewrite Hn; rvi_lia | right; rvi_lia].
Qed.

Lemma rvi_got : forall B v, rvi_w B -> length v = Z.to_nat TW.SZ_GOT -> rvi_w (TW.upd B TW.OFF_GOT v).
Proof.
  intros B v H Hv. assert (Hn : Z.of_nat (length v) = TW.SZ_GOT) by (rewrite Hv; apply Z2Nat.id; rvi_lia).
  apply rvi_upd; [exact H | rvi_lia | rewrite Hn; rvi_lia | right; rvi_lia].
Qed.

(* ------------------------------------------------------------------ *)
(* The worlds receive hands its callees                                *)
(* ------------------------------------------------------------------ *)

(* op_begin (TCb.v op_begin_m): the two memsets, OW.desk_off = -1, M.fail = g_fail_next. *)
Lemma rvi_w1 : forall Bw, rvi_w Bw -> rvi_w (recv_w1 Bw).
Proof.
  intros Bw H. unfold recv_w1, TC.op_begin_m. cbv beta iota zeta.
  apply rvi_set_M_fail. apply rvi_set_OW_desk_off.
  apply rvi_got; [| apply repeat_length].
  apply rvi_ow; [exact H | apply repeat_length].
Qed.

(* m_rx's world (by_poll = 0) and the poll cut's: op_begin, then the store of the send value at g_rx_send. *)
Lemma rvi_w2 : forall Bw bytes, rvi_w Bw -> rvi_w (recv_w2 Bw bytes).
Proof.
  intros Bw bytes H. unfold recv_w2. apply rvi_set_g_rx_send. apply rvi_w1. exact H.
Qed.

(* diginet_session_poll's world: recv_w2, then g_rx_send, g_rx, g_rx_len, g_rx_times, g_rx_fail. *)
Lemma rvi_w2c : forall Bw bytes a pf, rvi_w Bw -> rvi_w (recv_w2c Bw bytes a pf).
Proof.
  intros Bw bytes a pf H. unfold recv_w2c.
  apply rvi_set_g_rx_fail. apply rvi_set_g_rx_times. apply rvi_set_g_rx_len. apply rvi_set_g_rx.
  apply rvi_set_g_rx_send. apply rvi_w2. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* The model piece                                                     *)
(* ------------------------------------------------------------------ *)

Lemma recv_inv : recv_inv_stmt.
Proof.
  unfold recv_inv_stmt. split; [|split; [|split; [|split]]].
  - intros Bw bytes HL HI. exact (proj2 (rvi_w2 Bw bytes (conj HL HI))).
  - intros Bw bytes a pf HL HI. exact (proj2 (rvi_w2c Bw bytes a pf (conj HL HI))).
  - intros Bw bytes F n Bx t HL HI HM.
    destruct (rvi_w2 Bw bytes (conj HL HI)) as [L2 I2].
    exact (proj2 (TRunInv.mrx_m_run_inv timg_A F (recv_w2 Bw bytes) n Bx t L2 I2 HM)).
  - intros F Bx b now By r HL HI HM.
    exact (proj2 (TRunInv.rx_m_run_inv timg_A F Bx b now By r HL HI HM)).
  - intros Bw bytes a pf F B2d r HL HI HM.
    destruct (rvi_w2c Bw bytes a pf (conj HL HI)) as [L2 I2].
    destruct (TRunInv.poll_m_run_inv timg_A F (recv_w2c Bw bytes a pf) 0 B2d r L2 I2 HM) as [L3 I3].
    exact (proj2 (rvi_set_g_rx_fail (TW.set_g_rx B2d 0) 0 (rvi_set_g_rx B2d 0 (conj L3 I3)))).
Qed.

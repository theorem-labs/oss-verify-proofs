(* diginet_session_wake_seg_keep: the model-side facts (TModel, world = list byte) that the machine pieces of the ASan
   walk of diginet_session_wake (lib/A/Prog/diginet_session_wake_cg.v) share. No machine state, no image address:
   - the branch conditions as bit-vector tests: a 64-bit equality and a signed test against 0 of sign-extended
     values are the model's Z tests (wk_eqb, wk_lts0), and a 32-bit signed read is in range (wk_s32_range);
   - the stores as the code makes them: a 4-byte store of a sign-extended load is the model's (wk_put4_s32), a u64 sum
     stores as the plain sum (wk_put8_u64), the refused path's world (wk_refused_eq);
   - what the stores of :129-131 keep (wk_w1_eq, wk_w1_keep: S_state, GOT.n, g_fail_next, M.fly, g_ncmd and the
     commands, read by send_control and io_send), and what the stores of :139-142 keep (wk_w3_keep);
   - send_control_m's result: its world keeps the length, S_state and GOT.n (wk_sc_keep, from TOpsKeep.v), and its
     return value is a 64-bit value, 0 when not negative, with the 60 frame bytes (wk_sc_ret);
   - set_state_m's two branches: the same state leaves the world (wk_set_state_same); a change stores the state,
     whose store keeps the notify pointer, GOT.n and g_fail_next (wk_set_state_keep), and calls notice_m through
     the notify pointer (wk_set_state_go);
   - a state notice that is not to ONLINE keeps g_fail_next and the world's length (wk_notice_keep). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require MState Mem ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TImg TNeed TSess0 TCb
  TSess TIoSendFail TOpsKeep.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg.
Import ListNotations.
Open Scope Z_scope.

Module TOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOpsKeep.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNeed.
Module TIF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TIoSendFail.
Module LMS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.MState.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LZB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.ZBridge.

(* ---- the branch conditions ---- *)

Lemma wk_eqb : forall v c, -2^63 <= v < 2^63 -> -2^63 <= c < 2^63 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 c) = (v =? c).
Proof.
  intros v c Hv Hc. unfold bv_eqb. rewrite !LMS.unsigned_lit_wrap.
  destruct (Z.eqb_spec v c) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E.
  assert (E2 : (v - c) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  apply Z.mod_divide in E2; [|lia]. destruct E2 as [k Ek]. nia.
Qed.

Lemma wk_lts0 : forall v, -2^63 <= v < 2^63 -> bv_lts (Z_to_bv 64 v) (Z_to_bv 64 0) = (v <? 0).
Proof.
  intros v Hv. rewrite LZB.bv_lts_zero_r, LMS.unsigned_lit_wrap.
  destruct (Z.ltb_spec v 0) as [N|N].
  - apply Z.leb_le. assert (E : v mod 2^64 = v + 2^64) by (symmetry; apply Z.mod_unique with (-1); lia). lia.
  - apply Z.leb_gt. rewrite Z.mod_small by lia. lia.
Qed.

Lemma wk_s32_range : forall B k, -2^31 <= TW.s32_at B k < 2^31.
Proof. intros B k. apply TWL.s32_range. Qed.

(* ---- the stores ---- *)

(* A store of the model's u_at as the binary's sign-extended lw value writes the same 4 bytes. *)
Lemma wk_put4_s32 : forall bs k, TW.put 4 (TW.u_at bs k 4) = TW.put 4 (TW.s32_at bs k).
Proof.
  intros bs k. unfold TW.put, TW.s32_at.
  rewrite <- (LMem.Z_to_le_bytes_mod 4 (TW.u_at bs k 4) 32),
    <- (LMem.Z_to_le_bytes_mod 4 (bv_swrap 32 (TW.u_at bs k 4)) 32) by lia.
  f_equal. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  rewrite (Z.mod_eq (TW.u_at bs k 4 + 2^31) (2^32)) by lia.
  replace (TW.u_at bs k 4 + 2 ^ 31 - 2 ^ 32 * ((TW.u_at bs k 4 + 2 ^ 31) / 2 ^ 32) - 2 ^ 31)
    with (TW.u_at bs k 4 + (- ((TW.u_at bs k 4 + 2 ^ 31) / 2 ^ 32)) * 2 ^ 32) by ring.
  symmetry. apply Z.mod_add. lia.
Qed.

Lemma wk_put8_u64 : forall v, 0 <= v -> TW.put 8 (TS0.u64 v) = TW.put 8 v.
Proof. intros v _. unfold TS0.u64. apply TWL.put_mod64. lia. Qed.

Lemma wk_refused_eq : forall Bw, TW.set_S_stats_refused Bw (TS0.u64 (TW.S_stats_refused Bw + 1)) =
  TW.upd Bw TW.A_S_stats_refused (TW.put 8 (TW.u_at Bw TW.A_S_stats_refused 8 + 1)).
Proof.
  intros Bw. unfold TW.set_S_stats_refused, TW.S_stats_refused, TS0.u64. rewrite TWL.put_mod64 by lia.
  reflexivity.
Qed.

(* ---- writes inside a whole world and the reads they keep ---- *)

Lemma wk_len_upd : forall (bs v : list byte) k, length bs = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= TW.W_LEN -> length (TW.upd bs k v) = Z.to_nat TW.W_LEN.
Proof.
  intros bs v k HB Hk Hl. rewrite TWL.length_upd; [exact HB | exact Hk |].
  rewrite HB. unfold TW.W_LEN in *. lia.
Qed.

(* The offsets of TWorld.v the stores and reads of this walk use. *)
Ltac wk_offs :=
  unfold TW.A_S_e1_named_us, TW.A_S_wake_acked, TW.A_S_wake_sent_us, TW.A_S_state, TW.A_S_notify,
    TW.A_S_inflight, TW.A_S_inflight_frame, TW.A_S_inflight_len, TW.A_S_inflight_counter,
    TW.A_S_inflight_retries, TW.A_S_inflight_sent_us, TW.A_S_stats_tx_wakes, TW.A_GOT_n, TW.A_M_fly_on,
    TW.A_M_fly_len, TW.A_Cmd_st, TW.A_Cmd_len, TW.OFF_M, TW.OFF_g_s, TW.OFF_g_cmd, TW.OFF_g_fail_next,
    TW.OFF_g_ncmd, TW.OFF_GOT, TW.W_LEN in *.

(* the arithmetic side goal of a write: lengths of put and of the lists the context gives, then the offsets *)
Ltac wk_arith :=
  rewrite ?TWL.length_put;
  repeat match goal with H : length ?x = _ |- context [length ?x] => rewrite H end;
  wk_offs; lia.

(* the length of an upd chain over a whole world the context gives *)
Ltac wk_len := first [ assumption | apply wk_len_upd; [wk_len | wk_arith | wk_arith] ].

Ltac wk_side :=
  repeat match goal with
  | |- context [length (TW.upd ?bs ?k ?v)] =>
      let L := fresh "L" in assert (L : length (TW.upd bs k v) = Z.to_nat TW.W_LEN) by wk_len; rewrite L; clear L
  end;
  wk_arith.

(* a read of the world outside every write of an upd chain *)
Ltac wk_out := repeat first [ rewrite TWL.u_at_upd_out by wk_side | rewrite TWL.s32_at_upd_out by wk_side ].

(* ---- the stores of :129-131 ---- *)

Lemma wk_w1_eq : forall Bw now, wake_w1 Bw now =
  TW.upd (TW.upd (TW.upd Bw TW.A_S_e1_named_us (TW.put 4 0)) TW.A_S_wake_acked (TW.put 4 0))
         TW.A_S_wake_sent_us (TW.put 8 now).
Proof. intros Bw now. reflexivity. Qed.

Lemma wk_w1_keep : forall Bw now, length Bw = Z.to_nat TW.W_LEN ->
  length (wake_w1 Bw now) = Z.to_nat TW.W_LEN /\
  TW.S_state (wake_w1 Bw now) = TW.S_state Bw /\
  TW.GOT_n (wake_w1 Bw now) = TW.GOT_n Bw /\
  TW.g_fail_next (wake_w1 Bw now) = TW.g_fail_next Bw /\
  TW.M_fly_on (wake_w1 Bw now) = TW.M_fly_on Bw /\
  TW.M_fly_len (wake_w1 Bw now) = TW.M_fly_len Bw /\
  TW.g_ncmd (wake_w1 Bw now) = TW.g_ncmd Bw /\
  (forall s, 0 <= s -> TW.Cmd_st (wake_w1 Bw now) s = TW.Cmd_st Bw s) /\
  (forall s, 0 <= s -> TW.Cmd_len (wake_w1 Bw now) s = TW.Cmd_len Bw s).
Proof.
  intros Bw now HB. rewrite wk_w1_eq.
  unfold TW.S_state, TW.GOT_n, TW.g_fail_next, TW.M_fly_on, TW.M_fly_len, TW.g_ncmd, TW.Cmd_st, TW.Cmd_len.
  split; [wk_len|].
  split; [wk_out; reflexivity|]. split; [wk_out; reflexivity|]. split; [wk_out; reflexivity|].
  split; [wk_out; reflexivity|]. split; [wk_out; reflexivity|]. split; [wk_out; reflexivity|].
  split; intros s Hs; wk_out; reflexivity.
Qed.

(* ---- send_control_m ---- *)

Lemma wk_sc_keep : forall I F Bw cmd ack B1 r f, length Bw = Z.to_nat TW.W_LEN ->
  TSS.send_control_m I F Bw cmd ack = Some (B1, (r, f)) ->
  length B1 = Z.to_nat TW.W_LEN /\ TW.S_state B1 = TW.S_state Bw /\ TW.GOT_n B1 = TW.GOT_n Bw.
Proof.
  intros I F Bw cmd ack B1 r f HB H.
  destruct (TOK.send_control_m_keep I F Bw cmd ack B1 (r, f) HB H) as [L _].
  destruct (TOK.send_control_m_keeps I F Bw cmd ack B1 (r, f) HB H) as (Hs & Hg & _).
  split; [exact L|]. split; [exact Hs | exact Hg].
Qed.

(* check_sent_frame accepts only a frame of at least SPEC_MIN_FRAME = 60 bytes (fuzz_transport.c:408, :417) *)
Lemma wk_csf_len : forall X fr Y u, TC.check_sent_frame_m X fr = Some (Y, u) -> 60 <= Z.of_nat (length fr).
Proof.
  intros X fr Y u H. unfold TC.check_sent_frame_m in H. cbv zeta in H. revert H.
  match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end; [intros H; discriminate H|].
  match goal with |- (if ?c then _ else _) = _ -> _ => destruct c eqn:E end; [intros H; discriminate H|].
  intros _.
  apply orb_false_iff in E as [E _]. apply orb_false_iff in E as [E _].
  apply negb_false_iff, Z.eqb_eq in E. rewrite E.
  match goal with |- context [if ?c then _ else _] => destruct c eqn:E2 end.
  - lazymatch goal with |- 60 <= ?m => change m with 60 end. lia.
  - apply Z.ltb_ge in E2. lazymatch type of E2 with ?m <= _ => change m with 60 in E2 end. lia.
Qed.

(* send_control's frame with no body: the two MACs, 18 header bytes and 30 zero bytes *)
Lemma wk_lib_frame_len : forall dst src send ack cmd mode,
  length (DLib.lib_frame dst src send ack 0 cmd 0 [] mode) = (length dst + length src + 48)%nat.
Proof.
  intros dst src send ack cmd mode. unfold DLib.lib_frame. rewrite !length_app, repeat_length.
  unfold DSpec.put16, DSpec.put32. cbn [length]. unfold DSpec.frame_len. cbn [length Z.of_nat]. lia.
Qed.

Lemma wk_sc_ret : forall I F Bw cmd ack B1 r f,
  TSS.send_control_m I F Bw cmd ack = Some (B1, (r, f)) ->
  -2^63 <= r < 2^63 /\ (0 <= r -> r = 0 /\ length f = 60%nat).
Proof.
  intros I F Bw cmd ack B1 r f H. unfold TSS.send_control_m in H. cbv zeta in H.
  lazymatch type of H with context [TN.diginet_frame_build_code ?b ?M ?md] =>
    assert (E : TN.diginet_frame_build_code b M md = -1 \/ TN.diginet_frame_build_code b M md = 60)
      by (unfold TN.diginet_frame_build_code; destruct (negb _); [left; reflexivity | right; vm_compute; reflexivity]);
    destruct E as [E|E]; rewrite E in H
  end.
  - change (-1 <? 0) with true in H. cbv iota in H. injection H as _ <- <-. split; [lia | intros Hr; lia].
  - change (60 <? 0) with false in H. cbv iota in H.
    destruct (TSS.send_raw_m _ _ _ _) as [[B2 r2]|] eqn:SR; [|discriminate H].
    injection H as _ <- <-.
    unfold TSS.send_raw_m, TSS.call_send in SR.
    destruct (TW.S_io_send Bw =? TI.ti_io_send I); cbv beta iota in SR; [|discriminate SR].
    destruct (TC.io_send_m I Bw _) as [[B3 r3]|] eqn:IO; cbv beta iota in SR; [|discriminate SR].
    pose proof (TIF.io_send_m_ret _ _ _ _ _ IO) as R3.
    assert (Hr2 : r2 = r3) by (destruct (r3 =? 0); injection SR as _ <-; reflexivity).
    subst r2. clear SR.
    unfold TC.io_send_m in IO. cbv zeta in IO.
    destruct (TC.check_sent_frame_m _ _) as [[B4 u4]|] eqn:CS; [|discriminate IO].
    apply wk_csf_len in CS. rewrite wk_lib_frame_len in CS |- *.
    pose proof (TWL.length_sub_le Bw TW.A_S_desk_mac 6) as L1.
    pose proof (TWL.length_sub_le Bw TW.A_S_cfg_host_mac 6) as L2.
    unfold TW.S_desk_mac, TW.S_cfg_host_mac in *. unfold TC.EIO in R3.
    split; [lia|]. intros Hr. split; lia.
Qed.

(* ---- the stores of :139-142 ---- *)

Lemma wk_w3_keep : forall B1 e2 now, length B1 = Z.to_nat TW.W_LEN -> length e2 = 60%nat ->
  length (wake_w2 B1 e2) = Z.to_nat TW.W_LEN /\
  length (wake_w3 B1 e2 now) = Z.to_nat TW.W_LEN /\
  TW.S_state (wake_w3 B1 e2 now) = TW.S_state B1 /\
  TW.GOT_n (wake_w3 B1 e2 now) = TW.GOT_n B1 /\
  TW.g_fail_next (wake_w3 B1 e2 now) = TW.g_fail_next B1.
Proof.
  intros B1 e2 now HB HL.
  unfold wake_w3, wake_w2. cbv zeta.
  unfold TW.set_S_inflight_sent_us, TW.set_S_inflight_retries, TW.set_S_inflight_counter, TW.set_S_inflight,
    TW.set_S_stats_tx_wakes, TW.set_S_inflight_len, TW.set_S_inflight_frame.
  unfold TW.S_state, TW.GOT_n, TW.g_fail_next.
  split; [wk_len|]. split; [wk_len|].
  split; [wk_out; reflexivity|]. split; [wk_out; reflexivity|]. wk_out; reflexivity.
Qed.

(* ---- set_state_m ---- *)

Lemma wk_set_state_keep : forall X v, length X = Z.to_nat TW.W_LEN ->
  length (TW.set_S_state X v) = Z.to_nat TW.W_LEN /\
  TW.GOT_n (TW.set_S_state X v) = TW.GOT_n X /\
  TW.g_fail_next (TW.set_S_state X v) = TW.g_fail_next X /\
  TW.S_notify (TW.set_S_state X v) = TW.S_notify X.
Proof.
  intros X v HX. unfold TW.set_S_state, TW.GOT_n, TW.g_fail_next, TW.S_notify.
  split; [wk_len|]. split; [wk_out; reflexivity|]. split; [wk_out; reflexivity|]. wk_out; reflexivity.
Qed.

Lemma wk_set_state_same : forall I F B st why B2 u,
  TW.S_state B = st -> TSS.set_state_m I F B st why = Some (B2, u) -> B2 = B.
Proof.
  intros I F B st why B2 u Hs H. unfold TSS.set_state_m in H. rewrite Hs, Z.eqb_refl in H.
  cbv beta iota zeta in H. injection H; intros; subst; reflexivity.
Qed.

Lemma wk_set_state_go : forall I F B st why B2 u,
  TW.S_state B <> st -> TSS.set_state_m I F B st why = Some (B2, u) ->
  TW.S_notify (TW.set_S_state B st) = TI.ti_notice I /\
  TC.notice_m I F (TW.set_S_state B st)
    (TI.Ntc TS0.DIGINET_N_STATE st (TW.S_state B) why 0 0 0 0 None [] 0) = Some (B2, tt).
Proof.
  intros I F B st why B2 u Hs H. unfold TSS.set_state_m in H.
  rewrite (proj2 (Z.eqb_neq _ _) Hs) in H. cbv beta iota zeta in H.
  unfold TSS.call_notify in H.
  destruct (TW.S_notify (TW.set_S_state B st) =? TI.ti_notice I) eqn:EN; cbv beta iota in H; [|discriminate H].
  apply Z.eqb_eq in EN. destruct u. split; [exact EN | exact H].
Qed.

(* ---- notice_m of a state change ---- *)

Lemma wk_fail_upd : forall B k n v, length B = Z.to_nat TW.W_LEN -> 0 <= k ->
  (k + Z.of_nat n <= TW.OFF_g_fail_next \/ TW.OFF_g_fail_next + 1 <= k) -> k + Z.of_nat n <= TW.W_LEN ->
  length (TW.upd B k (TW.put n v)) = Z.to_nat TW.W_LEN /\
  TW.g_fail_next (TW.upd B k (TW.put n v)) = TW.g_fail_next B.
Proof.
  intros B k n v LB H0 Hk Hn. unfold TW.OFF_g_fail_next, TW.W_LEN in *. split.
  - rewrite TWL.length_upd_put; [exact LB | lia | rewrite LB; lia].
  - unfold TW.g_fail_next. apply TWL.u_at_upd_out;
      [lia | unfold TW.OFF_g_fail_next; lia
      | rewrite TWL.length_put; unfold TW.OFF_g_fail_next; cbn; lia | rewrite TWL.length_put, LB; lia].
Qed.

Ltac wk_cf_side := unfold TW.OFF_GOT, TW.OFF_g_fail_next, TW.W_LEN in *; cbn; lia.

(* notice of a state change that is not to ONLINE writes GOT only: g_fail_next and the length are kept *)
Lemma wk_notice_keep : forall I Fr B B2 st old why, length B = Z.to_nat TW.W_LEN ->
  st <> TS0.DIGINET_S_ONLINE ->
  TC.notice_m I Fr B (TI.Ntc TS0.DIGINET_N_STATE st old why 0 0 0 0 None [] 0) = Some (B2, tt) ->
  TW.g_fail_next B2 = TW.g_fail_next B /\ length B2 = Z.to_nat TW.W_LEN.
Proof.
  intros I Fr B B2 st old why LB Hst HN.
  assert (Hst' : st <> TC.S_ONLINE) by exact Hst.
  unfold TC.notice_m in HN. cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason] in HN.
  replace (TS0.DIGINET_N_STATE =? TC.N_STATE) with true in HN by reflexivity.
  cbv beta iota zeta in HN.
  replace (st =? TC.S_ONLINE) with false in HN by (symmetry; apply Z.eqb_neq; exact Hst').
  destruct (TW.GOT_n B <? TC.TRANS_MAX) eqn:G1.
  - destruct (TW.GOT_n B <? 0) eqn:G2; cbv beta iota in HN; [discriminate HN|].
    destruct (TC.int_inc (TW.GOT_n B)) as [g1|]; cbv beta iota in HN; [|discriminate HN].
    injection HN as <-.
    apply Z.ltb_lt in G1. apply Z.ltb_ge in G2. unfold TC.TRANS_MAX in G1.
    unfold TW.set_GOT_n, TW.set_GOT_t_reason, TW.set_GOT_t_old, TW.set_GOT_t_state, TW.A_GOT_n,
      TW.A_GOT_t_reason, TW.A_GOT_t_old, TW.A_GOT_t_state.
    destruct (wk_fail_upd B (TW.OFF_GOT + 4 + 12 * TW.GOT_n B + 0) 4 st LB) as [L1 F1];
      [wk_cf_side | wk_cf_side | wk_cf_side |].
    destruct (wk_fail_upd _ (TW.OFF_GOT + 4 + 12 * TW.GOT_n B + 4) 4 old L1) as [L2 F2];
      [wk_cf_side | wk_cf_side | wk_cf_side |].
    destruct (wk_fail_upd _ (TW.OFF_GOT + 4 + 12 * TW.GOT_n B + 8) 4 why L2) as [L3 F3];
      [wk_cf_side | wk_cf_side | wk_cf_side |].
    destruct (wk_fail_upd _ (TW.OFF_GOT + 0) 4 g1 L3) as [L4 F4];
      [wk_cf_side | wk_cf_side | wk_cf_side |].
    split; [rewrite F4, F3, F2, F1; reflexivity | exact L4].
  - cbv beta iota in HN.
    destruct (TC.int_inc (TW.GOT_n B)) as [g1|]; cbv beta iota in HN; [|discriminate HN].
    injection HN as <-.
    unfold TW.set_GOT_n, TW.A_GOT_n.
    destruct (wk_fail_upd B (TW.OFF_GOT + 0) 4 g1 LB) as [L1 F1];
      [wk_cf_side | wk_cf_side | wk_cf_side |].
    split; [exact F1 | exact L1].
Qed.

(* Every frame the session sends is diginet_frame_build's output (DS:97-109 send_control, DS:388-401 send_data,
   and a retransmission resends one with its retry field rewritten, DS:403-412). Given L2 / L3 (Links.v), such
   a frame passes check_sent_frame (FT:398-420), check_ack_frame (FT:422-430) and check_latest_control
   (FT:599-607). Each lemma is stated over the few world facts the check reads (M_desk_known, M_desk,
   Cfg_sum_mode, g_rx_send, M_host_counter), for ANY world: at the callback the harness model has already run
   ahead of the library, so the simulation proofs apply them to the world of the moment. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SimLib.
Import ListNotations.
Open Scope Z_scope.

(* ---- small facts ---- *)

Lemma beq_bytes_refl : forall a, beq_bytes a a = true.
Proof. intros a. unfold beq_bytes. destruct (list_eq_dec Z.eq_dec (zs a) (zs a)); [reflexivity | contradiction]. Qed.

(* spec_read_frame on SPEC_OK: dst at 0, src at 6, the body at 30 (spec.h:209-217) *)
Lemma read_frame_ok_fields : forall b len, sf_code (spec_read_frame b len) = SPEC_OK ->
  sf_dst (spec_read_frame b len) = 0 /\ sf_src (spec_read_frame b len) = SPEC_MAC /\
  sf_body (spec_read_frame b len) = SPEC_BODY_AT.
Proof.
  intros b len. unfold spec_read_frame. cbv zeta.
  destruct (len <? SPEC_BODY_AT); [cbv; intros H; discriminate H|].
  destruct (negb (spec_be16 b 12 =? SPEC_ETHERTYPE)); [cbv; intros H; discriminate H|].
  destruct ((spec_be16 b SPEC_AT_NUMBYTES <? SPEC_HDR) || (len - SPEC_ETH_HDR <? spec_be16 b SPEC_AT_NUMBYTES));
    [cbv; intros H; discriminate H|].
  intros _. cbn. auto.
Qed.

(* the harness's sum over the body inside the frame (spec_sum at f.body) is the sum of the body *)
Lemma sum_at_shift : forall fr body, (30 + length body <= length fr)%nat -> sub fr SPEC_BODY_AT (length body) = body ->
  spec_sum_at (zs fr) SPEC_BODY_AT (Z.of_nat (length body)) = spec_sum_at (zs body) 0 (Z.of_nat (length body)).
Proof.
  intros fr body Hl Hs. unfold spec_sum_at. rewrite Nat2Z.id. f_equal.
  change (spec_sum_loop (zs fr) SPEC_BODY_AT 0 0 (length body))
    with (spec_sum_loop (zs fr) (Z.of_nat 30) 0 (Z.of_nat 0) (length body)).
  change (spec_sum_loop (zs body) 0 0 0 (length body))
    with (spec_sum_loop (zs body) (Z.of_nat 0) 0 (Z.of_nat 0) (length body)).
  rewrite (lk_sum_loop (zs fr) fr (holds_body_map fr) (length body) 0 30 0) by lia.
  rewrite (lk_sum_loop (zs body) body (holds_body_map body) (length body) 0 0 0) by lia.
  rewrite Nat.add_0_r. cbn [Nat.add skipn]. rewrite firstn_all.
  unfold sub, SPEC_BODY_AT in Hs. change (Z.to_nat 30) with 30%nat in Hs. rewrite Hs. reflexivity.
Qed.

(* ---- the frame diginet_frame_build makes, read back (L2) ---- *)

(* the hypotheses of L2 for lib_frame dst src send ack retry cmd ncmds body mode *)
Definition build_ok (dst src : list byte) (send ack retry cmd ncmds : Z) (body : list byte) (mode : Z) : Prop :=
  length dst = 6%nat /\ length src = 6%nat /\ (mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO) /\
  0 <= send < 2 ^ 32 /\ 0 <= ack < 2 ^ 32 /\ 0 <= retry < 2 ^ 16 /\ 0 <= cmd < 2 ^ 8 /\ 0 <= ncmds < 2 ^ 8 /\
  (length body <= 1484)%nat /\ body_check body = DIGINET_OK.

Lemma rf_lib_frame : forall (HL : links) dst src send ack retry cmd ncmds body mode,
  build_ok dst src send ack retry cmd ncmds body mode ->
  let f := lib_frame dst src send ack retry cmd ncmds body mode in
  Z.of_nat (length f) = frame_len (length body) /\
  sf_code (rf f) = SPEC_OK /\ sf_dst (rf f) = 0 /\ sf_src (rf f) = SPEC_MAC /\ sf_body (rf f) = SPEC_BODY_AT /\
  sf_cmd (rf f) = cmd /\ sf_send (rf f) = send /\ sf_ack (rf f) = ack /\ sf_retry (rf f) = retry /\
  sf_ncmds (rf f) = ncmds /\ sf_body_len (rf f) = Z.of_nat (length body) /\
  sub f SPEC_BODY_AT (length body) = body /\ sub f 0 6 = dst /\ sub f SPEC_MAC 6 = src /\
  forallb (fun x => bz x =? 0) (skipn (Z.to_nat (SPEC_BODY_AT + Z.of_nat (length body))) f) = true /\
  sf_sum (rf f) = (if mode =? DIGINET_SUM_ZERO then 0 else spec_sum_at (zs body) 0 (Z.of_nat (length body))).
Proof.
  intros HL dst src send ack retry cmd ncmds body mode
    (Hd & Hs & Hm & Hsend & Hack & Hretry & Hcmd & Hncmds & Hbl & Hbc).
  destruct HL as (_ & L2 & _).
  destruct (L2 dst src send ack retry cmd ncmds body (frame_len (length body)) mode
              Hd Hs Hm Hsend Hack Hretry Hcmd Hncmds) as (A & _ & _).
  assert (Hb : Z.of_nat (length body) <= DIGINET_MAX_BODY_LEN) by (unfold DIGINET_MAX_BODY_LEN; lia).
  specialize (A Hb Hbc (Z.le_refl _)). cbv zeta in A.
  destruct A as (_ & Hlen & Hc & Hsd & Hss & Hcm & Hse & Hak & Hre & Hnc & Hbln & Hsub & Hz & Hsum).
  cbv zeta. unfold rf. rewrite Hlen.
  destruct (read_frame_ok_fields _ _ Hc) as (F1 & F2 & F3).
  rewrite F1 in Hsd. rewrite F2 in Hss.
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: assumption.
Qed.

(* the build's code (DS:101-103, :393-396): the frame length *)
Lemma build_code_ok : forall (HL : links) dst src send ack retry cmd ncmds body mode cap,
  build_ok dst src send ack retry cmd ncmds body mode -> frame_len (length body) <= cap ->
  diginet_frame_build_code body cap mode = frame_len (length body).
Proof.
  intros HL dst src send ack retry cmd ncmds body mode cap
    (Hd & Hs & Hm & Hsend & Hack & Hretry & Hcmd & Hncmds & Hbl & Hbc) Hcap.
  destruct HL as (_ & L2 & _).
  destruct (L2 dst src send ack retry cmd ncmds body cap mode
              Hd Hs Hm Hsend Hack Hretry Hcmd Hncmds) as (A & _ & _).
  assert (Hb : Z.of_nat (length body) <= DIGINET_MAX_BODY_LEN) by (unfold DIGINET_MAX_BODY_LEN; lia).
  specialize (A Hb Hbc Hcap). cbv zeta in A. exact (proj1 A).
Qed.

(* check_sent_frame (FT:398-420) passes on such a frame, in any world whose desk is the frame's dst *)
Lemma sent_frame_ok : forall (HL : links) (Bc : list byte) dst src send ack retry cmd ncmds body mode,
  build_ok dst src send ack retry cmd ncmds body mode ->
  src = HOST -> M_desk_known Bc = 1 -> M_desk Bc = dst -> Cfg_sum_mode Bc = mode ->
  check_sent_frame_m Bc (lib_frame dst src send ack retry cmd ncmds body mode) = Some (Bc, tt).
Proof.
  intros HL Bc dst src send ack retry cmd ncmds body mode Hok Hsrc Hknown Hdesk Hmode. subst src.
  pose proof (rf_lib_frame HL dst HOST send ack retry cmd ncmds body mode Hok) as R. cbv zeta in R.
  destruct R as (Hlen & Hc & Hd0 & Hs6 & Hb30 & _ & _ & _ & _ & _ & Hbl & Hsub & Hsubd & Hsubs & Hz & Hsum).
  destruct Hok as (_ & _ & _ & _ & _ & _ & _ & _ & Hlb & Hbc).
  set (fr := lib_frame dst HOST send ack retry cmd ncmds body mode) in *.
  assert (Hlfr : (30 + length body <= length fr)%nat) by (unfold frame_len in Hlen; lia).
  (* the system family test, by L3 on the bytes from the body on *)
  assert (Hsys : spec_system_at (zs (skipn 30 fr)) (Z.of_nat (length body)) < 0).
  { destruct HL as (_ & _ & L3 & _).
    assert (Hn : 0 <= Z.of_nat (length body) <= Z.of_nat (length (skipn 30 fr)))
      by (rewrite length_skipn; lia).
    destruct (L3 (skipn 30 fr) (Z.of_nat (length body)) Hn) as (E & _ & _).
    apply E. rewrite Nat2Z.id. unfold sub, SPEC_BODY_AT in Hsub. change (Z.to_nat 30) with 30%nat in Hsub.
    rewrite Hsub. exact Hbc. }
  unfold check_sent_frame_m. cbv zeta.
  rewrite Hc, Hs6, Hsubs, Hd0, Hsubd, Hbl, Hb30, Hlen, Hknown, Hdesk, Hmode.
  rewrite !beq_bytes_refl, Z.eqb_refl.
  change (Z.to_nat SPEC_BODY_AT) with 30%nat.
  destruct (Z.leb_spec 0 (spec_system_at (zs (skipn 30 fr)) (Z.of_nat (length body)))) as [Hx|Hx]; [lia|].
  rewrite Hz.
  assert (En : (frame_len (length body) =?
                (if SPEC_BODY_AT + Z.of_nat (length body) <? SPEC_MIN_FRAME then SPEC_MIN_FRAME
                 else SPEC_BODY_AT + Z.of_nat (length body))) = true).
  { unfold frame_len, SPEC_BODY_AT, SPEC_MIN_FRAME.
    destruct (Z.ltb_spec (30 + Z.of_nat (length body)) 60); apply Z.eqb_eq; lia. }
  rewrite En.
  rewrite (sum_at_shift fr body Hlfr Hsub), Hsum, Z.eqb_refl.
  reflexivity.
Qed.

(* check_ack_frame (FT:422-430): the ACK of the frame the operation handed over (FT:1002-1008),
   no body, retry 0 *)
Lemma ack_frame_ok : forall (HL : links) (Bc : list byte) dst src send ack cmd mode,
  build_ok dst src send ack 0 cmd 0 [] mode -> ack = g_rx_send Bc ->
  check_ack_frame_m Bc (lib_frame dst src send ack 0 cmd 0 [] mode) = Some (Bc, tt).
Proof.
  intros HL Bc dst src send ack cmd mode Hok Hack.
  pose proof (rf_lib_frame HL dst src send ack 0 cmd 0 [] mode Hok) as R. cbv zeta in R.
  destruct R as (_ & _ & _ & _ & _ & _ & _ & Hak & Hre & _ & Hbl & _).
  unfold check_ack_frame_m. cbv zeta. rewrite Hak, Hre, Hbl, Hack, Z.eqb_refl. reflexivity.
Qed.

(* check_latest_control (FT:599-607): send_control's counter is s->host_counter, unchanged (DS:100) *)
Lemma latest_control_ok : forall (HL : links) (Bc : list byte) dst src send ack retry cmd ncmds body mode,
  build_ok dst src send ack retry cmd ncmds body mode -> send = M_host_counter Bc ->
  check_latest_control_m Bc (lib_frame dst src send ack retry cmd ncmds body mode) = Some (Bc, tt).
Proof.
  intros HL Bc dst src send ack retry cmd ncmds body mode Hok Hs.
  pose proof (rf_lib_frame HL dst src send ack retry cmd ncmds body mode Hok) as R. cbv zeta in R.
  destruct R as (_ & _ & _ & _ & _ & _ & Hse & _).
  unfold check_latest_control_m. rewrite Hse, Hs, Z.eqb_refl. reflexivity.
Qed.

(* the control frame of send_control (DS:99-105): no body, ncmds 0, retry 0, in the 60-byte buffer *)
Lemma control_build_ok : forall dst src send ack cmd mode,
  length dst = 6%nat -> length src = 6%nat -> (mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO) ->
  0 <= send < 2 ^ 32 -> 0 <= ack < 2 ^ 32 -> 0 <= cmd < 2 ^ 8 ->
  build_ok dst src send ack 0 cmd 0 [] mode.
Proof.
  intros dst src send ack cmd mode Hd Hs Hm Hse Hak Hc.
  unfold build_ok. repeat match goal with |- _ /\ _ => split end.
  all: first [assumption | (cbn [length]; lia) | reflexivity | (vm_compute; reflexivity)].
Qed.

Lemma control_frame_ok : forall (HL : links) (Bc : list byte) dst src send ack cmd mode,
  build_ok dst src send ack 0 cmd 0 [] mode ->
  diginet_frame_build_code [] DIGINET_MIN_FRAME_LEN mode = DIGINET_MIN_FRAME_LEN /\
  length (lib_frame dst src send ack 0 cmd 0 [] mode) = 60%nat /\
  (src = HOST -> M_desk_known Bc = 1 -> M_desk Bc = dst -> Cfg_sum_mode Bc = mode ->
   check_sent_frame_m Bc (lib_frame dst src send ack 0 cmd 0 [] mode) = Some (Bc, tt)).
Proof.
  intros HL Bc dst src send ack cmd mode Hok.
  split; [exact (build_code_ok HL dst src send ack 0 cmd 0 [] mode DIGINET_MIN_FRAME_LEN Hok ltac:(cbv; discriminate))|].
  split.
  - pose proof (rf_lib_frame HL dst src send ack 0 cmd 0 [] mode Hok) as R. cbv zeta in R.
    destruct R as (Hlen & _). cbn [length] in Hlen. unfold frame_len in Hlen. cbn in Hlen. lia.
  - intros. apply sent_frame_ok; assumption.
Qed.

(* ---- a retransmission (DS:403-412) changes only the retry field, bytes 26-27 ---- *)

(* lib_frame = the 26 bytes before the retry field, the field, the rest *)
Definition lib_head (dst src : list byte) (send ack : Z) (body : list byte) (mode : Z) : list byte :=
  dst ++ src ++ put16 0x885f ++ put16 ((16 + Z.of_nat (length body)) mod 2 ^ 16) ++
  put16 (if mode =? 0 then lib_sum16 body else 0) ++ put32 (send mod 2 ^ 32) ++ put32 (ack mod 2 ^ 32).
Definition lib_tail (cmd ncmds : Z) (body : list byte) : list byte :=
  [b8 cmd; b8 ncmds] ++ body ++
  repeat (b8 0) (Z.to_nat (frame_len (length body) - (30 + Z.of_nat (length body)))).

Lemma lib_frame_split : forall dst src send ack retry cmd ncmds body mode,
  lib_frame dst src send ack retry cmd ncmds body mode =
  lib_head dst src send ack body mode ++ put16 (retry mod 2 ^ 16) ++ lib_tail cmd ncmds body.
Proof. intros. unfold lib_frame, lib_head, lib_tail. rewrite <- !app_assoc. reflexivity. Qed.

Lemma length_lib_head : forall dst src send ack body mode, length dst = 6%nat -> length src = 6%nat ->
  length (lib_head dst src send ack body mode) = 26%nat.
Proof. intros dst src send ack body mode Hd Hs. unfold lib_head. rewrite !length_app, Hd, Hs. reflexivity. Qed.

Lemma lib_frame_retry_head : forall dst src send ack retry cmd ncmds body mode,
  length dst = 6%nat -> length src = 6%nat ->
  firstn 26 (lib_frame dst src send ack retry cmd ncmds body mode) = lib_head dst src send ack body mode.
Proof.
  intros dst src send ack retry cmd ncmds body mode Hd Hs. rewrite lib_frame_split, firstn_app.
  rewrite length_lib_head by assumption. rewrite Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
  rewrite <- (length_lib_head dst src send ack body mode Hd Hs) at 1. apply firstn_all.
Qed.

Lemma lib_frame_retry_field : forall dst src send ack retry cmd ncmds body mode,
  length dst = 6%nat -> length src = 6%nat ->
  sub (lib_frame dst src send ack retry cmd ncmds body mode) 26 2 = put16 (retry mod 2 ^ 16).
Proof.
  intros dst src send ack retry cmd ncmds body mode Hd Hs. unfold sub. rewrite lib_frame_split.
  change (Z.to_nat 26) with 26%nat.
  rewrite <- (length_lib_head dst src send ack body mode Hd Hs), skipn_app, skipn_all, Nat.sub_diag.
  cbn [app skipn]. reflexivity.
Qed.

Lemma lib_frame_retry_tail : forall dst src send ack retry cmd ncmds body mode,
  length dst = 6%nat -> length src = 6%nat ->
  skipn 28 (lib_frame dst src send ack retry cmd ncmds body mode) = lib_tail cmd ncmds body.
Proof.
  intros dst src send ack retry cmd ncmds body mode Hd Hs. rewrite lib_frame_split.
  replace 28%nat with (2 + length (lib_head dst src send ack body mode))%nat
    by (rewrite length_lib_head by assumption; reflexivity).
  rewrite <- skipn_skipn, skipn_app, skipn_all, Nat.sub_diag. cbn [app skipn]. reflexivity.
Qed.

(* two frames that differ in the retry field only agree outside bytes 26-27 *)
Lemma lib_frame_retry_same : forall dst src send ack r1 r2 cmd ncmds body mode,
  length dst = 6%nat -> length src = 6%nat ->
  firstn 26 (lib_frame dst src send ack r1 cmd ncmds body mode) =
  firstn 26 (lib_frame dst src send ack r2 cmd ncmds body mode) /\
  skipn 28 (lib_frame dst src send ack r1 cmd ncmds body mode) =
  skipn 28 (lib_frame dst src send ack r2 cmd ncmds body mode).
Proof.
  intros. rewrite !lib_frame_retry_head, !lib_frame_retry_tail by assumption. split; reflexivity.
Qed.

(* ---- io_send (FT:823-899) of the ACK on_data sends (DS:242, send_control DS:97-109) ----
   The result world is the explicit write chain io_send_m makes on that path: g_fail_next := 0 (FT:829), then
   GOT.acks + 1 (FT:834); its return value is -EIO when g_fail_next was set (FT:898). *)

Local Ltac cnum :=
  unfold A_M_desk_known, A_M_desk, A_Cfg_sum_mode, A_GOT_acks, A_M_host_counter,
    OFF_M, OFF_g_cfg, OFF_GOT, OFF_g_fail_next, OFF_g_rx_send, W_LEN in *; lia.

Lemma io_send_ack_ok : forall (HL : links) (I : timg) (B : list byte) dst src send ack mode,
  length B = Z.to_nat W_LEN ->
  build_ok dst src send ack 0 SPEC_CMD_ACK 0 [] mode -> src = HOST ->
  M_desk_known B = 1 -> M_desk B = dst -> Cfg_sum_mode B = mode ->
  ack = g_rx_send B -> send = M_host_counter B -> GOT_acks B <> INT_MAX ->
  io_send_m I B (lib_frame dst src send ack 0 SPEC_CMD_ACK 0 [] mode) =
  Some (set_GOT_acks (set_g_fail_next B 0) (GOT_acks B + 1), if truth (g_fail_next B) then - EIO else 0).
Proof.
  intros HL I B dst src send ack mode Hlen Hok Hsrc Hknown Hdesk Hmode Hack Hsend Hgot. subst src.
  pose proof (rf_lib_frame HL dst HOST send ack 0 SPEC_CMD_ACK 0 [] mode Hok) as R. cbv zeta in R.
  destruct R as (_ & _ & _ & _ & _ & Hcm & _).
  set (fr := lib_frame dst HOST send ack 0 SPEC_CMD_ACK 0 [] mode) in *.
  set (B0 := set_g_fail_next B 0).
  set (B1 := set_GOT_acks B0 (GOT_acks B + 1)).
  assert (L0 : length B0 = length B)
    by (apply length_upd_put; [cnum | rewrite Hlen; cnum]).
  (* the reads of the checks, through the writes *)
  assert (K0 : M_desk_known B0 = 1).
  { transitivity (M_desk_known B); [|exact Hknown]. unfold M_desk_known.
    apply wr_s32_upd_disj; [cnum | cnum | rewrite Hlen; cnum | vm_compute; reflexivity]. }
  assert (D0 : M_desk B0 = dst).
  { transitivity (M_desk B); [|exact Hdesk]. unfold M_desk.
    apply wr_sub_upd_disj; [cnum | cnum | rewrite Hlen; cnum | vm_compute; reflexivity]. }
  assert (S0 : Cfg_sum_mode B0 = mode).
  { transitivity (Cfg_sum_mode B); [|exact Hmode]. unfold Cfg_sum_mode.
    apply wr_s32_upd_disj; [cnum | cnum | rewrite Hlen; cnum | vm_compute; reflexivity]. }
  assert (G0 : GOT_acks B0 = GOT_acks B).
  { unfold GOT_acks. apply wr_s32_upd_disj; [cnum | cnum | rewrite Hlen; cnum | vm_compute; reflexivity]. }
  assert (R0 : g_rx_send B1 = g_rx_send B).
  { transitivity (g_rx_send B0); unfold g_rx_send.
    - apply wr_u_upd_disj; [cnum | cnum | rewrite L0, Hlen; cnum | vm_compute; reflexivity].
    - apply wr_u_upd_disj; [cnum | cnum | rewrite Hlen; cnum | vm_compute; reflexivity]. }
  assert (H0 : M_host_counter B1 = M_host_counter B).
  { transitivity (M_host_counter B0); unfold M_host_counter.
    - apply wr_u_upd_disj; [cnum | cnum | rewrite L0, Hlen; cnum | vm_compute; reflexivity].
    - apply wr_u_upd_disj; [cnum | cnum | rewrite Hlen; cnum | vm_compute; reflexivity]. }
  (* the three checks *)
  pose proof (sent_frame_ok HL B0 dst HOST send ack 0 SPEC_CMD_ACK 0 [] mode Hok eq_refl K0 D0 S0) as CS.
  pose proof (ack_frame_ok HL B1 dst HOST send ack SPEC_CMD_ACK mode Hok (eq_trans Hack (eq_sym R0))) as CA.
  pose proof (latest_control_ok HL B1 dst HOST send ack 0 SPEC_CMD_ACK 0 [] mode Hok (eq_trans Hsend (eq_sym H0)))
    as CL.
  change (lib_frame dst HOST send ack 0 SPEC_CMD_ACK 0 [] mode) with fr in CS, CA, CL.
  unfold io_send_m. cbv zeta.
  change (set_g_fail_next B 0) with B0.
  rewrite CS. cbv beta iota.
  rewrite Hcm, (Z.eqb_refl SPEC_CMD_ACK). cbv beta iota.
  unfold int_inc. rewrite G0.
  destruct (Z.eqb_spec (GOT_acks B) INT_MAX) as [E|_]; [contradiction|]. cbv beta iota.
  change (set_GOT_acks B0 (GOT_acks B + 1)) with B1.
  rewrite CA. cbv beta iota. rewrite CL. cbv beta iota.
  reflexivity.
Qed.

(* ---- the frame in flight (agree_fly.b8_frames) gives the B8 frame facts and M1 / M13 ----
   Both copies are lib_frame of one accepted body: L2's hypotheses hold for them, so each passes
   check_sent_frame (code OK, src HOST, dst M_desk, no system family in the body (M1), length max(60, 30 +
   body_len) with zero padding (M13), the sum of Cfg_sum_mode), M's copy reads retry 0 and S's copy the retry
   count, both cmd M_fly_cmd and send M_fly_counter. *)
Lemma fly_frames_ok : forall (B : list byte), length B = Z.to_nat W_LEN ->
  agree_cfg B -> agree_st B -> agree_fly B -> M_fly_on B = 1 ->
  M_desk_known B = 1 /\ exists body ncmds,
    build_ok (M_desk B) HOST (M_fly_counter B) 0 0 (M_fly_cmd B) ncmds body (Cfg_sum_mode B) /\
    build_ok (M_desk B) HOST (M_fly_counter B) 0 (M_fly_retries B) (M_fly_cmd B) ncmds body (Cfg_sum_mode B) /\
    M_fly_len B = frame_len (length body) /\
    sub B A_M_fly_frame (Z.to_nat (M_fly_len B)) =
      lib_frame (M_desk B) HOST (M_fly_counter B) 0 0 (M_fly_cmd B) ncmds body (Cfg_sum_mode B) /\
    sub B A_S_inflight_frame (Z.to_nat (M_fly_len B)) =
      lib_frame (M_desk B) HOST (M_fly_counter B) 0 (M_fly_retries B) (M_fly_cmd B) ncmds body (Cfg_sum_mode B).
Proof.
  intros B Hlen Hcfg Hst Hfly Hon.
  split; [exact (b9_known _ Hst (b8_state _ Hfly Hon))|].
  destruct (b8_frames _ Hfly Hon) as (body & ncmds & Hbl & Hbc & Hnc & Hfl & HM & HS).
  exists body, ncmds.
  assert (Hd : length (M_desk B) = 6%nat)
    by (unfold M_desk; apply length_sub; [unfold A_M_desk, OFF_M; lia | rewrite Hlen; unfold A_M_desk, OFF_M, W_LEN; lia]).
  assert (Hc : 0 <= M_fly_counter B < 2 ^ 32).
  { unfold M_fly_counter. pose proof (u_at_range B A_M_fly_counter 4) as H.
    change (8 * Z.of_nat 4) with 32 in H. exact H. }
  assert (Hr : 0 <= M_fly_retries B < 2 ^ 16).
  { pose proof (b8_retries_le _ Hfly Hon). pose proof (a1_max_retries _ Hcfg).
    unfold M_fly_retries in *. pose proof (u_at_range B A_M_fly_retries 4). lia. }
  assert (Hcmd : 0 <= M_fly_cmd B < 2 ^ 8)
    by (destruct (b8_cmd _ Hfly Hon) as [E|E]; rewrite E; unfold SPEC_CMD_E2, SPEC_CMD_DATA; lia).
  pose proof (a1_sum_mode _ Hcfg) as Hm.
  assert (H2 : 0 <= 0 < 2 ^ 32) by (split; [lia | vm_compute; reflexivity]).
  assert (H3 : 0 <= 0 < 2 ^ 16) by (split; [lia | vm_compute; reflexivity]).
  unfold build_ok.
  split; [exact (conj Hd (conj eq_refl (conj Hm (conj Hc (conj H2 (conj H3 (conj Hcmd (conj Hnc
                   (conj Hbl Hbc)))))))))|].
  split; [exact (conj Hd (conj eq_refl (conj Hm (conj Hc (conj H2 (conj Hr (conj Hcmd (conj Hnc
                   (conj Hbl Hbc)))))))))|].
  split; [exact Hfl|]. split; [exact HM | exact HS].
Qed.

(* the two copies pass check_sent_frame in any world whose desk and sum mode are B's (the world of the moment at
   a retransmission), with the retry fields 0 and M_fly_retries *)
Lemma fly_sent_ok : forall (HL : links) (B Bc : list byte), length B = Z.to_nat W_LEN ->
  agree_cfg B -> agree_st B -> agree_fly B -> M_fly_on B = 1 ->
  M_desk_known Bc = 1 -> M_desk Bc = M_desk B -> Cfg_sum_mode Bc = Cfg_sum_mode B ->
  let fm := sub B A_M_fly_frame (Z.to_nat (M_fly_len B)) in
  let fs := sub B A_S_inflight_frame (Z.to_nat (M_fly_len B)) in
  check_sent_frame_m Bc fm = Some (Bc, tt) /\ check_sent_frame_m Bc fs = Some (Bc, tt) /\
  sf_retry (rf fm) = 0 /\ sf_retry (rf fs) = M_fly_retries B /\
  sf_cmd (rf fm) = M_fly_cmd B /\ sf_cmd (rf fs) = M_fly_cmd B /\
  sf_send (rf fm) = M_fly_counter B /\ sf_send (rf fs) = M_fly_counter B /\
  Z.of_nat (length fm) = M_fly_len B /\ Z.of_nat (length fs) = M_fly_len B.
Proof.
  intros HL B Bc Hlen Hcfg Hst Hfly Hon Hk Hd Hm. cbv zeta.
  destruct (fly_frames_ok B Hlen Hcfg Hst Hfly Hon) as (_ & body & ncmds & Ok0 & Okr & Hfl & HM & HS).
  rewrite HM, HS.
  pose proof (rf_lib_frame HL _ _ _ _ _ _ _ _ _ Ok0) as R0. cbv zeta in R0.
  pose proof (rf_lib_frame HL _ _ _ _ _ _ _ _ _ Okr) as Rr. cbv zeta in Rr.
  destruct R0 as (L0 & _ & _ & _ & _ & C0 & S0 & _ & T0 & _).
  destruct Rr as (Lr & _ & _ & _ & _ & Cr & Sr & _ & Tr & _).
  split; [exact (sent_frame_ok HL Bc _ _ _ _ _ _ _ _ _ Ok0 eq_refl Hk Hd Hm)|].
  split; [exact (sent_frame_ok HL Bc _ _ _ _ _ _ _ _ _ Okr eq_refl Hk Hd Hm)|].
  rewrite Hfl. exact (conj T0 (conj Tr (conj C0 (conj Cr (conj S0 (conj Sr (conj L0 Lr))))))).
Qed.

(* tt_send_stage: TSess.send_data_m on a body diginet_body_check accepts (at most 1484 bytes, a sum mode the build
   takes) is send_raw_m on the world TickTakeW.w_send and the frame TickTakeW.w_fr: DS:391 host_counter, :393-396
   the build succeeds with the frame length, :390-397 the frame into inflight_frame and its length into
   inflight_len, :398 inflight_start (DS:111-117), :399 stats.tx_data, :400 the frame read back from inflight_frame.
   tt_send_facts: the length, the frame (R_ss) and the fields of w_send that the simulation reads.
   TRAP (SettleOk.v, TickTakeW.v): no rewrite whose left side is absent, no `rewrite !`/`?` on world goals, no
   simpl/cbn without a constant list; the worlds of the main proof are abstracted (remember / generalize) and every
   closing reflexivity is guarded by a syntactic `?a = ?a` match. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links QueueFacts SimLib SendOk SettleOk
  TickDefs TakeOk TickTakeW.
Import ListNotations.
Open Scope Z_scope.

(* reflexivity only on a goal whose two sides are syntactically the same term *)
Local Ltac ts_refl := lazymatch goal with |- ?a = ?a => reflexivity end.

(* w_send as its chain of upd *)
Local Ltac ts_unfold := unfold w_send; cbv beta zeta;
  unfold set_S_stats_tx_data, set_S_inflight_sent_us, set_S_inflight_retries, set_S_inflight_counter,
    set_S_inflight, set_S_inflight_len, set_S_inflight_frame, set_S_host_counter.

(* ---------------------------------------------------------------- the frame *)

Lemma ts_fl_bound : forall body : list byte, (length body <= 1484)%nat -> 60 <= frame_len (length body) <= 1514.
Proof. intros body H. unfold frame_len. lia. Qed.

(* the hypotheses of L2 for the frame of DS:390-397 *)
Lemma ts_build_ok : forall B2 body n, length B2 = WN -> (length body <= 1484)%nat -> body_check body = DIGINET_OK ->
  (S_cfg_sum_mode B2 = DIGINET_SUM_BODY \/ S_cfg_sum_mode B2 = DIGINET_SUM_ZERO) ->
  build_ok (S_desk_mac B2) (S_cfg_host_mac B2) (u32 (S_host_counter B2 + n)) 0 0 DIGINET_CMD_DATA (u8 n) body
    (S_cfg_sum_mode B2).
Proof.
  intros B2 body n HB Hbl Hbc Hm. unfold build_ok.
  split; [unfold S_desk_mac; apply w_length_sub; rewrite HB; tk_offs|].
  split; [unfold S_cfg_host_mac; apply w_length_sub; rewrite HB; tk_offs|].
  split; [exact Hm|].
  split; [unfold u32; apply Z.mod_pos_bound; lia|].
  split; [lia|].
  split; [lia|].
  split; [unfold DIGINET_CMD_DATA; lia|].
  split; [unfold u8; change (2 ^ 8) with 256; apply Z.mod_pos_bound; lia|].
  split; [exact Hbl | exact Hbc].
Qed.

Lemma ts_fr_len : forall (HL : links) B2 body n, length B2 = WN -> (length body <= 1484)%nat ->
  body_check body = DIGINET_OK -> (S_cfg_sum_mode B2 = DIGINET_SUM_BODY \/ S_cfg_sum_mode B2 = DIGINET_SUM_ZERO) ->
  Z.of_nat (length (w_fr B2 body n)) = frame_len (length body).
Proof.
  intros HL B2 body n HB Hbl Hbc Hm.
  pose proof (rf_lib_frame HL _ _ _ _ _ _ _ _ _ (ts_build_ok B2 body n HB Hbl Hbc Hm)) as R. cbv zeta in R.
  unfold w_fr. exact (proj1 R).
Qed.

(* ---------------------------------------------------------------- DS:391, the world B3 *)

Lemma ts_b3 : forall B2 v B3, B3 = set_S_host_counter B2 v -> length B2 = WN -> 0 <= v < 2 ^ 32 ->
  length B3 = WN /\ S_host_counter B3 = v /\ S_cfg_sum_mode B3 = S_cfg_sum_mode B2 /\
  S_desk_mac B3 = S_desk_mac B2 /\ S_cfg_host_mac B3 = S_cfg_host_mac B2.
Proof.
  intros B2 v B3 -> HB Hv. unfold set_S_host_counter.
  split; [tk_len|].
  split; [unfold S_host_counter; apply tk_u_put_small; [tk_len | tk_offs | tk_offs |];
          change (8 * Z.of_nat 4) with 32; exact Hv|].
  split; [unfold S_cfg_sum_mode; tk_peel; ts_refl|].
  split; [unfold S_desk_mac; tk_peel; ts_refl|].
  unfold S_cfg_host_mac; tk_peel; ts_refl.
Qed.

(* DS:398: the counter inflight_start is called with, read after the frame and its length are written *)
Lemma ts_hc5 : forall B3 fr c, length B3 = WN -> Z.of_nat (length fr) <= 1514 ->
  S_host_counter (set_S_inflight_len (set_S_inflight_frame B3 fr) c) = S_host_counter B3.
Proof.
  intros B3 fr c HB Hf. unfold S_host_counter, set_S_inflight_len, set_S_inflight_frame.
  tk_peel; tk_peel; ts_refl.
Qed.

(* ---------------------------------------------------------------- w_send *)

Lemma ts_send_len : forall B2 body n now, length B2 = WN ->
  Z.of_nat (length (w_fr B2 body n)) = frame_len (length body) -> 60 <= frame_len (length body) <= 1514 ->
  length (w_send B2 body n now) = WN.
Proof. intros B2 body n now HB Hf Hfl. ts_unfold. tk_len. Qed.

Lemma ts_send_frame : forall B2 body n now, length B2 = WN ->
  Z.of_nat (length (w_fr B2 body n)) = frame_len (length body) -> 60 <= frame_len (length body) <= 1514 ->
  wframe R_ss B2 (w_send B2 body n now).
Proof. intros B2 body n now HB Hf Hfl. ts_unfold. tk_fr. Qed.

Lemma ts_send_hc : forall B2 body n now, length B2 = WN ->
  Z.of_nat (length (w_fr B2 body n)) = frame_len (length body) -> 60 <= frame_len (length body) <= 1514 ->
  S_host_counter (w_send B2 body n now) = u32 (S_host_counter B2 + n).
Proof.
  intros B2 body n now HB Hf Hfl. ts_unfold. unfold S_host_counter. repeat tk_peel.
  apply tk_u_put_small; [tk_len | tk_offs | tk_offs |].
  change (8 * Z.of_nat 4) with 32. unfold u32. apply Z.mod_pos_bound. lia.
Qed.

Lemma ts_send_on : forall B2 body n now, length B2 = WN ->
  Z.of_nat (length (w_fr B2 body n)) = frame_len (length body) -> 60 <= frame_len (length body) <= 1514 ->
  S_inflight (w_send B2 body n now) = 1.
Proof.
  intros B2 body n now HB Hf Hfl. ts_unfold. unfold S_inflight. repeat tk_peel.
  apply tk_s32_put; [tk_len | tk_offs | tk_offs | lia].
Qed.

Lemma ts_send_ctr : forall B2 body n now, length B2 = WN ->
  Z.of_nat (length (w_fr B2 body n)) = frame_len (length body) -> 60 <= frame_len (length body) <= 1514 ->
  S_inflight_counter (w_send B2 body n now) = u32 (S_host_counter B2 + n).
Proof.
  intros B2 body n now HB Hf Hfl. ts_unfold. unfold S_inflight_counter. repeat tk_peel.
  apply tk_u_put_small; [tk_len | tk_offs | tk_offs |].
  change (8 * Z.of_nat 4) with 32. unfold u32. apply Z.mod_pos_bound. lia.
Qed.

Lemma ts_send_ret : forall B2 body n now, length B2 = WN ->
  Z.of_nat (length (w_fr B2 body n)) = frame_len (length body) -> 60 <= frame_len (length body) <= 1514 ->
  S_inflight_retries (w_send B2 body n now) = 0.
Proof.
  intros B2 body n now HB Hf Hfl. ts_unfold. unfold S_inflight_retries. repeat tk_peel.
  apply tk_u_put_small; [tk_len | tk_offs | tk_offs |].
  change (8 * Z.of_nat 4) with 32. lia.
Qed.

Lemma ts_send_sent : forall B2 body n now, length B2 = WN ->
  Z.of_nat (length (w_fr B2 body n)) = frame_len (length body) -> 60 <= frame_len (length body) <= 1514 ->
  0 <= now < 2 ^ 64 -> S_inflight_sent_us (w_send B2 body n now) = now.
Proof.
  intros B2 body n now HB Hf Hfl Hnow. ts_unfold. unfold S_inflight_sent_us. repeat tk_peel.
  apply tk_u_put_small; [tk_len | tk_offs | tk_offs |].
  change (8 * Z.of_nat 8) with 64. exact Hnow.
Qed.

Lemma ts_send_flen : forall B2 body n now, length B2 = WN ->
  Z.of_nat (length (w_fr B2 body n)) = frame_len (length body) -> 60 <= frame_len (length body) <= 1514 ->
  S_inflight_len (w_send B2 body n now) = frame_len (length body).
Proof.
  intros B2 body n now HB Hf Hfl. ts_unfold. unfold S_inflight_len. repeat tk_peel.
  apply tk_u_put_small; [tk_len | tk_offs | tk_offs |].
  change (8 * Z.of_nat 8) with 64. lia.
Qed.

Lemma ts_send_sub : forall B2 body n now, length B2 = WN ->
  Z.of_nat (length (w_fr B2 body n)) = frame_len (length body) -> 60 <= frame_len (length body) <= 1514 ->
  sub (w_send B2 body n now) A_S_inflight_frame (Z.to_nat (frame_len (length body))) = w_fr B2 body n.
Proof.
  intros B2 body n now HB Hf Hfl. ts_unfold. repeat tk_peel.
  replace (Z.to_nat (frame_len (length body))) with (length (w_fr B2 body n)) by lia.
  apply tk_sub_same; [tk_len | tk_offs | tk_offs].
Qed.

(* DS:400: the inflight_len bytes at inflight_frame are the frame *)
Lemma ts_send_bytes : forall B2 body n now, length B2 = WN ->
  Z.of_nat (length (w_fr B2 body n)) = frame_len (length body) -> 60 <= frame_len (length body) <= 1514 ->
  inflight_bytes (w_send B2 body n now) = Some (w_fr B2 body n).
Proof.
  intros B2 body n now HB Hf Hfl.
  pose proof (ts_send_flen B2 body n now HB Hf Hfl) as E1.
  pose proof (ts_send_sub B2 body n now HB Hf Hfl) as E2.
  revert E1 E2. generalize (w_send B2 body n now) as W. intros W E1 E2.
  unfold inflight_bytes. rewrite E1.
  destruct (Z.ltb_spec 1514 (frame_len (length body))) as [Hx|_].
  - exfalso. clear - Hfl Hx. lia.
  - rewrite E2. ts_refl.
Qed.

(* ---------------------------------------------------------------- the stage *)

Lemma tt_send_stage : forall (HL : links) I F B2 body n now,
  length B2 = WN -> (length body <= 1484)%nat -> body_check body = DIGINET_OK ->
  (S_cfg_sum_mode B2 = DIGINET_SUM_BODY \/ S_cfg_sum_mode B2 = DIGINET_SUM_ZERO) ->
  send_data_m I F B2 body n now = send_raw_m I F (w_send B2 body n now) (w_fr B2 body n).
Proof.
  intros HL I F B2 body n now HB Hbl Hbc Hm.
  pose proof (ts_build_ok B2 body n HB Hbl Hbc Hm) as Hok.
  pose proof (ts_fr_len HL B2 body n HB Hbl Hbc Hm) as Hf.
  pose proof (ts_fl_bound body Hbl) as Hfl.
  (* DS:393-396: the build's code is the frame length *)
  assert (Hcode : diginet_frame_build_code body DIGINET_MAX_FRAME_LEN (S_cfg_sum_mode B2) = frame_len (length body)).
  { apply (build_code_ok HL _ _ _ _ _ _ _ _ _ _ Hok). unfold DIGINET_MAX_FRAME_LEN. lia. }
  pose proof (ts_send_bytes B2 body n now HB Hf Hfl) as Hby.
  assert (Hv : 0 <= u32 (S_host_counter B2 + n) < 2 ^ 32) by (unfold u32; apply Z.mod_pos_bound; lia).
  unfold send_data_m. cbv beta zeta.
  (* DS:391 *)
  remember (set_S_host_counter B2 (u32 (S_host_counter B2 + n))) as B3 eqn:E3.
  destruct (ts_b3 B2 _ B3 E3 HB Hv) as (HL3 & Hhc & Hmd & Hdm & Hhm).
  rewrite Hmd. rewrite Hcode.
  destruct (Z.ltb_spec (frame_len (length body)) 0) as [Hx|_]; [exfalso; lia|].
  cbv beta iota.
  (* DS:390-397: the frame is w_fr *)
  rewrite Hdm. rewrite Hhm. rewrite Hhc.
  change (lib_frame (S_desk_mac B2) (S_cfg_host_mac B2) (u32 (S_host_counter B2 + n)) 0 0 DIGINET_CMD_DATA
    (u8 n) body (S_cfg_sum_mode B2)) with (w_fr B2 body n).
  (* DS:398 *)
  rewrite (ts_hc5 B3 (w_fr B2 body n) (frame_len (length body)) HL3 ltac:(lia)). rewrite Hhc.
  unfold inflight_start_m. cbv beta iota zeta.
  (* DS:399: the world is w_send *)
  lazymatch goal with |- context [inflight_bytes ?W] =>
    replace W with (w_send B2 body n now) by (subst B3; unfold w_send; cbv beta zeta; ts_refl) end.
  (* DS:400 *)
  revert Hby. generalize (w_send B2 body n now) as W. intros W Hby.
  rewrite Hby. cbv beta iota. ts_refl.
Qed.

Lemma tt_send_facts : forall (HL : links) B2 body n now,
  length B2 = WN -> (length body <= 1484)%nat -> body_check body = DIGINET_OK ->
  (S_cfg_sum_mode B2 = DIGINET_SUM_BODY \/ S_cfg_sum_mode B2 = DIGINET_SUM_ZERO) -> 0 <= now < 2 ^ 64 ->
  length (w_send B2 body n now) = WN /\ wframe R_ss B2 (w_send B2 body n now) /\
  S_host_counter (w_send B2 body n now) = u32 (S_host_counter B2 + n) /\
  S_inflight (w_send B2 body n now) = 1 /\
  S_inflight_counter (w_send B2 body n now) = u32 (S_host_counter B2 + n) /\
  S_inflight_retries (w_send B2 body n now) = 0 /\
  S_inflight_sent_us (w_send B2 body n now) = now /\
  S_inflight_len (w_send B2 body n now) = frame_len (length body) /\
  Z.of_nat (length (w_fr B2 body n)) = frame_len (length body) /\
  sub (w_send B2 body n now) A_S_inflight_frame (Z.to_nat (frame_len (length body))) = w_fr B2 body n.
Proof.
  intros HL B2 body n now HB Hbl Hbc Hm Hnow.
  pose proof (ts_fr_len HL B2 body n HB Hbl Hbc Hm) as Hf.
  pose proof (ts_fl_bound body Hbl) as Hfl.
  split; [exact (ts_send_len B2 body n now HB Hf Hfl)|].
  split; [exact (ts_send_frame B2 body n now HB Hf Hfl)|].
  split; [exact (ts_send_hc B2 body n now HB Hf Hfl)|].
  split; [exact (ts_send_on B2 body n now HB Hf Hfl)|].
  split; [exact (ts_send_ctr B2 body n now HB Hf Hfl)|].
  split; [exact (ts_send_ret B2 body n now HB Hf Hfl)|].
  split; [exact (ts_send_sent B2 body n now HB Hf Hfl Hnow)|].
  split; [exact (ts_send_flen B2 body n now HB Hf Hfl)|].
  split; [exact Hf|].
  exact (ts_send_sub B2 body n now HB Hf Hfl).
Qed.

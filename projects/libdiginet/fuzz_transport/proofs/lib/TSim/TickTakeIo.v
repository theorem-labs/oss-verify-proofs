(* io_send (FT:823-899, TCb.io_send_m) on a DATA frame with retry 0 that diginet_frame_build made (DS:390-397):
   FT:829 g_fail_next := 0; check_sent_frame passes (SendOk.sent_frame_ok); FT:857 check_inflight_new passes;
   FT:858-865 the command count (tagged: the count loop over the body; raw: the frame's count); FT:866
   check_latest_frame passes; FT:867-868 M.host_counter, g_last_counter := the frame's counter (w_io8);
   tagged: FT:875-879 check_latest_sent and the display check (w_dispM); FT:883-889 the frame in flight (w_fly).
   The core lemmas tio_raw_core / tio_tagged_core take the frame as a variable with the facts the model reads;
   tt_io_raw / tt_io_tagged instantiate them with lib_frame through SendOk.rf_lib_frame.
   TRAP (SettleOk.v, TickTakeW.v): every rewrite below is of a subterm present in the goal, fully applied;
   no simpl / cbn without a constant list on a goal with world terms. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links QueueFacts SimLib SendOk SettleOk
  TickDefs TakeOk TickTakeW.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the frame's body *)

Lemma tt_frame_body : forall dst src send ack retry cmd ncmds body mode, length dst = 6%nat -> length src = 6%nat ->
  skipn 30 (lib_frame dst src send ack retry cmd ncmds body mode) =
  body ++ repeat (b8 0) (Z.to_nat (frame_len (length body) - (30 + Z.of_nat (length body)))).
Proof.
  intros dst src send ack retry cmd ncmds body mode Hd Hs.
  transitivity (skipn 2 (skipn 28 (lib_frame dst src send ack retry cmd ncmds body mode))).
  { rewrite skipn_skipn. reflexivity. }
  rewrite (lib_frame_retry_tail dst src send ack retry cmd ncmds body mode Hd Hs).
  unfold lib_tail. cbn [skipn app]. reflexivity.
Qed.

Local Lemma tio_at8_app : forall (body pad : list byte), at8 body 0 <> 0 -> at8 (body ++ pad) 0 = at8 body 0.
Proof.
  intros [|b body'] pad H.
  - exfalso. apply H. vm_compute. reflexivity.
  - reflexivity.
Qed.

Local Lemma tio_firstn_app : forall (body pad : list byte),
  firstn (Z.to_nat (Z.of_nat (length body))) (body ++ pad) = body.
Proof.
  intros body pad. rewrite (Nat2Z.id (length body)), firstn_app, Nat.sub_diag, (firstn_all body).
  cbn [firstn]. apply app_nil_r.
Qed.

Local Lemma tio_max : forall n, (n <= 1484)%nat -> frame_len n <= SPEC_MAX_FRAME.
Proof. intros n H. unfold frame_len, SPEC_MAX_FRAME. lia. Qed.

(* ---------------------------------------------------------------- reads through g_fail_next := 0 (FT:829) *)

Local Lemma tio_fn_raw : forall B, length B = WN -> g_raw (set_g_fail_next B 0) = g_raw B.
Proof. intros B HB. unfold g_raw, set_g_fail_next. tk_peel. reflexivity. Qed.
Local Lemma tio_fn_state : forall B, length B = WN -> M_state (set_g_fail_next B 0) = M_state B.
Proof. intros B HB. unfold M_state, set_g_fail_next. tk_peel. reflexivity. Qed.
Local Lemma tio_fn_fly_on : forall B, length B = WN -> M_fly_on (set_g_fail_next B 0) = M_fly_on B.
Proof. intros B HB. unfold M_fly_on, set_g_fail_next. tk_peel. reflexivity. Qed.
Local Lemma tio_fn_backoff : forall B, length B = WN -> M_backoff_until (set_g_fail_next B 0) = M_backoff_until B.
Proof. intros B HB. unfold M_backoff_until, set_g_fail_next. tk_peel. reflexivity. Qed.
Local Lemma tio_fn_now : forall B, length B = WN -> g_now (set_g_fail_next B 0) = g_now B.
Proof. intros B HB. unfold g_now, set_g_fail_next. tk_peel. reflexivity. Qed.
Local Lemma tio_fn_max_body : forall B, length B = WN -> Cfg_max_body (set_g_fail_next B 0) = Cfg_max_body B.
Proof. intros B HB. unfold Cfg_max_body, set_g_fail_next. tk_peel. reflexivity. Qed.
Local Lemma tio_fn_max_cmds : forall B, length B = WN -> Cfg_max_cmds (set_g_fail_next B 0) = Cfg_max_cmds B.
Proof. intros B HB. unfold Cfg_max_cmds, set_g_fail_next. tk_peel. reflexivity. Qed.
Local Lemma tio_fn_host_counter : forall B, length B = WN -> M_host_counter (set_g_fail_next B 0) = M_host_counter B.
Proof. intros B HB. unfold M_host_counter, set_g_fail_next. tk_peel. reflexivity. Qed.
Local Lemma tio_fn_desk_known : forall B, length B = WN -> M_desk_known (set_g_fail_next B 0) = M_desk_known B.
Proof. intros B HB. unfold M_desk_known, set_g_fail_next. tk_peel. reflexivity. Qed.
Local Lemma tio_fn_desk : forall B, length B = WN -> M_desk (set_g_fail_next B 0) = M_desk B.
Proof. intros B HB. unfold M_desk, set_g_fail_next. tk_peel. reflexivity. Qed.
Local Lemma tio_fn_sum_mode : forall B, length B = WN -> Cfg_sum_mode (set_g_fail_next B 0) = Cfg_sum_mode B.
Proof. intros B HB. unfold Cfg_sum_mode, set_g_fail_next. tk_peel. reflexivity. Qed.

Local Lemma tio_io8_raw : forall B s, length B = WN -> g_raw (w_io8 B s) = g_raw B.
Proof.
  intros B s HB. unfold g_raw, w_io8, set_g_last_counter, set_M_host_counter, set_g_fail_next.
  tk_peel. tk_peel. tk_peel. reflexivity.
Qed.

(* ---------------------------------------------------------------- the checks *)

(* FT:432-448 *)
Local Lemma tio_inflight : forall B6, length B6 = WN -> M_state B6 = S_ONLINE -> M_fly_on B6 = 0 ->
  M_backoff_until B6 <= g_now B6 ->
  check_inflight_new_m (set_g_fail_next B6 0) = Some (set_g_fail_next B6 0, tt).
Proof.
  intros B6 HB Hs Hf Hb. unfold check_inflight_new_m.
  rewrite (tio_fn_state B6 HB), (tio_fn_fly_on B6 HB), (tio_fn_now B6 HB), (tio_fn_backoff B6 HB), Hs, Hf.
  change (negb (S_ONLINE =? S_ONLINE) || truth 0) with false.
  destruct (Z.ltb_spec (g_now B6) (M_backoff_until B6)) as [E|E]; [lia | reflexivity].
Qed.

(* FT:582-597, cmds = the frame's count *)
Local Lemma tio_latest_frame : forall B6 fr send ncmds blen, length B6 = WN ->
  sf_body_len (rf fr) = blen -> sf_ncmds (rf fr) = ncmds -> sf_send (rf fr) = send ->
  blen <= Cfg_max_body B6 -> ncmds <= Cfg_max_cmds B6 -> send = u32 (M_host_counter B6 + ncmds) ->
  check_latest_frame_m (set_g_fail_next B6 0) fr ncmds = Some (set_g_fail_next B6 0, tt).
Proof.
  intros B6 fr send ncmds blen HB Hbl Hnc Hse Hmb Hmc Hhc.
  unfold check_latest_frame_m. cbv beta zeta.
  rewrite Hbl, Hnc, Hse, (tio_fn_max_body B6 HB), (tio_fn_max_cmds B6 HB), (tio_fn_host_counter B6 HB).
  rewrite (Z.eqb_refl ncmds).
  destruct (Z.ltb_spec (Cfg_max_body B6) blen) as [E|E]; [lia|].
  destruct (Z.ltb_spec (Cfg_max_cmds B6) ncmds) as [E'|E']; [lia|].
  destruct (Z.eqb_spec send (u32 (M_host_counter B6 + ncmds))) as [E''|E'']; [|exact (False_ind _ (E'' Hhc))].
  change (negb true) with false.
  rewrite (andb_false_r (negb (truth (g_raw (set_g_fail_next B6 0))))).
  reflexivity.
Qed.

(* FT:646-654 *)
Local Lemma tio_display : forall Bs,
  (M_display_sent Bs = 0 \/ Cfg_display_gap_us Bs <= u64 (g_now Bs - M_last_display Bs)) ->
  check_latest_display_m Bs = Some (Bs, tt).
Proof.
  intros Bs [H|H]; unfold check_latest_display_m.
  - rewrite H. change (truth 0) with false. reflexivity.
  - destruct (Z.ltb_spec (u64 (g_now Bs - M_last_display Bs)) (Cfg_display_gap_us Bs)) as [E|E]; [lia|].
    rewrite (andb_false_r (truth (M_display_sent Bs))). reflexivity.
Qed.

Local Lemma tio_flen : forall fr : list byte, Z.of_nat (length fr) <= SPEC_MAX_FRAME ->
  (if Z.of_nat (length fr) <? SPEC_MAX_FRAME then Z.of_nat (length fr) else SPEC_MAX_FRAME) = Z.of_nat (length fr).
Proof. intros fr H. destruct (Z.ltb_spec (Z.of_nat (length fr)) SPEC_MAX_FRAME); lia. Qed.

(* ---------------------------------------------------------------- io_send on the frame, the frame a variable *)

Local Lemma tio_raw_core : forall I B6 fr send ncmds blen,
  length B6 = WN ->
  check_sent_frame_m (set_g_fail_next B6 0) fr = Some (set_g_fail_next B6 0, tt) ->
  sf_cmd (rf fr) = DIGINET_CMD_DATA -> sf_retry (rf fr) = 0 -> sf_send (rf fr) = send ->
  sf_ncmds (rf fr) = ncmds -> sf_body_len (rf fr) = blen -> Z.of_nat (length fr) <= SPEC_MAX_FRAME ->
  M_state B6 = S_ONLINE -> M_fly_on B6 = 0 -> M_backoff_until B6 <= g_now B6 ->
  blen <= Cfg_max_body B6 -> ncmds <= Cfg_max_cmds B6 -> send = u32 (M_host_counter B6 + ncmds) ->
  g_raw B6 <> 0 ->
  io_send_m I B6 fr = Some (w_fly (w_io8 B6 send) send fr, if truth (g_fail_next B6) then - EIO else 0).
Proof.
  intros I B6 fr send ncmds blen HB Hsf Hcmd Hret Hse Hnc Hbl Hlen Hst Hfo Hbo Hmb Hmc Hhc Hraw.
  pose proof (tio_inflight B6 HB Hst Hfo Hbo) as Hin.
  pose proof (tio_latest_frame B6 fr send ncmds blen HB Hbl Hnc Hse Hmb Hmc Hhc) as Hlf.
  assert (Hr : truth (g_raw B6) = true).
  { unfold truth. destruct (Z.eqb_spec (g_raw B6) 0) as [E|E]; [exact (False_ind _ (Hraw E)) | reflexivity]. }
  pose proof (tio_fn_raw B6 HB) as Hr0. pose proof (tio_io8_raw B6 send HB) as Hr8.
  pose proof (tio_flen fr Hlen) as Hfl.
  clear Hst Hfo Hbo Hmb Hmc Hhc Hraw Hlen.
  unfold io_send_m. cbv beta zeta.
  rewrite Hsf. cbv beta iota.
  rewrite Hcmd. change (DIGINET_CMD_DATA =? SPEC_CMD_ACK) with false. cbv beta iota.
  change ((DIGINET_CMD_DATA =? SPEC_CMD_E2) || (DIGINET_CMD_DATA =? SPEC_CMD_DATA)) with true. cbv beta iota.
  rewrite Hret. change (truth 0) with false. cbv beta iota.
  change (DIGINET_CMD_DATA =? SPEC_CMD_E2) with false. cbv beta iota.
  rewrite Hin. cbv beta iota.
  rewrite Hr0, Hr. cbn [negb andb].
  rewrite Hnc, Hlf. cbv beta iota.
  rewrite Hse.
  change (set_g_last_counter (set_M_host_counter (set_g_fail_next B6 0) send) send) with (w_io8 B6 send).
  rewrite Hr8, Hr. cbn [negb andb].
  rewrite Hfl, (Nat2Z.id (length fr)), (firstn_all fr).
  unfold w_fly. change SPEC_CMD_DATA with DIGINET_CMD_DATA. reflexivity.
Qed.

Local Lemma tio_tagged_core : forall I B6 fr send ncmds blen bd Bs disp,
  length B6 = WN ->
  check_sent_frame_m (set_g_fail_next B6 0) fr = Some (set_g_fail_next B6 0, tt) ->
  sf_cmd (rf fr) = DIGINET_CMD_DATA -> sf_retry (rf fr) = 0 -> sf_send (rf fr) = send ->
  sf_ncmds (rf fr) = ncmds -> sf_body (rf fr) = SPEC_BODY_AT -> sf_body_len (rf fr) = blen ->
  Z.of_nat (length fr) <= SPEC_MAX_FRAME ->
  M_state B6 = S_ONLINE -> M_fly_on B6 = 0 -> M_backoff_until B6 <= g_now B6 ->
  blen <= Cfg_max_body B6 -> ncmds <= Cfg_max_cmds B6 -> send = u32 (M_host_counter B6 + ncmds) ->
  g_raw B6 = 0 -> at8 (skipn 30 fr) 0 <> 0 ->
  cmds_loop (S (Z.to_nat blen)) (set_g_fail_next B6 0) (skipn 30 fr) blen 0 0 = Some ncmds ->
  firstn (Z.to_nat blen) (skipn 30 fr) = bd ->
  check_latest_sent_m (w_io8 B6 send) bd blen = Some (Bs, disp) ->
  (truth disp = true -> M_display_sent Bs = 0 \/ Cfg_display_gap_us Bs <= u64 (g_now Bs - M_last_display Bs)) ->
  io_send_m I B6 fr = Some (w_fly (w_dispM Bs disp) send fr, if truth (g_fail_next B6) then - EIO else 0).
Proof.
  intros I B6 fr send ncmds blen bd Bs disp HB Hsf Hcmd Hret Hse Hnc Hbd Hbl Hlen Hst Hfo Hbo Hmb Hmc Hhc
    Hraw Hat Hcl Hfst Hls Hdisp.
  pose proof (tio_inflight B6 HB Hst Hfo Hbo) as Hin.
  pose proof (tio_latest_frame B6 fr send ncmds blen HB Hbl Hnc Hse Hmb Hmc Hhc) as Hlf.
  pose proof (tio_fn_raw B6 HB) as Hr0. pose proof (tio_io8_raw B6 send HB) as Hr8.
  pose proof (tio_flen fr Hlen) as Hfl.
  assert (Hka : ((blen =? 1) && (at8 (skipn 30 fr) 0 =? 0) && (ncmds =? 1)) = false).
  { destruct (Z.eqb_spec (at8 (skipn 30 fr) 0) 0) as [E|E]; [exact (False_ind _ (Hat E))|].
    rewrite (andb_false_r (blen =? 1)). reflexivity. }
  clear Hst Hfo Hbo Hmb Hmc Hhc Hat Hlen.
  unfold io_send_m. cbv beta zeta.
  rewrite Hsf. cbv beta iota.
  rewrite Hcmd. change (DIGINET_CMD_DATA =? SPEC_CMD_ACK) with false. cbv beta iota.
  change ((DIGINET_CMD_DATA =? SPEC_CMD_E2) || (DIGINET_CMD_DATA =? SPEC_CMD_DATA)) with true. cbv beta iota.
  rewrite Hret. change (truth 0) with false. cbv beta iota.
  change (DIGINET_CMD_DATA =? SPEC_CMD_E2) with false. cbv beta iota.
  rewrite Hin. cbv beta iota.
  rewrite Hbl, Hbd, Hnc. change (Z.to_nat SPEC_BODY_AT) with 30%nat.
  rewrite Hka, Hr0, Hraw. change (truth 0) with false. cbn [negb andb].
  rewrite Hcl. cbv beta iota.
  rewrite Hlf. cbv beta iota.
  rewrite Hse.
  change (set_g_last_counter (set_M_host_counter (set_g_fail_next B6 0) send) send) with (w_io8 B6 send).
  rewrite Hr8, Hraw. change (truth 0) with false. cbn [negb andb].
  rewrite Hfst, Hls. cbv beta iota.
  unfold w_dispM. destruct (truth disp) eqn:Hd.
  - rewrite (tio_display Bs (Hdisp eq_refl)). cbv beta iota.
    rewrite Hfl, (Nat2Z.id (length fr)), (firstn_all fr).
    unfold w_fly. change SPEC_CMD_DATA with DIGINET_CMD_DATA. reflexivity.
  - cbv beta iota.
    rewrite Hfl, (Nat2Z.id (length fr)), (firstn_all fr).
    unfold w_fly. change SPEC_CMD_DATA with DIGINET_CMD_DATA. reflexivity.
Qed.

(* ---------------------------------------------------------------- io_send on the frame diginet_frame_build made *)

Lemma tt_io_raw : forall (HL : links) I B6 dst send ncmds body mode,
  length B6 = WN -> build_ok dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode ->
  M_desk_known B6 = 1 -> M_desk B6 = dst -> Cfg_sum_mode B6 = mode ->
  M_state B6 = S_ONLINE -> M_fly_on B6 = 0 -> M_backoff_until B6 <= g_now B6 ->
  Z.of_nat (length body) <= Cfg_max_body B6 -> ncmds <= Cfg_max_cmds B6 ->
  send = u32 (M_host_counter B6 + ncmds) -> g_raw B6 <> 0 ->
  io_send_m I B6 (lib_frame dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode) =
    Some (w_fly (w_io8 B6 send) send (lib_frame dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode),
          if truth (g_fail_next B6) then - EIO else 0).
Proof.
  intros HL I B6 dst send ncmds body mode HB Hok Hkn Hdk Hsm Hst Hfo Hbo Hmb Hmc Hhc Hraw.
  pose proof (rf_lib_frame HL dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode Hok) as R. cbv zeta in R.
  destruct R as (Hlen & _ & _ & _ & Hbd & Hcmd & Hse & _ & Hret & Hnc & Hbl & _).
  pose proof (sent_frame_ok HL (set_g_fail_next B6 0) dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode Hok
    eq_refl (eq_trans (tio_fn_desk_known B6 HB) Hkn) (eq_trans (tio_fn_desk B6 HB) Hdk)
    (eq_trans (tio_fn_sum_mode B6 HB) Hsm)) as Hsf.
  destruct Hok as (_ & _ & _ & _ & _ & _ & _ & _ & Hlb & _).
  assert (Hmax : Z.of_nat (length (lib_frame dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode)) <= SPEC_MAX_FRAME).
  { rewrite Hlen. exact (tio_max (length body) Hlb). }
  exact (tio_raw_core I B6 (lib_frame dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode) send ncmds
    (Z.of_nat (length body)) HB Hsf Hcmd Hret Hse Hnc Hbl Hmax Hst Hfo Hbo Hmb Hmc Hhc Hraw).
Qed.

Lemma tt_io_tagged : forall (HL : links) I B6 dst send ncmds body mode Bs disp,
  length B6 = WN -> build_ok dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode ->
  M_desk_known B6 = 1 -> M_desk B6 = dst -> Cfg_sum_mode B6 = mode ->
  M_state B6 = S_ONLINE -> M_fly_on B6 = 0 -> M_backoff_until B6 <= g_now B6 ->
  Z.of_nat (length body) <= Cfg_max_body B6 -> ncmds <= Cfg_max_cmds B6 ->
  send = u32 (M_host_counter B6 + ncmds) -> g_raw B6 = 0 -> at8 body 0 <> 0 ->
  cmds_loop (S (Z.to_nat (Z.of_nat (length body)))) (set_g_fail_next B6 0)
    (skipn 30 (lib_frame dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode)) (Z.of_nat (length body)) 0 0 = Some ncmds ->
  check_latest_sent_m (w_io8 B6 send) body (Z.of_nat (length body)) = Some (Bs, disp) ->
  (truth disp = true -> M_display_sent Bs = 0 \/ Cfg_display_gap_us Bs <= u64 (g_now Bs - M_last_display Bs)) ->
  io_send_m I B6 (lib_frame dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode) =
    Some (w_fly (w_dispM Bs disp) send (lib_frame dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode),
          if truth (g_fail_next B6) then - EIO else 0).
Proof.
  intros HL I B6 dst send ncmds body mode Bs disp HB Hok Hkn Hdk Hsm Hst Hfo Hbo Hmb Hmc Hhc Hraw Hat Hcl Hls
    Hdisp.
  pose proof (rf_lib_frame HL dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode Hok) as R. cbv zeta in R.
  destruct R as (Hlen & _ & _ & _ & Hbd & Hcmd & Hse & _ & Hret & Hnc & Hbl & _).
  pose proof (sent_frame_ok HL (set_g_fail_next B6 0) dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode Hok
    eq_refl (eq_trans (tio_fn_desk_known B6 HB) Hkn) (eq_trans (tio_fn_desk B6 HB) Hdk)
    (eq_trans (tio_fn_sum_mode B6 HB) Hsm)) as Hsf.
  destruct Hok as (Hd & Hs & _ & _ & _ & _ & _ & _ & Hlb & _).
  assert (Hmax : Z.of_nat (length (lib_frame dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode)) <= SPEC_MAX_FRAME).
  { rewrite Hlen. exact (tio_max (length body) Hlb). }
  pose proof (tt_frame_body dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode Hd Hs) as Hfb.
  assert (Hat' : at8 (skipn 30 (lib_frame dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode)) 0 <> 0).
  { rewrite Hfb, (tio_at8_app body _ Hat). exact Hat. }
  assert (Hfst : firstn (Z.to_nat (Z.of_nat (length body)))
                   (skipn 30 (lib_frame dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode)) = body).
  { rewrite Hfb. apply tio_firstn_app. }
  exact (tio_tagged_core I B6 (lib_frame dst HOST send 0 0 DIGINET_CMD_DATA ncmds body mode) send ncmds
    (Z.of_nat (length body)) body Bs disp HB Hsf Hcmd Hret Hse Hnc Hbd Hbl Hmax Hst Hfo Hbo Hmb Hmc Hhc
    Hraw Hat' Hcl Hfst Hls Hdisp).
Qed.

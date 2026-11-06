(* TickTakeW.v's stage worlds composed into tt_end.
     tt_fr_eq          the frame send_data builds (w_fr, DS:390-397) in the world after take and DS:467-470 is tt_fr
     tt_stage_frames   the frames of the stages up to io_send's writes (FT:829, :867-868)
     tt_end_raw        the world after the run, raw: w_tx (w_fly (w_io8 B6 send) send fr) r
     tt_end_tagged     tagged: w_tx (w_fly (w_dispM Bs hd) send fr) r, Bs the world check_latest_sent leaves
                       (FT:626-644), w_dispM the harness's display pacing (FT:876-879)
   Each stage writes inside a region (the RE_ regions below, each inside one of TickTakeW's R_ regions), so a getter
   outside the region reads the same after the stage. The reads are small lemmas over world variables (the TRAP of
   TickTakeW.v: no unification of two different world terms); the main lemmas only chain them with
   transitivity / exact on terms that are syntactically the goal's.
   Hypotheses added to the statements first proposed (both are agree_core facts): S_queued B <= QUEUE_MAX
   (d4_queued raw, d1_queued + d1_nq tagged), and tagged g_nq B <= QUEUE_MAX (d1_nq) and every queued serial
   < CMDS_MAX (d1_entry, d3_ncmd, d3_ops). Without them the queue entries past index 512 / the serials past
   1023 overlap the stats / the scalars the run writes (w_tx's tx_frames, w_io8's g_fail_next). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links QueueFacts SimLib SendOk SettleOk
  TickDefs TakeOk TickTakeW.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the regions of the later stages *)

Definition RE_tx (a : Z) : Prop := A_S_stats_tx_frames <= a < A_S_stats_tx_frames + 8.      (* w_tx *)
Definition RE_io (a : Z) : Prop := (OFF_g_fail_next <= a < OFF_g_fail_next + 1) \/          (* w_io8 *)
  (A_M_host_counter <= a < A_M_host_counter + 4) \/
  (OFF_g_last_counter <= a < OFF_g_last_counter + SZ_g_last_counter).
Definition RE_dm (a : Z) : Prop := A_M_last_display <= a < A_M_display_sent + 4.             (* w_dispM *)
Definition RE_fl (a : Z) : Prop := A_M_fly_on <= a < A_M_fly_len + 8.                        (* w_fly *)
Definition RE_hi (a : Z) : Prop := (OFF_g_cmd <= a < OFF_g_fail_next) \/                     (* R_cs, R_hq *)
  (OFF_g_nq <= a < OFF_g_nq + SZ_g_nq).
(* from a stage world to the world after the run *)
Definition RE_Ff (a : Z) : Prop := RE_fl a \/ RE_tx a.          (* from the world w_fly starts in *)
Definition RE_Sf (a : Z) : Prop := RE_dm a \/ RE_Ff a.          (* from Bs (tagged) *)
Definition RE_Xf (a : Z) : Prop := RE_hi a \/ RE_Sf a.          (* from w_io8 *)
Definition RE_6f (a : Z) : Prop := RE_io a \/ RE_Xf a.          (* from B6 *)
Definition RE_Df (a : Z) : Prop := R_ss a \/ RE_6f a.           (* from w_dispS *)
Definition RE_1f (a : Z) : Prop := R_ds a \/ RE_Df a.           (* from B1 *)
(* from B to w_io8 *)
Definition RE_BX (a : Z) : Prop := R_lib a \/ RE_io a.

(* the kit's tk_get / tk_fr with the RE_* unfolded too *)
Ltac te_unfold := unfold RE_1f, RE_Df, RE_6f, RE_Xf, RE_Sf, RE_Ff, RE_BX, RE_tx, RE_io, RE_dm, RE_fl, RE_hi in *.
Ltac te_offs := te_unfold; tk_offs.
Ltac te_notR := let a := fresh "a" in let Ha := fresh "Ha" in let HR := fresh "HR" in
  intros a Ha HR; cbv beta in HR; te_offs.
Ltac te_get H := match goal with
  | |- u_at _ _ _ = u_at _ _ _ => apply (wframe_u_at _ _ _ _ _ H); [tk_offs | te_notR]
  | |- s32_at _ _ = s32_at _ _ => apply (wframe_s32_at _ _ _ _ H); [tk_offs | te_notR]
  | |- sub _ _ _ = sub _ _ _ => apply (wframe_sub _ _ _ _ _ H); [tk_offs | te_notR]
  end.
Ltac te_fr := lazymatch goal with
  | |- wframe _ ?B ?B => apply wframe_refl
  | |- wframe _ _ (upd _ _ _) =>
      apply tk_frame_upd; [te_fr | tk_len | tk_offs | tk_offs
      | let a := fresh "a" in let Ha := fresh "Ha" in
        intros a Ha; rewrite ?w_length_put, ?repeat_length in Ha; te_offs]
  end.

(* ---- inclusions ---- *)

Lemma tte_gs_nq : forall a, R_gs a -> R_nq a.
Proof. intros a H. unfold R_nq. right; right; right; right. exact H. Qed.

Lemma RE_io_nq : forall a, RE_io a -> R_nq a.
Proof.
  intros a [H|[H|H]]; unfold R_nq.
  - right; right; right; right. unfold R_gs. left. exact H.
  - right; right; right; left. unfold R_ms. right; left. exact H.
  - right; right; right; right. unfold R_gs. right. exact H.
Qed.

Lemma RE_fl_nq : forall a, RE_fl a -> R_nq a.
Proof. intros a H. unfold R_nq. right; right; right; left. unfold R_ms. right; right. exact H. Qed.

Lemma RE_dm_nq : forall a, RE_dm a -> R_nq a.
Proof. intros a H. unfold R_nq. right; right; right; left. unfold R_ms. left. exact H. Qed.

Lemma RE_tx_nq : forall a, RE_tx a -> R_nq a.
Proof. intros a H. unfold R_nq. right; right; left. unfold R_ss. right; right. unfold RE_tx in H. tk_offs. Qed.

Lemma RE_Ff_nq : forall a, RE_Ff a -> R_nq a.
Proof. intros a [H|H]; [apply RE_fl_nq | apply RE_tx_nq]; exact H. Qed.

Lemma RE_BX_nq : forall a, RE_BX a -> R_nq a.
Proof. intros a [H|H]; [apply R_lib_nq | apply RE_io_nq]; exact H. Qed.

Lemma tte_BX_tt : forall a, RE_BX a -> R_tt a.
Proof. intros a H. apply R_nq_tt, RE_BX_nq, H. Qed.

Lemma R_cshq_tt : forall a, R_cs a \/ R_hq a -> R_tt a.
Proof. intros a H. unfold R_tt. right. exact H. Qed.

Lemma R_cshq_hi : forall a, R_cs a \/ R_hq a -> RE_hi a.
Proof. intros a [[H _]|[H|H]]; unfold RE_hi; tk_offs. Qed.

Lemma tte_in_hd_Xf : forall a, RE_hi a \/ RE_dm a -> RE_Xf a.
Proof. intros a [H|H]; unfold RE_Xf, RE_Sf; [left | right; left]; exact H. Qed.

(* ---------------------------------------------------------------- small facts *)

Lemma tte_zero_small : forall n, 0 <= 0 < 2 ^ (8 * Z.of_nat n).
Proof. intros n. split; [lia|]. apply Z.pow_pos_nonneg; lia. Qed.

Lemma tte_now_bound : forall B, 0 <= g_now B < 2 ^ 64.
Proof. intros B. unfold g_now. split; [apply u_at_nonneg | apply (u_at_bound B OFF_g_now 8)]. Qed.

Lemma tte_send_bound : forall B m, 0 <= tt_send B m < 2 ^ 32.
Proof. intros B m. unfold tt_send, u32. apply Z.mod_pos_bound. lia. Qed.

Lemma tte_frl : forall (body fr : list byte), (length body <= 1484)%nat ->
  Z.of_nat (length fr) = frame_len (length body) -> (length fr <= 1514)%nat.
Proof. intros body fr Hb Hf. unfold frame_len in Hf. lia. Qed.

Lemma tte_flen_nat : forall n, (n <= 1484)%nat -> (Z.to_nat (frame_len n) <= 1514)%nat.
Proof. intros n Hn. unfold frame_len. lia. Qed.

Lemma tte_to_nat_len : forall (l : list byte) L, Z.of_nat (length l) = L -> Z.to_nat L = length l.
Proof. intros l L <-. apply Nat2Z.id. Qed.

Lemma tte_pick_le : forall {A} (m : list bool) (l : list A), (length (pick m l) <= length l)%nat.
Proof.
  intros A m l. revert m. induction l as [|x l IH]; intros [|b m]; cbn [pick length]; try lia.
  destruct b; cbn [length]; specialize (IH m); lia.
Qed.

Lemma tte_queued_bound : forall B B1 m, S_queued B1 = Z.of_nat (length (unpick m (sq B))) ->
  S_queued B <= QUEUE_MAX -> S_queued B1 <= QUEUE_MAX.
Proof.
  intros B B1 m H1 H. pose proof (tte_pick_le (map negb m) (sq B)) as Hp. pose proof (tk_sq_length B) as Hl.
  unfold unpick in H1. unfold QUEUE_MAX in *. lia.
Qed.

Lemma tte_le_cmds : forall B, g_nq B <= QUEUE_MAX -> g_nq B <= CMDS_MAX.
Proof. intros B H. unfold QUEUE_MAX, CMDS_MAX in *. lia. Qed.

Lemma tte_cmdN : forall k, 0 <= k < Cmd_N -> 0 <= k < CMDS_MAX.
Proof. intros k H. unfold Cmd_N, CMDS_MAX in *. lia. Qed.

Lemma tte_Ts_bound : forall B m k, (forall i, 0 <= i < g_nq B -> Q_at B i < CMDS_MAX) ->
  In k (pick m (hq B)) -> 0 <= k < CMDS_MAX.
Proof.
  intros B m k HQ Hk. apply in_pick in Hk. apply tk_In_hq in Hk. destruct Hk as [i [Hi Hki]]. subst k.
  split; [unfold Q_at; apply u_at_nonneg | apply HQ; exact Hi].
Qed.

Lemma tte_map_zseq : forall {A} (f g : Z -> A) n1 n2, n1 = n2 ->
  (forall i, 0 <= i < Z.of_nat n1 -> f i = g i) -> map f (zseq n1) = map g (zseq n2).
Proof. intros A f g n1 n2 <- H. apply map_ext_in. intros i Hi. apply in_zseq in Hi. apply H. exact Hi. Qed.

Lemma tte_if_true : forall (b : bool) (x y : Z), b = true -> (if b then x else y) = x.
Proof. intros b x y ->. reflexivity. Qed.

Lemma tte_if_false : forall (b : bool) (x y : Z), b = false -> (if b then x else y) = y.
Proof. intros b x y ->. reflexivity. Qed.

(* te_ms / te_ml's right sides, tagged and raw *)
Lemma tte_shape_tagged : forall g hd a1 a2 x y : Z, g = 0 -> a1 = a2 -> x = y ->
  (if truth hd then a1 else x) = (if (g =? 0) && negb (hd =? 0) then a2 else y).
Proof. intros g hd a1 a2 x y -> -> ->. unfold truth. reflexivity. Qed.

Lemma tte_shape_raw : forall g hd a x y : Z, g <> 0 -> x = y -> x = (if (g =? 0) && negb (hd =? 0) then a else y).
Proof. intros g hd a x y Hg ->. destruct (Z.eqb_spec g 0) as [E|E]; [exfalso; exact (Hg E) | reflexivity]. Qed.

Lemma tte_frame_cong : forall (d1 d2 s1 s2 : list byte) (c1 c2 n : Z) (body : list byte) (m1 m2 : Z),
  d1 = d2 -> s1 = s2 -> c1 = c2 -> m1 = m2 ->
  lib_frame d1 s1 (u32 (c1 + n)) 0 0 DIGINET_CMD_DATA (u8 n) body m1 =
  lib_frame d2 s2 (u32 (c2 + n)) 0 0 DIGINET_CMD_DATA (u8 n) body m2.
Proof. intros d1 d2 s1 s2 c1 c2 n body m1 m2 -> -> -> ->. reflexivity. Qed.

(* ---------------------------------------------------------------- the later stages *)

(* ---- w_io8 (FT:829, :867-868) ---- *)
Lemma tte_io8_len : forall Y send, length Y = WN -> length (w_io8 Y send) = WN.
Proof. intros Y send HY. unfold w_io8, set_g_last_counter, set_M_host_counter, set_g_fail_next. tk_len. Qed.

Lemma tte_io8_frame : forall Y send, length Y = WN -> wframe RE_io Y (w_io8 Y send).
Proof. intros Y send HY. unfold w_io8, set_g_last_counter, set_M_host_counter, set_g_fail_next. te_fr. Qed.

Lemma tte_io8_mhc : forall Y send, length Y = WN -> 0 <= send < 2 ^ 32 -> M_host_counter (w_io8 Y send) = send.
Proof.
  intros Y send HY Hs. unfold M_host_counter, w_io8, set_g_last_counter, set_M_host_counter, set_g_fail_next.
  tk_peel. apply tk_u_put_small; [tk_len | tk_offs | tk_offs | exact Hs].
Qed.

Lemma tte_io8_fail : forall Y send, length Y = WN -> g_fail_next (w_io8 Y send) = 0.
Proof.
  intros Y send HY. unfold g_fail_next, w_io8, set_g_last_counter, set_M_host_counter, set_g_fail_next.
  tk_peel. tk_peel. apply tk_u_put_small; [tk_len | tk_offs | tk_offs | apply tte_zero_small].
Qed.

(* ---- w_dispM (FT:876-879) ---- *)
Lemma tte_dispM_len : forall Y hd, length Y = WN -> length (w_dispM Y hd) = WN.
Proof.
  intros Y hd HY. unfold w_dispM. destruct (truth hd); [|exact HY].
  unfold set_M_last_display, set_M_display_sent. tk_len.
Qed.

Lemma tte_dispM_frame : forall Y hd, length Y = WN -> wframe RE_dm Y (w_dispM Y hd).
Proof.
  intros Y hd HY. unfold w_dispM. destruct (truth hd); [|apply wframe_refl].
  unfold set_M_last_display, set_M_display_sent. te_fr.
Qed.

Lemma tte_dispM_ds : forall Y hd, length Y = WN ->
  M_display_sent (w_dispM Y hd) = if truth hd then 1 else M_display_sent Y.
Proof.
  intros Y hd HY. unfold w_dispM. destruct (truth hd); [|reflexivity].
  unfold M_display_sent, set_M_last_display, set_M_display_sent. tk_peel.
  apply tk_s32_put; [tk_len | tk_offs | tk_offs | lia].
Qed.

Lemma tte_dispM_dl : forall Y hd, length Y = WN ->
  M_last_display (w_dispM Y hd) = if truth hd then g_now Y else M_last_display Y.
Proof.
  intros Y hd HY. unfold w_dispM. destruct (truth hd); [|reflexivity].
  unfold M_last_display, set_M_last_display, set_M_display_sent.
  apply tk_u_put_small; [tk_len | tk_offs | tk_offs |].
  unfold g_now. split; [apply u_at_nonneg | apply u_at_bound].
Qed.

(* ---- w_fly (FT:883-889) ---- *)
Ltac fly_unfold := unfold w_fly, set_M_fly_frame, set_M_fly_len, set_M_fly_sent, set_M_fly_retries,
  set_M_fly_counter, set_M_fly_cmd, set_M_fly_on.

Lemma tte_fly_len : forall Y send fr, length Y = WN -> (length fr <= 1514)%nat -> length (w_fly Y send fr) = WN.
Proof. intros Y send fr HY Hf. fly_unfold. tk_len. Qed.

Lemma tte_fly_frame : forall Y send fr, length Y = WN -> (length fr <= 1514)%nat ->
  wframe RE_fl Y (w_fly Y send fr).
Proof. intros Y send fr HY Hf. fly_unfold. te_fr. Qed.

Lemma tte_fly_on : forall Y send fr, length Y = WN -> (length fr <= 1514)%nat -> M_fly_on (w_fly Y send fr) = 1.
Proof.
  intros Y send fr HY Hf. unfold M_fly_on. fly_unfold. do 6 tk_peel.
  apply tk_s32_put; [tk_len | tk_offs | tk_offs | lia].
Qed.

Lemma tte_fly_cmd : forall Y send fr, length Y = WN -> (length fr <= 1514)%nat ->
  M_fly_cmd (w_fly Y send fr) = SPEC_CMD_DATA.
Proof.
  intros Y send fr HY Hf. unfold M_fly_cmd. fly_unfold. do 5 tk_peel.
  apply tk_u_put_small; [tk_len | tk_offs | tk_offs | apply tte_zero_small].
Qed.

Lemma tte_fly_ctr : forall Y send fr, length Y = WN -> (length fr <= 1514)%nat -> 0 <= send < 2 ^ 32 ->
  M_fly_counter (w_fly Y send fr) = send.
Proof.
  intros Y send fr HY Hf Hs. unfold M_fly_counter. fly_unfold. do 4 tk_peel.
  apply tk_u_put_small; [tk_len | tk_offs | tk_offs | exact Hs].
Qed.

Lemma tte_fly_ret : forall Y send fr, length Y = WN -> (length fr <= 1514)%nat -> M_fly_retries (w_fly Y send fr) = 0.
Proof.
  intros Y send fr HY Hf. unfold M_fly_retries. fly_unfold. do 3 tk_peel.
  apply tk_u_put_small; [tk_len | tk_offs | tk_offs | apply tte_zero_small].
Qed.

Lemma tte_fly_sent : forall Y send fr, length Y = WN -> (length fr <= 1514)%nat ->
  M_fly_sent (w_fly Y send fr) = g_now Y.
Proof.
  intros Y send fr HY Hf. unfold M_fly_sent. fly_unfold. do 2 tk_peel.
  apply tk_u_put_small; [tk_len | tk_offs | tk_offs |].
  unfold g_now. split; [apply u_at_nonneg | apply u_at_bound].
Qed.

Lemma tte_fly_flen : forall Y send fr, length Y = WN -> (length fr <= 1514)%nat ->
  M_fly_len (w_fly Y send fr) = Z.of_nat (length fr).
Proof.
  intros Y send fr HY Hf. unfold M_fly_len. fly_unfold. tk_peel.
  apply tk_u_put_small; [tk_len | tk_offs | tk_offs |].
  change (8 * Z.of_nat 8) with 64. lia.
Qed.

Lemma tte_fly_fr : forall Y send fr n, length Y = WN -> (length fr <= 1514)%nat -> n = length fr ->
  sub (w_fly Y send fr) A_M_fly_frame n = fr.
Proof. intros Y send fr n HY Hf ->. fly_unfold. apply tk_sub_same; [tk_len | tk_offs | tk_offs]. Qed.

(* ---- w_tx (DS:91-93) ---- *)
Lemma tte_tx_len : forall F r, length F = WN -> length (w_tx F r) = WN.
Proof. intros F r HF. unfold w_tx. destruct (r =? 0); [unfold set_S_stats_tx_frames; tk_len | exact HF]. Qed.

Lemma tte_tx_frame : forall F r, length F = WN -> wframe RE_tx F (w_tx F r).
Proof. intros F r HF. unfold w_tx. destruct (r =? 0); [unfold set_S_stats_tx_frames; te_fr | apply wframe_refl]. Qed.

(* ---------------------------------------------------------------- reads through a frame *)

(* ---- from B1 ---- *)
Lemma tte_rd1_queued : forall X Y, wframe RE_1f X Y -> S_queued Y = S_queued X.
Proof. intros X Y H. unfold S_queued. te_get H. Qed.

Lemma tte_rd1_ent : forall X Y i, wframe RE_1f X Y -> 0 <= i < QUEUE_MAX -> sq_ent Y i = sq_ent X i.
Proof. intros X Y i H Hi. unfold sq_ent. te_get H. Qed.

Lemma tte_rd1_sq : forall X Y, wframe RE_1f X Y -> S_queued X <= QUEUE_MAX -> sq Y = sq X.
Proof.
  intros X Y H Hq. pose proof (tte_rd1_queued X Y H) as E. unfold sq.
  apply tte_map_zseq; [exact (f_equal Z.to_nat E) |].
  intros i Hi. apply tte_rd1_ent; [exact H | lia].
Qed.

(* ---- from w_dispS ---- *)
Lemma tte_rdD_ds : forall X Y, wframe RE_Df X Y -> S_display_sent Y = S_display_sent X.
Proof. intros X Y H. unfold S_display_sent. te_get H. Qed.

Lemma tte_rdD_dl : forall X Y, wframe RE_Df X Y -> S_last_display_us Y = S_last_display_us X.
Proof. intros X Y H. unfold S_last_display_us. te_get H. Qed.

(* ---- B to B1 ---- *)
Lemma tte_rdq_ds : forall X Y, wframe R_qs X Y -> S_display_sent Y = S_display_sent X.
Proof. intros X Y H. unfold S_display_sent. te_get H. Qed.

Lemma tte_rdq_dl : forall X Y, wframe R_qs X Y -> S_last_display_us Y = S_last_display_us X.
Proof. intros X Y H. unfold S_last_display_us. te_get H. Qed.

(* ---- B to the world send_data starts in ---- *)
Lemma tte_rdqd_desk : forall X Y, wframe (fun a => R_qs a \/ R_ds a) X Y -> S_desk_mac Y = S_desk_mac X.
Proof. intros X Y H. unfold S_desk_mac. te_get H. Qed.

Lemma tte_rdqd_host : forall X Y, wframe (fun a => R_qs a \/ R_ds a) X Y -> S_cfg_host_mac Y = S_cfg_host_mac X.
Proof. intros X Y H. unfold S_cfg_host_mac. te_get H. Qed.

Lemma tte_rdqd_sum : forall X Y, wframe (fun a => R_qs a \/ R_ds a) X Y -> S_cfg_sum_mode Y = S_cfg_sum_mode X.
Proof. intros X Y H. unfold S_cfg_sum_mode. te_get H. Qed.

Lemma tte_rdqd_hc : forall X Y, wframe (fun a => R_qs a \/ R_ds a) X Y -> S_host_counter Y = S_host_counter X.
Proof. intros X Y H. unfold S_host_counter. te_get H. Qed.

(* ---- from B6 ---- *)
Lemma tte_rd6_hc : forall X Y, wframe RE_6f X Y -> S_host_counter Y = S_host_counter X.
Proof. intros X Y H. unfold S_host_counter. te_get H. Qed.

Lemma tte_rd6_on : forall X Y, wframe RE_6f X Y -> S_inflight Y = S_inflight X.
Proof. intros X Y H. unfold S_inflight. te_get H. Qed.

Lemma tte_rd6_ctr : forall X Y, wframe RE_6f X Y -> S_inflight_counter Y = S_inflight_counter X.
Proof. intros X Y H. unfold S_inflight_counter. te_get H. Qed.

Lemma tte_rd6_ret : forall X Y, wframe RE_6f X Y -> S_inflight_retries Y = S_inflight_retries X.
Proof. intros X Y H. unfold S_inflight_retries. te_get H. Qed.

Lemma tte_rd6_sent : forall X Y, wframe RE_6f X Y -> S_inflight_sent_us Y = S_inflight_sent_us X.
Proof. intros X Y H. unfold S_inflight_sent_us. te_get H. Qed.

Lemma tte_rd6_flen : forall X Y, wframe RE_6f X Y -> S_inflight_len Y = S_inflight_len X.
Proof. intros X Y H. unfold S_inflight_len. te_get H. Qed.

Lemma tte_rd6_ifr : forall X Y n, wframe RE_6f X Y -> (n <= 1514)%nat ->
  sub Y A_S_inflight_frame n = sub X A_S_inflight_frame n.
Proof. intros X Y n H Hn. te_get H. Qed.

(* ---- from w_io8 ---- *)
Lemma tte_rdX_mhc : forall X Y, wframe RE_Xf X Y -> M_host_counter Y = M_host_counter X.
Proof. intros X Y H. unfold M_host_counter. te_get H. Qed.

Lemma tte_rdX_fail : forall X Y, wframe RE_Xf X Y -> g_fail_next Y = g_fail_next X.
Proof. intros X Y H. unfold g_fail_next. te_get H. Qed.

(* ---- from w_fly ---- *)
Lemma tte_rdT_mon : forall X Y, wframe RE_tx X Y -> M_fly_on Y = M_fly_on X.
Proof. intros X Y H. unfold M_fly_on. te_get H. Qed.

Lemma tte_rdT_mcmd : forall X Y, wframe RE_tx X Y -> M_fly_cmd Y = M_fly_cmd X.
Proof. intros X Y H. unfold M_fly_cmd. te_get H. Qed.

Lemma tte_rdT_mctr : forall X Y, wframe RE_tx X Y -> M_fly_counter Y = M_fly_counter X.
Proof. intros X Y H. unfold M_fly_counter. te_get H. Qed.

Lemma tte_rdT_mret : forall X Y, wframe RE_tx X Y -> M_fly_retries Y = M_fly_retries X.
Proof. intros X Y H. unfold M_fly_retries. te_get H. Qed.

Lemma tte_rdT_msent : forall X Y, wframe RE_tx X Y -> M_fly_sent Y = M_fly_sent X.
Proof. intros X Y H. unfold M_fly_sent. te_get H. Qed.

Lemma tte_rdT_mflen : forall X Y, wframe RE_tx X Y -> M_fly_len Y = M_fly_len X.
Proof. intros X Y H. unfold M_fly_len. te_get H. Qed.

Lemma tte_rdT_mfr : forall X Y n, wframe RE_tx X Y -> (n <= 1514)%nat ->
  sub Y A_M_fly_frame n = sub X A_M_fly_frame n.
Proof. intros X Y n H Hn. te_get H. Qed.

(* ---- the clock, outside every stage ---- *)
Lemma tte_rdtt_now : forall X Y, wframe R_tt X Y -> g_now Y = g_now X.
Proof. intros X Y H. unfold g_now. te_get H. Qed.

(* ---- from Bs (tagged) ---- *)
Lemma tte_rdS_nq : forall X Y, wframe RE_Sf X Y -> g_nq Y = g_nq X.
Proof. intros X Y H. unfold g_nq. te_get H. Qed.

Lemma tte_rdS_Q : forall X Y i, wframe RE_Sf X Y -> 0 <= i -> Q_at Y i = Q_at X i.
Proof. intros X Y i H Hi. unfold Q_at. te_get H. Qed.

Lemma tte_rdS_cmd : forall X Y k, wframe RE_Sf X Y -> 0 <= k -> Cmd_st Y k = Cmd_st X k.
Proof. intros X Y k H Hk. unfold Cmd_st. te_get H. Qed.

Lemma tte_hq_Sf : forall X Y, wframe RE_Sf X Y -> hq Y = hq X.
Proof.
  intros X Y H. pose proof (tte_rdS_nq X Y H) as E. unfold hq.
  apply tte_map_zseq; [exact (f_equal Z.to_nat E) |].
  intros i Hi. apply tte_rdS_Q; [exact H | lia].
Qed.

(* ---- from the world w_fly starts in ---- *)
Lemma tte_rdF_md : forall X Y, wframe RE_Ff X Y -> M_display_sent Y = M_display_sent X.
Proof. intros X Y H. unfold M_display_sent. te_get H. Qed.

Lemma tte_rdF_ml : forall X Y, wframe RE_Ff X Y -> M_last_display Y = M_last_display X.
Proof. intros X Y H. unfold M_last_display. te_get H. Qed.

(* ---- w_io8 to Bs ---- *)
Lemma tte_rdH_md : forall X Y, wframe RE_hi X Y -> M_display_sent Y = M_display_sent X.
Proof. intros X Y H. unfold M_display_sent. te_get H. Qed.

Lemma tte_rdH_ml : forall X Y, wframe RE_hi X Y -> M_last_display Y = M_last_display X.
Proof. intros X Y H. unfold M_last_display. te_get H. Qed.

(* ---- B to w_io8 ---- *)
Lemma tte_rdBX_md : forall X Y, wframe RE_BX X Y -> M_display_sent Y = M_display_sent X.
Proof. intros X Y H. unfold M_display_sent. te_get H. Qed.

Lemma tte_rdBX_ml : forall X Y, wframe RE_BX X Y -> M_last_display Y = M_last_display X.
Proof. intros X Y H. unfold M_last_display. te_get H. Qed.

Lemma tte_rdBX_now : forall X Y, wframe RE_BX X Y -> g_now Y = g_now X.
Proof. intros X Y H. unfold g_now. te_get H. Qed.

Lemma tte_rdBX_nq : forall X Y, wframe RE_BX X Y -> g_nq Y = g_nq X.
Proof. intros X Y H. unfold g_nq. te_get H. Qed.

Lemma tte_rdBX_Q : forall X Y i, wframe RE_BX X Y -> 0 <= i < CMDS_MAX -> Q_at Y i = Q_at X i.
Proof. intros X Y i H Hi. unfold Q_at. te_get H. Qed.

Lemma tte_rdBX_cmd : forall X Y k, wframe RE_BX X Y -> 0 <= k < CMDS_MAX -> Cmd_st Y k = Cmd_st X k.
Proof. intros X Y k H Hk. unfold Cmd_st. te_get H. Qed.

Lemma tte_hq_BX : forall X Y, wframe RE_BX X Y -> g_nq X <= CMDS_MAX -> hq Y = hq X.
Proof.
  intros X Y H Hn. pose proof (tte_rdBX_nq X Y H) as E. unfold hq.
  apply tte_map_zseq; [exact (f_equal Z.to_nat E) |].
  intros i Hi. apply tte_rdBX_Q; [exact H | lia].
Qed.

(* ---------------------------------------------------------------- the frame send_data builds *)

Lemma tt_fr_eq : forall B B2 m, length B = WN -> wframe (fun a => R_qs a \/ R_ds a) B B2 ->
  S_desk_mac B = M_desk B -> S_cfg_host_mac B = HOST -> S_cfg_sum_mode B = Cfg_sum_mode B ->
  w_fr B2 (tt_body B m) (tt_n B m) = tt_fr B m.
Proof.
  intros B B2 m HB F Hd Hh Hs. unfold w_fr, tt_fr, tt_send.
  apply tte_frame_cong.
  - exact (eq_trans (tte_rdqd_desk _ _ F) Hd).
  - exact (eq_trans (tte_rdqd_host _ _ F) Hh).
  - exact (tte_rdqd_hc _ _ F).
  - exact (eq_trans (tte_rdqd_sum _ _ F) Hs).
Qed.

(* ---------------------------------------------------------------- the frames of the first stages *)

Lemma tte_stage_B6 : forall B B1 B6 m, length B1 = WN -> wframe R_qs B B1 ->
  wframe R_ss (w_dispS B1 (tt_hd B m) (g_now B)) B6 -> wframe R_lib B B6.
Proof.
  intros B B1 B6 m HB1 FB1 F6.
  pose proof (tk_dispS_frame B1 (tt_hd B m) (g_now B) HB1) as FD.
  exact (tk_frame_comb R_lib R_ss R_lib _ _ _ (fun a H => H) (fun a H => or_intror (or_intror H))
    (tk_frame_comb R_qs R_ds R_lib _ _ _ (fun a H => or_introl H) (fun a H => or_intror (or_introl H)) FB1 FD) F6).
Qed.

Lemma tt_stage_frames : forall B B1 B6 m send, length B = WN -> length B1 = WN -> wframe R_qs B B1 ->
  length B6 = WN -> wframe R_ss (w_dispS B1 (tt_hd B m) (g_now B)) B6 ->
  wframe (fun a => R_qs a \/ R_ds a) B (w_dispS B1 (tt_hd B m) (g_now B)) /\ wframe R_lib B B6 /\
  length (set_g_fail_next B6 0) = WN /\ wframe R_nq B (set_g_fail_next B6 0) /\
  length (w_io8 B6 send) = WN /\ wframe R_nq B (w_io8 B6 send).
Proof.
  intros B B1 B6 m send HB HB1 FB1 HB6 F6.
  pose proof (tk_dispS_frame B1 (tt_hd B m) (g_now B) HB1) as FD.
  pose proof (tte_stage_B6 B B1 B6 m HB1 FB1 F6) as FB6.
  assert (Hf : length (set_g_fail_next B6 0) = WN) by (unfold set_g_fail_next; tk_len).
  assert (Ff : wframe R_gs B6 (set_g_fail_next B6 0)) by (unfold set_g_fail_next; tk_fr).
  refine (conj (tk_frame_comb R_qs R_ds (fun a => R_qs a \/ R_ds a) _ _ _ (fun a H => or_introl H)
    (fun a H => or_intror H) FB1 FD) (conj FB6 (conj Hf (conj _ (conj (tte_io8_len B6 send HB6) _))))).
  - exact (tk_frame_comb R_lib R_gs R_nq _ _ _ R_lib_nq tte_gs_nq FB6 Ff).
  - exact (tk_frame_comb R_lib RE_io R_nq _ _ _ R_lib_nq RE_io_nq FB6 (tte_io8_frame B6 send HB6)).
Qed.

(* ---------------------------------------------------------------- the world after the run *)

(* both modes: Y the world w_fly starts in (raw w_io8 B6 send, tagged w_dispM Bs hd); the mode's own fields
   are hypotheses *)
Lemma tte_gen : forall B B1 B6 Y Bf m r,
  Bf = w_tx (w_fly Y (tt_send B m) (tt_fr B m)) r ->
  length B = WN -> length B1 = WN -> wframe R_qs B B1 -> sq B1 = unpick m (sq B) ->
  S_queued B1 = Z.of_nat (length (unpick m (sq B))) -> S_queued B <= QUEUE_MAX ->
  length B6 = WN -> wframe R_ss (w_dispS B1 (tt_hd B m) (g_now B)) B6 ->
  S_host_counter B6 = tt_send B m -> S_inflight B6 = 1 -> S_inflight_counter B6 = tt_send B m ->
  S_inflight_retries B6 = 0 -> S_inflight_sent_us B6 = g_now B ->
  S_inflight_len B6 = frame_len (length (tt_body B m)) ->
  Z.of_nat (length (tt_fr B m)) = frame_len (length (tt_body B m)) ->
  sub B6 A_S_inflight_frame (Z.to_nat (frame_len (length (tt_body B m)))) = tt_fr B m ->
  (length (tt_body B m) <= 1484)%nat ->
  length Y = WN -> wframe R_tt (w_io8 B6 (tt_send B m)) Y ->
  wframe (fun a => RE_hi a \/ RE_dm a) (w_io8 B6 (tt_send B m)) Y -> g_now Y = g_now B ->
  (g_raw B <> 0 -> wframe R_nq B Bf) ->
  (g_raw B = 0 -> g_nq Bf = Z.of_nat (length (unpick m (hq B)))) ->
  (g_raw B = 0 -> hq Bf = unpick m (hq B)) ->
  (g_raw B = 0 -> forall k, In k (tt_Ts B m) -> Cmd_st Bf k = SENT) ->
  (g_raw B = 0 -> forall k, 0 <= k < Cmd_N -> ~ In k (tt_Ts B m) -> Cmd_st Bf k = Cmd_st B k) ->
  M_display_sent Bf = (if (g_raw B =? 0) && negb (tt_hd B m =? 0) then 1 else M_display_sent B) ->
  M_last_display Bf = (if (g_raw B =? 0) && negb (tt_hd B m =? 0) then g_now B else M_last_display B) ->
  tt_end B Bf m.
Proof.
  intros B B1 B6 Y Bf m r -> HB HB1 FB1 Hsq Hq1 HqB HB6 F6 Hhc Hon Hctr Hret Hsent Hflen HLfr Hfr Hbody
    HY FXY_tt FXY Hnow Hraw Hnq Hhq Hin Hout Hms Hml.
  pose proof (tte_frl _ _ Hbody HLfr) as Hfl.
  pose proof (tte_send_bound B m) as Hsb.
  pose proof (tk_dispS_frame B1 (tt_hd B m) (g_now B) HB1) as FD.
  pose proof (tte_io8_frame B6 (tt_send B m) HB6) as FX.
  pose proof (tte_fly_len Y (tt_send B m) (tt_fr B m) HY Hfl) as HF.
  pose proof (tte_fly_frame Y (tt_send B m) (tt_fr B m) HY Hfl) as FF.
  pose proof (tte_tx_frame _ r HF) as FT.
  pose proof (tk_frame_comb RE_fl RE_tx RE_Ff _ _ _ (fun a H => or_introl H) (fun a H => or_intror H) FF FT) as FFf.
  pose proof (tk_frame_comb (fun a => RE_hi a \/ RE_dm a) RE_Ff RE_Xf _ _ _ tte_in_hd_Xf
    (fun a H => or_intror (or_intror H)) FXY FFf) as FXf.
  pose proof (tk_frame_comb RE_io RE_Xf RE_6f _ _ _ (fun a H => or_introl H) (fun a H => or_intror H) FX FXf) as F6f.
  pose proof (tk_frame_comb R_ss RE_6f RE_Df _ _ _ (fun a H => or_introl H) (fun a H => or_intror H) F6 F6f) as FDf.
  pose proof (tk_frame_comb R_ds RE_Df RE_1f _ _ _ (fun a H => or_introl H) (fun a H => or_intror H) FD FDf) as F1f.
  pose proof (tte_stage_B6 B B1 B6 m HB1 FB1 F6) as FB6.
  pose proof (tk_frame_comb R_lib RE_io R_tt _ _ _ (fun a H => R_nq_tt a (R_lib_nq a H))
    (fun a H => R_nq_tt a (RE_io_nq a H)) FB6 FX) as FBX.
  pose proof (tk_frame_comb R_tt R_tt R_tt _ _ _ (fun a H => H) (fun a H => H) FBX FXY_tt) as FBY.
  pose proof (tk_frame_comb R_tt RE_Ff R_tt _ _ _ (fun a H => H) (fun a H => R_nq_tt a (RE_Ff_nq a H)) FBY FFf)
    as FBf.
  constructor.
  - (* te_len *) exact (tte_tx_len _ r HF).
  - (* te_frame *) exact FBf.
  - (* te_raw *) exact Hraw.
  - (* te_queued *) transitivity (S_queued B1); [exact (tte_rd1_queued _ _ F1f) | exact Hq1].
  - (* te_sq *) transitivity (sq B1); [| exact Hsq].
    exact (tte_rd1_sq _ _ F1f (tte_queued_bound B B1 m Hq1 HqB)).
  - (* te_nq *) exact Hnq.
  - (* te_hq *) exact Hhq.
  - (* te_st_in *) exact Hin.
  - (* te_st_out *) exact Hout.
  - (* te_ds *) transitivity (S_display_sent (w_dispS B1 (tt_hd B m) (g_now B))); [exact (tte_rdD_ds _ _ FDf) |].
    etransitivity; [exact (tk_dispS_ds B1 (tt_hd B m) (g_now B) HB1) |].
    destruct (tt_hd B m =? 0); [exact (tte_rdq_ds _ _ FB1) | reflexivity].
  - (* te_dl *) transitivity (S_last_display_us (w_dispS B1 (tt_hd B m) (g_now B))); [exact (tte_rdD_dl _ _ FDf) |].
    etransitivity; [exact (tk_dispS_dl B1 (tt_hd B m) (g_now B) HB1 (tte_now_bound B)) |].
    destruct (tt_hd B m =? 0); [exact (tte_rdq_dl _ _ FB1) | reflexivity].
  - (* te_ms *) exact Hms.
  - (* te_ml *) exact Hml.
  - (* te_hc *) transitivity (S_host_counter B6); [exact (tte_rd6_hc _ _ F6f) | exact Hhc].
  - (* te_mhc *) transitivity (M_host_counter (w_io8 B6 (tt_send B m))); [exact (tte_rdX_mhc _ _ FXf) |].
    exact (tte_io8_mhc B6 (tt_send B m) HB6 Hsb).
  - (* te_on *) transitivity (S_inflight B6); [exact (tte_rd6_on _ _ F6f) | exact Hon].
  - (* te_mon *) transitivity (M_fly_on (w_fly Y (tt_send B m) (tt_fr B m))); [exact (tte_rdT_mon _ _ FT) |].
    exact (tte_fly_on Y (tt_send B m) (tt_fr B m) HY Hfl).
  - (* te_ctr *) transitivity (S_inflight_counter B6); [exact (tte_rd6_ctr _ _ F6f) | exact Hctr].
  - (* te_mctr *) transitivity (M_fly_counter (w_fly Y (tt_send B m) (tt_fr B m))); [exact (tte_rdT_mctr _ _ FT) |].
    exact (tte_fly_ctr Y (tt_send B m) (tt_fr B m) HY Hfl Hsb).
  - (* te_ret *) transitivity (S_inflight_retries B6); [exact (tte_rd6_ret _ _ F6f) | exact Hret].
  - (* te_mret *) transitivity (M_fly_retries (w_fly Y (tt_send B m) (tt_fr B m))); [exact (tte_rdT_mret _ _ FT) |].
    exact (tte_fly_ret Y (tt_send B m) (tt_fr B m) HY Hfl).
  - (* te_sent *) transitivity (S_inflight_sent_us B6); [exact (tte_rd6_sent _ _ F6f) | exact Hsent].
  - (* te_msent *) transitivity (M_fly_sent (w_fly Y (tt_send B m) (tt_fr B m))); [exact (tte_rdT_msent _ _ FT) |].
    transitivity (g_now Y); [exact (tte_fly_sent Y (tt_send B m) (tt_fr B m) HY Hfl) | exact Hnow].
  - (* te_flen *) transitivity (S_inflight_len B6); [exact (tte_rd6_flen _ _ F6f) | exact Hflen].
  - (* te_mflen *) transitivity (M_fly_len (w_fly Y (tt_send B m) (tt_fr B m))); [exact (tte_rdT_mflen _ _ FT) |].
    transitivity (Z.of_nat (length (tt_fr B m))); [exact (tte_fly_flen Y (tt_send B m) (tt_fr B m) HY Hfl) |].
    exact HLfr.
  - (* te_mcmd *) transitivity (M_fly_cmd (w_fly Y (tt_send B m) (tt_fr B m))); [exact (tte_rdT_mcmd _ _ FT) |].
    exact (tte_fly_cmd Y (tt_send B m) (tt_fr B m) HY Hfl).
  - (* te_fr *) transitivity (sub B6 A_S_inflight_frame (Z.to_nat (frame_len (length (tt_body B m))))); [| exact Hfr].
    exact (tte_rd6_ifr _ _ _ F6f (tte_flen_nat _ Hbody)).
  - (* te_mfr *)
    transitivity (sub (w_fly Y (tt_send B m) (tt_fr B m)) A_M_fly_frame (Z.to_nat (frame_len (length (tt_body B m))))).
    + exact (tte_rdT_mfr _ _ _ FT (tte_flen_nat _ Hbody)).
    + exact (tte_fly_fr Y (tt_send B m) (tt_fr B m) _ HY Hfl (tte_to_nat_len _ _ HLfr)).
  - (* te_fail *) transitivity (g_fail_next (w_io8 B6 (tt_send B m))); [exact (tte_rdX_fail _ _ FXf) |].
    exact (tte_io8_fail B6 (tt_send B m) HB6).
Qed.

Lemma tt_end_raw : forall B B1 B6 m r,
  length B = WN -> g_raw B <> 0 -> S_queued B <= QUEUE_MAX ->
  length B1 = WN -> wframe R_qs B B1 -> sq B1 = unpick m (sq B) ->
  S_queued B1 = Z.of_nat (length (unpick m (sq B))) ->
  length B6 = WN -> wframe R_ss (w_dispS B1 (tt_hd B m) (g_now B)) B6 ->
  S_host_counter B6 = tt_send B m -> S_inflight B6 = 1 -> S_inflight_counter B6 = tt_send B m ->
  S_inflight_retries B6 = 0 -> S_inflight_sent_us B6 = g_now B ->
  S_inflight_len B6 = frame_len (length (tt_body B m)) ->
  Z.of_nat (length (tt_fr B m)) = frame_len (length (tt_body B m)) ->
  sub B6 A_S_inflight_frame (Z.to_nat (frame_len (length (tt_body B m)))) = tt_fr B m ->
  (length (tt_body B m) <= 1484)%nat ->
  tt_end B (w_tx (w_fly (w_io8 B6 (tt_send B m)) (tt_send B m) (tt_fr B m)) r) m.
Proof.
  intros B B1 B6 m r HB Hraw HqB HB1 FB1 Hsq Hq1 HB6 F6 Hhc Hon Hctr Hret Hsent Hflen HLfr Hfr Hbody.
  pose proof (tte_frl _ _ Hbody HLfr) as Hfl.
  pose proof (tte_io8_len B6 (tt_send B m) HB6) as HX.
  pose proof (tte_fly_len _ (tt_send B m) (tt_fr B m) HX Hfl) as HF.
  pose proof (tk_frame_comb RE_fl RE_tx RE_Ff _ _ _ (fun a H => or_introl H) (fun a H => or_intror H)
    (tte_fly_frame _ (tt_send B m) (tt_fr B m) HX Hfl) (tte_tx_frame _ r HF)) as FFf.
  pose proof (tk_frame_comb R_lib RE_io RE_BX _ _ _ (fun a H => or_introl H) (fun a H => or_intror H)
    (tte_stage_B6 B B1 B6 m HB1 FB1 F6) (tte_io8_frame B6 (tt_send B m) HB6)) as FBX.
  refine (tte_gen B B1 B6 (w_io8 B6 (tt_send B m)) _ m r eq_refl HB HB1 FB1 Hsq Hq1 HqB HB6 F6 Hhc Hon Hctr Hret
    Hsent Hflen HLfr Hfr Hbody HX (wframe_refl _ _) (wframe_refl _ _) (tte_rdBX_now _ _ FBX) _ _ _ _ _ _ _).
  - (* te_raw *) intros _. exact (tk_frame_comb RE_BX RE_Ff R_nq _ _ _ RE_BX_nq RE_Ff_nq FBX FFf).
  - (* te_nq *) intros H. exfalso. exact (Hraw H).
  - (* te_hq *) intros H. exfalso. exact (Hraw H).
  - (* te_st_in *) intros H. exfalso. exact (Hraw H).
  - (* te_st_out *) intros H. exfalso. exact (Hraw H).
  - (* te_ms *) apply tte_shape_raw; [exact Hraw |].
    transitivity (M_display_sent (w_io8 B6 (tt_send B m))); [exact (tte_rdF_md _ _ FFf) | exact (tte_rdBX_md _ _ FBX)].
  - (* te_ml *) apply tte_shape_raw; [exact Hraw |].
    transitivity (M_last_display (w_io8 B6 (tt_send B m))); [exact (tte_rdF_ml _ _ FFf) | exact (tte_rdBX_ml _ _ FBX)].
Qed.

Lemma tt_end_tagged : forall B B1 B6 Bs m r,
  length B = WN -> g_raw B = 0 -> S_queued B <= QUEUE_MAX -> g_nq B <= QUEUE_MAX ->
  (forall i, 0 <= i < g_nq B -> Q_at B i < CMDS_MAX) ->
  length B1 = WN -> wframe R_qs B B1 -> sq B1 = unpick m (sq B) ->
  S_queued B1 = Z.of_nat (length (unpick m (sq B))) ->
  length B6 = WN -> wframe R_ss (w_dispS B1 (tt_hd B m) (g_now B)) B6 ->
  S_host_counter B6 = tt_send B m -> S_inflight B6 = 1 -> S_inflight_counter B6 = tt_send B m ->
  S_inflight_retries B6 = 0 -> S_inflight_sent_us B6 = g_now B ->
  S_inflight_len B6 = frame_len (length (tt_body B m)) ->
  Z.of_nat (length (tt_fr B m)) = frame_len (length (tt_body B m)) ->
  sub B6 A_S_inflight_frame (Z.to_nat (frame_len (length (tt_body B m)))) = tt_fr B m ->
  (length (tt_body B m) <= 1484)%nat ->
  length Bs = WN -> wframe (fun a => R_cs a \/ R_hq a) (w_io8 B6 (tt_send B m)) Bs ->
  hq Bs = unpick m (hq (w_io8 B6 (tt_send B m))) ->
  g_nq Bs = Z.of_nat (length (unpick m (hq (w_io8 B6 (tt_send B m))))) ->
  (forall k, 0 <= k < CMDS_MAX -> Cmd_st Bs k =
     if existsb (Z.eqb k) (pick m (hq (w_io8 B6 (tt_send B m)))) then SENT else Cmd_st (w_io8 B6 (tt_send B m)) k) ->
  tt_end B (w_tx (w_fly (w_dispM Bs (tt_hd B m)) (tt_send B m) (tt_fr B m)) r) m.
Proof.
  intros B B1 B6 Bs m r HB Hraw HqB HnqB HQ HB1 FB1 Hsq Hq1 HB6 F6 Hhc Hon Hctr Hret Hsent Hflen HLfr Hfr Hbody
    HBs FBs HhqBs HnqBs HstBs.
  pose proof (tte_frl _ _ Hbody HLfr) as Hfl.
  pose proof (tte_dispM_len Bs (tt_hd B m) HBs) as HM.
  pose proof (tte_dispM_frame Bs (tt_hd B m) HBs) as FM.
  pose proof (tte_fly_len _ (tt_send B m) (tt_fr B m) HM Hfl) as HF.
  pose proof (tk_frame_comb RE_fl RE_tx RE_Ff _ _ _ (fun a H => or_introl H) (fun a H => or_intror H)
    (tte_fly_frame _ (tt_send B m) (tt_fr B m) HM Hfl) (tte_tx_frame _ r HF)) as FFf.
  pose proof (tk_frame_comb RE_dm RE_Ff RE_Sf _ _ _ (fun a H => or_introl H) (fun a H => or_intror H) FM FFf) as FSf.
  pose proof (wframe_weaken _ RE_hi _ _ R_cshq_hi FBs) as FXS.
  pose proof (tk_frame_comb R_lib RE_io RE_BX _ _ _ (fun a H => or_introl H) (fun a H => or_intror H)
    (tte_stage_B6 B B1 B6 m HB1 FB1 F6) (tte_io8_frame B6 (tt_send B m) HB6)) as FBX.
  pose proof (tk_frame_comb (fun a => R_cs a \/ R_hq a) RE_dm R_tt _ _ _ R_cshq_tt
    (fun a H => R_nq_tt a (RE_dm_nq a H)) FBs FM) as FXM.
  pose proof (tk_frame_comb RE_BX (fun a => R_cs a \/ R_hq a) R_tt _ _ _ tte_BX_tt R_cshq_tt FBX FBs) as FBS.
  pose proof (tk_frame_comb RE_BX R_tt R_tt _ _ _ tte_BX_tt (fun a H => H) FBX FXM) as FBM.
  pose proof (tte_hq_BX _ _ FBX (tte_le_cmds _ HnqB)) as EhqX.
  refine (tte_gen B B1 B6 (w_dispM Bs (tt_hd B m)) _ m r eq_refl HB HB1 FB1 Hsq Hq1 HqB HB6 F6 Hhc Hon Hctr Hret
    Hsent Hflen HLfr Hfr Hbody HM FXM
    (tk_frame_comb RE_hi RE_dm (fun a => RE_hi a \/ RE_dm a) _ _ _ (fun a H => or_introl H) (fun a H => or_intror H)
       FXS FM)
    (tte_rdtt_now _ _ FBM) _ _ _ _ _ _ _).
  - (* te_raw *) intros H. exfalso. exact (H Hraw).
  - (* te_nq *) intros _. transitivity (g_nq Bs); [exact (tte_rdS_nq _ _ FSf) |].
    transitivity (Z.of_nat (length (unpick m (hq (w_io8 B6 (tt_send B m)))))); [exact HnqBs |].
    exact (f_equal (fun l => Z.of_nat (length (unpick m l))) EhqX).
  - (* te_hq *) intros _. transitivity (hq Bs); [exact (tte_hq_Sf _ _ FSf) |].
    transitivity (unpick m (hq (w_io8 B6 (tt_send B m)))); [exact HhqBs |].
    exact (f_equal (@unpick Z m) EhqX).
  - (* te_st_in *) intros _ k Hk. unfold tt_Ts in Hk.
    pose proof (tte_Ts_bound B m k HQ Hk) as Hk'.
    transitivity (Cmd_st Bs k); [exact (tte_rdS_cmd _ _ k FSf (proj1 Hk')) |].
    etransitivity; [exact (HstBs k Hk') |].
    apply tte_if_true. apply existsb_exists. exists k. split.
    + exact (@eq_ind_r _ (hq B) (fun l => In k (pick m l)) Hk (hq (w_io8 B6 (tt_send B m))) EhqX).
    + apply Z.eqb_refl.
  - (* te_st_out *) intros _ k Hk Hn. unfold tt_Ts in Hn.
    pose proof (tte_cmdN k Hk) as Hk'.
    transitivity (Cmd_st Bs k); [exact (tte_rdS_cmd _ _ k FSf (proj1 Hk')) |].
    etransitivity; [exact (HstBs k Hk') |].
    assert (E : existsb (Z.eqb k) (pick m (hq (w_io8 B6 (tt_send B m)))) = false).
    { destruct (existsb (Z.eqb k) (pick m (hq (w_io8 B6 (tt_send B m))))) eqn:E'; [|reflexivity].
      exfalso. apply existsb_exists in E'. destruct E' as [x [Hx Hkx]]. apply Z.eqb_eq in Hkx. subst x.
      apply Hn. exact (@eq_ind _ (hq (w_io8 B6 (tt_send B m))) (fun l => In k (pick m l)) Hx (hq B) EhqX). }
    etransitivity; [exact (tte_if_false _ SENT _ E) |].
    exact (tte_rdBX_cmd _ _ k FBX Hk').
  - (* te_ms *) transitivity (M_display_sent (w_dispM Bs (tt_hd B m))); [exact (tte_rdF_md _ _ FFf) |].
    etransitivity; [exact (tte_dispM_ds Bs (tt_hd B m) HBs) |].
    apply tte_shape_tagged; [exact Hraw | reflexivity |].
    transitivity (M_display_sent (w_io8 B6 (tt_send B m))); [exact (tte_rdH_md _ _ FXS) | exact (tte_rdBX_md _ _ FBX)].
  - (* te_ml *) transitivity (M_last_display (w_dispM Bs (tt_hd B m))); [exact (tte_rdF_ml _ _ FFf) |].
    etransitivity; [exact (tte_dispM_dl Bs (tt_hd B m) HBs) |].
    apply tte_shape_tagged; [exact Hraw | exact (tte_rdtt_now _ _ FBS) |].
    transitivity (M_last_display (w_io8 B6 (tt_send B m))); [exact (tte_rdH_ml _ _ FXS) | exact (tte_rdBX_ml _ _ FBX)].
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 1878 of its 1989 lines of code are new or changed and 815 lines of the source are left out. *)
(* io_send_seg_tail: the DATA arm's tail of the image-A walk of io_send (fuzz_transport.asan e89be137db17, entry
   0x82d60 = TImgA.v ti_io_send timg_A; the statement is lib/A/Prog/io_send_cg.v transport_io_send_cg_holds_stmt),
   0x832cc .. 0x83334 (io_send_cg.v header lines 135-143), in continuation form: ios_tail_seg (end of file), from
   either entry of the tail to transport_text + IOS_FLY (0x83338) with the cut facts ios_tail_at at the world
   io_send_segs.v ios_B6 frame B5 gives.

   - The keepalive case (ios_tail_ka, 0x832cc): check_keepalive_due through TransportGCg.v gx_call_leaf and
     DgnTransportLeafb.v decode_leafb_journal; then the store of next_ka + keepalive_ms * 1000 at M + 48 and the
     `bltu` on g_now, whose fall-through stores g_now + keepalive_ms * 1000 there (TCb.v h_ms_m does not wrap: the
     factor is a 4-byte value).
   - The check_latest_sent case (ios_tail_sent, 0x83304): the `bnez` on g_raw; check_latest_sent from its G-form
     contract (ios_cls_at: the post folded with TransportGCg.v dk_kept_trans_out_g, the int at sp + 4 being a byte of
     io_send's own window; the frame carried by ios_src_cls, io_send_seg_src.v ios_src_ok_acall_g for a callee that
     writes G: the frame inside g_s is kept by the world relation, check_latest_sent_m writing nothing below g_cmd);
     the `beqz` on the int; check_latest_display through the leaf bridge; the stores of g_now at M + 64 and of 1 at
     M + 72.
   Each world change is one io_send_seg_world.v ios_tw_step at the M row; each store is a byte of G in iosend_wr. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  io_send_cg io_send_segs io_send_seg_cut io_send_seg_world io_send_seg_frm io_send_seg_src.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_sent_frame_cg check_latest_sent_cg m_lost_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  check_keepalive_due_cg check_latest_display_cg check_keepalive_due_c check_latest_display_c check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require DgnTransportLeafb LeafCgKit AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TSess0 TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Frame ExecF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
Module LKD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_keepalive_due_cg.
Module LLD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_display_cg.
Module CKD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_keepalive_due_c.
Module CLD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_display_c.
Module CSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_c.
Module LB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.DgnTransportLeafb.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.AsanKA.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LFrame := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Frame.
Module LExecF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.ExecF.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The model: what check_latest_sent leaves below g_cmd, and *display  *)
(* ------------------------------------------------------------------ *)

(* The world bytes below g_cmd (M, g_s): no store of check_latest_sent reaches them. *)
Definition IOS_LOWN : nat := Z.to_nat TW.OFF_g_cmd.

Lemma ios_len_upd_ge : forall (bs v : list byte) k, (length bs <= length (TW.upd bs k v))%nat.
Proof. intros bs v k. unfold TW.upd. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

Lemma ios_firstn_upd : forall (bs v : list byte) k n, (n <= Z.to_nat k)%nat -> (n <= length bs)%nat ->
  firstn n (TW.upd bs k v) = firstn n bs.
Proof.
  intros bs v k n H1 H2. unfold TW.upd. rewrite firstn_app, length_firstn.
  replace (n - Nat.min (Z.to_nat k) (length bs))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r, firstn_firstn. f_equal. lia.
Qed.

Lemma ios_nth_firstn : forall (l : list byte) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros l n i d Hi. destruct (Nat.lt_ge_cases i (length l)) as [Hl|Hl].
  - rewrite <- (firstn_skipn n l) at 2. rewrite app_nth1; [reflexivity|]. rewrite length_firstn. lia.
  - rewrite (nth_overflow (firstn n l)) by (rewrite length_firstn; lia). rewrite (nth_overflow l) by lia.
    reflexivity.
Qed.

Lemma ios_inv2 : forall (x y : list byte) (a b : Z), Some (x, a) = Some (y, b) -> y = x /\ b = a.
Proof. intros x y a b H. injection H as H1 H2. split; symmetry; assumption. Qed.
Lemma ios_inv2o : forall (x y : list byte) (a b : option Z), Some (x, a) = Some (y, b) -> y = x /\ b = a.
Proof. intros x y a b H. injection H as H1 H2. split; symmetry; assumption. Qed.

(* A signed 32-bit range: the quotient by 2 ^ 31 is 0 or -1. *)
Lemma ios_s32_shiftr : forall x, -2^31 <= x < 2^31 <-> (Z.shiftr x 31 = 0 \/ Z.shiftr x 31 = -1).
Proof.
  intros x. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod x (2^31) ltac:(lia)) as D. pose proof (Z.mod_pos_bound x (2^31) ltac:(lia)) as M.
  split; [intros H | intros [H|H]]; lia.
Qed.

Lemma ios_lor_s32 : forall a b, -2^31 <= a < 2^31 -> -2^31 <= b < 2^31 -> -2^31 <= Z.lor a b < 2^31.
Proof.
  intros a b Ha Hb. apply ios_s32_shiftr. apply ios_s32_shiftr in Ha. apply ios_s32_shiftr in Hb.
  rewrite Z.shiftr_lor.
  destruct Ha as [-> | ->]; destruct Hb as [-> | ->]; [left | right | right | right]; reflexivity.
Qed.

(* tagged_of leaves the world and gives a serial >= 0. *)
Lemma ios_tag_inv : forall B b n B' s, TC.tagged_of_m B b n = Some (B', Some s) -> B' = B /\ 0 <= s.
Proof.
  intros B b n B' s H. unfold TC.tagged_of_m in H. cbv zeta in H.
  repeat (match type of H with
          | context [if ?c then _ else _] => destruct c; cbv beta iota in H
          end); try discriminate H.
  apply ios_inv2o in H. destruct H as [-> Hs]. split; [reflexivity|].
  injection Hs as ->. apply Z.lor_nonneg.
  split; [unfold DSpec.at8, DSpec.bz; exact (proj1 (bv_unsigned_in_range _ _))|].
  apply Z.shiftl_nonneg. unfold DSpec.at8, DSpec.bz; exact (proj1 (bv_unsigned_in_range _ _)).
Qed.

(* q_remove's loop stores only into g_q (at k >= 0). *)
Lemma ios_qrl_low : forall fuel B serial nq i k B' k', TC.q_remove_loop fuel B serial nq i k = Some (B', k') ->
  0 <= k -> (IOS_LOWN <= length B)%nat -> (IOS_LOWN <= length B')%nat /\ firstn IOS_LOWN B' = firstn IOS_LOWN B.
Proof.
  induction fuel as [|fuel IH]; intros B serial nq i k B' k' H Hk HL; cbn [TC.q_remove_loop] in H; [discriminate H|].
  destruct (i <? nq); [|apply ios_inv2 in H; destruct H as [-> _]; split; [exact HL | reflexivity]].
  destruct (TC.CMDS_MAX <=? i); [discriminate H|].
  destruct (TW.Q_at B i =? serial).
  - exact (IH _ _ _ _ _ _ _ H Hk HL).
  - destruct (IH _ _ _ _ _ _ _ H ltac:(lia) (Nat.le_trans _ _ _ HL (ios_len_upd_ge _ _ _))) as [H1 H2].
    split; [exact H1|]. rewrite H2. unfold TW.set_Q_at. apply ios_firstn_upd; [|exact HL].
    unfold IOS_LOWN, TW.OFF_g_cmd, TW.OFF_g_q. lia.
Qed.

(* check_latest_sent's loop stores only into g_cmd (st of a serial >= 0), g_q and g_nq; *display stays a signed
   32-bit value (Cmd_display is one). *)
Lemma ios_lsl_low : forall fuel B body len pos disp B' d,
  TC.latest_sent_loop fuel B body len pos disp = Some (B', d) ->
  (IOS_LOWN <= length B)%nat -> -2^31 <= disp < 2^31 ->
  (IOS_LOWN <= length B')%nat /\ firstn IOS_LOWN B' = firstn IOS_LOWN B /\ -2^31 <= d < 2^31.
Proof.
  induction fuel as [|fuel IH]; intros B body len pos disp B' d H HL Hd; cbn [TC.latest_sent_loop] in H;
    [discriminate H|].
  destruct (pos <? len); [|apply ios_inv2 in H; destruct H as [-> ->]; split; [exact HL | split; [reflexivity | exact Hd]]].
  cbv zeta in H.
  destruct (TC.tagged_of_m B (skipn (Z.to_nat pos) body) (len - pos)) as [[B0 [s|]]|] eqn:Et;
    cbv beta iota zeta in H; [|discriminate H|discriminate H].
  destruct (ios_tag_inv _ _ _ _ _ Et) as [_ Hs].
  match type of H with context [if ?c then None else _] => destruct c; [discriminate H|] end.
  unfold TC.q_remove_m in H.
  destruct (TC.q_remove_loop (S (Z.to_nat TC.CMDS_MAX)) (TW.set_Cmd_st B s TC.SENT) s
              (TW.g_nq (TW.set_Cmd_st B s TC.SENT)) 0 0) as [[B1 k]|] eqn:Eq;
    cbv beta iota in H; [|discriminate H].
  assert (L1 : (IOS_LOWN <= length (TW.set_Cmd_st B s TC.SENT))%nat)
    by exact (Nat.le_trans _ _ _ HL (ios_len_upd_ge _ _ _)).
  assert (F1 : firstn IOS_LOWN (TW.set_Cmd_st B s TC.SENT) = firstn IOS_LOWN B).
  { unfold TW.set_Cmd_st, TW.A_Cmd_st. apply ios_firstn_upd; [|exact HL]. unfold IOS_LOWN. lia. }
  destruct (ios_qrl_low _ _ _ _ _ _ _ _ Eq ltac:(lia) L1) as [L2 F2].
  assert (L3 : (IOS_LOWN <= length (TW.set_g_nq B1 k))%nat) by exact (Nat.le_trans _ _ _ L2 (ios_len_upd_ge _ _ _)).
  assert (F3 : firstn IOS_LOWN (TW.set_g_nq B1 k) = firstn IOS_LOWN B1).
  { unfold TW.set_g_nq. apply ios_firstn_upd; [|exact L2]. unfold IOS_LOWN, TW.OFF_g_cmd, TW.OFF_g_nq. lia. }
  destruct (IH _ _ _ _ _ _ _ H L3 (ios_lor_s32 _ _ Hd (TWL.s32_range _ _))) as (L4 & F4 & D4).
  split; [exact L4|]. split; [|exact D4]. rewrite F4, F3, F2, F1. reflexivity.
Qed.

Lemma ios_cls_low : forall B body len Bs d, TC.check_latest_sent_m B body len = Some (Bs, d) ->
  (IOS_LOWN <= length B)%nat -> firstn IOS_LOWN Bs = firstn IOS_LOWN B /\ -2^31 <= d < 2^31.
Proof.
  intros B body len Bs d H HL. unfold TC.check_latest_sent_m in H.
  destruct (ios_lsl_low _ _ _ _ _ _ _ _ H HL ltac:(lia)) as (_ & F & D). split; [exact F | exact D].
Qed.

(* The keepalive tail's world fields: M.next_ka (M + 48) is apart from g_now and g_cfg.keepalive_ms, and a second
   store of it overwrites the first. *)
Lemma ios_now_nka : forall Bx v, length Bx = Z.to_nat TW.W_LEN -> TW.g_now (TW.set_M_next_ka Bx v) = TW.g_now Bx.
Proof.
intros Bx v HL. unfold TW.g_now, TW.set_M_next_ka, TW.A_M_next_ka.
apply TWL.u_at_upd_out; [unfold TW.OFF_M; lia | unfold TW.OFF_g_now; lia | | ];
  rewrite TWL.length_put; [unfold TW.OFF_M, TW.OFF_g_now; lia | rewrite HL; unfold TW.OFF_M, TW.W_LEN; lia].
Qed.

Lemma ios_cfg_nka : forall Bx v, length Bx = Z.to_nat TW.W_LEN ->
  TW.Cfg_keepalive_ms (TW.set_M_next_ka Bx v) = TW.Cfg_keepalive_ms Bx.
Proof.
intros Bx v HL. unfold TW.Cfg_keepalive_ms, TW.A_Cfg_keepalive_ms, TW.set_M_next_ka, TW.A_M_next_ka.
apply TWL.u_at_upd_out; [unfold TW.OFF_M; lia | unfold TW.OFF_g_cfg; lia | | ];
  rewrite TWL.length_put; [unfold TW.OFF_M, TW.OFF_g_cfg; lia | rewrite HL; unfold TW.OFF_M, TW.W_LEN; lia].
Qed.

Lemma ios_nka_nka : forall Bx a b, length Bx = Z.to_nat TW.W_LEN ->
  TW.set_M_next_ka (TW.set_M_next_ka Bx a) b = TW.set_M_next_ka Bx b.
Proof.
intros Bx a b HL. unfold TW.set_M_next_ka, TW.A_M_next_ka.
apply TWL.upd_upd_same; [unfold TW.OFF_M; lia | rewrite !TWL.length_put; reflexivity |].
rewrite TWL.length_put, HL. unfold TW.OFF_M, TW.W_LEN. lia.
Qed.

(* g_cfg.keepalive_ms * 1000 is below 2 ^ 64: TCb.v h_ms_m does not wrap it. *)
Lemma ios_hms : forall Bx, TC.h_ms_m (TW.Cfg_keepalive_ms Bx) = TW.Cfg_keepalive_ms Bx * 1000.
Proof.
intros Bx. pose proof (TWL.u_at_range Bx TW.A_Cfg_keepalive_ms 4) as R.
change (TW.u_at Bx TW.A_Cfg_keepalive_ms 4) with (TW.Cfg_keepalive_ms Bx) in R. change (8 * Z.of_nat 4) with 32 in R.
unfold TC.h_ms_m, TS0.u64. apply Z.mod_small. lia.
Qed.

(* A world byte below g_cmd is the same in the world check_latest_sent leaves. *)
Lemma ios_cls_nth : forall B body len Bs d i, TC.check_latest_sent_m B body len = Some (Bs, d) ->
  length B = Z.to_nat TW.W_LEN -> 0 <= i < TW.OFF_g_cmd ->
  nth (Z.to_nat i) Bs (Z_to_bv 8 0) = nth (Z.to_nat i) B (Z_to_bv 8 0).
Proof.
  intros B body len Bs d i H HL Hi.
  assert (HL' : (IOS_LOWN <= length B)%nat) by (rewrite HL; unfold IOS_LOWN, TW.OFF_g_cmd, TW.W_LEN; lia).
  destruct (ios_cls_low _ _ _ _ _ H HL') as [F _].
  rewrite <- (ios_nth_firstn Bs IOS_LOWN) by (unfold IOS_LOWN; lia).
  rewrite <- (ios_nth_firstn B IOS_LOWN) by (unfold IOS_LOWN; lia).
  rewrite F. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Image values and the bytes of G                                      *)
(* ------------------------------------------------------------------ *)

Lemma ios_inG_M : forall a, TA_M <= a < TA_M + TW.SZ_M -> inG TG.G_HARNESS a.
Proof. intros a Ha. exact (ios_inG_row _ _ _ a TMAP_A_M Ha). Qed.
Lemma ios_inG_now : forall a, TA_g_now <= a < TA_g_now + TW.SZ_g_now -> inG TG.G_HARNESS a.
Proof. intros a Ha. exact (ios_inG_row _ _ _ a TMAP_A_g_now Ha). Qed.
Lemma ios_inG_cfg : forall a, TA_g_cfg <= a < TA_g_cfg + TW.SZ_g_cfg -> inG TG.G_HARNESS a.
Proof. intros a Ha. exact (ios_inG_row _ _ _ a TMAP_A_g_cfg Ha). Qed.

(* G lies below every stack byte. *)
Lemma ios_inG_low : forall a, inG TG.G_HARNESS a -> TG.G_HARNESS_LO <= a < TG.G_HARNESS_HI.
Proof. intros a Ha. exact (inG_G_HARNESS_hull a Ha). Qed.

Section tail. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The listing's objects the tail reads (M, g_now, g_cfg.keepalive_ms) and its code base. *)
Lemma ios_tail_vals : VAL (A_OBJ 8) = TA_M /\ VAL (A_OBJ 27) = TA_g_now /\ VAL (A_OBJ 30) = TA_g_cfg + 24 /\
  BASE = transport_text.
Proof. vm_compute. repeat split. Qed.

(* A byte of G is never hidden (it is a byte of a loaded segment). *)
Lemma ios_G_vis : forall (W : world segs) a, inG TG.G_HARNESS a -> w_H W (Z_to_bv 64 a) = false.
Proof.
intros W a Ha. destruct (aview segs (w_H W) (fun _ => None) a) as [v|] eqn:E.
- exact (LB.decode_leafb_aview_vis W (fun _ => None) a v E).
- exfalso. exact (gx_rw_vis segs TG.G_HARNESS a G_HARNESS_rw Ha (w_H W) (fun _ => None) E).
Qed.

(* A range of G bytes is a range a leaf's footprint may read. *)
Lemma ios_rng_G : forall (W : world segs) lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> inG TG.G_HARNESS a) ->
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) lo len.
Proof.
intros W lo len H0 H1 HG. apply (LB.decode_leafb_rng W lo len H0 H1). intros a Ha. exact (ios_G_vis W a (HG a Ha)).
Qed.

(* The world relation at the leaf form's view: on the payload bytes the two views agree. *)
Lemma ios_csw : forall (W : world segs) mem Bw,
  tw_at TMAP_A (aview segs (w_H W) mem) Bw -> tw_at TMAP_A (CSW.csw_view mem) Bw.
Proof.
intros W mem Bw H. apply (tw_kept TMAP_A _ _ Bw H). intros x Hx.
unfold CSW.csw_view, aview. cbv beta. f_equal.
exact (LB.decode_leafb_mrd W mem x (ios_G_vis W x (ios_tw_in_G x Hx))).
Qed.

(* garr8 at a later memory whose view keeps the bytes. *)
Lemma ios_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) p l,
  garr8 segs (mrestrict H m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> aview segs H' m' a = aview segs H m a) ->
  garr8 segs (mrestrict H' m') p l.
Proof.
intros H H' m m' p l HG HK j Hj. destruct (HG j Hj) as [HV HR]. split; [|exact HR].
intros kk Hk. assert (kk = 0)%nat by lia. subst kk.
specialize (HV 0%nat Hk).
assert (Hk' : p <= p + Z.of_nat j + Z.of_nat 0 < p + Z.of_nat (length l)) by lia.
pose proof (HK _ Hk') as E. unfold aview in E. cbv beta in E. rewrite HV in E. cbn [option_map] in E.
destruct (mbyte segs (mrestrict H' m') (p + Z.of_nat j + Z.of_nat 0)) as [b'|] eqn:Eb; [|discriminate E].
cbn [option_map] in E. injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* The w bytes at p + off of a struct held by garr8 are the value u_at of its byte list. *)
Lemma ios_val_of_garr8 : forall (mm : word -> option byte) p (SB : list byte) off (n : nat),
  garr8 segs mm p (map DSpec.bz SB) -> 0 <= off -> off + Z.of_nat n <= Z.of_nat (length SB) ->
  val_mem segs mm (p + off) n (TW.u_at SB off n).
Proof.
intros mm p SB off n HG Ho Hn k Hk.
assert (Hj : (Z.to_nat off + k < length (map DSpec.bz SB))%nat) by (rewrite length_map; lia).
destruct (HG _ Hj) as [HV _]. specialize (HV 0%nat ltac:(lia)).
replace (p + off + Z.of_nat k) with (p + Z.of_nat (Z.to_nat off + k) + Z.of_nat 0) by lia.
rewrite HV. f_equal. f_equal.
assert (HL : length (TW.sub SB off n) = n) by (apply TWL.length_sub; lia).
assert (E1 : YO0f.le_byte (TW.u_at SB off n) n k = bv_unsigned (nth (Z.to_nat off + k) SB (Z_to_bv 8 0))).
{ unfold TW.u_at. pose proof (tw_le_byte_ble (TW.sub SB off n) k (Z_to_bv 8 0)) as T. rewrite HL in T.
  rewrite (T Hk). f_equal. apply tw_nth_sub; [lia | exact Hk | lia]. }
assert (E2 : YO0f.le_byte (nth (Z.to_nat off + k) (map DSpec.bz SB) 0) 1 0 =
             bv_unsigned (nth (Z.to_nat off + k) SB (Z_to_bv 8 0))).
{ rewrite (nth_indep _ 0 (DSpec.bz (Z_to_bv 8 0))) by exact Hj. rewrite map_nth.
  apply tw_le_byte1. unfold DSpec.bz. exact (bv_unsigned_in_range _ _). }
exact (eq_trans E2 (eq_sym E1)).
Qed.

(* The body's bytes are the frame's from offset 30. *)
Lemma ios_garr8_body : forall (mm : word -> option byte) p (frame : list byte) (blen : nat),
  garr8 segs mm p (map DSpec.bz frame) -> (30 + blen <= length frame)%nat ->
  garr8 segs mm (p + 30) (TW.zs (firstn blen (skipn 30 frame))).
Proof.
intros mm p frame blen HG HL j Hj. unfold TW.zs in *. rewrite length_map, length_firstn, length_skipn in Hj.
assert (Hj' : (30 + j < length (map DSpec.bz frame))%nat) by (rewrite length_map; lia).
destruct (HG _ Hj') as [HV HR].
assert (EN : nth j (map bv_unsigned (firstn blen (skipn 30 frame))) 0 = nth (30 + j) (map DSpec.bz frame) 0).
{ rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, length_firstn, length_skipn; lia).
  rewrite map_nth. rewrite (nth_indep _ 0 (DSpec.bz (Z_to_bv 8 0))) by exact Hj'. rewrite map_nth.
  unfold DSpec.bz. f_equal. rewrite ios_nth_firstn by lia.
  rewrite <- (firstn_skipn 30 frame) at 2. rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn. replace (30 + j - Nat.min 30 (length frame))%nat with j by lia. reflexivity. }
rewrite EN. split; [|exact HR].
intros kk Hk. replace (p + 30 + Z.of_nat j + Z.of_nat kk) with (p + Z.of_nat (30 + j) + Z.of_nat kk) by lia.
exact (HV kk Hk).
Qed.

(* What a step keeps, at a later world (dk_kept_step_g with the allocator state's AR at any memory). *)
Lemma ios_kept_step : forall G lyc Sc (Wa : world segs) mema mda (W : world segs) memc (W2 : world segs) memX memY
    slo shi (Eo Zs : Z -> Prop),
  AR_laws segs B -> @AR rc segs B lyc Sc Wa mema mda ->
  acall_kept_g segs B G lyc Sc W memc W2 memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) memY a = aview segs (w_H W2) memX a) ->
  (forall a, apresent (w_H W2) memX a -> apresent (w_H W2) memY a) ->
  (forall a, Zs a -> alloc_ceiling <= a < 2 ^ 64 -> slo <= a < shi) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> Zs (b + i) -> Eo (b + i)) ->
  (forall a, Zs a -> in_img segs a -> ~ inG G a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> False) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     Zs a -> Eo a) ->
  acall_kept_g segs B G lyc Sc W memc W2 memY slo shi Eo.
Proof.
intros G lyc Sc Wa mema mda W memc W2 memX memY slo shi Eo Zs LAWS HAR (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr
  HZw HZb HZi HZf.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite (Hkp a ltac:(lia) (fun HZ => Hw (HZw a HZ Ha))). exact (K1 a Ha Hw).
- intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc Wa mema mda b m HAR Hb) as (_ & H4096 & Hce & _).
  rewrite (Hkp (b + i) ltac:(lia) (fun HZ => Hn (HZb b m i Hb Hi HZ))). exact (K2 b m i Hb Hi Hn).
- intros a Hi HnG Hno He. pose proof (transport_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite (Hkp a ltac:(lia) (fun HZ => HZi a HZ Hi HnG Hno He)). exact (K3 a Hi HnG Hno He).
- intros cid pos a Hin Hr Hn.
  destruct (frames_bounds segs B LAWS lyc Sc Wa mema mda cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  assert (Ha : 0 <= a < 2 ^ 64).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  rewrite (Hkp a Ha (fun HZ => Hn (HZf cid pos a Hin Hr HZ))). exact (K4 cid pos a Hin Hr Hn).
- intros a Ha Hw Hp. apply Hgr. exact (K5 a Ha Hw Hp).
- intros a Ha. apply Hgr. exact (K6 a Ha).
Qed.

(* A step that changes only io_send's stack window and bytes of iosend_wr keeps the running kept fact. *)
Lemma ios_kept_win : forall lyc Sc (Wa : world segs) mema mda (W : world segs) memc (W2 : world segs) memX memY sp n,
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS -> @AR rc segs B lyc Sc Wa mema mda ->
  alloc_ceiling <= sp - IOSEND_STK -> sp <= 2 ^ 47 ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 memX (sp - IOSEND_STK) sp (iosend_wr n) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - IOSEND_STK <= a < sp) -> ~ iosend_wr n a ->
     aview segs (w_H W2) memY a = aview segs (w_H W2) memX a) ->
  (forall a, apresent (w_H W2) memX a -> apresent (w_H W2) memY a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 memY (sp - IOSEND_STK) sp (iosend_wr n).
Proof.
intros lyc Sc Wa mema mda W memc W2 memX memY sp n LAWS HGX HAR Hce Hsp KP Hkp Hgr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (ios_kept_step TG.G_HARNESS lyc Sc Wa mema mda W memc W2 memX memY (sp - IOSEND_STK) sp (iosend_wr n)
  (fun a => (sp - IOSEND_STK <= a < sp) \/ iosend_wr n a) LAWS HAR KP).
- intros a Ha Hn. apply Hkp; [exact Ha | intros H; apply Hn; left; exact H | intros H; apply Hn; right; exact H].
- exact Hgr.
- intros a [Hw | Hw] Hc; [exact Hw|]. exfalso.
  pose proof (transport_segs_low a (proj1 (HGX a (ios_wr_inG n a Hw)))) as Hl. unfold kLowMemEnd in Hl. lia.
- intros b m i Hb Hi [Hw | Hw]; [|exact Hw]. exfalso.
  destruct (al_blocks _ _ LAWS lyc Sc Wa mema mda b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
- intros a [Hw | Hw] Hi HnG _ _.
  + pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
  + apply HnG. exact (ios_wr_inG n a Hw).
- intros cid pos a Hin Hr [Hw | Hw]; [|exact Hw]. exfalso.
  destruct (frames_bounds segs B LAWS lyc Sc Wa mema mda cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.

(* A written range E keeps nothing more than E' on the block and frame bytes when it adds only bytes at or above
   alloc_ceiling (the caller's own machine frame). *)
Lemma ios_kept_shrink : forall G lyc Sc (Wa : world segs) mema mda (W : world segs) memc (W2 : world segs) mem2
    slo shi (E E' : Z -> Prop),
  AR_laws segs B -> @AR rc segs B lyc Sc Wa mema mda ->
  (forall a, E a -> a < alloc_ceiling -> E' a) ->
  acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi E -> acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi E'.
Proof.
intros G lyc Sc Wa mema mda W memc W2 mem2 slo shi E E' LAWS HAR HE (K1 & K2 & K3 & K4 & K5 & K6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact K1|]. split.
{ intros b m i Hb Hi Hn. apply (K2 b m i Hb Hi). intros HE0. apply Hn. apply HE; [exact HE0|].
  destruct (al_blocks _ _ LAWS lyc Sc Wa mema mda b m HAR Hb) as (_ & H4096 & Hbc & _). lia. }
split; [exact K3|]. split.
{ intros cid pos a Hin Hr Hn. apply (K4 cid pos a Hin Hr). intros HE0. apply Hn. apply HE; [exact HE0|].
  destruct (frames_bounds segs B LAWS lyc Sc Wa mema mda cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
  unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
split; [exact K5 | exact K6].
Qed.

(* A leaf call (the leaf bridge's post, written range WR = []) from io_send's G journal, in continuation form: the
   return state keeps the journal, the callee-saved registers, every byte outside the leaf's window [sp - ESTACK, sp)
   and presence, and the leaf's X. *)
Lemma ios_leaf_call : forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc
    k (o PC : Z) (X : (word -> option byte) -> Prop) (Q : world segs -> config -> Prop),
  AR_laws segs B ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (YK11.getr regsT 1) -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  (LB.decode_leafb_ecall_pre B lyc Sc W regsT memT mdc ->
     SRr segs W (@LCK.cfg_at fx PC regsT memT mdc) (LB.decode_leafb_post B lyc Sc W regsT memT mdc None [] X)) ->
  (forall regs2 mem2 md2,
     ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k ->
     aregs_preserved regsT regs2 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
        aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) ->
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
     X mem2 ->
     SRr segs W (mkCfg (YK11.mkst regs2 (YK11.getr regsT 1) mem2 (YK11.seg_rom segs)) md2) Q) ->
  SRr segs W (mkCfg (YK11.mkst regsT (Z_to_bv 64 PC) memT (YK11.seg_rom segs)) mdc) Q.
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o PC X Q LAWS HJ Hsp Hal Hneg Hbud Hra Hgp Htp
  HLEAF HK.
eapply SRr_bind.
{ apply (@gx_call_leaf fx rc tfib_sink_head segs B TG.G_HARNESS STK sp0 FP ly S W0 mem md own
    lyc Sc W memT mdc k _ (YK11.getr regsT 1)
    (fun regs2 mem2 md2 => aregs_preserved regsT regs2 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\ X mem2) HJ).
  intros memS HJS.
  eapply SRr_mono.
  { exact (@LB.decode_leafb_journal fx rc tfib_sink_head B LAWS W regsT memT STK sp0 FP ly S W0 memS md own lyc Sc
      mdc k o PC None [] X HJS Hsp Hal Hneg Hbud Hra Hgp Htp
      ltac:(intros a Ha; unfold LCK.in_wr in Ha; inversion Ha) HLEAF). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & _ & HK2 & HG2 & HX).
  split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|].
  split; [exact HP|]. split; [|split; [exact HG2 | exact HX]].
  intros a Ha Hn. apply HK2; [exact Ha | exact Hn | intros Hw; unfold LCK.in_wr in Hw; inversion Hw]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HK2 & HG2 & HX).
exact (HK regs2 mem2 md2 HJ2 HP HK2 HG2 HX).
Qed.

(* check_keepalive_due through the leaf form: its footprint premises at a call state whose sp is above G. *)
Lemma ios_ckd_leaf : forall (W : world segs) regsT memT mdc ly2 S2 B5,
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LKD.transport_check_keepalive_due_cg) fx') ->
  tw_at TMAP_A (aview segs (w_H W) memT) B5 -> TC.check_keepalive_due_m B5 = Some (B5, tt) ->
  TG.G_HARNESS_HI + ESTACK <= spZ regsT -> spZ regsT <= 2 ^ 47 ->
  LB.decode_leafb_ecall_pre B ly2 S2 W regsT memT mdc ->
  SRr segs W (@LCK.cfg_at fx (transport_sigma TS_check_keepalive_due) regsT memT mdc)
    (LB.decode_leafb_post B ly2 S2 W regsT memT mdc None [] (fun _ => B5 = B5)).
Proof.
intros W regsT memT mdc ly2 S2 B5 HL Htw Hm Hlo Hhi HPRE.
pose proof (HL fx ly2 S2 W regsT memT mdc (spZ regsT - CKD.CHECK_KEEPALIVE_DUE_FRAME) B5 B5 HPRE) as HC.
cbv zeta in HC.
change (bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))) with (spZ regsT) in HC.
change CKD.CHECK_KEEPALIVE_DUE with (transport_sigma TS_check_keepalive_due) in HC.
unfold LB.decode_leafb_ecall_pre, LCK.ecall_pre in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & Hpres & _).
change (LCK.spZ regsT) with (spZ regsT) in Hpres.
assert (EST : LCK.ESTACK = 4096) by reflexivity. rewrite EST in Hpres.
assert (FR : CKD.CHECK_KEEPALIVE_DUE_FRAME = 16) by reflexivity.
assert (GHI : TG.G_HARNESS_HI = 0x5f3190) by reflexivity.
assert (EE : ESTACK = 4096) by reflexivity.
assert (EM : TA_M = 0x5df160) by reflexivity. assert (EN : TA_g_now = 0x5df100) by reflexivity.
unfold CKD.CHECK_KEEPALIVE_DUE_STATE, CKD.CHECK_KEEPALIVE_DUE_FLY_ON, CKD.CHECK_KEEPALIVE_DUE_NOW,
  CKD.CHECK_KEEPALIVE_DUE_BACKOFF, CKD.CHECK_KEEPALIVE_DUE_NEXT_KA, TW.A_M_state, TW.A_M_fly_on,
  TW.A_M_backoff_until, TW.A_M_next_ka, TW.OFF_M in HC.
assert (GLO : TG.G_HARNESS_LO = 0x5df080) by reflexivity.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SN : TW.SZ_g_now = 8) by reflexivity.
apply HC.
- exact (ios_csw W memT B5 Htw).
- exact Hm.
- apply (LB.decode_leafb_stk W memT); [lia | lia |]. intros a Ha. apply Hpres. lia.
- lia.
- unfold AKA.off_stk. left. change (bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))) with (spZ regsT). lia.
- apply (LB.decode_leafb_rng_vis W memT); [lia | lia |]. intros a Ha. apply Hpres. lia.
- apply ios_rng_G; [lia | lia |]. intros a Ha. apply ios_inG_M. lia.
- apply ios_rng_G; [lia | lia |]. intros a Ha. apply ios_inG_M. lia.
- apply ios_rng_G; [lia | lia |]. intros a Ha. apply ios_inG_now. lia.
- apply ios_rng_G; [lia | lia |]. intros a Ha. apply ios_inG_M. lia.
- apply ios_rng_G; [lia | lia |]. intros a Ha. apply ios_inG_M. lia.
Qed.

(* check_latest_display through the leaf form. *)
Lemma ios_cld_leaf : forall (W : world segs) regsT memT mdc ly2 S2 Bs,
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLD.transport_check_latest_display_cg) fx') ->
  tw_at TMAP_A (aview segs (w_H W) memT) Bs -> TC.check_latest_display_m Bs = Some (Bs, tt) ->
  TG.G_HARNESS_HI + ESTACK <= spZ regsT -> spZ regsT <= 2 ^ 47 ->
  LB.decode_leafb_ecall_pre B ly2 S2 W regsT memT mdc ->
  SRr segs W (@LCK.cfg_at fx (transport_sigma TS_check_latest_display) regsT memT mdc)
    (LB.decode_leafb_post B ly2 S2 W regsT memT mdc None [] (fun _ => Bs = Bs)).
Proof.
intros W regsT memT mdc ly2 S2 Bs HL Htw Hm Hlo Hhi HPRE.
pose proof (HL fx ly2 S2 W regsT memT mdc (spZ regsT - CLD.CHECK_LATEST_DISPLAY_FRAME) Bs Bs HPRE) as HC.
cbv zeta in HC.
change (bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))) with (spZ regsT) in HC.
change CLD.CHECK_LATEST_DISPLAY with (transport_sigma TS_check_latest_display) in HC.
unfold LB.decode_leafb_ecall_pre, LCK.ecall_pre in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & Hpres & _).
change (LCK.spZ regsT) with (spZ regsT) in Hpres.
assert (EST : LCK.ESTACK = 4096) by reflexivity. rewrite EST in Hpres.
assert (FR : CLD.CHECK_LATEST_DISPLAY_FRAME = 16) by reflexivity.
assert (GHI : TG.G_HARNESS_HI = 0x5f3190) by reflexivity.
assert (EE : ESTACK = 4096) by reflexivity.
assert (EM : TA_M = 0x5df160) by reflexivity. assert (EN : TA_g_now = 0x5df100) by reflexivity.
assert (EC : TA_g_cfg = 0x5df080) by reflexivity.
unfold CLD.CHECK_LATEST_DISPLAY_SENT, CLD.CHECK_LATEST_DISPLAY_LAST, CLD.CHECK_LATEST_DISPLAY_GAP,
  TW.A_M_display_sent, TW.A_M_last_display, TW.A_Cfg_display_gap_us, TW.OFF_M, TW.OFF_g_cfg in HC.
assert (GLO : TG.G_HARNESS_LO = 0x5df080) by reflexivity.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SN : TW.SZ_g_now = 8) by reflexivity.
assert (SC : TW.SZ_g_cfg = 60) by reflexivity.
apply HC.
- exact (ios_csw W memT Bs Htw).
- exact Hm.
- apply (LB.decode_leafb_stk W memT); [lia | lia |]. intros a Ha. apply Hpres. lia.
- lia.
- unfold AKA.off_stk. left. change (bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))) with (spZ regsT). lia.
- apply (LB.decode_leafb_rng_vis W memT); [lia | lia |]. intros a Ha. apply Hpres. lia.
- apply ios_rng_G; [lia | lia |]. intros a Ha. apply ios_inG_M. lia.
- apply ios_rng_G; [lia | lia |]. intros a Ha. apply ios_inG_M. lia.
- apply ios_rng_G; [lia | lia |]. intros a Ha. apply ios_inG_now. lia.
- apply ios_rng_G; [lia | lia |]. intros a Ha. apply ios_inG_cfg. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The cut facts of the DATA tail                                       *)
(* ------------------------------------------------------------------ *)

(* What holds at 0x832cc / 0x83304 (the tail's entries) and at IOS_FLY (its exit), at a state (ly2, S2, W2, mem2,
   md2) and the model's world Bx there: io_send_seg_cut.v ios_cur and ios_saved, the struct spec_frame f at sp + 8
   holding the parse of the frame, the frame's bytes and placement at this state, the frame apart from io_send's
   window and placed as iosend_frame_at says, and the world relation at Bx. *)
Definition ios_tail_at (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (p : Z) (frame : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (Bx : list byte) : Prop :=
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem2 md2 /\
  ios_saved W2 mem2 regs /\
  trans_sframe_at W2 mem2 (spZ regs - IOSEND_FRAME + IOS_F_OFF) p (TC.rf frame) /\
  garr8 segs (mrestrict (w_H W2) mem2) p (map DSpec.bz frame) /\
  trans_src_ok B ly2 S2 W2 mem2 p (Z.of_nat (length frame)) /\
  decode_off_win regs IOSEND_STK p (Z.of_nat (length frame)) /\
  iosend_frame_at p (Z.of_nat (length frame)) /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) Bx.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                  *)
(* ------------------------------------------------------------------ *)

Definition IOS_KA : Z := IOS_AT 0x56c.
Definition IOS_KA_RET : Z := IOS_AT 0x570.
Definition IOS_Bx : sv := SLit SHADOW_OFF.

(* A state with no region and no fact: the registers only (the call of a leaf right at a cut). *)
Definition ios_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Definition ios_E0 (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).

Lemma ios_e0_entry : forall (W : world segs) (regs : bvmap 5 word) mem pc,
  st_ok_pi segs VAL (ios_E0 regs) (ios_ss0 pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx. unfold ios_ss0.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- constructor.
- apply pairwise_disjoint_of_extents. cbn. tauto.
- unfold facts_ok. cbn. repeat constructor.
Qed.

Lemma ios_e0_agree : forall regs, env_agree 32 (Ereg regs []) (ios_E0 regs).
Proof.
intros regs. split; [|reflexivity]. intros n Hn. unfold ios_E0. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity.
Qed.

(* After check_keepalive_due (0x832d0): g_cfg.keepalive_ms (object 30, atom 32), M.next_ka (M + 48 through s4 = M,
   atom 33, written) and g_now (object 27, atom 34). *)
Definition ka_cfg_region : YP09.region := YP09.mkRegion (Some (A_OBJ 30)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition ka_nka_region : YP09.region := YP09.mkRegion (Some 20%nat) 48 56 48 56 [YP09.mkChunk 48 (CVal 8 (SOff 33 0))].
Definition ka_now_region : YP09.region := YP09.mkRegion (Some (A_OBJ 27)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition ka_regions : smem := [ka_cfg_region; ka_nka_region; ka_now_region].
Definition ka_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF TA_M TA_M 5); (32%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (A_OBJ 27, mkAF TA_g_now TA_g_now 5); (A_OBJ 30, mkAF (TA_g_cfg + 24) (TA_g_cfg + 24) 3)] [] [].
Definition ss_ka : sstate := mkSS IOS_KA_RET sr_atoms ka_regions None ka_facts.
Definition ios_ka_E (regs : bvmap 5 word) (kams nka now : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 kams; Z_to_bv 64 nka; Z_to_bv 64 now]).

Lemma ios_ka_agree : forall regs kams nka now, env_agree 32 (Ereg regs [Z_to_bv 64 kams; Z_to_bv 64 nka; Z_to_bv 64 now])
  (ios_ka_E regs kams nka now).
Proof.
intros regs kams nka now. split; [|reflexivity]. intros n Hn. unfold ios_ka_E.
rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity.
Qed.

Lemma ios_ka_entry : forall (W : world segs) (regs : bvmap 5 word) mem (Bx : list byte),
  tw_at TMAP_A (aview segs (w_H W) mem) Bx ->
  YK11.getr regs 20 = w64 TA_M ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (ios_ka_E regs (TW.Cfg_keepalive_ms Bx) (TW.M_next_ka Bx) (TW.g_now Bx)) ss_ka
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + IOS_KA_RET)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem Bx Htw H20 Hsp Hsp16.
set (E := ios_ka_E regs (TW.Cfg_keepalive_ms Bx) (TW.M_next_ka Bx) (TW.g_now Bx)).
assert (EM : TA_M = 0x5df160) by reflexivity. assert (EN : TA_g_now = 0x5df100) by reflexivity.
assert (EC : TA_g_cfg = 0x5df080) by reflexivity.
assert (E20 : ew E 20 = Z_to_bv 64 TA_M)
  by (unfold E, ios_ka_E; rewrite (ew_Eimg_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (U20 : bv_unsigned (ew E 20) = TA_M) by (rewrite E20; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (unfold E, ios_ka_E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 (TW.Cfg_keepalive_ms Bx))
  by (unfold E, ios_ka_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (TW.M_next_ka Bx))
  by (unfold E, ios_ka_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (TW.g_now Bx))
  by (unfold E, ios_ka_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EOB : forall j, (j < 95)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
  by (intros j Hj; unfold E, ios_ka_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
destruct ios_tail_vals as (V8 & V27 & V30 & VB).
assert (U27 : bv_unsigned (ew E (A_OBJ 27)) = TA_g_now)
  by (rewrite (EOB 27%nat ltac:(lia)), V27; apply unsigned_lit_small; lia).
assert (U30 : bv_unsigned (ew E (A_OBJ 30)) = TA_g_cfg + 24)
  by (rewrite (EOB 30%nat ltac:(lia)), V30; apply unsigned_lit_small; lia).
pose proof (TWL.u_at_range Bx TW.A_Cfg_keepalive_ms 4) as Rk.
pose proof (TWL.u_at_range Bx TW.A_M_next_ka 8) as Rn.
pose proof (TWL.u_at_range Bx TW.OFF_g_now 8) as Rw.
change (TW.u_at Bx TW.A_Cfg_keepalive_ms 4) with (TW.Cfg_keepalive_ms Bx) in Rk.
change (TW.u_at Bx TW.A_M_next_ka 8) with (TW.M_next_ka Bx) in Rn.
change (TW.u_at Bx TW.OFF_g_now 8) with (TW.g_now Bx) in Rw.
change (8 * Z.of_nat 4) with 32 in Rk. change (8 * Z.of_nat 8) with 64 in Rn, Rw.
assert (VK : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z) by (intros z Hz; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_ka, ka_regions.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + unfold ka_cfg_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U30. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (TA_g_cfg + 24) 0 4 (SOff 32 0) (TW.Cfg_keepalive_ms Bx));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
    rewrite Z.add_0_r.
    exact (tw_read_val segs (mrestrict (w_H W) mem) TMAP_A Bx TW.OFF_g_cfg TA_g_cfg TW.SZ_g_cfg 24 4 TMAP_A_ok Htw
      TMAP_A_g_cfg ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)).
  + unfold ka_nka_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply ios_inG_M.
      unfold TW.SZ_M. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val segs E _ TA_M 48 8 (SOff 33 0) (TW.M_next_ka Bx));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
      exact (tw_read_val segs (mrestrict (w_H W) mem) TMAP_A Bx TW.OFF_M TA_M TW.SZ_M 48 8 TMAP_A_ok Htw
        TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
  + unfold ka_now_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ TA_g_now 0 8 (SOff 34 0) (TW.g_now Bx));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
    exact (tw_read_val segs (mrestrict (w_H W) mem) TMAP_A Bx TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8 TMAP_A_ok Htw
      TMAP_A_g_now ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)).
- apply pairwise_disjoint_of_extents.
  unfold ka_cfg_region, ka_nka_region, ka_now_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20, U27, U30.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold ka_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, U20, U27, U30, E32. rewrite (VK (TW.Cfg_keepalive_ms Bx)) by lia.
  change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.

Ltac ios_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

Ltac ios_awr_nil :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.

(* The windows a run wrote: the windows of the state's regions, computed, each case closed by tac. *)
Ltac ios_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The run's write right: the regions' windows are bytes of M (G); UME rewrites the base of M's atom. *)
Ltac ios_awr_M UME :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first
      [ lia
      | rewrite UME in Ha; right; left; apply ios_inG_M; unfold TW.SZ_M; lia ] |]);
  apply awr_ok_x_nil.

(* ------------------------------------------------------------------ *)
(* From one cut of the tail to the next                                *)
(* ------------------------------------------------------------------ *)

(* What a journal state says of its layout: AR, and the side-stack frames and the machine stack where the journal's
   start state has them. *)
Lemma ios_jlayout : forall G STK sp0 FP ly S (W0 : world segs) mem0 md0 own ly2 S2 (W2 : world segs) mem2 md2 k,
  ajournal_gx G 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k ->
  @AR rc segs B ly2 S2 W2 mem2 md2 /\ (forall cid pos, frame_addr ly2 cid pos = frame_addr ly cid pos) /\
  ly_stk_lo ly2 = ly_stk_lo ly /\ ly_stk_hi ly2 = ly_stk_hi ly.
Proof.
intros G STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & Hly & _).
destruct Hly as (_ & _ & _ & _ & _ & HF & _ & _ & _ & Hlo & Hhi & _).
split; [exact HAR|]. split; [intros cid pos; unfold frame_addr; rewrite HF; reflexivity|].
split; [exact Hlo | exact Hhi].
Qed.

Lemma ios_rdword_ext : forall (rd rd' : Z -> option Z) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
assert (H0 : rd' a = rd a) by (rewrite <- (Z.add_0_r a); apply H; lia).
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

(* The nine saved words, at a memory that keeps [sp - 72, sp). *)
Lemma ios_saved_kept : forall (W2 W3 : world segs) mem2 mem3 regs,
  ios_saved W2 mem2 regs ->
  (forall a, spZ regs - 72 <= a < spZ regs -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a) ->
  ios_saved W3 mem3 regs.
Proof.
intros W2 W3 mem2 mem3 regs HS HK. unfold ios_saved in *.
assert (HB : forall o, In o IOS_SAVED -> 8 <= fst o <= 72).
{ intros o Ho. unfold IOS_SAVED in Ho.
  repeat (destruct Ho as [Ho | Ho]; [subst o; cbn [fst]; lia |]). destruct Ho. }
rewrite Forall_forall in *. intros o Ho. rewrite <- (HS o Ho). apply ios_rdword_ext.
intros i Hi. pose proof (HB o Ho). apply HK. lia.
Qed.

(* The struct spec_frame at a memory that keeps its 80 bytes. *)
Lemma ios_sframe_kept : forall (W2 W3 : world segs) mem2 mem3 q fa f,
  trans_sframe_at W2 mem2 q fa f ->
  (forall a, q <= a < q + 80 -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a) ->
  trans_sframe_at W3 mem3 q fa f.
Proof.
intros W2 W3 mem2 mem3 q fa f (H0 & H8 & SB & HG & HL & HR) HK.
split; [exact H0|]. split; [exact H8|]. exists SB. split; [|split; [exact HL | exact HR]].
apply (ios_garr8_kept _ _ _ _ _ _ HG). rewrite length_map, HL. exact HK.
Qed.

(* The cut facts at a later state Y of the tail, from those at X: the journal at Y, the side-stack frames and
   blocks and the meter as at X, the running kept fact at Y, the frame's placement at Y with its bytes as at X,
   io_send's frame above sp + 8 as at X, and the world relation at Y. *)
Lemma ios_tail_core : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc k regs p frame
    lyX SX (WX : world segs) memX mdX Bx lyY SY (WY : world segs) memY mdY By,
  ameter_laws MT ->
  ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame lyX SX WX memX mdX Bx ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyY SY WY memY mdY (k + 0) ->
  frames SY = frames SX -> Permutation (ablocks B lyY SY) (ablocks B lyX SX) -> mo_le MT SX SY 0 ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc WY memY (spZ regs - IOSEND_STK) (spZ regs)
    (iosend_wr (Z.of_nat (length frame))) ->
  trans_src_ok B lyY SY WY memY p (Z.of_nat (length frame)) ->
  (forall a, p <= a < p + Z.of_nat (length frame) -> aview segs (w_H WY) memY a = aview segs (w_H WX) memX a) ->
  (forall a, spZ regs - IOSEND_FRAME + 8 <= a < spZ regs -> aview segs (w_H WY) memY a = aview segs (w_H WX) memX a) ->
  tw_at TMAP_A (aview segs (w_H WY) memY) By ->
  ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame lyY SY WY memY mdY By.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame lyX SX WX memX mdX Bx lyY SY WY memY mdY By
  MTL HT HJY HfrY HpermY HmoY RKY HSRCY KF KW HtwY.
destruct HT as ((HJX & HfrX & HpermX & HmoX & _) & HSVX & HSFX & HG8X & HSRCX & HOFF & HFAT & _).
assert (EIF : IOSEND_FRAME = 160) by reflexivity. assert (EFO : IOS_F_OFF = 8) by reflexivity.
split.
{ split; [exact HJY|]. split; [rewrite HfrY; exact HfrX|]. split; [exact (Permutation_trans HpermY HpermX)|].
  split; [exact (mle_station MT Sc SX SY 0 0 MTL HmoX HmoY) | exact RKY]. }
split; [apply (ios_saved_kept WX WY memX memY regs HSVX); intros a Ha; apply KW; lia|].
split; [apply (ios_sframe_kept WX WY memX memY _ p (TC.rf frame) HSFX); intros a Ha; apply KW; lia|].
split; [apply (ios_garr8_kept _ _ _ _ _ _ HG8X); rewrite length_map; exact KF|].
split; [exact HSRCY|]. split; [exact HOFF|]. split; [exact HFAT | exact HtwY].
Qed.

(* The cut facts at a later state Y of the tail, from those at X: the journal at Y, the side-stack frames and
   blocks and the meter as at X, the running kept fact at Y, every byte that is not an image byte kept outside the
   callees' windows below io_send's sp and outside the int at sp + 4, the bytes of g_s kept, and the world
   relation at Y. *)
Lemma ios_tail_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs p frame Bw
    lyX SX (WX : world segs) memX mdX Bx lyY SY (WY : world segs) memY mdY By,
  AR_laws segs B -> ameter_laws MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  60 <= Z.of_nat (length frame) ->
  ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame lyX SX WX memX mdX Bx ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyY SY WY memY mdY (k + 0) ->
  frames SY = frames SX -> Permutation (ablocks B lyY SY) (ablocks B lyX SX) -> mo_le MT SX SY 0 ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc WY memY (spZ regs - IOSEND_STK) (spZ regs)
    (iosend_wr (Z.of_nat (length frame))) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - IOSEND_STK <= a < spZ regs - IOSEND_FRAME) ->
     ~ (spZ regs - IOSEND_FRAME + 4 <= a < spZ regs - IOSEND_FRAME + 8) -> ~ in_img segs a ->
     aview segs (w_H WY) memY a = aview segs (w_H WX) memX a) ->
  (forall a, TA_g_s <= a < TA_g_s + TW.SZ_g_s -> aview segs (w_H WY) memY a = aview segs (w_H WX) memX a) ->
  tw_at TMAP_A (aview segs (w_H WY) memY) By ->
  ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame lyY SY WY memY mdY By.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw lyX SX WX memX mdX Bx lyY SY WY memY
  mdY By LAWS MTL HF H60 HT HJY HfrY HpermY HmoY RKY KX KG HtwY.
pose proof HT as HT0.
destruct HF as (HJc & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & Hp0 & _).
destruct HT as ((HJX & HfrX & HpermX & HmoX & _) & HSVX & HSFX & HG8X & HSRCX & HOFF & HFAT & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EIS : IOSEND_STK = 8496) by reflexivity. assert (EIF : IOSEND_FRAME = 160) by reflexivity.
assert (EFO : IOS_F_OFF = 8) by reflexivity.
assert (GHI : TG.G_HARNESS_HI = 0x5f3190) by reflexivity.
destruct (ios_jlayout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX) as (HARX & FX & LoX & HiX).
destruct (ios_jlayout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJY) as (HARY & FY & LoY & HiY).
pose proof HJc as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _). clear memS HJi.
assert (HRDX : decode_rd_ok WX memX p (Z.of_nat (length frame)))
  by exact (trans_src_ok_rd B LAWS lyX SX WX memX mdX p _ HARX HSRCX ltac:(lia)).
destruct HRDX as (_ & _ & _ & _ & Hq0 & Hq63).
(* the frame's bytes *)
assert (KF : forall a, p <= a < p + Z.of_nat (length frame) ->
  aview segs (w_H WY) memY a = aview segs (w_H WX) memX a).
{ intros a Ha. destruct HFAT as [Hout | Hgs]; [|apply KG; lia].
  assert (Hni : ~ in_img segs a).
  { intros Hi. destruct (ios_src_ok_not_ro B lyX SX WX memX p _ H60 HSRCX) as [(bA & nA & Hin & B1 & B2) | (HL & _)].
    - destruct (al_blocks _ _ LAWS lyX SX WX memX mdX bA nA HARX Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
      exact (blk_img segs B LAWS lyX SX WX memX mdX bA nA a HARX Hin ltac:(lia) Hi).
    - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | (S1 & S3)]].
      + exact (frm_img segs B LAWS lyX SX WX memX mdX cid pos a HARX Hin ltac:(lia) Hi).
      + exact (Hout a Ha (HG a Ha)).
      + pose proof (transport_segs_low a Hi) as Hl.
        destruct (trans_stk_bounds B lyX SX WX memX mdX HARX) as [T1 T2]. unfold kLowMemEnd in *. lia. }
  unfold decode_off_win in HOFF. apply KX; [lia | lia | lia | exact Hni]. }
(* the shadow bytes of the caller's side-stack frames *)
assert (KS : forall cid pos s, In (cid, pos) (frames SX) ->
   in_zr s (shadow_addr (frame_addr lyX cid pos), fs_frame_bytes cid / 8) ->
   aview segs (w_H WY) memY s = aview segs (w_H WX) memX s).
{ intros cid pos s Hin Hs'.
  destruct (frames_bounds segs B LAWS lyX SX WX memX mdX cid pos HARX Hin) as (F1 & F2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (shadow_range_end (frame_addr lyX cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr lyX cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos (frame_addr lyX cid pos) 8 ltac:(lia) ltac:(lia)).
  unfold in_zr in Hs'. cbn [fst snd] in Hs'.
  unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd.
  apply KX; [lia | lia | lia |]. intros Hi. pose proof (transport_segs_low s Hi) as Hl. unfold kLowMemEnd in Hl. lia. }
assert (FYX : forall cid pos, frame_addr lyY cid pos = frame_addr lyX cid pos) by (intros cid pos; rewrite FY, FX; reflexivity).
pose proof (trans_src_ok_kept B LAWS lyX SX WX memX mdX lyY SY WY memY mdY p _ HARX HARY HpermY HfrY FYX
  ltac:(rewrite LoY, LoX; reflexivity) ltac:(rewrite HiY, HiX; reflexivity) KF KS HSRCX ltac:(lia)) as HSRCY.
assert (KW : forall a, spZ regs - IOSEND_FRAME + 8 <= a < spZ regs ->
  aview segs (w_H WY) memY a = aview segs (w_H WX) memX a).
{ intros a Ha. apply KX; [lia | lia | lia |]. intros Hi. pose proof (transport_segs_low a Hi) as Hl.
  unfold kLowMemEnd in Hl. lia. }
exact (ios_tail_core STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame lyX SX WX memX mdX Bx lyY SY WY
  memY mdY By MTL HT0 HJY HfrY HpermY HmoY RKY HSRCY KF KW HtwY).
Qed.

(* The view of n stored bytes. *)
Lemma ios_view_val : forall (H : word -> bool) (m : word -> option byte) a (n : nat) v,
  val_mem segs (mrestrict H m) a n v ->
  forall j, (j < n)%nat -> aview segs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small.
change (le_byte v n j) with (YO0f.le_byte v n j). unfold YO0f.le_byte.
pose proof (Z.mod_pos_bound (Z.shiftr (v mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat j)) 256 ltac:(lia)).
change (2 ^ Z.of_N 8) with 256. lia.
Qed.

(* One store of m bytes of v at M + k: the world relation at TW.upd Bx (OFF_M + k) (put m v). *)
Lemma ios_tw_M1 : forall (rd0 rdF : Z -> option Z) Bx k (m : nat) v,
  tw_at TMAP_A rd0 Bx -> 0 <= k -> k + Z.of_nat m <= TW.SZ_M ->
  (forall j, (j < m)%nat -> rdF (TA_M + k + Z.of_nat j) = Some (YO0f.le_byte v m j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_M + k <= x < TA_M + k + Z.of_nat m) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.upd Bx (TW.OFF_M + k) (TW.put m v)).
Proof.
intros rd0 rdF Bx k m v H0 Hk Hkm HV HK.
pose proof (ios_tw_step rdF rd0 (fun _ => false) Bx TW.OFF_M TA_M TW.SZ_M k (TW.OFF_M + k) m v
  (ios_tw_start rdF rd0 Bx H0) TMAP_A_M eq_refl Hk Hkm HV) as H1.
apply (ios_tw_end rdF rd0 _ _ H1). intros x Hx HP. ios_unP HP. exact (HK x Hx Hq).
Qed.

(* Two stores into M: 4 bytes of v1 at M + k1, then 8 bytes of v2 at M + k2. *)
Lemma ios_tw_M2 : forall (rd0 rdF : Z -> option Z) Bx k1 v1 k2 v2,
  tw_at TMAP_A rd0 Bx -> 0 <= k1 -> k1 + 4 <= TW.SZ_M -> 0 <= k2 -> k2 + 8 <= TW.SZ_M ->
  (forall j, (j < 4)%nat -> rdF (TA_M + k1 + Z.of_nat j) = Some (YO0f.le_byte v1 4 j)) ->
  (forall j, (j < 8)%nat -> rdF (TA_M + k2 + Z.of_nat j) = Some (YO0f.le_byte v2 8 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_M + k1 <= x < TA_M + k1 + 4) -> ~ (TA_M + k2 <= x < TA_M + k2 + 8) ->
     rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.upd (TW.upd Bx (TW.OFF_M + k1) (TW.put 4 v1)) (TW.OFF_M + k2) (TW.put 8 v2)).
Proof.
intros rd0 rdF Bx k1 v1 k2 v2 H0 Hk1 Hkm1 Hk2 Hkm2 HV1 HV2 HK.
pose proof (ios_tw_step rdF rd0 (fun _ => false) Bx TW.OFF_M TA_M TW.SZ_M k1 (TW.OFF_M + k1) 4 v1
  (ios_tw_start rdF rd0 Bx H0) TMAP_A_M eq_refl Hk1 Hkm1 HV1) as H1.
pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M k2 (TW.OFF_M + k2) 8 v2 H1 TMAP_A_M eq_refl Hk2 Hkm2 HV2)
  as H2.
apply (ios_tw_end rdF rd0 _ _ H2). intros x Hx HP. ios_unP HP.
apply (HK x Hx); [cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hq0; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hq; lia].
Qed.

(* The cut facts at a later memory of the same state (ly2, S2, W2) (the leaf calls and the runs keep them): the
   memory differs from mem2 only on io_send's own frame below sp (the callees' windows) and on bytes Wr of M that
   iosend_wr allows. *)
Lemma ios_tail_same : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs p frame Bw
    ly2 S2 (W2 : world segs) mem2 md2 Bx memY mdY By (Wr : Z -> Prop),
  AR_laws segs B -> ameter_laws MT -> gx_ok segs B TG.G_HARNESS ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  60 <= Z.of_nat (length frame) ->
  ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 mem2 md2 Bx ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memY mdY (k + 0) ->
  (forall a, Wr a -> TA_M <= a < TA_M + TW.SZ_M /\ iosend_wr (Z.of_nat (length frame)) a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - IOSEND_STK <= a < spZ regs - IOSEND_FRAME) -> ~ Wr a ->
     aview segs (w_H W2) memY a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memY a) ->
  tw_at TMAP_A (aview segs (w_H W2) memY) By ->
  ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 memY mdY By.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 Bx memY mdY By Wr
  LAWS MTL HGX HF H60 HT HJY HWr KY GY HtwY.
pose proof HF as HF0. pose proof HT as HT0.
destruct HF as (HJc & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & Hp0 & _).
destruct HT as ((HJX & HfrX & HpermX & HmoX & HKX) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EIS : IOSEND_STK = 8496) by reflexivity. assert (EIF : IOSEND_FRAME = 160) by reflexivity.
assert (EM : TA_M = 0x5df160) by reflexivity. assert (EGS : TA_g_s = 0x5df9c0) by reflexivity.
assert (SM : TW.SZ_M = 1648) by reflexivity.
assert (GHI : TG.G_HARNESS_HI = 0x5f3190) by reflexivity.
destruct (ios_jlayout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (HARc & _ & _ & _).
pose proof HJc as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _). clear memS HJi.
apply (ios_tail_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 Bx
  ly2 S2 W2 memY mdY By LAWS MTL HF0 H60 HT0 HJY eq_refl (Permutation_refl _) (mle_start MT S2 MTL)).
- apply (ios_kept_win lyc Sc W memc mdc W memc W2 mem2 memY (spZ regs) (Z.of_nat (length frame)) LAWS HGX HARc
    ltac:(lia) ltac:(lia) HKX).
  + intros a Ha H1 H2. apply KY; [exact Ha | lia |]. intros HW. exact (H2 (proj2 (HWr a HW))).
  + exact GY.
- intros a Ha H1 H2 H3. apply KY; [exact Ha | lia |]. intros HW.
  exact (H3 (proj1 (HGX a (ios_wr_inG _ a (proj2 (HWr a HW)))))).
- intros a Ha. apply KY; [unfold TW.SZ_g_s in Ha; lia | unfold TW.SZ_g_s in Ha; lia |].
  intros HW. destruct (HWr a HW) as [H1 _]. unfold TW.SZ_g_s in Ha. lia.
- exact HtwY.
Qed.

(* The end of the keepalive case: one 8-byte store of v at M + 48 (M.next_ka) after check_keepalive_due, whose
   window mem3 differs from mem2 on; the state at IOS_FLY with the world TW.set_M_next_ka B5 v. *)
Lemma ios_ka_fin : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs p frame Bw
    ly2 S2 (W2 : world segs) mem2 md2 B5 mem3 memF mdF (regs2 regsF : bvmap 5 word) v
    (Q : world segs -> config -> Prop),
  AR_laws segs B -> ameter_laws MT -> gx_ok segs B TG.G_HARNESS ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  60 <= Z.of_nat (length frame) ->
  ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 mem2 md2 B5 ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memF mdF (k + 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - IOSEND_FRAME - ESTACK <= a < spZ regs - IOSEND_FRAME) ->
     aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 48 <= a < TA_M + 56) ->
     aview segs (w_H W2) memF a = aview segs (w_H W2) mem3 a) ->
  (forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) memF a) ->
  val_mem segs (mrestrict (w_H W2) memF) (TA_M + 48) 8 v ->
  aregs_preserved regs2 regsF ->
  (forall ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word),
     ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly3 S3 W3 mem3 md3
       (TW.set_M_next_ka B5 v) ->
     aregs_preserved regs2 regs3 ->
     SRr segs W3 (@cfg_at fx segs (transport_text + IOS_FLY) regs3 mem3 md3) Q) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_FLY) regsF memF mdF) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 B5 mem3 memF mdF
  regs2 regsF v Q LAWS MTL HGX HF H60 HT HJF K3 G3 KF GF VF HPF HK.
pose proof HF as (HJc & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & _).
pose proof HT as (_ & _ & _ & _ & _ & _ & _ & Htw2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EIS : IOSEND_STK = 8496) by reflexivity. assert (EIF : IOSEND_FRAME = 160) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (EM : TA_M = 0x5df160) by reflexivity. assert (SM : TW.SZ_M = 1648) by reflexivity.
assert (GHI : TG.G_HARNESS_HI = 0x5f3190) by reflexivity. assert (GLO : TG.G_HARNESS_LO = 0x5df080) by reflexivity.
pose proof HJc as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _). clear memS HJi.
assert (Htw3 : tw_at TMAP_A (aview segs (w_H W2) mem3) B5).
{ apply (tw_kept TMAP_A _ _ B5 Htw2). intros x Hx. pose proof (TMAP_A_hull x Hx). apply K3; lia. }
apply (HK ly2 S2 W2 memF mdF regsF); [|exact HPF].
apply (ios_tail_same STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 B5
  memF mdF _ (fun a => TA_M + 48 <= a < TA_M + 56) LAWS MTL HGX HF H60 HT HJF).
- intros a Ha. cbv beta in Ha. split; [lia | apply ios_wr_nextka; lia].
- intros a Ha H1 H2. rewrite (KF a Ha H2). apply K3; [exact Ha | lia].
- intros a Ha. exact (GF a (G3 a Ha)).
- unfold TW.set_M_next_ka, TW.A_M_next_ka.
  apply (ios_tw_M1 (aview segs (w_H W2) mem3) _ B5 48 8 v Htw3); [lia | lia | |].
  + intros j Hj. exact (ios_view_val _ _ _ 8 v VF j Hj).
  + intros x Hx Hn. pose proof (TMAP_A_hull x Hx). apply KF; [lia | cbn [Z.of_nat Pos.of_succ_nat] in Hn; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* The keepalive case, 0x832cc .. 0x83300                               *)
(* ------------------------------------------------------------------ *)

Lemma ios_tail_ka : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) p frame Bw ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) B5 B6
    (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 mem2 md2 B5 ->
  60 <= Z.of_nat (length frame) ->
  YK11.getr regs2 2 = w64 (spZ regs - IOSEND_FRAME) ->
  YK11.getr regs2 3 = w64 (as_gp B) -> YK11.getr regs2 4 = w64 (as_tp B) ->
  YK11.getr regs2 20 = w64 TA_M ->
  ios_B6 frame B5 = Some (B6, tt) -> TC.truth (TW.g_raw B5) = false -> ios_ka frame = true ->
  (forall ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word),
     ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly3 S3 W3 mem3 md3 B6 ->
     aregs_preserved regs2 regs3 ->
     SRr segs W3 (@cfg_at fx segs (transport_text + IOS_FLY) regs3 mem3 md3) Q) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_KA) regs2 mem2 md2) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 B5 B6 Q
  HL HF HT H60 R2 R3 R4 R20 HB6 Hraw Hka HK.
pose proof HF as HF0. pose proof HT as HT0.
destruct HL as (HCELLS & HIOC & LAWS & MTL & HGX & HGE & HMS & HCSF & HCAF & HCLC & HCIR & HCSW & HCIN & HCLF & HCKD
  & HCLS & HCLD & HMC).
destruct HF as (HJc & Hra & Hra4 & Hgp & Htp & H11 & H12 & Hsp16 & Hlo & Hhi & Hp0 & HG8c & HSRCc & HOFFc & HFATc
  & Hfail & HROM & Htwc & Hfly & Hcmd & Hev).
destruct HT as (HC2 & HSV2 & HSF2 & HG82 & HSRC2 & HOFF & HFAT & Htw2).
pose proof HC2 as (HJ2 & Hfr2 & Hperm2 & Hmo2 & HK2).
destruct (ios_B6_ka frame B5 B6 HB6 Hraw Hka) as [Hckd HB6'].
pose proof HJc as (HSTK & _ & (memSc & HJic & _) & _). rewrite !Z.add_0_r in HJic.
pose proof HJic as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). rewrite !Z.add_0_r in HJi2.
pose proof HJi2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
clear memSc HJic memS2 HJi2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EIS : IOSEND_STK = 8496) by reflexivity. assert (EIF : IOSEND_FRAME = 160) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (EM : TA_M = 0x5df160) by reflexivity.
assert (GHI : TG.G_HARNESS_HI = 0x5f3190) by reflexivity. assert (GLO : TG.G_HARNESS_LO = 0x5df080) by reflexivity.
assert (Hsp2 : spZ regs2 = spZ regs - IOSEND_FRAME).
{ unfold spZ at 1. rewrite R2. apply unsigned_lit_small. lia. }
(* run 1, +0x56c: `jal check_keepalive_due` *)
set (E0 := ios_E0 regs2).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ios_E0; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0, ios_E0; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (ios_e0_entry W2 regs2 mem2 IOS_KA) as HS. fold E0 in HS.
assert (SHOK : sh_ok segs IOS_Bx [] E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof HJ2 as HJ.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + IOS_KA)) mem2 (YK11.seg_rom segs)) md2) Qx) end.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ios_awr_nil. }
set (mdC := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdC. clear mat.
assert (KC : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx. exfalso. vm_compute in Hin. exact Hin. }
assert (GC : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
pmkst HS.
ios_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + IOS_KA_RET)) Q1 ltac:(apply codeptr_val; exact HEI).
ios_reg HS (2%bv : bv 5) (YK11.getr regs2 2) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ios_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R3).
ios_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R4).
assert (HPC : aregs_preserved regs2 (ms_regs ms)).
{ apply (aregs_preserved_of_st_ok segs (w_H W2) E0 _ ms regs2 [] HS).
  - exact (ios_e0_agree regs2).
  - vm_compute. reflexivity. }
assert (Hspc : spZ (ms_regs ms) = spZ regs - IOSEND_FRAME) by (unfold spZ at 1; rewrite Q2; exact Hsp2).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS_check_keepalive_due)) mm rom) mdx) Qx) end.
apply (ios_leaf_call W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own ly2 S2 mdC (k + 0)
  (spZ regs - IOSEND_FRAME - sp0) (transport_sigma TS_check_keepalive_due) (fun _ => B5 = B5) Q LAWS HJ).
- lia.
- replace (spZ regs - IOSEND_FRAME - sp0) with (spZ regs - sp0 + (-10) * 16) by (rewrite EIF; lia).
  rewrite Z_mod_plus_full, Zminus_mod, Hsp16, Hsp0a. reflexivity.
- lia.
- lia.
- rewrite Q1. apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold IOS_KA_RET, IOS_AT, AF_io_send; lia | reflexivity].
- exact Q3.
- exact Q4.
- intros HPRE. apply (ios_ckd_leaf W2 (ms_regs ms) (ms_mem ms) mdC ly2 S2 B5 HCKD); [| exact Hckd | lia | lia | exact HPRE].
  apply (tw_kept TMAP_A _ _ B5 Htw2). intros x Hx. apply KC. pose proof (TMAP_A_hull x Hx). lia.
- intros regs3 mem3 md3 HJ3 HP3 HK3 HG3 _.
  rewrite Q1.
  assert (HP23 : aregs_preserved regs2 regs3) by exact (aregs_preserved_trans _ _ _ HPC HP3).
  assert (R20' : YK11.getr regs3 20 = w64 TA_M)
    by (rewrite <- R20; exact (HP23 20 ltac:(unfold acallee_saved; lia))).
  assert (R2' : YK11.getr regs3 2 = YK11.getr regs2 2) by exact (HP23 2 ltac:(unfold acallee_saved; lia)).
  assert (Hsp3 : spZ regs3 = spZ regs - IOSEND_FRAME) by (unfold spZ at 1; rewrite R2'; exact Hsp2).
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - IOSEND_FRAME - ESTACK <= a < spZ regs - IOSEND_FRAME) ->
    aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hn. rewrite (HK3 a Ha ltac:(rewrite Hspc; exact Hn)). exact (KC a Ha). }
  assert (G3 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) by (intros a Ha; exact (HG3 a (GC a Ha))).
  assert (Htw3 : tw_at TMAP_A (aview segs (w_H W2) mem3) B5).
  { apply (tw_kept TMAP_A _ _ B5 Htw2). intros x Hx. pose proof (TMAP_A_hull x Hx). apply K3; lia. }
  clear HS SHOK HJ.
  (* run 2, +0x570 .. +0x594: a1 = keepalive_ms * 1000, a2 = M.next_ka + a1 stored at M + 48, a0 = g_now, `bltu` *)
  set (E1 := ios_ka_E regs3 (TW.Cfg_keepalive_ms B5) (TW.M_next_ka B5) (TW.g_now B5)).
  assert (HEI1 : img_env VAL A_LIM E1) by (unfold E1, ios_ka_E; apply Eimg_env).
  assert (Hm16 : spZ regs3 mod 16 = 0).
  { rewrite Hsp3, EIF. replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hsp16. }
  pose proof (ios_ka_entry W2 regs3 mem3 B5 Htw3 R20' ltac:(rewrite Hsp3; lia) Hm16) as HS. fold E1 in HS.
  assert (SHOK : sh_ok segs IOS_Bx [] E1 (mrestrict (w_H W2) mem3)) by constructor.
  rename HJ3 into HJ.
  assert (U20 : bv_unsigned (ew E1 20) = TA_M).
  { unfold E1, ios_ka_E. rewrite (ew_Eimg_Ereg_nat regs3 _ 20 20%bv eq_refl), R20'. apply unsigned_lit_small. lia. }
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ios_awr_M U20. }
  set (mdK := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdK. clear mat.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msK end.
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 48 <= a < TA_M + 56) ->
    aview segs (w_H W2) (ms_mem msK) a = aview segs (w_H W2) mem3 a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => TA_M + 48 <= x < TA_M + 56) HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. ios_win Hin Hx ltac:(rewrite ?U20 in Hx; lia). }
  assert (GR2 : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem msK) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  (* the values the run computed *)
  assert (HLB : length B5 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw2).
  pose proof (TWL.u_at_range B5 TW.A_Cfg_keepalive_ms 4) as Rk.
  change (TW.u_at B5 TW.A_Cfg_keepalive_ms 4) with (TW.Cfg_keepalive_ms B5) in Rk. change (8 * Z.of_nat 4) with 32 in Rk.
  pose proof (TWL.u_at_range B5 TW.A_M_next_ka 8) as Rn.
  change (TW.u_at B5 TW.A_M_next_ka 8) with (TW.M_next_ka B5) in Rn. change (8 * Z.of_nat 8) with 64 in Rn.
  pose proof (TWL.u_at_range B5 TW.OFF_g_now 8) as Rw.
  change (TW.u_at B5 TW.OFF_g_now 8) with (TW.g_now B5) in Rw. change (8 * Z.of_nat 8) with 64 in Rw.
  assert (E32 : ew E1 32 = Z_to_bv 64 (TW.Cfg_keepalive_ms B5))
    by (unfold E1, ios_ka_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E1 33 = Z_to_bv 64 (TW.M_next_ka B5))
    by (unfold E1, ios_ka_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
  assert (E34 : ew E1 34 = Z_to_bv 64 (TW.g_now B5))
    by (unfold E1, ios_ka_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
  assert (Uk : U E1 (SOff 32 0) = TW.Cfg_keepalive_ms B5) by (apply U_atom; [exact E32 | lia]).
  assert (Un : U E1 (SOff 33 0) = TW.M_next_ka B5) by (apply U_atom; [exact E33 | lia]).
  assert (Uw : U E1 (SOff 34 0) = TW.g_now B5) by (apply U_atom; [exact E34 | lia]).
  assert (Um : U E1 (SMd M_MUL (SOff 32 0) (SLit 1000)) = TW.Cfg_keepalive_ms B5 * 1000).
  { rewrite U_SMd, Uk, U_SLit. rewrite (zcanon_id 1000) by (unfold M64; lia). cbn [zmd_raw].
    apply zcanon_id. unfold M64. lia. }
  set (nk := TS0.u64 (TW.M_next_ka B5 + TC.h_ms_m (TW.Cfg_keepalive_ms B5))) in *.
  assert (Ua : U E1 (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit 1000)) (SOff 33 0)) = nk).
  { rewrite U_SAlu, Um, Un. cbn [zalu_raw]. unfold nk, zcanon, M64, TS0.u64. rewrite ios_hms. f_equal. lia. }
  assert (Ua2 : U E1 (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit 1000)) (SOff 34 0)) =
                TS0.u64 (TW.g_now B5 + TC.h_ms_m (TW.Cfg_keepalive_ms B5))).
  { rewrite U_SAlu, Um, Uw. cbn [zalu_raw]. unfold zcanon, M64, TS0.u64. rewrite ios_hms. f_equal. lia. }
  cbv zeta in HB6'. rewrite (ios_now_nka B5 nk HLB), (ios_cfg_nka B5 nk HLB), (ios_nka_nka B5 nk _ HLB) in HB6'.
  assert (Rnk : 0 <= nk < 2 ^ 64) by (unfold nk, TS0.u64; apply Z.mod_pos_bound; lia).
  assert (Rg2 : 0 <= TS0.u64 (TW.g_now B5 + TC.h_ms_m (TW.Cfg_keepalive_ms B5)) < 2 ^ 64)
    by (unfold TS0.u64; apply Z.mod_pos_bound; lia).
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* g_now < next_ka + a1: next_ka stays (:871) *)
    rewrite branch_ltu_U, Uw, Ua in Hc. apply Z.ltb_lt in Hc.
    destruct HB6' as [[Hle _] | [_ EB6]]; [apply Z.leb_le in Hle; lia |]. subst B6.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_FLY.
    { ios_awr_M U20. }
    set (mdF := with_vm_backing (m_vm_lazy mdK) mat mdK) in *. clearbody mdF. clear mat.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
    assert (KRF : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 48 <= a < TA_M + 56) ->
      aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem3 a).
    { intros a Ha Hn. rewrite <- (KR2 a Ha Hn).
      apply (kept_of_frame _ _ _ _ _ (fun x => TA_M + 48 <= x < TA_M + 56) HFr); [| exact Ha | exact Hn].
      intros b wlo whi x Hin Hx. ios_win Hin Hx ltac:(rewrite ?U20 in Hx; lia). }
    assert (GRF : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem msF) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GR2 a Ha))).
    clear HF HFr HG.
    pose proof (st_ok_pi_region_nth E1 _ (restrict (w_H W2) msF) 1 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
    destruct RG as (_ & _ & _ & HCH). apply Forall_inv in HCH.
    pose proof (val_of_chunk_any segs E1 _ _ _ _ _ HCH ltac:(lia)) as VS.
    cbn [YP09.r_base base_val] in VS. rewrite U20 in VS.
    pose proof Ua as Ua'. unfold U in Ua'. rewrite Ua' in VS.
    change (N.to_nat 8) with 8%nat in VS. change (8 * Z.of_N 8) with 64 in VS.
    rewrite (Z.mod_small nk) in VS by lia.
    assert (HPF : aregs_preserved regs3 (ms_regs msF)).
    { apply (aregs_preserved_of_st_ok segs (w_H W2) E1 _ msF regs3
        [Z_to_bv 64 (TW.Cfg_keepalive_ms B5); Z_to_bv 64 (TW.M_next_ka B5); Z_to_bv 64 (TW.g_now B5)] HS).
      - apply ios_ka_agree.
      - vm_compute. reflexivity. }
    pmkst HS.
    change (SRr segs W2 (@cfg_at fx segs (transport_text + IOS_FLY) (ms_regs msF) (ms_mem msF) mdF) Q).
    exact (ios_ka_fin STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 B5 mem3
      (ms_mem msF) mdF regs2 (ms_regs msF) nk Q LAWS MTL HGX HF0 H60 HT0 HJ K3 G3 KRF GRF VS
      (aregs_preserved_trans _ _ _ HP23 HPF) HK).
  + (* next_ka + a1 <= g_now: next_ka = g_now + a1 (:872) *)
    rewrite branch_ltu_U, Uw, Ua in Hc. apply Z.ltb_ge in Hc.
    destruct HB6' as [[_ EB6] | [Hle _]]; [| apply Z.leb_gt in Hle; lia]. subst B6.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_FLY.
    { ios_awr_M U20. }
    set (mdF := with_vm_backing (m_vm_lazy mdK) mat mdK) in *. clearbody mdF. clear mat.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
    assert (KRF : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 48 <= a < TA_M + 56) ->
      aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem3 a).
    { intros a Ha Hn. rewrite <- (KR2 a Ha Hn).
      apply (kept_of_frame _ _ _ _ _ (fun x => TA_M + 48 <= x < TA_M + 56) HFr); [| exact Ha | exact Hn].
      intros b wlo whi x Hin Hx. ios_win Hin Hx ltac:(rewrite ?U20 in Hx; lia). }
    assert (GRF : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem msF) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GR2 a Ha))).
    clear HF HFr HG.
    pose proof (st_ok_pi_region_nth E1 _ (restrict (w_H W2) msF) 1 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
    destruct RG as (_ & _ & _ & HCH). apply Forall_inv in HCH.
    pose proof (val_of_chunk_any segs E1 _ _ _ _ _ HCH ltac:(lia)) as VS.
    cbn [YP09.r_base base_val] in VS. rewrite U20 in VS.
    pose proof Ua2 as Ua'. unfold U in Ua'. rewrite Ua' in VS.
    change (N.to_nat 8) with 8%nat in VS. change (8 * Z.of_N 8) with 64 in VS.
    rewrite Z.mod_small in VS by lia.
    assert (HPF : aregs_preserved regs3 (ms_regs msF)).
    { apply (aregs_preserved_of_st_ok segs (w_H W2) E1 _ msF regs3
        [Z_to_bv 64 (TW.Cfg_keepalive_ms B5); Z_to_bv 64 (TW.M_next_ka B5); Z_to_bv 64 (TW.g_now B5)] HS).
      - apply ios_ka_agree.
      - vm_compute. reflexivity. }
    pmkst HS.
    change (SRr segs W2 (@cfg_at fx segs (transport_text + IOS_FLY) (ms_regs msF) (ms_mem msF) mdF) Q).
    exact (ios_ka_fin STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 B5 mem3
      (ms_mem msF) mdF regs2 (ms_regs msF) _ Q LAWS MTL HGX HF0 H60 HT0 HJ K3 G3 KRF GRF VS
      (aregs_preserved_trans _ _ _ HP23 HPF) HK).
Qed.
(* ------------------------------------------------------------------ *)
(* The call of check_latest_sent                                       *)
(* ------------------------------------------------------------------ *)

Lemma ios_inG1 : forall q n a, inG [(q, n)] a <-> q <= a < q + n.
Proof. intros q n a. unfold inG. rewrite Exists_cons, Exists_nil. unfold in_zr. cbn [fst snd]. tauto. Qed.

(* g_s at two memories whose worlds agree below g_cmd. *)
Lemma ios_gs_kept : forall (rdA rdB : Z -> option Z) BA BB,
  tw_at TMAP_A rdA BA -> tw_at TMAP_A rdB BB ->
  (forall i, 0 <= i < TW.OFF_g_cmd -> nth (Z.to_nat i) BB (Z_to_bv 8 0) = nth (Z.to_nat i) BA (Z_to_bv 8 0)) ->
  forall a, TA_g_s <= a < TA_g_s + TW.SZ_g_s -> rdB a = rdA a.
Proof.
intros rdA rdB BA BB [_ HA] [_ HB] HN a Ha.
replace a with (TA_g_s + (a - TA_g_s)) by lia.
rewrite (HB _ _ _ (a - TA_g_s) TMAP_A_g_s ltac:(lia)), (HA _ _ _ (a - TA_g_s) TMAP_A_g_s ltac:(lia)).
rewrite (HN (TW.OFF_g_s + (a - TA_g_s))) by (unfold TA_g_s, TW.OFF_g_s, TW.OFF_g_cmd, TW.SZ_g_s in *; lia).
reflexivity.
Qed.

(* check_latest_sent's written bytes: bytes of iosend_wr (g_cmd's st fields, g_q, g_nq) or the int at dp. *)
Lemma ios_cls_wr_iosend : forall n dp a, cls_wr dp a -> iosend_wr n a \/ dp <= a < dp + 4.
Proof.
intros n dp a [H | [H | [H | H]]]; [left | left | left | right; exact H]; unfold iosend_wr; do 16 right;
  [left; exact H | right; left; exact H | right; right; exact H].
Qed.

(* The frame holds no byte check_latest_sent writes: it is outside G or inside g_s, and outside io_send's window. *)
Lemma ios_frame_not_cls : forall (regs : bvmap 5 word) p n dp a,
  iosend_frame_at p n -> decode_off_win regs IOSEND_STK p n ->
  spZ regs - IOSEND_STK <= dp -> dp + 4 <= spZ regs ->
  p <= a < p + n -> ~ cls_wr dp a.
Proof.
intros regs p n dp a HFAT HOFF H1 H2 Ha Hc. unfold decode_off_win in HOFF.
destruct HFAT as [Hout | Hgs].
- destruct (ios_cls_wr_iosend n dp a Hc) as [Hw | Hd]; [exact (Hout a Ha (ios_wr_inG n a Hw)) | lia].
- unfold TA_g_s, TW.SZ_g_s in Hgs.
  destruct Hc as [(s & Hs & Hf) | [Hf | [Hf | Hd]]];
    [| | | lia]; unfold twa_fld, TW.A_Cmd_st, TW.OFF_g_cmd, TW.OFF_g_q, TW.OFF_g_nq, TW.SZ_g_q, TW.SZ_g_nq,
    TA_g_cmd, TA_g_q, TA_g_nq in Hf; lia.
Qed.

(* A sub-range of a source range, the empty range included. *)
Lemma ios_src_sub0 : forall lyc Sc (W : world segs) memc q n q' n',
  trans_src_ok B lyc Sc W memc q n -> q <= q' -> 0 <= n' -> q' + n' <= q + n ->
  trans_src_ok B lyc Sc W memc q' n'.
Proof.
intros lyc Sc W memc q n q' n' Hs H1 Hn H2.
destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
- left. exists bA, nA. split; [exact Hin | lia].
- right. split; [|exact (trans_rd_ok_sub W memc q n q' n' Hrd H1 H2 Hn)].
  destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & Hsh) | [(S1 & S2) | (HR & Hsh)]]].
  + left. exists cid, pos. split; [exact Hin | lia].
  + right. left. split; [intros a Ha; apply HG; lia | exact (trans_sh_any_sub B q n q' n' Hsh H1 H2)].
  + right. right. left. lia.
  + right. right. right. split; [intros a Ha; apply HR; lia | exact (trans_sh_any_sub B q n q' n' Hsh H1 H2)].
Qed.

(* A callee's kept fact at the call state (ly2, S2) is one at the walk's entry (lyc, Sc) when the two have the same
   blocks, frames and frame addresses. *)
Lemma ios_kept_relay : forall G ly2 S2 lyc Sc (W1 : world segs) memX (W3 : world segs) mem3 slo shi (E : Z -> Prop),
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  acall_kept_g segs B G ly2 S2 W1 memX W3 mem3 slo shi E -> acall_kept_g segs B G lyc Sc W1 memX W3 mem3 slo shi E.
Proof.
intros G ly2 S2 lyc Sc W1 memX W3 mem3 slo shi E HP HF HA (K1 & K2 & K3 & K4 & K5 & K6).
split; [exact K1|]. split.
{ intros b m i Hb. apply K2. exact (Permutation_in _ (Permutation_sym HP) Hb). }
split; [exact K3|]. split.
{ intros cid pos a Hin Hr. apply (K4 cid pos a); [rewrite HF; exact Hin |].
  unfold frame_rng in *. cbn [fst snd] in *. rewrite !HA. exact Hr. }
split; [exact K5 | exact K6].
Qed.

(* A visible garr8 range. *)
Lemma ios_garr8_vis : forall (H : word -> bool) (m : word -> option byte) q l,
  garr8 segs (mrestrict H m) q l -> forall a, q <= a < q + Z.of_nat (length l) -> aview segs H m a <> None.
Proof.
intros H m q l HG a Ha. assert (Hj : (Z.to_nat (a - q) < length l)%nat) by lia.
destruct (HG _ Hj) as [HV _]. specialize (HV 0%nat ltac:(lia)).
replace a with (q + Z.of_nat (Z.to_nat (a - q)) + Z.of_nat 0) by lia.
unfold aview. rewrite HV. discriminate.
Qed.

(* The frame across check_latest_sent: io_send_seg_src.v ios_src_ok_acall_g with the callee's kept fact at the
   memory with the out cells put back (gover), and the frame inside g_s (the callee writes G) kept by the world
   relation. *)
Lemma ios_src_cls : forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi
    (E : Z -> Prop) outs q n,
  AR_laws segs B ->
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (gover outs mem2 memc) slo shi E ->
  (forall a, inG outs a -> alloc_ceiling <= a) ->
  (forall a, q <= a < q + n -> ~ inG outs a) ->
  (forall a, TA_g_s <= a < TA_g_s + TW.SZ_g_s -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, q <= a < q + n -> ~ E a) -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
  (q + n <= slo \/ shi <= q) -> iosend_frame_at q n ->
  trans_src_ok B lyc Sc W memc q n -> 60 <= n ->
  trans_src_ok B ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
intros lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E outs q n LAWS HAR HAR2 Hperm Hfr Hfa Elo Ehi HK Hout Hqo KG
  HnE HnEs Hoff HFAT Hs Hn.
pose proof HK as (K1 & K2 & K3 & K4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (GV : forall a, 0 <= a < alloc_ceiling ->
  aview segs (w_H W2) (gover outs mem2 memc) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. apply gover_out_aview; [lia|]. intros Hi. pose proof (Hout a Hi). lia. }
assert (KS : forall cid pos s, In (cid, pos) (frames Sc) ->
   in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
   aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
{ intros cid pos s Hin Hs'.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
  pose proof Hs' as Hs2. unfold in_zr in Hs2. cbn [fst snd] in Hs2.
  unfold shadow_addr, SHADOW_OFF in Hs2, Hse. change (2 ^ 47 / 8) with (2 ^ 44) in Hd.
  rewrite <- (GV s ltac:(lia)). apply (K4 cid pos s Hin (or_intror Hs')). apply HnEs.
  unfold kLowMemEnd, kHighShadowEnd. lia. }
assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a Ha. destruct (ios_src_ok_not_ro B lyc Sc W memc q n Hn Hs) as [(bA & nA & Hin & B1 & B2) | (HL & _)].
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & H4096 & Hbc & _ & _ & _ & Hn0).
    pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
    rewrite <- (GV a ltac:(lia)).
    replace a with (bA + (a - bA)) by lia.
    apply (K2 bA nA (a - bA) Hin ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
  - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | (S1 & S3)]].
    + destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (FB1 & FB2 & _).
      pose proof (fs_frame_bytes_nonneg cid).
      rewrite <- (GV a ltac:(lia)).
      apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
    + destruct HFAT as [Hno | Hgs]; [exfalso; exact (Hno a Ha (HG a Ha)) | apply KG; lia].
    + destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [T1 T2].
      rewrite <- (gover_out_aview segs outs (w_H W2) mem2 memc a ltac:(lia) (Hqo a Ha)). apply K1; lia. }
split; [|exact KV].
exact (trans_src_ok_kept B LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 q n HAR HAR2 Hperm Hfr Hfa Elo Ehi KV KS Hs
  ltac:(lia)).
Qed.
(* The call of check_latest_sent at 0x83314 (a0 = f.body = p + 30, a1 = f.body_len, a2 = sp + 4): its contract
   (check_latest_sent_cg.v) at the call state, its post folded into io_send's running kept fact
   (dk_kept_trans_out_g: the int at sp + 4 lies in io_send's own window), and the cut facts again at the state it
   returns, with the world check_latest_sent_m gives and the int at sp + 4 holding disp. *)
Lemma ios_cls_at : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs p frame Bw
    ly2 S2 (W2 : world segs) memT mdT B5 (regsT : bvmap 5 word) Bs disp (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  DSpec.sf_code (TC.rf frame) = DSpec.SPEC_OK -> 60 <= Z.of_nat (length frame) ->
  ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 memT mdT B5 ->
  YK0s.ret_ok (YK11.getr regsT 1) -> 4096 <= raZ regsT ->
  YK11.getr regsT 2 = w64 (spZ regs - IOSEND_FRAME) ->
  YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 10 = w64 (p + 30) -> YK11.getr regsT 11 = w64 (ios_blen frame) ->
  YK11.getr regsT 12 = w64 (spZ regs - IOSEND_FRAME + IOS_DISP_OFF) ->
  TC.check_latest_sent_m B5 (firstn (Z.to_nat (ios_blen frame)) (ios_body frame)) (ios_blen frame) =
    Some (Bs, disp) ->
  (forall s, 0 <= s < TW.g_ncmd B5 -> TW.Cmd_st B5 s = TC.PENDING -> TW.Cmd_len B5 s <= DSpec.SPEC_CMD_MAX) ->
  (forall ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word),
     ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly3 S3 W3 mem3 md3 Bs ->
     aregs_preserved regsT regs3 ->
     garr8 segs (mrestrict (w_H W3) mem3) (spZ regs - IOSEND_FRAME + IOS_DISP_OFF) (TW.zs (TW.put 4 disp)) ->
     SRr segs W3 (mkCfg (YK11.mkst regs3 (YK11.getr regsT 1) mem3 (YK11.seg_rom segs)) md3) Q) ->
  SRr segs W2 (@cfg_at fx segs (transport_sigma TS_check_latest_sent) regsT memT mdT) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 memT mdT B5 regsT Bs disp Q
  HL HF HOK H60 HT Hra Hra4 R2 R3 R4 R10 R11 R12 Hm Hcmd HK.
destruct HL as (HCELLS & HIOC & LAWS & MTL & HGX & HGE & HMS & HCSF & HCAF & HCLC & HCIR & HCSW & HCIN & HCLF & HCKD
  & HCLS & HCLD & HMC).
pose proof HF as HF0. pose proof HT as HT0.
destruct HF as (HJc & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & Hp0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev).
destruct HT as ((HJ2 & Hfr2 & Hperm2 & Hmo2 & HK2) & HSV2 & HSF2 & HG82 & HSRC2 & HOFF & HFAT & Htw2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EIS : IOSEND_STK = 8496) by reflexivity. assert (EIF : IOSEND_FRAME = 160) by reflexivity.
assert (ECS : CLS_STK = 8336) by reflexivity. assert (EST : ESTACK = 4096) by reflexivity.
assert (EDO : IOS_DISP_OFF = 4) by reflexivity.
assert (GHI : TG.G_HARNESS_HI = 0x5f3190) by reflexivity. assert (GLO : TG.G_HARNESS_LO = 0x5df080) by reflexivity.
destruct (ios_jlayout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (HARc & FAc & Loc & Hic).
destruct (ios_jlayout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (HAR2 & FA2 & Lo2 & Hi2).
pose proof HJc as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _). clear memS HJi.
destruct (ios_body_len frame HOK) as (EB & LB & Hb0 & Hb1).
assert (HspT : spZ regsT = spZ regs - IOSEND_FRAME).
{ unfold spZ at 1. rewrite R2. apply unsigned_lit_small. lia. }
assert (E16 := Z.div_mod (spZ regs) 16 ltac:(lia)). rewrite Hsp16 in E16.
assert (Hlenb : Z.of_nat (length (firstn (Z.to_nat (ios_blen frame)) (ios_body frame))) = ios_blen frame)
  by (rewrite length_firstn; lia).
assert (HG8T : garr8 segs (mrestrict (w_H W2) memT) (p + 30)
  (TW.zs (firstn (Z.to_nat (ios_blen frame)) (ios_body frame)))).
{ rewrite EB. apply (ios_garr8_body (mrestrict (w_H W2) memT) p frame (Z.to_nat (ios_blen frame)) HG82). lia. }
assert (TWR : transport_twr_ok_g segs B TG.G_HARNESS STK sp0 FP ly S ly2 S2 own W2 memT (spZ regsT)
  (spZ regs - IOSEND_FRAME + IOS_DISP_OFF) 4).
{ apply (transport_twr_ok_g_intro segs B LAWS TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT (k + 0)
    (spZ regsT) (spZ regs - IOSEND_FRAME + IOS_DISP_OFF) 4 HJ2).
  intros a Ha. left. split; [unfold awr_byte; left; lia | rewrite HspT; lia]. }
assert (RD : decode_rd_ok W2 memT (spZ regs - IOSEND_FRAME + IOS_DISP_OFF) 4).
{ split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. destruct (TWR a Ha) as [(_ & Hp & _) | Hg];
      [exact (aview_some_of_apresent _ _ _ a Hp) | exfalso; pose proof (ios_inG_low a Hg); lia].
  - apply (can_stack_addressable segs B ly2 S2 W2 memT mdT _ 4 HAR2); lia.
  - apply (can_stack_hull segs B ly2 S2 W2 memT mdT _ 4 HAR2); lia.
  - unfold amem_range. right. lia.
  - lia.
  - lia. }
eapply SRr_bind.
{ apply (HCLS fx STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT (k + 0) regsT (p + 30) (ios_blen frame)
    (spZ regs - IOSEND_FRAME + IOS_DISP_OFF) disp (firstn (Z.to_nat (ios_blen frame)) (ios_body frame)) B5 Bs
    HJ2 Hra Hra4 R3 R4 R10 R11 R12).
  - rewrite HspT, EIF. replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hsp16.
  - rewrite HspT. lia.
  - rewrite HspT. lia.
  - lia.
  - exact Hlenb.
  - exact HG8T.
  - apply (ios_src_sub0 ly2 S2 W2 memT p (Z.of_nat (length frame)) (p + 30) (ios_blen frame) HSRC2); lia.
  - unfold decode_off_win in *. rewrite HspT. lia.
  - intros x Hx. apply (ios_frame_not_cls regs p (Z.of_nat (length frame)) _ x HFAT HOFF); lia.
  - replace (spZ regs - IOSEND_FRAME + IOS_DISP_OFF) with ((4 * (spZ regs / 16) - 39) * 4) by lia.
    apply Z_mod_mult.
  - exact TWR.
  - exact RD.
  - unfold decode_off_win. right. rewrite HspT. lia.
  - intros x Hx Hg. pose proof (ios_inG_low x Hg). lia.
  - exact Htw2.
  - exact Hm.
  - exact Hcmd.
  - unfold CLS_EV. unfold IOSEND_EV in Hev. lia. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & e & -> & He & HJ3 & HP3 & Hfr3 & Hperm3 & HKc & HMO3 & Htw3
  & HG8d).
assert (Ee : e = 0) by (unfold CLS_EV in He; lia). subst e.
replace (k + 0 + 0) with (k + 0) in HJ3 by lia.
destruct (ios_jlayout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (HAR3 & FA3 & Lo3 & Hi3).
(* the int at sp + 4: present at the returned memory *)
assert (HPd : forall a, inG [(spZ regs - IOSEND_FRAME + IOS_DISP_OFF, 4)] a -> apresent (w_H W3) mem3 a).
{ intros a Ha. apply ios_inG1 in Ha. apply (apresent_of_aview segs (w_H W3) mem3 a ltac:(lia)).
  - intros Hi. pose proof (transport_segs_low a Hi). unfold kLowMemEnd in *. lia.
  - apply (ios_garr8_vis (w_H W3) mem3 _ _ HG8d). unfold TW.zs. rewrite length_map, TWL.length_put. lia. }
(* the callee's kept fact, at io_send's entry state, then folded into io_send's own *)
assert (KCr : acall_kept_g segs B TG.G_HARNESS lyc Sc W2 memT W3
  (gover [(spZ regs - IOSEND_FRAME + IOS_DISP_OFF, 4)] mem3 memT) (spZ regsT - CLS_STK) (spZ regsT)
  (cls_wr (spZ regs - IOSEND_FRAME + IOS_DISP_OFF))).
{ apply (ios_kept_relay TG.G_HARNESS ly2 S2 lyc Sc W2 memT W3 _ _ _ _ Hperm2 Hfr2); [|exact HKc].
  intros cid pos. rewrite FA2, FAc. reflexivity. }
assert (RK3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - IOSEND_STK) (spZ regs)
  (fun a => iosend_wr (Z.of_nat (length frame)) a \/
            spZ regs - IOSEND_FRAME + IOS_DISP_OFF <= a < spZ regs - IOSEND_FRAME + IOS_DISP_OFF + 4)).
{ apply (dk_kept_trans_out_g segs B LAWS transport_segs_low TG.G_HARNESS [(spZ regs - IOSEND_FRAME + IOS_DISP_OFF, 4)]
    lyc Sc W memc mdc W2 memT W3 mem3 (spZ regs - IOSEND_STK) (spZ regs) (spZ regsT - CLS_STK) (spZ regsT) _
    (cls_wr (spZ regs - IOSEND_FRAME + IOS_DISP_OFF)) HARc).
  - lia.
  - lia.
  - intros a Ha. apply ios_inG1 in Ha. lia.
  - exact HPd.
  - exact (acall_kept_g_weaken segs B _ _ _ _ _ _ _ _ _ _ _ (fun a Ha => or_introl Ha) HK2).
  - exact KCr.
  - rewrite HspT. lia.
  - rewrite HspT. lia.
  - intros a Ha. exact (ios_cls_wr_iosend _ _ a Ha). }
assert (RKY : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - IOSEND_STK) (spZ regs)
  (iosend_wr (Z.of_nat (length frame)))).
{ apply (ios_kept_shrink TG.G_HARNESS lyc Sc W memc mdc W memc W3 mem3 _ _
    (fun a => iosend_wr (Z.of_nat (length frame)) a \/
              spZ regs - IOSEND_FRAME + IOS_DISP_OFF <= a < spZ regs - IOSEND_FRAME + IOS_DISP_OFF + 4)
    _ LAWS HARc); [|exact RK3].
  intros a [Ha | Ha] Hc; [exact Ha | lia]. }
(* g_s: check_latest_sent_m leaves the world below g_cmd *)
assert (HLB5 : length B5 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw2).
assert (KGs : forall a, TA_g_s <= a < TA_g_s + TW.SZ_g_s ->
  aview segs (w_H W3) mem3 a = aview segs (w_H W2) memT a).
{ apply (ios_gs_kept _ _ B5 Bs Htw2 Htw3). intros i Hi. exact (ios_cls_nth _ _ _ _ _ i Hm HLB5 Hi). }
(* the frame at the returned state *)
assert (SRCK : trans_src_ok B ly3 S3 W3 mem3 p (Z.of_nat (length frame)) /\
  (forall a, p <= a < p + Z.of_nat (length frame) -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) memT a)).
{ apply (ios_src_cls ly2 S2 W2 memT mdT ly3 S3 W3 mem3 md3 (spZ regsT - CLS_STK) (spZ regsT)
    (cls_wr (spZ regs - IOSEND_FRAME + IOS_DISP_OFF)) [(spZ regs - IOSEND_FRAME + IOS_DISP_OFF, 4)] p
    (Z.of_nat (length frame)) LAWS HAR2 HAR3 Hperm3 Hfr3).
  - intros cid pos. rewrite FA3, FA2. reflexivity.
  - rewrite Lo3, Lo2. reflexivity.
  - rewrite Hi3, Hi2. reflexivity.
  - exact HKc.
  - intros a Ha. apply ios_inG1 in Ha. lia.
  - intros a Ha Hg. apply ios_inG1 in Hg. unfold decode_off_win in HOFF. lia.
  - exact KGs.
  - intros a Ha. apply (ios_frame_not_cls regs p (Z.of_nat (length frame)) _ a HFAT HOFF); lia.
  - intros a Ha Hc. destruct (ios_cls_wr_iosend (Z.of_nat (length frame)) _ a Hc) as [Hw | Hd].
    + pose proof (ios_inG_low a (ios_wr_inG _ a Hw)). lia.
    + lia.
  - unfold decode_off_win in HOFF. rewrite HspT. lia.
  - exact HFAT.
  - exact HSRC2.
  - exact H60. }
destruct SRCK as [HSRC3 KF3].
(* io_send's frame above sp + 8: above the callee's window and above the int at sp + 4 *)
assert (KW3 : forall a, spZ regs - IOSEND_FRAME + 8 <= a < spZ regs ->
  aview segs (w_H W3) mem3 a = aview segs (w_H W2) memT a).
{ intros a Ha. pose proof HKc as (K1 & _).
  assert (Hn : ~ inG [(spZ regs - IOSEND_FRAME + IOS_DISP_OFF, 4)] a) by (intros Hg; apply ios_inG1 in Hg; lia).
  rewrite <- (gover_out_aview segs _ (w_H W3) mem3 memT a ltac:(lia) Hn).
  apply K1; [lia | rewrite HspT; lia]. }
apply (HK ly3 S3 W3 mem3 md3 regs3); [| exact HP3 | exact HG8d].
exact (ios_tail_core STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 memT mdT B5 ly3 S3 W3
  mem3 md3 Bs MTL HT0 HJ3 Hfr3 Hperm3 HMO3 RKY HSRC3 KF3 KW3 Htw3).
Qed.

(* ------------------------------------------------------------------ *)
(* The check_latest_sent case, 0x83304 .. 0x83334                      *)
(* ------------------------------------------------------------------ *)

Definition IOS_SENT : Z := IOS_AT 0x5a4.
Definition IOS_DISP_RET : Z := IOS_AT 0x5c4.

(* The end of a case of the tail at IOS_FLY: after a leaf call (whose window mem3 differs from mem2 on) and stores
   into [M + lo, M + hi) (bytes of iosend_wr), the state at IOS_FLY with the world relation at B6. *)
Lemma ios_fin_gen : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs p frame Bw
    ly2 S2 (W2 : world segs) mem2 md2 Bx mem3 memF mdF (regs2 regsF : bvmap 5 word) lo hi B6
    (Q : world segs -> config -> Prop),
  AR_laws segs B -> ameter_laws MT -> gx_ok segs B TG.G_HARNESS ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  60 <= Z.of_nat (length frame) ->
  ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 mem2 md2 Bx ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memF mdF (k + 0) ->
  0 <= lo -> hi <= TW.SZ_M ->
  (forall a, TA_M + lo <= a < TA_M + hi -> iosend_wr (Z.of_nat (length frame)) a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - IOSEND_FRAME - ESTACK <= a < spZ regs - IOSEND_FRAME) ->
     aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + lo <= a < TA_M + hi) ->
     aview segs (w_H W2) memF a = aview segs (w_H W2) mem3 a) ->
  (forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) memF a) ->
  tw_at TMAP_A (aview segs (w_H W2) memF) B6 ->
  aregs_preserved regs2 regsF ->
  (forall ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word),
     ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly3 S3 W3 mem3 md3 B6 ->
     aregs_preserved regs2 regs3 ->
     SRr segs W3 (@cfg_at fx segs (transport_text + IOS_FLY) regs3 mem3 md3) Q) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_FLY) regsF memF mdF) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 Bx mem3 memF mdF
  regs2 regsF lo hi B6 Q LAWS MTL HGX HF H60 HT HJF Hlo0 Hhi0 HWr K3 G3 KF GF HtwF HPF HK.
pose proof HF as (HJc & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EIS : IOSEND_STK = 8496) by reflexivity. assert (EIF : IOSEND_FRAME = 160) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (EM : TA_M = 0x5df160) by reflexivity. assert (SM : TW.SZ_M = 1648) by reflexivity.
pose proof HJc as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _). clear memS HJi.
apply (HK ly2 S2 W2 memF mdF regsF); [|exact HPF].
apply (ios_tail_same STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 Bx
  memF mdF B6 (fun a => TA_M + lo <= a < TA_M + hi) LAWS MTL HGX HF H60 HT HJF).
- intros a Ha. cbv beta in Ha. split; [lia | exact (HWr a Ha)].
- intros a Ha H1 H2. rewrite (KF a Ha H2). apply K3; [exact Ha | lia].
- intros a Ha. exact (GF a (G3 a Ha)).
- exact HtwF.
Qed.

(* The int a callee wrote through a pointer, as the 4-byte value a load reads. *)
Lemma ios_val_put4 : forall (H : word -> bool) (m : word -> option byte) q v,
  garr8 segs (mrestrict H m) q (TW.zs (TW.put 4 v)) -> val_mem segs (mrestrict H m) q 4 (v mod 2 ^ 32).
Proof.
intros H m q v HG k Hk.
assert (Hj : (k < length (TW.zs (TW.put 4 v)))%nat) by (unfold TW.zs; rewrite length_map, TWL.length_put; lia).
destruct (HG k Hj) as [HV _]. specialize (HV 0%nat ltac:(lia)).
replace (q + Z.of_nat k) with (q + Z.of_nat k + Z.of_nat 0) by lia. rewrite HV. f_equal. f_equal.
unfold TW.zs. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, TWL.length_put; lia).
rewrite map_nth. rewrite (tw_le_byte_put 4 v k _ Hk).
assert (R : 0 <= YO0f.le_byte v 4 k < 256) by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
rewrite (tw_le_byte1 _ R).
change (le_byte (v mod 2 ^ 32) 4 k) with (YO0f.le_byte (v mod 2 ^ 32) 4 k).
unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* A signed 32-bit value through its low 32 bits and back. *)
Lemma ios_swrap32 : forall d, -2^31 <= d < 2^31 -> bv_swrap 32 (d mod 2 ^ 32) = d.
Proof.
intros d Hd. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648.
change (2 ^ 32) with 4294967296. rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

(* One stack cell at sp + off holding v (a load's source), as the run's entry state. *)
Definition stk1_region (off : Z) (n : N) : YP09.region :=
  YP09.mkRegion (Some 2%nat) off (off + Z.of_N n) off off [YP09.mkChunk off (CVal n (SOff 32 0))].
Definition stk1_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_stk1 (pc off : Z) (n : N) : sstate := mkSS pc sr_atoms [stk1_region off n] None stk1_facts.
Definition ios_x1_E (regs : bvmap 5 word) (x : Z) : env := Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 x]).

Lemma ios_x1_agree : forall regs x, env_agree 32 (Ereg regs [Z_to_bv 64 x]) (ios_x1_E regs x).
Proof.
intros regs x. split; [|reflexivity]. intros n Hn. unfold ios_x1_E. rewrite Eimg_low by (unfold A_TEXT; lia).
reflexivity.
Qed.

Lemma ios_stk1_entry : forall (W : world segs) (regs : bvmap 5 word) mem pc off (n : N) v,
  regions_wf [stk1_region off n] = true ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 -> 0 <= off -> off + Z.of_N n <= 256 -> Z.of_N n <= 8 ->
  0 <= v < 2 ^ (8 * Z.of_N n) ->
  val_mem segs (mrestrict (w_H W) mem) (spZ regs + off) (N.to_nat n) v ->
  st_ok_pi segs VAL (ios_x1_E regs v) (ss_stk1 pc off n)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem pc off n v Hwf Hsp Hsp16 Hoff Hn Hn8 Hv HV.
set (E := ios_x1_E regs v).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (unfold E, ios_x1_E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 v)
  by (unfold E, ios_x1_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
rewrite restrict_mkst_fx. unfold ss_stk1.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- exact Hwf.
- apply Forall_cons; [|apply Forall_nil].
  unfold stk1_region, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val segs E _ (spZ regs) off n (SOff 32 0) v);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Hv | exact Hn8 | exact HV].
- apply pairwise_disjoint_of_extents. cbn. tauto.
- unfold stk1_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.

(* After check_latest_display (0x83324): g_now (object 27, atom 32) and the 12 bytes M + 64 .. M + 76 through
   s4 = M (atom 20, written). *)
Definition cd_now_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 27)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition cd_M_region : YP09.region := YP09.mkRegion (Some 20%nat) 64 76 64 76 [].
Definition cd_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF TA_M TA_M 5); (A_OBJ 27, mkAF TA_g_now TA_g_now 5)]
    [] [].
Definition ss_cd : sstate := mkSS IOS_DISP_RET sr_atoms [cd_now_region; cd_M_region] None cd_facts.

Lemma ios_cd_entry : forall (W : world segs) (regs : bvmap 5 word) mem (Bx : list byte),
  tw_at TMAP_A (aview segs (w_H W) mem) Bx -> YK11.getr regs 20 = w64 TA_M ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (ios_x1_E regs (TW.g_now Bx)) ss_cd
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + IOS_DISP_RET)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem Bx Htw H20 Hsp Hsp16.
set (E := ios_x1_E regs (TW.g_now Bx)).
assert (EM : TA_M = 0x5df160) by reflexivity. assert (EN : TA_g_now = 0x5df100) by reflexivity.
assert (E20 : ew E 20 = Z_to_bv 64 TA_M)
  by (unfold E, ios_x1_E; rewrite (ew_Eimg_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (U20 : bv_unsigned (ew E 20) = TA_M) by (rewrite E20; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (unfold E, ios_x1_E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 (TW.g_now Bx))
  by (unfold E, ios_x1_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
destruct ios_tail_vals as (V8 & V27 & V30 & VB).
assert (U27 : bv_unsigned (ew E (A_OBJ 27)) = TA_g_now).
{ unfold E, ios_x1_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V27.
  apply unsigned_lit_small. lia. }
pose proof (TWL.u_at_range Bx TW.OFF_g_now 8) as Rw.
change (TW.u_at Bx TW.OFF_g_now 8) with (TW.g_now Bx) in Rw. change (8 * Z.of_nat 8) with 64 in Rw.
rewrite restrict_mkst_fx. unfold ss_cd.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold cd_now_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ TA_g_now 0 8 (SOff 32 0) (TW.g_now Bx));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
    exact (tw_read_val segs (mrestrict (w_H W) mem) TMAP_A Bx TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8 TMAP_A_ok Htw
      TMAP_A_g_now ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)).
  + unfold cd_M_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply ios_inG_M.
    unfold TW.SZ_M. lia.
- apply pairwise_disjoint_of_extents.
  unfold cd_now_region, cd_M_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20, U27.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold cd_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, U20, U27. change (2 ^ 4) with 16. change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.

Ltac ios_awr_lia :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* From 0x83304 (the `bnez a0` on g_raw; reached when g_raw is set or the frame is no keepalive) to IOS_FLY: the
   g_raw case goes there at once (:874); else check_latest_sent (ios_cls_at), and when it set the display int the
   call of check_latest_display and the stores M.last_display = g_now, M.display_sent = 1 (:875-879). *)
Lemma ios_tail_sent : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) p frame Bw ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) B5 B6
    (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 mem2 md2 B5 ->
  DSpec.sf_code (TC.rf frame) = DSpec.SPEC_OK -> 60 <= Z.of_nat (length frame) ->
  YK11.getr regs2 2 = w64 (spZ regs - IOSEND_FRAME) ->
  YK11.getr regs2 3 = w64 (as_gp B) -> YK11.getr regs2 4 = w64 (as_tp B) ->
  YK11.getr regs2 10 = w64 (TW.g_raw B5) -> YK11.getr regs2 18 = w64 (ios_blen frame) ->
  YK11.getr regs2 20 = w64 TA_M ->
  ios_B6 frame B5 = Some (B6, tt) ->
  (TC.truth (TW.g_raw B5) = false -> ios_ka frame = false) ->
  (forall s, 0 <= s < TW.g_ncmd B5 -> TW.Cmd_st B5 s = TC.PENDING -> TW.Cmd_len B5 s <= DSpec.SPEC_CMD_MAX) ->
  (forall ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word),
     ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly3 S3 W3 mem3 md3 B6 ->
     aregs_preserved regs2 regs3 ->
     SRr segs W3 (@cfg_at fx segs (transport_text + IOS_FLY) regs3 mem3 md3) Q) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_SENT) regs2 mem2 md2) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 B5 B6 Q
  HL HF HT HOK H60 R2 R3 R4 R10 R18 R20 HB6 Hka Hcmd HK.
pose proof HL as HL0. pose proof HF as HF0. pose proof HT as HT0.
destruct HL as (HCELLS & HIOC & LAWS & MTL & HGX & HGE & HMS & HCSF & HCAF & HCLC & HCIR & HCSW & HCIN & HCLF & HCKD
  & HCLS & HCLD & HMC).
destruct HF as (HJc & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & Hp0 & _).
destruct HT as ((HJ2 & _) & _ & HSF2 & _ & HSRC2 & _ & _ & Htw2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EIS : IOSEND_STK = 8496) by reflexivity. assert (EIF : IOSEND_FRAME = 160) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity. assert (EFO : IOS_F_OFF = 8) by reflexivity.
assert (EDO : IOS_DISP_OFF = 4) by reflexivity.
assert (EM : TA_M = 0x5df160) by reflexivity. assert (SM : TW.SZ_M = 1648) by reflexivity.
assert (GHI : TG.G_HARNESS_HI = 0x5f3190) by reflexivity. assert (GLO : TG.G_HARNESS_LO = 0x5df080) by reflexivity.
destruct (ios_jlayout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (HAR2 & _ & _ & _).
pose proof HJc as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _). clear memS HJi.
assert (Hsp2 : spZ regs2 = spZ regs - IOSEND_FRAME).
{ unfold spZ at 1. rewrite R2. apply unsigned_lit_small. lia. }
assert (Hm16 : spZ regs2 mod 16 = 0).
{ rewrite Hsp2, EIF. replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hsp16. }
assert (HLB5 : length B5 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw2).
pose proof (TWL.s32_range B5 TW.OFF_g_raw) as Rg. change (TW.s32_at B5 TW.OFF_g_raw) with (TW.g_raw B5) in Rg.
(* f.body: the 8 bytes at sp + 56 (the struct at sp + 8, field body at 48) hold p + 30 *)
destruct (ios_fields frame HOK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fbody & _).
destruct HSF2 as (_ & _ & SB & HGSB & HLSB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HB48 & _).
unfold TCt.sf_ptr in HB48. rewrite HOK, Fbody, Z.eqb_refl in HB48.
pose proof (trans_src_ok_rd B LAWS ly2 S2 W2 mem2 md2 p _ HAR2 HSRC2 ltac:(lia)) as (_ & _ & _ & _ & Hq0 & Hq63).
pose proof (ios_val_of_garr8 _ (spZ regs - IOSEND_FRAME + IOS_F_OFF) SB 48 8 HGSB ltac:(lia)
  ltac:(rewrite HLSB; lia)) as VB.
rewrite HB48 in VB. replace (spZ regs - IOSEND_FRAME + IOS_F_OFF + 48) with (spZ regs2 + 56) in VB by lia.
(* run 1, +0x5a4: `bnez a0` *)
set (E0 := ios_x1_E regs2 (p + 30)).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ios_x1_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0, ios_x1_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E0 32 = Z_to_bv 64 (p + 30))
  by (unfold E0, ios_x1_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
pose proof (ios_stk1_entry W2 regs2 mem2 IOS_SENT 56 8 (p + 30) ltac:(vm_compute; reflexivity) ltac:(lia) Hm16
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(change (8 * Z.of_N 8) with 64; lia) VB) as HS. fold E0 in HS.
assert (SHOK : sh_ok segs IOS_Bx [] E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof HJ2 as HJ.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + IOS_SENT)) mem2 (YK11.seg_rom segs)) md2) Qx)
end.
assert (Ug : U E0 (SOff 10 0) = TW.g_raw B5 mod 2 ^ 64).
{ rewrite U_SOff, (EE 10%nat 10%bv eq_refl), R10, Z.add_0_r. unfold w64. rewrite Z_to_bv_unsigned.
  unfold zcanon, M64, bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_mod. lia. }
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* g_raw set: on to IOS_FLY (:874) *)
  rewrite branch_ne_U, Ug, U_SLit in Hc. unfold zcanon, M64 in Hc. rewrite Zmod_0_l in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Htr : TC.truth (TW.g_raw B5) = true).
  { unfold TC.truth. apply negb_true_iff, Z.eqb_neq. intros E. apply Hc. rewrite E. reflexivity. }
  pose proof (ios_B6_raw frame B5 B6 HB6 Htr) as EB6. subst B6.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_FLY.
  { ios_awr_lia. }
  set (mdF := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdF. clear mat.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  assert (KRF : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem2 a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin Hx. ios_win Hin Hx ltac:(lia). }
  assert (GRF : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msF) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  assert (HPF : aregs_preserved regs2 (ms_regs msF)).
  { apply (aregs_preserved_of_st_ok segs (w_H W2) E0 _ msF regs2 [Z_to_bv 64 (p + 30)] HS).
    - apply ios_x1_agree.
    - vm_compute. reflexivity. }
  pmkst HS.
  change (SRr segs W2 (@cfg_at fx segs (transport_text + IOS_FLY) (ms_regs msF) (ms_mem msF) mdF) Q).
  apply (ios_fin_gen STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 B5 mem2
    (ms_mem msF) mdF regs2 (ms_regs msF) 0 0 B5 Q LAWS MTL HGX HF0 H60 HT0 HJ);
    [lia | lia | intros a Ha; lia | intros a _ _; reflexivity | intros a Ha; exact Ha
    | intros a Ha _; exact (KRF a Ha) | exact GRF | | exact HPF | exact HK].
  apply (tw_kept TMAP_A _ _ B5 Htw2). intros x Hx. pose proof (TMAP_A_hull x Hx). apply KRF. lia.
- (* g_raw clear: check_latest_sent (:875) *)
  rewrite branch_ne_U, Ug, U_SLit in Hc. unfold zcanon, M64 in Hc. rewrite Zmod_0_l in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hg0 : TW.g_raw B5 = 0).
  { pose proof (Z.div_mod (TW.g_raw B5) (2 ^ 64) ltac:(lia)) as D. rewrite Hc in D. lia. }
  assert (Htr : TC.truth (TW.g_raw B5) = false) by (unfold TC.truth; rewrite Hg0; reflexivity).
  clear Hc.
  destruct (ios_B6_sent frame B5 B6 HB6 Htr (Hka Htr)) as (Bs & disp & Hm & HBs).
  (* run 2, +0x5a8 .. +0x5b4: a0 = f.body, a2 = sp + 4, a1 = s2 = f.body_len; the call *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ios_awr_lia. }
  set (mdT := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdT. clear mat.
  lazymatch type of HS with
  | st_ok _ _ _ (restrict _ ?m) => rename m into msT
  | st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msT
  end.
  assert (KRT : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msT) a = aview segs (w_H W2) mem2 a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin Hx. ios_win Hin Hx ltac:(lia). }
  assert (GRT : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msT) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  pmkst HS.
  ios_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + IOS_TAIL)) Q1 ltac:(apply codeptr_val; exact HEI).
  ios_reg HS (2%bv : bv 5) (YK11.getr regs2 2) Q2
    ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  ios_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
    ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R3).
  ios_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
    ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R4).
  ios_reg HS (10%bv : bv 5) (w64 (p + 30)) Q10
    ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  ios_reg HS (11%bv : bv 5) (YK11.getr regs2 18) Q11
    ltac:(cbn [sv_denot]; rewrite (EE 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  ios_reg HS (12%bv : bv 5) (w64 (spZ regs - IOSEND_FRAME + IOS_DISP_OFF)) Q12
    ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl);
          change (bv_unsigned (YK11.getr regs2 2)) with (spZ regs2); rewrite Hsp2; reflexivity).
  assert (HPT : aregs_preserved regs2 (ms_regs msT)).
  { apply (aregs_preserved_of_st_ok segs (w_H W2) E0 _ msT regs2 [Z_to_bv 64 (p + 30)] HS).
    - apply ios_x1_agree.
    - vm_compute. reflexivity. }
  assert (HTT : ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 (ms_mem msT)
    mdT B5).
  { apply (ios_tail_same STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 B5
      (ms_mem msT) mdT B5 (fun _ => False) LAWS MTL HGX HF0 H60 HT0 HJ).
    - intros a [].
    - intros a Ha _ _. exact (KRT a Ha).
    - exact GRT.
    - apply (tw_kept TMAP_A _ _ B5 Htw2). intros x Hx. pose proof (TMAP_A_hull x Hx). apply KRT. lia. }
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_check_latest_sent) rg mm mdx) Qx) end.
  destruct ios_tail_vals as (_ & _ & _ & VBASE).
  apply (ios_cls_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 (ms_mem msT) mdT
    B5 (ms_regs msT) Bs disp Q HL0 HF0 HOK H60 HTT).
  + rewrite Q1. apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold IOS_TAIL, IOS_AT, AF_io_send; lia | reflexivity].
  + unfold raZ. rewrite Q1, VBASE. rewrite unsigned_lit_small by (unfold transport_text, IOS_TAIL, IOS_AT, AF_io_send; lia).
    unfold transport_text, IOS_TAIL, IOS_AT, AF_io_send. lia.
  + rewrite Q2. exact R2.
  + exact Q3.
  + exact Q4.
  + exact Q10.
  + rewrite Q11. exact R18.
  + exact Q12.
  + exact Hm.
  + exact Hcmd.
  + intros ly3 S3 W3 mem3 md3 regs3 HT3 HP3 HG8d. rewrite Q1.
    (* run 3, +0x5b8 .. +0x5bc: the display int, `beqz a0` *)
    pose proof HT3 as HT3c.
    destruct HT3 as ((HJ3 & _) & _ & _ & _ & _ & _ & _ & Htw3).
    assert (HPB : aregs_preserved regs2 regs3) by exact (aregs_preserved_trans _ _ _ HPT HP3).
    assert (R2b : YK11.getr regs3 2 = YK11.getr regs2 2) by exact (HPB 2 ltac:(unfold acallee_saved; lia)).
    assert (R3b : YK11.getr regs3 3 = w64 (as_gp B))
      by (rewrite <- R3; exact (HPB 3 ltac:(unfold acallee_saved; lia))).
    assert (R4b : YK11.getr regs3 4 = w64 (as_tp B))
      by (rewrite <- R4; exact (HPB 4 ltac:(unfold acallee_saved; lia))).
    assert (R20b : YK11.getr regs3 20 = w64 TA_M)
      by (rewrite <- R20; exact (HPB 20 ltac:(unfold acallee_saved; lia))).
    assert (Hsp3 : spZ regs3 = spZ regs - IOSEND_FRAME) by (unfold spZ at 1; rewrite R2b; exact Hsp2).
    assert (Hm3 : spZ regs3 mod 16 = 0) by (rewrite Hsp3, <- Hsp2; exact Hm16).
    assert (HLs : (IOS_LOWN <= length B5)%nat) by (rewrite HLB5; unfold IOS_LOWN, TW.OFF_g_cmd, TW.W_LEN; lia).
    destruct (ios_cls_low _ _ _ _ _ Hm HLs) as [_ Hdr].
    pose proof (ios_val_put4 (w_H W3) mem3 _ disp HG8d) as VD.
    replace (spZ regs - IOSEND_FRAME + IOS_DISP_OFF) with (spZ regs3 + 4) in VD by lia.
    clear HS SHOK HJ.
    set (E1 := ios_x1_E regs3 (disp mod 2 ^ 32)).
    assert (HEI1 : img_env VAL A_LIM E1) by (unfold E1, ios_x1_E; apply Eimg_env).
    assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = YK11.getr regs3 r)
      by (intros n r Hn; unfold E1, ios_x1_E; apply ew_Eimg_Ereg_nat; exact Hn).
    assert (E32b : ew E1 32 = Z_to_bv 64 (disp mod 2 ^ 32))
      by (unfold E1, ios_x1_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
    assert (Rd : 0 <= disp mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
    pose proof (ios_stk1_entry W3 regs3 mem3 IOS_TAIL 4 4 (disp mod 2 ^ 32) ltac:(vm_compute; reflexivity)
      ltac:(rewrite Hsp3; lia) Hm3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(change (8 * Z.of_N 4) with 32; lia) VD)
      as HS. fold E1 in HS.
    assert (SHOK : sh_ok segs IOS_Bx [] E1 (mrestrict (w_H W3) mem3)) by constructor.
    rename HJ3 into HJ.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { ios_awr_lia. }
    set (mdB := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdB. clear mat.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msB end.
    assert (KRB : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem msB) a = aview segs (w_H W3) mem3 a).
    { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
      intros b wlo whi x Hin Hx. ios_win Hin Hx ltac:(lia). }
    assert (GRB : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msB) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    clear HF HFr HG.
    assert (Ud : U E1 (SOff 32 0) = disp mod 2 ^ 32) by (apply U_atom; [exact E32b | lia]).
    assert (Ua0 : U E1 (SExt true 32 (SOff 32 0)) = disp mod 2 ^ 64).
    { rewrite U_SExt, Ud. cbv iota. change (Z.of_N 32) with 32. rewrite Z.mod_mod by lia.
      rewrite ios_swrap32 by lia. reflexivity. }
    assert (Uz : U E1 (SLit 0) = 0) by (rewrite U_SLit; reflexivity).
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * (* the display int is 0: on to IOS_FLY (:876) *)
      rewrite branch_eq_U, Ua0, Uz in Hc. apply Z.eqb_eq in Hc.
      assert (Hd0 : disp = 0).
      { pose proof (Z.div_mod disp (2 ^ 64) ltac:(lia)) as D. rewrite Hc in D. lia. }
      destruct HBs as [[_ EB6] | [Htd _]]; [| unfold TC.truth in Htd; rewrite Hd0 in Htd; discriminate Htd].
      subst B6.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_FLY.
      { ios_awr_lia. }
      set (mdF := with_vm_backing (m_vm_lazy mdB) mat mdB) in *. clearbody mdF. clear mat.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
      assert (KRF : forall a, 0 <= a < 2 ^ 64 ->
        aview segs (w_H W3) (ms_mem msF) a = aview segs (w_H W3) mem3 a).
      { intros a Ha. rewrite <- (KRB a Ha).
        apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
        intros b wlo whi x Hin Hx. ios_win Hin Hx ltac:(lia). }
      assert (GRF : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msF) a)
        by (intros a Ha; exact (apresent_grows _ _ _ a HG (GRB a Ha))).
      clear HF HFr HG.
      assert (HPF : aregs_preserved regs3 (ms_regs msF)).
      { apply (aregs_preserved_of_st_ok segs (w_H W3) E1 _ msF regs3 [Z_to_bv 64 (disp mod 2 ^ 32)] HS).
        - apply ios_x1_agree.
        - vm_compute. reflexivity. }
      pmkst HS.
      change (SRr segs W3 (@cfg_at fx segs (transport_text + IOS_FLY) (ms_regs msF) (ms_mem msF) mdF) Q).
      apply (ios_fin_gen STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly3 S3 W3 mem3 md3 Bs
        mem3 (ms_mem msF) mdF regs2 (ms_regs msF) 0 0 Bs Q LAWS MTL HGX HF0 H60 HT3c HJ);
        [lia | lia | intros a Ha; lia | intros a _ _; reflexivity | intros a Ha; exact Ha
        | intros a Ha _; exact (KRF a Ha) | exact GRF | | exact (aregs_preserved_trans _ _ _ HPB HPF) | exact HK].
      apply (tw_kept TMAP_A _ _ Bs Htw3). intros x Hx. pose proof (TMAP_A_hull x Hx). apply KRF. lia.
    * (* the display int is set: check_latest_display, then M.last_display and M.display_sent (:877-879) *)
      rewrite branch_eq_U, Ua0, Uz in Hc. apply Z.eqb_neq in Hc.
      assert (Hd0 : disp <> 0) by (intros E; apply Hc; rewrite E; reflexivity).
      destruct HBs as [[Htd _] | [_ [Hcld EB6]]].
      { exfalso. unfold TC.truth in Htd. apply negb_false_iff, Z.eqb_eq in Htd. exact (Hd0 Htd). }
      subst B6.
      (* run 4, +0x5bc .. +0x5c0: the call of check_latest_display *)
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { ios_awr_lia. }
      set (mdC := with_vm_backing (m_vm_lazy mdB) mat mdB) in *. clearbody mdC. clear mat.
      lazymatch type of HS with
      | st_ok _ _ _ (restrict _ ?m) => rename m into msC
      | st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msC
      end.
      assert (KRC : forall a, 0 <= a < 2 ^ 64 ->
        aview segs (w_H W3) (ms_mem msC) a = aview segs (w_H W3) mem3 a).
      { intros a Ha. rewrite <- (KRB a Ha).
        apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
        intros b wlo whi x Hin Hx. ios_win Hin Hx ltac:(lia). }
      assert (GRC : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msC) a)
        by (intros a Ha; exact (apresent_grows _ _ _ a HG (GRB a Ha))).
      clear HF HFr HG.
      pmkst HS.
      ios_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + IOS_DISP_RET)) Q1c ltac:(apply codeptr_val; exact HEI1).
      ios_reg HS (2%bv : bv 5) (YK11.getr regs3 2) Q2c
        ltac:(cbn [sv_denot]; rewrite (EE1 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
      ios_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3c
        ltac:(cbn [sv_denot]; rewrite (EE1 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R3b).
      ios_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4c
        ltac:(cbn [sv_denot]; rewrite (EE1 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R4b).
      assert (HPC : aregs_preserved regs3 (ms_regs msC)).
      { apply (aregs_preserved_of_st_ok segs (w_H W3) E1 _ msC regs3 [Z_to_bv 64 (disp mod 2 ^ 32)] HS).
        - apply ios_x1_agree.
        - vm_compute. reflexivity. }
      assert (Hspc : spZ (ms_regs msC) = spZ regs - IOSEND_FRAME) by (unfold spZ at 1; rewrite Q2c; exact Hsp3).
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
        change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS_check_latest_display)) mm rom) mdx)
          Qx) end.
      apply (ios_leaf_call W3 (ms_regs msC) (ms_mem msC) STK sp0 FP ly S W0 mem0 md0 own ly3 S3 mdC (k + 0)
        (spZ regs - IOSEND_FRAME - sp0) (transport_sigma TS_check_latest_display) (fun _ => Bs = Bs) Q LAWS HJ).
      -- lia.
      -- replace (spZ regs - IOSEND_FRAME - sp0) with (spZ regs - sp0 + (-10) * 16) by (rewrite EIF; lia).
         rewrite Z_mod_plus_full, Zminus_mod, Hsp16, Hsp0a. reflexivity.
      -- lia.
      -- lia.
      -- rewrite Q1c. apply (ret_ok_codeptr_v (PI := PI_transport));
           [unfold IOS_DISP_RET, IOS_AT, AF_io_send; lia | reflexivity].
      -- exact Q3c.
      -- exact Q4c.
      -- intros HPRE.
         apply (ios_cld_leaf W3 (ms_regs msC) (ms_mem msC) mdC ly3 S3 Bs HCLD); [| exact Hcld | lia | lia | exact HPRE].
         apply (tw_kept TMAP_A _ _ Bs Htw3). intros x Hx. pose proof (TMAP_A_hull x Hx). apply KRC. lia.
      -- intros regs4 mem4 md4 HJ4 HP4 HK4 HG4 _.
         rewrite Q1c.
         (* run 5, +0x5c4 .. +0x5d4: a0 = g_now, the stores at M + 64 (8 bytes) and M + 72 (4 bytes of 1) *)
         assert (HP34 : aregs_preserved regs3 regs4) by exact (aregs_preserved_trans _ _ _ HPC HP4).
         assert (R20c : YK11.getr regs4 20 = w64 TA_M)
           by (rewrite <- R20b; exact (HP34 20 ltac:(unfold acallee_saved; lia))).
         assert (R2c : YK11.getr regs4 2 = YK11.getr regs3 2) by exact (HP34 2 ltac:(unfold acallee_saved; lia)).
         assert (Hsp4 : spZ regs4 = spZ regs - IOSEND_FRAME) by (unfold spZ at 1; rewrite R2c; exact Hsp3).
         assert (Hm4 : spZ regs4 mod 16 = 0) by (rewrite Hsp4, <- Hsp3; exact Hm3).
         assert (K4 : forall a, 0 <= a < 2 ^ 64 ->
           ~ (spZ regs - IOSEND_FRAME - ESTACK <= a < spZ regs - IOSEND_FRAME) ->
           aview segs (w_H W3) mem4 a = aview segs (w_H W3) mem3 a).
         { intros a Ha Hn. rewrite (HK4 a Ha ltac:(rewrite Hspc; exact Hn)). exact (KRC a Ha). }
         assert (G4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem4 a)
           by (intros a Ha; exact (HG4 a (GRC a Ha))).
         assert (Htw4 : tw_at TMAP_A (aview segs (w_H W3) mem4) Bs).
         { apply (tw_kept TMAP_A _ _ Bs Htw3). intros x Hx. pose proof (TMAP_A_hull x Hx). apply K4; lia. }
         clear HS SHOK HJ.
         set (E2 := ios_x1_E regs4 (TW.g_now Bs)).
         assert (HEIc : img_env VAL A_LIM E2) by (unfold E2, ios_x1_E; apply Eimg_env).
         pose proof (ios_cd_entry W3 regs4 mem4 Bs Htw4 R20c ltac:(rewrite Hsp4; lia) Hm4) as HS. fold E2 in HS.
         assert (SHOK : sh_ok segs IOS_Bx [] E2 (mrestrict (w_H W3) mem4)) by constructor.
         rename HJ4 into HJ.
         assert (U20c : bv_unsigned (ew E2 20) = TA_M).
         { unfold E2, ios_x1_E. rewrite (ew_Eimg_Ereg_nat regs4 _ 20 20%bv eq_refl), R20c.
           apply unsigned_lit_small. lia. }
         assert (E32c : ew E2 32 = Z_to_bv 64 (TW.g_now Bs))
           by (unfold E2, ios_x1_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 0)).
         pose proof (TWL.u_at_range Bs TW.OFF_g_now 8) as Rw.
         change (TW.u_at Bs TW.OFF_g_now 8) with (TW.g_now Bs) in Rw. change (8 * Z.of_nat 8) with 64 in Rw.
         paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_FLY.
         { ios_awr_M U20c. }
         set (mdF := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody mdF. clear mat.
         lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
         assert (KRF : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 64 <= a < TA_M + 76) ->
           aview segs (w_H W3) (ms_mem msF) a = aview segs (w_H W3) mem4 a).
         { intros a Ha Hn.
           apply (kept_of_frame _ _ _ _ _ (fun x => TA_M + 64 <= x < TA_M + 76) HFr); [| exact Ha | exact Hn].
           intros b wlo whi x Hin Hx. ios_win Hin Hx ltac:(rewrite ?U20c in Hx; lia). }
         assert (GRF : forall a, apresent (w_H W3) mem4 a -> apresent (w_H W3) (ms_mem msF) a)
           by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
         clear HF HFr HG.
         (* the two stores *)
         pose proof (st_ok_pi_region_nth E2 _ (restrict (w_H W3) msF) 1 _ HS eq_refl) as RG.
         cbn [ms_mem restrict] in RG.
         destruct RG as (_ & _ & _ & HCH). rewrite Forall_forall in HCH.
         pose proof (HCH (YP09.mkChunk 64 (CVal 8 (SOff 32 0))) ltac:(cbn; tauto)) as CH1.
         pose proof (HCH (YP09.mkChunk 72 (CVal 4 (SLit 1))) ltac:(cbn; tauto)) as CH2.
         pose proof (val_of_chunk_any segs E2 _ _ _ _ _ CH1 ltac:(lia)) as VS1.
         pose proof (val_of_chunk_any segs E2 _ _ _ _ _ CH2 ltac:(lia)) as VS2.
         cbn [YP09.r_base base_val] in VS1, VS2. rewrite U20c in VS1, VS2.
         change (N.to_nat 8) with 8%nat in VS1. change (8 * Z.of_N 8) with 64 in VS1.
         change (N.to_nat 4) with 4%nat in VS2. change (8 * Z.of_N 4) with 32 in VS2.
         assert (U32 : U E2 (SOff 32 0) = TW.g_now Bs) by (apply U_atom; [exact E32c | lia]).
         assert (U1 : U E2 (SLit 1) = 1) by (rewrite U_SLit; reflexivity).
         unfold U in U32, U1. rewrite U32, Z.mod_small in VS1 by lia. rewrite U1 in VS2.
         change (1 mod 2 ^ 32) with 1 in VS2.
         assert (HPF : aregs_preserved regs4 (ms_regs msF)).
         { apply (aregs_preserved_of_st_ok segs (w_H W3) E2 _ msF regs4 [Z_to_bv 64 (TW.g_now Bs)] HS).
           - apply ios_x1_agree.
           - vm_compute. reflexivity. }
         pmkst HS.
         change (SRr segs W3 (@cfg_at fx segs (transport_text + IOS_FLY) (ms_regs msF) (ms_mem msF) mdF) Q).
         apply (ios_fin_gen STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly3 S3 W3 mem3 md3 Bs
           mem4 (ms_mem msF) mdF regs2 (ms_regs msF) 64 76
           (TW.set_M_last_display (TW.set_M_display_sent Bs 1) (TW.g_now Bs)) Q LAWS MTL HGX HF0 H60 HT3c HJ).
         ++ lia.
         ++ lia.
         ++ intros a Ha. destruct (Z_lt_ge_dec a (TA_M + 72)) as [H1 | H1];
              [apply ios_wr_lastdisp | apply ios_wr_dispsent]; lia.
         ++ exact K4.
         ++ exact G4.
         ++ exact KRF.
         ++ exact GRF.
         ++ unfold TW.set_M_last_display, TW.set_M_display_sent, TW.A_M_last_display, TW.A_M_display_sent.
            apply (ios_tw_M2 (aview segs (w_H W3) mem4) _ Bs 72 1 64 (TW.g_now Bs) Htw4);
              [lia | lia | lia | lia | | |].
            ** intros j Hj. exact (ios_view_val _ _ _ 4 1 VS2 j Hj).
            ** intros j Hj. exact (ios_view_val _ _ _ 8 _ VS1 j Hj).
            ** intros x Hx H1 H2. pose proof (TMAP_A_hull x Hx). apply KRF; lia.
         ++ exact (aregs_preserved_trans _ _ _ (aregs_preserved_trans _ _ _ HPB HP34) HPF).
         ++ exact HK.
Qed.

(* The cut points of the tail, as the statement's header measures them. *)
Lemma ios_tail_addrs : transport_text + IOS_KA = 0x832cc /\ transport_text + IOS_SENT = 0x83304 /\
  transport_text + IOS_TAIL = 0x83318 /\ transport_text + IOS_DISP_RET = 0x83324 /\
  transport_text + IOS_FLY = 0x83338.
Proof. repeat split; reflexivity. Qed.

(* ios_tail_seg: the DATA arm's tail, 0x832cc .. 0x83334, in continuation form. From the state at 0x832cc (the
   keepalive case: g_raw clear and the frame a keepalive) or at 0x83304 (a0 = g_raw; g_raw set, or the frame no
   keepalive), with the cut facts at the world B5, to the state at transport_text + IOS_FLY with the cut facts at the
   world ios_B6 frame B5 gives and every callee-saved register as at the start. *)
Theorem ios_tail_seg : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) p frame Bw ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) B5 B6 (pc : Z)
    (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly2 S2 W2 mem2 md2 B5 ->
  DSpec.sf_code (TC.rf frame) = DSpec.SPEC_OK -> 60 <= Z.of_nat (length frame) ->
  YK11.getr regs2 2 = w64 (spZ regs - IOSEND_FRAME) ->
  YK11.getr regs2 3 = w64 (as_gp B) -> YK11.getr regs2 4 = w64 (as_tp B) ->
  YK11.getr regs2 18 = w64 (ios_blen frame) -> YK11.getr regs2 20 = w64 TA_M ->
  ios_B6 frame B5 = Some (B6, tt) ->
  (forall s, 0 <= s < TW.g_ncmd B5 -> TW.Cmd_st B5 s = TC.PENDING -> TW.Cmd_len B5 s <= DSpec.SPEC_CMD_MAX) ->
  (pc = IOS_KA /\ TC.truth (TW.g_raw B5) = false /\ ios_ka frame = true \/
   pc = IOS_SENT /\ YK11.getr regs2 10 = w64 (TW.g_raw B5) /\
     (TC.truth (TW.g_raw B5) = false -> ios_ka frame = false)) ->
  (forall ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word),
     ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly3 S3 W3 mem3 md3 B6 ->
     aregs_preserved regs2 regs3 ->
     SRr segs W3 (@cfg_at fx segs (transport_text + IOS_FLY) regs3 mem3 md3) Q) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + pc) regs2 mem2 md2) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 B5 B6 pc Q
  HL HF HT HOK H60 R2 R3 R4 R18 R20 HB6 Hcmd HC HK.
destruct HC as [(-> & Hraw & Hka) | (-> & R10 & Hka)].
- exact (ios_tail_ka STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 B5
    B6 Q HL HF HT H60 R2 R3 R4 R20 HB6 Hraw Hka HK).
- exact (ios_tail_sent STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2
    B5 B6 Q HL HF HT HOK H60 R2 R3 R4 R10 R18 R20 HB6 Hka Hcmd HK).
Qed.

(* What the frame-in-flight segment reads of the struct at the cut memory: f.send, the 4 bytes at sp + 40 (the
   struct at sp + 8, field send at 32), from the cut facts. *)
Lemma ios_tail_send : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc k regs p frame
    ly3 S3 (W3 : world segs) mem3 md3 Bx,
  ios_tail_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly3 S3 W3 mem3 md3 Bx ->
  0 <= DSpec.sf_send (TC.rf frame) < 2 ^ 32 /\
  val_mem segs (mrestrict (w_H W3) mem3) (spZ regs - IOSEND_FRAME + 40) 4 (DSpec.sf_send (TC.rf frame)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame ly3 S3 W3 mem3 md3 Bx HT.
destruct HT as (_ & _ & HSF & _).
destruct HSF as (_ & _ & SB & HGSB & HLSB & _ & _ & _ & _ & _ & _ & _ & HS32 & _).
pose proof (TWL.u_at_range SB 32 4) as R. rewrite HS32 in R. change (8 * Z.of_nat 4) with 32 in R.
split; [exact R|].
pose proof (ios_val_of_garr8 _ (spZ regs - IOSEND_FRAME + IOS_F_OFF) SB 32 4 HGSB ltac:(lia)
  ltac:(rewrite HLSB; lia)) as V.
rewrite HS32 in V.
replace (spZ regs - IOSEND_FRAME + 40) with (spZ regs - IOSEND_FRAME + IOS_F_OFF + 32) by (unfold IOS_F_OFF; lia).
exact V.
Qed.

End tail.

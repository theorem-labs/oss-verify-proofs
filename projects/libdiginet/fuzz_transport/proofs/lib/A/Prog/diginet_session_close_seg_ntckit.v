(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module names changed; 1031 of its 1126 lines of code are new or changed and 935 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/diginet_session_wake_seg_ntc.v, with its module names and numbers changed; 67 of its 164 lines of code are new or changed and 1029 lines of the source are left out. *)
(* diginet_session_close_seg_ntckit: the lemmas the notice piece of diginet_session_close's walk
   (lib/A/Prog/diginet_session_close_seg_ntc.v) uses beyond the kits it Requires (lib/A/Prog/TransportGNotice.v among
   them):
   - close_len1_inv: the length of B1 from the length of close_w1 B1 (the cut gives the world relation at close_w1 B1
     only);
   - close_vm_kept: a value stored at a (val_mem), read again at a later memory and world whose view keeps its bytes;
   - close_nb: the 72 bytes of the notice at p = F + 32 (the 8-byte store of 0x0000000300000002, the stores of old and
     of 8, and the memset's 56 zeros) read as lib/Prog/T/WalkNotify.v ntc_state_bytes 3 old 8;
   - close_trans_ntc: the notice at p as notice's statement reads it (check_state_data_cg.v trans_ntc_at), its bytes in
     the own frame;
   - close_ntc_apart: notice_cg.v notice_apart of this call's notice (its stores are bytes of G, outside the own frame,
     and bytes of close_wr, outside TF by close_apart). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
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
DgnTransportList DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg CanKit TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_close_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_close_seg_kit TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkNotify.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module WN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkNotify.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The world and the bytes                                          *)
(* ------------------------------------------------------------------ *)

(* close_w1 B1 is B1 with 4 bytes put at g_s.inflight, which lies inside the world: B1 has the world's length. *)
Lemma close_len1_inv : forall B1, length (close_w1 B1) = Z.to_nat TW.W_LEN -> length B1 = Z.to_nat TW.W_LEN.
Proof.
  intros B1 L. unfold close_w1, TW.set_S_inflight, TW.upd in L.
  rewrite !length_app, length_firstn, length_skipn, TWL.length_put in L.
  assert (Ho : (Z.to_nat TW.A_S_inflight + 4 < Z.to_nat TW.W_LEN)%nat)
    by (unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; lia).
  set (o := Z.to_nat TW.A_S_inflight) in *. set (w := Z.to_nat TW.W_LEN) in *. clearbody o w. lia.
Qed.

(* A value stored at a, read at a later memory and world whose view keeps its n bytes. *)
Lemma close_vm_kept : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  (forall k, (k < n)%nat -> aview tfibsegs H' m' (a + Z.of_nat k) = aview tfibsegs H m (a + Z.of_nat k)) ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v.
Proof.
  intros H H' m m' a n v Hk Hv k Hlt.
  rewrite (mbyte_of_aview tfibsegs H H' m m' _ (Hk k Hlt)). exact (Hv k Hlt).
Qed.

(* The 72 bytes of the notice at p = F + 32: the 8-byte store of 0x0000000300000002 (kind N_STATE = 2, state
   S_CLOSED = 3), the stores of old and of 8 (reason R_CLOSED), and the memset's 56 zeros, read as
   WalkNotify.v ntc_state_bytes 3 old 8. *)
Lemma close_nb : forall (H : word -> bool) (m : word -> option byte) F old,
  val_mem tfibsegs (mrestrict H m) (F + 32) 8 12884901890 ->
  val_mem tfibsegs (mrestrict H m) (F + 40) 4 old ->
  val_mem tfibsegs (mrestrict H m) (F + 44) 4 8 ->
  (forall a, F + 48 <= a < F + 104 -> aview tfibsegs H m a = Some 0) ->
  garr8 tfibsegs (mrestrict H m) (F + 32) (map DSpec.bz (WN.ntc_state_bytes 3 old 8)).
Proof.
  intros H m F old V0 V8 V12 Z0.
  assert (E8 : map DSpec.bz (TW.put 8 12884901890) = map DSpec.bz (TW.put 4 2 ++ TW.put 4 3))
    by (vm_compute; reflexivity).
  unfold WN.ntc_state_bytes. rewrite app_assoc, map_app, <- E8.
  rewrite !map_app. apply garr8_app. split; [exact (garr8_of_put tfibsegs _ _ 8 12884901890 V0) |].
  rewrite length_map, TWL.length_put. replace (F + 32 + Z.of_nat 8) with (F + 40) by lia.
  apply garr8_app. split; [exact (garr8_of_put tfibsegs _ _ 4 old V8) |].
  rewrite length_map, TWL.length_put. replace (F + 40 + Z.of_nat 4) with (F + 44) by lia.
  apply garr8_app. split; [exact (garr8_of_put tfibsegs _ _ 4 8 V12) |].
  rewrite length_map, TWL.length_put. replace (F + 44 + Z.of_nat 4) with (F + 48) by lia.
  rewrite map_repeat. change (DSpec.bz (DSpec.b8 0)) with 0.
  apply garr8_zeros. intros a Ha.
  pose proof (Z0 a ltac:(lia)) as Za. unfold aview in Za.
  destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Za].
  cbn in Za. injection Za as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The current heap frame, the notice and its stores at the call    *)
(* ------------------------------------------------------------------ *)

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.

(* The notice at p = F + 32 in the own frame, as notice's statement reads it (check_state_data_cg.v trans_ntc_at):
   FAKE, decode_rd_ok from the frame's presence, its shadow bytes 4 .. 12 = 0 and its present shadow; the bytes
   ntc_state_bytes 3 old 8, whose fields are close_ntc B1's; the body NULL with length 0; the announce NULL. *)
Lemma close_trans_ntc : forall lyN S2 (W : world segs) memN mdN (regsC : bvmap 5 word) B1 F pos,
  AR_laws segs B -> @AR rc segs B lyN S2 W memN mdN -> In (CLOSE_CID, pos) (frames S2) ->
  F = frame_addr lyN CLOSE_CID pos -> 4096 <= F -> F mod 64 = 0 -> F + 256 <= alloc_ceiling -> in_app F 256 ->
  F + 256 <= spZ regsC - NOTICE_STK ->
  (forall i, 4 <= i < 13 -> aview segs (w_H W) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  garr8 segs (mrestrict (w_H W) memN) (F + 32) (map DSpec.bz (WN.ntc_state_bytes 3 (TW.S_state (close_w1 B1)) 8)) ->
  trans_ntc_at B lyN S2 W memN regsC NOTICE_STK (F + 32) (close_ntc B1).
Proof.
  intros lyN S2 W memN mdN regsC B1 F pos LAWS HAR Hin EF HF0 HF64 HFc HFapp Hwin ZS HNB.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_frames _ _ LAWS lyN S2 W memN mdN CLOSE_CID pos HAR Hin) as (_ & _ & HFb & HFsh).
  rewrite <- EF in HFb, HFsh. change (fs_frame_bytes CLOSE_CID) with 256 in HFb.
  change (fs_frame_bytes CLOSE_CID / 8) with 32 in HFsh. change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh.
  assert (DFm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  set (old := TW.S_state (close_w1 B1)) in *.
  assert (Hold : - 2 ^ 31 <= old < 2 ^ 31) by (unfold old, TW.S_state; apply TWL.s32_range).
  unfold trans_ntc_at.
  split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
  split.
  { right. split.
    - left. exists CLOSE_CID, pos. split; [exact Hin|]. rewrite <- EF. change (fs_frame_bytes CLOSE_CID) with 256.
      unfold NTC_SIZE. lia.
    - unfold decode_rd_ok, NTC_SIZE. split; [|split; [|split; [|split; [|split]]]].
      + intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
      + apply (frame_ra_zero _ F (F + 32) 72 4 13); [lia | exact DFm8 | lia | lia | exact ZS].
      + apply (frame_hull_vis _ F 256 (F + 32) 72); [lia | exact HF64 | reflexivity | lia | lia | lia |].
        intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
      + apply (amem_range_sub_app F 256); [exact HFapp | lia | lia | lia | lia].
      + lia.
      + lia. }
  split; [left; unfold NTC_SIZE; lia|].
  exists (WN.ntc_state_bytes 3 old 8).
  split; [exact HNB|].
  unfold close_ntc. fold old.
  cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len TI.n_counter TI.n_retry
    TI.n_body TI.n_ann length].
  unfold WN.ntc_state_bytes, TW.s32_at.
  assert (Z0 : TW.u_at (TW.put 4 2 ++ TW.put 4 3 ++ TW.put 4 old ++ TW.put 4 8 ++ repeat (DSpec.b8 0) 56) 48 8 = 0)
    by WN.ntc_field.
  rewrite Z0.
  split; [rewrite ?length_app, ?TWL.length_put, ?repeat_length; reflexivity |].
  split; [WN.ntc_field; try (apply WN.swrap32_mod; lia) |].
  split; [WN.ntc_field; try (apply WN.swrap32_mod; lia) |].
  split; [WN.ntc_field; apply WN.swrap32_mod; exact Hold |].
  split; [WN.ntc_field; try (apply WN.swrap32_mod; lia) |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [apply garr8_nil |].
  split; [exact (trans_src_ok_null B lyN S2 W memN) |].
  split; [left; lia |].
  WN.ntc_field.
Qed.

(* notice's stores (an N_STATE notice: bytes of GOT, bytes of G) are apart from the notice's own bytes (a frame is
   not image), from its empty body, and from TF (close_apart: on this path they are bytes of close_wr). *)
Lemma close_ntc_apart : forall ly2 S2 (W2 : world segs) mem2 md2 (W : world segs) memN (TF : option TI.tframe) Bw B1 r
    F pos,
  AR_laws segs B -> @AR rc segs B ly2 S2 W2 mem2 md2 -> In (CLOSE_CID, pos) (frames S2) ->
  F = frame_addr ly2 CLOSE_CID pos ->
  close_apart TF Bw -> close_sent timg_A TF Bw = Some (B1, r) -> TW.S_state (close_w1 B1) <> TS0.DIGINET_S_CLOSED ->
  notice_apart W memN (F + 32) (close_ntc B1) TF (close_w2 B1).
Proof.
  intros ly2 S2 W2 mem2 md2 W memN TF Bw B1 r F pos LAWS HAR Hin EF Hap Hs Hst x Hx.
  assert (Hw : close_wr TF Bw x)
    by (right; right; exists B1, r; split; [exact Hs | split; [exact Hst | right; exact Hx]]).
  split; [|split].
  - intros Hr. apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 CLOSE_CID pos x HAR Hin);
      [rewrite <- EF; change (fs_frame_bytes CLOSE_CID) with 256; unfold NTC_SIZE in Hr; lia|].
    exact (trans_g_img x (close_nwr_G (close_w2 B1) (close_ntc B1) x eq_refl Hx)).
  - intros NB _ _. split.
    + unfold close_ntc. cbn [TI.n_body length Z.of_nat]. lia.
    + intros Hn. exfalso. apply Hn. reflexivity.
  - intros fr Hfr. exact (Hap x Hw fr Hfr).
Qed.
End k.

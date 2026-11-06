(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 678 of its 962 lines of code are new or changed and 855 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcHead.v, with its module paths, module names and numbers changed; 528 of its 590 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/notice_seg_base.v, with its module paths and module names changed; 329 of its 428 lines of code are new or changed and 491 lines of the source are left out. *)
(* notice_seg_acked: the arm of notice for a notice of kind N_ACKED (0x83618), which counts the notice and tail-jumps
   to check_inflight_acked:
     +0xa0 .. +0xa8  a2 = (s32) GOT.acked (read from the region of that field, its value the world's u32),
                     a2 = a2 + 1;
     +0xac           `sw a2, -608(a0)` with a0 the auipc value of the field (pinned to the field's object + 608 so the
                     store lands in its region);
     +0xb0 .. +0xbc  a0 = p, ra loaded back, sp = sp + 16, the tail jump to check_inflight_acked (0x85240).
   check_inflight_acked is a leaf: its statement (check_inflight_acked_cg.v, read through DgnTransportCg.v
   transport_leaf_at) is applied at the jump's state, which has notice's entry sp and ra, through TransportGCg.v
   gx_call_leaf and DgnTransportLeafb.v decode_leafb_journal; its model call is notice_m's (nt_m_acked: at the world
   after GOT.acked++, which is then Bw'). The leaf returns to notice's caller with every byte outside its ESTACK window
   kept, so the post is the walk's (nta_close). The image-B twin is lib/B/Prog/notice_seg_acked.v. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_data_cg check_state_desk_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import notice_seg_base notice_seg_lib notice_seg_disp.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  DgnTransportLeafb DgnTransportCgRun AsanKA check_state_wake_c check_inflight_acked_c check_inflight_acked_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module NtaAC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module NtaKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.AsanKA.
Module NtaCSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_c.
Module NtaLIAc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_acked_c.
Module NtaLIA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_acked_cg.
Module NtaLB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.DgnTransportLeafb.
Module NtaCR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.DgnTransportCgRun.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The stored value                                                    *)
(* ------------------------------------------------------------------ *)

(* The bytes a notice of kind N_ACKED writes: GOT.acked's four. *)
Lemma nta_wr_acked : forall Bw n a, TI.n_kind n = TC.N_ACKED -> notice_wr Bw n a ->
  TA_GOT + 216 <= a < TA_GOT + 220.
Proof.
  intros Bw n a Hk Hw.
  unfold notice_wr, TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in Hk, Hw.
  unfold twa_fld, TW.A_GOT_acked, TW.OFF_GOT in Hw.
  destruct Hw as [(E & _) | [(E & Ha) | [(E & _) | [(E & _) | [(E & _) | (E & _)]]]]]; try lia.
Qed.

Lemma nta_le_byte_small : forall v (m j : nat), 0 <= YO0f.le_byte v m j < 256.
Proof. intros v m j. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

Lemma nta_mod_64_32 : forall v, bv_unsigned (Z_to_bv 64 v) mod 2 ^ 32 = v mod 2 ^ 32.
Proof.
  intros v. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity.
Qed.

Lemma nta_le_byte_mod32 : forall v (j : nat), YO0f.le_byte (v mod 2 ^ 32) 4 j = YO0f.le_byte v 4 j.
Proof.
  intros v j. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* A leaf entered by a tail jump of the walk                           *)
(* ------------------------------------------------------------------ *)

(* Every byte of the harness globals' hull lies in one loaded segment of image A, so no world hides it. *)
Lemma nta_hull_vis : forall (W : world tfibsegs) x, TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI ->
  w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x Hx. replace x with (TG.G_HARNESS_LO + (x - TG.G_HARNESS_LO)) by lia.
  apply (NtaLB.decode_leafb_covers_visible (w_H W) TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO));
    [exact (w_Hoff W) | vm_compute; reflexivity | lia | unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia].
Qed.

(* The world relation at the view of a world is the world relation at the raw memory (the leaf's csw_view). *)
Lemma nta_tw_csw : forall (W : world tfibsegs) m Bw,
  tw_at TMAP_A (aview tfibsegs (w_H W) m) Bw -> tw_at TMAP_A (NtaCSW.csw_view m) Bw.
Proof.
  intros W m Bw H. apply (tw_kept TMAP_A _ _ Bw H). intros x Hx.
  unfold NtaCSW.csw_view. rewrite (NtaCR.decode_aview_mrd W m x (nta_hull_vis W x (TMAP_A_hull x Hx))).
  reflexivity.
Qed.

(* The leaf's footprint holds every range of the hull. *)
Lemma nta_rng_hull : forall (W : world tfibsegs) lo len,
  TG.G_HARNESS_LO <= lo -> lo + len <= TG.G_HARNESS_HI ->
  NtaLB.LExecF.rng (NtaLB.LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H1 H2. apply NtaLB.decode_leafb_rng;
    [unfold TG.G_HARNESS_LO in H1; lia | unfold TG.G_HARNESS_HI in H2; lia |].
  intros a Ha. apply nta_hull_vis. lia.
Qed.

(* A byte the view shows is not hidden. *)
Lemma nta_vis_of_view : forall (W : world tfibsegs) m a,
  aview tfibsegs (w_H W) m a <> None -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W m a H. destruct (aview tfibsegs (w_H W) m a) as [v|] eqn:E;
    [exact (NtaLB.decode_leafb_aview_vis W m a v E) | exfalso; exact (H eq_refl)].
Qed.

(* w bytes of the notice at p + k, read from its garr8 array: u_at NB k w. *)
Lemma nta_val : forall (mm : word -> option byte) p (NB : list byte) k (w : nat),
  garr8 tfibsegs mm p (map DSpec.bz NB) -> length NB = 72%nat -> 0 <= k -> k + Z.of_nat w <= 72 ->
  val_mem tfibsegs mm (p + k) w (TW.u_at NB k w).
Proof.
  intros mm p NB k w HG HL Hk Hkw j Hj.
  assert (Hjl : (Z.to_nat k + j < length (map DSpec.bz NB))%nat) by (rewrite length_map; lia).
  pose proof (garr8_mbyte tfibsegs mm p (map DSpec.bz NB) (Z.to_nat k + j) HG Hjl) as Hb.
  replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j)) by lia. rewrite Hb. f_equal. f_equal.
  assert (Hls : length (TW.sub NB k w) = w) by (unfold TW.sub; rewrite length_firstn, length_skipn; lia).
  unfold TW.u_at. rewrite <- Hls at 2.
  rewrite (tw_le_byte_ble (TW.sub NB k w) j (Z_to_bv 8 0)) by lia.
  rewrite (tw_nth_sub NB k w j (Z_to_bv 8 0)) by lia.
  rewrite (nth_indep _ 0 (DSpec.bz (Z_to_bv 8 0))) by (rewrite length_map; lia).
  rewrite map_nth. reflexivity.
Qed.

(* The walk's kept bytes across a leaf entered at notice's entry sp: the leaf's window lies in notice's. *)
Lemma nta_KA_leaf : forall (W : world tfibsegs) memc (mT m2 : word -> option byte) regs Bw n spT,
  nt_KA W memc mT (nt_Zs regs Bw n) -> spT = spZ regs ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spT - ESTACK <= a < spT) -> ~ NtaLB.LCK.in_wr [] a ->
     aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) mT a) ->
  (forall a, apresent (w_H W) mT a -> apresent (w_H W) m2 a) ->
  nt_KA W memc m2 (nt_Zs regs Bw n).
Proof.
  intros W memc mT m2 regs Bw n spT HKA Hsp Hk Hg.
  apply (nt_KA_step W memc mT m2 _ (fun a => spT - ESTACK <= a < spT) HKA); [| exact Hg |].
  - intros a Ha Hn. apply Hk; [exact Ha | exact Hn | intros Hw; inversion Hw].
  - intros a Ha. left. subst spT. assert (FS : NOTICE_STK = 8240) by reflexivity. unfold ESTACK in Ha. lia.
Qed.

(* The world relation across a leaf whose window lies above the hull. *)
Lemma nta_tw_leaf : forall (W : world tfibsegs) (mT m2 : word -> option byte) Bw spT,
  tw_at TMAP_A (aview tfibsegs (w_H W) mT) Bw -> TG.G_HARNESS_HI <= spT - ESTACK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spT - ESTACK <= a < spT) -> ~ NtaLB.LCK.in_wr [] a ->
     aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) mT a) ->
  tw_at TMAP_A (aview tfibsegs (w_H W) m2) Bw.
Proof.
  intros W mT m2 Bw spT H Hs Hk. apply (tw_kept TMAP_A _ _ Bw H). intros x Hx.
  pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in *.
  apply Hk; [lia | lia | intros Hw; inversion Hw].
Qed.

Section acked. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The post at a leaf's return to notice's caller (a tail jump: the leaf ran from notice's entry sp with notice's
   entry ra, so it returns to raw = the entry ra), from the walk's last facts. *)
Lemma nta_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
    regsF (raw : word) mF mdF,
  @nt_ctx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
    mF mdF k ->
  nt_KA W memc mF (nt_Zs regs Bw n) ->
  tw_at TMAP_A (aview segs (w_H W) mF) Bw' ->
  aregs_preserved regs regsF -> raw = YK11.getr regs 1 ->
  @transport_notice_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n Bw Bw' W
    (mkCfg (@YK11.mkst fx regsF raw mF (YK11.seg_rom segs)) mdF).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB regsF raw mF mdF HC HJF
    [KA GA] HtwF HP Hraw.
  destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
    as (HAR & Hwin & Hsp & Hce & _ & _ & _ & _ & _ & _).
  pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJ Hra Hra4 Hgp Htp H11 Hsp16 Hlo
    Hhi HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : NOTICE_STK = 8240) by reflexivity.
  assert (GLOW : forall a, inG TG.G_HARNESS a -> a < kLowMemEnd).
  { intros a Ha. exact (proj2 (transport_segs_low a (proj1 (HGX a Ha)))). }
  unfold transport_notice_post, transport_cg_post.
  exists lyc, Sc, regsF, mF, mdF, 0.
  split; [rewrite Hraw; reflexivity|].
  split; [unfold NOTICE_EV; lia|].
  split; [rewrite Z.add_0_r; exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc mF
      (spZ regs - NOTICE_STK) (spZ regs) (notice_wr Bw n) (nt_Zs regs Bw n) HAR).
    - apply dk_kept_refl_g. exact Hwin.
    - exact KA.
    - exact GA.
    - intros a [Hw | Hw] Hc; [exact Hw|]. exfalso. pose proof (GLOW a (nt_wr_G _ _ _ Hw)). unfold kLowMemEnd in *. lia.
    - intros b m i Hb Hi [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
    - intros a [Hw | Hw] Hi HnG _ _.
      + pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
      + exact (HnG (nt_wr_G _ _ _ Hw)).
    - intros cid pos a Hin Hr [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  exact HtwF.
Qed.

Lemma nt_path_acked : @nt_path fx rc B MT TC.N_ACKED NT_ACKED.
Proof.
unfold nt_path.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E ms md
  HC Ek HS HEI HElo HEd SHOK HJ KA.
destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
  as (HAR & Hwin & Hsp & Hce & Hm16 & Hp4096 & Hp47 & Hp8 & Hoffp & Hrd).
pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJ0 Hra Hra4 Hgp Htp H11 Hsp16
  Hlo Hhi HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : NOTICE_STK = 8240) by reflexivity.
destruct (nt_m_acked timg_A Fr Bw n Bw' Ek Hm) as [Hmax HMa].
(* the valuation at the arm *)
pose proof (nt_E_atom regs NB Bw 8%nat ltac:(lia)) as E40q. cbn [Nat.add nth nt_vals] in E40q.
assert (E40 : ew E 40 = Z_to_bv 64 (TW.u_at Bw TW.A_GOT_acked 4)) by (rewrite (HElo 40%nat ltac:(lia)); exact E40q).
assert (U38 : bv_unsigned (ew E (A_OBJ 38)) = TA_GOT + 216)
  by (rewrite (HEI (A_OBJ 38) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); vm_compute; reflexivity).
assert (U38n : bv_unsigned (ew E 279%nat) = TA_GOT + 216) by exact U38.
pose proof (nt_KA_mono W memc (ms_mem ms) (nt_Wn regs) (nt_Zs regs Bw n)
  (fun a Ha => nt_Wn_Zs regs Bw n a Ha) KA) as KA0.
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (HElo 2%nat ltac:(lia)); rewrite (nt_E_reg regs NB Bw 2%nat 2%bv eq_refl); reflexivity).
pose proof (nt_E_atom regs NB Bw 0%nat ltac:(lia)) as E32q. cbn [Nat.add nth nt_vals] in E32q.
assert (E32e : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (HElo 32%nat ltac:(lia)); exact E32q).
assert (U11e : bv_unsigned (ew E 11) = p).
{ rewrite (HElo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11%nat 11%bv eq_refl), H11.
  apply unsigned_lit_small. lia. }
assert (HtwM : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) Bw).
{ apply (nt_tw_keep W memc (ms_mem ms) Bw (nt_Wn regs) Htw KA).
  intros x Hx Hz. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia. }
(* GOT.acked's region added *)
pose proof (nt_add E _ _ (nt_reg_fld 38 40) HS ltac:(vm_compute; reflexivity)) as HSq. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq.
specialize (HSq ltac:(cbn [ms_mem restrict]; apply (nt_fld_ok W _ E Bw 38%nat 40%nat 216);
  [exact U38 | lia | unfold TW.SZ_GOT; lia | exact E40 | exact HtwM])).
specialize (HSq ltac:(cbn [all_disjoint]; split; [|exact I];
  unfold extent_disjoint, nt_reg_fld, nt_reg_frame;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold TA_GOT in U38; lia)).
rename HSq into HS.
pose proof (nt_facts_set E _ _ (nt_facts_f 279%nat (TA_GOT + 216)) HS
  ltac:(apply (nt_facts_f_ok E (spZ regs) p 279%nat (TA_GOT + 216));
        first [exact Usp | exact U11e | exact E32e | exact U38n | lia])) as HSq.
clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
(* run 1, +0xa0 .. +0xa8: the load of GOT.acked and the increment; the store needs its auipc pinned *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ nt_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (md1 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md1; clear mt end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
  assert (KA1 : nt_KA W memc (ms_mem mz) (nt_Zs regs Bw n)) by
    (apply (nt_KA_run _ _ W memc _ _ _ KA0 HFr HG);
     intros b wlo whi x Hin Hx; cbv beta;
     nt_win Hin Hx ltac:(rewrite ?Usp, ?U38n in Hx;
       first [ left; unfold nt_Wn; lia
             | right; unfold notice_wr, twa_fld, TW.A_GOT_acked, TW.OFF_GOT;
               right; left; split; [exact Ek | unfold TA_GOT in *; lia] ])) end.
clear HF HFr HG.
nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (TA_GOT + 216 + 608)) Q10
  ltac:(cbn [sv_denot]; rewrite (HEI 475%nat ltac:(unfold A_TEXT, A_LIM; lia)); f_equal; vm_compute; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ =>
  assert (QD : sv_denot EF (SOff (A_OBJ 38) 608) = Z_to_bv 64 (TA_GOT + 216 + 608)) by
    (cbn [sv_denot]; rewrite (HEI (A_OBJ 38) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
     f_equal; vm_compute; reflexivity);
  pose proof (nt_pin EF _ _ (Z_to_bv 5 10) (SOff (A_OBJ 38) 608) HS (eq_trans Q10 (eq_sym QD))
    ltac:(vm_compute; reflexivity)) as HSq end.
clear HS Q10. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
(* run 2, +0xac .. +0xbc: the store of GOT.acked + 1, a0 = p, the frame given back, the tail jump *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ nt_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (mdF := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdF; clear mt end.
lazymatch type of HS with context [restrict _ ?mz] => rename mz into msF end.
assert (KAF : nt_KA W memc (ms_mem msF) (nt_Zs regs Bw n)).
{ apply (nt_KA_run _ _ W memc _ _ _ KA1 HFr HG).
  intros b wlo whi x Hin Hx. cbv beta.
  nt_win Hin Hx ltac:(rewrite ?Usp, ?U38n in Hx;
    first [ left; unfold nt_Wn; lia
          | right; unfold notice_wr, twa_fld, TW.A_GOT_acked, TW.OFF_GOT;
            right; left; split; [exact Ek | unfold TA_GOT in *; lia] ]). }
clear HF HFr HG KA1.
(* the field's new value, read back from its region *)
assert (HVAL : val_mem segs (mrestrict (w_H W) (ms_mem msF)) (TA_GOT + 216 + 0) 4
  (bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 40 0)) (SLit 1))) mod 2 ^ (8 * Z.of_N 4))).
{ eapply (field_of_region_any E _ 279%nat (TA_GOT + 216) _ 0 4 0 4 0 4%N
    (SAlu ALU_ADD (SExt true 32 (SOff 40 0)) (SLit 1))).
  - exact (st_ok_region_nth E _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)).
  - exact U38n.
  - cbn [In]. left. reflexivity.
  - lia. }
assert (HDEN : sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 40 0)) (SLit 1))
  = Z_to_bv 64 (TW.GOT_acked Bw + 1)).
{ change (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 40 0)) (SLit 1)))
    with (alu64 ALU_ADD (sv_denot E (SExt true 32 (SOff 40 0))) (Z_to_bv 64 1)).
  pose proof (TWL.u_at_range Bw TW.A_GOT_acked 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  rewrite (nt_sext32 E 40 _ E40 R).
  rewrite nt_add_lit. reflexivity. }
rewrite HDEN in HVAL. change (8 * Z.of_N 4) with 32 in HVAL. rewrite nta_mod_64_32 in HVAL.
(* the world after the store: GOT.acked + 1 *)
assert (HtwF : tw_at TMAP_A (aview segs (w_H W) (ms_mem msF)) (TW.set_GOT_acked Bw (TW.GOT_acked Bw + 1))).
{ unfold TW.set_GOT_acked, TW.A_GOT_acked.
  apply (tw_write TMAP_A (aview segs (w_H W) memc) _ Bw TW.OFF_GOT TA_GOT TW.SZ_GOT 216 4
    (TW.GOT_acked Bw + 1) TMAP_A_ok Htw TMAP_A_GOT ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)).
  - intros j Hj. unfold aview.
    replace (TA_GOT + 216 + Z.of_nat j) with (TA_GOT + 216 + 0 + Z.of_nat j) by lia.
    rewrite (HVAL j Hj). cbn [option_map]. f_equal.
    rewrite AF0x.unsigned_lit_small8
      by (match goal with |- 0 <= YO0f.le_byte ?v ?m ?jj < _ => pose proof (nta_le_byte_small v m jj) end; lia).
    apply nta_le_byte_mod32.
  - intros x Hx Hout. pose proof KAF as [KAv _]. apply KAv.
    + pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. lia.
    + intros [Hz | Hz].
      * pose proof (TMAP_A_hull x Hx) as Hh. unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia.
      * pose proof (nta_wr_acked Bw n x Ek Hz) as Hr. lia. }
(* the state at check_inflight_acked's entry: notice's entry sp, ra, gp, tp and callee-saved registers, a0 = p *)
pmkst HS.
nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RT1
  ltac:(cbn [sv_denot]; rewrite (HElo 1%nat ltac:(lia)), (nt_E_reg regs NB Bw 1 1%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
nt_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) RT2
  ltac:(cbn [sv_denot]; rewrite (HElo 2%nat ltac:(lia)), (nt_E_reg regs NB Bw 2 (Z_to_bv 5 2) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
nt_reg HS (3%bv : bv 5) (YK11.getr regs 3) RT3
  ltac:(cbn [sv_denot]; rewrite (HElo 3%nat ltac:(lia)), (nt_E_reg regs NB Bw 3 3%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
nt_reg HS (4%bv : bv 5) (YK11.getr regs 4) RT4
  ltac:(cbn [sv_denot]; rewrite (HElo 4%nat ltac:(lia)), (nt_E_reg regs NB Bw 4 4%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 p) RT10
  ltac:(cbn [sv_denot]; rewrite (HElo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11 11%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact H11).
assert (HPT : aregs_preserved regs (ms_regs msF)).
{ apply (aregs_preserved_of_st_ok segs (w_H W) E _ msF regs (nt_vals NB Bw) HS).
  - apply nt_agree; [intros j Hj; apply HElo; lia | exact HEd].
  - vm_compute. reflexivity. }
assert (Hsp1 : spZ (ms_regs msF) = spZ regs) by exact (f_equal bv_unsigned RT2).
assert (Hsp2 : bv_unsigned (YK11.getr (ms_regs msF) (Z_to_bv 5 2)) = spZ regs) by exact (f_equal bv_unsigned RT2).
(* the notice's bytes, their shadow and their visibility at the jump *)
destruct Hrd as (Hvis & HRA0 & _ & Ham & _ & _).
assert (HNBT : garr8 segs (mrestrict (w_H W) (ms_mem msF)) p (map DSpec.bz NB)).
{ apply (nt_garr8_keep W memc (ms_mem msF) (nt_Zs regs Bw n) p _ KAF HNB).
  rewrite length_map, HNBL. intros a Ha. split; [lia|]. intros [Hz | Hz].
  - unfold decode_off_win in Hoffp. destruct Hoffp; lia.
  - destruct (HAP a Hz) as [Hn _]. apply Hn. unfold NTC_SIZE. lia. }
assert (HRAT : range_addressable (aview segs (w_H W) (ms_mem msF)) SHADOW_OFF p 72).
{ apply (nt_ra_kept W memc (ms_mem msF) p 72 (nt_Zs regs Bw n) HRA0 KAF).
  intros x Hx. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D1.
  assert (D2 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  unfold SHADOW_OFF. split; [lia|]. intros Hz.
  destruct (nt_Zs_far regs Bw n _ Hce Hz) as [Hf | Hf]; unfold TA_M, TA_GOT in Hf; lia. }
assert (HAPP : forall i, 0 <= i < 72 -> NtaAC.app_mem (p + i)).
{ intros i Hi. unfold amem_range in Ham. unfold NtaAC.app_mem, NtaAC.LOWMEM_END, NtaAC.HIGHMEM_BEG, NtaAC.APPMEM_END.
  destruct Ham as [Ham | Ham]; [left | right]; lia. }
assert (HVP : forall a, p <= a < p + 72 -> w_H W (Z_to_bv 64 a) = false)
  by (intros a Ha; exact (nta_vis_of_view W memc a (Hvis a Ha))).
(* the tail jump: check_inflight_acked's statement through the leaf bridge, lifted into the G journal *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (?mk ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (mk rg (Z_to_bv 64 NtaLIAc.CHECK_INFLIGHT_ACKED) mm rom) mdx) Q) end.
eapply SRr_mono.
{ eapply (@gx_call_leaf fx rc tfib_sink_head segs B TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
    (ms_mem msF) mdF k _ _ _ HJ).
  intros memS HJS.
  apply (@NtaLB.decode_leafb_journal fx rc tfib_sink_head B LAWS W (ms_regs msF) (ms_mem msF) STK sp0 FP ly S W0
    memS md0 own lyc Sc mdF k (spZ regs - sp0) NtaLIAc.CHECK_INFLIGHT_ACKED None []
    (fun _ => Bw' = TW.set_GOT_acked Bw (TW.GOT_acked Bw + 1)) HJS).
  - rewrite Hsp1. lia.
  - replace (spZ regs - sp0) with (spZ regs - 16 - sp0 + 1 * 16) by lia. rewrite Z_mod_plus_full. exact Hm16.
  - lia.
  - unfold ESTACK. lia.
  - exact (eq_ind_r YK0s.ret_ok Hra RT1).
  - exact (eq_trans RT3 Hgp).
  - exact (eq_trans RT4 Htp).
  - intros a Ha. inversion Ha.
  - intros HPRE.
    pose proof (HACK fx) as LF.
    unfold transport_leaf_at, NtaLIA.transport_check_inflight_acked_cg in LF.
    specialize (LF lyc Sc W (ms_regs msF) (ms_mem msF) mdF p (spZ regs - NOTICE_STK) n
      (TW.set_GOT_acked Bw (TW.GOT_acked Bw + 1)) Bw' HPRE RT10).
    cbv zeta in LF. unfold NtaKA.off_stk in LF. rewrite Hsp2 in LF.
    unfold decode_off_win in Hoffp.
    apply LF; clear LF.
    + (* 0 < p *) lia.
    + exact Hp8.
    + rewrite <- HK68. pose proof (TWL.u_at_range NB 68 2) as R. change (8 * Z.of_nat 2) with 16 in R. exact R.
    + exact (NtaLB.decode_leafb_bytes_le W (ms_mem msF) (p + 64) 4 (TI.n_counter n) (TW.u_at NB 64 4)
        (nta_val _ p NB 64 4 HNBT HNBL ltac:(lia) ltac:(lia)) ltac:(rewrite HK64; reflexivity)
        ltac:(lia) ltac:(lia)).
    + exact (NtaLB.decode_leafb_bytes_le W (ms_mem msF) (p + 68) 2 (TI.n_retry n) (TW.u_at NB 68 2)
        (nta_val _ p NB 68 2 HNBT HNBL ltac:(lia) ltac:(lia)) ltac:(rewrite HK68; reflexivity)
        ltac:(lia) ltac:(lia)).
    + exact (nta_tw_csw W (ms_mem msF) _ HtwF).
    + exact HMa.
    + exact (@NtaLB.decode_leafb_stk_journal rc tfib_sink_head B STK sp0 FP ly S W0 memS md0 own lyc Sc W
        (ms_mem msF) mdF k (spZ regs - NOTICE_STK) (spZ regs) HJS ltac:(lia) ltac:(lia)).
    + unfold NtaLIAc.CHECK_INFLIGHT_ACKED_FRAME. lia.
    + left. unfold NtaLIAc.CHECK_INFLIGHT_ACKED_FRAME, TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
    + exact (NtaLB.decode_leafb_asan_cells B HCELLS lyc Sc W (ms_mem msF) mdF (proj1 HPRE)).
    + apply NtaLB.decode_leafb_app_stack. unfold NtaLIAc.CHECK_INFLIGHT_ACKED_FRAME. lia.
    + apply NtaLB.decode_leafb_app_stack. lia.
    + left. unfold NtaLIAc.CHECK_INFLIGHT_ACKED_FRAME, NtaAC.GOT_CELL_K. lia.
    + left. unfold NtaLIAc.CHECK_INFLIGHT_ACKED_FRAME, NtaAC.CELL_K. lia.
    + unfold NtaLIAc.CHECK_INFLIGHT_ACKED_FRAME. lia.
    + apply (NtaLB.decode_leafb_addressable W (ms_mem msF) (p + 64) 4);
        [intros x Hx; apply HRAT; lia | lia | lia | unfold NtaAC.APPMEM_END; lia |].
      intros i Hi. replace (p + 64 + i) with (p + (64 + i)) by lia. apply HAPP. lia.
    + unfold NtaLIAc.CHECK_INFLIGHT_ACKED_FRAME. lia.
    + apply (NtaLB.decode_leafb_addressable W (ms_mem msF) (p + 68) 2);
        [intros x Hx; apply HRAT; lia | lia | lia | unfold NtaAC.APPMEM_END; lia |].
      intros i Hi. replace (p + 68 + i) with (p + (68 + i)) by lia. apply HAPP. lia.
    + exact (@NtaLB.decode_leafb_rng_journal rc tfib_sink_head B STK sp0 FP ly S W0 memS md0 own lyc Sc W
        (ms_mem msF) mdF k (spZ regs - NtaLIAc.CHECK_INFLIGHT_ACKED_FRAME) NtaLIAc.CHECK_INFLIGHT_ACKED_FRAME HJS
        ltac:(unfold NtaLIAc.CHECK_INFLIGHT_ACKED_FRAME; lia) ltac:(lia)).
    + rewrite NtaLIAc.check_inflight_acked_got_acked_at.
      apply nta_rng_hull; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
    + rewrite NtaLIAc.check_inflight_acked_ow_acked_at.
      apply nta_rng_hull; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
    + exact (proj1 (NtaLB.decode_leafb_rng_cells W)).
    + exact (proj2 (NtaLB.decode_leafb_rng_cells W)).
    + pose proof (NtaLB.decode_leafb_rng_shadow W (ms_mem msF) (p + 64) 1
        ltac:(intros x Hx; apply HRAT; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as R.
      replace (p + 64 + 1 - 1) with (p + 64) in R by lia. rewrite Z.sub_diag, Z.add_0_l in R. exact R.
    + apply NtaLB.decode_leafb_rng; [lia | lia |]. intros a Ha. apply HVP. lia.
    + rewrite NtaLIAc.check_inflight_acked_ow_counter_at.
      apply nta_rng_hull; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
    + pose proof (NtaLB.decode_leafb_rng_shadow W (ms_mem msF) (p + 68) 1
        ltac:(intros x Hx; apply HRAT; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as R.
      replace (p + 68 + 1 - 1) with (p + 68) in R by lia. rewrite Z.sub_diag, Z.add_0_l in R. exact R.
    + apply NtaLB.decode_leafb_rng; [lia | lia |]. intros a Ha. apply HVP. lia.
    + rewrite NtaLIAc.check_inflight_acked_ow_retry_at.
      apply nta_rng_hull; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia. }
(* the leaf's return to notice's caller *)
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & HK2 & HG2 & HX).
assert (Htw2 : tw_at TMAP_A (aview segs (w_H W) mem2) Bw').
{ rewrite HX. apply (nta_tw_leaf W (ms_mem msF) mem2 _ (spZ (ms_regs msF)) HtwF); [|exact HK2].
  rewrite Hsp1. unfold TG.G_HARNESS_HI, ESTACK. lia. }
exact (nta_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB regs2 _ mem2 md2
  HC HJ2 (nta_KA_leaf W memc (ms_mem msF) mem2 regs Bw n _ KAF Hsp1 HK2 HG2) Htw2
  (aregs_preserved_trans regs (ms_regs msF) regs2 HPT HP2) RT1).
Qed.
End acked.

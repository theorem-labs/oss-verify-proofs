(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 678 of its 962 lines of code are new or changed and 855 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcHead.v, with its module paths, module names and numbers changed; 528 of its 590 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/notice_seg_base.v; 308 of its 415 lines of code are new or changed and 483 lines of the source are left out. *)
(* notice_seg_acked: the N_ACKED arm of notice's walk on fuzz_transport.asan-ubsan (lib/B/Prog/notice_cgW.v),
   from the jump `jr a0` (0x83474) with a0 = 0x834d0:
     0x834d0 - 0x834d8  a0 = the auipc value 0x5e5510; a3 = GOT.acked (the 4-byte signed load at GOT + 216, read
                        from the region of that field, its value the world's u32), a2 = a3 + 1 (addiw);
     0x834dc            `blt a2, a3` to the UBSan trap 0x83610: taken exactly at INT_MAX (nt_ovf_br), which notice_m
                        rules out (its int_inc is None there);
     0x834e0            the store of a2 at a0 - 1176 = GOT + 216 (a0 pinned to that field's object + 1176);
     0x834e4 - 0x834f0  a0 = p, ra loaded back, sp = sp + 16, the tail jump to check_inflight_acked (0x85358).
   check_inflight_acked is a leaf: its statement (check_inflight_acked_cg.v, read through DgnTransportBCg.v
   transport_leaf_at) is applied at the jump's state, which has notice's entry sp and ra, through TransportGCg.v
   gx_call_leaf and DgnTransportBLeafb.v decode_leafb_journal; its model call is notice_m's (nt_m_acked: at the world
   after GOT.acked++, which is then Bw'). The leaf returns to notice's caller with every byte outside its ESTACK window
   kept, so the post is the walk's (ntacked_close). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_data_cg check_state_desk_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import notice_seg_base notice_seg_lib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  DgnTransportBLeafb AsanKA check_state_wake_c check_inflight_acked_c check_inflight_acked_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module BAC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Module CSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_c.
Module LIAc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_acked_c.
Module LIA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_acked_cg.
Module LB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.DgnTransportBLeafb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* A leaf entered by a tail jump of the walk                           *)
(* ------------------------------------------------------------------ *)

(* Every byte of the harness globals' hull lies in one loaded segment of image B, so no world hides it. *)
Lemma ntacked_hull_vis : forall (W : world tfibsegs) x, TG.G_HARNESS_B_LO <= x < TG.G_HARNESS_B_HI ->
  w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x Hx. replace x with (TG.G_HARNESS_B_LO + (x - TG.G_HARNESS_B_LO)) by lia.
  apply (LB.decode_leafb_covers_visible (w_H W) TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO));
    [exact (w_Hoff W) | vm_compute; reflexivity | lia | unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia].
Qed.

(* The world relation at the view of a world is the world relation at the raw memory (the leaf's csw_view). *)
Lemma ntacked_tw_csw : forall (W : world tfibsegs) m Bw,
  tw_at TMAP_B (aview tfibsegs (w_H W) m) Bw -> tw_at TMAP_B (CSW.csw_view m) Bw.
Proof.
  intros W m Bw H. apply (tw_kept TMAP_B _ _ Bw H). intros x Hx.
  pose proof (LB.decode_leafb_mrd W m x (ntacked_hull_vis W x (TMAP_B_hull x Hx))) as E.
  unfold CSW.csw_view, aview. rewrite <- E. reflexivity.
Qed.

(* The leaf's footprint holds every range of the hull. *)
Lemma ntacked_rng_hull : forall (W : world tfibsegs) lo len,
  TG.G_HARNESS_B_LO <= lo -> lo + len <= TG.G_HARNESS_B_HI ->
  LB.LExecF.rng (LB.LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H1 H2. apply LB.decode_leafb_rng;
    [unfold TG.G_HARNESS_B_LO in H1; lia | unfold TG.G_HARNESS_B_HI in H2; lia |].
  intros a Ha. apply ntacked_hull_vis. lia.
Qed.

(* A byte the view shows is not hidden. *)
Lemma ntacked_vis_of_view : forall (W : world tfibsegs) m a,
  aview tfibsegs (w_H W) m a <> None -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W m a H. destruct (aview tfibsegs (w_H W) m a) as [v|] eqn:E;
    [exact (LB.decode_leafb_aview_vis W m a v E) | exfalso; exact (H eq_refl)].
Qed.

(* w bytes of the notice at p + k, read from its garr8 array: u_at NB k w. *)
Lemma ntacked_val : forall (mm : word -> option byte) p (NB : list byte) k (w : nat),
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
Lemma ntacked_KA_leaf : forall (W : world tfibsegs) memc (mT m2 : word -> option byte) regs Bw n spT,
  nt_KA W memc mT (nt_Zs regs Bw n) -> spT = spZ regs ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spT - ESTACK <= a < spT) -> ~ LB.LCK.in_wr [] a ->
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
Lemma ntacked_tw_leaf : forall (W : world tfibsegs) (mT m2 : word -> option byte) Bw spT,
  tw_at TMAP_B (aview tfibsegs (w_H W) mT) Bw -> TG.G_HARNESS_B_HI <= spT - ESTACK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spT - ESTACK <= a < spT) -> ~ LB.LCK.in_wr [] a ->
     aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) mT a) ->
  tw_at TMAP_B (aview tfibsegs (w_H W) m2) Bw.
Proof.
  intros W mT m2 Bw spT H Hs Hk. apply (tw_kept TMAP_B _ _ Bw H). intros x Hx.
  pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in *.
  apply Hk; [lia | lia | intros Hw; inversion Hw].
Qed.

Section acked. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The post at a leaf's return to notice's caller (a tail jump: the leaf ran from notice's entry sp with notice's
   entry ra, so it returns to raw = the entry ra), from the walk's last facts. *)
Lemma ntacked_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
    regsF (raw : word) mF mdF,
  @nt_ctx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
    mF mdF k ->
  nt_KA W memc mF (nt_Zs regs Bw n) ->
  tw_at TMAP_B (aview segs (w_H W) mF) Bw' ->
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
  assert (GLOW : forall a, inG TG.G_HARNESS_B a -> a < kLowMemEnd).
  { intros a Ha. exact (proj2 (transportb_segs_low a (proj1 (HGX a Ha)))). }
  unfold transport_notice_post, transport_cg_post.
  exists lyc, Sc, regsF, mF, mdF, 0.
  split; [rewrite Hraw; reflexivity|].
  split; [unfold NOTICE_EV; lia|].
  split; [rewrite Z.add_0_r; exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc mF
      (spZ regs - NOTICE_STK) (spZ regs) (notice_wr Bw n) (nt_Zs regs Bw n) HAR).
    - apply dk_kept_refl_g. exact Hwin.
    - exact KA.
    - exact GA.
    - intros a [Hw | Hw] Hc; [exact Hw|]. exfalso. pose proof (GLOW a (nt_wr_G _ _ _ Hw)). unfold kLowMemEnd in *. lia.
    - intros b m i Hb Hi [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
    - intros a [Hw | Hw] Hi HnG _ _.
      + pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
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

Lemma nt_acked : @nt_path fx rc B MT TC.N_ACKED NT_ACKED.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E ms md
  HC Ek HS HEI Elo Ed SHOK HJ KA0.
destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
  as (HAR & Hwin & Hsp & Hce & Hm16 & Hp4096 & Hp47 & Hp8 & Hoffp & Hrd).
pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJc Hra Hra4 Hgp Htp H11 Hsp16 Hlo Hhi
    HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : NOTICE_STK = 8240) by reflexivity.
destruct (nt_m_acked timg_B Fr Bw n Bw' Ek Hm) as [Hmax HMa].
destruct nt_cvals as (V1 & V95 & VN & V36 & V13 & V37 & V38 & V39 & V40 & V73 & V72 & V74 & V75 & V77 & VB).
(* the atoms the arm reads *)
assert (E40 : ew E 40 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_GOT + 216) 4)).
{ rewrite (Elo 40%nat ltac:(lia)). exact (nt_E_atom regs NB Bw 8 ltac:(lia)). }
pose proof (TWL.u_at_range Bw (TW.OFF_GOT + 216) 4) as R40. change (8 * Z.of_nat 4) with 32 in R40.
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (Elo 2%nat ltac:(lia)), (nt_E_reg regs NB Bw 2 2%bv eq_refl); reflexivity).
assert (U39 : bv_unsigned (ew E (A_OBJ 39)) = TB_GOT + 216).
{ rewrite (HEI (A_OBJ 39) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V39. reflexivity. }
assert (U39n : bv_unsigned (ew E 280) = TB_GOT + 216) by exact U39.
assert (U75 : bv_unsigned (ew E (A_HI 75)) = VAL (A_HI 75))
  by (apply HEI; unfold A_HI, A_OBJ, A_TEXT, A_LIM; lia).
assert (U75n : bv_unsigned (ew E 475) = VAL (A_HI 75)) by exact U75.
(* the world at the arm's entry, and the field's region *)
pose proof (nt_tw_Wn W memc (ms_mem ms) regs Bw ltac:(unfold TG.G_HARNESS_B_HI; lia) Htw KA0) as Htw0.
pose proof (nt_add E _ _ (nt_reg_fld 39 40) HS ltac:(vm_compute; reflexivity)) as HS2. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts nt_ss_jr] in HS2.
specialize (HS2 ltac:(cbn [ms_mem restrict];
  exact (nt_fld_ok W (ms_mem ms) E Bw 39 40 216 U39 ltac:(lia) ltac:(unfold TW.SZ_GOT; lia) E40 Htw0))).
specialize (HS2 ltac:(cbn [all_disjoint]; split; [|exact I];
  unfold extent_disjoint, nt_reg_fld, nt_reg_frame;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Usp, U39; unfold TB_GOT; lia)).
rename HS2 into HS.
assert (U11 : bv_unsigned (ew E 11) = p).
{ rewrite (Elo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11 11%bv eq_refl), H11. apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (Elo 32%nat ltac:(lia)); exact (nt_E_atom regs NB Bw 0 ltac:(lia))).
pose proof (nt_facts_set E _ _ (nt_facts_g 39 (TB_GOT + 216)) HS
  (nt_facts_g_ok E (spZ regs) p 39 (TB_GOT + 216) Usp U11 E32 U39 ltac:(lia) Hsp16 ltac:(lia) Hp8
    ltac:(unfold TB_GOT; reflexivity))) as HS2.
clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2. rename HS2 into HS.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* run 1: the jump, the load of GOT.acked, the increment, to `blt` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U39, ?U39n in Ha.
    apply nt_inG_GOT. lia. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
  left. split; [unfold awr_byte; left; lia | lia]. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
assert (KA1 : nt_KA W memc (ms_mem ms1) (nt_Zs regs Bw n)).
{ apply (nt_KA_run _ _ W memc _ _ _ (nt_KA_mono W memc _ _ _ (nt_Wn_Zs regs Bw n) KA0) HFr HG).
  intros b wlo whi x Hin Hx. cbv beta.
  nt_win Hin Hx ltac:(rewrite ?Usp, ?U39, ?U39n in Hx; first
    [ left; unfold nt_Wn; lia
    | right; unfold notice_wr; right; left; split; [exact Ek|];
      unfold twb_fld, TW.A_GOT_acked; lia ]). }
clear HF HFr HG.
(* the runs of this arm make no fresh atom (sh_j = 0): the valuation stays E *)
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* the trap: GOT.acked = INT_MAX *)
  rewrite (nt_ovf_br E 40 _ E40 R40) in Hc. apply Z.eqb_eq in Hc. exfalso. apply Hmax. exact Hc.
- rewrite (nt_ovf_br E 40 _ E40 R40) in Hc. apply Z.eqb_neq in Hc.
  (* a0 pinned to the field's object + 1176 *)
  nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (VAL (A_HI 75))) Q10
    ltac:(cbn [sv_denot]; rewrite ?U75, ?U75n, Z.add_0_r; reflexivity).
  pose proof (nt_pin E _ _ (Z_to_bv 5 10) (SOff (A_OBJ 39) 1176) HS
    ltac:(cbn [ms_regs restrict]; rewrite Q10; cbn [sv_denot]; rewrite U39, V75; f_equal; lia)
    ltac:(vm_compute; reflexivity)) as HS3.
  clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_cond] in HS3. rename HS3 into HS.
  (* run 2: the store, a0 = p, the frame given back, to the tail jump *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_cons_g.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U39, ?U39n in Ha.
      apply nt_inG_GOT. lia. }
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
    left. split; [unfold awr_byte; left; lia | lia]. }
  set (mdF := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody mdF. clear mat.
  lazymatch type of HS with context [restrict _ ?m] => rename m into msF end.
  assert (KAF : nt_KA W memc (ms_mem msF) (nt_Zs regs Bw n)).
  { apply (nt_KA_run _ _ W memc _ _ _ KA1 HFr HG).
    intros b wlo whi x Hin Hx. cbv beta.
    nt_win Hin Hx ltac:(rewrite ?Usp, ?U39, ?U39n in Hx; first
      [ left; unfold nt_Wn; lia
      | right; unfold notice_wr; right; left; split; [exact Ek|];
        unfold twb_fld, TW.A_GOT_acked; lia ]). }
  clear HF HFr HG.
  (* the field's 4 bytes at the jump, and the world after GOT.acked++ *)
  pose proof (st_ok_region_nth E _ (restrict (w_H W) msF) 0 _ HS eq_refl) as RGF.
  cbn [ms_mem restrict] in RGF.
  destruct RGF as (_ & _ & _ & HCH). cbn [YP09.r_base YP09.r_chunks base_val] in HCH.
  apply Forall_cons_iff in HCH as [HCH _].
  rewrite ?U39, ?U39n in HCH.
  assert (HV4 : forall j, (j < 4)%nat ->
    aview segs (w_H W) (ms_mem msF) (TB_GOT + 216 + Z.of_nat j) =
    Some (YO0f.le_byte (TW.GOT_acked Bw + 1) 4 j)).
  { intros j Hj. pose proof (nt_chunk_aview W (ms_mem msF) E (TB_GOT + 216) 0 4 _ (Z.of_nat j) HCH ltac:(lia)) as X.
    rewrite Z.add_0_r in X. rewrite X. f_equal.
    apply (nt_inc_bytes E 40 _ j); [exact E40 | exact R40 | exact Hc | exact Hj]. }
  assert (HtwF : tw_at TMAP_B (aview segs (w_H W) (ms_mem msF)) (TW.set_GOT_acked Bw (TW.GOT_acked Bw + 1))).
  { unfold TW.set_GOT_acked, TW.A_GOT_acked.
    apply (nt_tw_set4 W memc (ms_mem msF) Bw TW.OFF_GOT TB_GOT TW.SZ_GOT 216 (TW.GOT_acked Bw + 1) Htw TMAP_B_GOT);
      [lia | unfold TW.SZ_GOT; lia | exact HV4 |].
    intros x Hx Hn. pose proof KAF as [KAx _]. apply KAx.
    + pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. lia.
    + unfold nt_Zs. intros [Hz | Hz].
      * pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_HI in Hh. lia.
      * apply Hn. unfold notice_wr in Hz.
        unfold TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in Hz, Ek.
        destruct Hz as [(E' & _) | [(_ & Hz) | [(E' & _) | [(E' & _) | [(E' & _) | (E' & _)]]]]]; try lia.
        unfold twb_fld, TW.A_GOT_acked in Hz. lia. }
  (* the state at check_inflight_acked's entry: notice's entry sp, ra, gp, tp and callee-saved registers, a0 = p *)
  pmkst HS.
  nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RT1
    ltac:(cbn [sv_denot]; rewrite (Elo 1%nat ltac:(lia)), (nt_E_reg regs NB Bw 1 1%bv eq_refl), Z.add_0_r,
            Z_to_bv_bv_unsigned; reflexivity).
  nt_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) RT2
    ltac:(cbn [sv_denot]; rewrite (Elo 2%nat ltac:(lia)), (nt_E_reg regs NB Bw 2 (Z_to_bv 5 2) eq_refl), Z.add_0_r,
            Z_to_bv_bv_unsigned; reflexivity).
  nt_reg HS (3%bv : bv 5) (YK11.getr regs 3) RT3
    ltac:(cbn [sv_denot]; rewrite (Elo 3%nat ltac:(lia)), (nt_E_reg regs NB Bw 3 3%bv eq_refl), Z.add_0_r,
            Z_to_bv_bv_unsigned; reflexivity).
  nt_reg HS (4%bv : bv 5) (YK11.getr regs 4) RT4
    ltac:(cbn [sv_denot]; rewrite (Elo 4%nat ltac:(lia)), (nt_E_reg regs NB Bw 4 4%bv eq_refl), Z.add_0_r,
            Z_to_bv_bv_unsigned; reflexivity).
  nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 p) RT10
    ltac:(cbn [sv_denot]; rewrite (Elo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11 11%bv eq_refl), Z.add_0_r,
            Z_to_bv_bv_unsigned; exact H11).
  assert (HPT : aregs_preserved regs (ms_regs msF)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E _ msF regs (nt_vals NB Bw) HS).
    - split; [intros j Hj; rewrite (Elo j ltac:(lia)); unfold nt_E; apply Eimg_low; unfold A_TEXT; lia
             | rewrite Ed; reflexivity].
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
    destruct (nt_Zs_far regs Bw n _ Hce Hz) as [Hf | Hf]; unfold TB_M, TB_GOT in Hf; lia. }
  assert (HAPP : forall i, 0 <= i < 72 -> BAC.app_mem (p + i)).
  { intros i Hi. unfold amem_range in Ham. unfold BAC.app_mem, BAC.LOWMEM_END, BAC.HIGHMEM_BEG, BAC.APPMEM_END. lia. }
  assert (HVP : forall a, p <= a < p + 72 -> w_H W (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (ntacked_vis_of_view W memc a (Hvis a Ha))).
  (* the tail jump: check_inflight_acked's statement through the leaf bridge, lifted into the G journal *)
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (?mk ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (mk rg (Z_to_bv 64 LIAc.CHECK_INFLIGHT_ACKED) mm rom) mdx) Q) end.
  eapply SRr_mono.
  { eapply (@gx_call_leaf fx rc tfib_sink_head segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
      (ms_mem msF) mdF k _ _ _ HJ).
    intros memS HJS.
    apply (@LB.decode_leafb_journal fx rc tfib_sink_head B LAWS W (ms_regs msF) (ms_mem msF) STK sp0 FP ly S W0 memS
      md0 own lyc Sc mdF k (spZ regs - sp0) LIAc.CHECK_INFLIGHT_ACKED None []
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
      unfold transport_leaf_at, LIA.transport_check_inflight_acked_cg in LF.
      specialize (LF lyc Sc W (ms_regs msF) (ms_mem msF) mdF p (spZ regs - NOTICE_STK) n
        (TW.set_GOT_acked Bw (TW.GOT_acked Bw + 1)) Bw' HPRE RT10).
      cbv zeta in LF. unfold AKA.off_stk in LF. rewrite Hsp2 in LF.
      unfold decode_off_win in Hoffp.
      apply LF; clear LF.
      + (* 0 < p *) lia.
      + exact Hp8.
      + rewrite <- HK68. pose proof (TWL.u_at_range NB 68 2) as R. change (8 * Z.of_nat 2) with 16 in R. exact R.
      + exact (LB.decode_leafb_bytes_le W (ms_mem msF) (p + 64) 4 (TI.n_counter n) (TW.u_at NB 64 4)
          (ntacked_val _ p NB 64 4 HNBT HNBL ltac:(lia) ltac:(lia)) ltac:(rewrite HK64; reflexivity)
          ltac:(lia) ltac:(lia)).
      + exact (LB.decode_leafb_bytes_le W (ms_mem msF) (p + 68) 2 (TI.n_retry n) (TW.u_at NB 68 2)
          (ntacked_val _ p NB 68 2 HNBT HNBL ltac:(lia) ltac:(lia)) ltac:(rewrite HK68; reflexivity)
          ltac:(lia) ltac:(lia)).
      + exact (ntacked_tw_csw W (ms_mem msF) _ HtwF).
      + exact HMa.
      + exact (@LB.decode_leafb_stk_journal rc tfib_sink_head B STK sp0 FP ly S W0 memS md0 own lyc Sc W (ms_mem msF)
          mdF k (spZ regs - NOTICE_STK) (spZ regs) HJS ltac:(lia) ltac:(lia)).
      + unfold LIAc.CHECK_INFLIGHT_ACKED_FRAME. lia.
      + left. unfold LIAc.CHECK_INFLIGHT_ACKED_FRAME, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
      + exact (LB.decode_leafb_asan_cells B HCELLS lyc Sc W (ms_mem msF) mdF (proj1 HPRE)).
      + apply LB.decode_leafb_app_stack. unfold LIAc.CHECK_INFLIGHT_ACKED_FRAME. lia.
      + apply LB.decode_leafb_app_stack. lia.
      + left. unfold LIAc.CHECK_INFLIGHT_ACKED_FRAME, BAC.GOT_CELL_K. lia.
      + left. unfold LIAc.CHECK_INFLIGHT_ACKED_FRAME, BAC.CELL_K. lia.
      + unfold LIAc.CHECK_INFLIGHT_ACKED_FRAME. lia.
      + apply (LB.decode_leafb_addressable W (ms_mem msF) (p + 64) 4);
          [intros x Hx; apply HRAT; lia | lia | lia | unfold BAC.APPMEM_END; lia |].
        intros i Hi. replace (p + 64 + i) with (p + (64 + i)) by lia. apply HAPP. lia.
      + unfold LIAc.CHECK_INFLIGHT_ACKED_FRAME. lia.
      + apply (LB.decode_leafb_addressable W (ms_mem msF) (p + 68) 2);
          [intros x Hx; apply HRAT; lia | lia | lia | unfold BAC.APPMEM_END; lia |].
        intros i Hi. replace (p + 68 + i) with (p + (68 + i)) by lia. apply HAPP. lia.
      + exact (@LB.decode_leafb_rng_journal rc tfib_sink_head B STK sp0 FP ly S W0 memS md0 own lyc Sc W (ms_mem msF)
          mdF k (spZ regs - LIAc.CHECK_INFLIGHT_ACKED_FRAME) LIAc.CHECK_INFLIGHT_ACKED_FRAME HJS
          ltac:(unfold LIAc.CHECK_INFLIGHT_ACKED_FRAME; lia) ltac:(lia)).
      + rewrite LIAc.check_inflight_acked_got_acked_at.
        apply ntacked_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
      + rewrite LIAc.check_inflight_acked_ow_acked_at.
        apply ntacked_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
      + exact (proj1 (LB.decode_leafb_rng_cells W)).
      + exact (proj2 (LB.decode_leafb_rng_cells W)).
      + pose proof (LB.decode_leafb_rng_shadow W (ms_mem msF) (p + 64) 1
          ltac:(intros x Hx; apply HRAT; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as R.
        replace (p + 64 + 1 - 1) with (p + 64) in R by lia. rewrite Z.sub_diag, Z.add_0_l in R. exact R.
      + apply LB.decode_leafb_rng; [lia | lia |]. intros a Ha. apply HVP. lia.
      + rewrite LIAc.check_inflight_acked_ow_counter_at.
        apply ntacked_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
      + pose proof (LB.decode_leafb_rng_shadow W (ms_mem msF) (p + 68) 1
          ltac:(intros x Hx; apply HRAT; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as R.
        replace (p + 68 + 1 - 1) with (p + 68) in R by lia. rewrite Z.sub_diag, Z.add_0_l in R. exact R.
      + apply LB.decode_leafb_rng; [lia | lia |]. intros a Ha. apply HVP. lia.
      + rewrite LIAc.check_inflight_acked_ow_retry_at.
        apply ntacked_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia. }
  (* the leaf's return to notice's caller *)
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & HK2 & HG2 & HX).
  assert (Htw2 : tw_at TMAP_B (aview segs (w_H W) mem2) Bw').
  { rewrite HX. apply (ntacked_tw_leaf W (ms_mem msF) mem2 _ (spZ (ms_regs msF)) HtwF); [|exact HK2].
    rewrite Hsp1. unfold TG.G_HARNESS_B_HI, ESTACK. lia. }
  exact (ntacked_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB regs2 _ mem2 md2
    HC HJ2 (ntacked_KA_leaf W memc (ms_mem msF) mem2 regs Bw n _ KAF Hsp1 HK2 HG2) Htw2
    (aregs_preserved_trans regs (ms_regs msF) regs2 HPT HP2) RT1).
Qed.
End acked.

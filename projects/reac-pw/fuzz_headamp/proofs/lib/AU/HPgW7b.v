(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 692 of its 736 lines of code are new or changed and 246 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Hd.v, with its module paths and module names changed; 425 of its 454 lines of code are new or changed and 707 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/AU/HPgCaseBJ.v at 5b1aa5ec2a87; its case-entry
   and join bridges (cj_D_facts, cj_D_keep, cj_D_img, cj_J_of) restated over the cut G of lib/AU/HPgSeg.v
   (hsu_cut_G, 0x81afc, through its hsu_pod_base) in place of the case entries (hsu_cut_D): the frame's shadow at G
   (hsu_PG), the cursor cell R+0x110, the shadow of R+0x180 (hi_rz), the read-only premise aro_unowned from rom_view,
   and a join (hw7b_J_of) built from the continuation facts of lib/AU/HPgW7bBase.v hw7b_core_stmt, where the layout,
   the abstract state and the world are the cut's own; the piece lemma hsu_piece_W7b_of_core is new. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the walk piece W7b of
   LLVMFuzzerTestOneInput (0x80c40), lib/AU/HPgSeg.v's hsu_piece_W7b_stmt at segs = Img0U.rsegs, I = headamp_himg_B,
   BI = headamp_bld_B, from the cut G 0x81afc (ent_build's case 0 after the key's first part, pod.h:250) to the join
   J 0x82618 (the pod built, the call of pod_write_ent next), taken from the walk's statement over explicit facts
   HPgW7bBase.hw7b_core_stmt. Proves no function (kind: segment lemma).

   hw7b_base_facts: from the segment's start and the pod loop's base at a cut (hsu_pod_base), the journal, the bounds
     of R, F and pp, the frame's bytes present and outside the image, rom_view, and every image byte and every shadow
     byte outside F's 116 shadow bytes as at the segment's start.
   hw7b_base_img: image B's strings (hd_cstr), registered globals and 8-byte cells, and the shadow of the 8-byte cell
     R+0x180 (hi_rz), at a later state whose frame shadow is any 116-byte pattern.
   hw7b_J_of: hsu_cut_J at J from the cut G and the facts hw7b_core_stmt's continuation gives at J.
   hsu_piece_W7b_of_core: the piece from hw7b_core_stmt.

   REGISTERS AND REAL-FRAME CELLS read at G (image B, HPgSeg.hsu_cut_G): sp (x2), gp (x3), tp (x4), s0 = S (x8),
   s1 = R (x9), s3 = shadow_addr F (x19), s6 = F + 0xe0 (x22), s8 = the `v / 10` multiplier (x24), s9 = F + 0x20 (x25),
   s11 = SHADOW_OFF (x27), s2 = F + 0xa0 (x18), s10 = p (x26), t1 = what is left (x6); R+0x110 the cursor,
   R+0x118 = F + 0x218, R+0x130 = F + 0x210, R+0xe8 = -(F + 0x219), R+0x138 = pp + 0x4000, R+0x148 = pp, and every
   cell of HPgSeg.hsu_L_Dc. At J (HPgSeg.hsu_cut_J): a3 = the cursor (x13), t1 (x6), s2 = pp + 0x4000 (x18),
   s4 = F + 0x210 (x20), s7 = pp (x23), e62 at F + 0x210, and the registers and cells of hsu_L_Dc as at G. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Spa.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0q YP03.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import WrapRo.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgSteps HPgCaseBJ.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgW7bBase HPgW7bFacts HPgCaseB.
Import ListNotations.
(* the cut record's projections, with the segments implicit *)
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* a location of the cut G's list (HPgSeg.hsu_cut_G: hsu_L_Dc and four more) *)
Ltac hw7b_inG := cbv [hsu_L_Dc hsu_Rc0 hsu_Kc app]; cbn [In]; repeat (first [left; reflexivity | right]).

(* the frame's 116 shadow bytes lie above the low application range and below the high one *)
Lemma hw7b_shF_bounds : forall F, 4096 <= F -> F + 1024 <= 0x7fffff800000 ->
  0x7fff8200 <= shadow_addr F /\ shadow_addr F + 116 <= 0x7fff8000 + 2 ^ 44 - 2 ^ 20.
Proof.
  intros F H1 H2. unfold shadow_addr, SHADOW_OFF.
  pose proof (Z.div_le_mono 4096 F 8 ltac:(lia) H1) as A. change (4096 / 8) with 512 in A.
  assert (Bd : F / 8 <= 2 ^ 44 - 2 ^ 20 - 128) by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

(* the param table's eight pointers lie between "reac.headamp." and "." *)
Lemma hw7b_pptr_range : forall p, 0 <= p -> 0x20f40 <= hw7b_pptr (p mod 8) <= 0x21460.
Proof.
  intros p Hp.
  assert (Hb : forallb (fun j => (0x20f40 <=? hw7b_pptr (Z.of_nat j)) && (hw7b_pptr (Z.of_nat j) <=? 0x21460))
    (seq 0 8) = true) by (vm_compute; reflexivity).
  pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hm.
  pose proof (proj1 (forallb_forall _ _) Hb (Z.to_nat (p mod 8)) ltac:(apply in_seq; lia)) as H.
  cbv beta in H. rewrite Z2Nat.id in H by lia.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma hw7b_val_eq : forall H mem a n v v', v' = v ->
  val_mem rsegs (mrestrict H mem) a n v -> val_mem rsegs (mrestrict H mem) a n v'.
Proof. intros H mem a n v v' -> V. exact V. Qed.

(* ============================== the pod loop's base at a cut ============================== *)
Lemma hw7b_base_facts : forall cx rest sh np ps cnt es rr r ly2 S2 W2 regs2 mem2 md2,
  hsu_start_M01 rsegs B headamp_himg_B cx rest ->
  hsu_pod_base rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem2 md2 (x_k cx) /\
  getr regs2 2 = w64 (e_R (x_e cx)) /\ getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
  (* bounds *)
  alloc_ceiling + T_SEG_STK <= e_R (x_e cx) /\ e_R (x_e cx) + 0x220 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_sp0 cx mod 16 = 0 /\ e_R (x_e cx) mod 32 = 0 /\ x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK /\
  spZ (x_regs cx) = e_R (x_e cx) /\
  In (4, x_pos cx) (x_own cx) /\ e_F (x_e cx) = frame_addr ly2 4 (x_pos cx) /\
  4096 <= e_F (x_e cx) /\ e_F (x_e cx) + 1024 <= alloc_ceiling /\ e_F (x_e cx) mod 32 = 0 /\
  in_app (e_F (x_e cx)) 1024 /\
  4096 <= e_pp (x_e cx) /\ e_pp (x_e cx) + Layout.PP_SIZE <= alloc_ceiling /\
  zdisjoint (e_pp (x_e cx), Layout.PP_SIZE) (e_F (x_e cx), 1024) /\ in_app (e_pp (x_e cx)) Layout.PP_SIZE /\
  1 <= hsu_cur rsegs cx rest r /\ hsu_cur rsegs cx rest r + Z.of_nat (length r) <= 2 ^ 47 - 1 /\
  (* the frame, the read-only bytes, and what the walk kept since the segment's start *)
  (forall a, e_F (x_e cx) <= a < e_F (x_e cx) + 1024 -> apresent (w_H W2) mem2 a /\ ~ in_img rsegs a) /\
  rom_view rsegs W2 mem2 /\
  (forall a, in_img rsegs a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a) /\
  (forall s, kLowMemEnd <= s < kHighMemBeg ->
     ~ (shadow_addr (e_F (x_e cx)) <= s < shadow_addr (e_F (x_e cx)) + 116) ->
     aview rsegs (w_H W2) mem2 s = aview rsegs (w_H (x_W cx)) (x_memc cx) s).
Proof.
  intros cx rest sh np ps cnt es rr r ly2 S2 W2 regs2 mem2 md2 HST HPB.
  pose proof (AR_laws_ok rsegs B) as LAWS.
  pose proof (@asan_consts rc) as (Hceil & _).
  destruct HST as (HPRE & HL1 & Hlen & HIN).
  destruct HPRE as (HJc & Hnev & HR2 & Hgp & Htp & ES & ER32 & ERS & ESTK & Hown & EF & Hfsh0 & Hcap & Hnull
    & Haro & Hglobs & Hrz & Hstrs & Hcells & Hguard & Hrom & Hfresh).
  destruct Hfresh as (Hpp0 & Hppb & Hnpp).
  destruct HPB as (HCORE & HIN' & Hsr & Hsrr' & Hwf & Hlen' & Hps & Htie & Hsh & Hnp & Hlp & Hnp3 & Hsh7 & Hps2 & Hcnt
    & Hesw & Hes32 & Hesc).
  destruct HCORE as (HJ & Hspr & Hfr & Hperm & Hio & Hmo & Hkept).
  pose proof HJ as (HAR & Hlyle & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hc1 & Hc2 & Hc3 & Hc4 & _).
  pose proof HJc as (_ & Hlyle_c & _).
  cbn [hi_cid hi_rsz headamp_himg_B] in Hown, EF, ERS.
  assert (HTS : T_SEG_STK = 16384) by reflexivity.
  assert (HRb : alloc_ceiling + T_SEG_STK <= e_R (x_e cx) /\ e_R (x_e cx) + 0x220 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47)
    by (rewrite HTS in *; lia).
  assert (HspR : spZ (x_regs cx) = e_R (x_e cx)).
  { unfold spZ. rewrite HR2. unfold w64. apply unsigned_lit_small. rewrite HTS in HRb. lia. }
  (* the frame *)
  assert (HinF : In (4, x_pos cx) (frames S2)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  assert (EF2 : e_F (x_e cx) = frame_addr ly2 4 (x_pos cx)).
  { rewrite EF, (cj_frame_addr_le _ _ _ 4 (x_pos cx) Hlyle_c), (cj_frame_addr_le _ _ _ 4 (x_pos cx) Hlyle). reflexivity. }
  destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) HAR HinF) as (HF1 & HF2 & HF3).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 4 (x_pos cx) HAR HinF) as (HF32 & _ & HFp & _).
  rewrite <- EF2 in HF1, HF2, HF3, HF32, HFp. change (fs_frame_bytes 4) with 1024 in HF1, HF2, HF3, HFp.
  (* pp *)
  assert (Hpp2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
    by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppb]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp2) as (_ & Hp1 & Hp2 & Hppapp & _).
  assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
  change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hp2, Hppapp.
  pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ 4 (x_pos cx) HAR Hpp2 HinF) as Hsep.
  rewrite Hrq, <- EF2 in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
  (* the cursor *)
  destruct HIN as (Hel & Hgar & Hra & Hhull & Hamr & Hsrc0 & Hsrc63 & Hdis).
  destruct Hsr as (j & Hj & Er).
  assert (Hlr : length r = (length rest - j)%nat) by (rewrite Er, length_skipn; reflexivity).
  assert (Hcur : hsu_cur rsegs cx rest r = e_src (x_e cx) + Z.of_nat j) by (unfold hsu_cur; rewrite Hlr; lia).
  assert (Hhi : e_src (x_e cx) + e_left (x_e cx) <= 2 ^ 47 - 1).
  { unfold amem_range in Hamr.
    unfold kHighMemBeg, kHighMemEnd, kLowMemEnd in Hamr. lia. }
  (* rom_view at the cut: a read-only byte lies outside the stack below R and outside the segment's writes *)
  assert (HromG : rom_view rsegs W2 mem2).
  { intros a Ha. rewrite <- (Hrom a Ha).
    destruct Ha as (sg & Hsg & _ & Hr). assert (Himg : in_img rsegs a) by (exists sg; split; [exact Hsg | lia]).
    pose proof (img_segs_low a Himg) as Hlow.
    unfold kLowMemEnd in Hlow.
    apply Hkept; [lia | rewrite HspR; rewrite HTS in HRb; lia |].
    unfold hsu_E1. intros [Hw | Hw]; [| exact (blk_img rsegs B LAWS _ _ _ _ _ _ _ a HAR Hpp2 ltac:(rewrite Hrq; lia) Himg)].
    unfold hd_inw in Hw. cbn [hi_w1 headamp_himg_B] in Hw.
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
    { apply (frm_img rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) a HAR HinF); [| exact Himg].
      rewrite <- EF2. change (fs_frame_bytes 4) with 1024. lia. }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
    { unfold shadow_addr, SHADOW_OFF in Hw. pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)). lia. }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [rewrite HTS in HRb; lia|].
    apply Exists_nil in Hw. exact Hw. }
  (* every image byte as at the segment's start *)
  assert (K1 : forall a, in_img rsegs a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
  { intros a Himg. pose proof (img_segs_low a Himg) as Hlow. unfold kLowMemEnd in Hlow.
    apply Hkept; [lia | rewrite HspR, HTS; rewrite HTS in HRb; lia |].
    unfold hsu_E1. intros [Hw | Hw].
    2: { apply (blk_img rsegs B LAWS _ _ _ _ _ _ _ a HAR Hpp2); [| exact Himg]. rewrite Hrq. lia. }
    unfold hd_inw in Hw. cbn [hi_w1 headamp_himg_B] in Hw.
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
    { apply (frm_img rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) a HAR HinF); [| exact Himg].
      rewrite <- EF2. change (fs_frame_bytes 4) with 1024. lia. }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
    { unfold shadow_addr, SHADOW_OFF in Hw. pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)). lia. }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [rewrite HTS in HRb; lia|].
    apply Exists_nil in Hw. exact Hw. }
  (* every shadow byte outside F's 116 as at the segment's start *)
  assert (K2 : forall s, kLowMemEnd <= s < kHighMemBeg ->
     ~ (shadow_addr (e_F (x_e cx)) <= s < shadow_addr (e_F (x_e cx)) + 116) ->
     aview rsegs (w_H W2) mem2 s = aview rsegs (w_H (x_W cx)) (x_memc cx) s).
  { intros s Hs HnF. unfold kLowMemEnd, kHighMemBeg in Hs.
    apply Hkept; [lia | rewrite HspR, HTS; rewrite HTS in HRb; lia |].
    unfold hsu_E1. intros [Hw | Hw].
    2: { unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, Layout.PP_SIZE in Hppapp.
         unfold Layout.PP_SIZE in Hw. lia. }
    unfold hd_inw in Hw. cbn [hi_w1 headamp_himg_B] in Hw.
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
    { unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HF3. lia. }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [lia|].
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [rewrite HTS in HRb; lia|].
    apply Exists_nil in Hw. exact Hw. }
  destruct HRb as (BR1 & BR2 & BR3).
  split; [exact HJ|].
  split; [exact (eq_trans (Hspr 2 ltac:(lia)) HR2)|].
  split; [exact (eq_trans (Hspr 3 ltac:(lia)) Hgp)|].
  split; [exact (eq_trans (Hspr 4 ltac:(lia)) Htp)|].
  split; [exact BR1|]. split; [exact BR2|]. split; [exact BR3|].
  split; [exact Hsp0al|]. split; [exact ER32|]. split; [exact ESTK|]. split; [exact HspR|].
  split; [exact Hown|]. split; [exact EF2|].
  split; [exact HF1|]. split; [exact HF2|]. split; [exact HF32|]. split; [exact HF3|].
  split; [exact Hp1|]. split; [exact Hp2|]. split; [exact Hsep|]. split; [exact Hppapp|].
  split; [rewrite Hcur; lia|]. split; [rewrite Hcur, Hlr; lia|].
  split.
  { intros a Ha. split; [exact (proj1 (HFp a Ha))|]. intros Himg.
    apply (frm_img rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) a HAR HinF); [| exact Himg].
    rewrite <- EF2. change (fs_frame_bytes 4) with 1024. exact Ha. }
  split; [exact HromG|].
  split; [exact K1|].
  exact K2.
Qed.

(* ============================== what the walk reads of the image ============================== *)
Lemma hw7b_base_img : forall cx rest (W2 : world rsegs) mem2 pat,
  hsu_start_M01 rsegs B headamp_himg_B cx rest ->
  0 <= e_R (x_e cx) -> e_R (x_e cx) + 0x220 <= 2 ^ 47 ->
  (forall a, in_img rsegs a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a) ->
  (forall s, kLowMemEnd <= s < kHighMemBeg ->
     ~ (shadow_addr (e_F (x_e cx)) <= s < shadow_addr (e_F (x_e cx)) + 116) ->
     aview rsegs (w_H W2) mem2 s = aview rsegs (w_H (x_W cx)) (x_memc cx) s) ->
  hd_fsh rsegs (w_H W2) mem2 (e_F (x_e cx)) pat -> Z.of_nat (length pat) = 116 ->
  (forall a s, In (a, s) headamp_B_strs -> hd_cstr rsegs (w_H W2) mem2 a s) /\
  (forall a n, In (a, n) headamp_B_globs -> range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF a n) /\
  (forall a v, In (a, v) headamp_B_cells -> val_mem rsegs (mrestrict (w_H W2) mem2) a 8 v) /\
  range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_R (x_e cx) + 0x180) 8.
Proof.
  intros cx rest W2 mem2 pat HST HR0 HR1 K1 K2 HFSH Hplen.
  pose proof (@asan_consts rc) as (_ & _ & EHB & EHE & ELE).
  destruct HST as (HPRE & _).
  destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfsh0 & _ & _ & _ & Hglobs & Hrz & Hstrs & Hcells & _).
  cbn [hi_shA hi_globs hi_strs hi_cells hi_rz headamp_himg_B] in Hfsh0, Hglobs, Hrz, Hstrs, Hcells.
  split; [| split; [| split]].
  - intros a s Hin.
    assert (Hseg : forall x, a <= x < a + Z.of_nat (length s) + 8 -> in_img rsegs x).
    { intros x Hx. pose proof (proj1 (forallb_forall _ _) cj_strs_in_img (a, s) Hin) as Hb. cbn [fst snd] in Hb.
      exact (cj_in_seg _ _ x Hb Hx). }
    apply (cj_cstr_kept (w_H (x_W cx)) (x_memc cx) (w_H W2) mem2 (e_F (x_e cx)) pat a s).
    + exact (proj1 (Forall_forall _ _) Hstrs (a, s) Hin).
    + exact Hseg.
    + exact Hfsh0.
    + exact HFSH.
    + exact Hplen.
    + exact K1.
    + exact K2.
  - intros a n Hin.
    assert (Hseg : forall x, a <= x < a + n -> in_img rsegs x).
    { intros x Hx. pose proof (proj1 (forallb_forall _ _) cj_globs_in_img (a, n) Hin) as Hb. cbn [fst snd] in Hb.
      exact (cj_in_seg _ _ x Hb Hx). }
    pose proof (proj1 (Forall_forall _ _) Hglobs (a, n) Hin) as Hra. cbn [fst snd] in Hra.
    apply (hm_ra_kept rsegs (w_H (x_W cx)) (x_memc cx)); [exact Hra|]. intros x Hx.
    pose proof (img_segs_low x (Hseg x Hx)) as Hlow. unfold kLowMemEnd in Hlow.
    apply K2.
    + pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as X. exact X.
    + pose proof (hm_ra_not_fsh rsegs _ _ _ _ a n Hra Hfsh0 hmu_sh_P0_big x Hx) as HnF.
      rewrite cj_shA_len in HnF. exact HnF.
  - intros a v Hin.
    assert (Hseg : forall x, a <= x < a + 8 -> in_img rsegs x).
    { intros x Hx. pose proof (proj1 (forallb_forall _ _) cj_cells_in_img (a, v) Hin) as Hb. cbn [fst snd] in Hb.
      exact (cj_in_seg _ _ x Hb Hx). }
    unfold hd_ro_cells in Hcells.
    pose proof (proj1 (Forall_forall _ _) Hcells _ Hin) as V0. cbn [fst snd] in V0.
    apply hm_val_of_bytes. apply (hm_bytes_kept rsegs (w_H (x_W cx)) (x_memc cx)).
    { apply hm_bytes_of_val. exact V0. }
    intros x Hx. rewrite length_Z_to_le_bytes in Hx. apply K1. apply Hseg. lia.
  - (* the 8-byte cell R+0x180: its shadow at the start (hi_rz), outside F's shadow bytes, kept *)
    apply Forall_inv in Hrz. cbn [fst snd] in Hrz.
    apply (hm_ra_kept rsegs (w_H (x_W cx)) (x_memc cx)); [exact Hrz|]. intros x Hx.
    apply K2.
    + pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as X. exact X.
    + pose proof (hm_ra_not_fsh rsegs _ _ _ _ _ _ Hrz Hfsh0 hmu_sh_P0_big x Hx) as HnF.
      rewrite cj_shA_len in HnF. exact HnF.
Qed.

(* ============================== the join J from the walk's continuation ============================== *)
Lemma hw7b_J_of : forall cx rest sh np ps cnt es rr r pb chs ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
  hsu_start_M01 rsegs B headamp_himg_B cx rest ->
  hsu_cut_G rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r pb chs ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall rg, In rg cj_kregs -> getr regs3 (Z_to_bv 5 rg) = getr regs2 (Z_to_bv 5 rg)) ->
  getr regs3 6 = getr regs2 6 -> getr regs3 13 = w64 (hsu_cur rsegs cx rest r) ->
  getr regs3 18 = w64 (e_pp (x_e cx) + 0x4000) -> getr regs3 20 = w64 (e_F (x_e cx) + 0x210) ->
  getr regs3 23 = w64 (e_pp (x_e cx)) ->
  hm_bytes rsegs (w_H W2) mem3 (e_F (x_e cx) + 0x210) (hw7b_e62 (hw7b_js chs pb)) ->
  hd_fsh rsegs (w_H W2) mem3 (e_F (x_e cx)) (hmu_sh false false false false false true false false) ->
  cb_kept W2 mem2 mem3 (fun a => e_R (x_e cx) - 2 * ESTACK <= a < e_R (x_e cx) \/
    e_R (x_e cx) + 0x178 <= a < e_R (x_e cx) + 0x198 \/
    e_F (x_e cx) + 0x20 <= a < e_F (x_e cx) + 0x80 \/ e_F (x_e cx) + 0x210 <= a < e_F (x_e cx) + 0x278 \/
    shadow_addr (e_F (x_e cx)) <= a < shadow_addr (e_F (x_e cx)) + 116) ->
  hsu_cut_J rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r (ent_text (hw7b_js chs pb) true)
    ly2 S2 W2 regs3 mem3 md3.
Proof.
  intros cx rest sh np ps cnt es rr r pb chs ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HST HG HJ3 Hio3 Hregs
    H6 H13 H18 H20 H23 HE3 HF3 HK3.
  pose proof (@asan_consts rc) as (Hceil & _).
  pose proof HG as (HPB & HAT & HFSH & HPP & HCH & HE0 & Hkd & Hg & Hchl & Hpb).
  destruct (hw7b_base_facts cx rest sh np ps cnt es rr r ly2 S2 W2 regs2 mem2 md2 HST HPB) as
    (_ & R2 & R3 & R4 & BR1 & BR2 & BR3 & BSP & BR4 & BR5 & HspR & Hown & EF2 & HF1 & HF2 & HF32 & HFapp
     & Hpp1 & Hpp2 & Hsep & Hppapp & Hc1 & Hc2 & HFp & HromG & K1 & K2).
  pose proof HPB as (HCORE & HIN' & Hsr & Hsrr' & Hwf & Hlen' & Hps & Htie & Hsh & Hnp & Hlp & Hnp3 & Hsh7 & Hps2
    & Hcnt & Hesw & Hes32 & Hesc).
  destruct HCORE as (_ & Hspr & Hfr & Hperm & Hio & Hmo & Hkept).
  assert (HTS : T_SEG_STK = 16384) by reflexivity. rewrite HTS in BR1, BR5.
  assert (HES : ESTACK = 4096) by reflexivity.
  pose proof (hw7b_shF_bounds (e_F (x_e cx)) HF1 ltac:(lia)) as (SB1 & SB2).
  unfold cb_kept in HK3.
  (* what the walk may have written since G *)
  set (Wr := fun a => ~ (0 <= a < 2 ^ 64) \/ (e_R (x_e cx) - 2 * ESTACK <= a < e_R (x_e cx) \/
    e_R (x_e cx) + 0x178 <= a < e_R (x_e cx) + 0x198 \/
    e_F (x_e cx) + 0x20 <= a < e_F (x_e cx) + 0x80 \/ e_F (x_e cx) + 0x210 <= a < e_F (x_e cx) + 0x278 \/
    shadow_addr (e_F (x_e cx)) <= a < shadow_addr (e_F (x_e cx)) + 116)).
  assert (KE : forall x, ~ Wr x -> aview rsegs (w_H W2) mem3 x = aview rsegs (w_H W2) mem2 x).
  { intros x Hx. unfold Wr in Hx.
    assert (Hx0 : 0 <= x < 2 ^ 64).
    { destruct (Z_le_gt_dec 0 x) as [H0|H0]; [|exfalso; apply Hx; left; lia].
      destruct (Z_lt_ge_dec x (2 ^ 64)) as [H1|H1]; [lia|exfalso; apply Hx; left; lia]. }
    apply HK3; [exact Hx0 | intros H; apply Hx; right; exact H]. }
  pose proof (cj_pc_len sh ps es Hwf Hesw Hes32 Hps2) as Hlpp.
  unfold hsu_cut_J. split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* the pod loop's base *)
    unfold hsu_pod_base. split.
    { unfold hsu_core, hsu_mid. split; [exact HJ3|]. split.
      { intros rg Hrg. rewrite (Hregs rg ltac:(unfold cj_kregs; cbn [In]; lia)). exact (Hspr rg Hrg). }
      split; [exact Hfr|]. split; [exact Hperm|].
      split; [exact (same_io_trans _ _ _ Hio Hio3)|].
      split; [exact Hmo|].
      intros a Ha Hs HE1. rewrite KE; [exact (Hkept a Ha Hs HE1)|]. rewrite HspR, HTS in Hs.
      intros Hw. destruct Hw as [Hw | Hw]; [exact (Hw Ha)|].
      apply HE1. unfold hsu_E1, hd_inw. left. cbn [hi_w1 headamp_himg_B].
      destruct Hw as [Hw | [Hw | [Hw | [Hw | Hw]]]].
      + exfalso. apply Hs. rewrite HES in Hw. lia.
      + apply Exists_cons. right. apply Exists_cons. right. apply Exists_cons. left. cbn [fst snd hd_xv]. lia.
      + apply Exists_cons. left. cbn [fst snd hd_xv]. lia.
      + apply Exists_cons. left. cbn [fst snd hd_xv]. lia.
      + apply Exists_cons. right. apply Exists_cons. left. cbn [fst snd hd_xv]. lia. }
    split; [exact HIN'|]. split; [exact Hsr|]. split; [exact Hsrr'|].
    repeat (split; [eassumption|]). exact Hesc.
  - (* the registers and cells *)
    unfold hsu_at_cx, hsu_at. apply Forall_forall. intros [l v] Hf.
    apply in_app_or in Hf as [Hf | Hf].
    + assert (HfG : In (l, v) (hsu_L_Dc rsegs cx sh np ps cnt es ++
          [(LCell XR 0x110, hsu_cur rsegs cx rest r); (LReg 6, Z.of_nat (length r));
           (LReg 18, e_F (x_e cx) + HSU_CH); (LReg 26, pb)]))
        by (apply in_or_app; left; exact Hf).
      apply (hm_at_kept rsegs _ _ _ _ regs2 regs3 (x_e cx) l v (cj_at _ _ _ _ _ l v HAT HfG)).
      apply (hm_keeps_of rsegs Wr _ _ _ _ _ _ _ l KE).
      destruct (cj_Dc_locs cx sh np ps cnt es l v Hf) as [(rg & -> & Hrg) | (o & -> & Ho)].
      * exact (Hregs rg Hrg).
      * intros i Hi. cbn [hd_xv].
        assert (Hob : 0 <= o <= 0x158) by (unfold cj_cells in Ho; cbn [In] in Ho; lia).
        clear Ho. intros Hw.
        destruct Hw as [Hw | [Hw | [Hw | [Hw | [Hw | Hw]]]]].
        -- apply Hw. lia.
        -- lia.
        -- lia.
        -- lia.
        -- lia.
        -- lia.
    + cbn [In] in Hf. destruct Hf as [E | [E | [E | [E | [E | []]]]]]; injection E as <- <-; cbn [hd_at].
      * exact H13.
      * pose proof (cj_at _ _ _ _ _ (LReg 6) _ HAT ltac:(hw7b_inG)) as A6. cbn [hd_at] in A6.
        exact (eq_trans H6 A6).
      * exact H18.
      * exact H20.
      * exact H23.
  - (* the frame's shadow: e62 in scope, t and ch out of scope again *)
    unfold hsu_fsh_at. rewrite hw7b_PJ. exact HF3.
  - (* the first block *)
    unfold hsu_pp_at. unfold hsu_pp_at in HPP.
    change (garr8 rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx)) (hd_zbytes (pc_image (PbCut sh ps (Some es)))))
      with (hm_bytes rsegs (w_H W2) mem2 (e_pp (x_e cx)) (pc_image (PbCut sh ps (Some es)))) in HPP.
    change (garr8 rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx)) (hd_zbytes (pc_image (PbCut sh ps (Some es)))))
      with (hm_bytes rsegs (w_H W2) mem3 (e_pp (x_e cx)) (pc_image (PbCut sh ps (Some es)))).
    refine (hm_bytes_kept_wr rsegs Wr (w_H W2) mem2 (w_H W2) mem3 _ _ HPP KE _).
    intros x Hx Hw. rewrite Hlpp in Hx. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hppapp. unfold Layout.PP_SIZE in Hx, Hsep, Hpp2, Hppapp.
    destruct Hw as [Hw | [Hw | [Hw | [Hw | [Hw | Hw]]]]].
    + apply Hw. lia.
    + rewrite HES in Hw. lia.
    + lia.
    + lia.
    + lia.
    + lia.
  - (* e62: the key's pod *)
    unfold hsu_obj_at. rewrite (hw7b_ent_mem_js chs pb Hchl). exact HE3.
  - (* ent_build of the turn's input *)
    rewrite (hw7b_ent_build_0 rr chs pb r Hkd Hg Hchl). reflexivity.
  - exact (hw7b_ent_wf_js chs pb Hchl).
Qed.

(* ============================== the piece from the walk's statement ============================== *)
Hypothesis MTL : ameter_laws MT.

Lemma hsu_piece_W7b_of_core :
  hw7b_core_stmt B -> hsu_piece_W7b_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof using All.
  intros CORE cx POST rest i k HST HJ.
  unfold hsu_from_G. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r pb chs Hi Hk HG.
  pose proof (@asan_consts rc) as (Hceil & _).
  pose proof HG as (HPB & HAT & HFSH & HPP & HCH & HE0 & Hkd & Hg & Hchl & Hpb).
  destruct (hw7b_base_facts cx rest sh np ps cnt es rr r ly2 S2 W2 regs2 mem2 md2 HST HPB) as
    (HJ2 & R2 & R3 & R4 & BR1 & BR2 & BR3 & BSP & BR4 & BR5 & HspR & Hown & EF2 & HF1 & HF2 & HF32 & HFapp
     & Hpp1 & Hpp2 & Hsep & Hppapp & Hc1 & Hc2 & HFp & HromG & K1 & K2).
  assert (HTS : T_SEG_STK = 16384) by reflexivity.
  unfold hsu_fsh_at in HFSH. rewrite hw7b_PG in HFSH.
  destruct (hw7b_base_img cx rest W2 mem2 (hmu_sh true true false false false true false false) HST
    ltac:(rewrite HTS in BR1; lia) ltac:(lia) K1 K2 HFSH ltac:(rewrite hmu_sh_len; reflexivity))
    as (KS & KG & KC & KRZ).
  (* the values of the cut G *)
  assert (AT : forall l v, In (l, v) (hsu_L_Dc rsegs cx sh np ps cnt es ++
      [(LCell XR 0x110, hsu_cur rsegs cx rest r); (LReg 6, Z.of_nat (length r));
       (LReg 18, e_F (x_e cx) + HSU_CH); (LReg 26, pb)]) ->
    hd_at rsegs (w_H W2) mem2 regs2 (x_e cx) l v)
    by (intros l v Hin; exact (cj_at _ _ _ _ _ l v HAT Hin)).
  assert (VS : forall o v, In (LCell XR o, v) (hsu_L_Dc rsegs cx sh np ps cnt es ++
      [(LCell XR 0x110, hsu_cur rsegs cx rest r); (LReg 6, Z.of_nat (length r));
       (LReg 18, e_F (x_e cx) + HSU_CH); (LReg 26, pb)]) -> 0 <= v < 2 ^ 64 ->
    val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + o) 8 v).
  { intros o v Hin Hv. apply cj_val_small; [exact Hv|]. exact (AT (LCell XR o) v Hin). }
  assert (Hpbn : 0 <= pb) by lia.
  unfold cfg_at.
  apply (CORE (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem2 md2 (x_k cx) regs2 (e_R (x_e cx)) (e_F (x_e cx)) pb chs (hw7b_pptr (pb mod 8))
    (e_pp (x_e cx) + 0x4000) (hsu_cur rsegs cx rest r) (e_pp (x_e cx)) POST).
  - exact HJ2.
  - exact R2.
  - exact (AT (LReg 9) _ ltac:(hw7b_inG)).
  - exact R3.
  - exact R4.
  - exact BR4.
  - exact BR2.
  - exact BR5.
  - exact BR3.
  - exact BSP.
  - exact BR1.
  - exact HF32.
  - exact HF1.
  - exact HF2.
  - exact HFapp.
  - (* the frame for locals: a frame the journal owns, present, outside the image *)
    intros a Ha. destruct (HFp a Ha) as [Hpr Hni].
    split; [| split; [exact (aview_some_of_apresent rsegs _ _ _ Hpr) | exact Hni]].
    unfold awr_byte, in_frames, in_zr. right. right. right.
    exists 4, (x_pos cx). split; [exact Hown|]. left. cbn [fst snd].
    rewrite <- EF2. change (fs_frame_bytes 4) with 1024. lia.
  - (* its shadow bytes *)
    intros i0 Hi0. unfold awr_byte, in_frames, in_zr. right. right. right.
    exists 4, (x_pos cx). split; [exact Hown|]. right. cbn [fst snd].
    rewrite <- EF2. change (fs_frame_bytes 4 / 8) with 128. lia.
  - (* parts[0 .. 3]: the real frame, inside the journal's stack window *)
    intros a Ha. unfold awr_byte. left. rewrite HTS in BR5. lia.
  - exact (AT (LReg 27) _ ltac:(hw7b_inG)).
  - exact (AT (LReg 26) _ ltac:(hw7b_inG)).
  - exact Hpb.
  - exact (AT (LReg 25) _ ltac:(hw7b_inG)).
  - exact (AT (LReg 18) _ ltac:(hw7b_inG)).
  - exact (AT (LReg 19) _ ltac:(hw7b_inG)).
  - exact HFSH.
  - exact HCH.
  - exact (hw7b_chs_nonzero rr chs pb r Hg).
  - exact Hchl.
  - exact HE0.
  - exact (KS _ _ hw7b_hpfx_str).
  - exact (KS _ _ (hw7b_sep_str pb)).
  - exact (KC _ _ (hw7b_param_cell pb Hpbn)).
  - exact (KS _ _ (hw7b_param_str pb Hpbn)).
  - exact (hw7b_pptr_range pb Hpbn).
  - destruct (hw7b_param_glob pb Hpbn) as ([ga gn] & Hgl & Hlo & Hhi). cbn [fst snd] in Hlo, Hhi.
    exact (range_addressable_sub _ _ _ _ _ _ (KG ga gn Hgl) Hlo Hhi).
  - exact KRZ.
  - (* the read-only bytes: rom_view at G *)
    intros a Ha _ _. exact (HromG a Ha).
  - eapply hw7b_val_eq; [| exact (VS 0x118 _ ltac:(hw7b_inG) ltac:(unfold HSU_E62; lia))]. unfold HSU_E62. lia.
  - eapply hw7b_val_eq; [| exact (VS 0x130 _ ltac:(hw7b_inG) ltac:(unfold HSU_E62; lia))]. unfold HSU_E62. lia.
  - pose proof (AT (LCell XR 0xe8) _ ltac:(hw7b_inG)) as V. cbn [hd_at hd_xv] in V.
    eapply hw7b_val_eq; [| exact V]. unfold HSU_E62. f_equal. lia.
  - exact (VS 0x138 (e_pp (x_e cx) + 0x4000) ltac:(hw7b_inG) ltac:(unfold Layout.PP_SIZE in Hpp2; lia)).
  - unfold Layout.PP_SIZE in Hpp2. lia.
  - exact (VS 0x110 (hsu_cur rsegs cx rest r) ltac:(hw7b_inG) ltac:(lia)).
  - lia.
  - exact (VS 0x148 (e_pp (x_e cx)) ltac:(hw7b_inG) ltac:(unfold Layout.PP_SIZE in Hpp2; lia)).
  - unfold Layout.PP_SIZE in Hpp2. lia.
  - (* at J: hsu_cut_J from the continuation's facts, then the piece's continuation *)
    intros regs3 mem3 md3 HJ3 Hio3 Hregs3 H6 H13 H18 H20 H23 HE3 HF3 HK3 _.
    exact (HJ ly2 S2 W2 regs3 mem3 md3 sh np ps cnt es rr r (ent_text (hw7b_js chs pb) true) Hi Hk
      (hw7b_J_of cx rest sh np ps cnt es rr r pb chs ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HST HG HJ3 Hio3
        Hregs3 H6 H13 H18 H20 H23 HE3 HF3 HK3)).
Qed.
End w.

Print Assumptions hw7b_shF_bounds.
Print Assumptions hw7b_pptr_range.
Print Assumptions hw7b_base_facts.
Print Assumptions hw7b_base_img.
Print Assumptions hw7b_J_of.
Print Assumptions hsu_piece_W7b_of_core.

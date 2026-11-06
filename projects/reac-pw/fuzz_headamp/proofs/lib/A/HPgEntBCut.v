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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Hd.v, with its module paths and module names changed; 747 of its 791 lines of code are new or changed and 692 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEntBCut.v at f3898085bda; for reac-pw/fuzz_headamp image A: module paths and the rs_ / rl_ / rm_ / role_ prefixes renamed, every pc moved by the code's uniform shift +0xd20 over [0x80a80, 0x81af0), the real-frame cells by the plan's slot map, the frame for locals of class 4 (1024 bytes, 80 shadow bytes, objects [F+0x20, F+0x158)), the real frame of 0x1e0 bytes (cells [R, R+0x160)), hd_seg_pre's conjunct order (cap / null where role has pp <> 0 / In / flags, hd_guard_ok before rom_view, pp's block from the last conjunct hd_fresh_block, R mod 32), headamp's hm_sh (res and x), hd_cstr's tenth conjunct, the vocab table ent_build.vocab 0x9c060, RPgCfgChanges.cfg_segs_low -> HPgSteps.img_segs_low; the unused Pod.Role import dropped. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the two bridges between lib/A/HPgSeg.v's cut
   states at ent_build's case entries (hs_cut_D, pcs 0x81860 .. 0x81ea4) and at the join J (hs_cut_J, 0x8237c) and
   the facts a walk of one case uses. Proves no function (kind: segment lemma).

   eb_D_facts: what hs_start_M01 and hs_cut_D give at a case entry, in the form the engine's entry state and the
     call contracts ask: the harness's journal, the registers, the real frame's cells, the bounds of R, F and pp,
     e = 0^104 and its shadow in scope, the frame's bytes present, rom_view at the cut.
   eb_D_input: the input bytes after the kind byte at the case entry (bytes, shadow bytes, shadow hull, ranges).
   eb_D_keep: every image byte, and every shadow byte outside F's 80 shadow bytes, is at the case entry as at the
     segment's start.
   eb_D_w6b: the case blocks' premises (lib/A/HPgW6bBase.v: lib/A/HPgW6aBase.w6_ctx and w6b_in) at a case entry.
   eb_D_img: what cases 9 and 1 read of the image at a case entry (HPgW6bBase.w6b_s_ok, w6b_vocab_ok), from
     hd_seg_pre's strings, registered globals and cells.
   eb_J_of: hs_cut_J at the join at the case entry's (ly2, S2, W2), from the journal at the join's memory, the
     registers the case leaves, the bytes it kept (every byte outside the callees' stack below R and the case's
     three write windows [R+0x68, R+0x70), [R+0x118, R+0x120), [F+0xf0, F+0x158) as at the case entry), R+0x118 = what
     is left, and e = Layout.ent_mem of the pod.
   eb_J_post: the post of a case block (HPgW6aBase.w6_post at J with HPgW6bBase's w6b_clob, w6b_wr, w6b_J_R) is
     hs_cut_J at the join: the journal, the frames, the blocks, the I/O state and the meter chain from the case
     entry's hs_core through the block; the registers outside w6b_clob, every byte outside the callees' stack below R
     and the case's three write windows are as at the case entry; R+0x118 = what is left, and e = Layout.ent_mem of
     the pod. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps HPgW6aBase HPgW6bBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Tables.
Import ListNotations.
(* the cut record's projections, with the segments implicit as inside lib/A/HPgSeg.v *)
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the frame's shadow at a case entry: e's granules in scope, the rest the prologue's *)
Lemma eb_PJ : hs_PJ = hm_sh false false false true false false.
Proof. vm_compute. reflexivity. Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.

Lemma eb_at : forall H mem regs e (L : list (hd_loc * Z)) l v,
  hs_at rsegs H mem regs e L -> In (l, v) L -> hd_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v HA Hin. exact (proj1 (Forall_forall _ _) HA (l, v) Hin). Qed.

Lemma eb_frame_addr_le : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos Hle. unfold frame_addr. destruct Hle as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. Qed.

Lemma eb_val_small : forall H mem a v, 0 <= v < 2 ^ 64 ->
  val_mem rsegs (mrestrict H mem) a 8 (v mod 2 ^ 64) -> val_mem rsegs (mrestrict H mem) a 8 v.
Proof. intros H mem a v Hv V. rewrite Z.mod_small in V by lia. exact V. Qed.
Lemma eb_val_mod : forall H mem a v, 0 <= v < 2 ^ 64 ->
  val_mem rsegs (mrestrict H mem) a 8 v -> val_mem rsegs (mrestrict H mem) a 8 (v mod 2 ^ 64).
Proof. intros H mem a v Hv V. rewrite Z.mod_small by lia. exact V. Qed.

Ltac eb_in := cbn [hs_L_D hs_L_Dc hs_L_Dc0 hs_Rc hs_Rc0 hs_Kc app]; repeat (first [left; reflexivity | right]).

(* ============================== the case entry ============================== *)
Lemma eb_D_facts : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  hs_start_M01 rsegs B cx rest ->
  hs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem2 md2 (x_k cx) /\
  (* registers *)
  getr regs2 2 = w64 (e_R (x_e cx)) /\ getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
  getr regs2 9 = w64 (e_R (x_e cx)) /\ getr regs2 23 = w64 SHADOW_OFF /\
  getr regs2 24 = w64 (hs_cur rsegs cx rest r) /\ getr regs2 14 = w64 (hs_cur rsegs cx rest r - 1) /\
  getr regs2 25 = w64 (Z.of_nat (length r)) /\
  getr regs2 21 = w64 (e_pp (x_e cx) + 0x4000) /\ getr regs2 27 = w64 (e_pp (x_e cx)) /\
  (* the real frame's cells *)
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x48) 8 (e_F (x_e cx) + 0x100) /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x98) 8 (e_pp (x_e cx) + 0x4000) /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0xf0) 8 (e_pp (x_e cx)) /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0xd0) 8 (shadow_addr (e_pp (x_e cx) + 0x4000)) /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0xe0) 8 (e_F (x_e cx) + 0xf8) /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x110) 8 (e_F (x_e cx) + 0xf0) /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + 0x118) 8 (Z.of_nat (length r) + 1) /\
  (* bounds *)
  alloc_ceiling + T_SEG_STK <= e_R (x_e cx) /\ e_R (x_e cx) + 0x1e0 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  e_R (x_e cx) mod 16 = 0 /\ x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK /\
  In (4, x_pos cx) (x_own cx) /\ In (4, x_pos cx) (frames S2) /\ e_F (x_e cx) = frame_addr ly2 4 (x_pos cx) /\
  4096 <= e_F (x_e cx) /\ e_F (x_e cx) + 1024 <= alloc_ceiling /\ e_F (x_e cx) mod 32 = 0 /\ in_app (e_F (x_e cx)) 1024 /\
  In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2) /\ 4096 <= e_pp (x_e cx) /\
  e_pp (x_e cx) + Layout.PP_SIZE <= alloc_ceiling /\ zdisjoint (e_pp (x_e cx), Layout.PP_SIZE) (e_F (x_e cx), 1024) /\
  1 <= hs_cur rsegs cx rest r /\ hs_cur rsegs cx rest r + Z.of_nat (length r) <= 2 ^ 47 - 1 /\
  (* e, the frame, the real frame *)
  (forall i, 0 <= i < 104 -> mbyte rsegs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xf0 + i) = Some (Z_to_bv 8 0)) /\
  (forall o, 0 <= o < 1024 -> apresent (w_H W2) mem2 (e_F (x_e cx) + o)) /\
  range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_F (x_e cx) + 0xf0) 104 /\
  (forall a, x_sp0 cx - x_STK cx <= a < x_sp0 cx -> apresent (w_H W2) mem2 a) /\
  hd_fsh rsegs (w_H W2) mem2 (e_F (x_e cx)) hs_PJ /\
  rom_view rsegs W2 mem2.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof asan_consts as (Hceil & _).
  destruct HST as (HPRE & HL1 & Hlen & HIN).
  destruct HPRE as (HJc & Hnev & HR2 & Hgp & Htp & ES & ER32 & ERS & ESTK & Hown & EF & Hfsh0 & Hcap & Hnull
    & Haro & Hglobs & Hrz & Hstrs & Hcells & Hguard & Hrom & (Hpp0 & Hppb & Hnfresh)).
  assert (ER16 : e_R (x_e cx) mod 16 = 0).
  { pose proof (Z.div_mod (e_R (x_e cx)) 32 ltac:(lia)) as D. rewrite ER32, Z.add_0_r in D. rewrite D.
    replace (32 * (e_R (x_e cx) / 32)) with ((2 * (e_R (x_e cx) / 32)) * 16) by ring. apply Z_mod_mult. }
  destruct HD as (HPB & HAT & HFSH & HPP & HE0 & Hsrr & Hfu & Hkd & Hrr).
  destruct HPB as (HCORE & HIN' & Hsr & Hsrr' & Hwf & Hlen' & Hps & Htie & Hsh & Hnp & Hlp & Hnp3 & Hsh7 & Hps2 & Hcnt
    & Hesw & Hes32 & Hesc).
  destruct HCORE as (HJ & Hspr & Hfr & Hperm & Hio & Hmo & Hkept).
  pose proof HJ as (HAR & Hlyle & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hc1 & Hc2 & Hc3 & Hc4 & _).
  pose proof HJc as (_ & Hlyle_c & _).
  cbn [hi_cid hi_rsz headamp_himg_A] in Hown, EF, ERS.
  assert (AT : forall l v, In (l, v) (hs_L_D rsegs cx sh np ps cnt es rest r kd) ->
    hd_at rsegs (w_H W2) mem2 regs2 (x_e cx) l v)
    by (intros l v Hin; exact (eb_at _ _ _ _ _ l v HAT Hin)).
  assert (HTS : T_SEG_STK = 16384) by reflexivity.
  assert (HRb : alloc_ceiling + T_SEG_STK <= e_R (x_e cx) /\ e_R (x_e cx) + 0x1e0 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47)
    by (rewrite HTS in *; lia).
  assert (HspR : spZ (x_regs cx) = e_R (x_e cx)).
  { unfold spZ. rewrite HR2. unfold w64. apply unsigned_lit_small. rewrite HTS in HRb. lia. }
  (* the frame *)
  assert (HinF : In (4, x_pos cx) (frames S2)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  assert (EF2 : e_F (x_e cx) = frame_addr ly2 4 (x_pos cx)).
  { rewrite EF, (eb_frame_addr_le _ _ _ 4 (x_pos cx) Hlyle_c), (eb_frame_addr_le _ _ _ 4 (x_pos cx) Hlyle). reflexivity. }
  destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) HAR HinF) as (HF1 & HF2 & HF3).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 4 (x_pos cx) HAR HinF) as (HF32 & _ & HFp & _).
  rewrite <- EF2 in HF1, HF2, HF3, HF32, HFp. change (fs_frame_bytes 4) with 1024 in HF1, HF2, HF3, HFp.
  (* pp *)
  assert (Hpp2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
    by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppb]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp2) as (_ & Hp1 & Hp2 & _).
  assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
  rewrite Hrq in Hp2.
  assert (Hp2' : e_pp (x_e cx) + 19744 <= alloc_ceiling) by (unfold Layout.PP_SIZE in Hp2; exact Hp2).
  pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ 4 (x_pos cx) HAR Hpp2 HinF) as Hsep.
  rewrite Hrq, <- EF2 in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
  (* the cursor *)
  destruct HIN as (Hel & Hgar & Hra & Hhull & Hamr & Hsrc0 & Hsrc63 & Hdis).
  destruct Hsr as (j & Hj & Er).
  assert (Hlr : length r = (length rest - j)%nat) by (rewrite Er, length_skipn; reflexivity).
  assert (Hcur : hs_cur rsegs cx rest r = e_src (x_e cx) + Z.of_nat j) by (unfold hs_cur; rewrite Hlr; lia).
  assert (Hhi : e_src (x_e cx) + e_left (x_e cx) <= 2 ^ 47 - 1).
  { unfold amem_range in Hamr. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. lia. }
  (* e *)
  assert (Ez : forall i, 0 <= i < 104 ->
    mbyte rsegs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xf0 + i) = Some (Z_to_bv 8 0)).
  { intros i Hi. destruct (HE0 (Z.to_nat i) ltac:(unfold hd_zbytes, zeros; rewrite length_map, repeat_length; lia)) as [V _].
    rewrite Z2Nat.id in V by lia. specialize (V 0%nat ltac:(lia)). rewrite Z.add_0_r in V. rewrite V.
    f_equal. unfold hd_zbytes. rewrite (hm_nth_map (zeros 104) (Z.to_nat i)).
    unfold zeros. rewrite (hm_nth_repeat _ _ 104 (Z.to_nat i)) by lia. reflexivity. }
  assert (HF8 : e_F (x_e cx) mod 8 = 0).
  { apply (proj1 (Z.mod_divide (e_F (x_e cx)) 32 ltac:(discriminate))) in HF32. destruct HF32 as [c Hc]. rewrite Hc.
    replace (c * 32) with ((c * 4) * 8) by ring. apply Z_mod_mult. }
  assert (HraE : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_F (x_e cx) + 0xf0) 104).
  { unfold hs_fsh_at in HFSH. rewrite eb_PJ in HFSH.
    pose proof (hm_A_ra_e rsegs (w_H W2) mem2 _ false false false false false 0 104 HFSH HF8 ltac:(lia) ltac:(lia)) as X.
    unfold HM_E in X. rewrite Z.add_0_r in X. exact X. }
  (* rom_view at the cut: a read-only byte lies outside the stack below R and outside the segment's writes *)
  assert (HromD : rom_view rsegs W2 mem2).
  { intros a Ha. rewrite <- (Hrom a Ha).
    destruct Ha as (sg & Hsg & _ & Hr). assert (Himg : in_img rsegs a) by (exists sg; split; [exact Hsg | lia]).
    pose proof (HPgSteps.img_segs_low a Himg) as Hlow. unfold kLowMemEnd in Hlow.
    apply Hkept; [lia | rewrite HspR; lia |].
    unfold hs_E1. intros [Hw | Hw]; [| exact (blk_img rsegs B LAWS _ _ _ _ _ _ _ a HAR Hpp2 ltac:(rewrite Hrq; lia) Himg)].
    unfold hd_inw in Hw. cbn [hi_w1 headamp_himg_A] in Hw.
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
    { apply (frm_img rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) a HAR HinF); [| exact Himg].
      rewrite <- EF2. change (fs_frame_bytes 4) with 1024. lia. }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
    { unfold shadow_addr, SHADOW_OFF in Hw. pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)). lia. }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [lia|].
    apply Exists_nil in Hw. exact Hw. }
  split; [exact HJ|].
  split; [exact (eq_trans (Hspr 2 ltac:(lia)) HR2)|].
  split; [exact (eq_trans (Hspr 3 ltac:(lia)) Hgp)|].
  split; [exact (eq_trans (Hspr 4 ltac:(lia)) Htp)|].
  split; [exact (AT (LReg 9) _ ltac:(eb_in))|].
  split; [exact (AT (LReg 23) _ ltac:(eb_in))|].
  split; [exact (AT (LReg 24) _ ltac:(eb_in))|].
  split; [exact (AT (LReg 14) _ ltac:(eb_in))|].
  split; [exact (AT (LReg 25) _ ltac:(eb_in))|].
  split; [exact (AT (LReg 21) _ ltac:(eb_in))|].
  split; [exact (AT (LReg 27) _ ltac:(eb_in))|].
  split; [apply eb_val_small; [lia | exact (AT (LCell XR 0x48) _ ltac:(eb_in))]|].
  split; [apply eb_val_small; [lia | exact (AT (LCell XR 0x98) _ ltac:(eb_in))]|].
  split; [apply eb_val_small; [lia | exact (AT (LCell XR 0xf0) _ ltac:(eb_in))]|].
  split; [apply eb_val_small; [unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (e_pp (x_e cx) + 0x4000) 8 ltac:(lia) ltac:(lia));
            pose proof (Z.div_le_upper_bound (e_pp (x_e cx) + 0x4000) 8 (2 ^ 47) ltac:(lia) ltac:(lia)); lia
          | exact (AT (LCell XR 0xd0) _ ltac:(eb_in))]|].
  split; [apply eb_val_small; [lia | exact (AT (LCell XR 0xe0) _ ltac:(eb_in))]|].
  split; [apply eb_val_small; [lia | exact (AT (LCell XR 0x110) _ ltac:(eb_in))]|].
  split; [apply eb_val_small; [rewrite Hlr; lia | exact (AT (LCell XR 0x118) _ ltac:(eb_in))]|].
  split; [exact (proj1 HRb)|]. split; [exact (proj1 (proj2 HRb))|]. split; [exact (proj2 (proj2 HRb))|].
  split; [exact ER16|]. split; [exact ESTK|].
  split; [exact Hown|]. split; [exact HinF|]. split; [exact EF2|].
  split; [exact HF1|]. split; [exact HF2|]. split; [exact HF32|]. split; [exact HF3|].
  split; [exact Hpp2|]. split; [exact Hp1|]. split; [exact Hp2|]. split; [exact Hsep|].
  split; [rewrite Hcur; lia|]. split; [rewrite Hcur, Hlr; lia|].
  split; [exact Ez|].
  split; [intros o Ho; exact (proj1 (HFp (e_F (x_e cx) + o) ltac:(lia)))|].
  split; [exact HraE|].
  split; [exact Hpres|].
  split; [exact HFSH|].
  exact HromD.
Qed.

(* ============================== the first block's image is PP_SIZE bytes ============================== *)
Lemma eb_pc_len : forall sh ps es, hs_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat -> (length ps <= 2)%nat ->
  Z.of_nat (length (pc_image (PbCut sh ps (Some es)))) = Layout.PP_SIZE.
Proof.
  intros sh ps es (Hsh & Hkv & Hall & Hps3) Hes Hes32 Hps2.
  assert (Hpv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [| exact Hkv]; intros kv [_ H]; exact H).
  unfold pc_image. apply length_pp_image.
  - destruct (pc_buf_len_open sh ps es Hpv Hall Hes) as [L _]. cbn [pc_shape pc_props pc_open]. unfold POD_BUF_MAX. lia.
  - unfold pc_ents. cbn [pc_props pc_open]. destruct (first_params ps) as [[iv|es']|] eqn:E; [cbn; lia | | lia].
    unfold first_params in E. destruct (find _ _) as [kv|] eqn:Fd; [|discriminate]. cbn in E. injection E as E.
    apply find_some in Fd as [Hin _]. rewrite Forall_forall in Hpv. specialize (Hpv kv Hin). rewrite E in Hpv. exact Hpv.
  - unfold pc_ents. cbn [pc_props pc_open]. destruct (first_params ps) as [[iv|es']|] eqn:E; [constructor | |].
    + unfold first_params in E. destruct (find _ _) as [kv|] eqn:Fd; [|discriminate]. cbn in E. injection E as E.
      apply find_some in Fd as [Hin _]. apply all_ents_Forall in Hall. rewrite Forall_forall in Hall.
      specialize (Hall kv Hin). rewrite E in Hall. cbn beta iota in Hall.
      eapply Forall_impl; [| exact Hall]. intros e' (_ & Hb & Hs). lia.
    + eapply Forall_impl; [| exact Hes]. intros e' (_ & Hb & Hs). lia.
Qed.

(* the shadow hull of an application range below 2^47 lies in the shadow band *)
Lemma eb_hull_band : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 - 1 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> kLowMemEnd <= s < kHighMemBeg.
Proof.
  intros x n s H0 Hn Hx Hs. unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg in *.
  assert (A1 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (A2 : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  assert (A3 : 0 <= (x + n - 1) / 8) by (apply Z.div_pos; lia).
  rewrite (Z.add_comm 0x7fff8000 (x / 8)), (Z.add_comm 0x7fff8000 ((x + n - 1) / 8)) in Hs.
  replace 0x7fff8000 with (0xffff000 * 8) in Hs by reflexivity.
  rewrite !Z.div_add in Hs by lia.
  assert (B1 : 0 <= x / 8 / 8) by (apply Z.div_pos; lia).
  assert (B2 : (x + n - 1) / 8 / 8 < 2 ^ 41) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma eb_suffix_trans : forall (rest rr r' : list byte), hs_suffix rest rr -> is_rest r' rr -> hs_suffix rest r'.
Proof.
  intros rest rr r' (j & Hj & Erj) (k & Ek). subst rr r'. rewrite skipn_skipn.
  destruct (Nat.le_gt_cases (k + j) (length rest)) as [Hle|Hgt].
  - exists (k + j)%nat. split; [exact Hle | reflexivity].
  - exists (length rest). split; [lia|]. rewrite !skipn_all2 by lia. reflexivity.
Qed.

(* ============================== the input at the case entry ============================== *)
Lemma eb_D_input : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  hs_start_M01 rsegs B cx rest ->
  hs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  garr8 rsegs (mrestrict (w_H W2) mem2) (hs_cur rsegs cx rest r) (hd_zbytes r) /\
  range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (hs_cur rsegs cx rest r) (Z.of_nat (length r)) /\
  (0 < Z.of_nat (length r) -> shadow_hull_vis (aview rsegs (w_H W2) mem2) (hs_cur rsegs cx rest r) (Z.of_nat (length r))) /\
  amem_range (hs_cur rsegs cx rest r) (Z.of_nat (length r)) /\
  (forall a, hs_cur rsegs cx rest r <= a < hs_cur rsegs cx rest r + Z.of_nat (length r) ->
     ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx) + 0x160) /\ ~ (e_F (x_e cx) + 0x20 <= a < e_F (x_e cx) + 0x158) /\
     ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE)).
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof asan_consts as (Hceil & _).
  pose proof (eb_D_facts cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (HJ & R2 & R3 & R4 & R9 & R23 & R24 & R14 & R25 & R21 & R27 & V20 & V70 & V80 & Vb0 & Vc0 & Vf0 & Vf8
     & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp & Hpp & Hpp1 & Hpp2 & Hsep
     & Hc1 & Hc2 & Ez & HFp & HraE & Hpres & HFSHD & HromD).
  destruct HST as (HPRE & _ & _ & HIN).
  destruct HPRE as (HJc & _ & HR2 & _ & _ & _ & _ & _ & _ & _ & _ & Hfsh0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hppb & _)).
  destruct HD as (HPB & _). destruct HPB as (HCORE & _ & Hsr & _).
  destruct HCORE as (_ & _ & _ & _ & _ & _ & Hkept).
  destruct HIN as (Hel & Hgar & Hra & Hhull & Hamr & Hsrc0 & Hsrc63 & Hdis).
  destruct Hsr as (j & Hj & Er).
  assert (Hlr : length r = (length rest - j)%nat) by (rewrite Er, length_skipn; reflexivity).
  assert (Hcur : hs_cur rsegs cx rest r = e_src (x_e cx) + Z.of_nat j) by (unfold hs_cur; rewrite Hlr; lia).
  assert (Hend : hs_cur rsegs cx rest r + Z.of_nat (length r) = e_src (x_e cx) + e_left (x_e cx)) by (rewrite Hcur, Hlr; lia).
  assert (Hhi : e_src (x_e cx) + e_left (x_e cx) <= 2 ^ 47 - 1).
  { unfold amem_range in Hamr. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. lia. }
  assert (HspR : spZ (x_regs cx) = e_R (x_e cx)).
  { unfold spZ. rewrite HR2. unfold w64. apply unsigned_lit_small. unfold T_SEG_STK, ASTACK in BR1. lia. }
  (* the bytes the walk may have changed since the segment's start *)
  set (Wr := fun a => ~ (0 <= a < 2 ^ 64) \/ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) \/ hs_E1 rsegs cx a).
  assert (KE : forall x, ~ Wr x -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W cx)) (x_memc cx) x).
  { intros x Hx. unfold Wr in Hx. cbv beta in Hx.
    destruct (Z_le_gt_dec 0 x) as [X0 | X0]; [| exfalso; apply Hx; left; lia].
    destruct (Z_lt_ge_dec x (2 ^ 64)) as [X1 | X1]; [| exfalso; apply Hx; left; lia].
    apply Hkept; [lia | rewrite HspR; intros X; apply Hx; right; left; exact X | intros X; apply Hx; right; right; exact X]. }
  assert (Hppin : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx))) by exact Hppb.
  pose proof HJc as (HARc & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hppin) as (_ & _ & _ & Hppapp & _).
  change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hppapp.
  assert (HFE : in_app (e_F (x_e cx) + 0x20) 0x138) by (apply (in_app_sub (e_F (x_e cx)) 1024); [exact HFapp | lia | lia | lia]).
  (* a shadow byte of an input byte avoids everything the segment may have written *)
  assert (SHW : forall x, e_src (x_e cx) <= x < e_src (x_e cx) + e_left (x_e cx) -> ~ Wr (shadow_of_addr SHADOW_OFF x)).
  { intros x Hx. pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as Hb.
    unfold kLowMemEnd, kHighMemBeg in Hb.
    intros [Hw | [Hw | Hw]]; [lia | unfold T_SEG_STK, ASTACK in *; lia |].
    destruct Hw as [Hw | Hw].
    - unfold hd_inw in Hw. cbn [hi_w1 headamp_himg_A] in Hw.
      apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
      { exact (hm_shadow_not_app x _ _ ltac:(unfold kHighMemEnd; lia) HFE ltac:(lia)). }
      apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
      { cbn [hi_shA headamp_himg_A] in Hfsh0.
        exact (hm_ra_not_fsh rsegs _ _ _ _ _ _ Hra Hfsh0 hm_sh_P0_big x Hx
          ltac:(change (length headamp_A_shA) with 80%nat; cbn [Z.of_nat]; lia)). }
      apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [unfold T_SEG_STK, ASTACK in *; lia|].
      apply Exists_nil in Hw. exact Hw.
    - exact (hm_shadow_not_app x _ _ ltac:(unfold kHighMemEnd; lia) Hppapp Hw). }
  split.
  { (* the bytes *)
    assert (B0 : hm_bytes rsegs (w_H (x_W cx)) (x_memc cx) (e_src (x_e cx)) rest) by exact Hgar.
    pose proof (hm_bytes_slice rsegs _ _ _ rest j (length rest - j) B0 ltac:(lia)) as B1.
    unfold hm_slice in B1. rewrite firstn_all2 in B1 by (rewrite length_skipn; lia). rewrite <- Er, <- Hcur in B1.
    refine (hm_bytes_kept_wr rsegs Wr _ _ _ _ _ r B1 KE _).
    intros x Hx. rewrite Hlr in Hx. destruct (Hdis x ltac:(lia)) as (D1 & D2 & D3).
    unfold Wr, hs_E1. intros [Hw | [Hw | [Hw | Hw]]]; [lia | exact (D1 Hw) | exact (D2 Hw) | exact (D3 Hw)]. }
  split.
  { (* the shadow *)
    apply (hm_ra_kept_wr rsegs Wr (w_H (x_W cx)) (x_memc cx)); [| exact KE |].
    + apply (range_addressable_sub _ _ _ _ _ _ Hra); lia.
    + intros x Hx. apply SHW. lia. }
  split.
  { (* the shadow hull *)
    intros Hn. apply (hm_hull_kept rsegs (w_H (x_W cx)) (x_memc cx)).
    + apply (hm_hull_sub _ _ _ _ _ (Hhull ltac:(lia))); lia.
    + intros s Hs Hns.
      pose proof (eb_hull_band (hs_cur rsegs cx rest r) (Z.of_nat (length r)) s ltac:(lia) Hn ltac:(lia) Hs) as Hb.
      unfold kLowMemEnd, kHighMemBeg in Hb.
      destruct (Z_lt_le_dec s (shadow_addr (e_F (x_e cx)))) as [Hs1 | Hs1];
        [| destruct (Z_lt_le_dec s (shadow_addr (e_F (x_e cx)) + 80)) as [Hs2 | Hs2]].
      2: { unfold hd_fsh in HFSHD.
        replace s with (shadow_addr (e_F (x_e cx)) + (s - shadow_addr (e_F (x_e cx)))) by lia.
        rewrite (HFSHD (s - shadow_addr (e_F (x_e cx))) ltac:(vm_compute (length hs_PJ); lia)). discriminate. }
      all: rewrite KE; [exact Hns|].
      all: intros [Hw | [Hw | [Hw | Hw]]]; [lia | unfold T_SEG_STK, ASTACK in *; lia | |
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hppapp; lia].
      all: unfold hd_inw in Hw; cbn [hi_w1 headamp_himg_A] in Hw.
      all: apply Exists_cons in Hw; destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw;
        [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFE; lia |].
      all: apply Exists_cons in Hw; destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [lia|].
      all: apply Exists_cons in Hw; destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [unfold T_SEG_STK, ASTACK in *; lia|].
      all: apply Exists_nil in Hw; exact Hw. }
  split.
  - unfold amem_range in *. lia.
  - intros a Ha. destruct (Hdis a ltac:(lia)) as (D1 & D2 & D3). split; [| split; [| exact D3]].
    + intros Hx. apply D2. unfold hd_inw. cbn [hi_w1 headamp_himg_A].
      apply Exists_cons. right. apply Exists_cons. right. apply Exists_cons. left. cbn [fst snd hd_xv].
      destruct (Z_lt_le_dec a (e_R (x_e cx))) as [Hl|Hl]; [exfalso; apply D1; lia | lia].
    + intros Hx. apply D2. unfold hd_inw. cbn [hi_w1 headamp_himg_A]. apply Exists_cons. left. cbn [fst snd hd_xv]. lia.
Qed.

(* ============================== what the walk kept since the segment's start ============================== *)
(* the bytes [lo, hi) lie in one segment of the image *)
Definition eb_in_seg_b (lo hi : Z) : bool :=
  existsb (fun sg => (Z.of_N (seg_base sg) <=? lo) && (hi <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) rsegs.
Lemma eb_in_seg : forall lo hi a, eb_in_seg_b lo hi = true -> lo <= a < hi -> in_img rsegs a.
Proof.
  intros lo hi a Hb Ha. unfold eb_in_seg_b in Hb. apply existsb_exists in Hb as (sg & Hin & Hs).
  apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hin | lia].
Qed.

(* The walk writes only the callees' stack below R and hs_E1 (F's objects [F+0x20, F+0x158), F's 80 shadow bytes,
   the real frame's cells [R, R+0x160) and the block pp). None of them meets an image byte (the frame and the block
   are not in the image, R is above alloc_ceiling), and only F's shadow bytes lie in the shadow map's band
   [kLowMemEnd, kHighMemBeg) (the frame and the block are application ranges, R is above kHighMemBeg). *)
Lemma eb_D_keep : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  hs_start_M01 rsegs B cx rest ->
  hs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  (forall a, in_img rsegs a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a) /\
  (forall s, kLowMemEnd <= s < kHighMemBeg ->
     ~ (shadow_addr (e_F (x_e cx)) <= s < shadow_addr (e_F (x_e cx)) + 80) ->
     aview rsegs (w_H W2) mem2 s = aview rsegs (w_H (x_W cx)) (x_memc cx) s).
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof asan_consts as (Hceil & _).
  pose proof (eb_D_facts cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (HJ & R2 & R3 & R4 & R9 & R23 & R24 & R14 & R25 & R21 & R27 & V20 & V70 & V80 & Vb0 & Vc0 & Vf0 & Vf8
     & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp & Hpp & Hpp1 & Hpp2 & Hsep
     & Hc1 & Hc2 & Ez & HFp & HraE & Hpres & HFSHD & HromD).
  destruct HST as (HPRE & _ & _ & _).
  destruct HPRE as (_ & _ & HR2 & _).
  destruct HD as (HPB & _). destruct HPB as (HCORE & _).
  destruct HCORE as (_ & _ & _ & _ & _ & _ & Hkept).
  pose proof HJ as (HAR & _).
  assert (HTS : T_SEG_STK = 16384) by reflexivity. rewrite HTS in BR1.
  assert (HspR : spZ (x_regs cx) = e_R (x_e cx)).
  { unfold spZ. rewrite HR2. unfold w64. apply unsigned_lit_small. lia. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (_ & _ & _ & Hppapp & _).
  change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hppapp.
  split.
  - intros a Himg. pose proof (HPgSteps.img_segs_low a Himg) as Hlow. unfold kLowMemEnd in Hlow.
    apply Hkept; [lia | rewrite HspR, HTS; lia |].
    unfold hs_E1. intros [Hw | Hw].
    2: { apply (blk_img rsegs B LAWS _ _ _ _ _ _ _ a HAR Hpp); [| exact Himg].
         change (req_size Layout.PP_SIZE) with Layout.PP_SIZE. lia. }
    unfold hd_inw in Hw. cbn [hi_w1 headamp_himg_A] in Hw.
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
    { apply (frm_img rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) a HAR HinF); [| exact Himg].
      rewrite <- EF2. change (fs_frame_bytes 4) with 1024. lia. }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
    { unfold shadow_addr, SHADOW_OFF in Hw. pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)). lia. }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [lia|].
    apply Exists_nil in Hw. exact Hw.
  - intros s Hs HnF. unfold kLowMemEnd, kHighMemBeg in Hs.
    apply Hkept; [lia | rewrite HspR, HTS; lia |].
    unfold hs_E1. intros [Hw | Hw].
    2: { unfold in_app, kLowShadowBeg, kHighMemBeg, Layout.PP_SIZE in Hppapp. unfold Layout.PP_SIZE in Hw. lia. }
    unfold hd_inw in Hw. cbn [hi_w1 headamp_himg_A] in Hw.
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
    { unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. lia. }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [lia|].
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [lia|].
    apply Exists_nil in Hw. exact Hw.
Qed.

Lemma eb_shA_len : Z.of_nat (length headamp_A_shA) = 80.
Proof. vm_compute. reflexivity. Qed.

(* the image's segments start and end on 8-byte boundaries, so the 8-byte word of an image byte is image bytes *)
Lemma eb_segs_al8 : forallb (fun sg => (Z.of_N (seg_base sg) mod 8 =? 0) && (Z.of_N (seg_size sg) mod 8 =? 0)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma eb_img_word : forall x y, in_img rsegs x -> x <= y < x - x mod 8 + 8 -> in_img rsegs y.
Proof.
  intros x y (sg & Hin & Hx) Hy. exists sg. split; [exact Hin|].
  pose proof (proj1 (forallb_forall _ _) eb_segs_al8 sg Hin) as Hq. apply andb_prop in Hq as [Hb Hs].
  apply Z.eqb_eq in Hb. apply Z.eqb_eq in Hs.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  pose proof (Z.div_mod (Z.of_N (seg_base sg)) 8 ltac:(lia)). pose proof (Z.div_mod (Z.of_N (seg_size sg)) 8 ltac:(lia)).
  assert (E : Z.of_N (seg_base sg) + Z.of_N (seg_size sg) = 8 * (Z.of_N (seg_base sg) / 8 + Z.of_N (seg_size sg) / 8)) by lia.
  assert (x / 8 < Z.of_N (seg_base sg) / 8 + Z.of_N (seg_size sg) / 8) by lia.
  lia.
Qed.

(* A string of the image (hd_cstr) at a later state. Its bytes and its NUL are image bytes; the shadow bytes of
   its bytes are outside F's shadow bytes (at the earlier state they mark the string usable, and the prologue's
   pattern marks no byte of F usable); a shadow byte of its hull is one of F's shadow bytes (present at the later
   state) or kept. *)
Lemma eb_cstr_kept : forall H mem H' mem' F pat a s,
  hd_cstr rsegs H mem a s ->
  hd_fsh rsegs H mem F headamp_A_shA -> hd_fsh rsegs H' mem' F pat -> Z.of_nat (length pat) = 80 ->
  (forall x, in_img rsegs x -> aview rsegs H' mem' x = aview rsegs H mem x) ->
  (forall u, kLowMemEnd <= u < kHighMemBeg -> ~ (shadow_addr F <= u < shadow_addr F + 80) ->
     aview rsegs H' mem' u = aview rsegs H mem u) ->
  hd_cstr rsegs H' mem' a s.
Proof.
  intros H mem H' mem' F pat a s (Hb & Hn & Hf & Ha0 & Ha63 & Himg & Ham & Hra & Hhull & Htl) P0 PJ PJlen K1 K2.
  assert (Hlow : forall i, 0 <= i <= Z.of_nat (length s) -> 0 <= a + i < kLowMemEnd)
    by (intros i Hi; exact (HPgSteps.img_segs_low _ (Himg i Hi))).
  pose proof (Hlow (Z.of_nat (length s)) ltac:(lia)) as Hend. unfold kLowMemEnd in Hend, Hlow.
  split; [intros i Hi; rewrite K1 by (apply Himg; lia); exact (Hb i Hi)|].
  split; [rewrite K1 by (apply Himg; lia); exact Hn|].
  do 5 (split; [assumption|]).
  split; [|split].
  - apply (hm_ra_kept rsegs H mem); [exact Hra|]. intros x Hx.
    pose proof (Hlow (x - a) ltac:(lia)) as Hx'.
    pose proof (hm_ra_not_fsh rsegs H mem F headamp_A_shA a _ Hra P0 hm_sh_P0_big x Hx) as HnF.
    rewrite eb_shA_len in HnF.
    apply K2; [apply hm_shadow_band; unfold kHighMemEnd; lia | exact HnF].
  - apply (hm_hull_kept rsegs H mem); [exact Hhull|]. intros u Hu Hne.
    pose proof (eb_hull_band a (Z.of_nat (length s) + 1) u ltac:(lia) ltac:(lia) ltac:(lia) Hu) as Hband.
    destruct (Z_lt_le_dec u (shadow_addr F)) as [Hu1 | Hu1];
      [| destruct (Z_lt_le_dec u (shadow_addr F + 80)) as [Hu2 | Hu2]].
    2: { replace u with (shadow_addr F + (u - shadow_addr F)) by lia.
         rewrite (PJ (u - shadow_addr F) ltac:(rewrite PJlen; lia)). discriminate. }
    all: rewrite K2; [exact Hne | exact Hband | lia].
  - (* the rest of the NUL's 8-byte word: image bytes, kept *)
    intros y Hy. rewrite K1; [exact (Htl y Hy)|].
    apply (eb_img_word (a + Z.of_nat (length s))); [apply Himg; lia | lia].
Qed.

(* ============================== the case blocks' premises at a case entry ============================== *)
Lemma eb_D_w6b : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  hs_start_M01 rsegs B cx rest ->
  hs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  HPgW6aBase.w6_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) (x_k cx) ly2 S2 W2 mem2 md2 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx) /\
  HPgW6bBase.w6b_in B W2 mem2 regs2 (e_R (x_e cx)) (e_F (x_e cx)) (hs_cur rsegs cx rest r)
    (shadow_addr (e_pp (x_e cx) + 0x4000)) (e_pp (x_e cx)) kd r.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof asan_consts as (Hceil & _).
  pose proof (eb_D_facts cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (HJ & R2 & R3 & R4 & R9 & R23 & R24 & R14 & R25 & R21 & R27 & V20 & V70 & V80 & Vb0 & Vc0 & Vf0 & Vf8
     & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp & Hpp & Hpp1 & Hpp2 & Hsep
     & Hc1 & Hc2 & Ez & HFp & HraE & Hpres & HFSHD & HromD).
  pose proof (eb_D_input cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (Igar & Ira & Ihull & Iam & Idis).
  pose proof HD as (HPB & HAT & _ & _ & _ & Hsrr & Hfu & Hkd & Hrr).
  pose proof HPB as (_ & HIN & _).
  pose proof HIN as (_ & _ & _ & _ & _ & Hsrc0 & _).
  unfold Layout.PP_SIZE in Hpp2.
  (* the cursor is past the kind byte *)
  assert (Hlr : (S (length r) <= length rest)%nat).
  { destruct Hsrr as (j & Hj & Ej). destruct rr as [|b r0]; [congruence|].
    cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as _ Er. subst r0.
    assert (L : length (b :: r) = length (skipn j rest)) by (rewrite <- Ej; reflexivity).
    rewrite length_skipn in L. cbn [length] in L. lia. }
  assert (Hc0 : 0 < hs_cur rsegs cx rest r - 1) by (unfold hs_cur; lia).
  split.
  - unfold HPgW6aBase.w6_ctx. split; [exact HJ|]. split; [exact BR4|]. split; [exact BR2|]. split; [exact BR5|].
    split; [exact Hown|]. split; [exact EF2|]. exact HromD.
  - unfold HPgW6bBase.w6b_in.
    split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R9|]. split; [exact R23|].
    split; [exact R24|]. split; [exact R14|]. split; [exact R25|]. split; [exact R21|]. split; [exact R27|].
    split.
    { (* s4 holds the sign-extended kind byte on the nine table entries *)
      intros H9. assert (E9 : (kd mod 10 =? 9) = false) by (apply Z.eqb_neq; exact H9).
      exact (eb_at _ _ _ _ _ (LReg 20) (kd - 256 * (kd / 128)) HAT ltac:(unfold hs_L_D; rewrite E9; eb_in)). }
    split; [exact Vf8|]. split; [exact Vb0|]. split; [exact Vf0|]. split; [exact Vc0|]. split; [exact V20|].
    split; [exact V70|]. split; [exact V80|].
    split.
    { unfold shadow_addr, SHADOW_OFF.
      pose proof (Z.div_pos (e_pp (x_e cx) + 0x4000) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound (e_pp (x_e cx) + 0x4000) 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
    split; [exact Hkd|]. split; [exact Hpp1|]. split; [lia|].
    split; [exact HF1|]. split; [exact HF2|]. split; [exact HF32|].
    split; [exact Ez|]. split; [exact HraE|].
    split.
    { (* e's shadow hull: shadow bytes 23 .. 49 of F's 80, which the frame's shadow pattern gives *)
      assert (Hq : exists q, e_F (x_e cx) = 32 * q).
      { apply (proj1 (Z.mod_divide (e_F (x_e cx)) 32 ltac:(discriminate))) in HF32. destruct HF32 as [q Hq].
        exists q. lia. }
      destruct Hq as [q Hq].
      assert (EsF : shadow_addr (e_F (x_e cx)) = SHADOW_OFF + 4 * q).
      { unfold shadow_addr. rewrite Hq. f_equal. replace (32 * q) with ((4 * q) * 8) by ring. apply Z.div_mul. lia. }
      assert (LPJ : Z.of_nat (length hs_PJ) = 80) by (vm_compute; reflexivity).
      unfold shadow_hull_vis. intros s Hs. unfold shadow_addr in Hs. rewrite Hq in Hs.
      assert (A1 : (32 * q + 0xf0) / 8 = 4 * q + 30)
        by (replace (32 * q + 0xf0) with ((4 * q + 30) * 8) by ring; apply Z.div_mul; lia).
      assert (A2 : (32 * q + 0xf0 + 104 - 1) / 8 = 4 * q + 42)
        by (replace (32 * q + 0xf0 + 104 - 1) with ((4 * q + 42) * 8 + 7) by ring; rewrite Z.div_add_l by lia;
            change (7 / 8) with 0; ring).
      rewrite A1, A2 in Hs.
      pose proof (Z.div_mod (SHADOW_OFF + (4 * q + 30)) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (SHADOW_OFF + (4 * q + 30)) 8 ltac:(lia)).
      pose proof (Z.div_mod (SHADOW_OFF + (4 * q + 42)) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (SHADOW_OFF + (4 * q + 42)) 8 ltac:(lia)).
      replace s with (shadow_addr (e_F (x_e cx)) + (s - shadow_addr (e_F (x_e cx)))) by lia.
      rewrite (HFSHD (s - shadow_addr (e_F (x_e cx))) ltac:(rewrite LPJ, EsF; lia)). discriminate. }
    split; [exact Hc0|].
    split.
    { unfold HPgW6aBase.w6_in. split; [exact Igar|]. split; [exact Ira|]. split; [lia|]. split; [lia|].
      split; [exact Iam|]. intros a Ha. exact (proj1 (Idis a Ha)). }
    split; [exact Ihull|].
    intros a Ha. exact (proj1 (proj2 (Idis a Ha))).
Qed.

(* ============================== what cases 9 and 1 read of the image ============================== *)
Ltac eb_in_l := repeat (first [left; vm_compute; reflexivity | right]).
Lemma eb_D_img : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  hs_start_M01 rsegs B cx rest ->
  hs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  HPgW6bBase.w6b_s_ok W2 mem2 /\ HPgW6bBase.w6b_vocab_ok W2 mem2.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof (eb_D_keep cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as (K1 & K2).
  pose proof HD as (_ & _ & HFSH & _). unfold hs_fsh_at in HFSH.
  destruct HST as (HPRE & _).
  destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfsh0 & _ & _ & _ & Hglobs & _ & Hstrs & Hcells & _).
  cbn [hi_shA hi_globs hi_strs hi_cells headamp_himg_A] in Hfsh0, Hglobs, Hstrs, Hcells.
  assert (LPJ : Z.of_nat (length hs_PJ) = 80) by (vm_compute; reflexivity).
  (* the image's strings, its registered globals and its cells at the case entry *)
  assert (KS : forall a s, In (a, s) headamp_A_strs -> hd_cstr rsegs (w_H W2) mem2 a s).
  { intros a s Hin. apply (eb_cstr_kept (w_H (x_W cx)) (x_memc cx) (w_H W2) mem2 (e_F (x_e cx)) hs_PJ a s).
    - exact (proj1 (Forall_forall _ _) Hstrs (a, s) Hin).
    - exact Hfsh0.
    - exact HFSH.
    - exact LPJ.
    - exact K1.
    - exact K2. }
  assert (KR : forall a n, (forall x, a <= x < a + n -> in_img rsegs x) ->
    range_addressable (aview rsegs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF a n ->
    range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF a n).
  { intros a n Himg Hra. apply (hm_ra_kept rsegs (w_H (x_W cx)) (x_memc cx)); [exact Hra|]. intros x Hx.
    pose proof (HPgSteps.img_segs_low x (Himg x Hx)) as Hlow. unfold kLowMemEnd in Hlow.
    apply K2; [apply hm_shadow_band; unfold kHighMemEnd; lia|].
    pose proof (hm_ra_not_fsh rsegs _ _ _ _ a n Hra Hfsh0 hm_sh_P0_big x Hx) as HnF.
    rewrite eb_shA_len in HnF. exact HnF. }
  assert (Hvc : eb_in_seg_b HPgW6bBase.W6B_VOCAB (HPgW6bBase.W6B_VOCAB + 72) = true) by (vm_compute; reflexivity).
  split.
  - (* ent_build.s *)
    unfold HPgW6bBase.w6b_s_ok, HPgW6bBase.W6B_S. apply KS. unfold headamp_A_strs. cbn [In]. eb_in_l.
  - unfold HPgW6bBase.w6b_vocab_ok. split.
    { (* the registered table ent_build.vocab *)
      apply KR; [intros x Hx; exact (eb_in_seg _ _ x Hvc Hx)|].
      exact (proj1 (Forall_forall _ _) Hglobs (HPgW6bBase.W6B_VOCAB, 72)
        ltac:(unfold headamp_A_globs; cbn [In]; eb_in_l)). }
    intros i Hi.
    assert (Ei : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
    split.
    + (* the cell vocab[i] *)
      assert (HinC : In (HPgW6bBase.W6B_VOCAB + 8 * i, HPgW6bBase.w6b_vptr i) headamp_A_cells).
      { unfold headamp_A_cells.
        repeat (destruct Ei as [Ei|Ei]; [subst i; cbn [In]; eb_in_l|]). subst i. cbn [In]. eb_in_l. }
      unfold hd_ro_cells in Hcells.
      pose proof (proj1 (Forall_forall _ _) Hcells _ HinC) as V0. cbn [fst snd] in V0.
      apply hm_val_of_bytes. apply (hm_bytes_kept rsegs (w_H (x_W cx)) (x_memc cx)).
      { apply hm_bytes_of_val. exact V0. }
      intros x Hx. change (Z.of_nat (length (Z_to_le_bytes 8 (HPgW6bBase.w6b_vptr i)))) with 8 in Hx.
      apply K1. apply (eb_in_seg _ _ x Hvc). unfold HPgW6bBase.W6B_VOCAB in *. lia.
    + (* the string vocab[i] points to *)
      apply KS.
      unfold headamp_A_strs.
      repeat (destruct Ei as [Ei|Ei]; [subst i; cbn [In]; eb_in_l|]). subst i. cbn [In]. eb_in_l.
Qed.

(* ============================== the join ============================== *)
Lemma eb_J_of : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ed r',
  hs_start_M01 rsegs B cx rest ->
  hs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall rg : Z, In rg [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 26; 27] ->
     getr regs3 (Z_to_bv 5 rg) = getr regs2 (Z_to_bv 5 rg)) ->
  getr regs3 20 = w64 (shadow_addr (e_pp (x_e cx) + 0x4000)) ->
  getr regs3 25 = w64 (hs_cur rsegs cx rest r') ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) ->
     ~ (e_R (x_e cx) + 0x68 <= a < e_R (x_e cx) + 0x70) -> ~ (e_R (x_e cx) + 0x118 <= a < e_R (x_e cx) + 0x120) ->
     ~ (e_F (x_e cx) + 0xf0 <= a < e_F (x_e cx) + 0x158) ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_R (x_e cx) + 0x118) 8 (Z.of_nat (length r')) ->
  garr8 rsegs (mrestrict (w_H W2) mem3) (e_F (x_e cx) + 0xf0) (hd_zbytes (ent_mem ed)) ->
  (ed, r') = ent_build rr ->
  hs_cut_J rsegs B MT cx sh np ps cnt es rest rr r' ed ly2 S2 W2 regs3 mem3 md3.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ed r' HST HD HJ3 Hio3 Hregs H20 H25
    K3 V3 E3 Hed.
  pose proof asan_consts as (Hceil & _).
  pose proof (eb_D_facts cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (HJ & R2 & R3 & R4 & R9 & R23 & R24 & R14 & R25 & R21 & R27 & V20 & V70 & V80 & Vb0 & Vc0 & Vf0 & Vf8
     & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp & Hpp & Hpp1 & Hpp2 & Hsep
     & Hc1 & Hc2 & Ez & HFp & HraE & Hpres & HFSHD & HromD).
  assert (HTS : T_SEG_STK = 16384) by reflexivity. rewrite HTS in BR1, BR5.
  destruct HD as (HPB & HAT & HFSH & HPP & HE0 & Hsrr & Hfu & Hkd & Hrr).
  destruct HPB as (HCORE & HIN' & Hsr & Hsrr' & Hwf & Hlen' & Hps & Htie & Hsh & Hnp & Hlp & Hnp3 & Hsh7 & Hps2 & Hcnt
    & Hesw & Hes32 & Hesc).
  destruct HCORE as (_ & Hspr & Hfr & Hperm & Hio & Hmo & Hkept).
  (* what the case may have written since the case entry *)
  set (Wr := fun a => ~ (0 <= a < 2 ^ 64) \/ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) \/
    (e_R (x_e cx) + 0x68 <= a < e_R (x_e cx) + 0x70) \/ (e_R (x_e cx) + 0x118 <= a < e_R (x_e cx) + 0x120) \/
    (e_F (x_e cx) + 0xf0 <= a < e_F (x_e cx) + 0x158)).
  assert (KE : forall x, ~ Wr x -> aview rsegs (w_H W2) mem3 x = aview rsegs (w_H W2) mem2 x).
  { intros x Hx. unfold Wr in Hx.
    (* intuitionistic: 0 <= x < 2 ^ 64 is decidable, so no excluded middle is needed *)
    assert (Hx0 : 0 <= x < 2 ^ 64).
    { destruct (Z_le_gt_dec 0 x) as [H0|H0]; [|exfalso; apply Hx; left; lia].
      destruct (Z_lt_ge_dec x (2 ^ 64)) as [H1|H1]; [lia|exfalso; apply Hx; left; lia]. }
    apply K3; [exact Hx0
              | intros H; apply Hx; right; left; exact H
              | intros H; apply Hx; right; right; left; exact H
              | intros H; apply Hx; right; right; right; left; exact H
              | intros H; apply Hx; right; right; right; right; exact H]. }
  assert (HspR : spZ (x_regs cx) = e_R (x_e cx)).
  { unfold spZ. pose proof (Hspr 2 ltac:(lia)) as X.
    assert (X2 : getr (x_regs cx) 2 = w64 (e_R (x_e cx))) by (rewrite <- R2; symmetry; exact X).
    rewrite X2. unfold w64. apply unsigned_lit_small. lia. }
  pose proof (eb_pc_len sh ps es Hwf Hesw Hes32 Hps2) as Hlpp.
  unfold hs_cut_J. split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* the pod loop's base *)
    unfold hs_pod_base. split.
    { unfold hs_core, hs_mid. split; [exact HJ3|]. split.
      { intros rg Hrg. rewrite (Hregs rg ltac:(cbn; lia)). exact (Hspr rg Hrg). }
      split; [exact Hfr|]. split; [exact Hperm|]. split; [exact (same_io_trans _ _ _ Hio Hio3)|]. split; [exact Hmo|].
      intros a Ha Hs HE1. rewrite KE; [exact (Hkept a Ha Hs HE1)|]. rewrite HspR in Hs.
      unfold Wr. intros [Hw | [Hw | Hw]]; [lia | exact (Hs Hw) |]. apply HE1. unfold hs_E1, hd_inw. left.
      cbn [hi_w1 headamp_himg_A].
      destruct Hw as [Hw | [Hw | Hw]].
      - apply Exists_cons. right. apply Exists_cons. right. apply Exists_cons. left. cbn [fst snd hd_xv]. lia.
      - apply Exists_cons. right. apply Exists_cons. right. apply Exists_cons. left. cbn [fst snd hd_xv]. lia.
      - apply Exists_cons. left. cbn [fst snd hd_xv]. lia. }
    split; [exact HIN'|].
    split; [exact (eb_suffix_trans rest rr r' Hsrr' ltac:(pose proof (ent_build_rest rr) as X; rewrite <- Hed in X; exact X))|].
    repeat (split; [eassumption|]). exact Hesc.
  - (* the registers and cells *)
    assert (SUB : forall f, In f (hs_Rc rsegs cx) \/ In f (hs_L_Dc rsegs cx sh np ps cnt es) ->
      In f (hs_L_D rsegs cx sh np ps cnt es rest r kd)).
    { intros f Hf. unfold hs_L_D. apply in_or_app. left. destruct Hf as [Hf | Hf]; [| exact Hf].
      unfold hs_Rc in Hf. unfold hs_L_Dc, hs_L_Dc0. apply in_app_or in Hf as [Hf | Hf].
      - apply in_or_app. left. apply in_or_app. left. exact Hf.
      - apply in_or_app. right. exact Hf. }
    unfold hs_at_cx, hs_at. apply Forall_forall. intros [l v] Hf.
    apply in_app_or in Hf as [Hf | Hf]; [| apply in_app_or in Hf as [Hf | Hf]].
    + apply (hm_at_kept rsegs _ _ _ _ regs2 regs3 (x_e cx) l v (eb_at _ _ _ _ _ l v HAT (SUB _ (or_introl Hf)))).
      apply (hm_keeps_of rsegs Wr _ _ _ _ _ _ _ l KE).
      cbn [hs_Rc hs_Rc0 app In] in Hf.
      repeat (destruct Hf as [Hf|Hf]; [injection Hf as <- <-; solve [apply Hregs; cbn [In]; repeat (first [left; reflexivity | right])]|]).
      destruct Hf.
    + apply (hm_at_kept rsegs _ _ _ _ regs2 regs3 (x_e cx) l v (eb_at _ _ _ _ _ l v HAT (SUB _ (or_intror Hf)))).
      apply (hm_keeps_of rsegs Wr _ _ _ _ _ _ _ l KE).
      cbn [hs_L_Dc hs_L_Dc0 hs_Rc0 hs_Kc app In] in Hf.
      repeat (destruct Hf as [Hf|Hf];
        [injection Hf as <- <-; first [solve [apply Hregs; cbn [In]; repeat (first [left; reflexivity | right])]
                                      | intros i Hi; unfold Wr; rewrite HTS; cbn [hd_xv]; lia] |]).
      destruct Hf.
    + cbn [In] in Hf. destruct Hf as [E | [E | [E | []]]]; injection E as <- <-; cbn [hd_at].
      * exact H20.
      * exact H25.
      * apply eb_val_mod; [| exact V3].
        assert (Hb : Z.of_nat (length r') <= 2 ^ 47).
        { pose proof (ent_build_rest rr) as (k0 & Ek0). rewrite <- Hed in Ek0. cbn [snd] in Ek0.
          destruct Hsrr' as (j & Hj & Ej). destruct HIN' as (Hel & _ & _ & _ & Hamr & Hsrc0 & _).
          unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr.
          assert (Hlen : (length r' <= length rest)%nat) by (rewrite Ek0, Ej, !length_skipn; lia).
          apply Nat2Z.inj_le in Hlen. lia. }
        split; [apply Nat2Z.is_nonneg | eapply Z.le_lt_trans; [exact Hb | reflexivity]].
  - (* the frame's shadow *)
    unfold hs_fsh_at. apply (hm_fsh_kept rsegs (w_H W2) mem2). { exact HFSH. }
    intros i Hi. apply KE. vm_compute (length hs_PJ) in Hi.
    unfold shadow_addr, SHADOW_OFF in *. pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (e_F (x_e cx)) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_mod (e_F (x_e cx)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_F (x_e cx)) 8 ltac:(lia)).
    unfold Wr. rewrite HTS. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia.
  - (* the first block *)
    unfold hs_pp_at. unfold hs_pp_at in HPP.
    refine (hm_bytes_kept_wr rsegs Wr (w_H W2) mem2 (w_H W2) mem3 _ _ HPP KE _).
    intros x Hx. rewrite Hlpp in Hx. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
    unfold Wr. rewrite HTS. lia.
  - exact E3.
  - exact Hed.
  - pose proof (ent_build_wf rr) as X. rewrite <- Hed in X. exact X.
Qed.

(* ============================== the join, from a case block's post ============================== *)
Section J.
Hypothesis MTL : ameter_laws MT.
Lemma eb_J_post : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 W3 c3,
  hs_start_M01 rsegs B cx rest ->
  hs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  HPgW6aBase.w6_post B MT (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) (x_k cx) regs2 ly2 S2 W2 mem2 md2 HPgW6aBase.W6_J HPgW6bBase.w6b_clob
    (HPgW6bBase.w6b_wr (e_R (x_e cx)) (e_F (x_e cx)))
    (HPgW6bBase.w6b_J_R (e_R (x_e cx)) (e_F (x_e cx)) (hs_cur rsegs cx rest r)
      (shadow_addr (e_pp (x_e cx) + 0x4000)) (e_pp (x_e cx)) r rr) W3 c3 ->
  exists regs3 mem3 md3 ly3 S3, c3 = cfg_at rsegs HPgW6aBase.W6_J regs3 mem3 md3 /\
    hs_cut_J rsegs B MT cx sh np ps cnt es rest rr (snd (ent_build rr)) (fst (ent_build rr)) ly3 S3 W3 regs3 mem3 md3.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 W3 c3 HST HD HP.
  destruct HP as (ly3 & S3 & regs3 & mem3 & md3 & Ec & HJ3 & Hr3 & Hf3 & Hp3 & Hio3 & Hmo3 & Hm3 & HR3).
  destruct HR3 as (H20 & H21 & H27 & H25 & V3 & E3).
  exists regs3, mem3, md3, ly3, S3. split; [exact Ec|].
  pose proof asan_consts as (Hceil & _).
  pose proof (eb_D_facts cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (HJ & R2 & R3 & R4 & R9 & R23 & R24 & R14 & R25 & R21 & R27 & V20 & V70 & V80 & Vb0 & Vc0 & Vf0 & Vf8
     & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp & Hpp & Hpp1 & Hpp2 & Hsep
     & Hc1 & Hc2 & Ez & HFp & HraE & Hpres & HFSHD & HromD).
  assert (HTS : T_SEG_STK = 16384) by reflexivity. rewrite HTS in BR1, BR5.
  destruct HD as (HPB & HAT & HFSH & HPP & HE0 & Hsrr & Hfu & Hkd & Hrr).
  destruct HPB as (HCORE & HIN' & Hsr & Hsrr' & Hwf & Hlen' & Hps & Htie & Hsh & Hnp & Hlp & Hnp3 & Hsh7 & Hps2 & Hcnt
    & Hesw & Hes32 & Hesc).
  destruct HCORE as (_ & Hspr & Hfr & Hperm & Hio & Hmo & Hkept).
  (* the registers: the case keeps those outside w6b_clob and reloads s5 and s11 *)
  assert (NK : forall rg : bv 5, existsb (fun c => bv_eqb c rg) HPgW6bBase.w6b_clob = false ->
    ~ In rg HPgW6bBase.w6b_clob).
  { intros rg Hb Hin. assert (Ht : existsb (fun c => bv_eqb c rg) HPgW6bBase.w6b_clob = true)
      by (apply existsb_exists; exists rg; split; [exact Hin | unfold bv_eqb; apply Z.eqb_refl]).
    rewrite Hb in Ht. discriminate Ht. }
  assert (Hregs : forall rg : Z, In rg [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 26; 27] ->
    getr regs3 (Z_to_bv 5 rg) = getr regs2 (Z_to_bv 5 rg)).
  { intros rg Hrg. cbn [In] in Hrg.
    repeat (destruct Hrg as [<- | Hrg];
      [first [ exact (eq_trans H21 (eq_sym R21)) | exact (eq_trans H27 (eq_sym R27))
             | apply Hr3; [vm_compute; intros X; discriminate X | apply NK; vm_compute; reflexivity] ] |]).
    destruct Hrg. }
  (* what the case may have written since the case entry *)
  set (Wr := fun a => ~ (0 <= a < 2 ^ 64) \/ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) \/
    (e_R (x_e cx) + 0x68 <= a < e_R (x_e cx) + 0x70) \/ (e_R (x_e cx) + 0x118 <= a < e_R (x_e cx) + 0x120) \/
    (e_F (x_e cx) + 0xf0 <= a < e_F (x_e cx) + 0x158)).
  assert (KE : forall x, ~ Wr x -> aview rsegs (w_H W3) mem3 x = aview rsegs (w_H W2) mem2 x).
  { intros x Hx. unfold Wr in Hx. cbv beta in Hx.
    destruct (Z_le_gt_dec 0 x) as [X0 | X0]; [| exfalso; apply Hx; left; lia].
    destruct (Z_lt_ge_dec x (2 ^ 64)) as [X1 | X1]; [| exfalso; apply Hx; left; lia].
    apply Hm3; [lia|]. unfold HPgW6bBase.w6b_wr. intros X. apply Hx. right. exact X. }
  assert (HspR : spZ (x_regs cx) = e_R (x_e cx)).
  { unfold spZ. pose proof (Hspr 2 ltac:(lia)) as X.
    assert (X2 : getr (x_regs cx) 2 = w64 (e_R (x_e cx))) by (rewrite <- R2; symmetry; exact X).
    rewrite X2. unfold w64. apply unsigned_lit_small. lia. }
  assert (LPJ : Z.of_nat (length hs_PJ) = 80) by (vm_compute; reflexivity).
  pose proof (eb_pc_len sh ps es Hwf Hesw Hes32 Hps2) as Hlpp.
  unfold hs_cut_J. split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* the pod loop's base *)
    unfold hs_pod_base. split.
    { unfold hs_core, hs_mid. split; [exact HJ3|]. split.
      { intros rg Hrg. rewrite (Hregs rg ltac:(cbn; lia)). exact (Hspr rg Hrg). }
      split; [rewrite Hf3; exact Hfr|]. split; [eapply Permutation_trans; [exact Hp3 | exact Hperm]|].
      split; [exact (same_io_trans _ _ _ Hio Hio3)|].
      split; [exact (mle_station MT _ _ _ 0 0 MTL Hmo Hmo3)|].
      intros a Ha Hs HE1. rewrite KE; [exact (Hkept a Ha Hs HE1)|]. rewrite HspR in Hs.
      unfold Wr. intros [Hw | [Hw | Hw]]; [lia | exact (Hs Hw) |]. apply HE1. unfold hs_E1, hd_inw. left.
      cbn [hi_w1 headamp_himg_A].
      destruct Hw as [Hw | [Hw | Hw]].
      - apply Exists_cons. right. apply Exists_cons. right. apply Exists_cons. left. cbn [fst snd hd_xv]. lia.
      - apply Exists_cons. right. apply Exists_cons. right. apply Exists_cons. left. cbn [fst snd hd_xv]. lia.
      - apply Exists_cons. left. cbn [fst snd hd_xv]. lia. }
    split; [exact HIN'|].
    split; [exact (eb_suffix_trans rest rr _ Hsrr' (ent_build_rest rr))|].
    repeat (split; [eassumption|]). exact Hesc.
  - (* the registers and cells *)
    assert (SUB : forall f, In f (hs_Rc rsegs cx) \/ In f (hs_L_Dc rsegs cx sh np ps cnt es) ->
      In f (hs_L_D rsegs cx sh np ps cnt es rest r kd)).
    { intros f Hf. unfold hs_L_D. apply in_or_app. left. destruct Hf as [Hf | Hf]; [| exact Hf].
      unfold hs_Rc in Hf. unfold hs_L_Dc, hs_L_Dc0. apply in_app_or in Hf as [Hf | Hf].
      - apply in_or_app. left. apply in_or_app. left. exact Hf.
      - apply in_or_app. right. exact Hf. }
    unfold hs_at_cx, hs_at. apply Forall_forall. intros [l v] Hf.
    apply in_app_or in Hf as [Hf | Hf]; [| apply in_app_or in Hf as [Hf | Hf]].
    + apply (hm_at_kept rsegs _ _ _ _ regs2 regs3 (x_e cx) l v (eb_at _ _ _ _ _ l v HAT (SUB _ (or_introl Hf)))).
      apply (hm_keeps_of rsegs Wr _ _ _ _ _ _ _ l KE).
      cbn [hs_Rc hs_Rc0 app In] in Hf.
      repeat (destruct Hf as [Hf|Hf]; [injection Hf as <- <-; solve [apply Hregs; cbn [In]; repeat (first [left; reflexivity | right])]|]).
      destruct Hf.
    + apply (hm_at_kept rsegs _ _ _ _ regs2 regs3 (x_e cx) l v (eb_at _ _ _ _ _ l v HAT (SUB _ (or_intror Hf)))).
      apply (hm_keeps_of rsegs Wr _ _ _ _ _ _ _ l KE).
      cbn [hs_L_Dc hs_L_Dc0 hs_Rc0 hs_Kc app In] in Hf.
      repeat (destruct Hf as [Hf|Hf];
        [injection Hf as <- <-; first [solve [apply Hregs; cbn [In]; repeat (first [left; reflexivity | right])]
                                      | intros i Hi; unfold Wr; rewrite HTS; cbn [hd_xv]; lia] |]).
      destruct Hf.
    + cbn [In] in Hf. destruct Hf as [E | [E | [E | []]]]; injection E as <- <-; cbn [hd_at].
      * exact H20.
      * assert (Ec25 : hs_cur rsegs cx rest r + Z.of_nat (length r) - Z.of_nat (length (snd (ent_build rr))) =
          hs_cur rsegs cx rest (snd (ent_build rr))) by (unfold hs_cur; lia).
        rewrite <- Ec25. exact H25.
      * apply eb_val_mod; [| exact V3].
        assert (Hb : Z.of_nat (length (snd (ent_build rr))) <= 2 ^ 47).
        { pose proof (ent_build_rest rr) as (k0 & Ek0).
          destruct Hsrr' as (j & Hj & Ej). destruct HIN' as (Hel & _ & _ & _ & Hamr & Hsrc0 & _).
          unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr.
          assert (Hlen : (length (snd (ent_build rr)) <= length rest)%nat) by (rewrite Ek0, Ej, !length_skipn; lia).
          apply Nat2Z.inj_le in Hlen. lia. }
        split; [apply Nat2Z.is_nonneg | eapply Z.le_lt_trans; [exact Hb | reflexivity]].
  - (* the frame's shadow *)
    unfold hs_fsh_at. apply (hm_fsh_kept rsegs (w_H W2) mem2). { exact HFSH. }
    intros i Hi. apply KE. rewrite LPJ in Hi.
    unfold shadow_addr, SHADOW_OFF in *. pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (e_F (x_e cx)) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_mod (e_F (x_e cx)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_F (x_e cx)) 8 ltac:(lia)).
    unfold Wr. rewrite HTS. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia.
  - (* the first block *)
    unfold hs_pp_at. unfold hs_pp_at in HPP.
    refine (hm_bytes_kept_wr rsegs Wr (w_H W2) mem2 (w_H W3) mem3 _ _ HPP KE _).
    intros x Hx. rewrite Hlpp in Hx. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
    unfold Wr. rewrite HTS. lia.
  - exact E3.
  - destruct (ent_build rr); reflexivity.
  - exact (ent_build_wf rr).
Qed.
End J.
End w.

Print Assumptions eb_D_facts.
Print Assumptions eb_D_input.
Print Assumptions eb_D_w6b.
Print Assumptions eb_D_img.
Print Assumptions eb_J_of.
Print Assumptions eb_J_post.

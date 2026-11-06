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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Hd.v, with its module paths and module names changed; 52 of its 75 lines of code are new or changed and 713 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6b.v at 32f84792c2a6; for image B
   (fuzz_rate.asan-ubsan): the cut states and the piece statement are lib/AU/RtPgSegB.v's, the two bridges
   lib/AU/RtPgEntBCutB.v's and the four block statements lib/AU/RtPgW6bBaseB.v's; image B's case entries and join,
   and image B's case-entry premise (no reloaded shadow address of &pp->len in it). *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the walk piece
   rsb_piece_W6b_stmt of lib/AU/RtPgSegB.v, ent_build's cases 1, 4, 5 and 9 inside LLVMFuzzerTestOneInput (0x8076c),
   from the case entries (rsb_cut_D at 0x81900, 0x81774, 0x81968, 0x81a94) to the join J 0x820dc (rsb_cut_J).
   Proves no function (kind: segment lemma).

   The piece is a chain: the entry bridge of lib/AU/RtPgEntBCutB.v (ebb_D: rsb_cut_D -> the case block's premises),
   the case's block statement of lib/AU/RtPgW6bBaseB.v (w6bb_c1_stmt / w6bb_c4_stmt / w6bb_c5_stmt / w6bb_c9_stmt,
   taken as hypotheses: other lanes prove them), and the join bridge (ebb_J_of: the block's rtsb_post ->
   rsb_cut_J), after which the piece's continuation at J (rsb_from_J) runs. The meter of the segment needs
   ameter_laws MT (the post's mo_le chains through the case). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgStepsB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgSegB RtPgW6bBaseB RtPgEntBCutB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
(* the cut record's projections, with the segments implicit as inside lib/AU/RtPgSegB.v *)
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* image B's loaded segments, as RtPgStepsB names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* one case: from the cut at its entry, through its block, to the cut at J and the piece's continuation there *)
Lemma w6bb_case_of : forall pc (P : Z -> Prop) (X : world rsegs -> (word -> option byte) -> Prop) cx POST rest i k kd
  ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r,
  w6bb_case_stmt B MT pc P X ->
  rsb_start_M01 rsegs B cx rest -> rsb_from_J rsegs B MT cx POST rest i k ->
  (length ps = i)%nat -> (length es = k)%nat ->
  rsb_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  P kd -> X W2 mem2 ->
  SRr rsegs W2 (cfg_at rsegs pc regs2 mem2 md2) POST.
Proof.
  intros pc P X cx POST rest i k kd ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r HC HST HJ Hi Hk HD HP HX.
  destruct (ebb_D B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD)
    as ((b & Erb & Eb) & HCTX & HIN & _ & _).
  subst rr kd.
  eapply SRr_bind.
  { exact (HC (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) (x_k cx)
      ly2 S2 W2 mem2 md2 regs2 (q_R (x_e cx)) (q_F (x_e cx)) (x_pos cx) (rsb_cur rsegs cx rest r)
      (q_pp (x_e cx)) b r HCTX HP HIN HX). }
  intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hr3 & Hf3 & Hp3 & Hio3 & Hmo3 & Hm3 & HR3).
  exact (HJ ly3 S3 W3 regs3 mem3 md3 sh np ps cnt es (b :: r) (snd (ent_build (b :: r))) (fst (ent_build (b :: r)))
    Hi Hk (ebb_J_of B MT MTL cx rest sh np ps cnt es (b :: r) r (bv_unsigned b) ly2 S2 W2 regs2 mem2 md2
             ly3 S3 W3 regs3 mem3 md3 HST HD HJ3 Hr3 Hf3 Hp3 Hio3 Hmo3 Hm3 HR3)).
Qed.

(* the piece: kind % 10 picks the case (rsb_pc_D), each case's block is the hypothesis of its lane *)
Theorem w6bb_piece_of : w6bb_c1_stmt B MT -> w6bb_c4_stmt B MT -> w6bb_c5_stmt B MT -> w6bb_c9_stmt B MT ->
  rsb_piece_W6b_stmt rsegs B MT.
Proof using MTL.
  intros C1 C4 C5 C9 cx POST rest i k kd HST Hkd HJ ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r Hi Hk HD.
  destruct (ebb_D B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as (_ & _ & _ & HS & HV).
  cbn [In] in Hkd. destruct Hkd as [E | [E | [E | [E | []]]]].
  - replace (rsb_pc_D kd) with W6BB_D1 by (unfold rsb_pc_D; rewrite <- E; reflexivity).
    exact (w6bb_case_of _ _ _ cx POST rest i k kd ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r C1 HST HJ Hi Hk HD
      (eq_sym E) HV).
  - replace (rsb_pc_D kd) with W6BB_D4 by (unfold rsb_pc_D; rewrite <- E; reflexivity).
    exact (w6bb_case_of _ _ _ cx POST rest i k kd ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r C4 HST HJ Hi Hk HD
      (eq_sym E) I).
  - replace (rsb_pc_D kd) with W6BB_D5 by (unfold rsb_pc_D; rewrite <- E; reflexivity).
    exact (w6bb_case_of _ _ _ cx POST rest i k kd ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r C5 HST HJ Hi Hk HD
      (eq_sym E) I).
  - replace (rsb_pc_D kd) with W6BB_D9 by (unfold rsb_pc_D; rewrite <- E; reflexivity).
    exact (w6bb_case_of _ _ _ cx POST rest i k kd ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r C9 HST HJ Hi Hk HD
      (eq_sym E) HS).
Qed.
End p.

Print Assumptions w6bb_piece_of.

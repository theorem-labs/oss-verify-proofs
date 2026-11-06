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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Hd.v, with its module paths and module names changed; 131 of its 151 lines of code are new or changed and 716 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the walk piece W6c of LLVMFuzzerTestOneInput
   (0x80c40), lib/AU/HPgSeg.v's hsu_piece_W6c_stmt at segs = Img0U.rsegs, I = headamp_himg_B, BI = headamp_bld_B: the
   cases 6, 7 and 8 of ent_build's `switch (kind % 10)` (pod.h:340-366), from each case entry (hsu_cut_D at
   hsu_pc_D kd: 0x81f08, 0x81d88, 0x81f5c) to the join J 0x82618 (hsu_cut_J). Proves no function (kind: segment
   lemma).

   w6c_D_blk: at a case entry the case's context and entry state (HPgW6cEng.w6c_ctx, HPgW6cCase.w6c_in) from
     HPgCaseBJ.cj_D_facts, cj_D_at (image B's registers s1, s11, s2, a7, t1, s4, a6 and cells R+0x10, R+0x118,
     R+0x130, R+0x138, R+0x148 of hsu_L_D), cj_D_input and cj_D_img (ent_build.t 0x21120 and ent_build.t.11
     0x21140 are registered globals of 16 bytes); e62's shadow hull from the frame's shadow pattern hsu_PJ.
   hsu_piece_W6c_of_cases: the piece from the three case statements. At a case entry the kind byte kd is the first
     byte b of the turn's input rr = b :: r and hsu_pc_D kd is the case's pc; the case runs to J, where cj_J_post
     turns its post into hsu_cut_J and the continuation hsu_from_J runs on with the same property and pod counts.
   hsu_piece_W6c: the piece, from the three proved heads (lib/AU/HPgW6cH6.v, HPgW6cH7.v, HPgW6cH8.v) and tails
     (HPgW6cTake.v, HPgW6cFill.v). The calls the cases make are image B's __asan_memcpy (aintrin_realizes OCpy at
     0x51d8c) and __asan_memset (aintrin_realizes OSet at 0x52228), Section hypotheses here as in every walk lane
     that calls them; the step at each call is HPgCaseB.cb_intrin_at. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgSteps HPgCaseB
  HPgCaseBJ HPgW6cEng HPgW6cCase.
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

Ltac w6c_in_D := cbv [hsu_L_D hsu_L_Dc hsu_Rc0 hsu_Kc app]; cbn [In]; repeat (first [left; reflexivity | right]).

Lemma w6c_tb6_glob : In (W6C_TB6, 16) headamp_B_globs.
Proof. vm_compute. tauto. Qed.
Lemma w6c_tb8_glob : In (W6C_TB8, 16) headamp_B_globs.
Proof. vm_compute. tauto. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma w6c_val_eq : forall H mem a n v v', v' = v -> val_mem rsegs (mrestrict H mem) a n v ->
  val_mem rsegs (mrestrict H mem) a n v'.
Proof. intros H mem a n v v' -> V. exact V. Qed.

(* ============================== a case's premises at a case entry ============================== *)
Lemma w6c_D_blk : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  hsu_start_M01 rsegs B headamp_himg_B cx rest ->
  hsu_cut_D rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  w6c_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) (x_k cx) ly2 S2 W2 mem2 md2 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx) /\
  w6c_in B W2 mem2 regs2 (e_R (x_e cx)) (e_F (x_e cx)) (hsu_cur rsegs cx rest r) (e_pp (x_e cx)) r.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof (@asan_consts rc) as (Hceil & _).
  pose proof (cj_D_facts B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (HJ & R2 & R3 & R4 & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp
     & Hpp & Hpp1 & Hpp2 & Hsep & Hc1 & Hc2 & Ez & HFp & HraE & Hpres & HFSHD & HromD).
  pose proof (cj_D_input B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (Igar & Ira & Ihull & Iam & Idis).
  pose proof (cj_D_img B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as (_ & KG & _).
  assert (AT : forall l v, In (l, v) (hsu_L_D rsegs cx sh np ps cnt es rest r kd) ->
    hd_at rsegs (w_H W2) mem2 regs2 (x_e cx) l v)
    by (intros l v Hin; exact (cj_D_at B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 l v HD Hin)).
  pose proof HD as (HPB & _ & _ & _ & _ & Hsrr & Hfu & Hkd & Hrr).
  pose proof HPB as (_ & HIN & _).
  pose proof HIN as (_ & _ & _ & _ & _ & Hsrc0 & _).
  (* the cursor is past the kind byte *)
  assert (Hlr : (S (length r) <= length rest)%nat).
  { destruct Hsrr as (j & Hj & Ej). destruct rr as [|b r0]; [congruence|].
    cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as _ Er. subst r0.
    assert (L : length (b :: r) = length (skipn j rest)) by (rewrite <- Ej; reflexivity).
    rewrite length_skipn in L. cbn [length] in L. lia. }
  assert (Hc0 : 0 < hsu_cur rsegs cx rest r - 1) by (unfold hsu_cur; lia).
  assert (VS : forall o v, In (LCell XR o, v) (hsu_L_D rsegs cx sh np ps cnt es rest r kd) -> 0 <= v < 2 ^ 64 ->
    val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + o) 8 v).
  { intros o v Hin Hv. apply cj_val_small; [exact Hv|]. exact (AT (LCell XR o) v Hin). }
  split.
  - unfold w6c_ctx. split; [exact HJ|]. split; [exact BR4|]. split; [exact BR1|]. split; [exact BR2|].
    split; [exact BR3|]. split; [exact BR5|]. split; [exact Hown|]. split; [exact EF2|].
    split; [exact HF1|]. split; [exact HF2|]. split; [exact HF32|]. split; [exact HFapp|]. exact HFp.
  - unfold w6c_in.
    split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
    split; [exact (AT (LReg 9) _ ltac:(w6c_in_D))|].
    split; [exact (AT (LReg 27) _ ltac:(w6c_in_D))|].
    split; [exact (AT (LReg 18) _ ltac:(w6c_in_D))|].
    split; [exact (AT (LReg 17) _ ltac:(w6c_in_D))|].
    split; [exact (AT (LReg 6) _ ltac:(w6c_in_D))|].
    split; [exact (AT (LReg 20) _ ltac:(w6c_in_D))|].
    split; [exact (AT (LReg 16) _ ltac:(w6c_in_D))|].
    split; [exact (VS 0x10 _ ltac:(w6c_in_D) ltac:(lia))|].
    split; [eapply w6c_val_eq; [|exact (VS 0x118 _ ltac:(w6c_in_D) ltac:(unfold HSU_E62; lia))]; unfold HSU_E62; lia|].
    split; [eapply w6c_val_eq; [|exact (VS 0x130 _ ltac:(w6c_in_D) ltac:(unfold HSU_E62; lia))]; unfold HSU_E62; lia|].
    split; [eapply w6c_val_eq; [|exact (VS 0x138 _ ltac:(w6c_in_D)
              ltac:(unfold Layout.PP_SIZE in Hpp2; lia))]; lia|].
    split; [eapply w6c_val_eq; [|exact (VS 0x148 _ ltac:(w6c_in_D) ltac:(unfold Layout.PP_SIZE in Hpp2; lia))]; lia|].
    split; [exact Hpp1|]. split; [exact Hpp2|].
    split; [exact Ez|]. split; [exact HraE|].
    split.
    { (* e62's shadow hull: shadow bytes 66 .. 78 of F's 116, which the frame's shadow pattern gives *)
      assert (Hq : exists q, e_F (x_e cx) = 32 * q).
      { apply (proj1 (Z.mod_divide (e_F (x_e cx)) 32 ltac:(discriminate))) in HF32. destruct HF32 as [q Hq].
        exists q. lia. }
      destruct Hq as [q Hq].
      assert (EsF : shadow_addr (e_F (x_e cx)) = SHADOW_OFF + 4 * q).
      { unfold shadow_addr. rewrite Hq. f_equal. replace (32 * q) with ((4 * q) * 8) by ring. apply Z.div_mul. lia. }
      unfold shadow_hull_vis. intros s Hs. unfold shadow_addr in Hs. rewrite Hq in Hs.
      assert (A1 : (32 * q + 0x210) / 8 = 4 * q + 66)
        by (replace (32 * q + 0x210) with ((4 * q + 66) * 8) by ring; apply Z.div_mul; lia).
      assert (A2 : (32 * q + 0x210 + 104 - 1) / 8 = 4 * q + 78)
        by (replace (32 * q + 0x210 + 104 - 1) with ((4 * q + 78) * 8 + 7) by ring; rewrite Z.div_add_l by lia;
            change (7 / 8) with 0; ring).
      rewrite A1, A2 in Hs.
      pose proof (Z.div_mod (SHADOW_OFF + (4 * q + 66)) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (SHADOW_OFF + (4 * q + 66)) 8 ltac:(lia)).
      pose proof (Z.div_mod (SHADOW_OFF + (4 * q + 78)) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (SHADOW_OFF + (4 * q + 78)) 8 ltac:(lia)).
      replace s with (shadow_addr (e_F (x_e cx)) + (s - shadow_addr (e_F (x_e cx)))) by lia.
      rewrite (HFSHD (s - shadow_addr (e_F (x_e cx))) ltac:(rewrite cj_PJ_len, EsF; lia)). discriminate. }
    split; [exact Igar|]. split; [exact Ira|]. split; [exact Ihull|]. split; [exact Iam|].
    split; [lia|].
    split; [intros a Ha; destruct (Idis a Ha) as (D1 & D2 & _); split; [exact D1 | exact D2]|].
    split; [exact (KG _ _ w6c_tb6_glob)|].
    split; [exact (KG _ _ w6c_tb8_glob)|].
    exact HromD.
Qed.

(* ============================== the piece from the three cases ============================== *)
Hypothesis MTL : ameter_laws MT.

Lemma hsu_piece_W6c_of_cases :
  w6c_case_stmt B MT 6 -> w6c_case_stmt B MT 7 -> w6c_case_stmt B MT 8 ->
  hsu_piece_W6c_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof.
  intros C6 C7 C8 cx POST rest i k kd HST Hkd HJ.
  unfold hsu_from_D. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r Hi Hk HD.
  pose proof (w6c_D_blk cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as (Hctx & Hin).
  (* the kind byte is the first byte of the turn's input *)
  pose proof HD as (_ & _ & _ & _ & _ & _ & Hfu & _ & Hrr).
  destruct rr as [|b r0]; [congruence|].
  cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as Ekd Er. subst kd r0.
  (* from J on: cj_J_post and the continuation *)
  assert (KJ : forall W3 c3,
    hdu_blk_postE B MT (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
      (x_own cx) (x_k cx) regs2 ly2 S2 W2 mem2 md2 W6C_J w6c_clob (cj_wr (e_R (x_e cx)) (e_F (x_e cx)) [])
      (cj_J_R (e_R (x_e cx)) (e_F (x_e cx)) (e_pp (x_e cx)) (hsu_cur rsegs cx rest r) r (b :: r)) W3 c3 ->
    SRr rsegs W3 c3 POST).
  { intros W3 c3 HP.
    destruct (cj_J_post B MT cx rest sh np ps cnt es (b :: r) r (bv_unsigned b) ly2 S2 W2 regs2 mem2 md2
      w6c_clob [] W3 c3 HST HD MTL w6c_clob_ok w6c_ws_ok HP) as (regs3 & mem3 & md3 & ly3 & S3 & -> & HJc).
    exact (HJ ly3 S3 W3 regs3 mem3 md3 sh np ps cnt es (b :: r) _ _ Hi Hk HJc). }
  cbn [In] in Hkd. destruct Hkd as [E | [E | [E | []]]]; symmetry in E.
  - assert (Epc : hsu_pc_D headamp_bld_B (bv_unsigned b) = w6c_pc 6) by (unfold hsu_pc_D; rewrite E; reflexivity).
    rewrite Epc. eapply SRr_bind; [exact (C6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ _ _ b r Hctx E Hin)|].
    intros W3 c3 _ HP. exact (KJ W3 c3 HP).
  - assert (Epc : hsu_pc_D headamp_bld_B (bv_unsigned b) = w6c_pc 7) by (unfold hsu_pc_D; rewrite E; reflexivity).
    rewrite Epc. eapply SRr_bind; [exact (C7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ _ _ b r Hctx E Hin)|].
    intros W3 c3 _ HP. exact (KJ W3 c3 HP).
  - assert (Epc : hsu_pc_D headamp_bld_B (bv_unsigned b) = w6c_pc 8) by (unfold hsu_pc_D; rewrite E; reflexivity).
    rewrite Epc. eapply SRr_bind; [exact (C8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ _ _ b r Hctx E Hin)|].
    intros W3 c3 _ HP. exact (KJ W3 c3 HP).
Qed.

(* the step at a call of a memory intrinsic: HPgCaseB's twin of lib/A/HPgIntrin.v's hd_intrin_at *)
Lemma w6c_intrin : w6c_intrin_law B.
Proof. exact (cb_intrin_at B). Qed.
End b.

Print Assumptions w6c_D_blk.
Print Assumptions hsu_piece_W6c_of_cases.
Print Assumptions w6c_intrin.

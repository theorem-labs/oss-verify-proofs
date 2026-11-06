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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Hd.v, with its module paths and module names changed; 216 of its 242 lines of code are new or changed and 710 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostTop.v at 01f4363fe7d, for image B of
   reac-pw/fuzz_headamp: w10t_ -> hw10p_, rs_ -> hsu_ (the cut states of lib/AU/HPgSeg.v), rm_ -> hm_, rl_ -> hd_;
   the entry states walk image B's own code (the arms split on what is left of the input as image B's tests do:
   0, 1, 2, 3, >= 4 bytes), with image B's UBSan tests decided by the atoms' range facts, the pod block reached from
   one atom (pp) whose 19744 bytes are one shadow entry, and pp->len's shadow address reloaded from R+0x150. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the arm |r| >= 4 of the builder's end P1
   0x82bf0 of LLVMFuzzerTestOneInput (0x80c40), pod.h:441-445 (code and states in HPgW10PostK.v's header). Proves no
   function (kind: segment lemma). c & 15 <> 15 ends at 0x82ee0; len < 9 at C2 0x82efc; a count byte & 7 = 0 at RT
   0x82ec8 with no byte written; otherwise at R 0x82e2c with kk = 0, a2 = the count, a4 = the offset, a0 = the cursor
   after the four bytes and a5 = what is left of them. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgW10Kit HPgW10Req HPgW10PostK.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma hw10p_split4 : forall (r : list byte), (4 <= length r)%nat ->
  exists c0 xa xb xc r4, r = c0 :: xa :: xb :: xc :: r4.
Proof. intros r H. destruct r as [|c0 [|xa [|xb [|xc r4]]]]; cbn [length] in H; try lia. eauto 6. Qed.

(* ---- |r| >= 4: c, the offset's two bytes and the count byte ---- *)
Lemma hw10p_P1_4 : forall cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps r,
  hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) ->
  (forall kk, hsu_from_R rsegs B MT headamp_himg_B headamp_bld_B cx POST rest kk) ->
  hsu_from_RT rsegs B MT headamp_himg_B headamp_bld_B cx POST rest ->
  hsu_from_C2 rsegs B MT headamp_himg_B cx POST rest ->
  hsu_cut_P1 rsegs B MT headamp_himg_B cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 -> (4 <= length r)%nat ->
  SRr rsegs W2 (cfg_at rsegs HW10_P1 regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps r HP HR HRT HC2 (HB & HL) Hr4.
hw10p_pre B MT HP HB HL.
pose proof (hw10p_len_cell cx sh ps W2 mem2 Hwf Hpp) as HLv. unfold hsu_plen in HLv.
set (L := Z.of_nat (length (pc_buf (PbCut sh ps None)))) in *.
set (pp := e_pp (x_e cx)) in *.
destruct (hw10_in_now B MT cx rest (hsu_P0 headamp_himg_B) ly2 S2 W2 regs2 mem2 md2 HP Hin HC Hfsh eq_refl)
  as (Hbytes & Hra & _).
pose proof Hin as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & _).
pose proof Hsuf as (jr & Hjr & Hrj).
assert (Hlr : (length r <= length rest)%nat) by (rewrite Hrj, length_skipn; lia).
set (cur := hsu_cur rsegs cx rest r) in *.
assert (Hcd : cur = e_src (x_e cx) + Z.of_nat (length rest) - Z.of_nat (length r)) by reflexivity.
assert (Hcur : 1 <= cur /\ cur + Z.of_nat (length r) <= 2 ^ 47)
  by (rewrite Hcd; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
assert (Hr63 : Z.of_nat (length r) <= 2 ^ 63) by lia.
pose proof (hw10_build_tie rest sh np ps r Hsh Hnp Hnps Hps) as Htie.
assert (HLp : Z.of_nat (length (pod_encode (PodRec sh ps None))) = L) by (rewrite HW2; reflexivity).
rewrite HLp in Htie.
assert (HIN : forall i, (i < length r)%nat ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (cur + Z.of_nat i) 1 (bv_unsigned (nth i r (Z_to_bv 8 0))) /\
  ~ (e_R (x_e cx) <= cur + Z.of_nat i < e_R (x_e cx) + 0x198) /\
  ~ (pp <= cur + Z.of_nat i < pp + PP_SIZE)).
{ intros i Hi. destruct (hw10p_in_at cx rest r W2 mem2 i Hin Hbytes Hra Hsuf Hi) as (V & N1 & N2 & _).
  split; [exact V|]. split; [exact N1 | exact N2]. }
remember (Ereg regs2 ([Z_to_bv 64 pp; Z_to_bv 64 L; Z_to_bv 64 (2 ^ 64 - 1 - pp)]
  ++ map (fun i => Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))) (seq 0 4))) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 (e_R (x_e cx))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl); exact P9).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl); exact P27).
assert (E28 : ew E 28 = Z_to_bv 64 (Z.of_nat (length r))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 28 (Z_to_bv 5 28) eq_refl); exact P28).
assert (E17 : ew E 17 = Z_to_bv 64 cur) by (subst E; rewrite (ew_Ereg_nat regs2 _ 17 (Z_to_bv 5 17) eq_refl); exact P17).
assert (E32 : ew E 32 = Z_to_bv 64 pp) by (subst E; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 L) by (subst E; reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 (2 ^ 64 - 1 - pp)) by (subst E; reflexivity).
assert (EB : forall i, (i < 4)%nat -> ew E (35 + i) = Z_to_bv 64 (bv_unsigned (nth i r (Z_to_bv 8 0)))).
{ intros i Hi. subst E. destruct i as [|[|[|[|i]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia]. }
assert (U32 : bv_unsigned (ew E 32) = pp) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HUB : U E hw10_Bx = SHADOW_OFF) by exact (hw10_UB E E27).
assert (HAE0 : env_agree 39 E E) by apply env_agree_refl.
assert (SHOK : sh_ok rsegs hw10_Bx (hw10p_SH 4) E (mrestrict (w_H W2) mem2)).
{ unfold hw10p_SH. constructor; [|constructor; [|constructor]].
  - apply (hw10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 32 0 0x4d20 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HUB | | | lia];
    rewrite (hw10_U_atom E 32 _ E32 ltac:(lia)); lia.
  - apply (hw10_shent_in E _ 17 (e_src (x_e cx)) (e_left (x_e cx)) cur (Z.of_nat 4) Hamr HUB
      (hw10_U_atom E 17 _ E17 ltac:(lia))); [lia | lia | lia | exact Hra]. }
destruct (hw10p_split4 r Hr4) as (c0 & xa & xb & xc & r4 & Hr0).
pose proof (hm_byte_range c0) as Bc0. pose proof (hm_byte_range xa) as Bxa.
pose proof (hm_byte_range xb) as Bxb. pose proof (hm_byte_range xc) as Bxc.
unfold cfg_at. change (w64 HW10_P1) with (Z_to_bv 64 HW10_P1).
destruct (Z.eq_dec (bv_unsigned (nth 0 r (Z_to_bv 8 0)) mod 16) 15) as [Hc15|Hc15].
2: { (* c & 15 <> 15: no corruption, 0x82ee0 *)
  assert (HS : st_ok rsegs E (hw10p_ssk 4 8 (2 ^ 47 - 4) 4 (2 ^ 63) [hw10p_cNE15])
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 HW10_P1) mem2 (seg_rom rsegs)))).
  { apply (hw10p_HS_lem cx r W2 regs2 mem2 E _ L cur 4 8 (2 ^ 47 - 4) 4 (2 ^ 63) _
      HE E9 E27 E17 E28 E32 E33 E34 EB);
    [ first [ assumption | solve [unfold kHighMemBeg, T_SEG_STK, ASTACK, HW10_PPHI in *; lia]
            | solve [intros i Hi; apply HIN; lia] | solve [lia] ] ..
    | hw10p_conds EB E33 E28 ]. }
  aj_run_to_tok hw10_tbl_ok HS HJ SHOK hw10_Bspan HW10_TAIL.
  all: try solve [hw10p_awr E pp U32 Hinp Hfresh].
  lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ => assert (HAE : env_agree 39 E E') by env_agree_chain HAE0;
  assert (HAE34 : env_agree 34 E E') by (eapply env_agree_le; [|exact HAE]; lia) end.
  destruct (hw10p_fin_lem B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E _ _ _ ms _ _ _ HP HB0
    (proj1 (proj1 (Forall_app _ _ _) HL0)) HE E32 E33 HS HAE34 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
    ltac:(hw10p_in) ltac:(hw10p_in) ltac:(hw10p_in) ltac:(hw10p_in) HFr ltac:(hw10p_kwr) HJ
    (HPgSteps.same_io_wvb _ _ _)) as (L1 & L2 & L3 & L4).
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (hw10_tail B MT cx POST rest ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HP HC2 L1 L2 L3); [| exact Hlen].
  rewrite Hr0 in Hc15. cbn [nth] in Hc15.
  rewrite Htie, Hr0, (hw10_corr_none L c0 _ (or_introl Hc15)). exact L4. }
destruct (Z_lt_le_dec L 9) as [HL9|HL9].
{ (* len < 9: no corruption, 0x82ef4 -> C2 *)
  assert (HS : st_ok rsegs E (hw10p_ssk 4 8 (2 ^ 47 - 4) 4 (2 ^ 63) [hw10p_cEQ15; hw10p_cLT9])
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 HW10_P1) mem2 (seg_rom rsegs)))).
  { apply (hw10p_HS_lem cx r W2 regs2 mem2 E _ L cur 4 8 (2 ^ 47 - 4) 4 (2 ^ 63) _
      HE E9 E27 E17 E28 E32 E33 E34 EB);
    [ first [ assumption | solve [unfold kHighMemBeg, T_SEG_STK, ASTACK, HW10_PPHI in *; lia]
            | solve [intros i Hi; apply HIN; lia] | solve [lia] ] ..
    | hw10p_conds EB E33 E28 ]. }
  aj_run_to_tok hw10_tbl_ok HS HJ SHOK hw10_Bspan HW10_C2.
  all: try solve [hw10p_awr E pp U32 Hinp Hfresh].
  lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ => assert (HAE : env_agree 39 E E') by env_agree_chain HAE0;
  assert (HAE34 : env_agree 34 E E') by (eapply env_agree_le; [|exact HAE]; lia) end.
  destruct (hw10p_fin_lem B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E _ _ _ ms _ _ _ HP HB0
    (proj1 (proj1 (Forall_app _ _ _) HL0)) HE E32 E33 HS HAE34 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
    ltac:(hw10p_in) ltac:(hw10p_in) ltac:(hw10p_in) ltac:(hw10p_in) HFr ltac:(hw10p_kwr) HJ
    (HPgSteps.same_io_wvb _ _ _)) as (L1 & L2 & L3 & L4).
  assert (Hnone : fst (corr_step L r) = None) by (rewrite Hr0; apply hw10_corr_none; right; lia).
  assert (HeL : e_len (x_e cx) = L).
  { rewrite Hlen. unfold hd_len. rewrite Htie, Hnone. cbn [buf p_corr]. rewrite HW2. reflexivity. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (e_len (x_e cx))).
  { apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 10) 39 (SOff 33 0) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
    rewrite HeL. exact (hw10_den_atom _ 33 _ E33). }
  assert (R21 : getr (ms_regs ms) (Z_to_bv 5 21) = w64 (e_len (x_e cx))).
  { apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 21) 39 (SOff 33 0) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
    rewrite HeL. exact (hw10_den_atom _ 33 _ E33). }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HC2 ly2 S2). apply (hw10p_mkC2 B MT cx rest ly2 S2 W2 _ _ _ L1 L2 L3); [| exact Hlen | exact R10 | exact R21].
  rewrite Htie, Hnone. exact L4. }
pose proof Hc15 as Hc15r. rewrite Hr0 in Hc15. cbn [nth] in Hc15.
destruct (Z.eq_dec (bv_unsigned (nth 3 r (Z_to_bv 8 0)) mod 8) 0) as [Hn0|Hn0].
{ (* the count byte & 7 = 0: no byte written, RT *)
  assert (HS : st_ok rsegs E (hw10p_ssk 4 9 (2 ^ 47 - 4) 4 (2 ^ 63) [hw10p_cEQ15; hw10p_cEQ7])
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 HW10_P1) mem2 (seg_rom rsegs)))).
  { apply (hw10p_HS_lem cx r W2 regs2 mem2 E _ L cur 4 9 (2 ^ 47 - 4) 4 (2 ^ 63) _
      HE E9 E27 E17 E28 E32 E33 E34 EB);
    [ first [ assumption | solve [unfold kHighMemBeg, T_SEG_STK, ASTACK, HW10_PPHI in *; lia]
            | solve [intros i Hi; apply HIN; lia] | solve [lia] ] ..
    | hw10p_conds EB E33 E28 ]. }
  aj_run_to_tok hw10_tbl_ok HS HJ SHOK hw10_Bspan HW10_RT.
  all: try solve [hw10p_awr E pp U32 Hinp Hfresh].
  lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ => assert (HAE : env_agree 39 E E') by env_agree_chain HAE0;
  assert (HAE34 : env_agree 34 E E') by (eapply env_agree_le; [|exact HAE]; lia) end.
  destruct (hw10p_fin_lem B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E _ _ _ ms _ _ _ HP HB0
    (proj1 (proj1 (Forall_app _ _ _) HL0)) HE E32 E33 HS HAE34 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
    ltac:(hw10p_in) ltac:(hw10p_in) ltac:(hw10p_in) ltac:(hw10p_in) HFr ltac:(hw10p_kwr) HJ
    (HPgSteps.same_io_wvb _ _ _)) as (L1 & L2 & L3 & L4).
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  rewrite Hr0 in Hn0. cbn [nth] in Hn0.
  destruct (hw10p_model_RT L c0 (xa :: xb :: xc :: r4) Hc15 HL9 ltac:(cbn; exact Hn0)) as (Hm & Hob).
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps (8 + fst (fuzz_u16 (xa :: xb :: xc :: r4)) mod (L - 8)) [] r).
  apply (hw10p_mkRT B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 _ _ _ _ HB0 L1 L2 L3 L4);
  [rewrite Htie, Hr0, Hm; reflexivity | lia | unfold hsu_plen; fold L; lia]. }
(* the count byte & 7 <> 0: the corruption loop, R with kk = 0 *)
assert (HS : st_ok rsegs E (hw10p_ssk 4 9 (2 ^ 47 - 4) 4 (2 ^ 63) [hw10p_cEQ15; hw10p_cNE7])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 HW10_P1) mem2 (seg_rom rsegs)))).
{ apply (hw10p_HS_lem cx r W2 regs2 mem2 E _ L cur 4 9 (2 ^ 47 - 4) 4 (2 ^ 63) _
    HE E9 E27 E17 E28 E32 E33 E34 EB);
  [ first [ assumption | solve [unfold kHighMemBeg, T_SEG_STK, ASTACK, HW10_PPHI in *; lia]
          | solve [intros i Hi; apply HIN; lia] | solve [lia] ] ..
  | hw10p_conds EB E33 E28 ]. }
aj_run_to_tok hw10_tbl_ok HS HJ SHOK hw10_Bspan HW10_R.
all: try solve [hw10p_awr E pp U32 Hinp Hfresh].
lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ => assert (HAE : env_agree 39 E E') by env_agree_chain HAE0;
  assert (HAE34 : env_agree 34 E E') by (eapply env_agree_le; [|exact HAE]; lia) end.
lazymatch type of HFr with frame_of _ ?rs0 _ _ =>
  assert (Hwr : forall a, in_wrange E rs0 a -> pp <= a < pp + 4) by hw10p_kwr end.
assert (HKf : forall a, 0 <= a < 2 ^ 64 -> ~ (pp <= a < pp + 4) ->
  aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (hw10_frame_kept _ _ _ _ _ HFr a Ha). intros X. exact (Hn (Hwr a X)). }
destruct (hw10p_fin_lem B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 E _ _ _ ms _ _ _ HP HB0
  (proj1 (proj1 (Forall_app _ _ _) HL0)) HE E32 E33 HS HAE34 ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(hw10p_in) ltac:(hw10p_in) ltac:(hw10p_in) ltac:(hw10p_in) HFr Hwr HJ
  (HPgSteps.same_io_wvb _ _ _)) as (L1 & L2 & L3 & L4).
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
pose proof Hn0 as Hn0r. rewrite Hr0 in Hn0. cbn [nth] in Hn0.
set (off := 8 + (bv_unsigned xa + 256 * bv_unsigned xb) mod (L - 8)).
set (cnt := bv_unsigned xc mod 8).
set (bs := fst (fuzz_u8s (Z.to_nat (Z.min cnt (L - off))) r4)).
destruct (hw10p_model_R L c0 xa xb xc r4 off cnt bs Hc15 HL9 Hn0 eq_refl eq_refl eq_refl)
  as (Hm & Hoff & Hcnt & Hbl & Hbs).
assert (Hlr4 : length r = (4 + length r4)%nat) by (rewrite Hr0; reflexivity).
assert (R13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 0).
{ apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 13) 39 (SLit 0) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  reflexivity. }
assert (R12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 cnt).
{ apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 12) 39 (SAlu ALU_AND (SOff 38 0) (SLit 7)) _ HS HAE);
    [vm_compute; reflexivity | reflexivity |].
  rewrite denot_lit_U. rewrite (hw10p_U_and7 E 38 _ (EB 3%nat ltac:(lia)) (hm_byte_range _)). rewrite Hr0. reflexivity. }
assert (R14 : getr (ms_regs ms) (Z_to_bv 5 14) = w64 off).
{ apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 14) 39
    (SAlu ALU_ADD (SMd M_REMU (SAlu ALU_OR (SAlu ALU_SLL (SOff 37 0) (SLit 8)) (SOff 36 0)) (SOff 33 (-8))) (SLit 8))
    _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  rewrite denot_lit_U.
  rewrite (hw10p_U_off E (bv_unsigned xa) (bv_unsigned xb) L); [reflexivity | | | exact E33 | lia | lia | lia].
  - transitivity (Z_to_bv 64 (bv_unsigned (nth 1 r (Z_to_bv 8 0)))); [exact (EB 1%nat ltac:(lia)) | rewrite Hr0; reflexivity].
  - transitivity (Z_to_bv 64 (bv_unsigned (nth 2 r (Z_to_bv 8 0)))); [exact (EB 2%nat ltac:(lia)) | rewrite Hr0; reflexivity]. }
assert (R16 : getr (ms_regs ms) (Z_to_bv 5 16) = w64 1).
{ apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 16) 39 (SLit 1) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  reflexivity. }
assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (hsu_cur rsegs cx rest r4)).
{ apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 10) 39 (SOff 17 4) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  rewrite (hw10_den_off _ 17 _ _ E17). unfold w64. f_equal. unfold hsu_cur. rewrite Hcd, Hlr4. lia. }
assert (R15 : getr (ms_regs ms) (Z_to_bv 5 15) = w64 (Z.of_nat (length r4))).
{ apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 15) 39 (SOff 28 (-4)) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  rewrite (hw10_den_off _ 28 _ _ E28). unfold w64. f_equal. rewrite Hlr4. lia. }
assert (Qf0' : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (e_R (x_e cx) + 0xf0) 8 ((- pp - 1) mod 2 ^ 64)).
{ apply (hm_at_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) (LCell XR 0xf0) (- pp - 1) Qf0).
  cbn [hm_keeps hd_xv]. intros i Hi. apply HKf; [unfold T_SEG_STK, ASTACK in *; lia |].
  unfold T_SEG_STK, ASTACK in *. lia. }
assert (Hsuf4 : hsu_suffix rest r4).
{ exists (4 + jr)%nat. split; [rewrite Hrj, length_skipn in Hlr4; lia|].
  rewrite <- skipn_skipn, <- Hrj, Hr0. reflexivity. }
apply (HR 0%nat ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps r4 off bs cnt).
apply (hw10p_mkR B MT cx sh np ps rest r r4 ly2 S2 W2 regs2 mem2 md2 _ _ _ off bs cnt HB0 L1 L2 L3 L4
  R13 R12 R14 R16 R10 R15 Qf0' Hsuf4); [rewrite Htie, Hr0, Hm; reflexivity | | exact Hbs].
unfold hsu_corr_wf, hsu_plen. fold L. lia.
Qed.

End t.

Print Assumptions hw10p_P1_4.

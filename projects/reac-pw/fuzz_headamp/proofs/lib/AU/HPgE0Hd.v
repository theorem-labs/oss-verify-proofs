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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Hd.v, with its module paths and module names changed; 254 of its 384 lines of code are new or changed and 606 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Hd.v at 97ea9c9eafa; restated for
   reac-pw/fuzz_headamp's image B: the head's blocks of lib/AU/HPgE0HdB.v chained from HPgSeg.hsu_cut_D (through
   lib/AU/HPgCaseBJ.v's cj_D_facts / cj_D_input) and hsu_cut_D0E to HPgE0Def.e0_cut_DIG / e0_cut_ODD (through
   lib/AU/HPgE0HdC.v), with image B's registers and the cursor cell R+0x110. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): HPgE0Def.e0_head_stmt,
   the head of ent_build's case 0 in LLVMFuzzerTestOneInput 0x80c40 from both its entries (D = 0x8194c with the
   kind byte read, D0E = 0x819c0 with no input left) to the two arms DIG = 0x81a1c and ODD = 0x82318. Proves no
   function (kind: segment lemma).

   HOW. The walk is the six blocks of lib/AU/HPgE0HdB.v, chained with SRr_bind, by what is left of the input after
   the kind byte (r):
     r = []          eh_T0                      to DIG with c = p = 0, nothing more read
     r = [c]         eh_T1, eh_K1, eh_C         c read, p = 0
     r = c :: p :: _ eh_T1, eh_K2, eh_C         c and p read
     D0E             eh_TE                      to DIG with c = p = 0
   and eh_C goes to DIG when c < 200, to ODD otherwise. The registers the blocks read at D are the cut's (image B):
   s1 = R (x9), s3 = shadow_addr F (x19), s11 = K (x27), a7 = the cursor - 1 (x17), s2 = the cursor (x18),
   t1 = |r| + 1 (x6), s4 = |r| (x20), a6 = 1 (x16), t2 = 10 (x7), s7 = -8 (x23), and R+0xc8 = &ch; at D0E s5 = the
   cursor (x21). The input bytes, their shadow and their place apart from the frames come from cj_D_input and are
   carried across eh_T1 by its frame condition (it writes only t's shadow bytes). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YO09 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgMem HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgE0Def HPgE0Base HPgCaseBJ HPgE0HdB HPgE0HdC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* the cut record's projections, with the segments implicit *)
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

(* a register outside a concrete clobber list *)
Ltac eh_notin' :=
let H := fresh "H" in intros H; cbn [In eh_clob] in H;
repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
Ltac eh_kr' Hk R := rewrite Hk; [exact R | cbv; discriminate | eh_notin'].
Ltac eh_sub' := let q := fresh "q" in let X := fresh "X" in
intros q X; cbn [In eh_clob] in X |- *; tauto.
(* membership in a concrete location list of a cut *)
Ltac eh_in := cbn [hsu_L_D hsu_L_Dc hsu_Rc0 hsu_Kc app]; repeat (first [left; reflexivity | right]).

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================== after the reads: the ch stores, the arm test and the arm's cut =====================
   The state at 0x822fc (eh_K1 / eh_K2's post, after eh_T1) with everything it changed since the case entry. *)
Lemma eh_after_K : forall cx POST rest i k sh np ps cnt es rr r r3 c pb ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4,
hsu_start_M01 rsegs B headamp_himg_B cx rest ->
e0_from_DIG B MT cx POST rest i k -> e0_from_ODD B MT cx POST rest i k ->
(length ps = i)%nat -> (length es = k)%nat ->
hsu_pod_base rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
hsu_at_cx rsegs cx W2 mem2 regs2 (hsu_L_Dc rsegs cx sh np ps cnt es) ->
hsu_fsh_at rsegs cx W2 mem2 (hsu_PJ headamp_himg_B) ->
hsu_pp_at rsegs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) ->
hsu_obj_at rsegs cx W2 mem2 HSU_E62 (zeros 104) ->
eh_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) (x_k cx)
  ly2 S2 W2 mem4 md4 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx) ->
same_io md2 md4 ->
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q eh_clob -> getr regs4 q = getr regs2 q) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ eh_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a ->
 aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem2 a) ->
eh_zero W2 mem4 (e_F (x_e cx)) 4 12 ->
val_mem rsegs (mrestrict (w_H W2) mem4) (e_R (x_e cx) + 0x110) 8 (hsu_cur rsegs cx rest r3) ->
val_mem rsegs (mrestrict (w_H W2) mem4) (e_R (x_e cx) + 0xc8) 8 (e_F (x_e cx) + 0xa0) ->
getr regs4 6 = w64 (Z.of_nat (length r3)) -> getr regs4 26 = w64 pb -> getr regs4 13 = w64 c ->
getr regs4 28 = w64 9 -> getr regs4 7 = w64 10 -> getr regs4 23 = w64 (-8) ->
getr regs4 9 = w64 (e_R (x_e cx)) -> getr regs4 19 = w64 (shadow_addr (e_F (x_e cx))) ->
hsu_suffix rest r3 -> fst (Cursor.fuzz_u8 rr) mod 10 = 0 -> (c, pb, r3) = e0_cp_of rr ->
0 <= c < 256 -> 0 <= pb < 256 ->
SRr rsegs W2 (cfg_at rsegs EH_CH regs4 mem4 md4) POST.
Proof.
intros cx POST rest i k sh np ps cnt es rr r r3 c pb ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4
  Hst HDIG HODD Hlps Hles Hb Hat0 Hfsh Hpp He Hctx4 Hio4 Hk4 Hm4 Z4 V4 V4c R6 R26 R13 R28 R7 R23 R9 R19
  Hsuf Hkd Hcp Hc Hpb.
destruct (eh_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx4)
  as (HF32 & HF0 & HFc & HRc & HR0 & HR1 & Has & _).
pose proof (@asan_consts rc) as (C1 & _).
destruct (eh_sF (e_F (x_e cx)) ltac:(lia) ltac:(lia)) as [SF0 SF1].
assert (Hsub : forall q, In q eh_clob \/ In q [5; 11; 18]%bv -> In q eh_clob) by eh_sub'.
assert (Hwsub : forall a, eh_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a \/ eh_wCh (e_F (x_e cx)) a ->
  eh_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a) by (cbv [eh_wTCN]; tauto).
destruct (Z_lt_le_dec c 200) as [Hlt|Hge].
- eapply SRr_bind.
  { exact (eh_C B false _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs4 _ _ _ c Hctx4 R9 R19 R13 (conj (proj1 Hc) Hlt) V4c). }
  intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & Hio5 & Hk5 & Hm5 & Hp5 & (Z5 & S18 & S5)).
  change (mkCfg (mkst regs5 (Z_to_bv 64 (if false then E0_ODD else E0_DIG)) mem5 (seg_rom rsegs)) md5)
    with (cfg_at rsegs E0_DIG regs5 mem5 md5).
  apply (HDIG ly2 S2 W2 regs5 mem5 md5 sh np ps cnt es rr r3 c pb Hlps Hles).
  apply (eh_build_DIG B MT cx sh np ps cnt es rest rr r r3 c pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5
    Hst Hb Hat0 Hfsh Hpp He HJ5 (same_io_trans _ _ _ Hio4 Hio5)
    (eh_keep2 regs2 regs4 regs5 eh_clob [5; 11; 18]%bv eh_clob Hk4 Hk5 Hsub)
    (eh_mem2 _ mem2 mem4 mem5 _ _ _ Hm4 Hm5 Hwsub)).
  + apply (eh_zero_kept W2 mem4 mem5 _ 4 12 Z4). intros q Hq.
    apply Hm5; [lia | cbv [eh_wCh]; lia].
  + exact Z5.
  + eapply val_mem_kept; [|exact V4]. intros q Hq. apply Hm5; [lia | cbv [eh_wCh]; lia].
  + eh_kr' Hk5 R6.
  + exact S18.
  + eh_kr' Hk5 R26.
  + eh_kr' Hk5 R13.
  + exact S5.
  + eh_kr' Hk5 R28.
  + eh_kr' Hk5 R7.
  + eh_kr' Hk5 R23.
  + exact Hsuf.
  + exact Hkd.
  + exact Hcp.
  + lia.
  + exact Hpb.
- eapply SRr_bind.
  { exact (eh_C B true _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs4 _ _ _ c Hctx4 R9 R19 R13 (conj Hge (proj2 Hc)) V4c). }
  intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & Hio5 & Hk5 & Hm5 & Hp5 & (Z5 & S18 & S5)).
  change (mkCfg (mkst regs5 (Z_to_bv 64 (if true then E0_ODD else E0_DIG)) mem5 (seg_rom rsegs)) md5)
    with (cfg_at rsegs E0_ODD regs5 mem5 md5).
  apply (HODD ly2 S2 W2 regs5 mem5 md5 sh np ps cnt es rr r3 c pb Hlps Hles).
  apply (eh_build_ODD B MT cx sh np ps cnt es rest rr r r3 c pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5
    Hst Hb Hat0 Hfsh Hpp He HJ5 (same_io_trans _ _ _ Hio4 Hio5)
    (eh_keep2 regs2 regs4 regs5 eh_clob [5; 11; 18]%bv eh_clob Hk4 Hk5 Hsub)
    (eh_mem2 _ mem2 mem4 mem5 _ _ _ Hm4 Hm5 Hwsub)).
  + apply (eh_zero_kept W2 mem4 mem5 _ 4 12 Z4). intros q Hq.
    apply Hm5; [lia | cbv [eh_wCh]; lia].
  + exact Z5.
  + eapply val_mem_kept; [|exact V4]. intros q Hq. apply Hm5; [lia | cbv [eh_wCh]; lia].
  + eh_kr' Hk5 R6.
  + exact S18.
  + eh_kr' Hk5 R26.
  + eh_kr' Hk5 R13.
  + exact Hsuf.
  + exact Hkd.
  + exact Hcp.
  + lia.
  + exact Hpb.
Qed.

(* ======================================== D0E: no input left ======================================== *)
Lemma eh_piece_D0E : forall cx POST rest i k,
hsu_start_M01 rsegs B headamp_himg_B cx rest -> e0_from_DIG B MT cx POST rest i k ->
hsu_from_D0E rsegs B MT headamp_himg_B headamp_bld_B cx POST rest i k.
Proof.
intros cx POST rest i k Hst HDIG.
unfold hsu_from_D0E. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es Hlps Hles Hcut.
destruct Hcut as (Hb & Hat & Hfsh & Hppat & He).
destruct (eh_base_ctx B MT cx sh np ps cnt es rest [] [] ly2 S2 W2 regs2 mem2 md2 Hst Hb)
  as (Hctx & HFapp & Hppapp & Hpp2).
destruct (eh_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx)
  as (HF32 & HF0 & HFc & HRc & HR0 & HR1 & Has & _).
pose proof (@asan_consts rc) as (C1 & _).
assert (Hcur : 0 <= hsu_cur rsegs cx rest [] < 2 ^ 64).
{ pose proof Hb as (_ & Hin & _). destruct Hin as (Hel & _ & _ & _ & _ & Hs0 & Hs63 & _).
  unfold hsu_cur. cbn [length Z.of_nat]. lia. }
assert (Hat0 : hsu_at_cx rsegs cx W2 mem2 regs2 (hsu_L_Dc rsegs cx sh np ps cnt es)).
{ pose proof Hat as Hat'. unfold hsu_at_cx, hsu_at in Hat' |- *.
  apply Forall_app in Hat' as [Hat' _]. exact Hat'. }
pose proof (eh_at_get _ _ _ _ _ (LReg 9) _ Hat ltac:(eh_in)) as R9. cbn [hd_at] in R9.
pose proof (eh_at_get _ _ _ _ _ (LReg 19) _ Hat ltac:(eh_in)) as R19. cbn [hd_at] in R19.
pose proof (eh_at_get _ _ _ _ _ (LReg 21) _ Hat ltac:(eh_in)) as R21. cbn [hd_at] in R21.
pose proof (eh_at_get _ _ _ _ _ (LReg 23) _ Hat ltac:(eh_in)) as R23. cbn [hd_at] in R23.
pose proof (eh_at_get _ _ _ _ _ (LCell XR 0xc8) _ Hat ltac:(eh_in)) as V58. cbn [hd_at hd_xv] in V58.
unfold HSU_CH in V58. rewrite Z.mod_small in V58 by lia.
change (bi_D0E headamp_bld_B) with EH_D0E.
eapply SRr_bind.
{ exact (eh_TE B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ _ Hctx R9 R19 R21 Hcur V58). }
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hp3 &
  ((R5' & R6' & R13' & R18' & R26' & R28') & R7' & (Z1 & Z2 & V3))).
change (mkCfg (mkst regs3 (Z_to_bv 64 E0_DIG) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs E0_DIG regs3 mem3 md3).
apply (HDIG ly2 S2 W2 regs3 mem3 md3 sh np ps cnt es [] [] 0 0 Hlps Hles).
apply (eh_build_DIG B MT cx sh np ps cnt es rest [] [] [] 0 0 ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
  Hst Hb Hat0 Hfsh Hppat He HJ3 Hio3).
- apply (eh_keep1 regs2 regs3 [5; 6; 7; 13; 18; 26; 28]%bv Hk3). eh_sub'.
- exact Hm3.
- exact Z1.
- exact Z2.
- exact V3.
- exact R6'.
- exact R18'.
- exact R26'.
- exact R13'.
- exact R5'.
- exact R28'.
- exact R7'.
- eh_kr' Hk3 R23.
- exact (eh_suffix_nil rest).
- reflexivity.
- reflexivity.
- lia.
- lia.
Qed.

(* ======================================== D: the kind byte read ======================================== *)
Lemma eh_piece_D : forall cx POST rest i k kd,
hsu_start_M01 rsegs B headamp_himg_B cx rest -> kd mod 10 = 0 ->
e0_from_DIG B MT cx POST rest i k -> e0_from_ODD B MT cx POST rest i k ->
hsu_from_D rsegs B MT headamp_himg_B headamp_bld_B cx POST rest i k kd.
Proof.
intros cx POST rest i k kd Hst Hkd HDIG HODD.
unfold hsu_from_D. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r Hlps Hles Hcut.
replace (hsu_pc_D headamp_bld_B kd) with EH_D by (unfold hsu_pc_D; rewrite Hkd; reflexivity).
pose proof (cj_D_facts B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 Hst Hcut) as
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hc1 & Hc2 & _).
pose proof (cj_D_input B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 Hst Hcut) as
  (Hg & Hra & _ & Ham & Hdis).
destruct Hcut as (Hb & Hat & Hfsh & Hppat & He & Hsrr & Hkdr & Hkd8 & Hrr).
destruct (eh_base_ctx B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 Hst Hb)
  as (Hctx & HFapp & Hppapp & Hpp2).
destruct (eh_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx)
  as (HF32 & HF0 & HFc & HRc & HR0 & HR1 & Has & _).
pose proof (@asan_consts rc) as (C1 & _).
destruct (eh_sF (e_F (x_e cx)) ltac:(lia) ltac:(lia)) as [SF0 SF1].
assert (HF8 : e_F (x_e cx) mod 8 = 0).
{ apply (proj2 (Z.mod_divide (e_F (x_e cx)) 8 ltac:(lia))). apply (proj1 (Z.mod_divide _ 32 ltac:(lia))) in HF32.
  destruct HF32 as [q Hq]. exists (4 * q). lia. }
assert (Hat0 : hsu_at_cx rsegs cx W2 mem2 regs2 (hsu_L_Dc rsegs cx sh np ps cnt es)).
{ pose proof Hat as Hat'. unfold hsu_at_cx, hsu_at, hsu_L_D in Hat' |- *.
  apply Forall_app in Hat' as [Hat' _]. exact Hat'. }
pose proof (eh_at_get _ _ _ _ _ (LReg 9) _ Hat ltac:(eh_in)) as R9. cbn [hd_at] in R9.
pose proof (eh_at_get _ _ _ _ _ (LReg 19) _ Hat ltac:(eh_in)) as R19. cbn [hd_at] in R19.
pose proof (eh_at_get _ _ _ _ _ (LReg 27) _ Hat ltac:(eh_in)) as R27. cbn [hd_at] in R27.
pose proof (eh_at_get _ _ _ _ _ (LReg 17) _ Hat ltac:(eh_in)) as R17. cbn [hd_at] in R17.
pose proof (eh_at_get _ _ _ _ _ (LReg 18) _ Hat ltac:(eh_in)) as R18. cbn [hd_at] in R18.
pose proof (eh_at_get _ _ _ _ _ (LReg 6) _ Hat ltac:(eh_in)) as R6. cbn [hd_at] in R6.
pose proof (eh_at_get _ _ _ _ _ (LReg 20) _ Hat ltac:(eh_in)) as R20. cbn [hd_at] in R20.
pose proof (eh_at_get _ _ _ _ _ (LReg 7) _ Hat ltac:(eh_in)) as R7. cbn [hd_at] in R7.
pose proof (eh_at_get _ _ _ _ _ (LReg 16) _ Hat ltac:(eh_in)) as R16. cbn [hd_at] in R16.
pose proof (eh_at_get _ _ _ _ _ (LReg 23) _ Hat ltac:(eh_in)) as R23. cbn [hd_at] in R23.
pose proof (eh_at_get _ _ _ _ _ (LCell XR 0xc8) _ Hat ltac:(eh_in)) as V58. cbn [hd_at hd_xv] in V58.
unfold HSU_CH in V58. rewrite Z.mod_small in V58 by lia.
pose proof Hb as (_ & _ & Hsufr & _).
destruct rr as [|kb rr0]; [contradiction|].
cbn [Cursor.fuzz_u8] in Hkdr. injection Hkdr as Ekd Er. subst rr0.
assert (Hkd' : fst (Cursor.fuzz_u8 (kb :: r)) mod 10 = 0) by (cbn [Cursor.fuzz_u8 fst]; rewrite <- Ekd; exact Hkd).
clear Hkd Ekd Hkd8 Hrr.
(* the input bytes and their shadow keep their values across a block that writes only the frame's shadow row *)
assert (Hin_keep : forall (m : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> ~ eh_wT (e_F (x_e cx)) a -> aview rsegs (w_H W2) m a = aview rsegs (w_H W2) mem2 a) ->
  forall a, hsu_cur rsegs cx rest r <= a < hsu_cur rsegs cx rest r + Z.of_nat (length r) ->
  aview rsegs (w_H W2) m a = aview rsegs (w_H W2) mem2 a /\
  aview rsegs (w_H W2) m (shadow_of_addr SHADOW_OFF a) = aview rsegs (w_H W2) mem2 (shadow_of_addr SHADOW_OFF a)).
{ intros m Hm a Ha.
  pose proof Ham as Ham'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham'.
  pose proof (hm_shadow_band a ltac:(unfold kHighMemEnd; lia)) as Hsb. unfold kLowMemEnd, kHighMemBeg in Hsb.
  pose proof (eh_sh_not_row _ a HF8 (proj1 (proj2 (Hdis a Ha)))) as Hnr.
  split; apply Hm; try lia; cbv [eh_wT]; lia. }
destruct r as [|cb [|pb r3]].
- (* r = []: c = p = 0, the cursor does not move *)
  eapply SRr_bind.
  { exact (eh_T0 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ (hsu_cur rsegs cx rest []) Hctx R9 R19 R20 R18
      ltac:(cbn [length Z.of_nat] in Hc2; lia) V58). }
  intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hp3 &
    ((R5' & R6' & R13' & R18' & R26' & R28') & (Z1 & Z2 & V3))).
  change (mkCfg (mkst regs3 (Z_to_bv 64 E0_DIG) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs E0_DIG regs3 mem3 md3).
  apply (HDIG ly2 S2 W2 regs3 mem3 md3 sh np ps cnt es [kb] [] 0 0 Hlps Hles).
  apply (eh_build_DIG B MT cx sh np ps cnt es rest [kb] [] [] 0 0 ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    Hst Hb Hat0 Hfsh Hppat He HJ3 Hio3).
  + apply (eh_keep1 regs2 regs3 [5; 6; 13; 18; 20; 21; 26; 28]%bv Hk3). eh_sub'.
  + exact Hm3.
  + exact Z1.
  + exact Z2.
  + exact V3.
  + exact R6'.
  + exact R18'.
  + exact R26'.
  + exact R13'.
  + exact R5'.
  + exact R28'.
  + eh_kr' Hk3 R7.
  + eh_kr' Hk3 R23.
  + exact (eh_suffix_nil rest).
  + exact Hkd'.
  + reflexivity.
  + lia.
  + lia.
- (* r = [c]: c read, p = 0 *)
  change (Z.of_nat (length [cb])) with 1 in Hc2, R20, R6, Hra, Hdis, Hin_keep.
  destruct (Hg 0%nat ltac:(cbn; lia)) as [Vc _]. cbn [nth hd_zbytes map Z.of_nat] in Vc. rewrite Z.add_0_r in Vc.
  pose proof (Cursor.byte_range cb) as Bc.
  eapply SRr_bind.
  { exact (eh_T1 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ 1 Hctx R19 R20 ltac:(lia)). }
  intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hp3 & Z3).
  change (mkCfg (mkst regs3 (Z_to_bv 64 EH_K) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs EH_K regs3 mem3 md3).
  assert (Hctx3 : eh_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) (x_k cx) ly2 S2 W2 mem3 md3 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx))
    by (destruct Hctx as (_ & Hc); exact (conj HJ3 Hc)).
  eapply SRr_bind.
  { refine (eh_K1 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 _ _ _ (hsu_cur rsegs cx rest [cb]) (bv_unsigned cb) Hctx3
      _ _ _ _ _ _ Hc1 ltac:(lia) _ Bc _ _).
    - eh_kr' Hk3 R9.
    - eh_kr' Hk3 R27.
    - eh_kr' Hk3 R17.
    - eh_kr' Hk3 R18.
    - eh_kr' Hk3 R16.
    - eh_kr' Hk3 R6.
    - eapply val_mem_kept; [|exact Vc]. intros q Hq. cbn in Hq.
      exact (proj1 (Hin_keep mem3 Hm3 (hsu_cur rsegs cx rest [cb] + q) ltac:(lia))).
    - apply (hm_ra_kept rsegs _ _ _ _ _ _ _ Hra). intros x Hx. exact (proj2 (Hin_keep mem3 Hm3 x Hx)).
    - intros X. apply (proj1 (Hdis (hsu_cur rsegs cx rest [cb]) ltac:(lia))). lia. }
  intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hk4 & Hm4 & Hp4 & (K13 & K6 & K26 & K28 & V4)).
  change (mkCfg (mkst regs4 (Z_to_bv 64 EH_CH) mem4 (seg_rom rsegs)) md4) with (cfg_at rsegs EH_CH regs4 mem4 md4).
  assert (Hm34 : forall a, 0 <= a < 2 ^ 64 -> ~ eh_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a ->
    aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem2 a)
    by (apply (eh_mem2 _ mem2 mem3 mem4 _ _ _ Hm3 Hm4); cbv [eh_wTCN]; tauto).
  apply (eh_after_K cx POST rest i k sh np ps cnt es (kb :: [cb]) [cb] [] (bv_unsigned cb) 0
    ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 Hst HDIG HODD Hlps Hles Hb Hat0 Hfsh Hppat He).
  + destruct Hctx as (_ & Hc). exact (conj HJ4 Hc).
  + exact (same_io_trans _ _ _ Hio3 Hio4).
  + apply (eh_keep2 regs2 regs3 regs4 [] [6; 10; 11; 12; 13; 16; 18; 26; 28]%bv eh_clob Hk3 Hk4). eh_sub'.
  + exact Hm34.
  + apply (eh_zero_kept W2 mem3 mem4 _ 4 12 Z3). intros q Hq. apply Hm4; [lia | cbv [eh_wN]; lia].
  + replace (hsu_cur rsegs cx rest []) with (hsu_cur rsegs cx rest [cb] + 1) by (unfold hsu_cur; cbn [length]; lia).
    exact V4.
  + eapply val_mem_kept; [|exact V58]. intros q Hq. apply Hm34; [lia | apply eh_cell_out; lia].
  + exact K6.
  + exact K26.
  + exact K13.
  + exact K28.
  + rewrite Hk4; [|cbv; discriminate | eh_notin']. eh_kr' Hk3 R7.
  + rewrite Hk4; [|cbv; discriminate | eh_notin']. eh_kr' Hk3 R23.
  + rewrite Hk4; [|cbv; discriminate | eh_notin']. eh_kr' Hk3 R9.
  + rewrite Hk4; [|cbv; discriminate | eh_notin']. eh_kr' Hk3 R19.
  + exact (eh_suffix_tl rest [] cb Hsufr).
  + exact Hkd'.
  + reflexivity.
  + exact Bc.
  + lia.
- (* r = c :: p :: r3: both read *)
  destruct (Hg 0%nat ltac:(cbn; lia)) as [Vc _]. cbn [nth hd_zbytes map Z.of_nat] in Vc. rewrite Z.add_0_r in Vc.
  destruct (Hg 1%nat ltac:(cbn; lia)) as [Vp _]. cbn [nth hd_zbytes map Z.of_nat] in Vp.
  pose proof (Cursor.byte_range cb) as Bc. pose proof (Cursor.byte_range pb) as Bp.
  assert (Hn2 : 2 <= Z.of_nat (length (cb :: pb :: r3))) by (cbn [length]; lia).
  eapply SRr_bind.
  { exact (eh_T1 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ (Z.of_nat (length (cb :: pb :: r3))) Hctx R19 R20
      ltac:(lia)). }
  intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hp3 & Z3).
  change (mkCfg (mkst regs3 (Z_to_bv 64 EH_K) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs EH_K regs3 mem3 md3).
  assert (Hctx3 : eh_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) (x_k cx) ly2 S2 W2 mem3 md3 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx))
    by (destruct Hctx as (_ & Hc); exact (conj HJ3 Hc)).
  eapply SRr_bind.
  { refine (eh_K2 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 _ _ _ (hsu_cur rsegs cx rest (cb :: pb :: r3))
      (Z.of_nat (length (cb :: pb :: r3))) (bv_unsigned cb) (bv_unsigned pb) Hctx3
      _ _ _ _ _ _ ltac:(lia) Hc1 ltac:(lia) _ Bc _ Bp _ _).
    - eh_kr' Hk3 R9.
    - eh_kr' Hk3 R27.
    - eh_kr' Hk3 R17.
    - eh_kr' Hk3 R18.
    - eh_kr' Hk3 R16.
    - eh_kr' Hk3 R6.
    - eapply val_mem_kept; [|exact Vc]. intros q Hq. cbn in Hq.
      exact (proj1 (Hin_keep mem3 Hm3 (hsu_cur rsegs cx rest (cb :: pb :: r3) + q) ltac:(lia))).
    - eapply val_mem_kept; [|exact Vp]. intros q Hq. cbn in Hq.
      exact (proj1 (Hin_keep mem3 Hm3 (hsu_cur rsegs cx rest (cb :: pb :: r3) + 1 + q) ltac:(lia))).
    - apply (hm_ra_kept rsegs _ _ _ _ _ _ _ (range_addressable_sub _ _ _ _ (hsu_cur rsegs cx rest (cb :: pb :: r3)) 2
        Hra ltac:(lia) ltac:(lia))).
      intros x Hx. exact (proj2 (Hin_keep mem3 Hm3 x ltac:(lia))).
    - intros a Ha X. apply (proj1 (Hdis a ltac:(lia))). lia. }
  intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hk4 & Hm4 & Hp4 & (K13 & K6 & K26 & K28 & V4)).
  change (mkCfg (mkst regs4 (Z_to_bv 64 EH_CH) mem4 (seg_rom rsegs)) md4) with (cfg_at rsegs EH_CH regs4 mem4 md4).
  assert (Hm34 : forall a, 0 <= a < 2 ^ 64 -> ~ eh_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a ->
    aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem2 a)
    by (apply (eh_mem2 _ mem2 mem3 mem4 _ _ _ Hm3 Hm4); cbv [eh_wTCN]; tauto).
  apply (eh_after_K cx POST rest i k sh np ps cnt es (kb :: cb :: pb :: r3) (cb :: pb :: r3) r3
    (bv_unsigned cb) (bv_unsigned pb)
    ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 Hst HDIG HODD Hlps Hles Hb Hat0 Hfsh Hppat He).
  + destruct Hctx as (_ & Hc). exact (conj HJ4 Hc).
  + exact (same_io_trans _ _ _ Hio3 Hio4).
  + apply (eh_keep2 regs2 regs3 regs4 [] [6; 10; 11; 12; 13; 16; 18; 26; 28]%bv eh_clob Hk3 Hk4). eh_sub'.
  + exact Hm34.
  + apply (eh_zero_kept W2 mem3 mem4 _ 4 12 Z3). intros q Hq. apply Hm4; [lia | cbv [eh_wN]; lia].
  + replace (hsu_cur rsegs cx rest r3) with (hsu_cur rsegs cx rest (cb :: pb :: r3) + 2)
      by (unfold hsu_cur; cbn [length]; lia).
    exact V4.
  + eapply val_mem_kept; [|exact V58]. intros q Hq. apply Hm34; [lia | apply eh_cell_out; lia].
  + replace (Z.of_nat (length r3)) with (Z.of_nat (length (cb :: pb :: r3)) - 2) by (cbn [length]; lia). exact K6.
  + exact K26.
  + exact K13.
  + exact K28.
  + rewrite Hk4; [|cbv; discriminate | eh_notin']. eh_kr' Hk3 R7.
  + rewrite Hk4; [|cbv; discriminate | eh_notin']. eh_kr' Hk3 R23.
  + rewrite Hk4; [|cbv; discriminate | eh_notin']. eh_kr' Hk3 R9.
  + rewrite Hk4; [|cbv; discriminate | eh_notin']. eh_kr' Hk3 R19.
  + exact (eh_suffix_tl rest r3 pb (eh_suffix_tl rest (pb :: r3) cb Hsufr)).
  + exact Hkd'.
  + reflexivity.
  + exact Bc.
  + exact Bp.
Qed.

(* ======================================== the head ======================================== *)
Lemma e0_head : e0_head_stmt B MT.
Proof.
unfold e0_head_stmt. intros cx POST rest i k kd Hst Hkd HDIG HODD.
split; [exact (eh_piece_D cx POST rest i k kd Hst Hkd HDIG HODD) | exact (eh_piece_D0E cx POST rest i k Hst HDIG)].
Qed.

End g.

Print Assumptions e0_head.

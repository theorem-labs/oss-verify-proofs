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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Hd.v, with its module paths and module names changed; 118 of its 151 lines of code are new or changed and 703 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostTop.v at 01f4363fe7d, for image B of
   reac-pw/fuzz_headamp: w10t_ -> hw10p_, rs_ -> hsu_ (the cut states of lib/AU/HPgSeg.v), rm_ -> hm_, rl_ -> hd_;
   the entry states walk image B's own code (the arms split on what is left of the input as image B's tests do:
   0, 1, 2, 3, >= 4 bytes), with image B's UBSan tests decided by the atoms' range facts, the pod block reached from
   one atom (pp) whose 19744 bytes are one shadow entry, and pp->len's shadow address reloaded from R+0x150. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the post piece of the image-B builder,
   P 0x82bec / P1 0x82bf0 -> R 0x82e2c / RT 0x82ec8 / C2 0x82efc of LLVMFuzzerTestOneInput (0x80c40), pod.h:440-448.
   Proves no function (kind: segment lemma).
   hw10p_P1: P1 by the length of what is left of the input (HPgW10PostK.hw10p_P1_0, HPgW10PostN.hw10p_P1_1 .. _3,
   HPgW10Post4.hw10p_P1_4); hw10p_P_step: P's one instruction `mv a7,s2`, then P1; hw10_post: the statement
   hsu_piece_W10_post_stmt (lib/AU/HPgSeg.v). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgW10Kit HPgW10Req HPgW10PostK HPgW10PostN HPgW10Post4.
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

(* ---- P1 0x82bf0: every length of what is left of the input ---- *)
Lemma hw10p_P1 : forall cx POST rest,
  hsu_start_M01 rsegs B headamp_himg_B cx rest ->
  (forall kk, hsu_from_R rsegs B MT headamp_himg_B headamp_bld_B cx POST rest kk) ->
  hsu_from_RT rsegs B MT headamp_himg_B headamp_bld_B cx POST rest ->
  hsu_from_C2 rsegs B MT headamp_himg_B cx POST rest ->
  hsu_from_P1 rsegs B MT headamp_himg_B headamp_bld_B cx POST rest.
Proof.
intros cx POST rest Hst HR HRT HC2. destruct Hst as (HP & _ & _ & _).
unfold hsu_from_P1. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r HP1.
change (bi_P1 headamp_bld_B) with HW10_P1.
destruct r as [|c0 r1].
- exact (hw10p_P1_0 B MT cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps HP HC2 HP1).
- destruct r1 as [|x1 [|x2 [|x3 r4]]].
  + exact (hw10p_P1_1 B MT cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps [c0] HP HRT HC2 HP1 eq_refl).
  + exact (hw10p_P1_2 B MT cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps [c0; x1] HP HRT HC2 HP1 eq_refl).
  + exact (hw10p_P1_3 B MT cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps [c0; x1; x2] HP HRT HC2 HP1 eq_refl).
  + exact (hw10p_P1_4 B MT cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps (c0 :: x1 :: x2 :: x3 :: r4) HP HR HRT HC2 HP1
      ltac:(cbn [length]; lia)).
Qed.

(* ---- P 0x82bec `mv a7,s2`: one step to P1 ---- *)
Lemma hw10p_P_step : forall cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps r,
  hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) ->
  hsu_from_P1 rsegs B MT headamp_himg_B headamp_bld_B cx POST rest ->
  hsu_cut_P rsegs B MT headamp_himg_B cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  SRr rsegs W2 (cfg_at rsegs HW10_P regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps r HP HP1 (HB & HL).
pose proof HB as (HC & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Hsh & Hnp & Hnps & Hps).
pose proof hw10_wx as Hwx. pose proof hw10_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (hw10_ctx B MT cx _ ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR32 & HRS & HSTK & Hceil & H47 & HAR).
unfold T_SEG_STK, ASTACK in HSTK.
destruct (hw10_F_ctx B cx _ HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HL as HL0.
unfold hsu_at_cx, hsu_at, hsu_L_P in HL. cbv zeta in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P27 & Q08 & Q18 & Q20 & Q28 & Q30 & Q38 & Q48 & Qe0 & Qf0 & Q108 & Q120 & Q138
  & Q148 & Q150 & P18 & P28 & _).
cbn [fst snd hd_at hd_xv] in P18, P28.
pose proof HC as (HJ & _).
remember (Ereg regs2 []) as E eqn:HE.
assert (HS : st_ok rsegs E (mkSS HW10_P sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 HW10_P) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - unfold facts_ok. cbn. tauto. }
assert (SHOK : sh_ok rsegs hw10_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (HAE0 : env_agree 33 E E) by apply env_agree_refl.
unfold cfg_at. change (w64 HW10_P) with (Z_to_bv 64 HW10_P).
aj_run_to_tok hw10_tbl_ok HS HJ SHOK hw10_Bspan HW10_P1.
all: try solve [awr_ok_tac].
lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ =>
  assert (HAE : env_agree 33 E E') by env_agree_chain HAE0;
  assert (HAE32 : env_agree 32 (Ereg regs2 []) E')
    by (rewrite <- HE; eapply env_agree_le; [|exact HAE]; lia) end.
assert (HK : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply (hw10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr. destruct Hr. }
pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2) [Z_to_bv 5 17] HS HAE32
  ltac:(vm_compute; reflexivity)) as RK.
assert (R17 : getr (ms_regs ms) (Z_to_bv 5 17) = w64 (hsu_cur rsegs cx rest r)).
{ apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 17) 33 (SOff 18 0) _ HS HAE); [vm_compute; reflexivity | reflexivity |].
  apply hw10_den_atom. subst E. rewrite (ew_Ereg_nat regs2 _ 18 (Z_to_bv 5 18) eq_refl). exact P18. }
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
apply (HP1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh np ps r).
split.
- split; [|split; [|split]].
  + apply (hw10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun _ => False) HC HJ).
    * intros rr Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
      apply hw10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
    * apply HPgSteps.same_io_wvb.
    * intros a Ha _. exact (HK a Ha).
    * intros a [].
  + apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_F (x_e cx)) (hsu_P0 headamp_himg_B) Hfsh).
    intros i Hi. apply HK. change (length (hsu_P0 headamp_himg_B)) with 116%nat in Hi.
    pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)).
    assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
    unfold shadow_addr, SHADOW_OFF. lia.
  + apply (hm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_pp (x_e cx)) _ Hpp).
    intros x Hx. apply HK. destruct (hw10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
    assert (HLI : Z.of_nat (length (pc_image (PbCut sh ps None))) = PP_SIZE).
    { unfold pc_image. apply length_pp_image; [unfold POD_BUF_MAX in *; lia | |].
      - rewrite (pc_ents_final sh ps None). exact HW3.
      - rewrite (pc_ents_final sh ps None). exact HW4. }
    rewrite HLI in Hx. unfold PP_SIZE in Hx. lia.
  + exact (conj Hin (conj Hsuf (conj Hwf (conj Hlen (conj Hsh (conj Hnp (conj Hnps Hps))))))).
- unfold hsu_at_cx, hsu_at. apply Forall_app. split.
  + apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _
      (proj1 (proj1 (Forall_app _ _ _) HL0))).
    intros f Hf. unfold hsu_L_P in Hf. cbv zeta in Hf.
    repeat (destruct Hf as [<-|Hf]; [cbn [fst hm_keeps hd_xv];
      first [ solve [apply RK; [vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity]]
            | solve [intros i Hi; apply HK; unfold T_SEG_STK, ASTACK in *; lia] ] |]).
    destruct Hf.
  + apply Forall_cons; [exact R17|]. apply Forall_cons; [|apply Forall_nil].
    cbn [fst snd hd_at]. rewrite RK; [exact P28 | vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity].
Qed.

(* ---- the piece: HPgSeg.hsu_piece_W10_post_stmt ---- *)
Theorem hw10_post : hsu_piece_W10_post_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof.
unfold hsu_piece_W10_post_stmt. intros cx POST rest Hst HR HRT HC2.
pose proof (hw10p_P1 cx POST rest Hst HR HRT HC2) as HP1.
split; [|exact HP1].
unfold hsu_from_P. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r HcP.
destruct Hst as (HP & _).
exact (hw10p_P_step cx POST rest ly2 S2 W2 regs2 mem2 md2 sh np ps r HP HP1 HcP).
Qed.

End t.

Print Assumptions hw10p_P1.
Print Assumptions hw10p_P_step.
Print Assumptions hw10_post.

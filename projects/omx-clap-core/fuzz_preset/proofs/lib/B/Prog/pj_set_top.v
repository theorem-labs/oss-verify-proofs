(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the TOP of pj_set's image-B walk (fuzz_preset asan-ubsan, B 0x86e8c, 115 instructions;
   preset_file.c :373-392): the segments of lib/B/Prog/pj_set_seg_*.v composed into the text.
   proves pj_set (image B', asan-ubsan d663f82d) against the kit's tpj_set_specX ITSELF (lib/A/PRH_FnPj.v: ENTRY-keyed,
   the run keyed on ReaderRes.jr_strtod, cf_head = PresetReqAt.HEAD and a run of at most 4 calls among its premises;
   its post with DEAD-PJSET, the block Permutations and the FREEORD-COPY ordered free lists of the result, its goal
   the re-hiding form: SRr' over preset's zone with the post fpostWmR at YA0nH.wle'): tpj_set_specX_holds, and at
   preset's instance tpj_set_specX_B_preset.
   Callee texts (pj_set_defs.v pjs_texts, cited, never unfolded), all the kit's: tpj_get_specX, tpj_free_specX,
   tgrow_specX and tfuzz_strdup_specX (the last three in the post-implication form; pj_free's and grow's posts at
   wle'), and the m-form __asan_memcpy / __asan_memset texts (YGcallMxmn.v aintrin_realizes_xm).
   Section premises: LAWS (YCbqG.v AR_laws_x at the harness head length cf_head), VIS (pj_set_defs.v pjs_g_vis: the
   MARKED shadow-visibility facts; at the preset instance pj_set_vis_inst.v pjs_g_vis_preset, with its vm_compute
   witnesses at YD2l.TfibB), PAL (YC1fP.v PALib: the unit's image binding of B; at the preset instance
   lib/B/PALibB.v exvi_eh_palib), HULL (pj_set_defs.v pjs_g_hull: the hull budget at a run position, which pays the
   three allocating callees' hull premises from the run of at most 4 calls; at the preset instance
   pj_set_vis_inst.v pjs_hull_preset, from lib/A/PresetHullPay.v hull_budget_of_room_pos). LAWS at the preset
   instance: PALibB.exvi_eh_laws.
   The post is pj_set_defs.v pjs_Q, the kit's named post tpsP_Q; the walk's goal pjs_FIN is the kit's fpostWmR at wle'. The
   frame's keep is pj_set_seg_epi.v's at wle (pj_get's call, before any free) and at wle' (the calls after one).
   Numerals: none. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcallMxmn YG0ncf YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_set_defs pj_set_seg_epi
  pj_set_seg_tail pj_set_seg_fail pj_set_seg_ent pj_set_seg_c1 pj_set_seg_ret pj_set_seg_miss pj_set_seg_dup
  pj_set_vis_inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VIS : pjs_g_vis B ARx.
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PA) B.
Hypothesis HULL : @pjs_g_hull cp.

(* each segment theorem takes the Section premises it uses (some quantify the head length hl explicitly), so each is
   applied at the first argument list that fits and its remaining premises are found in the context *)
Ltac pjs_seg X := let H := fresh "HS" in
  first [ pose proof (X B ARx cf_head LAWS) as H | pose proof (X B ARx LAWS) as H | pose proof (X B ARx) as H ];
  repeat match type of H with ?A -> _ => specialize (H ltac:(assumption)) end;
  apply H; assumption.

(* the composition: every segment, its successors' statements discharged; the head premise (the kit's cf_head =
   PresetReqAt.HEAD, which every segment's pjs_pre also carries) gives the section premise prh_head_wide of the
   segments that write a 56-byte struct into a live block *)
Theorem pjs_walk_holds : forall CTX0 dd, pjs_texts B ARx CTX0 dd -> cf_head = PresetReqAt.HEAD ->
  pjs_seg_entry B ARx CTX0 dd.
Proof.
intros CTX0 dd TXT Hhd. pose proof (pjs_head_wide Hhd) as HW8.
assert (KEEP : pjs_frame_kept_stmt B ARx dd) by pjs_seg pjs_frame_kept_holds.
assert (KEEPR : pjs_frame_kept_stmtR B ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) dd) by pjs_seg pjs_frame_kept_holdsR.
assert (EPI : pjs_seg_epi B ARx CTX0 dd) by pjs_seg pjs_seg_epi_holds.
assert (TAIL : pjs_seg_tail B ARx CTX0 dd) by pjs_seg pjs_seg_tail_holds.
assert (FAIL : pjs_seg_fail B ARx CTX0 dd) by pjs_seg pjs_seg_fail_holds.
assert (DUP : pjs_seg_dup B ARx CTX0 dd) by pjs_seg pjs_seg_dup_holds.
assert (MISS : pjs_seg_miss B ARx CTX0 dd) by pjs_seg pjs_seg_miss_holds.
assert (RET : pjs_seg_ret B ARx CTX0 dd) by pjs_seg pjs_seg_ret_holds.
assert (C1 : pjs_seg_c1 B ARx CTX0 dd) by pjs_seg pjs_seg_c1_holds.
pjs_seg pjs_seg_ent_holds.
Qed.

(* pj_set at image B': the kit's text itself *)
Theorem tpj_set_specX_holds : forall CTX0 dd, pjs_texts B ARx CTX0 dd ->
  tpj_set_specX (fx := fx) (cp := cp) (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx SK CTX0 dd.
Proof.
intros CTX0 dd TXT rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch d o k w ms tv D Dw num
  str kids keys n cap kname Lam peak cnt fail ran
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30
  H31 H32 H33 H34.
pose proof (pjs_walk_holds CTX0 dd TXT H33
  (MkPjsEnt ly S Hp W regs mem md ch d o k w ms tv D Dw num str kids keys n cap kname Lam peak cnt fail ran most own
     rp_x rp_os rp_i rp_H0 rp_hist)) as HW.
unfold pjs_pre, pjs_FIN, pjs_FP, pjs_Q, js_klen in HW. cbv zeta in HW.
cbn [js_ly js_S js_Hp js_W js_regs js_mem js_md js_ch js_d js_o js_k js_w js_ms js_tv js_D
  js_Dw js_num js_str js_kids js_keys js_n js_cap js_kname js_Lam js_peak js_cnt js_fail js_ran js_most js_own
  js_x js_os js_i js_H0 js_hist] in HW.
unfold tpsP_Q in HW.
apply HW.
repeat (split; [assumption|]). assumption.
Qed.

End top.

(* the head width at preset's instance is the model's *)
Lemma pjs_head_preset : @cf_head CfParams_preset = PresetReqAt.HEAD.
Proof. reflexivity. Qed.

(* ---- at preset's instance: CfParams_preset, B := YD2l.TfibB, ARx := YG0ncf.ARcf rsegs TfibB, with LAWS and PAL
   discharged by lib/B/PALibB.v (exvi_eh_laws, exvi_eh_palib), VIS by pj_set_vis_inst.v pjs_g_vis_preset and HULL by
   pj_set_vis_inst.v pjs_hull_preset: the kit's text tpj_set_specX itself, the callee texts at the instance its
   premises ---- *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CP) rsegs TB).
Theorem tpj_set_specX_B_preset : forall CTX0 dd,
  pjs_texts (fx := fx) (cp := CP) (SK := SK) TB ARI CTX0 dd ->
  tpj_set_specX (fx := fx) (cp := CP) (PI := prh_img_B) (L := B_prog_listing) (PA := PA) TB ARI SK CTX0 dd.
Proof.
intros CTX0 dd TXT.
exact (tpj_set_specX_holds (fx := fx) (cp := CP) TB ARI PALibB.exvi_eh_laws pjs_g_vis_preset PALibB.exvi_eh_palib
  pjs_hull_preset CTX0 dd TXT).
Qed.
End p.

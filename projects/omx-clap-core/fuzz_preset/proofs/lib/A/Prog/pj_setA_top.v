(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the TOP of pj_set's image-A' walk (fuzz_preset asan, pin 1be0f53d96cb, unstripped twin
   bff8519bbe3e; A 0x8685c, 88 instructions; preset_file.c :373-392): the segments of lib/A/Prog/pj_setA_seg_*.v
   composed into the contract text.
   proves pj_set (image A') against tpj_set_specX ITSELF (lib/A/PRH_FnPj.v: ENTRY-keyed, the run keyed on
   ReaderRes.jr_strtod, a run of at most 4 calls and cf_head = PresetReqAt.HEAD among its premises; it concludes at
   the re-hiding relation, YA0nH.SRr' at YGcfRehidePost.RZ_cf over fpostWmR at wle', since pj_free and grow free or
   reallocate; its post with DEAD-PJSET, the block Permutations and the FREEORD-COPY ordered free lists of the
   result): tpj_set_specX_A_holds, generic in fx, rc, ci, cp, RL, SK, B and ARx; at preset's ARcf instance
   tpj_set_specX_A_preset.
   Callee texts (pj_setA_defs.v pjsA_texts, cited, never unfolded): tpj_get_specX, tpj_free_specX, tgrow_specX and
   tfuzz_strdup_specX (the last three in the post-implication form), and the m-form __asan_memcpy / __asan_memset
   rows (YGcallMxmn.v aintrin_realizes_xm at the listing's pa_sigma).
   Section premises: LAWS (YCbqG.v AR_laws_x at the harness head length cf_head), VIS (pj_setA_defs.v pjsA_g_vis: the
   MARKED shadow-visibility facts; at the preset instance pj_setA_vis_inst.v pjsA_g_vis_preset, with its vm_compute
   witnesses at AD2l.TfibB), PAL (YC1fP.v PALib: the unit's image binding of B; at the preset instance
   lib/A/PALibA.v palib_A), HULL (pj_setA_defs.v pjsA_g_hull: the callees' hull budgets from a run position; at the
   preset instance pjsA_g_hull_preset, from lib/A/PresetHullPay.v hull_budget_of_room_pos). LAWS at the preset
   instance: PALibA.palib_laws_A.
   The post is pj_setA_defs.v pjsA_Q, the contract's post body (its kit name tpsP_Q); the walk's goal pjsA_FIN is its
   fpostWmR at wle'. The keep statement is used at both relations: at wle for pj_get's call (before any free), at
   wle' for the calls after pj_free or grow (pjsA_frame_kept_holdsR).
   Numerals: 2 ^ 30 (the request bound pjsA_g_hull names, DERIVED: cf_malloc_max at preset is below it). No
   ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcallMxmn YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PALibA PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import pj_setA_defs pj_setA_seg_epi pj_setA_seg_tail pj_setA_seg_fail pj_setA_seg_ent pj_setA_seg_c1 pj_setA_seg_ret pj_setA_seg_miss pj_setA_seg_dup pj_setA_vis_inst.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_A.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VIS : pjsA_g_vis B ARx.
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PA) B.
Hypothesis HULL : @pjsA_g_hull cp.

(* each segment theorem takes the Section premises it uses (some quantify the head length hl explicitly), so each is
   applied at the first argument list that fits and its remaining premises are found in the context *)
Ltac pjsA_seg X := let H := fresh "HS" in
  first [ pose proof (X B ARx cf_head LAWS) as H | pose proof (X B ARx LAWS) as H | pose proof (X B ARx) as H ];
  repeat match type of H with ?A -> _ => specialize (H ltac:(assumption)) end;
  apply H; assumption.

(* the composition: every segment, its successors' statements discharged; the head premise (the contract's cf_head =
   PresetReqAt.HEAD, which every segment's pjsA_pre also carries) gives the section premise prh_head_wide of the
   segments that write a 56-byte struct into a live block. The keep statement is taken at wle (pj_get's call) and at
   the re-hiding relation (the calls after a free or realloc). *)
Theorem pjsA_walk_holds : forall CTX0 dd, pjsA_texts B ARx CTX0 dd -> cf_head = PresetReqAt.HEAD ->
  pjsA_seg_entry B ARx CTX0 dd.
Proof.
intros CTX0 dd TXT Hhd. pose proof (pjsA_head_wide Hhd) as HW8.
assert (KEEP : pjsA_frame_kept_stmt B ARx dd) by pjsA_seg pjsA_frame_kept_holds.
assert (KEEPR : pjsA_frame_kept_stmtR B ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) dd)
  by exact (pjsA_frame_kept_holdsR B ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) dd).
assert (EPI : pjsA_seg_epi B ARx CTX0 dd) by pjsA_seg pjsA_seg_epi_holds.
assert (TAIL : pjsA_seg_tail B ARx CTX0 dd) by pjsA_seg pjsA_seg_tail_holds.
assert (FAIL : pjsA_seg_fail B ARx CTX0 dd) by pjsA_seg pjsA_seg_fail_holds.
assert (DUP : pjsA_seg_dup B ARx CTX0 dd) by pjsA_seg pjsA_seg_dup_holds.
assert (MISS : pjsA_seg_miss B ARx CTX0 dd) by pjsA_seg pjsA_seg_miss_holds.
assert (RET : pjsA_seg_ret B ARx CTX0 dd) by pjsA_seg pjsA_seg_ret_holds.
assert (C1 : pjsA_seg_c1 B ARx CTX0 dd) by pjsA_seg pjsA_seg_c1_holds.
pjsA_seg pjsA_seg_ent_holds.
Qed.

(* pj_set at image A': the contract text itself *)
Theorem tpj_set_specX_A_holds : forall CTX0 dd, pjsA_texts B ARx CTX0 dd ->
  tpj_set_specX (fx := fx) (cp := cp) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK CTX0 dd.
Proof.
intros CTX0 dd TXT rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch d o k w ms tv D Dw num
  str kids keys n cap kname Lam peak cnt fail ran
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30
  H31 H32 H33 H34.
pose proof (pjsA_walk_holds CTX0 dd TXT H33
  (MkPjsEntA ly S Hp W regs mem md ch d o k w ms tv D Dw num str kids keys n cap kname Lam peak cnt fail ran most own
     rp_x rp_os rp_i rp_H0 rp_hist)) as HW.
unfold pjsA_pre, pjsA_FIN, pjsA_FP, pjsA_Q, jsA_klen in HW. cbv zeta in HW.
cbn [jsA_ly jsA_S jsA_Hp jsA_W jsA_regs jsA_mem jsA_md jsA_ch jsA_d jsA_o jsA_k jsA_w jsA_ms jsA_tv jsA_D
  jsA_Dw jsA_num jsA_str jsA_kids jsA_keys jsA_n jsA_cap jsA_kname jsA_Lam jsA_peak jsA_cnt jsA_fail jsA_ran jsA_most jsA_own
  jsA_x jsA_os jsA_i jsA_H0 jsA_hist] in HW.
apply HW.
repeat (split; [assumption|]). assumption.
Qed.

End top.

(* the head width at preset's instance is the model's *)
Lemma pjsA_head_preset : @cf_head CfParams_preset = PresetReqAt.HEAD.
Proof. reflexivity. Qed.

(* the hull budget's instance fact at preset's instance: requests below cf_malloc_max = 2 ^ 28 + 2 ^ 27, and the
   meters' room for one call's counts at a run position (lib/A/PresetHullPay.v hull_budget_of_room_pos) *)
Lemma pjsA_g_hull_preset : @pjsA_g_hull CfParams_preset.
Proof.
split; [apply Z.leb_le; vm_compute; reflexivity|].
exact PresetHullPay.hull_budget_of_room_pos.
Qed.

(* ---- at preset's instance: CfParams_preset, B := AD2l.TfibB, ARx := ARcf rsegs TfibB, with LAWS and PAL
   discharged by lib/A/PALibA.v (palib_laws_A, palib_A), VIS by pj_setA_vis_inst.v pjsA_g_vis_preset and HULL by
   pjsA_g_hull_preset: the contract text tpj_set_specX itself, the callee texts at the instance its premises ---- *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_A.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation TB := AD2l.TfibB.
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CP) rsegs TB).
Theorem tpj_set_specX_A_preset : forall CTX0 dd,
  pjsA_texts (fx := fx) (cp := CP) (SK := SK) TB ARI CTX0 dd ->
  tpj_set_specX (fx := fx) (cp := CP) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) TB ARI SK CTX0 dd.
Proof.
intros CTX0 dd TXT.
exact (tpj_set_specX_A_holds (fx := fx) (cp := CP) TB ARI PALibA.palib_laws_A pjsA_g_vis_preset PALibA.palib_A
  pjsA_g_hull_preset CTX0 dd TXT).
Qed.
End p.

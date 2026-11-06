(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEGMENT PRO of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x830dc .. 0x831f4, 71 instructions, no call), in the form of this lane's
   lib/A/W_send_line_entry.v (a segment into a loop head) and of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v.  The statement is W_drain_cx.v dr_pro_stmt.

   The prologue saves the 13 callee-saved registers at 232(sp) .. 328(sp) of its 336-byte frame, keeps the
   relay entry s in s6 and its field addresses s->buf / s->used / s->cap in s10 / s11 / s9, spills
   &s->npartial, &s->overlong, &s->held to 208(sp) / 96(sp) / 128(sp), takes g_s by PAddHi (A_OBJ 22) into
   s2 with g_s >> 3 in s1 and (g_s + 4) >> 3 in s0, loads the shadow base from the GOT (A_OBJ 0 -> A_OBJ 32)
   into s5, and writes the shifted field addresses of g_s and the shadow addresses of s's cells into the
   frame.  No call, no shadow check, no store outside [sp0 - 336, sp0): every representation the outer loop's
   head carries lies below alloc_ceiling + 8 (a live block, the image band) and moves across the stores. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_pro.v, with its module paths, module names and numbers changed; 1682 of its 1766 lines of code are new or changed and 1187 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PjGetB.v, with its module paths and module names changed; 617 of its 693 lines of code are new or changed and 1690 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Caw102B.v, with its module paths and module names changed; 170 of its 211 lines of code are new or changed and 652 lines of the source are left out. *)
(* fuzz_preset, image B' (asan-ubsan, harness fix #102: pin sha256 d663f82d7f488d30, twin c90d4fa54d43160b): CB_Top,
   the composition of check_no_overread's segment walk CB0 .. CB9 (entry B' 0x819f0 = slot 201 of the whole-program
   listing) into the kit's text tcheck_no_overread_specX (lib/A/PRH_FnCheck.v c40cf3fdcd2a :738-823, the kit cut
   7cdbb61b5fa0; the post-implication form with the copies' outcome clause and the
   budgeted post fpostFbm .. (wbudget [] 6)), with the memnorm invariant instantiated ONCE: P := cnb_mn D (the
   contract's instance; cnb_mn_laws / cnb_mn_call / cnb_mn_mn). Row R7-7 of a Theorem Labs lane's internal file PART7-ROWS.md
   (a Theorem Labs lane; family lead a Theorem Labs lane). Template: lib/B/Prog/Caw102B_Top.v caw_B_top (a working branch).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma; the composition of the segments).
   INPUTS (blobs at this file's commit; contract head 0e85941c7687):
     THE CONTRACT lib/B/Prog/Cno102B_Base.v 06098b64f859: cnb_pre (the text's premises at one record, verbatim; no
     DW), every cut cnb_at_* / exit cnb_ex_*, cnb_set_fpos, cnb_mn, cnb_post = cnb_ex_ret (the text's post, verbatim).
     The step kit lib/B/Prog/Cno102B_Ro.v c1b5ec3f8fff. Nothing here re-states the contract.
     THE INTERFACE lib/B/Prog/Cno102B_TopIf.v: cnbt_endP (CB9's interface, concluding SRr' SEGS RZ_cf).
     SEGMENTS, every one PROVED on the cut and cited (none is a hypothesis here):
       CB0 Cno102B_E0.v 3b404952bba5 cnb_seg_e0, CB1 Cno102B_E1.v 45b31763c511 cnb_seg_poison, CB2 Cno102B_E2.v
       bdb6dddde994 cnb_seg_copies (it derives the refused copy's cnb_cdead from padded's outcome clause), CB3
       Cno102B_E3.v ae7bbec0b006 cnb_seg_init (a Theorem Labs lane's R7-4 cut re-fit);
       CB4 / CB5 / CB6 Cno102B_R4.v b5a7aa98d243 cnb_read1_seg / cnb_read2_seg / cnb_read3_seg (lane CnoB102rR);
       PN1 / PN2 / PN3 Cno102B_Rpn.v fba52589a562 cnb_pn1_step / cnb_pn2_step / cnb_pn3_step (no named premise);
       CB7 Cno102B_R7.v 67e8babfec8c cnb_cmp_seg / cnb_same1_step / cnb_same2_step;
       CB8 Cno102B_F.v 7e8f1f5343e1 cnb_seg_free : cnb_seg_freeP (no premise beyond the contract's: CNT24 derived and
       the trees' free order, the former PJF-TIE, from the free cut's cnb_fo);
       CB9 Cno102B_E9.v 3e20ff19944e cnb_seg_end : cnbt_endP (this row).
   THE CHAIN (forward): CB0 (entry -> CNB_FRAME, reaching cnb_set_fpos D p) -> CB1 -> CB2 -> CB3 -> CB4 (CNB_READ1 ->
     {CNB_FREE, CNB_PN1 -> PN1}) -> CB5 (CNB_READ2 -> {CNB_READ3, CNB_PN2 -> PN2}) -> CB6 (CNB_READ3 -> {CNB_CMP,
     CNB_PN3 -> PN3}) -> CB7 (CNB_CMP -> {CNB_FREE, the first same call -> {the second same call -> CNB_FREE,
     CNB_FREE}}) -> CB8 (CNB_FREE -> CNB_END) -> CB9 (CNB_END -> the return, cnb_ex_ret).
   THE MOVE (SCRATCH: the kit's restated texts, the re-hiding relation wle' SEGS RZ_cf): a free can hide shadow again, so
     a walk that crosses one concludes SRr' SEGS RZ_cf (YA0nH.v). CB0 .. CB4 run before the first parse_noting and
     stay plain SRr; each is lifted ONCE where it meets an SRr' continuation (cnbt_seq_up: SRr_SRr', then SRr'_bind).
     PN1 .. PN3, CB5 .. CB9 conclude SRr' and compose by cnbt_seq' (SRr'_bind, YSRrG.v); their cuts and exits are the
     Base's R forms at WLE' (cnb_ex_freeR / read2R / read3R / pn2R / pn3R / cmpR).
   THE CONCLUSION: cnb_B_top IS the kit's restated text at this file's parameters, `tcheck_no_overread_specX B ARcfx SK
     CTX0` (SRr' segs RZ_cf, the post fpostFbm at wle', the hull budget its LAST premise): its premises and its post
     verbatim, by construction.
   SECTION HYPOTHESES (one each, no duplicates; the segment files' names and texts):
     STATIC-LAYOUT image facts, witnessed at PI_prog_B / YD2l.TfibB on a working branch
     (Cno102B_Wit.v): PAL : PALib B (CB0's; CB8's / CB9's PALibCore B is its projection palib_core) = cnbw_pal;
     SM3 = cnbw_sm3; ISV (CB0's cnb0_img_shadow_vis over [pa_lo, pa_hi); CB2's IMG_SHADOW is the same text) =
     cnbw_isv, with cnbw_band_cf (pa_lo / pa_hi = CfImg_B's cf_img_lo / cf_img_top); HTOP (CB1's / CB3's
     cnb1_img_top) = cnbw_htop. IMG : cnb_img B = a Theorem Labs lane's Cno102B_Img.cnb_img_inst (PROVISIONAL on YCej).
     STATE premises: callee and runtime texts at every float state: ASM3 (the frame-class row), AMEMSET (CB3's
     __asan_memset row), HPAD (padded), HPN (parse_noting), HRO / HSAME (fuzz_alloc_ran_out / same), AFREE (the
     primed runtime free row with the memnorm keep, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep: the form CB8
     takes) / HPJF (pj_free), ASETSH (the __asan_set_shadow_f5 row, YGcallMxmn.aset_shadow_realizes_xm: CB8's /
     CB9's). CB8 takes no memnorm premise (memnorm is out of the cf layer's QMm_cf, round6j); no memnorm stand-in.
     The cf_head facts CB8 takes, prh_head_wide (CfParamsPreset.preset_head_wide) and prh_head16 (reflexivity), are
     discharged at CfParams_preset (Lets HWIDE / HEAD16). No named state premise is left at an inner cut.
     The cf laws AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B), proved here.
   Numerals: 0 (bi_fpos of the entry record: no premise and no post conjunct reads it; CB0 names the frame's
   position); 245 (WORD: the shadow byte 0xf5 of ASETSH, Cno102B_F.v's spelling). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
(* YK06 is NOT imported: its plain alloc_ceiling would shadow the RunCeil field YM05.alloc_ceiling *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm.
(* the step relation over the re-hide zone (SRr', YA0nH.v), its bind / mono (YSRrG.v), the fixed zone RZ_cf
   (YGcfRehidePost.v), and the primed runtime free row with the memnorm keep (YGcfMallocComposeKeep.v) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YGcallx YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcallMxmn YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_PjOrder PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Cno102B_Base Cno102B_TopIf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Cno102B_E0 Cno102B_E1 Cno102B_E2
  Cno102B_E3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Cno102B_R4 Cno102B_Rpn Cno102B_R7
  Cno102B_F Cno102B_E9.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* open one exit: its existential witnesses, then the configuration equation substituted *)
Ltac cnbt_open H :=
  hnf in H; repeat match type of H with ex _ => let x := fresh "x" in destruct H as [x H] end;
  destruct H as [-> H].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance prh_room_live_a8.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PA).
(* after a free the walk's worlds are related by wle' at the fixed re-hiding zone (YA0nH.v, YGcfRehidePost.v) *)
#[local] Notation WLE' := (wle' SEGS YGcfRehidePost.RZ_cf).

(* the memory at a cut configuration *)
Lemma cnbt_pm : forall (P : (word -> option byte) -> Prop) fxk pc regs mem md,
  P (ms_mem (cfg_ms (@cnb_cfg SEGS fxk pc regs mem md))) -> P mem.
Proof. intros P fxk pc regs mem md H. exact H. Qed.

(* one segment after another at the re-hiding relation (SRr' SEGS RZ_cf; SRr'_bind, YSRrG.v): the first one's exit
   cut and P at its memory start the second *)
Lemma cnbt_seq' : forall (W : world SEGS) c (R Q : world SEGS -> config -> Prop) (P : (word -> option byte) -> Prop),
  SRr' SEGS YGcfRehidePost.RZ_cf W c (fun W' c' => R W' c' /\ P (ms_mem (cfg_ms c'))) ->
  (forall W' c', R W' c' -> P (ms_mem (cfg_ms c')) -> SRr' SEGS YGcfRehidePost.RZ_cf W' c' Q) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c Q.
Proof.
intros W c R Q P H1 H2. apply (SRr'_bind SEGS YGcfRehidePost.RZ_cf W c _ Q H1). intros W' c' _ [HR HP].
exact (H2 W' c' HR HP).
Qed.
(* a segment before the first free (plain SRr) followed by one after it: the first is lifted once (SRr_SRr',
   YA0nH.v) *)
Lemma cnbt_seq_up : forall (W : world SEGS) c (R Q : world SEGS -> config -> Prop) (P : (word -> option byte) -> Prop),
  SRr SEGS W c (fun W' c' => R W' c' /\ P (ms_mem (cfg_ms c'))) ->
  (forall W' c', R W' c' -> P (ms_mem (cfg_ms c')) -> SRr' SEGS YGcfRehidePost.RZ_cf W' c' Q) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c Q.
Proof. intros W c R Q P H1 H2. exact (cnbt_seq' W c R Q P (SRr_SRr' SEGS YGcfRehidePost.RZ_cf W c _ H1) H2). Qed.

Section f.
Variable B : asyms.
(* the walk's allocator relation, the cf instance (CnoB102f's ARcfx, Cno102B_F.v; every segment file's) *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Variables (CTX0 : list (list Z)).

(* ---- STATIC-LAYOUT IMAGE FACTS (witnessed at PI_prog_B), each spelled as in its segment file ---- *)
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PA) B.
Hypothesis IMG : cnb_img (PA := PA) B.
Hypothesis SM3 : pc_stack_malloc (as_code B) CNB_CID = SIGMA AS___asan_stack_malloc_3.
Hypothesis ISV : cnb0_img_shadow_vis (PA := PA) B.
Hypothesis HTOP : Cno102B_E1.cnb1_img_top (PA := PA).
(* ---- STATE PREMISES: the callee and runtime texts, at every float state ---- *)
Hypothesis ASM3 : forall fz : YK11.FPState,
  YGcallMxmn.astack_malloc_realizes_xm (fx := fz) SEGS B (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md) CNB_CID.
Hypothesis AMEMSET : forall fz : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fz) SEGS B ARcfx OSet (SIGMA AS___asan_memset).
Hypothesis HPAD : forall fz : YK11.FPState, tpadded_specX (fx := fz) B ARcfx SK CTX0.
Hypothesis HPN : forall fz : YK11.FPState, tparse_noting_specX (fx := fz) B ARcfx SK CTX0.
Hypothesis HRO : forall fz : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fz) B ARcfx SK.
Hypothesis HSAME : forall fz : YK11.FPState, tsame_specX (fx := fz) B ARcfx SK DOC_D.
Hypothesis AFREE : forall fz : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fz) SEGS B.
Hypothesis HPJF : forall fz : YK11.FPState, tpj_free_specX (fx := fz) B ARcfx SK CTX0 DOC_D.
Hypothesis ASETSH : forall fz : YK11.FPState,
  YGcallMxmn.aset_shadow_realizes_xm (fx := fz) SEGS B ARcfx (SIGMA AS___asan_set_shadow_f5) 245.
(* ---- the two cf_head facts CB8 takes, discharged at the instance CfParams_preset ---- *)
Let HWIDE : PRH_Base.prh_head_wide := preset_head_wide.
Let HEAD16 : PRH_Base.prh_head16 := eq_refl.

(* ---- THE BODY, CB1 .. CB9: from the frame cut to the function's exit, for any record, generic P. CB1 .. CB4 run
   before the first free (plain SRr, each lifted once by cnbt_seq_up); from parse_noting on every segment concludes
   SRr' SEGS RZ_cf (cnbt_seq') ---- *)
Lemma cnbt_body : forall P : (word -> option byte) -> Prop,
  srr_inv_laws SEGS P -> srr_inv_call SEGS P -> srr_inv_mn SEGS P ->
  forall D, cnb_pre (fx := fx) B ARcfx CTX0 D ->
  forall fxk ly S Hp W regs mem md k,
  cnb_at_frame (fx := fx) (SK := SK) B ARcfx D fxk ly S Hp W regs mem md k -> P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc CNB_FRAME) regs mem md)
    (cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D).
Proof.
intros P PLAW PCALL PMN D HPRE.
(* the cf laws, the segments' LAWS *)
assert (LAWSx : AR_laws_x SEGS B ARcfx cf_head) by exact (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)).
(* CB8's and CB9's image binding PALibCore B, the projection of PAL *)
assert (PALC : PALibCore (L := B_prog_listing) (PI := PA) B) by (apply palib_core; exact PAL).
(* CB8 and CB9, proved (Cno102B_F.v, Cno102B_E9.v), at this file's Section hypotheses *)
assert (HCB8 : cnb_seg_freeP (fx := fx) B SK CTX0) by (eapply (cnb_seg_free (fx := fx)); eassumption).
assert (HCB9 : cnbt_endP (fx := fx) (SK := SK) B CTX0) by (eapply (cnb_seg_end (fx := fx) (SK := SK)); eassumption).
(* the continuations, from the return back to the frame cut *)
assert (Kend : forall W c, cnb_ex_end (fx := fx) B SK D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D)).
{ intros W c HE HP. cnbt_open HE. apply cnbt_pm in HP.
  eapply SRr'_mono; [eapply (HCB9 P PLAW PCALL PMN D); eassumption|].
  intros W' c' _ [HR _]. exact HR. }
assert (Kfree : forall W c, cnb_ex_freeR (fx := fx) (SK := SK) B ARcfx WLE' D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D)).
{ intros W c HE HP. cnbt_open HE. apply cnbt_pm in HP.
  eapply cnbt_seq'; [eapply (HCB8 P PLAW PCALL D); [exact HPRE | exact HE | exact HP]|].
  exact Kend. }
(* CB7, proved (Cno102B_R7.v): the compare, then up to two same calls *)
assert (Ksame2 : forall W c, cnb_ex_same2 (fx := fx) (SK := SK) B ARcfx D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D)).
{ intros W c HE HP. cnbt_open HE. apply cnbt_pm in HP.
  eapply cnbt_seq'; [eapply (cnb_same2_step (fx := fx) (SK := SK) B ARcfx CTX0); eassumption|].
  exact Kfree. }
assert (Ksame1 : forall W c, cnb_ex_same1 (fx := fx) (SK := SK) B ARcfx D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D)).
{ intros W c HE HP. cnbt_open HE. apply cnbt_pm in HP.
  eapply cnbt_seq'; [eapply (cnb_same1_step (fx := fx) (SK := SK) B ARcfx CTX0); eassumption|].
  intros W' c' [HX | HX] HP'; [exact (Ksame2 W' c' HX HP') | exact (Kfree W' c' HX HP')]. }
assert (Kcmp : forall W c, cnb_ex_cmpR (fx := fx) (SK := SK) B ARcfx WLE' D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D)).
{ intros W c HE HP. cnbt_open HE. apply cnbt_pm in HP.
  eapply cnbt_seq'; [eapply (cnb_cmp_seg (fx := fx) (SK := SK) B ARcfx CTX0); eassumption|].
  intros W' c' [HX | HX] HP'; [exact (Kfree W' c' HX HP') | exact (Ksame1 W' c' HX HP')]. }
(* PN3, proved (Cno102B_Rpn.v) *)
assert (Kpn3 : forall W c, cnb_ex_pn3R (fx := fx) (SK := SK) B ARcfx WLE' D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D)).
{ intros W c HE HP. cnbt_open HE. apply cnbt_pm in HP.
  eapply cnbt_seq'; [eapply (cnb_pn3_step (fx := fx) (SK := SK) B ARcfx); eassumption|].
  exact Kcmp. }
(* CB6, proved (Cno102B_R4.v) *)
assert (Kread3 : forall W c, cnb_ex_read3R (fx := fx) (SK := SK) B ARcfx WLE' D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D)).
{ intros W c HE HP. cnbt_open HE. apply cnbt_pm in HP.
  eapply cnbt_seq'; [eapply (cnb_read3_seg (fx := fx) (SK := SK) B ARcfx CTX0); eassumption|].
  intros W' c' [HX | HX] HP'; [exact (Kcmp W' c' HX HP') | exact (Kpn3 W' c' HX HP')]. }
(* PN2, proved (Cno102B_Rpn.v) *)
assert (Kpn2 : forall W c, cnb_ex_pn2R (fx := fx) (SK := SK) B ARcfx WLE' D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D)).
{ intros W c HE HP. cnbt_open HE. apply cnbt_pm in HP.
  eapply cnbt_seq'; [eapply (cnb_pn2_step (fx := fx) (SK := SK) B ARcfx); eassumption|].
  exact Kread3. }
(* CB5, proved (Cno102B_R4.v) *)
assert (Kread2 : forall W c, cnb_ex_read2R (fx := fx) (SK := SK) B ARcfx WLE' D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D)).
{ intros W c HE HP. cnbt_open HE. apply cnbt_pm in HP.
  eapply cnbt_seq'; [eapply (cnb_read2_seg (fx := fx) (SK := SK) B ARcfx CTX0); eassumption|].
  intros W' c' [HX | HX] HP'; [exact (Kread3 W' c' HX HP') | exact (Kpn2 W' c' HX HP')]. }
(* PN1, proved (Cno102B_Rpn.v): the first parse_noting, the first step at SRr' *)
assert (Kpn1 : forall W c, cnb_ex_pn1 (fx := fx) (SK := SK) B ARcfx D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D)).
{ intros W c HE HP. cnbt_open HE. apply cnbt_pm in HP.
  eapply cnbt_seq'; [eapply (cnb_pn1_step (fx := fx) (SK := SK) B ARcfx); eassumption|].
  exact Kread2. }
(* CB4, proved (Cno102B_R4.v): plain SRr, lifted *)
assert (Kread1 : forall W c, cnb_ex_read1 (fx := fx) (SK := SK) B ARcfx D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D)).
{ intros W c HE HP. cnbt_open HE. apply cnbt_pm in HP.
  eapply cnbt_seq_up; [eapply (cnb_read1_seg (fx := fx) (SK := SK) B ARcfx CTX0); eassumption|].
  intros W' c' [HX | HX] HP'; [exact (Kfree W' c' HX HP') | exact (Kpn1 W' c' HX HP')]. }
(* CB3, proved (Cno102B_E3.v): plain SRr, lifted *)
assert (Kinit : forall W c, cnb_ex_init (fx := fx) (SK := SK) B ARcfx D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D)).
{ intros W c HE HP. cnbt_open HE. apply cnbt_pm in HP.
  eapply cnbt_seq_up; [eapply (cnb_seg_init (fx := fx) (SK := SK) B ARcfx); eassumption|].
  exact Kread1. }
(* CB2, proved (Cno102B_E2.v); its IMG_SHADOW is CB0's ISV (the same text); plain SRr, lifted *)
assert (Kcopy : forall W c, cnb_ex_copy (fx := fx) (SK := SK) B ARcfx D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D)).
{ intros W c HE HP. cnbt_open HE. apply cnbt_pm in HP.
  eapply cnbt_seq_up; [eapply (cnb_seg_copies (fx := fx) (SK := SK)); first [eassumption | exact ISV]|].
  exact Kinit. }
(* CB1, proved (Cno102B_E1.v); plain SRr, lifted *)
intros fxk ly S Hp W regs mem md k HAT HP.
eapply cnbt_seq_up; [eapply (cnb_seg_poison (fx := fx) B SK CTX0 HTOP P PLAW D); eassumption|].
exact Kcopy.
Qed.

(* ---- the record CB0 hands on: the entry data with the frame's position; nothing below reads bi_fpos ---- *)
Lemma cnbt_pre_fpos : forall D p, cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnb_pre (fx := fx) B ARcfx CTX0 (cnb_set_fpos D p).
Proof. intros D p H. exact H. Qed.
Lemma cnbt_ret_fpos : forall D p W c, cnb_ex_ret (fx := fx) (SK := SK) B ARcfx (cnb_set_fpos D p) W c ->
  cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D W c.
Proof. intros D p W c H. exact H. Qed.

(* ---- THE WALK: cnb_pre at the entry configuration to the contract's exit cnb_ex_ret (the text's post, every
   conjunct), P := cnb_mn D ONCE; CB0 runs before the first free (plain SRr, lifted once) ---- *)
Lemma cnb_B_walk : forall D, cnb_pre (fx := fx) B ARcfx CTX0 D ->
  SRr' SEGS YGcfRehidePost.RZ_cf (bi_W D) (cfg_at SEGS (SIGMA AS_check_no_overread) (bi_regs D) (bi_mem D) (bi_md D))
    (cnb_ex_ret (fx := fx) (SK := SK) B ARcfx D).
Proof.
intros D HPRE.
(* the memnorm invariant, ONCE *)
pose proof (cnb_mn_laws D) as PLAW.
pose proof (cnb_mn_call D) as PCALL.
pose proof (cnb_mn_mn B ARcfx CTX0 D HPRE) as PMN.
(* CB0, proved (Cno102B_E0.v) *)
eapply cnbt_seq_up; [exact (cnb_seg_e0 (fx := fx) B SK CTX0 PAL IMG SM3 ASM3 ISV (cnb_mn D) PLAW PCALL D HPRE
  (cnb_mn_entry D))|].
intros W1 c1 HE HP1. cnbt_open HE. apply cnbt_pm in HP1.
eapply SRr'_mono.
- eapply (cnbt_body (cnb_mn D) PLAW PCALL PMN (cnb_set_fpos D x) (cnbt_pre_fpos D x HPRE)); eassumption.
- intros W' c' _ H. exact (cnbt_ret_fpos D x W' c' H).
Qed.

(* CB_Top: the kit's RESTATED text tcheck_no_overread_specX (the move: SRr' segs RZ_cf, the post fpostFbm at wle'; the
   hull premise LAST) at this file's parameters, ITSELF: its premises and its post verbatim *)
Theorem cnb_B_top : tcheck_no_overread_specX (fx := fx) B ARcfx SK CTX0.
Proof.
unfold tcheck_no_overread_specX.
intros ly S Hp W regs mem md ch data x Lam peak cnt ran most.
cbv zeta.
intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23.
pose (D := mkCnbIn ly S Hp W regs mem md ch data x Lam peak cnt ran most 0).
assert (HPRE : cnb_pre (fx := fx) B ARcfx CTX0 D).
{ exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11
    (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 (conj H20 (conj H21
    (conj H22 H23)))))))))))))))))))))). }
exact (cnb_B_walk D HPRE).
Qed.

End f.
End d.

Check cnb_B_top.

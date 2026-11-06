(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of chain_words (0x8dfd4) on the ASan build of plugin-hostd/fuzz_command
   proves its statement tchain_words_spec (chain_words_c.v:94-134) directly: from the six segments and the transport
   (chain_words_a.v's cw_run), at statement passes 4 and 5 (the FP-existential post apost_baseF, the rounding-mode
   premise, no astack_pres). The returned block's size is exact in the statement
   (chain_words_c.v:127), as the walk's post cw_Q (chain_words_d.v) carries it from the two recorder callees. The
   callee contracts and runtime rules are the statement's, in its forall-fx0 form (chain_words_c.v:84-93); the
   per-binary facts the walk names are CmdRecFacts lemmas: relro_img and cmd_ro_ok_of_aro (CmdRecRo.v),
   cmd_prog_unowned (CmdRecImg.v), all over IMG : cmd_img_facts. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_exact.v, with its module paths and module names changed; 20 of its 39 lines of code are new or changed and 65 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/trim.v, with its module paths and module names changed; 76 of its 98 lines of code are new or changed and 17 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the walk of reac_segconf_parse_file (0x87a78, 4908 bytes,
   1227 instructions; reac_segconf.c:120-296) against its contract lib/A/Prog/reac_segconf_parse_file_c.v, from its
   15 segment theorems pf_a<k>_holds : S_A<k> B (lib/A/Prog/pf_a1.v .. pf_a12.v; the statements are
   lib/A/Prog/pf_pieces.v's) through pf_pieces_give_contract_holds (lib/A/Prog/pf_compose.v). Written by the
   G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (reuse search: origin/main, origin/ossv/recipes, origin/ossv/candidates,
   origin/release/pau-projects-recipes, the unreleased proof delivery, cold/* heads, image-A address 0x87a78 /
   the released-proof index's query for reac_segconf_parse_file): the unit's internal record, commit dfb49d6ad789,
   path records/segp/g3-lookup.md, CONFIRM by the rule-24 check
   2026-10-30T15:42:08Z; reuse verdict none: written new.
   THE SECTION HYPOTHESES are exactly the union of the Section hypotheses the 15 segment theorems keep in their
   types (`About pf_a<k>_holds`), each listed once, in the segments' own words: the runtime entries and wrappers
   at `pa_sigma SS_<name>` (SegSyms.v), each at every FP state; the program callees refuse, trim,
   reac_box_catalogue_by_token and reac_box_catalogue at `BASE + AF_<F>` and image A's numbers (SegInstA.v:
   STK_refuse, STK_trim, STK_reac_box_catalogue_by_token, STK_reac_box_catalogue, RLO_A, RHI_A, seg_litA_rc, catA,
   gotwA, guardA); the walk records PALib, PALibF and model_laws; the listing facts of SegObj.v (call targets,
   object atoms, the read-only range); and SSPX, the stack-protector cells at every AR state (the image-A owner's route
   A; temporary until listing stage 2). The comment after each names the segments whose theorem takes it.
   Image A's values: BASE + AF_reac_segconf_parse_file = 0x87a78 (SegList / SegInstA's
   A_reac_segconf_parse_file_A_AF), STK_reac_segconf_parse_file = 12800, RLO_A = 0xa14a0, RHI_A = 0xa3748,
   catA = 0xa18e0, gotwA = 0xa36d8, guardA = 0x5ff078 (SegInstA.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg RtString RtFormat RtStack RtShadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegObj
  SegPaLib PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c trim_c
  reac_box_catalogue_by_token_c reac_box_catalogue_c reac_segconf_parse_file_c SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_pieces pf_compose.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require pf_a1 pf_a2 pf_a3 pf_a4 pf_a5 pf_a6 pf_a7
  pf_a8a pf_a8b pf_a9 pf_a10a pf_a10b pf_a11a pf_a11b pf_a12.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* the wrappers (the interceptor owner's RtSeg rows at 80d098bd1905, the RtString / RtFormat rows of its interface) *)
Hypothesis ASTRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strchr).              (* A5, A7, A9 *)
Hypothesis ANCASE : forall fx0 : YK11.FPState,
  @RtSeg.astrncasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strncasecmp).    (* A7 *)
Hypothesis ASTRCASECMP : forall fx0 : YK11.FPState,
  @RtSeg.astrcasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcasecmp).      (* A9, A12 *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).           (* A5, A7, A9 *)
Hypothesis STRSPN : forall fx0 : YK11.FPState,
  @RtString.astrspn_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strspn) gotwA guardA. (* A6 *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).           (* A8a *)
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
  (* A3, A8b, A10b, A11a, A11b *)
(* the kit's bcmp, checked memcpy / memset, and the shadow-fill entries *)
Hypothesis ABCMP : forall fx0 : YK11.FPState,
  @abcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_bcmp).                         (* A10b *)
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy). (* A5 *)
Hypothesis AMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
  (* A3, A8b *)
Hypothesis ASHF8 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIG SS___asan_set_shadow_f8) 0xf8.              (* A2, A5 *)
Hypothesis ASH00 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIG SS___asan_set_shadow_00) 0.                 (* A5 *)
(* the class-5 side-stack frame: take (A1) and release (A4) *)
Hypothesis ASM5 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 5.            (* A1 *)
Hypothesis SMP : stack_malloc_progressP B.                                                       (* A1 *)
Hypothesis ASF5 : forall fx0 : YK11.FPState,
  @RtStack.astack_free_cls_realizes fx0 rc SEGS B (SIG SS___asan_stack_free_5) 5.               (* A4 *)
(* the program callees, at image A's numbers *)
Hypothesis REF : forall fx0 : YK11.FPState, refuse_contract (fx := fx0) SEGS B
  (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.     (* A6, A7, A8a, A8b, A9, A10b, A11b, A12 *)
Hypothesis TRIM : forall fx0 : YK11.FPState, trim_contract (fx := fx0) SEGS B
  (BASE + AF_trim) STK_trim RLO_A RHI_A.                                                         (* A5, A7, A9 *)
Hypothesis BT : forall fx0 : YK11.FPState, reac_box_catalogue_by_token_contract (fx := fx0) SEGS B
  (BASE + AF_reac_box_catalogue_by_token) STK_reac_box_catalogue_by_token RLO_A RHI_A catA.      (* A11a *)
Hypothesis CAT : forall fx0 : YK11.FPState, reac_box_catalogue_contract (fx := fx0) SEGS B
  (BASE + AF_reac_box_catalogue) STK_reac_box_catalogue catA.                                    (* A11b *)
(* the walk records (SegPaLib.v, PaLibF.v, YG0d.v's model_laws) and the listing's facts over the walk's abstract
   instance (SegObj.v) *)
Hypothesis TL : PALib B.                                                       (* A1, A5, A6, A7, A8a, A9, A12 *)
Hypothesis TLF : PALibF B.                                                                       (* A1 *)
Hypothesis ML : model_laws (as_universe B).                                                      (* A1, A4 *)
Hypothesis SIGP : seg_sig_prog (PI := PI).          (* A5, A6, A7, A8a, A8b, A9, A10b, A11a, A11b, A12 *)
Hypothesis OBJ : seg_val_objs (PI := PI).                (* A3, A7, A8a, A8b, A9, A10b, A11a, A11b, A12 *)
Hypothesis VRO : seg_val_relro (PI := PI).                (* A1, A6, A7, A8a, A8b, A9, A10b, A11b, A12 *)
(* the stack-protector cells at every AR state (the image-A owner's route A: pf_cx gives sa_ssp at the entry only; after a
   call a segment takes it from here; the shape of reac_segconf_parse.v's SSPX). TEMPORARY: discharged from
   SegRecCells.seg_rec_cells once listing stage 2 (AF0m) compiles *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
  (* A1, A6, A7, A8a, A8b, A9, A10b, A11b, A12 *)

Theorem reac_segconf_parse_file_walk :
  reac_segconf_parse_file_contract SEGS B (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file
    RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Proof.
refine (pf_pieces_give_contract_holds B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
- eapply pf_a1.pf_a1_holds; eassumption.
- eapply pf_a2.pf_a2_holds; eassumption.
- eapply pf_a3.pf_a3_holds; eassumption.
- eapply pf_a4.pf_a4_holds; eassumption.
- eapply pf_a5.pf_a5_holds; eassumption.
- eapply pf_a6.pf_a6_holds; eassumption.
- eapply pf_a7.pf_a7_holds; eassumption.
- eapply pf_a8a.pf_a8a_holds; eassumption.
- eapply pf_a8b.pf_a8b_holds; eassumption.
- eapply pf_a9.pf_a9_holds; eassumption.
- eapply pf_a10a.pf_a10a_holds; eassumption.
- eapply pf_a10b.pf_a10b_holds; eassumption.
- eapply pf_a11a.pf_a11a_holds; eassumption.
- eapply pf_a11b.pf_a11b_holds; eassumption.
- eapply pf_a12.pf_a12_holds; eassumption.
Qed.
End e.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module names changed; 3841 of its 4451 lines of code are new or changed and 2502 lines of the source are left out. *)
(* lib/B/ACtlW4f.v -- piece W4f (S_F30 .. S_F36_c2c, the row stages included, cut-table-B.tsv rows 74-83: B82abc_at j ..
   B82c90_at j) of fuzz_ctrl image B's (asan-ubsan) walk of LLVMFuzzerTestOneInput in the released
   cgif_file_fuzzer form.  One writer: a Theorem Labs lane.  rule 24: no function proved (segment lemmas of a
   walk).

   WHAT THIS FILE PROVES (when it builds): one stage lemma per stage hypothesis of lib/B/ACtl.v in the piece
   (seg_F30 .. seg_F36_c2c, ACtl.v:597-629 at 576147dfd46), with the SAME NAME and, once the top instantiates
   SK := Reusable.YE2k.tfib_sink_head and FP := [] (ACtl.v:171-177), the same statement, so the top cites
   ACtlW4f.seg_F30 .. directly.  Shape: "the successor cuts hold -> this cut holds" (the donor's rt_B / rt_C shape),
   POINTWISE in the frame turn j (and in the row i for the three row cuts) with ACtlCut.ix_cut.  The row loop
   itself is the top's (ACtl.v turn_rows / loop_rows :655-672, base vac_B82bf4 :342), over seg_F34 / seg_F35 /
   seg_F36 from this file.
     B82abc_at j   (0x82abc) --S_F30-->     B82af8_at j (reac_ctrl_classify_box_frame @0x82af4, callee-cut)
     B82af8_at j   (0x82af8) --S_F31-->     B82b38_at j (bcmp @0x82b34; t_cls j <> None) | B82b5c_at j (None)
     B82b38_at j   (0x82b38) --S_F32 e1-->  B82b5c_at j (0x82b38-0x82b58 then the cut 0x82b5c itself)
     B82b5c_at j   (0x82b5c) --S_F32 e2-->  B82bcc_at j (reac_box_catalogue @0x82bc8) | B82c90_at j (mismatch arms)
     B82bcc_at j   (0x82bcc) --S_F33-->     B82bf4_at j 0 (the row-loop head at i = 0)
     B82bf4_at j i (0x82bf4) --S_F34-->     B82c24_at j i (declaration_of @0x82c20)
     B82c24_at j i (0x82c24) --S_F35-->     B82c38_at j i (bcmp @0x82c34)
     B82c38_at j i (0x82c38) --S_F36-->     B82bf4_at j (S i) (row latch) | B82ca0_at j (match @0x82c9c)
     B82c84_at j   (0x82c84) --S_F36_c20--> B82ca0_at j (match @0x82c9c)
     B82c90_at j   (0x82c90) --S_F36_c2c--> B82ca0_at j (match @0x82c9c)
   Two routing choices that differ from ctrl's assembly forms, both on official cuts and both checked against the
   segment headers:
   - S_F32's first entry is walked only to the official cut B82b5c_at (0x82b5c lies on its path, UB Seg/F32.v
     :14-15; C_B82b5c_at's body is a sub-bundle of C_B82b38_at's: Perm, FRAC, HB, LK, FTK, PT32, FTURN, IFS), so
     the mismatch / catalogue stretches are walked once, from B82b5c_at: seg_F32_b38 and seg_F32_b5c, composed
     into ACtl.v's conjunctive seg_F32.
   - S_F33's exit B82c84_at and S_F35's exits B82bf4_at (S i) / B82ca0_at are dead under the cut bodies: at 0x82bcc
     a0 = CAT <> 0 and [fr + 32] = 11 <> 0 (C_B82bcc_at body; ctrl drops it too, Seg/F33.v:6-10, :140); at 0x82c24
     a0 = 1 (C_B82c24_at body `rgv regs 10 1`; Seg/F35.v:23-26).  seg_F33 / seg_F35 still take them as premises,
     because ACtl.v's hypotheses do (ctrl's seg_F33 / seg_F35 statement shapes); the proofs do not use them.
     B82c84_at keeps its own stage (seg_F36_c20), proved like any other.
   No allocator site.  The two callee-cut calls (classify @0x82af4, match @0x82c9c) take their own fake frames
   inside the callee and release them before returning (plan M8), so on return the frame list is own6 again and
   k is unchanged (a fake-stack request is not a model event: aj_stack_malloc_at's post keeps st_nev).

   ROUTE, BUILD STATE, SHELL BINDING, THE FRAME TIE (ctl_from's G1 premise, named HG1 in the plans): exactly as
   lib/B/ACtlW4e1.v's header (same lane, same date).
   Every stage lemma is closed with Qed; a fact that has no proof in this tree yet is a NAMED Section hypothesis with
   its OBLIGATION and OWNER (a Theorem Labs lane with a Theorem Labs lane, ~23:55Z).  No Axiom, no Parameter, no unclosed proof.

   SECTION HYPOTHESES (sources as ACtlW4e1.v's header for Hwx, LAWS, segs_low, B_bcmp_tramp_entry / H_bcmp; ctl_rt_C
   by w4f_ctlrt = B.ProgWorldCtlRtC.ctl_rt_C_of_AR with TFIB_SYMS / LAWS (route (C); no VIS0, no OWNED_RO), its
   arodata_okP by APostBase.arodata_ok_journalP with RELRO_IMG / RO_OFL; each hypothesis states its OBLIGATION and
   OWNER where declared):
   - reac_box_catalogue is NOT a hypothesis: its footprint contract is PROVED here with no premise, in its route (C)
     form B.Prog.reac_box_catalogueF.reac_box_catalogue_F_holds_on : reac_box_catalogue_contract_F_on
     (reac_box_catalogue_c.v, premise shadow_rw DROPPED; files by path from a working branch
     7cfe4683a44; plan F.2 row 38); seg_F32_b5c uses it directly.
   - declaration_of_F_holds_on: declaration_of's route (C) footprint contract `declaration_of_contract_F_on`
     (B/Prog/declaration_of_c.v, statements by path from a working branch 78f53925b08; the plan F.2 row 39 (a working note, not in this delivery)), a
     NAMED hypothesis until a Theorem Labs lane's image-B proof lands (this file does not Require declaration_ofF.v).
   - TCLS: reac_ctrl_classify_box_frame (0x837c4; it reaches __asan_stack_malloc_1 through reac_ctrl_parse, so it
     does not lift whole) by its cgif-form spec in the CALLER-JOURNAL form, by name:
     `treac_ctrl_classify_box_frame_spec B RLO RHI` of lib/B/Prog/C_reac_ctrl_classify_box_frame.v (sink head
     fixed there; SK_TFIB ties this Section's SK to it)
     (statement of record a Theorem Labs lane 24eccbe90cb, aligned to image A at 05:52Z, on the walk line since 4f5b5522959),
     proved there as `pb_reac_ctrl_classify_box_frame` (owner a Theorem Labs lane).
   - TMATCH: reac_box_catalogue_match (0x84e40; its own __asan_stack_malloc_2, the _1 in reac_ctrl_parse, the _0
     in reac_box_model_block) by `treac_box_catalogue_match_spec (SK := SK) RLO RHI B` of
     lib/B/Prog/C_reac_box_catalogue_match.v (brought by path from a working branch
     5608c59483e; gate finding w4f-tcls-tmatch.md (a working note, not in this delivery)), to be proved as `pb_reac_box_catalogue_match` (owner
     a Theorem Labs lane).  Its FORM is afn_pre / apost_base (NOT the caller-journal form TCLS has), with no achain premise.
     OBLIGATION at the composition: pb_reac_box_catalogue_match takes RELRO_IMG `forall a, RLO <= a < RHI ->
     in_img segs a` (the B PA instance's pa_relro) and `RLO <= A_CM_TBL /\ A_CM_TBL + CM_ROWS <= RHI` (lia at
     RLO = 0x9f168, RHI = 0xa15e8).  It is NOT a whole lift for this walk (the callee's fake-stack requests are
     allocator events), so it enters only through the spec, never through its footprint contract.
   SETTLED INTERFACE (a Theorem Labs lane with two Theorem Labs lanes ~23:40Z): every image-B callee spec is stated over the walk's
   Reusable.YB1v.tfibsegs (never pa_segs PI), so TCLS's C1 takes this file's journal as is; and its read-only-data
   premise is the core's arodata_okS .. RLO RHI, the same fact ctl_base gives (the PA layer's arodata_okP is reached,
   where needed, by a Theorem Labs lane's ProgWorld lemma arodata_okP_of_S).  The draft's section 3.2 text (a working note, not in this delivery) is to be read
   with those two substitutions.
   `_F` RUNS (a Theorem Labs lane's bF-statements/<File>F.md; names per bF-brief.md:36-43 (a working note, not in this delivery) and bseg-runs.tsv rows 125-154 (a working note, not in this delivery)).
   By the GLUE CLOSURE RULE (porter 23:38Z) this file Requires a Theorem Labs lane's `_F` modules QUALIFIED and uses their
   lemmas directly: no `_F` text is copied here, and no statement of this file names a frame-route identifier.
   AC.GT (porter 23:40Z): of the cited `_F` lemmas exactly ONE mentions AC.GT, B.Prog.Seg.F32F.f32c_evt_pre_F
   (F32F.v:262, the premise `AC.GT <= fr`); seg_F32_b5c rewrites it with the one lemma w4f_gt_img_top
   (`AC.GT = Reusable.YImgTop.IMG_TOP`, before Section W4f), so its statements say IMG_TOP only.  The other GT
   uses in a Theorem Labs lane's W4f texts are F30F.v:175 f30s_evt_ro_F and F32F.v:274 f32c_evt_pre_F_on (cited; their GT is rewritten the same way), F34F.v:409 f34_evt_ro_pre_F_on (cited; its GT is computed to 6283264, not rewritten) and, uncited, F32F.v:478
   f32c_evt_post_F, F34F.v:495 f34_evt_ro_pre_F.
   CITED (all PROVED on a working branch 12a7ea50807, the one branch with every image-B `_F`, first
   landed on a working branch 74c801af405; Required qualified):
   - B.Prog.Seg.F30F.f30s_evt_F      (F30F.md:18-35; Seg/F30.v:356; 0x82abc -> the classify entry 0x837c4 with
                                     ra = 0x82af8; it IS the pre stretch of the segment's one call and needs no
                                     split, F30F.md:6-8)
   - B.Prog.Seg.F31F.f31n_evt_F      (F31F.md:11-26; Seg/F31.v:170; the None arm, 0x82af8 -> 0x82b5c)
   - B.Prog.Seg.F31F.f31c_evt_pre_F  (F31F.md:31-63; Seg/F31.v:206; the Some arm, 0x82af8 -> 0x42aac with
                                     ra = 0x82b38)
   - B.Prog.Seg.F32F.f32e_evt_F      (F32F.md:14-25; Seg/F32.v:326; 0x82b38 -> 0x82b5c)
   - B.Prog.Seg.F32F.f32n_evt_F / f32m1_evt_F / f32m2_evt_F   (F32F.md:26-30 / :31-42 / :43-47; Seg/F32.v:364 /
                                     :382 / :419; the mismatch arms, 0x82b5c -> 0x82c90)
   - B.Prog.Seg.F32F.f32c_evt_pre_F_on (route (C) twin, a working branch, F32F.md (a working note, not in this delivery); premise
                                     shadow_rw dropped; 0x82b5c -> the reac_box_catalogue entry 0x84dec, ra = 0x82bcc)
   - B.Prog.Seg.F33F.f33_evt_F       (F33F.md:21-42; Seg/F33.v:69; 0x82bcc -> 0x82bf4; its premise a0 = 0x9f620
                                     is v1.9's CAT)
   - B.Prog.Seg.F34F.f34_evt_ro_pre_F_on (route (C) twin, a working branch, F34F.md (a working note, not in this delivery); premise
                                     shadow_rw dropped; 0x82bf4 -> the declaration_of entry 0x83114, ra = 0x82c24)
   - B.Prog.Seg.F35F.f35_evt_pre_F   (F35F.md:11-22; Seg/F35.v:187; 0x82c24 -> 0x42aac with ra = 0x82c38)
   - B.Prog.Seg.Tac_f36F.f36_evt_pre_F (Tac_f36F.md:97-120 (a working note, not in this delivery); Tac_f36.v:1974; 0x82c38 -> 0x82c54),
     f36_evt_hit_F (Tac_f36F.md:52-67 (a working note, not in this delivery); :2015; 0x82c54 -> 0x82c88), f36_evt_next_F (:125-150; :2038;
     0x82c54 -> 0x82bf4), f36_evt_last_F (:158-177; :2065; 0x82c54 -> 0x82c88), f36_evt_c24_F (:72-92; :2089;
     0x82c88 -> 0x82c94), f36_evt_c20_F (:14-28; :2121; 0x82c84 -> 0x82c88), f36_evt_c2c_F (:33-47; :2110;
     0x82c90 -> 0x82c94), f36_evt_call_pre_F (:188-194; :1653 split; 0x82c94 -> 0x84e40 with ra = 0x82ca0, no
     memory access, no rng)
   NOT USED: f31c_evt_post_F, f32c_evt_post_F, f34_evt_post_F, f35_evt_post_F, f36_evt_call_post_F, and every
   `_ro` twin whose plain run states no mem_inv.  ctl_rt carries ro_agree_at, NOT mem_inv (ACtlCut.v section 4,
   a Theorem Labs lane 00:35Z): a run whose plain form needs mem_inv is taken in its `_ro` form (f34_evt_ro_pre_F), and a callee
   contract stated with mem_inv is applied at `normalize rsegs m` and carried back by MemNormF.evtF_normalize_ro.
   Each `_post_F` is a zero-step stretch at the cut 0x82b38 / 0x82bcc / 0x82c24 / 0x82c38 / 0x82ca0; the
   continuation reads the cut body over VISIBLE addresses from the callee's post.  After a WORLD-FORM callee (the
   bcmp trampoline via aj_bcmp_at / H_bcmp; the callee-cut functions TCLS / TMATCH) a raw-munch `_post_F` cannot
   be applied at all (rule ~00:45Z (2)); after a FOOTPRINT callee (reac_box_catalogue_F_holds_on, declaration_of_F_holds_on) the same
   zero-step `_post_F` is not needed.
   CLOSURE (rule (3)-(4)): the frame-route files reached through the `_F` modules must be, up to comment text, the v1.9 blobs of record:
   lib/B/Prog/SlotModel.v de18d111c37, SlotInv.v dfc10b8f7a4 (23a791566db = UB 3803efccea0), AsanRT.v
   32e0f5191fd, Contract.v 65b05173b1a, and the Seg sources at a working branch 3803efccea0, the blobs a Theorem Labs lane re-runs (each
   `_F` module's `Source:` line): Seg/F30.v d2349dd89bf, Seg/F31.v 14939e90cc5, Seg/F32.v 8aab0c37ec8,
   Seg/F33.v 333b7b7d641, Seg/F34.v 3ea1805a512, Seg/F35.v cc6ce088e25, Seg/Tac_f36.v 6c08f44bcc3
   (Seg/F30.v-F36.v (Seg/F36.v not in this delivery) and Tac_f36.v are not in 23a791566db or the union).  No lib/AZ/AsanW, W6 or
   cut-free file.  lib/AZ in the closure: exactly AcctCore.v, AsanCtrl.v, AsanCtrlProps.v and STree.v, with the
   blobs and paths in lib/B/ACtlW4e1.v's header (allowed in the closure only, porter 00:24Z / 00:25Z); no
   statement or hypothesis here names any of them.
   ITEM 23 (a Theorem Labs lane 13:12Z rule: a PROVED ProgWorld statement is CITED, never carried):
   - B.ProgWorld.aview_vis_mrd (item 23's one primitive, lib/B/ProgWorld.v:587, PROVED; abbreviated aview_vis_mrd
     below): at a VISIBLE address the core's view read IS lib/Lib's mrd read.  Every continuation of this file takes
     that step -- after the bcmp trampoline (aj_bcmp_at's aview post) and after the two callee-cut functions, whose
     kept facts are view-level (TCLS's Q7 acall_kept, TMATCH's apost_base journal clauses).  munch_vis over ALL
     addresses is NOT derivable from such a post (the callee's own frame is visible and changes), so no statement or
     plan here claims a raw `mem x` equality.  (The earlier Section hypothesis ctl_post_bcmp, B.ProgWorld.ctl_post_bcmp
     there, was used by no proof here and is gone.)

   MODEL: drafted against image B's v1.9 SlotModel (blob de18d111c37 by path from 23a791566db: SM.CAT = 0x9f620;
   porter ruling via a Theorem Labs lane ~23:30Z), which this branch carries (up to comment text) since the shell re-twin (blob de18d111c37 at
   576147dfd46).

   PROVENANCE: cut table rows 74-83 (lines 75-84); cut records lib/B/ACtlCutP.v (6d691a975b6); plan 2.3 rows
   74-82, 3 (loop 13), F.2 rows 37-40, F.3 rows 24-25, 6.2, F.4.1 rows 65-70; ctrl's runs at
   a working branch 3803efccea0 (Seg/F30.v-F36.v (Seg/F36.v not in this delivery), Tac_f36.v, Slot.v (not in this delivery)); objdump
   fuzz_ctrl.objdump.txt L85500-L85621 (a working note, not in this delivery). *)

From Stdlib Require Import ZArith List Permutation Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* The six modules with a unit copy (YI04 YI16 YK11 YK1b YM05 YO09), and YI00 / YK0s, which have one too: Required by
   the core's own logical prefix (a Theorem Labs lane 04:24Z / 04:33Z), named lib.Reusable.X below. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09 YI16 YI04 YI00 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YK04R Reusable.YA0n Reusable.YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0f Reusable.YG01 Reusable.YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq Reusable.YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCfn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.AsanRT B.ACtlK B.ACtlCut B.ACtlCutP.
(* The kit bridge (fevt_of_evtF, RNG_W, rng_of_visible, img_vis_W, tfibsegs_rsegs, cfg_at_MS; a Theorem Labs lane's image-B
   ProgBridge, FROZEN 03:17Z, on this branch since 6fe149485c2) and lib/Lib's footprint-run and register vocabulary.
   lib/B/ACtlW4e1.v is NOT Required: it is another lane's file and does not build at 87506cf93a9 (its line 311). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgBridge.
(* route (C) (a Theorem Labs lane 11:03Z): the cut carries ctl_rt_C (B.ACtlRtC); at a cut state it is a Theorem Labs lane's
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR (no AR_states_vis0_shadow, no AR_states_owned_ro); B.ShadowRwOn's region form. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YF0m B.ACtlRtC B.ShadowRwOn B.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_box_catalogueF B.Prog.declaration_of_c.
(* The two callee-cut specs (TCLS / TMATCH, on the walk line) and the vocabulary used with the callee specs. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.C_reac_ctrl_classify_box_frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.C_reac_box_catalogue_match.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.APostBase Reusable.YE01 Reusable.YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcMatch Prog.RcParse Prog.RcClassify.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState PropExec.
(* lib/Lib's raw-memory vocabulary of the call-post fact below (Required only, never Imported). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Frame Mem.
(* a Theorem Labs lane's `_F` modules, Required qualified (glue closure rule, porter 23:38Z); the files land with a Theorem Labs lane's batch *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.Seg.F30F B.Prog.Seg.F31F B.Prog.Seg.F32F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.Seg.F33F B.Prog.Seg.F34F B.Prog.Seg.F35F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.Seg.Tac_f36F.
(* AC.GT = IMG_TOP (w4f_gt_img_top) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Contract Reusable.YImgTop.
(* Full-path aliases for the pure models the two callee specs name (lib/Prog; never a lib/B/Prog file). *)
Module RMT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcMatch.
Module RPS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module RCF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcClassify.
Import ListNotations.
Local Open Scope Z_scope.

(* F32F's f32c_evt_pre_F states `AC.GT <= fr` (F32F.v:262).  Porter 23:40Z: ONE lemma AC.GT = IMG_TOP, rewritten
   inside the stage proof, so no statement or hypothesis of this file says AC.GT.  Both sides are the literal
   0x5fe000 (lib/B/Contract.v:73 `Definition GT : Z := 0x5fe000`; YImgTop IMG_TOP).  Proof-internal, Qed. *)
Lemma w4f_gt_img_top : B.Contract.GT = Reusable.YImgTop.IMG_TOP.
Proof. reflexivity. Qed.

Section W4f.

Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

Local Notation segs := Reusable.YB1v.tfibsegs.

(* ---- SHELL BINDING (the only lines naming ACtlCut's / ACtlCutP's argument lists) ---- *)
Local Notation ctl_from := (ACtlCut.ctl_from B MT XM_LIB RLO RHI FP).
Local Notation ix := ACtlCut.ix_cut.
Local Notation C_B82abc_at := (ACtlCutP.C_B82abc_at B).
Local Notation C_B82af8_at := (ACtlCutP.C_B82af8_at B).
Local Notation C_B82b38_at := (ACtlCutP.C_B82b38_at B).
Local Notation C_B82b5c_at := (ACtlCutP.C_B82b5c_at B).
Local Notation C_B82bcc_at := (ACtlCutP.C_B82bcc_at B).
Local Notation C_B82bf4_at := (ACtlCutP.C_B82bf4_at B).
Local Notation C_B82c24_at := (ACtlCutP.C_B82c24_at B).
Local Notation C_B82c38_at := (ACtlCutP.C_B82c38_at B).
Local Notation C_B82c84_at := (ACtlCutP.C_B82c84_at B).
Local Notation C_B82c90_at := (ACtlCutP.C_B82c90_at B).
Local Notation C_B82ca0_at := (ACtlCutP.C_B82ca0_at B).

(* ---- Section hypotheses ---- *)
(* segs = B.Img0.rsegs is B.ProgBridge.tfibsegs_rsegs (Qed), cited where needed: no hypothesis. *)
Hypothesis Hwx : Reusable.YK04.wx_segs_nowrap segs.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.


(* ctl_rt_C at a cut state: w4f_ctlrt below (B.ProgWorldCtlRtC.ctl_rt_C_of_AR). *)

(* The bcmp trampoline (a Theorem Labs lane's shared contract, abcmp_realizes shape); entry by the core's name
   (YTramp.bcmp_tramp, image B 0x42aac; a Section variable until it lands). *)
Variable B_bcmp_tramp_entry : Z.
Hypothesis H_bcmp : Reusable.YG0d.abcmp_realizes segs B B_bcmp_tramp_entry.
(* The trampoline entry is bcmp_wrap's (owner ruling 06:15Z: constants, no literal; BCMP_WRAP = 0x42aac, the pc the
   F31 / F35 runs stop at).  OBLIGATION: the core's YTramp.bcmp_tramp = B.Prog.bcmp_wrap_c.BCMP_WRAP on image B
   (no YTramp in this tree).  OWNER: the top (a Theorem Labs lane). *)
Hypothesis B_bcmp_tramp_at : B_bcmp_tramp_entry = B.Prog.bcmp_wrap_c.BCMP_WRAP.

(* ---- RtPost, image B: B.ProgWorld.aview_vis_mrd (lib/B/ProgWorld.v:587, PROVED), cited by name (a Theorem Labs lane 13:12Z);
   this abbreviation only names it. ---- *)
Local Notation aview_vis_mrd := B.ProgWorld.aview_vis_mrd (only parsing).

(* V6 twin for the KIND_NAME table (added 04:35Z; drafted by a Theorem Labs lane; owner a Theorem Labs lane, same file and
   tables as V6): FLI's KNT (ACtlCutP.v, `addressable m KNA.KIND_NAME 112`, carried by every LK cut) crosses a runtime
   call only through AR, since the image's shadow is allocator-owned. *)
Hypothesis ctl_kind_name_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md -> B.AsanRT.addressable mem B.ACtlCutP.KNA.KIND_NAME 112.

(* T10 twin for KIND_NAME's 112 read-only bytes (RTPOST-SHARED-B.txt (a working note, not in this delivery), token for token; OWNER a Theorem Labs lane,
   lib/B/ProgBridgeData.v): FLI's KNT bytes cross a world-form callee by acall_kept's image arm. *)
Hypothesis ctl_kind_name_not_owned : forall a : Z,
  B.ACtlCutP.KNA.KIND_NAME <= a < B.ACtlCutP.KNA.KIND_NAME + 112 ->
  ~ Exists (Reusable.YG0n.in_zr a) (Reusable.YG0f.as_owned_static B) /\
  ~ (Reusable.YG0f.as_errno B <= a < Reusable.YG0f.as_errno B + 4).

(* T10 (RTPOST-SHARED-B.txt (a working note, not in this delivery), token for token; OWNER a Theorem Labs lane, lib/B/ProgBridgeData.v): the catalogue's read-only
   data is not a static owned extent nor the errno cell. *)
Hypothesis ctl_relro_not_owned : forall a : Z,
  (B.ACtlCutP.BAC.BA_FR + 72 <= a < B.ACtlCutP.BAC.BA_FR + 72 + Z.of_nat (length B.ACtlCutP.BAP.ba_tbl) \/
   B.ACtlCutP.SM.CAT <= a < B.ACtlCutP.SM.CAT + B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N) ->
  ~ Exists (Reusable.YG0n.in_zr a) (Reusable.YG0f.as_owned_static B) /\
  ~ (Reusable.YG0f.as_errno B <= a < Reusable.YG0f.as_errno B + 4).

(* The catalogue rows lie in the read-only-data span [RLO, RHI) of the entry's arodata_okS (ctl_base).  RLO and RHI
   are Section variables here.  OBLIGATION: at the composition (lib/B/ACtl.v), RLO = 0x9f168 and RHI = 0xa15e8 (the
   B PA instance's GNU_RELRO span), so 0x9f168 <= 0x9f620 and 0x9f620 + 296 * 11 = 0xa02d8 <= 0xa15e8 (lia).
   OWNER: a Theorem Labs lane (the top, ACtl.v).
   (Two atomic hypotheses, not one conjunction: tactics that destruct every conjunction in the context would loop on
   a conjunctive Section hypothesis.) *)
Hypothesis ctl_cat_relro_lo : RLO <= B.ACtlCutP.SM.CAT.
Hypothesis ctl_cat_relro_hi : B.ACtlCutP.SM.CAT + B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N <= RHI.

(* The catalogue's data (RTPOST-SHARED-B.txt (a working note, not in this delivery) at df3f9451f96, token for token; OWNER a Theorem Labs lane,
   lib/B/ProgBridgeData.v): addressable, and its 8-aligned shadow cover visible, at every AR state. *)
Hypothesis ctl_cat_addressable : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md ->
  B.AsanRT.addressable mem B.ACtlCutP.SM.CAT (B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N).
(* 07:22Z: WIDENED once to the 8-aligned shadow cover (a4 W2b: declaration_of_contract_F reads the row's aligned
   cover, up to 4 bytes below / 5 above the exact shadow at rows 0 and 10); visibility only, not zero. *)
Hypothesis ctl_cat_shadow_vis : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (B.Prog.rng_asan.sh_al8_lo B.ACtlCutP.SM.CAT)
    (B.Prog.rng_asan.sh_al8_hi B.ACtlCutP.SM.CAT (B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N) -
     B.Prog.rng_asan.sh_al8_lo B.ACtlCutP.SM.CAT).

(* declaration_of's footprint contract in its route (C) form (B/Prog/declaration_of_c.v, statements by path from
   a working branch 78f53925b08: shadow_rw narrowed to shadow_rw_on declaration_of_shadow_R, post
   region transport).  OBLIGATION: image B's proof of declaration_of_contract_F_on (declaration_of_F_holds_on, over
   asan_memcpy_contract_F_on; ETA ~14:00Z).  OWNER: a Theorem Labs lane. *)
Hypothesis declaration_of_F_holds_on : B.Prog.declaration_of_c.declaration_of_contract_F_on.

(* ctl_rt_C (route (C), a Theorem Labs lane 11:03Z, RTPOST-SHARED-B.txt (a working note, not in this delivery)): ctl_rt_C at a cut state is
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR (PROVED), which takes CtrlTSyms B and AR_laws (LAWS above), carried with ACtl.v's
   exact name and text (the top supplies TFIB_SYMS := Reusable.YD2l.CtrlB_syms).  VIS0 / OWNED_RO are gone. *)
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.
(* The arodata_okP premise of ctl_rt_C_of_AR at a cut state comes from ctl_base's arodata_okS moved along the journal by
   Reusable.APostBase.arodata_ok_journalP, which takes these two (owner ruling a Theorem Labs lane 06:46Z, token for token;
   OWNER: the top, which has RELRO_IMG in ACtl.v and the instance at its RLO / RHI). *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Context {RO_OFL : Reusable.APostBase.ro_below_ofl segs RLO RHI}.

(* TCLS: reac_ctrl_classify_box_frame (entry 0x837c4) by its cgif-form spec in the CALLER-JOURNAL form, cited by
   name from lib/B/Prog/C_reac_ctrl_classify_box_frame.v (on the walk line since 0110c1f2b9b; spec aligned to image A
   at 05:52Z: premises 0 <= f < 2^64, 0 <= u < 2^64 and C22; its post Q2 states the journal at k + EV_CLASSIFY,
   EV_CLASSIFY = 0).  OBLIGATION: pb_reac_ctrl_classify_box_frame : treac_ctrl_classify_box_frame_spec B RLO RHI.
   OWNER: a Theorem Labs lane (glue lane: another Theorem Labs lane).  The spec has no SK binder: its file fixes the journal's sink head to the
   core's Reusable.YE2k.tfib_sink_head (#[local] Existing Instance, its line 159). *)
Hypothesis TCLS : B.Prog.C_reac_ctrl_classify_box_frame.treac_ctrl_classify_box_frame_spec B RLO RHI.
(* This Section is generic in the journal's sink head SK (ACtl.v instantiates it, :169-172 / :187); seg_F30 passes its
   journal to TCLS and takes TCLS's journal back, so it needs SK to be TCLS's head.  OBLIGATION: eq_refl at ACtl.v's
   instantiation SK := Reusable.YE2k.tfib_sink_head.  OWNER: a Theorem Labs lane (the top). *)
Hypothesis SK_TFIB : SK = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YE2k.tfib_sink_head.

(* TMATCH: reac_box_catalogue_match (entry 0x84e40) by a Theorem Labs lane's treac_box_catalogue_match_spec (afn_pre /
   apost_base form, no achain), cited by name from lib/B/Prog/C_reac_box_catalogue_match.v (brought by path from
   a working branch 5608c59483e).  OBLIGATION: pb_reac_box_catalogue_match, whose Section
   takes RELRO_IMG (the B PA instance's pa_relro) and RLO <= 0x9f620 /\ 0x9f620 + 3256 <= RHI (lia at RLO = 0x9f168,
   RHI = 0xa15e8) at the composition.  OWNER: a Theorem Labs lane. *)
Hypothesis TMATCH : B.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec (SK := SK) RLO RHI B.

(* The F36 stretches are a Theorem Labs lane's proved lemmas B.Prog.Seg.Tac_f36F.f36_evt_*_F (header), used directly. *)

(* ===================== local helpers (proof plumbing; no statement here names a frame-route identifier) ===== *)
Local Notation AJ cx own ly3 S3 W3 mem3 md3 k :=
  (Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
     (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
     own ly3 S3 W3 mem3 md3 k).
Local Notation getr := lib.Reusable.YK11.getr.

(* A cut state as a footprint run's start state: lib/Lib's MS over the canonical register map (Regs6ss.mkR_of),
   which the walk does not tell apart from the cut's map (YA0nR.SRr_xregs_eqv). *)
Lemma w4f_enter : forall (W : Reusable.YA0n.world segs) pc regs mem md Q,
  Reusable.YA0n.SRr segs W
    (mkCfg (lib.Lib.MState.MS (lib.Lib.Regs6ss.mkR_of regs) lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc)
              lib.Reusable.YK11.fp_csr None mem (lib.Reusable.YK11.seg_rom segs)) md) Q ->
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc regs mem md) Q.
Proof.
  intros W pc regs mem md Q H. rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W (lib.Lib.Regs6ss.mkR_of regs) regs _ _ _ _ _ _ md Q H).
  apply lib.Lib.Regs6ss.xregs_eqv_sym, lib.Lib.Regs6ss.mkR_of_eqv.
Qed.

(* A footprint run (Lib/ExecF.evtF over Img0.rsegs) as a silent prefix of the walk (YA0nR.SRr_fevt_hid through
   ProgBridge.fevt_of_evtF); the continuation also gets the hidden bytes kept (ajournal_exec's premise). *)
Lemma w4f_run : forall (W : Reusable.YA0n.world segs) ms md RNG (P : machine_state -> Prop) Q,
  lib.Lib.ExecF.evtF B.Img0.rsegs RNG P ms ->
  Reusable.YK04R.fp_avoids (Reusable.YA0n.w_H W) RNG ->
  (forall ms' md', P ms' -> Reusable.YK04.same_but_materialized md md' ->
     (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem ms' x = ms_mem ms x) ->
     Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (mkCfg ms md) Q.
Proof.
  intros W ms md RNG P Q Hrun Hav K.
  apply (Reusable.YA0nR.SRr_fevt_hid segs Hwx W ms md RNG P Q (B.ProgBridge.fevt_of_evtF RNG P ms Hrun) Hav).
  intros ms' md' HP Hhid Hs. exact (K ms' md' HP Hs Hhid).
Qed.

(* The cut configuration of a run's end state. *)
Lemma w4f_exit : forall (W : Reusable.YA0n.world segs) pc R mem md Q,
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc R mem md) Q ->
  Reusable.YA0n.SRr segs W
    (mkCfg (lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem
              (lib.Reusable.YK11.seg_rom segs)) md) Q.
Proof. intros W pc R mem md Q H. rewrite <- B.ProgBridge.cfg_at_MS. exact H. Qed.

(* The journal across a stretch that writes no memory (YCbq.ajournal_exec, empty write set). *)
Lemma w4f_aj_nowrite : forall cx own ly3 S3 W3 mem3 md3 md' k,
  AJ cx own ly3 S3 W3 mem3 md3 k -> Reusable.YK04.same_but_materialized md3 md' ->
  AJ cx own ly3 S3 W3 mem3 md' k.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 md' k HJ Hs.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ => False) HJ);
    [intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity | exact Hs |
     intros a Ha; destruct Ha].
Qed.

(* ctl_rt_C at any cut state of the walk: B.ProgWorldCtlRtC.ctl_rt_C_of_AR on the journal's AR, its arodata_okP premise
   from ctl_base's arodata_okS (YCfn.tfib_lib_pre_x) moved along the journal by APostBase.arodata_ok_journalP. *)
Lemma w4f_ctlrt : forall cx own ly3 S3 W3 mem3 md3 k,
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx -> AJ cx own ly3 S3 W3 mem3 md3 k -> B.ACtlRtC.ctl_rt_C B ly3 S3 mem3.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  pose proof HJ as (HAR & _).
  apply (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 mem3 md3 HAR).
  destruct HB as (Hpre & _).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _).
  exact (Reusable.APostBase.arodata_ok_journalP segs RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hro).
Qed.

(* A stack range inside the journal's present window [c_sp cx - LLVMF_STK, c_sp cx) is visible. *)
Lemma w4f_vis_stack : forall cx own ly3 S3 W3 mem3 md3 k lo len,
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= lo -> lo + len <= ACtlCut.c_sp cx -> 0 <= lo ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k lo len HJ H1 H2 H0.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  pose proof (bv_unsigned_in_range 64 (getr (ACtlCut.c_regs cx) 2)) as Hsp.
  unfold ACtlCut.c_sp, Reusable.YG0d.spZ in *. unfold bv_modulus in Hsp. cbn [Z.of_N] in Hsp.
  split; [exact H0 |]. split; [lia |].
  intros a Ha. exact (proj1 (Hpres a ltac:(lia))).
Qed.

(* The owned class-6 frame of a cut is visible: its bytes are in_frames of the journal's own (awr_byte's fourth
   case), hence apresent (YCbq.awr_byte_present); the layout's frame base does not move (layout_le). *)
Lemma w4f_frame_at : forall cx ly3 S3 W3 mem3 md3 k fr,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  fr = Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr HJ HG1.
  pose proof HJ as (_ & Hly & _).
  rewrite (HG1 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)).
  unfold Reusable.YG0f.frame_addr. destruct Hly as (_ & _ & _ & _ & _ & HF & _). rewrite HF. reflexivity.
Qed.

Lemma w4f_frame_bounds : forall cx ly3 S3 W3 mem3 md3 k fr,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  4096 <= fr /\ fr + 4096 <= lib.Reusable.YM05.alloc_ceiling.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1.
  pose proof HJ as (HAR & _).
  rewrite (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (H1 & H2 & _).
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in H2. lia.
Qed.

Lemma w4f_vis_frame : forall cx ly3 S3 W3 mem3 md3 k fr lo len,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  fr <= lo -> lo + len <= fr + 4096 -> 0 <= len ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr lo len HJ HF HG1 H1 H2 H3.
  pose proof (w4f_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (B1 & B2).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hc.
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  split; [lia |]. split; [lia |].
  intros a Ha.
  refine (proj1 (proj1 (Reusable.YCbq.awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _))).
  right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
  left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr. change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
Qed.

(* A shadow byte of the owned frame is a shadow_rw byte by ctl_rt_C's cut-shadow conjunct: region (F) of
   B.ACtlRtC.cut_shadow, the frame (6, c_fpos cx) of frames S3 at frame_addr ly3 6 (c_fpos cx) = fr (w4f_frame_at). *)
Lemma w4f_cut_fsh : forall cx ly3 S3 W3 mem3 md3 k fr a,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  B.ShadowRwOn.shadow_rw_on (B.ACtlRtC.cut_shadow B ly3 S3) mem3 ->
  B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 512 -> B.AsanRT.in_shadow a ->
  wview B.Img0.rsegs mem3 (lib.Lib.Mem.wa a) <> None /\
  exists b, lib.Lib.Mem.mrd B.Img0.rsegs mem3 (lib.Lib.Mem.wa a) = Some b.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr a HJ HF HG1 HSW Ha Hsh.
  apply (HSW a); [| exact Hsh].
  left. exists 6, (ACtlCut.c_fpos cx). split; [rewrite HF; left; reflexivity |].
  rewrite <- (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1).
  change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha. lia.
Qed.

(* A spill slot read at the spill base of FRAC. *)
Lemma w4f_spill : forall regs m off v A,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 63 -> 0 <= off < 2 ^ 62 ->
  ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA HAb Hoff.
  assert (E : A' = A).
  { pose proof Hq as (Hq0 & Hq1 & _). unfold ACtlCut.rgv in HA, HA'. rewrite HA' in HA.
    apply (f_equal bv_unsigned) in HA. rewrite !Z_to_bv_unsigned in HA. unfold bv_wrap in HA.
    change (bv_modulus 64) with (2 ^ 64) in HA. rewrite lib.Lib.Mem.length_le8 in Hq1. cbn [Z.of_nat] in Hq1.
    Z.div_mod_to_equations. nia. }
  subst A'. exact Hq.
Qed.

(* Register transport of the body predicates: each reads only the registers named in its premises. *)
Ltac w4f_rw_regs :=
  repeat match goal with
  | E : getr ?R ?r = getr ?R0 ?r |- context [getr ?R ?r] => rewrite E
  end.
Ltac w4f_tr := intros; w4f_rw_regs; assumption.

Lemma w4f_rgv_tr : forall R R0 r v, getr R r = getr R0 r -> ACtlCut.rgv R0 r v -> ACtlCut.rgv R r v.
Proof. unfold ACtlCut.rgv. w4f_tr. Qed.
Lemma w4f_spill_tr : forall R R0 m off v, getr R 9 = getr R0 9 ->
  ACtlCutP.spill R0 m off v -> ACtlCutP.spill R m off v.
Proof. unfold ACtlCutP.spill, ACtlCut.rgv. w4f_tr. Qed.
Lemma w4f_FRAC_tr : forall cx fr sel R R0 m,
  getr R 2 = getr R0 2 -> getr R 3 = getr R0 3 -> getr R 4 = getr R0 4 -> getr R 8 = getr R0 8 ->
  getr R 9 = getr R0 9 -> getr R 19 = getr R0 19 -> getr R 26 = getr R0 26 ->
  ACtlCutP.FRAC B cx fr sel R0 m -> ACtlCutP.FRAC B cx fr sel R m.
Proof. unfold ACtlCutP.FRAC, ACtlCut.rgv, Reusable.YG0d.spZ. w4f_tr. Qed.
Lemma w4f_FLI_tr : forall cx fr R R0 m, getr R 9 = getr R0 9 -> getr R 27 = getr R0 27 ->
  ACtlCutP.FLI cx fr R0 m -> ACtlCutP.FLI cx fr R m.
Proof. unfold ACtlCutP.FLI, ACtlCutP.spill, ACtlCut.rgv. w4f_tr. Qed.
Lemma w4f_LK_tr : forall cx fr j R R0 m, getr R 9 = getr R0 9 -> getr R 27 = getr R0 27 ->
  ACtlCutP.LK cx fr j R0 m -> ACtlCutP.LK cx fr j R m.
Proof. unfold ACtlCutP.LK, ACtlCutP.FLI, ACtlCutP.spill, ACtlCut.rgv. w4f_tr. Qed.
Lemma w4f_FTK_tr : forall cx j fr R R0 m,
  getr R 9 = getr R0 9 -> getr R 22 = getr R0 22 -> getr R 24 = getr R0 24 -> getr R 25 = getr R0 25 ->
  ACtlCutP.FTK cx j fr R0 m -> ACtlCutP.FTK cx j fr R m.
Proof. unfold ACtlCutP.FTK, ACtlCutP.spill, ACtlCut.rgv. w4f_tr. Qed.
Lemma w4f_PT32_tr : forall cx j phi fr R R0 m,
  getr R 9 = getr R0 9 -> getr R 18 = getr R0 18 -> getr R 20 = getr R0 20 -> getr R 24 = getr R0 24 ->
  ACtlCutP.PT32 cx j phi fr R0 m -> ACtlCutP.PT32 cx j phi fr R m.
Proof. unfold ACtlCutP.PT32, ACtlCutP.spill, ACtlCut.rgv. w4f_tr. Qed.
Lemma w4f_FTURN_tr : forall cx j phi R R0 m, getr R 9 = getr R0 9 ->
  ACtlCutP.FTURN cx j phi R0 m -> ACtlCutP.FTURN cx j phi R m.
Proof. unfold ACtlCutP.FTURN, ACtlCutP.spill, ACtlCut.rgv. w4f_tr. Qed.
Lemma w4f_IFS_tr : forall cx fr j R R0 m, ACtlCutP.IFS cx fr j R0 m -> ACtlCutP.IFS cx fr j R m.
Proof. unfold ACtlCutP.IFS, ACtlCutP.FSj, ACtlCutP.FSb. w4f_tr. Qed.
Lemma w4f_PTL_tr : forall cx j phi fr R R0 m,
  getr R 9 = getr R0 9 -> getr R 18 = getr R0 18 -> getr R 20 = getr R0 20 ->
  ACtlCutP.PTL cx j phi fr R0 m -> ACtlCutP.PTL cx j phi fr R m.
Proof. unfold ACtlCutP.PTL, ACtlCutP.spill, ACtlCut.rgv. w4f_tr. Qed.

(* A spilled word as the 8-byte read the runs' premises state. *)
Lemma w4f_q64_read : forall m a v, ACtlCutP.q64 m a v ->
  ov_read_bytes B.Img0.rsegs m (Z_to_bv 64 a) 8 = Some (lib.Lib.Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. pose proof (lib.Lib.Mem.length_le8 (Z_to_bv 64 v)) as L.
  pose proof (lib.Lib.Mem.bytes_at_ov_read B.Img0.rsegs m a _ 0 8 H) as E.
  rewrite L in E. specialize (E ltac:(lia)).
  rewrite Z.add_0_r in E. change (skipn 0 ?l) with l in E. rewrite firstn_all2 in E by (rewrite L; lia). exact E.
Qed.

(* ---- helpers of seg_F32_b5c (a Theorem Labs lane) ---- *)

(* ===================== helpers of seg_F32_b5c (tag f32; proof plumbing, no statement names a frame-route
   identifier) ===================== *)

(* w4f_run with one more fact for the continuation: the run only grows the visible memory
   (YK04R.fsteps_restrict gives the restricted machine run, YI04.msteps_mem_grows its growth), the premise
   mem_grows (mrestrict ..) (mrestrict ..) of YCbq.ajournal_exec for a run that writes. *)
Lemma w4f_f32_run : forall (W : Reusable.YA0n.world segs) ms md RNG (P : machine_state -> Prop) Q,
  lib.Lib.ExecF.evtF B.Img0.rsegs RNG P ms ->
  Reusable.YK04R.fp_avoids (Reusable.YA0n.w_H W) RNG ->
  (forall ms' md', P ms' -> Reusable.YK04.same_but_materialized md md' ->
     (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem ms' x = ms_mem ms x) ->
     lib.Reusable.YK1b.mem_grows (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) (ms_mem ms))
       (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) (ms_mem ms')) ->
     Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (mkCfg ms md) Q.
Proof.
  intros W ms md RNG P Q Hrun Hav K.
  destruct (B.ProgBridge.fevt_of_evtF RNG P ms Hrun) as (ms' & Hf & HP).
  apply (Reusable.YA0nR.SRr_fsteps segs Hwx W ms ms' md RNG Q Hf Hav).
  intros md' Hs. apply (K ms' md' HP Hs).
  - exact (Reusable.YA0nR.fsteps_keeps_hidden segs Hwx (Reusable.YA0n.w_H W) RNG ms ms' (Reusable.YA0n.w_Hoff W) Hf Hav).
  - destruct (Reusable.YK04R.fsteps_restrict segs (Reusable.YA0n.w_H W) (Reusable.YA0n.w_Hoff W) Hwx RNG ms ms' Hf Hav)
      as [Hms _].
    exact (lib.Reusable.YI04.msteps_mem_grows segs _ _ Hms).
Qed.

(* The bytes a stage of this piece writes are awr_byte bytes of the journal: the owned class-6 frame
   [fr, fr + 4096), its shadow [S(fr), S(fr) + 512) (in_frames, awr_byte's fourth case), or the present stack window
   [c_sp cx - LLVMF_STK, c_sp cx) (the first case). *)
Lemma w4f_f32_awr : forall cx ly3 S3 W3 mem3 md3 k fr a,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  (fr <= a < fr + 4096 \/ B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 512 \/
   ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= a < ACtlCut.c_sp cx) ->
  Reusable.YCbq.awr_byte Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
    (ACtlCut.own6 cx) a.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 Ha.
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  destruct Ha as [Ha | [Ha | Ha]].
  - right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
    left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
    change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
  - right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
    right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
    change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *. lia.
  - left. exact Ha.
Qed.

(* Such bytes are visible (YCbq.awr_byte_present). *)
Lemma w4f_f32_vis : forall cx ly3 S3 W3 mem3 md3 k fr lo len,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len ->
     fr <= a < fr + 4096 \/ B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 512 \/
     ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= a < ACtlCut.c_sp cx) ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr lo len HJ HG1 H0 H1 Hin.
  split; [exact H0 |]. split; [exact H1 |]. intros a Ha.
  refine (proj1 (proj1 (Reusable.YCbq.awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _))).
  exact (w4f_f32_awr cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 (Hin a Ha)).
Qed.

(* The owned frame lies above the image (YG0s.frame_facts: the fake stack starts at ly_F >= 4096 and the class-6
   frames at ly_F + kFakeFramesOff + 6 * 2^20 or above) and in the low or the high application range
   (YCbq.frames_bounds' in_app). *)
Lemma w4f_f32_fr : forall cx ly3 S3 W3 mem3 md3 k fr,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k -> Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  0x60a000 <= fr /\ (fr + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= fr).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1.
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  pose proof HJ as (HAR & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (_ & _ & Happ).
  destruct HAR as (HM & _).
  destruct (Reusable.YG0s.frame_facts B ly3 S3 _ 6 (ACtlCut.c_fpos cx) HM Hin) as (_ & _ & (HF0 & _) & _ & _ & Hoff & _).
  assert (P20 : 2 ^ 20 = 1048576) by reflexivity. rewrite P20 in Hoff.
  unfold Reusable.YG0f.kFakeFramesOff in Hoff.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Happ.
  rewrite Efr. unfold Reusable.YG0f.frame_addr in *. lia.
Qed.

(* A live block of the journal: bounds, the application range, apart from the owned frame (YCbq.sep_block_frame),
   and visible (AR_blocks_law: apresent). *)
Lemma w4f_f32_blk : forall cx ly3 S3 W3 mem3 md3 k fr p n,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k -> Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  In (p, n) (Reusable.YG0d.ablocks B ly3 S3) ->
  4096 <= p /\ p + Reusable.YG00.req_size n <= lib.Reusable.YM05.alloc_ceiling /\
  (p + Reusable.YG00.req_size n <= 0x7fff7000 \/ 0x10007fff8000 <= p) /\
  (p + Reusable.YG00.req_size n <= fr \/ fr + 4096 <= p) /\
  (forall a, p <= a < p + Reusable.YG00.req_size n -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr p n HJ HF HG1 Hin.
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  pose proof HJ as (HAR & _).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR Hin) as (_ & H4 & Hc & Happ & Hpres & _).
  assert (Hinf : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 p n 6 (ACtlCut.c_fpos cx) HAR Hin Hinf)
    as Hd.
  unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. rewrite <- Efr in Hd.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hd.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ.
  split; [lia |]. split; [exact Hc |]. split; [lia |]. split; [lia |].
  intros a Ha. exact (proj1 (proj1 (Hpres a Ha))).
Qed.

(* A byte above the image whose view is not None is visible (the view of a hidden byte is the rom's, None there). *)
Lemma w4f_f32_vis_of_aview : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) s,
  0x5fe000 <= s < 2 ^ 64 -> Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem s <> None ->
  Reusable.YA0n.w_H W (Z_to_bv 64 s) = false.
Proof.
  intros W mem s Hs Hv. destruct (Reusable.YA0n.w_H W (Z_to_bv 64 s)) eqn:E; [| reflexivity].
  exfalso.
  assert (Hrom : lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 s) = None).
  { destruct (lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 s)) eqn:Er; [| reflexivity]. exfalso.
    destruct (Reusable.YG0s.seg_rom_in_img segs s ltac:(lia) ltac:(rewrite Er; discriminate)) as (sg & Hin & H1 & H2).
    apply (in_map (fun s0 : Segment => (Z.of_N (seg_base s0), Z.of_N (seg_size s0)))) in Hin.
    rewrite B.ProgBridge.tfibsegs_rsegs, B.ProgBridge.rsegs_spans in Hin. cbn [In] in Hin.
    destruct Hin as [E1 | [E1 | [E1 | [E1 | []]]]]; injection E1 as E1 E2; lia. }
  apply Hv. unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict. cbv beta.
  rewrite E, Hrom. reflexivity.
Qed.

(* The shadow byte of a live block's byte is visible (AR_shadow_law: the block's shadow hull is in the view). *)
Lemma w4f_f32_blksh : forall cx own ly3 S3 W3 mem3 md3 k p n i,
  AJ cx own ly3 S3 W3 mem3 md3 k -> In (p, n) (Reusable.YG0d.ablocks B ly3 S3) ->
  0 <= i < Reusable.YG00.req_size n ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (Z.shiftr (p + i) 3 + B.AsanRT.ASAN_K) 1.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k p n i HJ Hin Hi.
  pose proof HJ as (HAR & _).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR Hin) as (_ & H4 & Hc & _).
  destruct (Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR Hin) as (_ & Hhull).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (Hv : Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3 ((p + i) / 8 + B.AsanRT.ASAN_K) <> None).
  { apply Hhull. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.ASAN_K.
    Z.div_mod_to_equations. lia. }
  unfold B.AsanRT.ASAN_K in *.
  split; [Z.div_mod_to_equations; lia |]. split; [Z.div_mod_to_equations; lia |].
  intros a Ha. assert (Ea : a = (p + i) / 8 + 0x7fff8000) by lia. subst a.
  apply (w4f_f32_vis_of_aview W3 mem3); [Z.div_mod_to_equations; lia | exact Hv].
Qed.

(* The present stack window of the journal is a stack range of the memory (apresent: a byte is there). *)
Lemma w4f_f32_stk : forall cx own ly3 S3 W3 mem3 md3 k lo hi,
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= lo -> hi <= ACtlCut.c_sp cx -> 0 <= lo ->
  lib.Lib.Frame.stk B.Img0.rsegs mem3 lo hi.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k lo hi HJ H1 H2 H0.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  pose proof (bv_unsigned_in_range 64 (getr (ACtlCut.c_regs cx) 2)) as Hsp.
  unfold ACtlCut.c_sp, Reusable.YG0d.spZ in *. unfold bv_modulus in Hsp. cbn [Z.of_N] in Hsp.
  split; [exact H0 |]. split; [lia |].
  intros a Ha. destruct (Hpres a ltac:(lia)) as (_ & b & Hb).
  unfold lib.Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

(* A byte inside a bytes_at range reads Some. *)
Lemma w4f_f32_ba_some : forall m a bs x, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  a <= x < a + Z.of_nat (length bs) -> exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa x) = Some b.
Proof.
  intros m a bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - a)) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
  replace (a + (x - a)) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:En.
  - exists b. exact E.
  - apply nth_error_None in En. lia.
Qed.

(* A spill slot moves across a run that keeps its 8 bytes. *)
Lemma w4f_f32_spill : forall W regs m m' off v A, lib.Lib.Frame.munch W m m' -> ACtlCut.rgv regs 9 A ->
  0 <= A < 2 ^ 63 -> 0 <= off < 2 ^ 62 ->
  (forall x, A + off <= x < A + off + 8 -> lib.Lib.Frame.outside W x) ->
  ACtlCutP.spill regs m off v -> ACtlCutP.spill regs m' off v.
Proof.
  intros W regs m m' off v A MU HA HAb Hoff Hout Hs.
  exists A. split; [exact HA |].
  pose proof (w4f_spill regs m off v A Hs HA HAb Hoff) as Hq. unfold ACtlCutP.q64 in *.
  apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Hq MU). rewrite lib.Lib.Mem.length_le8.
  intros x Hx. apply Hout. lia.
Qed.

(* An addressable range apart from [fr + 32, fr + 40) stays addressable across the writes of S_F32's match arm:
   its shadow bytes are not S(fr) + 4 (another granule), and no shadow byte is in the frame or the stack. *)
Lemma w4f_f32_addr : forall fr spv m m' p n,
  lib.Lib.Frame.munch [(B.AsanRT.shadow_addr fr + 4, B.AsanRT.shadow_addr fr + 5); (fr + 32, fr + 40);
    (spv - 16, spv)] m m' ->
  B.AsanRT.addressable m p n -> fr mod 32 = 0 ->
  (fr + 40 <= B.AsanRT.LOWMEM_END \/ B.AsanRT.HIGHMEM_BEG <= fr) -> B.AsanRT.HIGHMEM_BEG <= spv - 16 ->
  (p + n <= fr + 32 \/ fr + 40 <= p) -> B.AsanRT.addressable m' p n.
Proof.
  intros fr spv m m' p n MU HA Hm Hf Hs Hd.
  apply (B.Prog.Seg.F32.f32_addr_keep _ m m' p n HA MU).
  intros i Hi. pose proof HA as (Hp0 & Hn0 & Hpn & _).
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG,
    B.AsanRT.APPMEM_END in *.
  cbn [lib.Lib.Frame.outside]. Z.div_mod_to_equations. repeat split; lia.
Qed.

(* FRAC's memory facts move across a run that keeps them; the frame's shadow bytes are given anew. *)
Lemma w4f_f32_FRAC_mem : forall cx fr sel R m m' W A0,
  ACtlCutP.FRAC B cx fr sel R m -> lib.Lib.Frame.munch W m m' -> ACtlCut.rgv R 9 A0 -> 0 <= A0 < 2 ^ 64 ->
  (forall x, A0 + 40 <= x < A0 + 56 \/ A0 + 336 <= x < A0 + 344 \/ fr <= x < fr + 24 \/
     fr + 4088 <= x < fr + 4096 \/ ACtlCut.c_sp cx - 104 <= x < ACtlCut.c_sp cx -> lib.Lib.Frame.outside W x) ->
  (exists sh, lib.Lib.Mem.bytes_at segs m' (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) ->
  ACtlCutP.FRAC B cx fr sel R m'.
Proof.
  intros cx fr sel R m m' W A0 HF MU HA0 HA0b Hout Hsh.
  destruct HF as (A & sp & E2 & Hm & Hsp & E4 & E8 & E9 & E3 & E19 & E26 & Hf32 & HA32 & HAle & HspA & HfrA & HA448 &
    Hsp4096 & HspEnd & Q336 & Q48 & Q40 & Qhdr & Q16 & _ & Hsv & Qflag).
  assert (EA : A = A0).
  { unfold ACtlCut.rgv in E9, HA0. rewrite E9 in HA0. apply (f_equal bv_unsigned) in HA0.
    pose proof (bv_unsigned_in_range 64 (getr R 2)) as R2.
    pose proof (bv_unsigned_in_range 64 (getr (ACtlCut.c_regs cx) 2)) as Rc.
    unfold bv_modulus in R2, Rc. cbn [Z.of_N] in R2, Rc. unfold Reusable.YG0d.spZ in Hsp.
    unfold ACtlCut.c_sp, Reusable.YG0d.spZ in HAle, HA448.
    rewrite !lib.Lib.MState.unsigned_lit in HA0 by lia. exact HA0. }
  subst A0.
  exists A, sp. unfold ACtlCutP.q64 in *.
  refine (conj E2 (conj Hm (conj Hsp (conj E4 (conj E8 (conj E9 (conj E3 (conj E19 (conj E26 (conj Hf32 (conj HA32
    (conj HAle (conj HspA (conj HfrA (conj HA448 (conj Hsp4096 (conj HspEnd (conj _ (conj _ (conj _ (conj _ (conj _
    (conj Hsh (conj _ _)))))))))))))))))))))))).
  - apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Q336 MU). rewrite lib.Lib.Mem.length_le8.
    intros x Hx. apply Hout. lia.
  - apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Q48 MU). rewrite lib.Lib.Mem.length_le8.
    intros x Hx. apply Hout. lia.
  - apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Q40 MU). rewrite lib.Lib.Mem.length_le8.
    intros x Hx. apply Hout. lia.
  - apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Qhdr MU). rewrite lib.Lib.Mem.length_le8.
    intros x Hx. apply Hout. lia.
  - apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Q16 MU). rewrite lib.Lib.Mem.length_le8.
    intros x Hx. apply Hout. lia.
  - apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Hsv MU).
    assert (L : length (ACtlCutP.saved_bytes cx) = 104%nat)
      by (unfold ACtlCutP.saved_bytes; rewrite !length_app, !lib.Lib.Mem.length_le8; reflexivity).
    rewrite L. intros x Hx. apply Hout. lia.
  - apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Qflag MU). rewrite lib.Lib.Mem.length_le8.
    intros x Hx. apply Hout. lia.
Qed.

(* LK moves when its spills, OURb, its addressable frame ranges (all at fr + 40 or above), the frame's stack fact and
   KNT move. *)
Lemma w4f_f32_LK_mem : forall cx fr j R m m',
  ACtlCutP.LK cx fr j R m ->
  (forall off v, ACtlCutP.spill R m off v -> 0 <= off <= 440 -> ACtlCutP.spill R m' off v) ->
  ACtlCutP.OURb cx fr m' ->
  (forall p n, B.AsanRT.addressable m p n -> fr + 40 <= p -> B.AsanRT.addressable m' p n) ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.KNT m' ->
  ACtlCutP.LK cx fr j R m'.
Proof.
  intros cx fr j R m m' (Hj & S240 & HOUR0 & HFLI) Hsp HOUR Had Hstk HKNT.
  unfold ACtlCutP.FLI, ACtlCutP.RAD in HFLI.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  unfold ACtlCutP.LK, ACtlCutP.FLI, ACtlCutP.RAD.
  repeat match goal with |- _ /\ _ => split end.
  all: first [ assumption
             | (apply Hsp; [assumption | lia])
             | (apply Had; [assumption | unfold ACtlCutP.fragb; lia]) ].
Qed.

(* IFS moves when the two frame records and `first` [fr + 2688, fr + 2920) are kept and `first` stays addressable;
   the record lengths are the model's (Tac_ro.tr_ID_length / tr_FG_length / tr_body_length). *)
Lemma w4f_f32_IFS_mem : forall cx fr j R m m' W,
  ACtlCutP.IFS cx fr j R m -> lib.Lib.Frame.munch W m m' ->
  (forall x, fr + 2688 <= x < fr + 2920 -> lib.Lib.Frame.outside W x) ->
  (B.AsanRT.addressable m (fr + 2880) 40 -> B.AsanRT.addressable m' (fr + 2880) 40) ->
  ACtlCutP.IFS cx fr j R m'.
Proof.
  intros cx fr j R m m' W ((Hid & Hidok) & (Hfg & Hfgok) & (Hh & Hn & Hb & Had & HFI)) MU Hout Hadk.
  unfold ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.IDb, ACtlCutP.IDBe, ACtlCutP.FGj, ACtlCutP.FGb, ACtlCutP.FGBe,
    ACtlCutP.FSj, ACtlCutP.FSb, ACtlCutP.u32, ACtlCutP.b8 in *.
  pose proof (B.Prog.Seg.Tac_ro.tr_ID_length (ACtlCut.c_in cx) j) as LID.
  pose proof (B.Prog.Seg.Tac_ro.tr_FG_length (ACtlCut.c_in cx) j) as LFG.
  pose proof (B.Prog.Seg.Tac_ro.tr_body_length (ACtlCut.c_in cx) j) as LB.
  refine (conj (conj _ Hidok) (conj (conj _ Hfgok) (conj _ (conj _ (conj _ (conj (Hadk Had) HFI)))))).
  - apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Hid MU). rewrite LID. intros x Hx. apply Hout. lia.
  - apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Hfg MU). rewrite LFG. intros x Hx. apply Hout. lia.
  - apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Hh MU). rewrite lib.Lib.Mem.length_le4.
    intros x Hx. apply Hout. lia.
  - apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Hn MU). cbn [length]. intros x Hx. apply Hout. lia.
  - apply (B.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Hb MU). intros x Hx. apply Hout. lia.
Qed.

(* reac_box_catalogue (entry 0x84dec) by its CLOSED footprint contract, lifted at the walk's RNG_W.  The ONE place
   that instantiates the contract (by eapply, so the order of its binders does not matter); the post is restated
   over spv = bv_unsigned sp and c <> 0.  Route (C): the `_on` contract (B/Prog/reac_box_catalogue_c.v, premise
   shadow_rw DROPPED; proved as reac_box_catalogueF.reac_box_catalogue_F_holds_on). *)
Lemma w4f_f32_cat_lift : B.Prog.reac_box_catalogue_c.reac_box_catalogue_contract_F_on ->
  forall (W : Reusable.YA0n.world segs) (c lo spv : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bv_unsigned sp = spv -> a0 = Z_to_bv 64 c -> c <> 0 ->
  lib.Lib.Frame.stk B.Img0.rsegs m lo spv -> lo + 16 <= spv ->
  B.AsanRT.asan_cells m ->
  (forall x, B.AsanRT.GOT_CELL_K <= x < B.AsanRT.GOT_CELL_K + 8 \/ B.AsanRT.CELL_K <= x < B.AsanRT.CELL_K + 8 \/
     B.AsanRT.in_shadow x -> lib.Lib.Frame.outside [(spv - 16, spv); (c, c + 8)] x) ->
  c mod 8 = 0 -> lib.Lib.Mem.wr_at B.Img0.rsegs m c 8 -> (c + 8 <= spv - 16 \/ spv <= c) ->
  B.AsanRT.addressable m c 8 ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (spv - 16) 16 ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) c 8 ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W) (B.AsanRT.shadow_addr c)
    (B.AsanRT.shadow_addr (c + 7) - B.AsanRT.shadow_addr c + 1) ->
  lib.Lib.ExecF.evtF B.Img0.rsegs (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W))
    (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
       ms' = lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1
               (Z_to_bv 64 B.Prog.reac_box_catalogue_c.BOX_CATALOGUE) a1' a2' a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (lib.Lib.MState.ret_pc ra) fc None m' (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
       lib.Lib.Frame.munch [(spv - 16, spv); (c, c + 8)] m m' /\
       lib.Lib.Frame.wmono B.Img0.rsegs m m' /\ lib.Lib.Frame.stk B.Img0.rsegs m' lo spv /\
       lib.Lib.Mem.bytes_at B.Img0.rsegs m' c (lib.Lib.Mem.le8 (Z_to_bv 64 11)))
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 B.Prog.reac_box_catalogue_c.REAC_BOX_CATALOGUE) fc None m
       (lib.Lib.PropExec.seg_rom B.Img0.rsegs)).
Proof.
  intros HC W c lo spv ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Hsp Ha0 Hc0 HST Hlo HAC Hout Hc8 HWR HD HAD Vsp Vc Vsh.
  subst spv.
  unfold B.Prog.reac_box_catalogue_c.reac_box_catalogue_contract_F_on in HC.
  assert (E : lib.Lib.ExecF.evtF B.Img0.rsegs (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W))
            (B.Prog.reac_box_catalogue_c.reac_box_catalogue_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4
               s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c lo)
            (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 B.Prog.reac_box_catalogue_c.REAC_BOX_CATALOGUE) fc None m
               (lib.Lib.PropExec.seg_rom B.Img0.rsegs))).
  { eapply HC; unfold B.Prog.reac_box_catalogue_c.REAC_BOX_CATALOGUE_FRAME;
      first [ eassumption
            | (refine (or_intror (conj _ (conj _ (conj _ _)))); eassumption)
            | (intros _; split; apply B.ProgBridge.rng_of_visible; eassumption)
            | (apply B.ProgBridge.rng_of_visible; eassumption)
            | (apply B.ProgBridge.rng_of_visible;
               apply (B.ProgBridge.range_visible_sub _ _ _ _ _ (B.ProgBridge.rt_vis_W W));
               unfold B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.RT_LO, B.AsanRT.RT_HI; lia) ]. }
  unfold lib.Lib.ExecF.evtF in *.
  destruct E as (ms' & Hrun & (a1' & a2' & m' & Ems & MU & WM & _ & ST & Hc11)).
  exists ms'. split; [exact Hrun |]. exists a1', a2', m'.
  replace (c =? 0) with false in Hc11 by (symmetry; apply Z.eqb_neq; exact Hc0).
  exact (conj Ems (conj MU (conj WM (conj ST Hc11)))).
Qed.

(* ---- helpers of seg_F31 / seg_F35 and of every world-form callee (a Theorem Labs lane) ---- *)
(* The raw bytes of [lo, hi) are the same in m and m'. *)
Local Notation MKEPT m m' lo hi :=
  (forall w4f_x : Z, lo <= w4f_x < hi ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 w4f_x) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 w4f_x)).

(* ---- the one step from a view-level post to a raw fact: a visible address whose view is kept keeps its byte ---- *)
Lemma w4f_bcmp_pt : forall (W : Reusable.YA0n.world segs) (m m' : word -> option byte) a,
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m' a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m a ->
  lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a).
Proof.
  intros W m m' a Hv E.
  rewrite (aview_vis_mrd W m' a Hv), (aview_vis_mrd W m a Hv) in E.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a)) as [b'|],
    (lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a)) as [b|]; cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma w4f_bcmp_mrd : forall (W : Reusable.YA0n.world segs) (m m' : word -> option byte) lo hi,
  (forall a, lo <= a < hi -> Reusable.YA0n.w_H W (Z_to_bv 64 a) = false) ->
  (forall a, lo <= a < hi ->
     Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m' a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m a) ->
  MKEPT m m' lo hi.
Proof. intros W m m' lo hi Hv Ha x Hx. exact (w4f_bcmp_pt W m m' x (Hv x Hx) (Ha x Hx)). Qed.

(* A byte whose view is not None at a non-image address is visible. *)
Lemma w4f_bcmp_vis_of_aview : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs a -> Reusable.YG0n.aview segs H m a <> None ->
  H (Z_to_bv 64 a) = false.
Proof.
  intros H m a Ha Hn Hv.
  destruct (Reusable.YG0n.aview segs H m a) as [v|] eqn:Ev; [| exfalso; apply Hv; reflexivity].
  destruct (Reusable.YCbq.aview_byte segs H m a v Ev) as (b & _ & -> & _).
  refine (proj1 (Reusable.YCbq.apresent_transfer segs (fun _ => false) H (fun _ => Some b) m a Ha Hn _ _)).
  - rewrite Ev. reflexivity.
  - split; [reflexivity | exists b; reflexivity].
Qed.

(* ---- primitive raw-fact transfers ---- *)
Lemma w4f_bcmp_bytes : forall (m m' : word -> option byte) a bs,
  MKEPT m m' a (a + Z.of_nat (length bs)) ->
  lib.Lib.Mem.bytes_at segs m a bs -> lib.Lib.Mem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs K (H0 & H1 & H). split; [exact H0 |]. split; [exact H1 |].
  intros i Hi. exact (eq_trans (K (a + Z.of_nat i) ltac:(lia)) (H i Hi)).
Qed.

Lemma w4f_bcmp_q64 : forall (m m' : word -> option byte) a v, MKEPT m m' a (a + 8) ->
  ACtlCutP.q64 m a v -> ACtlCutP.q64 m' a v.
Proof.
  intros m m' a v K H. unfold ACtlCutP.q64 in *. apply (w4f_bcmp_bytes m m' a _); [| exact H].
  rewrite lib.Lib.Mem.length_le8. exact K.
Qed.

Lemma w4f_bcmp_u32 : forall (m m' : word -> option byte) a v, MKEPT m m' a (a + 4) ->
  ACtlCutP.u32 m a v -> ACtlCutP.u32 m' a v.
Proof.
  intros m m' a v K H. unfold ACtlCutP.u32 in *. apply (w4f_bcmp_bytes m m' a _); [| exact H].
  rewrite lib.Lib.Mem.length_le4. exact K.
Qed.

Lemma w4f_bcmp_b8 : forall (m m' : word -> option byte) a v, MKEPT m m' a (a + 1) ->
  ACtlCutP.b8 m a v -> ACtlCutP.b8 m' a v.
Proof. intros m m' a v K H. unfold ACtlCutP.b8 in *. exact (w4f_bcmp_bytes m m' a [Z_to_bv 8 v] K H). Qed.

Lemma w4f_bcmp_sp : forall R R0 (m m' : word -> option byte) A csp off v,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> 0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 ->
  MKEPT m m' A csp -> 0 <= off <= 440 ->
  ACtlCutP.spill R0 m off v -> ACtlCutP.spill R m' off v.
Proof.
  intros R R0 m m' A csp off v HA E9 H0 H1 H2 K Hoff Hs.
  pose proof (w4f_spill R0 m off v A Hs HA ltac:(lia) ltac:(lia)) as Hq.
  exists A. split; [exact (w4f_rgv_tr R R0 9 A E9 HA) |].
  apply (w4f_bcmp_q64 m m' (A + off) v); [intros x Hx; apply K; lia | exact Hq].
Qed.

Lemma w4f_bcmp_addr : forall (m m' : word -> option byte) p n,
  (forall i, 0 <= i < n -> lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) =
                           lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i)))) ->
  B.AsanRT.addressable m p n -> B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n K (H0 & H1 & H2 & H). split; [exact H0 |]. split; [exact H1 |]. split; [exact H2 |].
  intros i Hi. destruct (H i Hi) as (Happ & b & Hb & Hok). split; [exact Happ |].
  exists b. split; [| exact Hok]. exact (eq_trans (K i Hi) Hb).
Qed.

(* A raw-present range stays a stack range (wview / mrd of a present byte). *)
Lemma w4f_bcmp_stk : forall (m m' : word -> option byte) lo hi,
  (forall a, lo <= a < hi -> exists b, m' (Z_to_bv 64 a) = Some b) ->
  lib.Lib.Frame.stk segs m lo hi -> lib.Lib.Frame.stk segs m' lo hi.
Proof.
  intros m m' lo hi Hp (H0 & H1 & _). split; [exact H0 |]. split; [exact H1 |].
  intros a Ha. destruct (Hp a Ha) as [b Hb]. unfold lib.Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

(* ---- the callee's view-level arguments from raw facts at visible addresses ---- *)
Lemma w4f_bcmp_signed : forall b : byte, 0 <= bv_signed b <= 7 -> bv_unsigned b = bv_signed b.
Proof.
  intros b Hb. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128 in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma w4f_bcmp_range_addr : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) p n,
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false) ->
  B.AsanRT.addressable m p n ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) Reusable.YG0f.SHADOW_OFF p n.
Proof.
  intros W m p n Hv (_ & _ & _ & H) x Hx.
  destruct (H (x - p) ltac:(lia)) as (_ & b & Hb & Hok).
  pose proof (Hv (x - p) ltac:(lia)) as Hvx.
  replace (p + (x - p)) with x in Hb, Hok, Hvx by lia.
  exists (bv_unsigned b). split.
  - replace (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x) with (B.AsanRT.shadow_addr x)
      by (unfold Reusable.YG0v.shadow_of_addr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.SHADOW_OFF; lia).
    rewrite (aview_vis_mrd W m _ Hvx). unfold lib.Lib.Mem.wa in Hb. rewrite Hb. reflexivity.
  - unfold Reusable.YG0v.saddr_ok. unfold B.AsanRT.shadow_ok in Hok.
    destruct Hok as [Hok | Hok].
    + left. rewrite (w4f_bcmp_signed b ltac:(lia)). exact Hok.
    + right. rewrite (w4f_bcmp_signed b ltac:(lia)). lia.
Qed.

(* The byte the view reads at a visible address of a bytes_at fact. *)
Lemma w4f_bcmp_aview_at : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) x l k,
  lib.Lib.Mem.bytes_at segs m x l -> (k < length l)%nat ->
  Reusable.YA0n.w_H W (Z_to_bv 64 (x + Z.of_nat k)) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (x + Z.of_nat k) =
  option_map (fun b : byte => bv_unsigned b) (nth_error l k).
Proof.
  intros W m x l k (_ & _ & H) Hk Hv. rewrite (aview_vis_mrd W m _ Hv). f_equal. exact (H k Hk).
Qed.

Lemma w4f_bcmp_list_eq : forall (l r : list byte), length l = length r ->
  (forall k, (k < length l)%nat -> nth_error l k = nth_error r k) -> l = r.
Proof.
  induction l as [|a l IH]; intros [|b r] HL H; cbn in HL; try discriminate; [reflexivity |].
  f_equal.
  - specialize (H 0%nat ltac:(cbn; lia)). cbn in H. injection H as H. exact H.
  - apply IH; [lia | intros k Hk; exact (H (S k) ltac:(cbn; lia))].
Qed.

(* The bcmp result: the view equality of the n compared bytes is the equality of the two byte lists. *)
Lemma w4f_bcmp_cmp : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) x y (l r : list byte) n,
  length l = length r -> n = Z.of_nat (length l) ->
  lib.Lib.Mem.bytes_at segs m x l -> lib.Lib.Mem.bytes_at segs m y r ->
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (x + i)) = false) ->
  (forall i, 0 <= i < n -> Reusable.YA0n.w_H W (Z_to_bv 64 (y + i)) = false) ->
  ((forall i, 0 <= i < n ->
      Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (x + i) =
      Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (y + i)) <-> l = r).
Proof.
  intros W m x y l r n HL Hn Hx Hy Vx Vy. subst n. split.
  - intros H. apply (w4f_bcmp_list_eq l r HL).
    intros k Hk. pose proof (H (Z.of_nat k) ltac:(lia)) as E.
    rewrite (w4f_bcmp_aview_at W m x l k Hx Hk (Vx (Z.of_nat k) ltac:(lia))) in E.
    rewrite (w4f_bcmp_aview_at W m y r k Hy ltac:(lia) (Vy (Z.of_nat k) ltac:(lia))) in E.
    destruct (nth_error l k) as [b1|], (nth_error r k) as [b2|]; cbn in E; try discriminate; [|reflexivity].
    injection E as E. f_equal. apply bv_eq. exact E.
  - intros <- i Hi.
    replace i with (Z.of_nat (Z.to_nat i)) by lia.
    rewrite (w4f_bcmp_aview_at W m x l (Z.to_nat i) Hx ltac:(lia) (Vx (Z.of_nat (Z.to_nat i)) ltac:(lia))).
    rewrite (w4f_bcmp_aview_at W m y l (Z.to_nat i) Hy ltac:(lia) (Vy (Z.of_nat (Z.to_nat i)) ltac:(lia))).
    reflexivity.
Qed.

(* ---- visibility of the walk's owned frame, its shadow and the live blocks ---- *)
Lemma w4f_bcmp_frame_present : forall cx ly3 S3 W3 mem3 md3 k fr a,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  (fr <= a < fr + 4096 \/ Reusable.YG0f.shadow_addr fr <= a < Reusable.YG0f.shadow_addr fr + 512) ->
  Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 Ha.
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  refine (proj1 (Reusable.YCbq.awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _)).
  right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
  unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096. change (4096 / 8) with 512. exact Ha.
Qed.

Lemma w4f_bcmp_hull_frame : forall cx ly3 S3 W3 mem3 md3 k fr d n,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  fr + 56 <= d -> d + n + 64 <= fr + 4096 -> 0 < n ->
  Reusable.YG0d.shadow_hull_vis (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3) d n.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr d n HJ HG1 H1 H2 H3 s Hs.
  apply (Reusable.YCbq.aview_some_of_apresent segs).
  apply (w4f_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr s HJ HG1). right.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in *. Z.div_mod_to_equations. lia.
Qed.

Lemma w4f_bcmp_block_shadow_vis : forall ly S (W : Reusable.YA0n.world segs) mem md p n i,
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  0 <= i < Reusable.YG00.req_size n ->
  Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) = false.
Proof.
  intros ly S W mem md p n i HAR Hin Hi.
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hp4096 & Hpc & _).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  destruct (Reusable.YCbq.range_addressable_of_block segs B LAWS ly S W mem md p n p (Reusable.YG00.req_size n)
              HAR Hin ltac:(lia) ltac:(lia) (p + i) ltac:(lia)) as (s & Hs & _).
  replace (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (p + i)) with (B.AsanRT.shadow_addr (p + i)) in Hs
    by (unfold Reusable.YG0v.shadow_of_addr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.SHADOW_OFF; lia).
  apply (w4f_bcmp_vis_of_aview _ mem).
  - unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia.
  - intros Him. apply segs_low in Him. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.kLowMemEnd in Him.
    Z.div_mod_to_equations. lia.
  - rewrite Hs. discriminate.
Qed.

(* ---- a view kept outside a window [wlo, whi) gives the raw bytes of the frame, its shadow, the spill area and
   KNT's image table (for the walk's cuts: everything the frame-loop bodies read except the live block) ---- *)
Lemma w4f_bcmp_frame_kept : forall cx ly3 S3 W3 mem3 md3 k fr (mem2 : word -> option byte) sp,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  ACtlCut.c_sp cx - 4096 < sp -> sp <= ACtlCut.c_sp cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 8192 <= a < sp) ->
     Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem2 a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3 a) ->
  MKEPT mem3 mem2 sp (ACtlCut.c_sp cx) /\ MKEPT mem3 mem2 fr (fr + 4096) /\
  MKEPT mem3 mem2 (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 512) /\
  MKEPT mem3 mem2 ACtlCutP.KNA.KIND_NAME (ACtlCutP.KNA.KIND_NAME + 112).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr mem2 sp HJ HF HG1 Hsp1 Hsp2 Hk.
  pose proof (w4f_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Bfr1 & Bfr2).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hastk as (_ & _ & Hcl & Hlsp & Hshi & Hshi47 & _). unfold Reusable.YCfn.LLVMF_STK in Hlsp, Hpres.
  pose proof (B.ProgBridge.img_vis_W W3) as (_ & _ & Himg).
  unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in Himg.
  assert (HS : 0 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 512 <= lib.Reusable.YM05.alloc_ceiling).
  { unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  refine (conj _ (conj _ (conj _ _))).
  - intros a Ha. apply (w4f_bcmp_pt W3); [exact (proj1 (Hpres a ltac:(lia))) | apply Hk; lia].
  - intros a Ha. apply (w4f_bcmp_pt W3); [| apply Hk; lia].
    exact (proj1 (w4f_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 (or_introl Ha))).
  - intros a Ha. apply (w4f_bcmp_pt W3); [| apply Hk; lia].
    refine (proj1 (w4f_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 (or_intror _))).
    unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
      Reusable.YG0f.SHADOW_OFF in *. lia.
  - intros a Ha. unfold ACtlCutP.KNA.KIND_NAME in Ha.
    apply (w4f_bcmp_pt W3); [apply Himg; lia | apply Hk; lia].
Qed.

(* The same for a live block and its shadow (the block law gives the bytes present, the shadow law the shadow
   bytes' view, hence their visibility). *)
Lemma w4f_bcmp_block_kept : forall ly S (W : Reusable.YA0n.world segs) mem md (mem2 : word -> option byte)
    wlo whi p n,
  Reusable.YG0n.AR segs B ly S W mem md -> In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  lib.Reusable.YM05.alloc_ceiling <= wlo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (wlo <= a < whi) ->
     Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem2 a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a) ->
  MKEPT mem mem2 p (p + Reusable.YG00.req_size n) /\
  (forall i, 0 <= i < Reusable.YG00.req_size n ->
     lib.Lib.Mem.mrd B.Img0.rsegs mem2 (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i)))).
Proof.
  intros ly S W mem md mem2 wlo whi p n HAR Hin Hw Hk.
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hp4096 & Hpc & _ & Hpr & _).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  split.
  - intros a Ha. apply (w4f_bcmp_pt W); [exact (proj1 (proj1 (Hpr a Ha))) | apply Hk; lia].
  - intros i Hi. apply (w4f_bcmp_pt W).
    + exact (w4f_bcmp_block_shadow_vis ly S W mem md p n i HAR Hin Hi).
    + apply Hk; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* ---- the cut-body predicates across a call that keeps the raw bytes of the regions they read ---- *)
Lemma w4f_bcmp_FRAC : forall cx fr sel R R0 (m m' : word -> option byte),
  getr R 2 = getr R0 2 -> getr R 3 = getr R0 3 -> getr R 4 = getr R0 4 -> getr R 8 = getr R0 8 ->
  getr R 9 = getr R0 9 -> getr R 19 = getr R0 19 -> getr R 26 = getr R0 26 ->
  MKEPT m m' (Reusable.YG0d.spZ R0) (ACtlCut.c_sp cx) -> MKEPT m m' fr (fr + 4096) ->
  MKEPT m m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 512) ->
  ACtlCutP.FRAC B cx fr sel R0 m -> ACtlCutP.FRAC B cx fr sel R m'.
Proof.
  intros cx fr sel R R0 m m' E2 E3 E4 E8 E9 E19 E26 KS KF KSH
    (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle & HspA & HfrA & HA448 &
     Hsp4096 & HspEnd & Q336 & Q48 & Q40 & Qhdr & Q16 & (sh & Hsh & Lsh) & Hsav & Q4088).
  assert (Lsv : length (ACtlCutP.saved_bytes cx) = 104%nat)
    by (unfold ACtlCutP.saved_bytes; rewrite !length_app, !lib.Lib.Mem.length_le8; reflexivity).
  assert (Lsh' : Z.of_nat (length sh) = 392) by (rewrite Lsh; reflexivity).
  unfold ACtlCutP.FRAME_BYTES in *.
  exists A, sp.
  split; [rewrite E2; exact Hr2 |].
  split; [exact Hspm |].
  split; [unfold Reusable.YG0d.spZ in *; rewrite E2; exact HspZ |].
  split; [rewrite E4; exact Hr4 |].
  split; [exact (w4f_rgv_tr R R0 8 _ E8 Hr8) |].
  split; [exact (w4f_rgv_tr R R0 9 _ E9 Hr9) |].
  split; [rewrite E3; exact Hr3 |].
  split; [exact (w4f_rgv_tr R R0 19 _ E19 Hr19) |].
  split; [exact (w4f_rgv_tr R R0 26 _ E26 Hr26) |].
  do 8 (split; [assumption |]).
  split; [apply (w4f_bcmp_q64 m m' (A + 336) fr); [intros x Hx; apply KS; lia | exact Q336] |].
  split; [apply (w4f_bcmp_q64 m m' (A + 48) sel); [intros x Hx; apply KS; lia | exact Q48] |].
  split; [apply (w4f_bcmp_q64 m m' (A + 40) fr); [intros x Hx; apply KS; lia | exact Q40] |].
  split; [apply (w4f_bcmp_q64 m m' fr _); [intros x Hx; apply KF; lia | exact Qhdr] |].
  split; [apply (w4f_bcmp_q64 m m' (fr + 16) _); [intros x Hx; apply KF; lia | exact Q16] |].
  split; [exists sh; split; [apply (w4f_bcmp_bytes m m' _ sh); [intros x Hx; apply KSH; lia | exact Hsh] |
    exact Lsh] |].
  split; [apply (w4f_bcmp_bytes m m' _ _); [intros x Hx; apply KS; rewrite Lsv in Hx; lia | exact Hsav] |].
  apply (w4f_bcmp_q64 m m' (fr + 4088) _); [intros x Hx; apply KF; lia | exact Q4088].
Qed.

Lemma w4f_bcmp_HB : forall (m m' : word -> option byte) phi len,
  (forall i, 0 <= i < B.ACtlK.a_size len ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i))) =
     lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (B.AsanRT.shadow_addr (phi + i)))) ->
  ACtlCutP.HB m phi len -> ACtlCutP.HB m' phi len.
Proof. intros m m' phi len K (H0 & H1). split; [exact H0 | exact (w4f_bcmp_addr m m' phi _ K H1)]. Qed.

Lemma w4f_bcmp_FTK : forall cx j fr R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> getr R 22 = getr R0 22 -> getr R 24 = getr R0 24 ->
  getr R 25 = getr R0 25 -> 0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 -> MKEPT m m' A csp ->
  ACtlCutP.FTK cx j fr R0 m -> ACtlCutP.FTK cx j fr R m'.
Proof.
  intros cx j fr R R0 m m' A csp HA E9 E22 E24 E25 H0 H1 H2 KS (H184 & H22 & H24 & H272 & H25).
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - exact (w4f_bcmp_sp R R0 m m' A csp 184 _ HA E9 H0 H1 H2 KS ltac:(lia) H184).
  - exact (w4f_rgv_tr R R0 22 _ E22 H22).
  - exact (w4f_rgv_tr R R0 24 _ E24 H24).
  - exact (w4f_bcmp_sp R R0 m m' A csp 272 _ HA E9 H0 H1 H2 KS ltac:(lia) H272).
  - exact (w4f_rgv_tr R R0 25 _ E25 H25).
Qed.

Lemma w4f_bcmp_FTURN : forall cx j phi R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> 0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 ->
  MKEPT m m' A csp -> MKEPT m m' phi (phi + ACtlCutP.flen cx j) ->
  ACtlCutP.FTURN cx j phi R0 m -> ACtlCutP.FTURN cx j phi R m'.
Proof.
  intros cx j phi R R0 m m' A csp HA E9 H0 H1 H2 KS KB (H224 & H232 & Hphi & Hlen).
  unfold ACtlCutP.flen in KB.
  refine (conj _ (conj _ (conj _ Hlen))).
  - exact (w4f_bcmp_sp R R0 m m' A csp 224 _ HA E9 H0 H1 H2 KS ltac:(lia) H224).
  - exact (w4f_bcmp_sp R R0 m m' A csp 232 _ HA E9 H0 H1 H2 KS ltac:(lia) H232).
  - apply (w4f_bcmp_bytes m m' phi _); [intros x Hx; apply KB; lia | exact Hphi].
Qed.

Lemma w4f_bcmp_PT32 : forall cx j phi fr R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> getr R 18 = getr R0 18 -> getr R 20 = getr R0 20 ->
  getr R 24 = getr R0 24 -> 0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 -> MKEPT m m' A csp ->
  MKEPT m m' phi (phi + ACtlCutP.flen cx j) ->
  (forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b) ->
  ACtlCutP.PT32 cx j phi fr R0 m -> ACtlCutP.PT32 cx j phi fr R m'.
Proof.
  intros cx j phi fr R R0 m m' A csp HA E9 E18 E20 E24 H0 H1 H2 KS KB Hpr
    (H18 & H24 & H20 & S152 & S312 & Hphi & Hlen & S160 & Hstk).
  refine (conj (w4f_rgv_tr R R0 18 _ E18 H18) (conj (w4f_rgv_tr R R0 24 _ E24 H24)
    (conj (w4f_rgv_tr R R0 20 _ E20 H20)
    (conj (w4f_bcmp_sp R R0 m m' A csp 152 _ HA E9 H0 H1 H2 KS ltac:(lia) S152)
    (conj (w4f_bcmp_sp R R0 m m' A csp 312 _ HA E9 H0 H1 H2 KS ltac:(lia) S312)
    (conj _ (conj Hlen (conj (w4f_bcmp_sp R R0 m m' A csp 160 _ HA E9 H0 H1 H2 KS ltac:(lia) S160)
      (w4f_bcmp_stk m m' fr _ Hpr Hstk))))))))).
  apply (w4f_bcmp_bytes m m' phi _); [intros x Hx; apply KB; lia | exact Hphi].
Qed.

Lemma w4f_bcmp_PTL : forall cx j phi fr R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> getr R 18 = getr R0 18 -> getr R 20 = getr R0 20 ->
  0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 -> MKEPT m m' A csp ->
  MKEPT m m' phi (phi + ACtlCutP.flen cx j) -> MKEPT m m' fr (fr + 4096) ->
  (forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b) ->
  ACtlCutP.PTL cx j phi fr R0 m -> ACtlCutP.PTL cx j phi fr R m'.
Proof.
  intros cx j phi fr R R0 m m' A csp HA E9 E18 E20 H0 H1 H2 KS KB KF Hpr
    (Hsel & H18 & H20 & S152 & S312 & Hphi & Hlen & S160 & Q32 & Hstk).
  refine (conj Hsel (conj (w4f_rgv_tr R R0 18 _ E18 H18) (conj (w4f_rgv_tr R R0 20 _ E20 H20)
    (conj (w4f_bcmp_sp R R0 m m' A csp 152 _ HA E9 H0 H1 H2 KS ltac:(lia) S152)
    (conj (w4f_bcmp_sp R R0 m m' A csp 312 _ HA E9 H0 H1 H2 KS ltac:(lia) S312)
    (conj _ (conj Hlen (conj (w4f_bcmp_sp R R0 m m' A csp 160 _ HA E9 H0 H1 H2 KS ltac:(lia) S160)
    (conj _ (w4f_bcmp_stk m m' fr _ Hpr Hstk)))))))))).
  - apply (w4f_bcmp_bytes m m' phi _); [intros x Hx; apply KB; lia | exact Hphi].
  - apply (w4f_bcmp_q64 m m' (fr + 32) 11); [intros x Hx; apply KF; lia | exact Q32].
Qed.

Lemma w4f_bcmp_RLc : forall cx j i phi fr R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> getr R 18 = getr R0 18 -> getr R 20 = getr R0 20 ->
  getr R 21 = getr R0 21 -> getr R 22 = getr R0 22 -> getr R 23 = getr R0 23 -> getr R 24 = getr R0 24 ->
  getr R 25 = getr R0 25 ->
  0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 -> MKEPT m m' A csp ->
  MKEPT m m' phi (phi + ACtlCutP.flen cx j) -> MKEPT m m' fr (fr + 4096) ->
  (forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b) ->
  ACtlCutP.RLc cx j i phi fr R0 m -> ACtlCutP.RLc cx j i phi fr R m'.
Proof.
  intros cx j i phi fr R R0 m m' A csp HA E9 E18 E20 E21 E22 E23 E24 E25 H0 H1 H2 KS KB KF Hpr
    (Hi & H23 & H24 & H25 & H21 & H22 & Hprev & HPTL).
  exact (conj Hi (conj (w4f_rgv_tr R R0 23 _ E23 H23) (conj (w4f_rgv_tr R R0 24 _ E24 H24)
    (conj (w4f_rgv_tr R R0 25 _ E25 H25) (conj (w4f_rgv_tr R R0 21 _ E21 H21) (conj (w4f_rgv_tr R R0 22 _ E22 H22)
    (conj Hprev (w4f_bcmp_PTL cx j phi fr R R0 m m' A csp HA E9 E18 E20 H0 H1 H2 KS KB KF Hpr HPTL)))))))).
Qed.

Lemma w4f_bcmp_IFS : forall cx fr j R R0 (m m' : word -> option byte),
  MKEPT m m' fr (fr + 4096) -> MKEPT m m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 512) ->
  ACtlCutP.IFS cx fr j R0 m -> ACtlCutP.IFS cx fr j R m'.
Proof.
  intros cx fr j R R0 m m' KF KSH ((HID & Hidok) & (HFG & Hfgok) & (Hhave & Hnb & Hbody & Had & HFI)).
  pose proof (B.Prog.Seg.Tac_ro.tr_ID_length (ACtlCut.c_in cx) j) as LID.
  pose proof (B.Prog.Seg.Tac_ro.tr_FG_length (ACtlCut.c_in cx) j) as LFG.
  pose proof (B.Prog.Seg.Tac_ro.tr_body_length (ACtlCut.c_in cx) j) as LBD.
  unfold ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.IDb, ACtlCutP.IDBe, ACtlCutP.FGj, ACtlCutP.FGb, ACtlCutP.FGBe,
    ACtlCutP.FSj, ACtlCutP.FSb in *.
  refine (conj (conj _ Hidok) (conj (conj _ Hfgok) (conj _ (conj _ (conj _ (conj _ HFI)))))).
  - apply (w4f_bcmp_bytes m m' _ _); [intros x Hx; apply KF; lia | exact HID].
  - apply (w4f_bcmp_bytes m m' _ _); [intros x Hx; apply KF; lia | exact HFG].
  - apply (w4f_bcmp_u32 m m' _ _); [intros x Hx; apply KF; lia | exact Hhave].
  - apply (w4f_bcmp_b8 m m' _ _); [intros x Hx; apply KF; lia | exact Hnb].
  - apply (w4f_bcmp_bytes m m' _ _); [intros x Hx; apply KF; lia | exact Hbody].
  - apply (w4f_bcmp_addr m m' _ _); [| exact Had]. intros i Hi. apply KSH.
    unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Lemma w4f_bcmp_FLI : forall cx fr R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> getr R 27 = getr R0 27 ->
  0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 -> MKEPT m m' A csp ->
  MKEPT m m' fr (fr + 4096) -> MKEPT m m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 512) ->
  MKEPT m m' ACtlCutP.KNA.KIND_NAME (ACtlCutP.KNA.KIND_NAME + 112) ->
  B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112 ->
  (forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b) ->
  ACtlCutP.FLI cx fr R0 m -> ACtlCutP.FLI cx fr R m'.
Proof.
  intros cx fr R R0 m m' A csp HA E9 E27 H0 H1 H2 KS KF KSH KK HKA Hpr HFLI.
  assert (SP : forall off v, 0 <= off <= 440 -> ACtlCutP.spill R0 m off v -> ACtlCutP.spill R m' off v)
    by (intros off v Ho Hs; exact (w4f_bcmp_sp R R0 m m' A csp off v HA E9 H0 H1 H2 KS Ho Hs)).
  assert (AD : forall p n, fr <= p -> p + n <= fr + 4000 -> 0 <= n ->
                 B.AsanRT.addressable m p n -> B.AsanRT.addressable m' p n).
  { intros p n Hp1 Hp2 Hn Hp. apply (w4f_bcmp_addr m m' p n); [| exact Hp].
    intros i Hi. apply KSH. unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr. Z.div_mod_to_equations. lia. }
  assert (LKN : length ACtlCutP.KNA.kind_name_bytes = 112%nat) by (vm_compute; reflexivity).
  unfold ACtlCutP.FLI in *.
  destruct HFLI as (H27 & HFLI).
  split; [exact (w4f_rgv_tr R R0 27 _ E27 H27) |].
  do 21 (destruct HFLI as (Hsp & HFLI); split; [apply SP; [lia | exact Hsp] | clear Hsp]).
  destruct HFLI as (Had & Hstk & HRAD & HKNT & Hs168 & Hs88).
  split; [apply AD; [lia | lia | lia | exact Had] |].
  split; [exact (w4f_bcmp_stk m m' fr _ Hpr Hstk) |].
  split.
  { unfold ACtlCutP.RAD, ACtlCutP.fragb in *. destruct HRAD as (Ra1 & Ra2 & Ra3).
    split; [apply AD; [lia | lia | lia | exact Ra1] |].
    split; [apply AD; [lia | lia | lia | exact Ra2] |].
    apply AD; [lia | lia | lia | exact Ra3]. }
  split.
  { unfold ACtlCutP.KNT in *. destruct HKNT as (Hkb & _). split; [| exact HKA].
    apply (w4f_bcmp_bytes m m' _ _); [intros x Hx; apply KK; rewrite LKN in Hx; lia | exact Hkb]. }
  split; [apply SP; [lia | exact Hs168] | apply SP; [lia | exact Hs88]].
Qed.

Lemma w4f_bcmp_LK : forall cx fr j R R0 (m m' : word -> option byte) A csp,
  ACtlCut.rgv R0 9 A -> getr R 9 = getr R0 9 -> getr R 27 = getr R0 27 ->
  0 <= A -> A + 448 <= csp -> csp <= 2 ^ 63 -> MKEPT m m' A csp ->
  MKEPT m m' fr (fr + 4096) -> MKEPT m m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 512) ->
  MKEPT m m' ACtlCutP.KNA.KIND_NAME (ACtlCutP.KNA.KIND_NAME + 112) ->
  B.AsanRT.addressable m' ACtlCutP.KNA.KIND_NAME 112 ->
  (forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, m' (Z_to_bv 64 a) = Some b) ->
  ACtlCutP.LK cx fr j R0 m -> ACtlCutP.LK cx fr j R m'.
Proof.
  intros cx fr j R R0 m m' A csp HA E9 E27 H0 H1 H2 KS KF KSH KK HKA Hpr (Hj & S240 & HOUR & HFLI).
  refine (conj Hj (conj (w4f_bcmp_sp R R0 m m' A csp 240 _ HA E9 H0 H1 H2 KS ltac:(lia) S240) (conj _ _))).
  - unfold ACtlCutP.OURb in *. apply (w4f_bcmp_bytes m m' _ _); [| exact HOUR].
    rewrite ACtlCutP.SM.OUR_length. intros x Hx. apply KF. lia.
  - exact (w4f_bcmp_FLI cx fr R R0 m m' A csp HA E9 E27 H0 H1 H2 KS KF KSH KK HKA Hpr HFLI).
Qed.

(* ---- helpers of seg_F30 (a Theorem Labs lane) ---- *)

(* w4f_run with the growth of the visible memory, ajournal_exec's premise for a run that writes. *)
Lemma w4f_f30_run : forall (W : Reusable.YA0n.world segs) ms md RNG (P : machine_state -> Prop) Q,
  lib.Lib.ExecF.evtF B.Img0.rsegs RNG P ms ->
  Reusable.YK04R.fp_avoids (Reusable.YA0n.w_H W) RNG ->
  (forall ms' md', P ms' -> Reusable.YK04.same_but_materialized md md' ->
     (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem ms' x = ms_mem ms x) ->
     lib.Reusable.YK1b.mem_grows (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) (ms_mem ms))
       (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) (ms_mem ms')) ->
     Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (mkCfg ms md) Q.
Proof.
  intros W ms md RNG P Q Hrun Hav K.
  destruct (B.ProgBridge.fevt_of_evtF RNG P ms Hrun) as (ms' & Hf & HP).
  apply (Reusable.YA0nR.SRr_fsteps segs Hwx W ms ms' md RNG Q Hf Hav).
  intros md' Hs. apply (K ms' md' HP Hs).
  - exact (Reusable.YA0nR.fsteps_keeps_hidden segs Hwx (Reusable.YA0n.w_H W) RNG ms ms' (Reusable.YA0n.w_Hoff W) Hf Hav).
  - destruct (Reusable.YK04R.fsteps_restrict segs (Reusable.YA0n.w_H W) (Reusable.YA0n.w_Hoff W) Hwx RNG ms ms' Hf Hav)
      as [Hms _].
    exact (lib.Reusable.YI04.msteps_mem_grows segs _ _ Hms).
Qed.

(* The owned class-6 frame [fr, fr + 4096), its shadow [S(fr), S(fr) + 512) and the present stack window are
   awr_byte bytes of the journal (in_frames, awr_byte's fourth case; the window, its first case). *)
Lemma w4f_f30_awr : forall cx ly3 S3 W3 mem3 md3 k fr a,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  (fr <= a < fr + 4096 \/ ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 \/
   ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= a < ACtlCut.c_sp cx) ->
  Reusable.YCbq.awr_byte Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
    (ACtlCut.own6 cx) a.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 Ha.
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  destruct Ha as [Ha | [Ha | Ha]].
  - right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
    left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
    change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
  - right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
    right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
    change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
    unfold ACtlCutP.Sfr, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *.
    lia.
  - left. exact Ha.
Qed.

(* The owned frame lies above the image and in the low or the high application range. *)
Lemma w4f_f30_frame_geo : forall cx ly3 S3 W3 mem3 md3 k fr,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  6332416 <= fr /\ fr + 4096 <= lib.Reusable.YM05.alloc_ceiling /\
  (fr + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= fr).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1.
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  pose proof HJ as (HAR & _).
  pose proof (Reusable.YG01.wfs_live _ (Reusable.YG01.wf_fakestack _ _ _ _ _
    (Reusable.YG0n.am_wf _ _ _ _ (proj1 HAR)))) as Hlive.
  change (Reusable.YG00.fs_live (Reusable.YG00.st_fs S3)) with (Reusable.YG01.frames S3) in Hlive.
  rewrite HF in Hlive. unfold ACtlCut.own6 in Hlive. apply Forall_inv in Hlive. cbn [fst snd] in Hlive.
  pose proof (Reusable.YG0f.lo_app _ (Reusable.YG0n.am_layout _ _ _ _ (proj1 HAR))) as Happ.
  pose proof (proj1 (Forall_forall _ _) Happ (Reusable.YG0f.ly_F ly3, Reusable.YG0f.kFakeStackSize)
    ltac:(unfold Reusable.YG0f.owned_extents; cbn [In]; tauto)) as HFa.
  cbn [fst snd] in HFa. destruct HFa as (HF4096 & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (_ & H2 & H3).
  rewrite <- Efr in H2, H3. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in H2, H3.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in H3.
  split; [|split; [exact H2 | lia]].
  rewrite Efr. unfold Reusable.YG0f.frame_addr, Reusable.YG0f.fs_frame_off, Reusable.YG0f.kFakeFramesOff.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096. change (Reusable.YG00.fs_frames 6) with 256 in Hlive.
  change (Z.shiftl 1 Reusable.YG00.kStackSizeLog) with 1048576. lia.
Qed.

(* A live block of the journal: bounds, the application range, apart from the owned frame, visible. *)
Lemma w4f_f30_blk : forall cx ly3 S3 W3 mem3 md3 k fr p n,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k -> Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  In (p, n) (Reusable.YG0d.ablocks B ly3 S3) ->
  4096 <= p /\ p + Reusable.YG00.req_size n <= lib.Reusable.YM05.alloc_ceiling /\
  (p + Reusable.YG00.req_size n <= 0x7fff7000 \/ 0x10007fff8000 <= p) /\
  (p + Reusable.YG00.req_size n <= fr \/ fr + 4096 <= p) /\
  (forall a, p <= a < p + Reusable.YG00.req_size n -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr p n HJ HF HG1 Hin.
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  pose proof HJ as (HAR & _).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR Hin) as (_ & H4 & Hc & Happ & Hpres & _).
  assert (Hinf : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 p n 6 (ACtlCut.c_fpos cx) HAR Hin Hinf)
    as Hd.
  unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. rewrite <- Efr in Hd.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hd.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ.
  split; [lia |]. split; [exact Hc |]. split; [lia |]. split; [lia |].
  intros a Ha. exact (proj1 (proj1 (Hpres a Ha))).
Qed.

(* A byte the core's view reads in a world is visible there (a hidden byte reads None: H_off_segments). *)
Lemma w4f_f30_vis : forall (W : Reusable.YA0n.world segs) mem a v,
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a = Some v -> Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v Hv. destruct (Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict in Hv. rewrite E in Hv.
  unfold lib.Reusable.YK11.seg_rom, memory_read in Hv. change (Z.of_N 1) with 1 in Hv.
  rewrite (Reusable.YA0n.w_Hoff W _ E) in Hv. discriminate Hv.
Qed.

(* The bytes and the shadow bytes of the owned frame are present (AR_frames_law). *)
Lemma w4f_f30_fpres : forall cx ly3 S3 W3 mem3 md3 k fr a,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k -> Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  (fr <= a < fr + 4096 \/ ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512) ->
  Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr a HJ HF HG1 Ha.
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  pose proof HJ as (HAR & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (_ & _ & Hb & Hs).
  rewrite <- Efr in Hb, Hs. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hb.
  change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512 in Hs.
  destruct Ha as [Ha | Ha].
  - exact (proj1 (Hb a Ha)).
  - assert (E : Reusable.YG0f.shadow_addr fr = ACtlCutP.Sfr fr)
      by (unfold ACtlCutP.Sfr, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr,
            B.AsanRT.ASAN_K; lia).
    destruct (Hs (a - ACtlCutP.Sfr fr) ltac:(lia)) as (Hp & _). rewrite E in Hp.
    replace (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) with a in Hp by lia. exact Hp.
Qed.

(* A view kept across a world step, at a byte visible before it, is a kept raw read (aview_vis_mrd). *)
Lemma w4f_f30_mrd_eq : forall (W W2 : Reusable.YA0n.world segs) (m m2 : word -> option byte) a,
  Reusable.YA0n.wle W W2 -> Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W2) m2 a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m a ->
  lib.Lib.Mem.mrd B.Img0.rsegs m2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa a).
Proof.
  intros W W2 m m2 a Hle Hv E.
  assert (Hv2 : Reusable.YA0n.w_H W2 (Z_to_bv 64 a) = false).
  { destruct (Reusable.YA0n.w_H W2 (Z_to_bv 64 a)) eqn:E2; [|reflexivity]. rewrite (Hle _ E2) in Hv. discriminate. }
  rewrite (aview_vis_mrd W2 m2 a Hv2), (aview_vis_mrd W m a Hv) in E. unfold lib.Lib.Mem.wa.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs m2 (Z_to_bv 64 a)) as [b2|],
    (lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a)) as [b|]; cbn [option_map] in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma w4f_f30_aview_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  Reusable.YG0n.aview segs H m' a = Reusable.YG0n.aview segs H m a.
Proof.
  intros H m m' a E. unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict. rewrite E.
  reflexivity.
Qed.

(* Transport of the readers by kept raw reads. *)
Lemma w4f_f30_bytes : forall m m' a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa x)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) K. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (K (a + Z.of_nat i)) by lia. exact (H i Hi).
Qed.

Lemma w4f_f30_addr : forall m m' p n, B.AsanRT.addressable m p n ->
  (forall x, p <= x < p + n ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x)) =
     lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x))) ->
  B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n (H0 & H1 & H2 & H) K. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. split; [|exact Hok].
  rewrite (K (p + i)) by lia. exact Hb.
Qed.

Lemma w4f_f30_addr_sub : forall m p n p' n', B.AsanRT.addressable m p n ->
  p <= p' -> 0 <= n' -> p' + n' <= p + n -> B.AsanRT.addressable m p' n'.
Proof.
  intros m p n p' n' (H0 & H1 & H2 & H) Hp Hn Hpn. split; [lia|]. split; [exact Hn|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply H. lia.
Qed.

Lemma w4f_f30_spill : forall R R' m m' off v A,
  ACtlCutP.spill R m off v -> ACtlCut.rgv R 9 A -> getr R' 9 = getr R 9 -> 0 <= A < 2 ^ 63 -> 0 <= off < 2 ^ 62 ->
  (forall x, A + off <= x < A + off + 8 ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa x)) ->
  ACtlCutP.spill R' m' off v.
Proof.
  intros R R' m m' off v A Hs HA E9 HAb Hoff K. exists A.
  split; [unfold ACtlCut.rgv in *; rewrite E9; exact HA|].
  pose proof (w4f_spill R m off v A Hs HA HAb Hoff) as Hq. unfold ACtlCutP.q64 in *.
  apply (w4f_f30_bytes m m' _ _ Hq). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply K. lia.
Qed.

(* A byte of small signed value has that unsigned value. *)
Lemma w4f_f30_byte_sgn : forall b : byte, 0 <= bv_signed b \/ bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  assert (E1 : bv_modulus 8 = 256) by reflexivity. assert (E2 : bv_half_modulus 8 = 128) by reflexivity.
  unfold bv_signed, bv_swrap, bv_wrap in *. rewrite E1, E2 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma w4f_f30_sh_eq : forall x, Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x = B.AsanRT.shadow_addr x.
Proof.
  intros x. unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. lia.
Qed.

(* ART.addressable (mrd vocabulary) to the core's range_addressable over the view, and back. *)
Lemma w4f_f30_range_of_addr : forall (W : Reusable.YA0n.world segs) m p n,
  B.AsanRT.addressable m p n ->
  (forall x, p <= x < p + n -> Reusable.YA0n.w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr x)) = false) ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) Reusable.YG0f.SHADOW_OFF p n.
Proof.
  intros W m p n (H0 & H1 & H2 & H) Hv x Hx.
  destruct (H (x - p) ltac:(lia)) as (_ & b & Hb & Hok). replace (p + (x - p)) with x in Hb, Hok by lia.
  rewrite w4f_f30_sh_eq, (aview_vis_mrd W m _ (Hv x Hx)). unfold lib.Lib.Mem.wa in Hb. rewrite Hb.
  exists (bv_unsigned b). split; [reflexivity|].
  unfold Reusable.YG0v.saddr_ok. unfold B.AsanRT.shadow_ok in Hok.
  rewrite (w4f_f30_byte_sgn b) in Hok by lia. lia.
Qed.

Lemma w4f_f30_addr_of_range : forall (W : Reusable.YA0n.world segs) m p n,
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) Reusable.YG0f.SHADOW_OFF p n ->
  0 <= p -> 0 <= n -> p + n <= B.AsanRT.APPMEM_END -> (forall x, p <= x < p + n -> B.AsanRT.app_mem x) ->
  B.AsanRT.addressable m p n.
Proof.
  intros W m p n Hr H0 H1 H2 Happ. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. split; [apply Happ; lia|].
  destruct (Hr (p + i) ltac:(lia)) as (s & Hs & Hok). rewrite w4f_f30_sh_eq in Hs.
  pose proof (w4f_f30_vis W m _ _ Hs) as Hv. rewrite (aview_vis_mrd W m _ Hv) in Hs.
  unfold lib.Lib.Mem.wa.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (B.AsanRT.shadow_addr (p + i)))) as [b|] eqn:Eb;
    [|discriminate]. cbn [option_map] in Hs. injection Hs as Hs.
  exists b. split; [reflexivity|].
  unfold Reusable.YG0v.saddr_ok in Hok. unfold B.AsanRT.shadow_ok.
  rewrite (w4f_f30_byte_sgn b) by lia. lia.
Qed.

(* The shadow byte of an address of a frame based at fr (fr mod 8 = 0). *)
Lemma w4f_f30_sh_in : forall fr x, fr mod 8 = 0 -> B.AsanRT.shadow_addr x = ACtlCutP.Sfr fr + (x - fr) / 8.
Proof. intros fr x H. unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma w4f_f30_sh_in' : forall fr q x, fr = 8 * q -> B.AsanRT.shadow_addr x = ACtlCutP.Sfr fr + (x - fr) / 8.
Proof. intros fr q x H. apply w4f_f30_sh_in. subst fr. rewrite Z.mul_comm. apply Z_mod_mult. Qed.

Lemma w4f_f30_mod8 : forall q d, d mod 8 = 0 -> (8 * q + d) mod 8 = 0.
Proof. intros q d H. rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full. exact H. Qed.

(* Image addresses (B.ProgBridge.rsegs_spans). *)
Lemma w4f_f30_img_bounds : forall a, Reusable.YG0d.in_img segs a -> 0x10000 <= a < 0x5fe000.
Proof.
  intros a (sg & Hin & H1).
  apply (in_map (fun s0 : Segment => (Z.of_N (seg_base s0), Z.of_N (seg_size s0)))) in Hin.
  rewrite B.ProgBridge.tfibsegs_rsegs, B.ProgBridge.rsegs_spans in Hin. cbn [In] in Hin.
  destruct Hin as [E1 | [E1 | [E1 | [E1 | []]]]]; injection E1 as E1 E2; lia.
Qed.

Lemma w4f_f30_kn_img : forall a, 0x9f000 <= a < 0xa2000 -> Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha.
  assert (Hm : In (651264, 12288) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) B.Img0.rsegs))
    by (rewrite B.ProgBridge.rsegs_spans; cbn [In]; tauto).
  apply in_map_iff in Hm as (sg & Esg & Hsg). exists sg. split; [exact Hsg|].
  injection Esg as E1 E2. rewrite E1, E2. lia.
Qed.

(* Bytes that read Some form a bytes_at list. *)
Lemma w4f_f30_bytes_ex : forall m a (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa (a + Z.of_nat i)) = Some b) ->
  exists bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs /\ length bs = n.
Proof.
  intros m a n H0 H1 H.
  exists (map (fun i => match lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa (a + Z.of_nat i)) with
                        | Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
  rewrite length_map, length_seq. split; [|reflexivity].
  split; [exact H0|]. split; [rewrite length_map, length_seq; exact H1|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite nth_error_map, (nth_error_nth' (seq 0 n) 0%nat) by (rewrite length_seq; exact Hi).
  rewrite seq_nth by exact Hi. cbn [option_map Nat.add].
  destruct (H i Hi) as (b & Hb). rewrite Hb. reflexivity.
Qed.

Lemma w4f_f30_rw1 : forall (H : word -> bool) m a, 0 <= a < 2 ^ 64 -> Reusable.YG0n.apresent H m a ->
  exists c, lib.Lib.Step.rw_cells B.Img0.rsegs m a [lib.Lib.Cells.C1 c].
Proof.
  intros H m a Ha (_ & b & Hb). exists b.
  unfold lib.Lib.Step.rw_cells, lib.Lib.Cells.cells_at. cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf
    lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes lib.Lib.Cells.cells_size lib.Lib.Cells.csize app Nat.add].
  split; [split; [tauto |] |].
  - split; [lia |]. split; [cbn [length]; lia |]. intros i Hi. cbn [length] in Hi.
    destruct i as [|i]; [| lia]. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
    unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity.
  - split; [lia |]. split; [cbn; lia |]. intros i Hi. replace (a + i) with a by (cbn in Hi; lia).
    unfold wview, lib.Lib.Mem.wa. rewrite Hb. discriminate.
Qed.

Lemma w4f_f30_rwn : forall (H : word -> bool) m a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> Reusable.YG0n.apresent H m (a + i)) ->
  exists bs, lib.Lib.Step.rw_cells B.Img0.rsegs m a [lib.Lib.Cells.CB n bs] /\ length bs = n.
Proof.
  intros H m a n H0 H1 Hp.
  destruct (w4f_f30_bytes_ex m a n H0 H1) as (bs & Hbs & Hl).
  { intros i Hi. destruct (Hp (Z.of_nat i) ltac:(lia)) as (_ & b & Hb). exists b.
    unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity. }
  exists bs. split; [| exact Hl].
  unfold lib.Lib.Step.rw_cells, lib.Lib.Cells.cells_at. cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf
    lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes lib.Lib.Cells.cells_size lib.Lib.Cells.csize].
  rewrite app_nil_r, Nat.add_0_r.
  split; [split; [split; [exact Hl | exact I] | exact Hbs] |].
  split; [lia |]. split; [lia |]. intros i Hi. destruct (Hp i Hi) as (_ & b & Hb).
  unfold wview, lib.Lib.Mem.wa. rewrite Hb. discriminate.
Qed.

Lemma w4f_f30_ro8 : forall m a v, ACtlCutP.q64 m a v ->
  lib.Lib.Step.ro_cells B.Img0.rsegs m a [lib.Lib.Cells.C8 (Z_to_bv 64 v)].
Proof.
  intros m a v H. unfold lib.Lib.Step.ro_cells, lib.Lib.Cells.cells_at.
  cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes].
  rewrite app_nil_r. split; [tauto | exact H].
Qed.

Lemma w4f_f30_mbyte_mrd : forall (H : word -> bool) m a, H (Z_to_bv 64 a) = false ->
  lib.Reusable.YP09.mbyte segs (Reusable.YK04.mrestrict H m) a = lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa a).
Proof.
  intros H m a Hv. unfold lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict, lib.Lib.Mem.mrd, lib.Lib.Mem.wa.
  rewrite Hv. reflexivity.
Qed.

(* The classify event word (0 .. 5) in the view, as ctrl's u32. *)
Lemma w4f_f30_u32 : forall (H : word -> bool) m a e, 0 <= e <= 5 -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  (forall k, (k < 4)%nat -> H (Z_to_bv 64 (a + Z.of_nat k)) = false) ->
  lib.Reusable.YI04.val_mem segs (Reusable.YK04.mrestrict H m) a 4 e ->
  ACtlCutP.u32 m a e.
Proof.
  intros H m a e He H0 H1 Hv Hval.
  unfold ACtlCutP.u32. split; [exact H0|]. split; [rewrite lib.Lib.Mem.length_le4; lia|].
  intros i Hi. rewrite lib.Lib.Mem.length_le4 in Hi.
  pose proof (Hval i Hi) as E. rewrite (w4f_f30_mbyte_mrd H m _ (Hv i Hi)) in E. refine (eq_trans E _).
  assert (Ee : e = 0 \/ e = 1 \/ e = 2 \/ e = 3 \/ e = 4 \/ e = 5) by lia.
  destruct i as [|[|[|[|i]]]]; [| | | | lia];
    destruct Ee as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity.
Qed.

(* bytes_at in the view at visible bytes. *)
Lemma w4f_f30_aview_bytes : forall (W : Reusable.YA0n.world segs) m a bs i,
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> (i < length bs)%nat ->
  Reusable.YA0n.w_H W (Z_to_bv 64 (a + Z.of_nat i)) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + Z.of_nat i) = Some (RPS.cp_v bs i).
Proof.
  intros W m a bs i (_ & _ & Hb) Hi Hv. rewrite (aview_vis_mrd W m _ Hv).
  pose proof (Hb i Hi) as E. unfold lib.Lib.Mem.wa in E. rewrite E.
  unfold RPS.cp_v, RPS.cp_b. rewrite (nth_error_nth' bs RPS.cp_z Hi). reflexivity.
Qed.

Lemma w4f_f30_bytes_of_aview : forall (W : Reusable.YA0n.world segs) m a bs,
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat ->
     Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + Z.of_nat i) = Some (bv_unsigned (nth i bs RPS.cp_z))) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs.
Proof.
  intros W m a bs H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (H i Hi) as E. pose proof (w4f_f30_vis W m _ _ E) as Hv.
  rewrite (aview_vis_mrd W m _ Hv) in E.
  rewrite (nth_error_nth' bs RPS.cp_z Hi). unfold lib.Lib.Mem.wa.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [|discriminate].
  cbn [option_map] in E. injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A range of present bytes is a stk range. *)
Lemma w4f_f30_stk : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> Reusable.YG0n.apresent H m a) -> lib.Lib.Frame.stk B.Img0.rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as (_ & b & Hb). unfold lib.Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

(* FRAC's memory facts move where the raw reads of their bytes are kept; the frame's shadow bytes are given anew. *)
Lemma w4f_f30_FRAC_mem : forall cx fr sel R m m' A0,
  ACtlCutP.FRAC B cx fr sel R m -> ACtlCut.rgv R 9 A0 -> 0 <= A0 < 2 ^ 64 ->
  (forall x, A0 + 40 <= x < A0 + 56 \/ A0 + 336 <= x < A0 + 344 \/ fr <= x < fr + 24 \/
     fr + 4088 <= x < fr + 4096 \/ ACtlCut.c_sp cx - 104 <= x < ACtlCut.c_sp cx ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa x)) ->
  (exists sh, lib.Lib.Mem.bytes_at segs m' (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) ->
  ACtlCutP.FRAC B cx fr sel R m'.
Proof.
  intros cx fr sel R m m' A0 HF HA0 HA0b K Hsh.
  destruct HF as (A & sp & E2 & Hm & Hsp & E4 & E8 & E9 & E3 & E19 & E26 & Hf32 & HA32 & HAle & HspA & HfrA & HA448 &
    Hsp4096 & HspEnd & Q336 & Q48 & Q40 & Qhdr & Q16 & _ & Hsv & Qflag).
  assert (EA : A = A0).
  { unfold ACtlCut.rgv in E9, HA0. rewrite E9 in HA0. apply (f_equal bv_unsigned) in HA0.
    pose proof (bv_unsigned_in_range 64 (getr R 2)) as R2.
    pose proof (bv_unsigned_in_range 64 (getr (ACtlCut.c_regs cx) 2)) as Rc.
    unfold bv_modulus in R2, Rc. cbn [Z.of_N] in R2, Rc. unfold Reusable.YG0d.spZ in Hsp.
    unfold ACtlCut.c_sp, Reusable.YG0d.spZ in HAle, HA448.
    rewrite !lib.Lib.MState.unsigned_lit in HA0 by lia. exact HA0. }
  subst A0.
  exists A, sp. unfold ACtlCutP.q64 in *.
  refine (conj E2 (conj Hm (conj Hsp (conj E4 (conj E8 (conj E9 (conj E3 (conj E19 (conj E26 (conj Hf32 (conj HA32
    (conj HAle (conj HspA (conj HfrA (conj HA448 (conj Hsp4096 (conj HspEnd (conj _ (conj _ (conj _ (conj _ (conj _
    (conj Hsh (conj _ _)))))))))))))))))))))))).
  - apply (w4f_f30_bytes m m' _ _ Q336). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply K. lia.
  - apply (w4f_f30_bytes m m' _ _ Q48). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply K. lia.
  - apply (w4f_f30_bytes m m' _ _ Q40). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply K. lia.
  - apply (w4f_f30_bytes m m' _ _ Qhdr). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply K. lia.
  - apply (w4f_f30_bytes m m' _ _ Q16). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply K. lia.
  - apply (w4f_f30_bytes m m' _ _ Hsv).
    assert (L : length (ACtlCutP.saved_bytes cx) = 104%nat)
      by (unfold ACtlCutP.saved_bytes; rewrite !length_app, !lib.Lib.Mem.length_le8; reflexivity).
    rewrite L. intros x Hx. apply K. lia.
  - apply (w4f_f30_bytes m m' _ _ Qflag). rewrite lib.Lib.Mem.length_le8. intros x Hx. apply K. lia.
Qed.

(* LK moves (with the registers) when its spills, OURb, its addressable frame ranges (at fr + 2600 or above), the
   frame's stk fact and KNT move. *)
Lemma w4f_f30_LK_mem : forall cx fr j R R' m m',
  ACtlCutP.LK cx fr j R m -> getr R' 27 = getr R 27 ->
  (forall off v, ACtlCutP.spill R m off v -> 0 <= off <= 440 -> ACtlCutP.spill R' m' off v) ->
  ACtlCutP.OURb cx fr m' ->
  (forall p n, B.AsanRT.addressable m p n -> fr + 2600 <= p -> p + n <= fr + 3136 -> B.AsanRT.addressable m' p n) ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.KNT m' ->
  ACtlCutP.LK cx fr j R' m'.
Proof.
  intros cx fr j R R' m m' (Hj & S240 & HOUR0 & HFLI) E27 Hsp HOUR Had Hstk HKNT.
  unfold ACtlCutP.FLI, ACtlCutP.RAD in HFLI.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  unfold ACtlCutP.LK, ACtlCutP.FLI, ACtlCutP.RAD.
  repeat match goal with |- _ /\ _ => split end.
  all: first [ assumption
             | (unfold ACtlCut.rgv in *; rewrite E27; assumption)
             | (apply Hsp; [assumption | lia])
             | (apply Had; [assumption | unfold ACtlCutP.fragb; lia | unfold ACtlCutP.fragb; lia]) ].
Qed.

(* IFS moves where the two frame records and `first` [fr + 2688, fr + 2920) are kept and `first` stays addressable. *)
Lemma w4f_f30_IFS_mem : forall cx fr j R m m',
  ACtlCutP.IFS cx fr j R m ->
  (forall x, fr + 2688 <= x < fr + 2920 ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa x)) ->
  (B.AsanRT.addressable m (fr + 2880) 40 -> B.AsanRT.addressable m' (fr + 2880) 40) ->
  ACtlCutP.IFS cx fr j R m'.
Proof.
  intros cx fr j R m m' ((Hid & Hidok) & (Hfg & Hfgok) & (Hh & Hn & Hb & Had & HFI)) K Hadk.
  unfold ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.IDb, ACtlCutP.IDBe, ACtlCutP.FGj, ACtlCutP.FGb, ACtlCutP.FGBe,
    ACtlCutP.FSj, ACtlCutP.FSb, ACtlCutP.u32, ACtlCutP.b8 in *.
  pose proof (B.Prog.Seg.Tac_ro.tr_ID_length (ACtlCut.c_in cx) j) as LID.
  pose proof (B.Prog.Seg.Tac_ro.tr_FG_length (ACtlCut.c_in cx) j) as LFG.
  pose proof (B.Prog.Seg.Tac_ro.tr_body_length (ACtlCut.c_in cx) j) as LB.
  refine (conj (conj _ Hidok) (conj (conj _ Hfgok) (conj _ (conj _ (conj _ (conj (Hadk Had) HFI)))))).
  - apply (w4f_f30_bytes m m' _ _ Hid). rewrite LID. intros x Hx. apply K. lia.
  - apply (w4f_f30_bytes m m' _ _ Hfg). rewrite LFG. intros x Hx. apply K. lia.
  - apply (w4f_f30_bytes m m' _ _ Hh). rewrite lib.Lib.Mem.length_le4. intros x Hx. apply K. lia.
  - apply (w4f_f30_bytes m m' _ _ Hn). cbn [length]. intros x Hx. apply K. lia.
  - apply (w4f_f30_bytes m m' _ _ Hb). intros x Hx. apply K. lia.
Qed.

(* ---- helpers of seg_F34 (a Theorem Labs lane) ---- *)
(* The catalogue's two shared data facts in the form the declaration_of footprint needs. *)
Lemma w4f_f34_cat_facts : forall ly S (W : Reusable.YA0n.world segs) mem md,
  Reusable.YG0n.AR segs B ly S W mem md ->
  B.AsanRT.addressable mem B.ACtlCutP.SM.CAT (B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N) /\
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W)
    (B.AsanRT.shadow_addr B.ACtlCutP.SM.CAT / 8 * 8)
    (B.AsanRT.shadow_addr (B.ACtlCutP.SM.CAT + B.ACtlCutP.SM.CAT_ROW * B.ACtlCutP.SM.CAT_N - 1) / 8 * 8 + 8
     - B.AsanRT.shadow_addr B.ACtlCutP.SM.CAT / 8 * 8).
Proof.
  intros ly S W mem md HAR. split; [exact (ctl_cat_addressable ly S W mem md HAR) | exact (ctl_cat_shadow_vis ly S W mem md HAR)].
Qed.

(* ===================== seg_F34 (B82bf4_at j i -> B82c24_at j i) ===================== *)





(* ---- small facts ---- *)
Lemma w4f_f34_noseg : forall a, Reusable.YImgTop.IMG_TOP <= a -> find_segment B.Img0.rsegs a 1 = None.
Proof.
  intros a Ha. destruct (find_segment B.Img0.rsegs a 1) as [s|] eqn:E; [|reflexivity]. exfalso.
  assert (E1 : Reusable.YImgTop.IMG_TOP = 6283264) by reflexivity.
  assert (E2 : B.Prog.Seg.F34.AC.GT = 6283264) by reflexivity.
  destruct (B.BzBridge.find_segment_below B.Img0.rsegs B.Prog.Seg.F34.AC.GT a 1 s B.Prog.Seg.F34.f34_segs_below_GT E
    ltac:(lia)) as [L|L]; lia.
Qed.

(* A byte the core's view reads in a world is visible there (a hidden byte reads None: H_off_segments). *)
Lemma w4f_f34_vis_of_aview : forall (W : Reusable.YA0n.world segs) mem a v,
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a = Some v -> Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v Hv. destruct (Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict in Hv. rewrite E in Hv.
  unfold lib.Reusable.YK11.seg_rom, memory_read in Hv. change (Z.of_N 1) with 1 in Hv.
  rewrite (Reusable.YA0n.w_Hoff W _ E) in Hv. discriminate Hv.
Qed.

Lemma w4f_f34_not_out : forall W a, ~ lib.Lib.Frame.outside W a -> exists lo hi, In (lo, hi) W /\ lo <= a < hi.
Proof.
  induction W as [|[lo hi] W IH]; intros a H; cbn [lib.Lib.Frame.outside] in H; [exfalso; exact (H I)|].
  destruct (Z_le_gt_dec lo a) as [H1|H1]; [destruct (Z_lt_ge_dec a hi) as [H2|H2]|].
  - exists lo, hi. split; [left; reflexivity | lia].
  - destruct (IH a) as (l & h & Hin & Hb); [intros Ho; apply H; split; [lia | exact Ho]|].
    exists l, h. split; [right; exact Hin | exact Hb].
  - destruct (IH a) as (l & h & Hin & Hb); [intros Ho; apply H; split; [lia | exact Ho]|].
    exists l, h. split; [right; exact Hin | exact Hb].
Qed.

(* The frame base of the owned class-6 frame: in its fake stack (layout_ok's lo_app, wf_fs's position bound), so
   it is above the image (0x60a000 = 4096 + kFakeFramesOff + 6 * 2^20). *)
Lemma w4f_f34_frame_geo : forall cx ly3 S3 W3 mem3 md3 k fr,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  6332416 <= fr /\ fr + 4096 <= lib.Reusable.YM05.alloc_ceiling /\
  (fr + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= fr).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1.
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  pose proof HJ as (HAR & _).
  pose proof (Reusable.YG01.wfs_live _ (Reusable.YG01.wf_fakestack _ _ _ _ _
    (Reusable.YG0n.am_wf _ _ _ _ (proj1 HAR)))) as Hlive.
  change (Reusable.YG00.fs_live (Reusable.YG00.st_fs S3)) with (Reusable.YG01.frames S3) in Hlive.
  rewrite HF in Hlive. unfold ACtlCut.own6 in Hlive. apply Forall_inv in Hlive. cbn [fst snd] in Hlive.
  pose proof (Reusable.YG0f.lo_app _ (Reusable.YG0n.am_layout _ _ _ _ (proj1 HAR))) as Happ.
  pose proof (proj1 (Forall_forall _ _) Happ (Reusable.YG0f.ly_F ly3, Reusable.YG0f.kFakeStackSize)
    ltac:(unfold Reusable.YG0f.owned_extents; cbn [In]; tauto)) as HFa.
  cbn [fst snd] in HFa. destruct HFa as (HF4096 & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (_ & H2 & H3).
  rewrite <- Efr in H2, H3. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in H2, H3.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in H3.
  split; [|split; [exact H2 | lia]].
  rewrite Efr. unfold Reusable.YG0f.frame_addr, Reusable.YG0f.fs_frame_off, Reusable.YG0f.kFakeFramesOff.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096. change (Reusable.YG00.fs_frames 6) with 256 in Hlive.
  change (Z.shiftl 1 Reusable.YG00.kStackSizeLog) with 1048576. lia.
Qed.

Lemma w4f_f34_vis_fsh : forall cx ly3 S3 W3 mem3 md3 k fr lo len,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  ACtlCutP.Sfr fr <= lo -> lo + len <= ACtlCutP.Sfr fr + 512 -> 0 <= len ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr lo len HJ HF HG1 H1 H2 H3.
  pose proof (w4f_f34_frame_geo cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (B0 & B1 & _).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hc.
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in H1, H2.
  assert (Hq : 0 <= fr / 8 <= fr) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  split; [lia|]. split; [lia|].
  intros a Ha.
  refine (proj1 (proj1 (Reusable.YCbq.awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _))).
  right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
  right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr. change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia.
Qed.

(* The shadow-word cover of a sub-window of the journal's present window is visible: the stack's shadow is zero in
   the view (AR's zero_shadow law, the stack entry of zero_shadow_ranges), hence visible. *)
Lemma w4f_f34_vis_stksh : forall cx own ly3 S3 W3 mem3 md3 k lo len,
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= lo -> lo + len <= ACtlCut.c_sp cx - 64 -> 0 < len ->
  B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (B.Prog.rng_asan.sh_al8_lo lo)
    (B.Prog.rng_asan.sh_al8_hi lo len - B.Prog.rng_asan.sh_al8_lo lo).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k lo len HJ H1 H2 H3.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _).
  destruct Hastk as (_ & _ & Hcl & Hlo & Hhi & Hhi47 & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  pose proof (Reusable.YG0d.al_zshadow _ _ LAWS ly3 S3 W3 mem3 md3 _ HAR (or_introl eq_refl)) as Hz.
  cbn [fst snd] in Hz. unfold Reusable.YG0v.zero_shadow, Reusable.YG0v.shadow_of_addr in Hz.
  pose proof (Reusable.YG0f.lo_top _ (Reusable.YG0n.am_layout _ _ _ _ (proj1 HAR))) as Htop.
  destruct Htop as (_ & _ & _ & _ & Hpl & Hph & _). unfold Reusable.YG0f.page_aligned in Hpl, Hph.
  rewrite <- Elo in Hlo, Hcl. rewrite <- Ehi in Hhi, Hhi47.
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hc.
  unfold Reusable.YCfn.LLVMF_STK in H1.
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
  set (L := Reusable.YG0f.ly_stk_lo ly3) in *. set (Hh := Reusable.YG0f.ly_stk_hi ly3) in *.
  set (sp0 := ACtlCut.c_sp cx) in *.
  unfold Reusable.YG0f.SHADOW_OFF in Hz. unfold Reusable.YCfn.LLVMF_STK in Hlo.
  clear - Hz Hcl Hlo Hhi Hhi47 Hpl Hph Hc H1 H2 H3.
  clearbody L Hh sp0.
  split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  intros a Ha.
  assert (Hi : 0 <= a - (2147450880 + L / 8) < (Hh - L) / 8) by (Z.div_mod_to_equations; lia).
  pose proof (Hz _ Hi) as Hv. replace (2147450880 + L / 8 + (a - (2147450880 + L / 8))) with a in Hv by lia.
  exact (w4f_f34_vis_of_aview W3 mem3 a 0 Hv).
Qed.

(* The journal's present window gives the runs' stk premise. *)
Lemma w4f_f34_stk_present : forall cx own ly3 S3 W3 mem3 md3 k lo hi,
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  ACtlCut.c_sp cx - Reusable.YCfn.LLVMF_STK <= lo -> hi <= ACtlCut.c_sp cx -> 0 <= lo ->
  lib.Lib.Frame.stk B.Img0.rsegs mem3 lo hi.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k lo hi HJ H1 H2 H0.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  pose proof (bv_unsigned_in_range 64 (getr (ACtlCut.c_regs cx) 2)) as Hsp.
  unfold ACtlCut.c_sp, Reusable.YG0d.spZ in *. unfold bv_modulus in Hsp. cbn [Z.of_N] in Hsp.
  split; [exact H0|]. split; [lia|].
  intros a Ha. destruct (Hpres a ltac:(lia)) as (_ & b & Hb).
  unfold lib.Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

(* The catalogue row i in the cut's memory: arodata_okS at the entry (ctl_base), the journal's image clause, and
   aview_vis_mrd at the visible image byte. *)
Lemma w4f_f34_row_bytes : forall cx own ly3 S3 W3 mem3 md3 k (i : nat),
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx -> AJ cx own ly3 S3 W3 mem3 md3 k -> (i <= 10)%nat ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (ACtlCutP.SM.CAT + ACtlCutP.SM.CAT_ROW * Z.of_nat i)
    (ACtlCutP.SM.rowb (Z.of_nat i)).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k i HB HJ Hi.
  destruct (B.Prog.Seg.F34.f34_row i ltac:(lia)) as (Himg & _ & Hlen).
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _) & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Himgk & _).
  pose proof ctl_cat_relro_lo as Hr1. pose proof ctl_cat_relro_hi as Hr2.
  unfold ACtlCutP.SM.CAT, ACtlCutP.SM.CAT_ROW, ACtlCutP.SM.CAT_N in Hr1, Hr2 |- *.
  split; [lia|]. split; [rewrite Hlen; lia|].
  intros kk Hk. rewrite Hlen in Hk.
  change (lib.Lib.Mem.mrd segs mem3 (lib.Lib.Mem.wa (652832 + 296 * Z.of_nat i + Z.of_nat kk))) with
    (lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 (652832 + 296 * Z.of_nat i + Z.of_nat kk))).
  pose proof (B.Prog.Seg.F34.f34_img_nth 296 _ _ kk Himg Hk) as Er.
  unfold ACtlCutP.SM.CAT, ACtlCutP.SM.CAT_ROW in Er.
  remember (652832 + 296 * Z.of_nat i + Z.of_nat kk) as a eqn:Ea.
  assert (Ha : 652832 <= a < 652832 + 296 * 11) by lia.
  assert (Hin : Reusable.YG0d.in_img segs a).
  { assert (Hm : In (651264, 12288) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) B.Img0.rsegs))
      by (rewrite B.ProgBridge.rsegs_spans; cbn [In]; tauto).
    apply in_map_iff in Hm as (sg & Esg & Hsg). exists sg. split; [exact Hsg|].
    injection Esg as E1 E2. rewrite E1, E2. lia. }
  destruct (ctl_relro_not_owned a (or_intror Ha)) as (Hno & Her).
  assert (Hrr : RLO <= a < RHI) by lia.
  pose proof (Himgk a Hin Hno Her (Reusable.APostBase.ro_spares segs RLO RHI FP a (or_intror Hrr))) as Ek.
  pose proof (Hro a (or_intror Hrr) Hno Her) as E0.
  rewrite E0 in Ek.
  pose proof (B.ProgBridge.img_vis_W W3) as (_ & _ & Hvis).
  pose proof (Hvis a ltac:(unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI; lia)) as Hva.
  rewrite (aview_vis_mrd W3 mem3 a Hva) in Ek.
  unfold lib.Lib.Mem.wa.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 a)) as [b|] eqn:Em;
  destruct (nth_error (ACtlCutP.SM.rowb (Z.of_nat i)) kk) as [b'|] eqn:En.
  - assert (Es : lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a) = Some b') by exact Er.
    rewrite Es in Ek. cbn [option_map] in Ek. injection Ek as Ek. f_equal. apply bv_eq. exact Ek.
  - apply nth_error_None in En. lia.
  - assert (Es : lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a) = Some b') by exact Er.
    rewrite Es in Ek. discriminate Ek.
  - apply nth_error_None in En. lia.
Qed.

(* ---- the write set of the stage and transport across it ---- *)
(* The stage writes the four frame-shadow bytes [Sfr fr + 8, + 12) (the stretch), the callee window [sp - 2256, sp)
   and the row slot [fr + 64, fr + 96) (declaration_of). *)
Definition w4f_f34_WR (fr sp : Z) : list lib.Lib.Frame.ivl :=
  [(ACtlCutP.Sfr fr + 8, ACtlCutP.Sfr fr + 12); (sp - 2256, sp); (fr + 64, fr + 96)].

(* Where the frame and the stack lie (the owned fake frame below the stack window, both in app memory). *)
Definition w4f_f34_G (fr sp : Z) : Prop :=
  fr mod 8 = 0 /\ 6332416 <= fr /\ (fr + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) /\
  fr + 4096 <= sp - 2256 /\ sp <= 2 ^ 47 /\ 0x10007fff8000 <= sp - 2256.

Lemma w4f_f34_dj : forall fr sp a len, w4f_f34_G fr sp -> 0 <= a -> 0 <= len ->
  (a + len <= 0x7fff7000 \/ 0x10007fff8000 <= a) ->
  (a + len <= sp - 2256 \/ sp <= a) -> (a + len <= fr + 64 \/ fr + 96 <= a) ->
  lib.Lib.Frame.disjoint_from (w4f_f34_WR fr sp) a len.
Proof.
  intros fr sp a len (H8 & H0 & Hfa & Hfs & Hsp & Hhm) Ha Hl Happ Hw Hs.
  unfold w4f_f34_WR, ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. cbn [lib.Lib.Frame.disjoint_from].
  assert (Hq : 8 * (fr / 8) = fr) by (Z.div_mod_to_equations; lia).
  assert (Hq0 : 0 <= fr / 8) by (apply Z.div_pos; lia).
  generalize dependent (fr / 8). intros q Hq Hq0.
  split; [lia | split; [lia | split; [lia | exact I]]].
Qed.

Lemma w4f_f34_sh_out : forall fr sp a, w4f_f34_G fr sp -> B.AsanRT.app_mem a -> ~ (fr + 64 <= a < fr + 96) ->
  lib.Lib.Frame.outside (w4f_f34_WR fr sp) (B.AsanRT.shadow_addr a).
Proof.
  intros fr sp a (H8 & H0 & Hfa & Hfs & Hsp & Hhm) Ha Hno.
  unfold w4f_f34_WR, ACtlCutP.Sfr. cbn [lib.Lib.Frame.outside].
  unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END in Ha.
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
  assert (Hq : 8 * (fr / 8) = fr) by (Z.div_mod_to_equations; lia).
  assert (Ha8 : 8 * (a / 8) <= a < 8 * (a / 8) + 8) by (Z.div_mod_to_equations; lia).
  generalize dependent (fr / 8). generalize dependent (a / 8). intros qa Ha8 q Hq.
  split; [lia | split; [lia | split; [lia | exact I]]].
Qed.

Lemma w4f_f34_ba_tr : forall fr sp m m' a bs, w4f_f34_G fr sp ->
  lib.Lib.Frame.munch (w4f_f34_WR fr sp) m m' -> lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  (a + Z.of_nat (length bs) <= 0x7fff7000 \/ 0x10007fff8000 <= a) ->
  (a + Z.of_nat (length bs) <= sp - 2256 \/ sp <= a) ->
  (a + Z.of_nat (length bs) <= fr + 64 \/ fr + 96 <= a) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros fr sp m m' a bs HG MU Hb H1 H2 H3.
  apply (lib.Lib.Frame.bytes_at_transport B.Img0.rsegs _ m m' a bs Hb MU).
  pose proof Hb as (Ha & _). apply w4f_f34_dj; auto; lia.
Qed.

Lemma w4f_f34_spill_m : forall fr sp regs m m' off v A, w4f_f34_G fr sp ->
  lib.Lib.Frame.munch (w4f_f34_WR fr sp) m m' -> ACtlCut.rgv regs 9 A -> sp <= A -> A + 448 <= 2 ^ 47 ->
  0 <= off <= 440 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill regs m' off v.
Proof.
  intros fr sp regs m m' off v A HG MU HA H1 H2 Hoff Hs.
  pose proof HG as (_ & _ & _ & Hfs & Hsp & Hhm).
  pose proof (w4f_spill regs m off v A Hs HA ltac:(lia) ltac:(lia)) as Hq.
  exists A. split; [exact HA|]. unfold ACtlCutP.q64 in *.
  apply (w4f_f34_ba_tr fr sp m m' _ _ HG MU Hq); rewrite lib.Lib.Mem.length_le8; lia.
Qed.

Lemma w4f_f34_addr_m : forall fr sp m m' p n, w4f_f34_G fr sp ->
  lib.Lib.Frame.munch (w4f_f34_WR fr sp) m m' -> B.AsanRT.addressable m p n ->
  (p + n <= fr + 64 \/ fr + 96 <= p) -> B.AsanRT.addressable m' p n.
Proof.
  intros fr sp m m' p n HG MU HA Hs.
  apply (B.Prog.Seg.F34.f34_addr_keep m m' p n HA).
  intros a Ha. pose proof HA as (Hp0 & Hn0 & Hend & HB).
  destruct (HB (a - p) ltac:(lia)) as (Happ & _). replace (p + (a - p)) with a in Happ by lia.
  unfold lib.Lib.Mem.mrd. rewrite (MU (lib.Lib.Mem.wa (B.AsanRT.shadow_addr a))); [reflexivity|].
  rewrite lib.Lib.Mem.wa_unsigned.
  - apply w4f_f34_sh_out; [exact HG | exact Happ | lia].
  - unfold B.AsanRT.APPMEM_END in Hend. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
    assert (0 <= a / 8 <= a) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia.
Qed.

Lemma w4f_f34_stk_m : forall fr sp m m' bs, w4f_f34_G fr sp ->
  lib.Lib.Frame.munch (w4f_f34_WR fr sp) m m' -> lib.Lib.Frame.wmono B.Img0.rsegs m m' ->
  lib.Lib.Frame.stk B.Img0.rsegs m fr (fr + 3136) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' (fr + 64) bs -> length bs = 32%nat ->
  lib.Lib.Frame.stk B.Img0.rsegs m' fr (fr + 3136).
Proof.
  intros fr sp m m' bs HG MU WM (H0 & H1 & H) Hb Hl. split; [exact H0|]. split; [exact H1|].
  pose proof HG as (_ & _ & Hfa & Hfs & Hsp & Hhm).
  intros a Ha. destruct (H a Ha) as (Hw & b & Hmb). split; [exact (WM _ Hw)|].
  assert (Hout : ~ (fr + 64 <= a < fr + 96) ->
                 exists b0, lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa a) = Some b0).
  { intros Hno. exists b. unfold lib.Lib.Mem.mrd in *. rewrite (MU (lib.Lib.Mem.wa a)); [exact Hmb|].
    rewrite lib.Lib.Mem.wa_unsigned by lia.
    apply (lib.Lib.Frame.disjoint_outside _ a 1); [|lia].
    apply w4f_f34_dj; [exact HG | lia | lia | lia | lia | lia]. }
  destruct (Z_lt_le_dec a (fr + 64)) as [Hlt|Hge]; [apply Hout; lia|].
  destruct (Z_lt_le_dec a (fr + 96)) as [Hlt2|Hge2]; [|apply Hout; lia].
  pose proof Hb as (_ & _ & Hn).
  destruct (nth_error bs (Z.to_nat (a - (fr + 64)))) as [b0|] eqn:E.
  - exists b0. rewrite <- E. replace a with (fr + 64 + Z.of_nat (Z.to_nat (a - (fr + 64)))) at 1 by lia.
    apply Hn. lia.
  - apply nth_error_None in E. lia.
Qed.

(* The journal across a stretch that writes only the bytes of W (YCbq.ajournal_exec); W lies above the image. *)
Lemma w4f_f34_aj_step : forall cx own ly3 S3 W3 m md m' md' k (W : list lib.Lib.Frame.ivl),
  AJ cx own ly3 S3 W3 m md k ->
  lib.Lib.Frame.munch W m m' -> lib.Lib.Frame.wmono B.Img0.rsegs m m' ->
  (forall x : word, Reusable.YA0n.w_H W3 x = true -> m' x = m x) ->
  Reusable.YK04.same_but_materialized md md' ->
  (forall a, ~ lib.Lib.Frame.outside W a -> Reusable.YImgTop.IMG_TOP <= a) ->
  (forall a, ~ lib.Lib.Frame.outside W a ->
     Reusable.YCbq.awr_byte Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
       (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3 own a) ->
  AJ cx own ly3 S3 W3 m' md' k.
Proof.
  intros cx own ly3 S3 W3 m md m' md' k W HJ MU WM Hhid Hs Hhi HW.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           (fun a => ~ lib.Lib.Frame.outside W a) HJ); [| | exact Hhid | exact Hs | exact HW].
  - intros x Hx. unfold Reusable.YK04.mrestrict. destruct (Reusable.YA0n.w_H W3 x); [reflexivity|].
    apply MU. destruct (B.Prog.Seg.F34.f34_outside_dec W (bv_unsigned x)) as [H|H]; [exact H | exfalso; exact (Hx H)].
  - intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H W3 x); [exact Hx|].
    destruct (B.Prog.Seg.F34.f34_outside_dec W (bv_unsigned x)) as [Ho|Ho].
    + rewrite (MU x Ho). exact Hx.
    + pose proof (Hhi _ Ho) as Hl.
      destruct (m x) as [b|] eqn:Em; [|contradiction].
      assert (Hw : wview B.Img0.rsegs m x <> None) by (unfold wview; rewrite Em; discriminate).
      pose proof (WM x Hw) as Hw'. unfold wview in Hw'. destruct (m' x); [discriminate|].
      rewrite (w4f_f34_noseg _ Hl) in Hw'. exfalso; exact (Hw' eq_refl).
Qed.

(* ---- declaration_of (0x83114) as a footprint run on the cut's own memory ----
   The continuation's post: declaration_of_post_on (B/Prog/declaration_of_c.v, route (C)) with ro_agree in place of
   mem_inv (the real memory keeps every read-only byte, MemNorm.ro_same, so mem_inv cannot be carried). *)
Definition w4f_f34_decl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (lo : Z) (row ob : list byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = lib.Lib.MState.MS
      (lib.Lib.Frame.mkR ra sp gp tp t0' t1' t2' s0 s1
         (Z_to_bv 64 (if OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcDecl.decl_ok row then 1 else 0))
         a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
      F (lib.Lib.MState.ret_pc ra) fc None m' (lib.Reusable.YK11.seg_rom B.Img0.rsegs) /\
    lib.Lib.Frame.munch [(bv_unsigned sp - 2256, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 32)] m m' /\
    lib.Lib.Frame.wmono B.Img0.rsegs m m' /\ B.MemNorm.ro_agree B.Img0.rsegs m' /\
    lib.Lib.Frame.stk B.Img0.rsegs m' lo (bv_unsigned sp) /\
    lib.Lib.Step.rw_cells B.Img0.rsegs m' (bv_unsigned a1)
      [lib.Lib.Cells.CB 32 (if OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcDecl.decl_ok row
                            then OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcDecl.decl row else ob)] /\
    lib.Lib.Mem.bytes_at B.Img0.rsegs m' (bv_unsigned a0) row /\
    B.AsanRT.asan_cells m' /\
    (forall P : Z -> Prop, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m').

Lemma w4f_f34_asan_cells_back : forall m m0, B.MemNorm.mem_rel B.Img0.rsegs m m0 ->
  B.AsanRT.asan_cells m0 -> B.AsanRT.asan_cells m.
Proof.
  intros m m0 R H. unfold B.AsanRT.asan_cells in H |- *.
  decompose [and] H. try clear H.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- lib.Lib.Mem.bytes_at _ _ ?a ?bs =>
      exact (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs m m0 a bs R) ltac:(assumption)) end.
Qed.

(* THE ONE PLACE that instantiates declaration_of's footprint contract (declaration_of_F_holds_on at the call): the run
   on normalize m (MemNorm.mem_inv_normalize), carried back to m by MemNormF.evtF_normalize_ro, at RNG := RNG_W H with
   one visibility fact per footprint range; the region premise moves to normalize m by ShadowRwOnT.shadow_rw_on_rel
   and the post's region transport back by ShadowRwOnT.shadow_rw_on_of_rel.  The contract is applied by `eapply`
   against its conclusion, so the footprint argument is fixed by unification whatever its binder position. *)
Lemma w4f_f34_decl_lift : B.Prog.declaration_of_c.declaration_of_contract_F_on ->
  forall (H : word -> bool)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (row ob : list byte),
    lib.Lib.Frame.stk B.Img0.rsegs m lo (bv_unsigned sp) ->
    lo + 2256 <= bv_unsigned sp ->
    bv_unsigned a0 mod 8 = 0 ->
    length row = 296%nat ->
    lib.Lib.Mem.bytes_at B.Img0.rsegs m (bv_unsigned a0) row ->
    lib.Lib.Step.rw_cells B.Img0.rsegs m (bv_unsigned a1) [lib.Lib.Cells.CB 32 ob] ->
    bv_unsigned a1 + 32 <= bv_unsigned a0 \/ bv_unsigned a0 + 296 <= bv_unsigned a1 ->
    bv_unsigned a0 + 296 <= bv_unsigned sp - 2256 \/ bv_unsigned sp <= bv_unsigned a0 ->
    bv_unsigned a1 + 32 <= bv_unsigned sp - 2256 \/ bv_unsigned sp <= bv_unsigned a1 ->
    B.MemNorm.ro_agree B.Img0.rsegs m ->
    Reusable.YImgTop.IMG_TOP <= bv_unsigned a1 ->
    B.AsanRT.asan_cells m ->
    B.ShadowRwOn.shadow_rw_on
      (B.Prog.declaration_of_c.declaration_of_shadow_R (bv_unsigned a0) (bv_unsigned a1)) m ->
    B.AsanRT.HIGHMEM_BEG <= lo -> bv_unsigned sp <= B.AsanRT.APPMEM_END ->
    B.AsanRT.addressable m (bv_unsigned a0) 296 -> B.AsanRT.addressable m (bv_unsigned a1) 32 ->
    B.AsanRT.app_mem (bv_unsigned a1 + 32) ->
    (bv_unsigned a1 + 32 <= B.AsanRT.RT_LO \/ B.AsanRT.RT_HI <= bv_unsigned a1) ->
    B.ProgBridge.range_visible H (bv_unsigned sp - 2256) 2256 ->
    B.ProgBridge.range_visible H (B.Prog.rng_asan.sh_al8_lo (bv_unsigned sp - 2256))
      (B.Prog.rng_asan.sh_al8_hi (bv_unsigned sp - 2256) 2256 - B.Prog.rng_asan.sh_al8_lo (bv_unsigned sp - 2256)) ->
    B.ProgBridge.range_visible H B.AsanRT.RT_LO (B.AsanRT.RT_HI - B.AsanRT.RT_LO) ->
    B.ProgBridge.range_visible H B.Prog.ImgBounds.IMG_LO (B.Prog.ImgBounds.IMG_HI - B.Prog.ImgBounds.IMG_LO) ->
    B.ProgBridge.range_visible H (bv_unsigned a0) 296 ->
    B.ProgBridge.range_visible H ((bv_unsigned a0 / 8 + B.AsanRT.ASAN_K) / 8 * 8)
      (((bv_unsigned a0 + 295) / 8 + B.AsanRT.ASAN_K) / 8 * 8 + 8 - (bv_unsigned a0 / 8 + B.AsanRT.ASAN_K) / 8 * 8) ->
    B.ProgBridge.range_visible H (bv_unsigned a1) 32 ->
    B.ProgBridge.range_visible H ((bv_unsigned a1 / 8 + B.AsanRT.ASAN_K) / 8 * 8)
      (((bv_unsigned a1 + 31) / 8 + B.AsanRT.ASAN_K) / 8 * 8 + 8 - (bv_unsigned a1 / 8 + B.AsanRT.ASAN_K) / 8 * 8) ->
    lib.Lib.ExecF.evtF B.Img0.rsegs (B.ProgBridge.RNG_W H)
      (w4f_f34_decl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m lo row ob)
      (lib.Lib.MState.MS
         (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
            t3 t4 t5 t6)
         F (Z_to_bv 64 B.Prog.declaration_of_c.DECLARATION_OF) fc None m (lib.Reusable.YK11.seg_rom B.Img0.rsegs)).
Proof.
  intros HC H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo row ob Pstk Plo Pal Plen Prow Pcell Pdj Pdm Pds Pro Pgt Pac Psw Phm Pae Pada Padb Pap Prt
    V2 VS VR VI V4 V5 V6 V7.
  pose proof (B.MemNorm.mem_rel_normalize B.Img0.rsegs m Pro) as REL.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  unfold bv_modulus in Rsp, Ra1. cbn [Z.of_N] in Rsp, Ra1.
  assert (Nstk : lib.Lib.Frame.stk B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs m) lo (bv_unsigned sp)).
  { apply (B.Prog.Seg.Tac_ro.stk_rel m _ lo _ REL); [unfold B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG in *; lia | lia |
      exact Pstk]. }
  assert (Ncell : lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs m) (bv_unsigned a1)
                    [lib.Lib.Cells.CB 32 ob]).
  { destruct Pcell as ((Hwf & Hbb) & Hw). split.
    - split; [exact Hwf | exact (B.Prog.Seg.Tac_ro.ba_rel m _ _ _ REL Hbb)].
    - pose proof Hw as (Hw0 & Hw1 & _).
      eapply (B.MemNorm.wr_at_norm B.Img0.rsegs); [exact REL | exact Hw |].
      intros i Hi. apply B.Prog.Seg.F34.f34_ro_gt.
      assert (E1 : Reusable.YImgTop.IMG_TOP = 6283264) by reflexivity.
      assert (E2 : B.Prog.Seg.F34.AC.GT = 6283264) by reflexivity. lia. }
  pose proof (B.Prog.Seg.Tac_ro.ba_rel m _ _ _ REL Prow) as Nrow.
  pose proof (B.Prog.Seg.Tac_ro.asan_cells_rel m _ REL Pac) as Nac.
  pose proof (B.ShadowRwOnT.shadow_rw_on_rel _ m _ REL Psw) as Nsw.
  pose proof (B.Prog.Seg.Tac_ro.addressable_rel m _ _ _ REL Pada) as Nada.
  pose proof (B.Prog.Seg.Tac_ro.addressable_rel m _ _ _ REL Padb) as Nadb.
  pose proof (B.MemNorm.mem_inv_normalize B.Img0.rsegs m) as Nmi.
  assert (HN : lib.Lib.ExecF.evtF B.Img0.rsegs (B.ProgBridge.RNG_W H)
     (B.Prog.declaration_of_c.declaration_of_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc
        (B.MemNorm.normalize B.Img0.rsegs m) lo row ob)
     (lib.Lib.MState.MS
        (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6)
        F (Z_to_bv 64 B.Prog.declaration_of_c.DECLARATION_OF) fc None (B.MemNorm.normalize B.Img0.rsegs m)
        (lib.Reusable.YK11.seg_rom B.Img0.rsegs))).
  { unfold B.Prog.declaration_of_c.declaration_of_contract_F_on in HC.
    eapply HC.
    all: first
      [ exact Nstk | exact Nrow | exact Ncell | exact Nmi | exact Nac | exact Nsw | exact Nada | exact Nadb
      | exact (B.ProgBridge.rng_bytes_RNG_W H)
      | exact (B.ProgBridge.rng_of_visible _ _ _ VI)
      | exact (B.ProgBridge.rng_of_visible _ _ _ V2)
      | (right; exact (B.ProgBridge.rng_of_visible _ _ _ VS))
      | exact (B.ProgBridge.rng_of_visible _ _ _ VR)
      | exact (B.ProgBridge.rng_of_visible _ _ _ V4)
      | exact (B.ProgBridge.rng_of_visible _ _ _ V5)
      | exact (B.ProgBridge.rng_of_visible _ _ _ V6)
      | exact (B.ProgBridge.rng_of_visible _ _ _ V7)
      | exact Plo | exact Pal | exact Plen | exact Pdj | exact Pdm | exact Pds | exact Phm | exact Pae | exact Pap
      | exact Prt ]. }
  pose proof (B.MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ m _ Pro HN) as HM.
  eapply lib.Lib.ExecF.evtF_mono; [exact HM|].
  intros ms (s0' & PO & Hrel & Hros).
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E & MU & WM & _ & ST & RW & BA & AC & SW).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom lib.Lib.MState.MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', memX.
  split; [reflexivity|].
  split; [exact (B.MemNorm.munch_rel B.Img0.rsegs _ m _ memX m0' REL Hmr Hros MU)|].
  split; [exact (B.MemNorm.wmono_rel B.Img0.rsegs m _ memX m0' REL Hmr Hros WM)|].
  split; [exact (B.MemNorm.ro_agree_of_mem_rel B.Img0.rsegs memX m0' Hmr)|].
  split; [exact (B.Prog.Seg.Tac_ro.stk_rel_back memX m0' lo (bv_unsigned sp) Hmr
                   ltac:(unfold B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG in *; lia) ltac:(lia) ST)|].
  split; [exact (B.Prog.Seg.F34F.f34F_rwc_back memX m0' _ _ Hmr RW)|].
  split; [exact (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs memX m0' _ _ Hmr) BA)|].
  split; [exact (w4f_f34_asan_cells_back memX m0' Hmr AC) |].
  intros P HP. apply (B.ShadowRwOnT.shadow_rw_on_of_rel P memX m0' Hmr).
  exact (SW P (B.ShadowRwOnT.shadow_rw_on_rel P m _ REL HP)).
Qed.

(* declaration_of's region at the call of seg_F34 (a0 = CAT + CAT_ROW * i, a1 = fr + 64) lies in ctl_rt_C's two
   regions: the two row spans' shadow words are shadow bytes of the image (img_shadow: the row sits in
   [CAT, CAT + CAT_ROW * CAT_N) inside [IMG_LO, IMG_HI), and a word cover adds at most 63 bytes on either side), and
   the slot's [fr + 64, fr + 96) shadow words lie in the owned frame's shadow [S(fr), S(fr) + 512) (cut_shadow (F);
   fr is 32-aligned, so the cover starts at S(fr) + 4 at the lowest). *)
Lemma w4f_f34_decl_region : forall ly3 S3 pos fr (ii : nat) a,
  In (6, pos) (Reusable.YG01.frames S3) -> fr = Reusable.YG0f.frame_addr ly3 6 pos ->
  fr mod 32 = 0 -> 0 <= fr -> (ii <= 10)%nat ->
  B.Prog.declaration_of_c.declaration_of_shadow_R (ACtlCutP.SM.CAT + ACtlCutP.SM.CAT_ROW * Z.of_nat ii) (fr + 64) a ->
  B.ACtlRtC.cut_shadow B ly3 S3 a \/ B.ACtlRtC.img_shadow a.
Proof.
  intros ly3 S3 pos fr ii a Hin Efr H32 H0 Hii Ha.
  assert (ECAT : ACtlCutP.SM.CAT = 652832) by reflexivity.
  assert (ECATR : ACtlCutP.SM.CAT_ROW = 296) by reflexivity.
  rewrite ECAT, ECATR in Ha.
  unfold B.Prog.declaration_of_c.declaration_of_shadow_R, B.Prog.sh_word_on.sh_word_on,
    B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
  destruct Ha as [(_ & Ha) | [(_ & Ha) | (_ & Ha)]].
  - right. exists ((a - 2147450880) * 8).
    unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
    Z.div_mod_to_equations. lia.
  - right. exists ((a - 2147450880) * 8).
    unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
    Z.div_mod_to_equations. lia.
  - left. left. exists 6, pos. split; [exact Hin |]. rewrite <- Efr.
    change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

(* ---- the body predicates across the stage's write set (same registers) ---- *)
Ltac w4f_f34_sp HG MU HA := eapply w4f_f34_spill_m; [exact HG | exact MU | exact HA | lia | lia | lia | eassumption].

Lemma w4f_f34_FRAC_m : forall cx fr sel regs m m' sp, w4f_f34_G fr sp ->
  lib.Lib.Frame.munch (w4f_f34_WR fr sp) m m' -> Reusable.YG0d.spZ regs = sp -> ACtlCut.c_sp cx <= 2 ^ 47 ->
  (exists sh, lib.Lib.Mem.bytes_at segs m' (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) ->
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros cx fr sel regs m m' sp HG MU Hsp Hcs Hsh' H.
  destruct H as (A & sp' & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle & HspA &
    HfrA & HA448 & Hsp4096 & HspEnd & Hq336 & Hq48 & Hq40 & Hq0 & Hq16 & Hsh & Hsaved & Hq4088).
  assert (E : sp' = sp) by congruence.
  pose proof HG as (H8 & H0 & Hfa & Hfs & Hsp47 & Hhm).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  assert (Hsl : length (ACtlCutP.saved_bytes cx) = 104%nat)
    by (unfold ACtlCutP.saved_bytes; rewrite !length_app, !lib.Lib.Mem.length_le8; reflexivity).
  exists A, sp'. refine (conj Hr2 (conj Hspm (conj HspZ (conj Hr4 (conj Hr8 (conj Hr9 (conj Hr3 (conj Hr19 (conj Hr26
    (conj Hfr32 (conj HA32 (conj HAle (conj HspA (conj HfrA (conj HA448 (conj Hsp4096 (conj HspEnd
    (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hsh' (conj _ _)))))))))))))))))))))))).
  all: unfold ACtlCutP.q64 in *.
  all: (eapply w4f_f34_ba_tr; [exact HG | exact MU | eassumption | | | ]); rewrite ?lib.Lib.Mem.length_le8, ?Hsl; lia.
Qed.

Lemma w4f_f34_LK_m : forall cx fr j regs m m' sp A, w4f_f34_G fr sp ->
  lib.Lib.Frame.munch (w4f_f34_WR fr sp) m m' -> ACtlCut.rgv regs 9 A -> sp <= A -> A + 448 <= 2 ^ 47 ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.LK cx fr j regs m -> ACtlCutP.LK cx fr j regs m'.
Proof.
  intros cx fr j regs m m' sp A HG MU HA HspA HA47 Hstk' H.
  pose proof HG as (H8 & H0 & Hfa & Hfs & Hsp47 & Hhm).
  destruct H as (Hj & H240 & HOUR & HFLI).
  destruct HFLI as (H27 & S168 & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 & S192 & S200 &
    S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & Hadr & Hstk & HRAD & HKNT & S168b & S88).
  destruct HRAD as (Ra & Rb & Rc). destruct HKNT as (Kb & Ka).
  assert (HK : ACtlCutP.KNA.KIND_NAME = 652672) by reflexivity.
  assert (HKl : length ACtlCutP.KNA.kind_name_bytes = 112%nat) by (vm_compute; reflexivity).
  pose proof (B.Prog.SlotModel.OUR_length (ACtlCut.c_in cx)) as HOl.
  refine (conj Hj (conj _ (conj _ _))); [w4f_f34_sp HG MU HA | |].
  { unfold ACtlCutP.OURb in *. eapply w4f_f34_ba_tr; [exact HG | exact MU | exact HOUR | | |]; rewrite HOl; lia. }
  refine (conj H27 _).
  do 21 (refine (conj _ _); [w4f_f34_sp HG MU HA |]).
  refine (conj _ (conj Hstk' (conj _ (conj _ (conj _ _))))).
  - eapply w4f_f34_addr_m; [exact HG | exact MU | exact Hadr | lia].
  - unfold ACtlCutP.fragb in *. refine (conj _ (conj _ _)).
    + eapply w4f_f34_addr_m; [exact HG | exact MU | exact Ra | lia].
    + eapply w4f_f34_addr_m; [exact HG | exact MU | exact Rb | unfold ACtlCutP.fragb; lia].
    + eapply w4f_f34_addr_m; [exact HG | exact MU | exact Rc | lia].
  - split.
    + eapply w4f_f34_ba_tr; [exact HG | exact MU | exact Kb | | |]; rewrite HKl, HK; lia.
    + eapply w4f_f34_addr_m; [exact HG | exact MU | exact Ka | rewrite HK; lia].
  - w4f_f34_sp HG MU HA.
  - w4f_f34_sp HG MU HA.
Qed.

(* The turn's heap block phi: below the stack window, in app memory, apart from the row slot. *)
Lemma w4f_f34_PTL_m : forall cx j phi fr regs m m' sp A, w4f_f34_G fr sp ->
  lib.Lib.Frame.munch (w4f_f34_WR fr sp) m m' -> ACtlCut.rgv regs 9 A -> sp <= A -> A + 448 <= 2 ^ 47 ->
  0 <= phi -> (phi + ACtlCutP.SM.t_len (ACtlCut.c_in cx) j <= 0x7fff7000 \/ 0x10007fff8000 <= phi) ->
  phi + ACtlCutP.SM.t_len (ACtlCut.c_in cx) j <= sp - 2256 ->
  (phi + ACtlCutP.SM.t_len (ACtlCut.c_in cx) j <= fr + 64 \/ fr + 96 <= phi) ->
  lib.Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.PTL cx j phi fr regs m -> ACtlCutP.PTL cx j phi fr regs m'.
Proof.
  intros cx j phi fr regs m m' sp A HG MU HA HspA HA47 Hp0 Hpa Hpw Hps Hstk' H.
  pose proof HG as (H8 & H0 & Hfa & Hfs & Hsp47 & Hhm).
  destruct H as (Hsel & H18 & H20 & S152 & S312 & Hphi & Hplen & S160 & Hq32 & Hstk).
  unfold ACtlCutP.flen in Hplen.
  refine (conj Hsel (conj H18 (conj H20 (conj _ (conj _ (conj _ (conj Hplen (conj _ (conj _ Hstk'))))))))).
  - w4f_f34_sp HG MU HA.
  - w4f_f34_sp HG MU HA.
  - eapply w4f_f34_ba_tr; [exact HG | exact MU | exact Hphi | | |]; lia.
  - w4f_f34_sp HG MU HA.
  - unfold ACtlCutP.q64 in *. eapply w4f_f34_ba_tr; [exact HG | exact MU | exact Hq32 | | |];
      rewrite lib.Lib.Mem.length_le8; lia.
Qed.

Lemma w4f_f34_FTURN_m : forall cx j phi fr regs m m' sp A, w4f_f34_G fr sp ->
  lib.Lib.Frame.munch (w4f_f34_WR fr sp) m m' -> ACtlCut.rgv regs 9 A -> sp <= A -> A + 448 <= 2 ^ 47 ->
  0 <= phi -> (phi + ACtlCutP.SM.t_len (ACtlCut.c_in cx) j <= 0x7fff7000 \/ 0x10007fff8000 <= phi) ->
  phi + ACtlCutP.SM.t_len (ACtlCut.c_in cx) j <= sp - 2256 ->
  (phi + ACtlCutP.SM.t_len (ACtlCut.c_in cx) j <= fr + 64 \/ fr + 96 <= phi) ->
  ACtlCutP.FTURN cx j phi regs m -> ACtlCutP.FTURN cx j phi regs m'.
Proof.
  intros cx j phi fr regs m m' sp A HG MU HA HspA HA47 Hp0 Hpa Hpw Hps H.
  pose proof HG as (H8 & H0 & Hfa & Hfs & Hsp47 & Hhm).
  destruct H as (S224 & S232 & Hphi & Hplen).
  refine (conj _ (conj _ (conj _ Hplen))).
  - w4f_f34_sp HG MU HA.
  - w4f_f34_sp HG MU HA.
  - eapply w4f_f34_ba_tr; [exact HG | exact MU | exact Hphi | | |]; lia.
Qed.

Lemma w4f_f34_IFS_m : forall cx fr j regs m m' sp, w4f_f34_G fr sp ->
  lib.Lib.Frame.munch (w4f_f34_WR fr sp) m m' -> ACtlCutP.IFS cx fr j regs m -> ACtlCutP.IFS cx fr j regs m'.
Proof.
  intros cx fr j regs m m' sp HG MU H.
  pose proof HG as (H8 & H0 & Hfa & Hfs & Hsp47 & Hhm).
  destruct H as ((HID & Hid) & (HFG & Hfg) & (Hhv & Hn & Hbody & Hadr & HFI)).
  pose proof (B.Prog.Seg.Tac_ro.tr_ID_length (ACtlCut.c_in cx) j) as L1.
  pose proof (B.Prog.Seg.Tac_ro.tr_FG_length (ACtlCut.c_in cx) j) as L2.
  pose proof (B.Prog.Seg.Tac_ro.tr_body_length (ACtlCut.c_in cx) j) as L3.
  unfold ACtlCutP.IDBe, ACtlCutP.FGBe, ACtlCutP.u32, ACtlCutP.b8 in *.
  refine (conj (conj _ Hid) (conj (conj _ Hfg) (conj _ (conj _ (conj _ (conj _ HFI)))))).
  - eapply w4f_f34_ba_tr; [exact HG | exact MU | exact HID | | |]; rewrite L1; lia.
  - eapply w4f_f34_ba_tr; [exact HG | exact MU | exact HFG | | |]; rewrite L2; lia.
  - eapply w4f_f34_ba_tr; [exact HG | exact MU | exact Hhv | | |]; rewrite lib.Lib.Mem.length_le4; lia.
  - eapply w4f_f34_ba_tr; [exact HG | exact MU | exact Hn | | |]; cbn [length]; lia.
  - eapply w4f_f34_ba_tr; [exact HG | exact MU | exact Hbody | | |]; lia.
  - eapply w4f_f34_addr_m; [exact HG | exact MU | exact Hadr | lia].
Qed.

(* Arithmetic of the row and the slot. *)
Lemma w4f_f34_slot_sh : forall fr kk, fr mod 8 = 0 -> 0 <= kk < 32 ->
  ACtlCutP.Sfr fr + 8 <= B.AsanRT.shadow_addr (fr + 64 + kk) < ACtlCutP.Sfr fr + 12.
Proof. intros fr kk H8 Hk. unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma w4f_f34_slotsh_in : forall fr, fr mod 8 = 0 -> 0 <= fr ->
  ACtlCutP.Sfr fr <= ((fr + 64) / 8 + B.AsanRT.ASAN_K) / 8 * 8 /\
  ((fr + 64) / 8 + B.AsanRT.ASAN_K) / 8 * 8 +
    (((fr + 64 + 31) / 8 + B.AsanRT.ASAN_K) / 8 * 8 + 8 - ((fr + 64) / 8 + B.AsanRT.ASAN_K) / 8 * 8)
    <= ACtlCutP.Sfr fr + 512 /\
  0 <= ((fr + 64 + 31) / 8 + B.AsanRT.ASAN_K) / 8 * 8 + 8 - ((fr + 64) / 8 + B.AsanRT.ASAN_K) / 8 * 8.
Proof. intros fr H8 H0. unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. Qed.

Lemma w4f_f34_rowsh_in : forall x : Z, 0 <= x <= 10 ->
  B.AsanRT.shadow_addr 652832 / 8 * 8 <= ((652832 + 296 * x) / 8 + B.AsanRT.ASAN_K) / 8 * 8 /\
  0 <= ((652832 + 296 * x + 295) / 8 + B.AsanRT.ASAN_K) / 8 * 8 + 8 - ((652832 + 296 * x) / 8 + B.AsanRT.ASAN_K) / 8 * 8 /\
  ((652832 + 296 * x) / 8 + B.AsanRT.ASAN_K) / 8 * 8 +
    (((652832 + 296 * x + 295) / 8 + B.AsanRT.ASAN_K) / 8 * 8 + 8 - ((652832 + 296 * x) / 8 + B.AsanRT.ASAN_K) / 8 * 8)
  <= B.AsanRT.shadow_addr 652832 / 8 * 8 +
     (B.AsanRT.shadow_addr (652832 + 296 * 11 - 1) / 8 * 8 + 8 - B.AsanRT.shadow_addr 652832 / 8 * 8).
Proof. intros x Hx. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. Qed.


(* ---- helpers of seg_F36 / seg_F36_c20 / seg_F36_c2c (a Theorem Labs lane) ---- *)


(* The byte at a kept address: lib/Lib's read is the same before and after. *)
Local Notation w4f_f36_K m m' a :=
  (lib.Lib.Mem.mrd segs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd segs m (Z_to_bv 64 a)).

(* A view equality at an address visible in the earlier world is an mrd equality (aview_vis_mrd twice). *)
Lemma w4f_f36_mrd_kept : forall (W W' : Reusable.YA0n.world segs) (m m' : word -> option byte) a,
  Reusable.YA0n.wle W W' -> Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W') m' a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m a ->
  w4f_f36_K m m' a.
Proof.
  intros W W' m m' a Hle Hv E.
  assert (Hv' : Reusable.YA0n.w_H W' (Z_to_bv 64 a) = false).
  { unfold Reusable.YA0n.wle, Reusable.YA0i.hsub in Hle.
    destruct (Reusable.YA0n.w_H W' (Z_to_bv 64 a)) eqn:Eh; [| reflexivity].
    rewrite (Hle _ Eh) in Hv. discriminate. }
  rewrite (aview_vis_mrd W' m' a Hv'), (aview_vis_mrd W m a Hv) in E.
  change (lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a) = lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a)).
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 a)) as [b'|];
    destruct (lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 a)) as [b|]; cbn in E; try discriminate; [| reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma w4f_f36_bytes_tr : forall (m m' : word -> option byte) a (bs : list byte),
  (forall i, (i < length bs)%nat -> w4f_f36_K m m' (a + Z.of_nat i)) ->
  lib.Lib.Mem.bytes_at segs m a bs -> lib.Lib.Mem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs K (H1 & H2 & H3). split; [exact H1 |]. split; [exact H2 |].
  intros i Hi. unfold lib.Lib.Mem.wa. rewrite (K i Hi). exact (H3 i Hi).
Qed.

Lemma w4f_f36_q64_tr : forall (m m' : word -> option byte) a v,
  (forall x, a <= x < a + 8 -> w4f_f36_K m m' x) -> ACtlCutP.q64 m a v -> ACtlCutP.q64 m' a v.
Proof.
  intros m m' a v K H. unfold ACtlCutP.q64 in *. apply (w4f_f36_bytes_tr m m' a _); [| exact H].
  intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. apply K. lia.
Qed.

Lemma w4f_f36_spill_tr : forall R R0 (m m' : word -> option byte) off v A,
  getr R 9 = getr R0 9 -> ACtlCut.rgv R0 9 A -> 0 <= A < 2 ^ 63 -> 0 <= off < 2 ^ 62 ->
  (forall x, A + off <= x < A + off + 8 -> w4f_f36_K m m' x) ->
  ACtlCutP.spill R0 m off v -> ACtlCutP.spill R m' off v.
Proof.
  intros R R0 m m' off v A E9 HA HAb Hoff K Hs.
  pose proof (w4f_spill R0 m off v A Hs HA HAb Hoff) as Hq.
  exists A. split; [exact (w4f_rgv_tr R R0 9 A E9 HA) |].
  exact (w4f_f36_q64_tr m m' (A + off) v K Hq).
Qed.

Lemma w4f_f36_addr_tr : forall (m m' : word -> option byte) p n,
  (forall i, 0 <= i < n -> w4f_f36_K m m' (B.AsanRT.shadow_addr (p + i))) ->
  B.AsanRT.addressable m p n -> B.AsanRT.addressable m' p n.
Proof.
  intros m m' p n K (H1 & H2 & H3 & H4). split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  intros i Hi. destruct (H4 i Hi) as (Happ & b & Hb & Hok). split; [exact Happ |].
  exists b. split; [| exact Hok]. unfold lib.Lib.Mem.wa. rewrite <- Hb. exact (K i Hi).
Qed.

Lemma w4f_f36_stk_tr : forall (m m' : word -> option byte) lo hi,
  (forall x, lo <= x < hi -> w4f_f36_K m m' x) ->
  (forall x, lo <= x < hi -> ~ Reusable.YG0d.in_img segs x) ->
  lib.Lib.Frame.stk segs m lo hi -> lib.Lib.Frame.stk segs m' lo hi.
Proof.
  intros m m' lo hi K Ni (H1 & H2 & H3). split; [exact H1 |]. split; [exact H2 |].
  intros a Ha. destruct (H3 a Ha) as (_ & b & Hb).
  assert (Hm : lib.Lib.Mem.mrd segs m' (lib.Lib.Mem.wa a) = Some b) by (unfold lib.Lib.Mem.wa; rewrite (K a Ha); exact Hb).
  split; [| exists b; exact Hm].
  unfold lib.Lib.Mem.mrd in Hm. unfold wview.
  destruct (m' (lib.Lib.Mem.wa a)) as [b'|] eqn:Em; [discriminate |].
  exfalso. unfold lib.Lib.Mem.wa in Hm.
  assert (Hm' : lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a) = Some b) by exact Hm.
  rewrite (Reusable.YCbq.seg_rom_none segs a ltac:(lia) (Ni a Ha)) in Hm'. discriminate.
Qed.

(* [0x9f000, 0xa2000) is the image's third segment (ProgBridge.rsegs_spans). *)
Lemma w4f_f36_img3 : forall a, 0x9f000 <= a < 0xa2000 -> Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha.
  assert (Hin : In (0x9f000, 0x3000)
                  (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) B.Img0.rsegs))
    by (rewrite B.ProgBridge.rsegs_spans; right; right; left; reflexivity).
  apply in_map_iff in Hin as (s & Es & Hs). injection Es as E1 E2.
  exists s. split; [exact Hs | lia].
Qed.

(* The owned frame's shadow [Sfr fr, Sfr fr + 512) is present (the shadow arm of awr_byte's in_frames case). *)
Lemma w4f_f36_vis_fsh : forall cx ly3 S3 W3 mem3 md3 k fr a,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 512 ->
  Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 Ha.
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  refine (proj1 (Reusable.YCbq.awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _)).
  right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
  right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
  change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha. lia.
Qed.

(* Across the match call (apost_base's callee journal at [sp - 9136, sp)), every byte of the caller's stack above
   the callee window, of the owned frame and its shadow, of the turn's live block and of KIND_NAME's table keeps its
   lib/Lib read: the journal's view clauses at visible addresses (w4f_f36_mrd_kept). *)
Lemma w4f_f36_kept : forall cx ly3 S3 W3 m md k fr sp ly' S' W' m' md' phi n a,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m md k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  Reusable.YCbq.ajournal (SK := SK) segs B 9136 sp [] ly3 S3 W3 m md [] ly' S' W' m' md' 0 ->
  In (phi, n) (Reusable.YG0d.ablocks B ly3 S3) -> In (phi, n) (Reusable.YG0d.ablocks B ly' S') ->
  ACtlCut.c_sp cx - 4096 < sp -> sp <= ACtlCut.c_sp cx ->
  (sp <= a < ACtlCut.c_sp cx \/ fr <= a < fr + 4096 \/
   B.AsanRT.shadow_addr fr <= a < B.AsanRT.shadow_addr fr + 512 \/
   phi <= a < phi + Reusable.YG00.req_size n \/
   B.ACtlCutP.KNA.KIND_NAME <= a < B.ACtlCutP.KNA.KIND_NAME + 112) ->
  w4f_f36_K m m' a.
Proof.
  intros cx ly3 S3 W3 m md k fr sp ly' S' W' m' md' phi n a HJ HF HG1 HJc Hb3 Hb' Hsp1 Hsp2 Ha.
  pose proof HJc as (_ & _ & _ & Hwle & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hc.
  unfold Reusable.YCfn.LLVMF_STK in *.
  pose proof (w4f_frame_at cx ly3 S3 W3 m md k fr HJ HG1) as Efr.
  destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
  - destruct (w4f_vis_stack cx _ ly3 S3 W3 m md k a 1 HJ) as (_ & _ & V);
      [unfold Reusable.YCfn.LLVMF_STK; lia | lia | lia |].
    apply (w4f_f36_mrd_kept W3 W' m m' a Hwle (V a ltac:(lia))).
    apply G1; lia.
  - destruct (w4f_vis_frame cx ly3 S3 W3 m md k fr a 1 HJ HF HG1) as (_ & _ & V); [lia | lia | lia |].
    apply (w4f_f36_mrd_kept W3 W' m m' a Hwle (V a ltac:(lia))).
    apply (G4 6 (ACtlCut.c_fpos cx) a); [rewrite HF; left; reflexivity | left | intros (r & [] & _)].
    unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite <- Efr.
    change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
  - pose proof (w4f_f36_vis_fsh cx ly3 S3 W3 m md k fr a HJ HG1 Ha) as (V & _).
    apply (w4f_f36_mrd_kept W3 W' m m' a Hwle V).
    apply (G4 6 (ACtlCut.c_fpos cx) a); [rewrite HF; left; reflexivity | right | intros (r & [] & _)].
    unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
    change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
    unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha. lia.
  - destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 m md phi n HAR Hb3) as (_ & _ & _ & _ & Hp & _).
    destruct (Hp a Ha) as ((V & _) & _).
    apply (w4f_f36_mrd_kept W3 W' m m' a Hwle V).
    replace a with (phi + (a - phi)) by lia.
    apply (G2 phi n (a - phi) Hb3 Hb'); [lia | intros (r & [] & _)].
  - destruct (B.ProgBridge.img_vis_W W3) as (_ & _ & V).
    assert (Hk : B.ACtlCutP.KNA.KIND_NAME = 0x9f580) by reflexivity.
    apply (w4f_f36_mrd_kept W3 W' m m' a Hwle).
    { apply V. unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI. lia. }
    destruct (ctl_kind_name_not_owned a Ha) as (Ho & He).
    apply G3; [apply w4f_f36_img3; lia | exact Ho | exact He |].
    apply Reusable.YCbq.fp_spares_closed, Reusable.YCbq.sink_closed_nil.
Qed.

(* HB of a live block, from the AR's block law and the core's range_addressable (the block's shadow lies above
   the image, so a Some view there is a present byte). *)
Lemma w4f_f36_HB : forall ly S (W : Reusable.YA0n.world segs) m md p n,
  Reusable.YG0n.AR segs B ly S W m md -> In (p, n) (Reusable.YG0d.ablocks B ly S) ->
  ACtlCutP.HB m p n.
Proof.
  intros ly S W m md p n HAR Hin.
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly S W m md p n HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & Hn).
  pose proof (Reusable.YCbq.range_addressable_of_block segs B LAWS ly S W m md p n p (Reusable.YG00.req_size n)
    HAR Hin ltac:(lia) ltac:(lia)) as HRA.
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hc.
  assert (Ea : B.ACtlK.a_size n = Reusable.YG00.req_size n).
  { unfold B.ACtlK.a_size, Reusable.YG00.req_size.
    destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia. }
  assert (Er : 1 <= Reusable.YG00.req_size n /\ n <= Reusable.YG00.req_size n)
    by (apply Reusable.YCbq.req_size_pos; lia).
  split; [lia |]. rewrite Ea.
  split; [lia |]. split; [lia |].
  split; [unfold B.AsanRT.APPMEM_END; lia |].
  intros i Hi. split.
  - unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
      Reusable.YG0f.ASAN_CEIL in Happ.
    unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
  - destruct (HRA (p + i) ltac:(lia)) as (s & Hs & Hok).
    set (x := Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (p + i)) in Hs.
    assert (Hx : x = B.AsanRT.shadow_addr (p + i))
      by (unfold x, Reusable.YG0v.shadow_of_addr, B.AsanRT.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.ASAN_K; lia).
    assert (Hxb : 0x7fff8000 <= x < 2 ^ 64)
      by (unfold x, Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF; Z.div_mod_to_equations; lia).
    assert (Hni : ~ Reusable.YG0d.in_img segs x)
      by (intros Him; pose proof (segs_low x Him) as Hl; unfold Reusable.YG0f.kLowMemEnd in Hl; lia).
    assert (Hr : lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 x) = None)
      by exact (Reusable.YCbq.seg_rom_none segs x ltac:(lia) Hni).
    unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict in Hs. cbv beta in Hs.
    destruct (Reusable.YA0n.w_H W (Z_to_bv 64 x)).
    { rewrite Hr in Hs. discriminate. }
    destruct (m (Z_to_bv 64 x)) as [b|] eqn:Em; [| rewrite Hr in Hs; discriminate].
    cbn in Hs. injection Hs as Hs.
    exists b. split.
    + unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite <- Hx, Em. reflexivity.
    + assert (Hu : 0 <= bv_unsigned b < 256) by (apply (bv_unsigned_in_range 8 b)).
      assert (Es : bv_signed b = bv_unsigned b).
      { unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
        unfold Reusable.YG0v.saddr_ok in Hok. rewrite Z.mod_small; lia. }
      unfold B.AsanRT.shadow_ok. rewrite Es, Hs. unfold Reusable.YG0v.saddr_ok in Hok. lia.
Qed.

(* The bytes the cut bodies of the match call read: the spill area and saved registers [A, c_sp cx), the owned
   frame, the frame-shadow bytes the bodies' addressable facts read (offsets 328 .. 364), the turn's frame bytes at
   phi and KIND_NAME's table. *)
Definition w4f_f36_R (cx : ACtlCut.ctlcx) (A fr phi n x : Z) : Prop :=
  A <= x < ACtlCut.c_sp cx \/ fr <= x < fr + 4096 \/
  B.AsanRT.shadow_addr fr + 328 <= x < B.AsanRT.shadow_addr fr + 365 \/
  phi <= x < phi + n \/ B.ACtlCutP.KNA.KIND_NAME <= x < B.ACtlCutP.KNA.KIND_NAME + 112.

(* One leaf of a body conjunction, moved from (R0, m) to (R, m') (Kreg: the bytes of w4f_f36_R are kept). *)
Ltac w4f_f36_leaf Kreg A H :=
  first
  [ exact H
  | assumption
  | refine (w4f_rgv_tr _ _ _ _ _ H); assumption
  | (etransitivity; [eassumption | exact H])
  | (unfold Reusable.YG0d.spZ in H |- *; rewrite <- H; f_equal; assumption)
  | refine (w4f_f36_spill_tr _ _ _ _ _ _ A _ _ _ _ _ H);
      [assumption | assumption | lia | lia | intros ? ?; apply Kreg; unfold w4f_f36_R; lia]
  | refine (w4f_f36_q64_tr _ _ _ _ _ H); intros ? ?; apply Kreg; unfold w4f_f36_R; lia
  | refine (w4f_f36_bytes_tr _ _ _ _ _ H); intros ? Hi; apply Kreg; unfold w4f_f36_R;
      cbn [length] in Hi; rewrite ?lib.Lib.Mem.length_le8, ?lib.Lib.Mem.length_le4 in Hi; lia
  | refine (w4f_f36_addr_tr _ _ _ _ _ H); intros ? ?; apply Kreg; unfold w4f_f36_R, B.AsanRT.shadow_addr;
      Z.div_mod_to_equations; lia
  | refine (w4f_f36_stk_tr _ _ _ _ _ _ H); [intros ? ?; apply Kreg; unfold w4f_f36_R; lia | assumption] ].

Ltac w4f_f36_walk Kreg A H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "L" in let H2 := fresh "L" in destruct H as [H1 H2];
              split; [w4f_f36_walk Kreg A H1 | w4f_f36_walk Kreg A H2]
  | _ => w4f_f36_leaf Kreg A H
  end.

Lemma w4f_f36_LK_tr : forall cx fr j R R0 (m m' : word -> option byte) A phi n,
  getr R 9 = getr R0 9 -> getr R 27 = getr R0 27 -> ACtlCut.rgv R0 9 A ->
  0 <= A -> A + 448 <= ACtlCut.c_sp cx -> ACtlCut.c_sp cx <= 2 ^ 47 ->
  fr mod 32 = 0 -> 0 <= fr -> fr + 4096 <= 2 ^ 47 ->
  (forall x, w4f_f36_R cx A fr phi n x -> w4f_f36_K m m' x) ->
  (forall x, fr <= x < fr + 3136 -> ~ Reusable.YG0d.in_img segs x) ->
  B.AsanRT.addressable m' B.ACtlCutP.KNA.KIND_NAME 112 ->
  ACtlCutP.LK cx fr j R0 m -> ACtlCutP.LK cx fr j R m'.
Proof.
  intros cx fr j R R0 m m' A phi n E9 E27 HA HA0 HA1 Hsp Hfr32 Hfr0 Hfr1 Kreg NI KNA H.
  assert (LO : length (ACtlCutP.SM.OUR (ACtlCut.c_in cx)) = 6%nat)
    by (unfold ACtlCutP.SM.OUR; rewrite length_map, length_seq; reflexivity).
  assert (LK : length B.ACtlCutP.KNA.kind_name_bytes = 112%nat) by (vm_compute; reflexivity).
  unfold ACtlCutP.LK, ACtlCutP.OURb, ACtlCutP.FLI, ACtlCutP.RAD, ACtlCutP.KNT, ACtlCutP.fragb,
    ACtlCutP.FRAME_BYTES in *.
  w4f_f36_walk Kreg A H.
Qed.

Lemma w4f_f36_FTURN_tr : forall cx j phi R R0 (m m' : word -> option byte) A fr,
  getr R 9 = getr R0 9 -> ACtlCut.rgv R0 9 A ->
  0 <= A -> A + 448 <= ACtlCut.c_sp cx -> ACtlCut.c_sp cx <= 2 ^ 47 ->
  (forall x, w4f_f36_R cx A fr phi (ACtlCutP.SM.t_len (ACtlCut.c_in cx) j) x -> w4f_f36_K m m' x) ->
  ACtlCutP.FTURN cx j phi R0 m -> ACtlCutP.FTURN cx j phi R m'.
Proof.
  intros cx j phi R R0 m m' A fr E9 HA HA0 HA1 Hsp Kreg H.
  pose proof (proj2 (proj2 (proj2 H))) as Hlen.
  unfold ACtlCutP.FTURN in *.
  w4f_f36_walk Kreg A H.
Qed.

Lemma w4f_f36_IFS_tr : forall cx fr j R R0 (m m' : word -> option byte) A phi n,
  fr mod 32 = 0 -> 0 <= fr -> fr + 4096 <= 2 ^ 47 ->
  (forall x, w4f_f36_R cx A fr phi n x -> w4f_f36_K m m' x) ->
  ACtlCutP.IFS cx fr j R0 m -> ACtlCutP.IFS cx fr j R m'.
Proof.
  intros cx fr j R R0 m m' A phi n Hfr32 Hfr0 Hfr1 Kreg H.
  pose proof (B.Prog.Seg.Tac_ro.tr_ID_length (ACtlCut.c_in cx) j) as L1.
  pose proof (B.Prog.Seg.Tac_ro.tr_FG_length (ACtlCut.c_in cx) j) as L2.
  pose proof (B.Prog.Seg.Tac_ro.tr_body_length (ACtlCut.c_in cx) j) as L3.
  unfold ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.FGj, ACtlCutP.FSj, ACtlCutP.IDb, ACtlCutP.FGb, ACtlCutP.FSb,
    ACtlCutP.IDBe, ACtlCutP.FGBe, ACtlCutP.u32, ACtlCutP.b8 in *.
  w4f_f36_walk Kreg A H.
Qed.

Lemma w4f_f36_PTL_tr : forall cx j phi fr R R0 (m m' : word -> option byte) A,
  getr R 9 = getr R0 9 -> getr R 18 = getr R0 18 -> getr R 20 = getr R0 20 -> ACtlCut.rgv R0 9 A ->
  0 <= A -> A + 448 <= ACtlCut.c_sp cx -> ACtlCut.c_sp cx <= 2 ^ 47 ->
  0 <= fr -> fr + 4096 <= 2 ^ 47 ->
  (forall x, w4f_f36_R cx A fr phi (ACtlCutP.SM.t_len (ACtlCut.c_in cx) j) x -> w4f_f36_K m m' x) ->
  (forall x, fr <= x < fr + 3136 -> ~ Reusable.YG0d.in_img segs x) ->
  ACtlCutP.PTL cx j phi fr R0 m -> ACtlCutP.PTL cx j phi fr R m'.
Proof.
  intros cx j phi fr R R0 m m' A E9 E18 E20 HA HA0 HA1 Hsp Hfr0 Hfr1 Kreg NI H.
  pose proof H as (_ & _ & _ & _ & _ & _ & Hlen & _).
  unfold ACtlCutP.PTL, ACtlCutP.flen, ACtlCutP.FRAME_BYTES in *.
  w4f_f36_walk Kreg A H.
Qed.

Lemma w4f_f36_rgv_inj : forall R r a b, ACtlCut.rgv R r a -> ACtlCut.rgv R r b ->
  0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof.
  intros R r a b Ha Hb Ra Rb. unfold ACtlCut.rgv in *. rewrite Ha in Hb.
  apply (f_equal bv_unsigned) in Hb. rewrite !Z_to_bv_unsigned in Hb. unfold bv_wrap in Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. rewrite !Z.mod_small in Hb by lia. exact Hb.
Qed.

Lemma w4f_f36_FRAC_tr : forall cx fr sel R R0 (m m' : word -> option byte) A phi n,
  getr R 2 = getr R0 2 -> getr R 3 = getr R0 3 -> getr R 4 = getr R0 4 -> getr R 8 = getr R0 8 ->
  getr R 9 = getr R0 9 -> getr R 19 = getr R0 19 -> getr R 26 = getr R0 26 ->
  ACtlCut.rgv R0 9 A -> 0 <= A < 2 ^ 64 ->
  (forall x, w4f_f36_R cx A fr phi n x -> w4f_f36_K m m' x) ->
  (exists sh, lib.Lib.Mem.bytes_at segs m' (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) ->
  ACtlCutP.FRAC B cx fr sel R0 m -> ACtlCutP.FRAC B cx fr sel R m'.
Proof.
  intros cx fr sel R R0 m m' A phi n E2 E3 E4 E8 E9 E19 E26 HA HAb Kreg Hsh H.
  assert (LSB : length (ACtlCutP.saved_bytes cx) = 104%nat)
    by (unfold ACtlCutP.saved_bytes; rewrite !length_app, !lib.Lib.Mem.length_le8; reflexivity).
  destruct H as (A' & sp & H).
  pose proof H as (Hr2 & _ & HspZ & _ & _ & Hr9 & _ & _ & _ & _ & _ & HAle & HspA & _ & HA448 & _ & Hend & _).
  pose proof (bv_unsigned_in_range 64 (getr R0 2)) as Hspr.
  unfold bv_modulus in Hspr. cbn [Z.of_N] in Hspr. unfold Reusable.YG0d.spZ in HspZ.
  unfold ACtlCutP.ART.APPMEM_END in Hend.
  assert (EA : A' = A) by (apply (w4f_f36_rgv_inj R0 9 A' A Hr9 HA); lia).
  subst A'.
  exists A, sp. unfold ACtlCutP.FRAME_BYTES in *.
  w4f_f36_walk Kreg A H.
Qed.

(* ---- the match call's premises ---- *)



Lemma w4f_f36_t_ret : lib.Reusable.YK0s.ret_ok (Z_to_bv 64 0x82ca0).
Proof. unfold lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity. Qed.

(* ctl_base's arodata_okS, moved along the journal's image clause. *)
Lemma w4f_f36_arodata : forall cx own ly3 S3 W3 mem3 md3 k,
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx -> AJ cx own ly3 S3 W3 mem3 md3 k ->
  Reusable.YE01.arodata_okS segs B RLO RHI (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  destruct HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _) & _).
  exact (Reusable.APostBase.arodata_ok_journalP segs RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hro).
Qed.

(* The callee's stack window [sp - 9136, sp) under the journal's present window (afn_pre_at's argument). *)
Lemma w4f_f36_callwin : forall cx own ly3 S3 W3 mem3 md3 k sp,
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  sp mod 16 = 0 -> ACtlCut.c_sp cx - 4096 < sp -> sp <= ACtlCut.c_sp cx ->
  Reusable.YCbq.astk_ok 9136 ly3 sp /\
  (forall a, sp - 9136 <= a < sp -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k sp HJ Hal Hsp1 Hsp2.
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres &
    (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  unfold Reusable.YCfn.LLVMF_STK in *.
  split.
  - unfold Reusable.YCbq.astk_ok, Reusable.YG0f.ly_bot in *. rewrite Eslo, Eshi, Etop.
    assert (Has : Reusable.YG0d.ASTACK = 16384) by reflexivity. rewrite Has in Hbot.
    repeat split; lia.
  - intros a Ha. apply Hpres. lia.
Qed.

(* A visible byte string as the core's garr8 over the restricted memory (YD1w.garr8_of_blk's argument). *)
Lemma w4f_f36_garr8 : forall (H : word -> bool) (m : word -> option byte) q (pl : list byte),
  (forall i, (i < length pl)%nat -> H (Z_to_bv 64 (q + Z.of_nat i)) = false) ->
  lib.Lib.Mem.bytes_at segs m q pl ->
  lib.Reusable.YI00.garr8 segs (Reusable.YK04.mrestrict H m) q (map (fun b : byte => bv_unsigned b) pl).
Proof.
  intros H m q pl Hv (_ & _ & Hb) j Hj. rewrite length_map in Hj.
  assert (Hn : nth j (map (fun b : byte => bv_unsigned b) pl) 0 = bv_unsigned (nth j pl (Z_to_bv 8 0))).
  { rewrite <- (map_nth (fun b : byte => bv_unsigned b)). reflexivity. }
  rewrite Hn. pose proof (bv_unsigned_in_range 8 (nth j pl (Z_to_bv 8 0))) as R.
  change (bv_modulus 8) with 256 in R.
  split; [| lia].
  intros k Hk. replace k with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
  pose proof (Hb j Hj) as X. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa in X.
  rewrite (nth_error_nth' pl (Z_to_bv 8 0) Hj) in X.
  unfold lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict. cbv beta. rewrite (Hv j Hj).
  etransitivity; [exact X |]. f_equal.
  unfold lib.Reusable.YO0f.le_byte, lib.Reusable.YG0f.le_byte.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small _ 256 R).
  symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* ---- the match call and the cut B82ca0_at (shared by seg_F36 / seg_F36_c20 / seg_F36_c2c) ----
   At the callee entry 0x84e40 (ra = 0x82ca0, a0 = s2 = phi, a1 = s4 = len): TMATCH (afn_pre / apost_base form) with
   len := t_len j, fb := t_g j; its post's callee journal composes with the caller's (YCbq.ajournal_sub, the window
   [sp - 9136, sp) inside [c_sp cx - 32768, c_sp cx)); the bytes the body reads are kept (w4f_f36_kept), the
   registers it reads are callee-saved (aregs_preserved), a0 = want 0x9f620 len fb = t_want j, HB from the post's AR,
   ctl_rt_C by ctl_rt_C_of_AR (w4f_ctlrt). *)
Lemma w4f_f36_match : forall POST (j jn : nat) cx fr k ly3 S3 W3 (R : bvmap 5 word) m md phi,
  jn = ACtlCutP.ixn 0 [Z.of_nat j] ->
  ctl_from POST (ix C_B82ca0_at [Z.of_nat j]) ->
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m md k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  k <= 14 + 2 * Z.of_nat jn + 1 ->
  getr R 1 = Z_to_bv 64 0x82ca0 -> getr R 10 = getr R 18 -> getr R 11 = getr R 20 ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3)
    (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx) ++ [(phi, ACtlCutP.flen cx jn)]) ->
  ACtlCutP.FRAC B cx fr fr R m ->
  ACtlCut.c_n cx < 2 ^ 26 -> (jn <= 255)%nat ->
  ACtlCut.rgv R 18 phi -> ACtlCut.rgv R 20 (ACtlCutP.flen cx jn) ->
  ACtlCutP.FTURN cx jn phi R m -> ACtlCutP.LK cx fr jn R m ->
  ACtlCutP.spill R m 272 (ACtlCutP.SM.t_k (ACtlCut.c_in cx) jn) ->
  ACtlCut.rgv R 23 (ACtlCutP.SM.t_want_m (ACtlCut.c_in cx) jn) ->
  ACtlCutP.spill R m 152 (fr + 64) -> ACtlCutP.spill R m 160 (fr + 32) ->
  ACtlCutP.SM.t_want (ACtlCut.c_in cx) jn = ACtlCutP.SM.t_want_m (ACtlCut.c_in cx) jn ->
  ACtlCutP.IFS cx fr (S jn) R m -> ACtlCut.rgv R 22 1 ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x84e40 R m md) (POST cx).
Proof.
  intros POST j jn cx fr k ly3 S3 W3 R m md phi Ejn Hca0 HB HJ HF HG1 Hk Hra Ha0 Ha1 Hperm HFRAC Hn Hj Hr18 Hr20
    HFT HLK H272 Hr23 H152 H160 Hwant HIFS Hr22.
  pose proof HB as HB0.
  destruct HB0 as (((_ & _ & _ & Hgp0 & _) & _ & _ & _ & _ & _ & _ & _ & Hnev0 & Hbb0 & _) & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _ & _ & _ & _ & _ & Hsh & _).
  unfold ACtlCutP.ART.APPMEM_END, ACtlCutP.FRAME_BYTES in *.
  pose proof (w4f_frame_bounds cx ly3 S3 W3 m md k fr HJ HF HG1) as (Bfr1 & Bfr2).
  pose proof (w4f_frame_at cx ly3 S3 W3 m md k fr HJ HG1) as Efr.
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof (bv_unsigned_in_range 64 (getr R 2)) as Hspr.
  unfold bv_modulus in Hspr. cbn [Z.of_N] in Hspr. unfold Reusable.YG0d.spZ in HspZ.
  unfold ACtlCutP.flen in *.
  assert (Hin3 : In (phi, ACtlCutP.SM.t_len (ACtlCut.c_in cx) jn) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 m md phi _ HAR Hin3)
    as (_ & Hphi4096 & Hphic & _ & Hphip & _ & Hlen).
  unfold Reusable.YG00.MALLOC_MAX in Hlen.
  pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.SM.t_len (ACtlCut.c_in cx) jn) ltac:(lia)) as Hrq.
  pose proof (B.Prog.SlotInv.t_phi_length (ACtlCut.c_in cx) jn) as Hplen.
  destruct (w4f_f36_callwin cx _ ly3 S3 W3 m md k sp HJ Hspm ltac:(lia) ltac:(lia)) as (Hastk & Hwin).
  assert (NI : forall x, fr <= x < fr + 3136 -> ~ Reusable.YG0d.in_img segs x).
  { intros x Hx. apply (Reusable.YCbq.frm_img segs B LAWS ly3 S3 W3 m md 6 (ACtlCut.c_fpos cx) x HAR);
      [rewrite HF; left; reflexivity |].
    rewrite <- Efr. change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia. }
  eapply (Reusable.YA0n.SRr_bind segs).
  { apply (TMATCH ly3 S3 W3 R m md phi (ACtlCutP.SM.t_len (ACtlCut.c_in cx) jn)
             (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jn)).
    - exact HAR.
    - rewrite Hra. exact w4f_f36_t_ret.
    - unfold Reusable.YG0d.raZ. rewrite Hra. change (Z_to_bv 64 0x82ca0) with (lib.Lib.Mem.wa 0x82ca0).
      rewrite lib.Lib.Mem.wa_unsigned; lia.
    - rewrite Hr3. exact Hgp0.
    - exact Hr4.
    - unfold Reusable.YG0d.spZ. rewrite HspZ. exact Hastk.
    - intros a Ha. apply Hwin. unfold Reusable.YG0d.spZ in Ha. unfold B.Prog.C_reac_box_catalogue_match.CM_STK in Ha.
      lia.
    - exact HQT.
    - exact (w4f_f36_arodata cx _ ly3 S3 W3 m md k HB HJ).
    - rewrite Ha0. exact Hr18.
    - rewrite Ha1. exact Hr20.
    - lia.
    - lia.
    - unfold ACtlCutP.SM.t_g, B.Prog.SlotModel.fr50. rewrite length_firstn, length_app, repeat_length. lia.
    - intros H50. exists (ACtlCutP.SM.t_len (ACtlCut.c_in cx) jn). split; [exact Hin3 | lia].
    - intros H50. apply w4f_f36_garr8.
      + intros i Hi.
        assert (Lg : length (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jn) = 50%nat)
          by (unfold ACtlCutP.SM.t_g, B.Prog.SlotModel.fr50; rewrite length_firstn, length_app, repeat_length; lia).
        exact (proj1 (proj1 (Hphip (phi + Z.of_nat i) ltac:(lia)))).
      + exact (B.Prog.SlotInv.t_g_of_phi m phi (ACtlCut.c_in cx) jn (proj1 (proj2 (proj2 HFT))) H50).
    - intros a Ha. apply ctl_relro_not_owned. right.
      unfold B.Prog.C_reac_box_catalogue_match.A_CM_TBL, B.Prog.C_reac_box_catalogue_match.CM_ROWS in Ha.
      unfold B.Prog.SlotModel.CAT, B.Prog.SlotModel.CAT_ROW, B.Prog.SlotModel.CAT_N. lia.
    - rewrite HF. unfold ACtlCut.own6. vm_compute. reflexivity.
    - rewrite HF. unfold ACtlCut.own6. vm_compute. reflexivity.
    - rewrite HF. unfold ACtlCut.own6. vm_compute. reflexivity.
    - unfold B.Prog.C_reac_box_catalogue_match.EV_CM. unfold Reusable.YCfn.EV_LIB, Reusable.YG00.EV_MAX in *. lia.
    - unfold B.Prog.C_reac_box_catalogue_match.LIVE_CM.
      rewrite (Reusable.YCbq.blocks_bytes_bsum B ly3 S3), (Reusable.YCbq.bsum_perm _ _ Hperm), Reusable.YCbq.bsum_app.
      rewrite <- (Reusable.YCbq.blocks_bytes_bsum B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)).
      cbn [Reusable.YCbq.bsum fold_right fst snd].
      unfold Reusable.YCfn.LIVE_LIB, Reusable.YG01.LIVE_MAX in *. lia. }
  intros W' c' Hle Hpost.
  unfold B.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_post, Reusable.APostBase.apost_base in Hpost.
  destruct Hpost as (ly' & S' & regs' & m' & md' & -> & HJc & Hpres & Hw & Hperm').
  pose proof HJc as (HAR' & _ & _ & _ & _ & Hfrc & _).
  assert (Hin' : In (phi, ACtlCutP.SM.t_len (ACtlCut.c_in cx) jn) (Reusable.YG0d.ablocks B ly' S'))
    by (apply (Permutation_in _ (Permutation_sym Hperm')); exact Hin3).
  assert (HJ' : AJ cx (ACtlCut.own6 cx) ly' S' W' m' md' k).
  { replace k with (k + 0) by lia. change (ACtlCut.own6 cx) with ([] ++ ACtlCut.own6 cx).
    eapply (Reusable.YCbq.ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJc | | | intros a (r & [] & _)];
      unfold Reusable.YCfn.LLVMF_STK, B.Prog.C_reac_box_catalogue_match.CM_STK, Reusable.YG0d.spZ; lia. }
  assert (Kc : forall x, w4f_f36_R cx A fr phi (ACtlCutP.SM.t_len (ACtlCut.c_in cx) jn) x -> w4f_f36_K m m' x).
  { intros x Hx.
    apply (w4f_f36_kept cx ly3 S3 W3 m md k fr (Reusable.YG0d.spZ R) ly' S' W' m' md' phi
             (ACtlCutP.SM.t_len (ACtlCut.c_in cx) jn) x HJ HF HG1 HJc Hin3 Hin');
      [unfold Reusable.YG0d.spZ; lia | unfold Reusable.YG0d.spZ; lia |].
    unfold w4f_f36_R in Hx. unfold Reusable.YG0d.spZ. lia. }
  assert (Hsh' : exists sh, lib.Lib.Mem.bytes_at segs m' (ACtlCutP.Sfr fr) sh /\
                             length sh = Z.to_nat ACtlCutP.FRAME_SHADOW).
  { destruct Hsh as (sh & Hb & Hl). exists sh. split; [| exact Hl].
    apply (w4f_f36_bytes_tr m m' _ sh); [| exact Hb].
    intros i Hi. rewrite Hl in Hi. change (Z.to_nat ACtlCutP.FRAME_SHADOW) with 392%nat in Hi.
    apply (w4f_f36_kept cx ly3 S3 W3 m md k fr (Reusable.YG0d.spZ R) ly' S' W' m' md' phi
             (ACtlCutP.SM.t_len (ACtlCut.c_in cx) jn) _ HJ HF HG1 HJc Hin3 Hin');
      [unfold Reusable.YG0d.spZ; lia | unfold Reusable.YG0d.spZ; lia |].
    right; right; left. unfold ACtlCutP.Sfr. lia. }
  pose proof (ctl_kind_name_addressable ly' S' W' m' md' HAR') as KNA'.
  assert (E2 : getr regs' 2 = getr R 2) by exact (Hpres 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E3 : getr regs' 3 = getr R 3) by exact (Hpres 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E4 : getr regs' 4 = getr R 4) by exact (Hpres 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E8 : getr regs' 8 = getr R 8) by exact (Hpres 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E9 : getr regs' 9 = getr R 9) by exact (Hpres 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E18 : getr regs' 18 = getr R 18) by exact (Hpres 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E19 : getr regs' 19 = getr R 19) by exact (Hpres 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E20 : getr regs' 20 = getr R 20) by exact (Hpres 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E22 : getr regs' 22 = getr R 22) by exact (Hpres 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E23 : getr regs' 23 = getr R 23) by exact (Hpres 23 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E26 : getr regs' 26 = getr R 26) by exact (Hpres 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E27 : getr regs' 27 = getr R 27) by exact (Hpres 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (HFT' : ACtlCutP.FTURN cx jn phi regs' m')
    by exact (w4f_f36_FTURN_tr cx jn phi regs' R m m' A fr E9 Hr9 ltac:(lia) ltac:(lia) ltac:(lia) Kc HFT).
  assert (HLK' : ACtlCutP.LK cx fr jn regs' m')
    by exact (w4f_f36_LK_tr cx fr jn regs' R m m' A phi _ E9 E27 Hr9 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) Kc NI KNA' HLK).
  cbv beta. rewrite Hra.
  refine (Hca0 cx [Z.of_nat j] fr k ly' S' W' regs' m' md' HB HJ' _ HG1 _ _ (w4f_ctlrt _ _ _ _ _ _ _ _ HB HJ')).
  - rewrite Hfrc, HF. reflexivity.
  - cbn [ACtlCut.cut_kmax ACtlCut.ix_cut]. unfold ACtlCutP.C_B82ca0_at. cbn [ACtlCut.cut_kmax].
    rewrite <- Ejn. exact Hk.
  - cbn [ACtlCut.cut_body ACtlCut.ix_cut]. unfold ACtlCutP.C_B82ca0_at. cbn [ACtlCut.cut_body]. cbv zeta.
    rewrite <- Ejn.
    split; [reflexivity |].
    split; [exact (w4f_f36_FRAC_tr cx fr fr regs' R m m' A phi _ E2 E3 E4 E8 E9 E19 E26 Hr9 ltac:(lia) Kc Hsh'
                     HFRAC) |].
    unfold ACtlCutP.fcutp_body. exists phi.
    refine (conj _ (conj Hn (conj Hj (conj _ (conj _ (conj _ (conj HFT' _))))))).
    + exact (Permutation_trans Hperm' Hperm).
    + exact (w4f_f36_HB ly' S' W' m' md' phi _ HAR' Hin').
    + exact (w4f_rgv_tr regs' R 18 phi E18 Hr18).
    + exact (w4f_rgv_tr regs' R 20 _ E20 Hr20).
    + cbv beta.
      refine (conj HLK' (conj _ (conj I (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
        (conj Hwant (conj _ _)))))))))))))).
      * exact (w4f_f36_spill_tr regs' R m m' 272 _ A E9 Hr9 ltac:(lia) ltac:(lia)
                 (fun x Hx => Kc x ltac:(unfold w4f_f36_R; lia)) H272).
      * exact Hw.
      * exact (w4f_rgv_tr regs' R 23 _ E23 Hr23).
      * exact (w4f_rgv_tr regs' R 18 phi E18 Hr18).
      * exact (w4f_rgv_tr regs' R 20 _ E20 Hr20).
      * exact (w4f_f36_spill_tr regs' R m m' 152 _ A E9 Hr9 ltac:(lia) ltac:(lia)
                 (fun x Hx => Kc x ltac:(unfold w4f_f36_R; lia)) H152).
      * exact (w4f_f36_spill_tr regs' R m m' 160 _ A E9 Hr9 ltac:(lia) ltac:(lia)
                 (fun x Hx => Kc x ltac:(unfold w4f_f36_R; lia)) H160).
      * exact (proj1 (proj2 (proj2 HFT'))).
      * unfold ACtlCutP.flen. rewrite Hplen. rewrite Z2Nat.id by lia. lia.
      * pose proof HLK as (_ & _ & _ & HFLI).
        pose proof HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
          _ & Hstk & _).
        refine (w4f_f36_stk_tr m m' _ _ _ NI Hstk).
        intros x Hx. apply Kc. unfold w4f_f36_R. lia.
      * exact (w4f_f36_IFS_tr cx fr (S jn) regs' R m m' A phi _ Hfr32 ltac:(lia) ltac:(lia) Kc HIFS).
      * exact (w4f_rgv_tr regs' R 22 _ E22 Hr22).
Qed.

(* ---- the two shadow stores of the F36 stretches (f36_evt_pre_F: [Sfr fr + 8, Sfr fr + 12); f36_evt_c24_F:
   [Sfr fr + 4, Sfr fr + 5)): the owned frame's shadow, awr_byte's in_frames shadow arm ---- *)

(* A present byte off the image: its lib/Lib read is the memory's byte. *)
Lemma w4f_f36_present_of_mrd : forall (m : word -> option byte) a b,
  lib.Lib.Mem.mrd segs m (Z_to_bv 64 a) = Some b -> 0 <= a < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs a ->
  m (Z_to_bv 64 a) = Some b.
Proof.
  intros m a b Hb Ha Hn. unfold lib.Lib.Mem.mrd in Hb. destruct (m (Z_to_bv 64 a)) as [b'|]; [exact Hb |].
  exfalso. assert (Hb' : lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a) = Some b) by exact Hb.
  rewrite (Reusable.YCbq.seg_rom_none segs a Ha Hn) in Hb'. discriminate.
Qed.

(* A shadow address is not an image address (the image lies below kLowMemEnd = ASAN_K). *)
Lemma w4f_f36_sh_not_img : forall fr x, 0 <= fr -> B.AsanRT.shadow_addr fr <= x -> ~ Reusable.YG0d.in_img segs x.
Proof.
  intros fr x Hf Hx Him. pose proof (segs_low x Him) as Hl. unfold Reusable.YG0f.kLowMemEnd in Hl.
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hx. Z.div_mod_to_equations. lia.
Qed.

(* The owned frame's shadow bytes are a stack range and visible. *)
Lemma w4f_f36_stk_fsh : forall cx ly3 S3 W3 mem3 md3 k fr lo hi,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  B.AsanRT.shadow_addr fr <= lo -> hi <= B.AsanRT.shadow_addr fr + 512 -> 0 <= lo -> lo <= hi -> hi <= 2 ^ 64 ->
  lib.Lib.Frame.stk segs mem3 lo hi /\ B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo (hi - lo).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr lo hi HJ HG1 H1 H2 H3 H4 H5. split.
  - split; [lia |]. split; [lia |]. intros a Ha.
    destruct (w4f_f36_vis_fsh cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 ltac:(lia)) as (_ & b & Hb).
    unfold wview, lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. split; [discriminate | exists b; reflexivity].
  - split; [lia |]. split; [lia |]. intros a Ha.
    exact (proj1 (w4f_f36_vis_fsh cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 ltac:(lia))).
Qed.

(* Outside the written range a byte is kept. *)
Lemma w4f_f36_munchK : forall (m m' : word -> option byte) lo hi x,
  lib.Lib.Frame.munch [(lo, hi)] m m' -> 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> w4f_f36_K m m' x.
Proof.
  intros m m' lo hi x MU Hx Hn. unfold lib.Lib.Mem.mrd. rewrite (MU (Z_to_bv 64 x)); [reflexivity |].
  cbn [lib.Lib.Frame.outside]. split; [| exact I].
  change (Z_to_bv 64 x) with (lib.Lib.Mem.wa x). rewrite lib.Lib.Mem.wa_unsigned by lia. exact Hn.
Qed.

(* The journal across a store inside the owned frame's shadow (YCbq.ajournal_exec, write set [lo, hi)). *)
Lemma w4f_f36_aj_store : forall cx ly3 S3 W3 m m' md md' k fr lo hi,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m md k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  B.AsanRT.shadow_addr fr <= lo -> hi <= B.AsanRT.shadow_addr fr + 512 ->
  lib.Lib.Frame.munch [(lo, hi)] m m' -> lib.Lib.Frame.stk segs m' lo hi ->
  (forall x : word, Reusable.YA0n.w_H W3 x = true -> m' x = m x) ->
  Reusable.YK04.same_but_materialized md md' ->
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k.
Proof.
  intros cx ly3 S3 W3 m m' md md' k fr lo hi HJ HF HG1 Hlo Hhi MU ST Hhid Hs.
  pose proof (w4f_frame_bounds cx ly3 S3 W3 m md k fr HJ HF HG1) as (Bfr1 & Bfr2).
  pose proof (w4f_frame_at cx ly3 S3 W3 m md k fr HJ HG1) as Efr.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           (fun a => lo <= a < hi) HJ).
  - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU x); [reflexivity |].
    cbn [lib.Lib.Frame.outside]. split; [exact Hx | exact I].
  - intros x Hx. unfold Reusable.YK04.mrestrict in *.
    destruct (Reusable.YA0n.w_H W3 x) eqn:Eh; [exact Hx |].
    destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hl | Hl].
    { rewrite (MU x) by (cbn [lib.Lib.Frame.outside]; split; [lia | exact I]). exact Hx. }
    destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hh | Hh].
    2: { rewrite (MU x) by (cbn [lib.Lib.Frame.outside]; split; [lia | exact I]). exact Hx. }
    destruct ST as (_ & _ & ST). destruct (ST (bv_unsigned x) ltac:(lia)) as (_ & b & Hb).
    pose proof (bv_unsigned_in_range 64 x) as Hxr. unfold bv_modulus in Hxr. cbn [Z.of_N] in Hxr.
    unfold lib.Lib.Mem.wa in Hb.
    pose proof (w4f_f36_present_of_mrd m' (bv_unsigned x) b Hb ltac:(lia)
               (w4f_f36_sh_not_img fr (bv_unsigned x) ltac:(lia) ltac:(lia))) as Hp.
    rewrite Z_to_bv_bv_unsigned in Hp. rewrite Hp. discriminate.
  - exact Hhid.
  - exact Hs.
  - intros a Ha. right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |]. right.
    unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
    change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
    unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hlo, Hhi. lia.
Qed.

(* FRAC's 392 frame-shadow bytes after a store inside them: the bytes are present, so they are some list. *)
Lemma w4f_f36_sh_store : forall (m m' : word -> option byte) fr lo hi,
  (exists sh, lib.Lib.Mem.bytes_at segs m (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) ->
  lib.Lib.Frame.munch [(lo, hi)] m m' -> lib.Lib.Frame.stk segs m' lo hi -> 0 <= fr ->
  (exists sh, lib.Lib.Mem.bytes_at segs m' (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW).
Proof.
  intros m m' fr lo hi (sh & (Hb0 & Hb1 & Hb) & Hl) MU ST Hf.
  change (Z.to_nat ACtlCutP.FRAME_SHADOW) with 392%nat in *. rewrite Hl in Hb1, Hb.
  assert (Hst : lib.Lib.Frame.stk segs m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 392)).
  { split; [lia |]. split; [lia |]. intros a Ha.
    destruct (Z_lt_le_dec a lo) as [Hl1 | Hl1]; [| destruct (Z_lt_le_dec a hi) as [Hh1 | Hh1]].
    3, 1: (assert (K : w4f_f36_K m m' a) by (apply (w4f_f36_munchK m m' lo hi a MU); lia);
           pose proof (Hb (Z.to_nat (a - ACtlCutP.Sfr fr)) ltac:(lia)) as X;
           rewrite Z2Nat.id in X by lia;
           replace (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) with a in X by lia;
           assert (Hlt : (Z.to_nat (a - ACtlCutP.Sfr fr) < length sh)%nat) by lia;
           rewrite (nth_error_nth' sh (Z_to_bv 8 0) Hlt) in X;
           unfold lib.Lib.Mem.wa in X; rewrite <- K in X;
           split; [| exists (nth (Z.to_nat (a - ACtlCutP.Sfr fr)) sh (Z_to_bv 8 0)); exact X];
           unfold wview, lib.Lib.Mem.wa;
           rewrite (w4f_f36_present_of_mrd m' a _ X ltac:(lia)
                      (w4f_f36_sh_not_img fr a Hf ltac:(unfold ACtlCutP.Sfr in Ha; lia)));
           discriminate).
    destruct ST as (_ & _ & ST). exact (ST a ltac:(lia)). }
  destruct (lib.Lib.Frame.stk_bytes segs m' _ _ Hst ltac:(lia)) as (bs & Hlb & Hbs).
  exists bs. split; [exact Hbs |]. rewrite Hlb. f_equal. lia.
Qed.

(* Every byte the bodies read lies off the frame-shadow bytes [Sfr fr, Sfr fr + 328) the stores touch. *)
Lemma w4f_f36_R_off : forall cx A fr phi n np x,
  Reusable.YG0f.in_app fr 4096 -> Reusable.YG0f.in_app phi np -> n <= np ->
  lib.Reusable.YM05.alloc_ceiling <= A -> ACtlCut.c_sp cx <= 2 ^ 47 ->
  w4f_f36_R cx A fr phi n x ->
  0 <= x < 2 ^ 64 /\ ~ (ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 328).
Proof.
  intros cx A fr phi n np x Hfa Hpa Hnp HA Hsp Hx.
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hc.
  assert (Hk : B.ACtlCutP.KNA.KIND_NAME = 0x9f580) by reflexivity.
  unfold w4f_f36_R, ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.in_app,
    Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in *.
  Z.div_mod_to_equations. lia.
Qed.


(* ---------------------------------------------------------------------------------------------------------
   B82abc_at j (0x82abc) --S_F30--> B82af8_at j.
   0x82abc sb zero,56..59(s3); li a0,4; sb a0,60(s3); sb a0,66(s3) (the 36 output bytes [fr + 448, fr + 484) and the
   4 event bytes [fr + 528, fr + 532) usable); ld a4,192(s1); li a0,-1; sw a0,0(a4) ([fr + 528] := -1);
   mv a0,s2; mv a1,s4; ld a2,264(s1); ld a3,216(s1) (a0 = phi, a1 = len, a2 = our[] = fr + 2624, a3 = o = fr + 448);
   jal reac_ctrl_classify_box_frame (entry 0x837c4, ra 0x82af8) (UB Seg/F30.v:3-14).
   SINK BRANCHES: none (objdump L85500-L85514). *)

(* ---------------------------------------------------------------------------------------------------------
   B82abc_at j (0x82abc) --S_F30--> B82af8_at j.
   0x82abc sb zero,56..59(s3); li a0,4; sb a0,60(s3); sb a0,66(s3) (the 36 output bytes [fr + 448, fr + 484) and the
   4 event bytes [fr + 528, fr + 532) usable); ld a4,192(s1); li a0,-1; sw a0,0(a4) ([fr + 528] := -1);
   mv a0,s2; mv a1,s4; ld a2,264(s1); ld a3,216(s1) (a0 = phi, a1 = len, a2 = our[] = fr + 2624, a3 = o = fr + 448);
   jal reac_ctrl_classify_box_frame (entry 0x837c4, ra 0x82af8) (UB Seg/F30.v:3-14).
   SINK BRANCHES: none (objdump L85500-L85514). *)
(* Proof: 1. the stretch is B.Prog.Seg.F30F.f30s_evt_ro_F (ctl_rt carries ro_agree, not mem_inv) at
   RNG := RNG_W (w_H W3), lifted by w4f_f30_run; its footprint is the owned frame's shadow S(fr) + 56 .. 60, 66 and
   [fr + 528, fr + 532) (present and visible: AR_frames_law, w4f_f30_fpres) and the spills [A + 192 / 216 / 264]
   (the journal's present window); the journal crosses its writes by YCbq.ajournal_exec (in_frames, w4f_f30_awr).
   2. the call is TCLS at the run's end state with this cut's journal as C1; C2 (arodata_okS at the call state) from
   ctl_base's arodata_okS through the journal's image clause (RELRO_IMG; fp_spares by APostBase.ro_spares); C11 / C18 the bytes of
   t_g j = firstn 50 (t_phi j) (F30.f30_tg) and of OUR at their visible addresses (aview_vis_mrd); C12 / C14 / C17
   the owned frame's objects o, v, u with the shadow bytes the stretch just stored (o, v) or FLI's (u).
   3. the post: SRr_bind; the successor B82af8_at j at the post journal (Q2, k + 0 <= k); a0 = cl_r (t_cls j) (Q4,
   t_cls's definition); the 36 bytes at fr + 448 are t_B j (Q5); u32 (fr + 528) e (Q6, 0 <= e <= 5 by F32.f32_cls);
   every entry conjunct crosses the call by Q7 (acall_kept: the stack above sp, the owned frame and its shadow off
   o / v, the live block phi, the image bytes of KNT) read at VISIBLE bytes through aview_vis_mrd (w4f_f30_mrd_eq),
   then the stretch by its munch; the frame's stk and shadow bytes, HB's shadow (AR_shadow_law) and KNT's
   addressability (ctl_kind_name_addressable) from the post journal's AR; ctl_rt_C by w4f_ctlrt. *)
Lemma seg_F30 : forall POST (j : nat),
  ctl_from POST (ix C_B82af8_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82abc_at [Z.of_nat j]).
Proof.
  intros POST j Haf8 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  unfold ACtlCutP.C_B82abc_at in *. cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc
    ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  set (jj := ACtlCutP.ixn 0 [Z.of_nat j]) in *.
  unfold ACtlCutP.fcutp_body in HBODY.
  destruct HBODY as (HFRAC & phi & Hperm & Hn & Hj & HHB & Hr18 & Hr20 & HFT & HLK & HFTK & HIFS & H312).
  pose proof HFRAC as (A & sp & Hr2 & _ & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & _ & HAle & HspA &
    HfrA & HA448 & Hsp4096 & HspEnd & _).
  pose proof HLK as (Hj' & H240 & HOUR & HFLI).
  pose proof HFLI as (Hr27 & H168 & H96 & H112 & H120 & H128 & H136 & H144 & H152 & H280 & H160 & H176 & H192 & H200 &
    H216 & H208 & H104 & H256 & H264 & H288 & H296 & H304 & HAd2624 & Hfstk & HRAD & HKNT & H168b & H88).
  pose proof HFTK as (H184 & Hr22 & Hr24 & H272 & Hr25).
  pose proof HFT as (H224 & H232 & Hphi & Hplen).
  pose proof HHB as (Hphi0 & HAdphi).
  unfold ACtlCutP.flen in *.
  set (L := ACtlCutP.SM.t_len (ACtlCut.c_in cx) jj) in *.
  (* bounds *)
  pose proof (bv_unsigned_in_range 64 (getr regs3 2)) as Hspr. unfold bv_modulus in Hspr. cbn [Z.of_N] in Hspr.
  unfold Reusable.YG0d.spZ in HspZ.
  unfold ACtlCutP.FRAME_BYTES, ACtlCutP.ART.APPMEM_END in HfrA, HspEnd.
  pose proof (w4f_f30_frame_geo cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Gfr1 & Gfr2 & Gfr3).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as (Hceil & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (_ & _ & Hst1 & Hst2 & _) & _).
  unfold Reusable.YCfn.LLVMF_STK in Hst2, Hpres.
  pose proof (bv_unsigned_in_range 64 (getr (ACtlCut.c_regs cx) 2)) as Hcspr.
  unfold bv_modulus in Hcspr. cbn [Z.of_N] in Hcspr.
  assert (Hcsp : ACtlCut.c_sp cx = bv_unsigned (getr (ACtlCut.c_regs cx) 2)) by reflexivity.
  assert (Efr8 : fr = 8 * (ACtlCutP.Sfr fr - 0x7fff8000)).
  { assert (ESh : ACtlCutP.Sfr fr = fr / 8 + 0x7fff8000) by reflexivity.
    rewrite ESh. clear - Hfr32. Z.div_mod_to_equations. lia. }
  clear Hfr32.
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  (* the block phi *)
  assert (Hinb : In (phi, L) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (w4f_f30_blk cx ly3 S3 W3 mem3 md3 k fr _ _ HJ HF HG1 Hinb) as (Hb0 & Hbc & Hbapp & Hbfr & Hbvis).
  pose proof (B.Prog.Seg.F30.f30_phi_len (ACtlCut.c_in cx) jj) as HplenE. fold L in HplenE.
  assert (Hreq : Reusable.YG00.req_size L = B.ACtlK.a_size L)
    by (unfold Reusable.YG00.req_size, B.ACtlK.a_size; destruct (Z.eqb_spec L 0); lia).
  rewrite Hreq in Hbc, Hbapp, Hbfr, Hbvis.
  pose proof HAdphi as (Hp0 & _ & Hpe & _). unfold B.ACtlK.a_size in Hpe, Hbc, Hbapp, Hbfr, Hbvis, Hreq.
  unfold B.AsanRT.APPMEM_END in Hpe.
  (* presence of the owned frame and its shadow *)
  assert (FPR : forall a, fr <= a < fr + 4096 \/ ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
             Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a)
    by (intros a Ha; exact (w4f_f30_fpres cx ly3 S3 W3 mem3 md3 k fr a HJ HF HG1 Ha)).
  destruct (w4f_f30_rw1 _ mem3 (ACtlCutP.Sfr fr + 56) ltac:(lia) (FPR (ACtlCutP.Sfr fr + 56) ltac:(lia))) as (c56 & Hc56).
  destruct (w4f_f30_rw1 _ mem3 (ACtlCutP.Sfr fr + 57) ltac:(lia) (FPR (ACtlCutP.Sfr fr + 57) ltac:(lia))) as (c57 & Hc57).
  destruct (w4f_f30_rw1 _ mem3 (ACtlCutP.Sfr fr + 58) ltac:(lia) (FPR (ACtlCutP.Sfr fr + 58) ltac:(lia))) as (c58 & Hc58).
  destruct (w4f_f30_rw1 _ mem3 (ACtlCutP.Sfr fr + 59) ltac:(lia) (FPR (ACtlCutP.Sfr fr + 59) ltac:(lia))) as (c59 & Hc59).
  destruct (w4f_f30_rw1 _ mem3 (ACtlCutP.Sfr fr + 60) ltac:(lia) (FPR (ACtlCutP.Sfr fr + 60) ltac:(lia))) as (c60 & Hc60).
  destruct (w4f_f30_rw1 _ mem3 (ACtlCutP.Sfr fr + 66) ltac:(lia) (FPR (ACtlCutP.Sfr fr + 66) ltac:(lia))) as (c66 & Hc66).
  destruct (w4f_f30_rwn _ mem3 (fr + 528) 4 ltac:(lia) ltac:(lia) (fun i Hi => FPR (fr + 528 + i) ltac:(lia)))
    as (vb0 & Hvb0 & Hvb0l).
  assert (Q192 : ACtlCutP.q64 mem3 (A + 192) (fr + 528)) by (apply (w4f_spill regs3 mem3 192 _ A H192 Hr9); lia).
  assert (Q216 : ACtlCutP.q64 mem3 (A + 216) (fr + 448)) by (apply (w4f_spill regs3 mem3 216 _ A H216 Hr9); lia).
  assert (Q264 : ACtlCutP.q64 mem3 (A + 264) (fr + 2624)) by (apply (w4f_spill regs3 mem3 264 _ A H264 Hr9); lia).
  (* 1. the stretch 0x82abc -> 0x837c4 (f30s_evt_ro_F) *)
  apply w4f_enter.
  eapply w4f_f30_run.
  { eapply (B.Prog.Seg.F30F.f30s_evt_ro_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3 A
      (ACtlCutP.Sfr fr) (fr + 528) (fr + 448) (fr + 2624) phi L c56 c57 c58 c59 c60 c66 vb0
      (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    - exact Hr9.
    - exact Hr19.
    - exact Hr18.
    - exact Hr20.
    - split; lia.
    - split; lia.
    - split; lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - left. lia.
    - left. lia.
    - exact Hc56.
    - exact Hc57.
    - exact Hc58.
    - exact Hc59.
    - exact Hc60.
    - exact Hc66.
    - exact Hvb0.
    - exact Hvb0l.
    - exact (w4f_f30_ro8 _ _ _ Q192).
    - exact (w4f_f30_ro8 _ _ _ Q216).
    - exact (w4f_f30_ro8 _ _ _ Q264).
    - exact (proj2 (proj2 (proj2 HRT))).
    - unfold B.AsanRT.LOWMEM_END. lia.
    - rewrite w4f_gt_img_top. lia.
    - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (FPR a ltac:(lia))).
    - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (FPR a ltac:(lia))).
    - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres a ltac:(lia))).
    - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres a ltac:(lia))).
    - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres a ltac:(lia))).
    - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (FPR a ltac:(lia))). }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms1 md1 (m1 & -> & MU & WM & HRO1 & (vb' & Hvb' & Hvbl) & B56 & B57 & B58 & B59 & B60 & B66) Hs1 Hhid1 Hgr1.
  apply w4f_exit.
  match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R1 := R) end.
  (* the stretch writes only S(fr) + 56 .. 60, S(fr) + 66 and [fr + 528, fr + 532) *)
  assert (K01 : forall x, 0 <= x < 2 ^ 64 -> ~ (ACtlCutP.Sfr fr + 56 <= x < ACtlCutP.Sfr fr + 67) ->
             ~ (fr + 528 <= x < fr + 532) -> m1 (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x)).
  { intros x Hx H1 H2. apply MU. rewrite lib.Lib.MState.unsigned_lit by lia.
    cbn [lib.Lib.Frame.outside]. repeat split; lia. }
  assert (K01r : forall x, 0 <= x < 2 ^ 64 -> ~ (ACtlCutP.Sfr fr + 56 <= x < ACtlCutP.Sfr fr + 67) ->
             ~ (fr + 528 <= x < fr + 532) ->
             lib.Lib.Mem.mrd B.Img0.rsegs m1 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx H1 H2. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite (K01 x Hx H1 H2). reflexivity. }
  (* the journal across the stretch's writes (owned frame and its shadow) *)
  assert (HJ1 : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m1 md1 k).
  { apply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun a => ACtlCutP.Sfr fr + 56 <= a < ACtlCutP.Sfr fr + 61 \/ ACtlCutP.Sfr fr + 66 <= a < ACtlCutP.Sfr fr + 67 \/
                fr + 528 <= a < fr + 532) HJ).
    - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU x); [reflexivity |].
      cbn [lib.Lib.Frame.outside]. repeat split; intro; apply Hx; lia.
    - exact Hgr1.
    - exact Hhid1.
    - exact Hs1.
    - intros a Ha. apply (w4f_f30_awr cx ly3 S3 W3 mem3 md3 k fr a HJ HG1). lia. }
  (* the read-only data at the call state (TCLS C2) *)
  assert (HRD1 : Reusable.YE01.arodata_okS segs B RLO RHI (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) m1)).
  { pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _) & _).
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Himgk & _).
    intros a Hdom Hno Her.
    assert (Himg : Reusable.YG0d.in_img segs a).
    { destruct Hdom as [(s & Hs & _ & Hb) | Hr]; [exists s; split; [exact Hs | exact Hb] | exact (RELRO_IMG a Hr)]. }
    pose proof (w4f_f30_img_bounds a Himg) as Hab.
    rewrite (w4f_f30_aview_eq _ mem3 m1 a (K01 a ltac:(lia) ltac:(lia) ltac:(lia))).
    rewrite (Himgk a Himg Hno Her (Reusable.APostBase.ro_spares segs RLO RHI FP a Hdom)).
    exact (Hro a Hdom Hno Her). }
  (* the call's registers *)
  assert (ER1 : getr R1 1 = Z_to_bv 64 0x82af8) by reflexivity.
  assert (HspR : Reusable.YG0d.spZ R1 = sp) by (unfold Reusable.YG0d.spZ; rewrite <- HspZ; reflexivity).
  pose proof HB as (((_ & _ & _ & Hgp & _) & _) & _).
  (* addressable bytes made by the stretch: [fr + 448, fr + 484) and [fr + 528, fr + 532) *)
  assert (AD448 : B.AsanRT.addressable m1 (fr + 448) 36).
  { split; [lia|]. split; [lia|]. split; [unfold B.AsanRT.APPMEM_END; lia|].
    intros i Hi. split; [unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END; lia|].
    rewrite (w4f_f30_sh_in' fr _ (fr + 448 + i) Efr8). replace (fr + 448 + i - fr) with (448 + i) by lia.
    assert (Hq : (448 + i) / 8 = 56 \/ (448 + i) / 8 = 57 \/ (448 + i) / 8 = 58 \/ (448 + i) / 8 = 59 \/
                 (448 + i) / 8 = 60) by (Z.div_mod_to_equations; lia).
    unfold B.AsanRT.shadow_ok.
    destruct Hq as [Hq | [Hq | [Hq | [Hq | Hq]]]]; rewrite Hq;
      [destruct B56 as (b & Hb & Hs) | destruct B57 as (b & Hb & Hs) | destruct B58 as (b & Hb & Hs) |
       destruct B59 as (b & Hb & Hs) | destruct B60 as (b & Hb & Hs)];
      exists b; (split; [exact Hb|]); rewrite Hs; [left; reflexivity .. |].
    right. split; [| lia]. Z.div_mod_to_equations. lia. }
  assert (AD528 : B.AsanRT.addressable m1 (fr + 528) 4).
  { split; [lia|]. split; [lia|]. split; [unfold B.AsanRT.APPMEM_END; lia|].
    intros i Hi. split; [unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END; lia|].
    rewrite (w4f_f30_sh_in' fr _ (fr + 528 + i) Efr8). replace ((fr + 528 + i - fr) / 8) with 66 by (Z.div_mod_to_equations; lia).
    destruct B66 as (b & Hb & Hs). exists b. split; [exact Hb|]. unfold B.AsanRT.shadow_ok. rewrite Hs.
    right. split; [| lia]. Z.div_mod_to_equations. lia. }
  assert (AD2624 : B.AsanRT.addressable m1 (fr + 2624) 6).
  { apply (w4f_f30_addr mem3 m1 _ _ HAd2624). intros x Hx. rewrite (w4f_f30_sh_in' fr _ x Efr8).
    apply K01r; Z.div_mod_to_equations; lia. }
  assert (SHV : forall x, fr <= x < fr + 4096 ->
             Reusable.YA0n.w_H W3 (Z_to_bv 64 (B.AsanRT.shadow_addr x)) = false).
  { intros x Hx. rewrite (w4f_f30_sh_in' fr _ x Efr8). apply (proj1 (FPR (ACtlCutP.Sfr fr + (x - fr) / 8) ltac:(Z.div_mod_to_equations; lia))). }
  assert (AFO : forall p n, fr <= p -> p + n <= fr + 4096 -> p mod 8 = 0 -> B.AsanRT.addressable m1 p n ->
             Reusable.APostBase.afobj segs B ly3 S3 W3 m1 p n).
  { intros p n Hp1 Hp2 Hp8 Had. split; [| split; [exact Hp8 |]].
    - exists 6, (ACtlCut.c_fpos cx). split; [rewrite HF; left; reflexivity|]. split; [lia|]. rewrite <- Efr.
      change (Reusable.YG00.fs_frame_bytes 6) with 4096. split; [rewrite Efr8, Z.mul_comm; apply Z_mod_mult | lia].
    - apply (w4f_f30_range_of_addr W3 m1 _ _ Had). intros x Hx. apply SHV. pose proof Had as (_ & Hn0 & _). lia. }
  assert (Hphi1 : lib.Lib.Mem.bytes_at B.Img0.rsegs m1 phi (ACtlCutP.SM.t_phi (ACtlCut.c_in cx) jj)).
  { apply (w4f_f30_bytes mem3 m1 _ _ Hphi). intros x Hx. apply K01r; lia. }
  assert (HOUR1 : lib.Lib.Mem.bytes_at B.Img0.rsegs m1 (fr + 2624) (ACtlCutP.SM.OUR (ACtlCut.c_in cx))).
  { apply (w4f_f30_bytes mem3 m1 _ _ HOUR). rewrite ACtlCutP.SM.OUR_length. intros x Hx. apply K01r; lia. }
  (* 2. the call: reac_ctrl_classify_box_frame by TCLS, in the caller-journal form *)
  eapply (Reusable.YA0n.SRr_bind segs).
  { eapply (TCLS Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
      (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 W3 m1 md1 k R1 phi L
      (fr + 2624) (fr + 448) (fr + 528) (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) (ACtlCutP.SM.OUR (ACtlCut.c_in cx))).
    - rewrite <- SK_TFIB. exact HJ1.
    - exact HRD1.
    - rewrite ER1. reflexivity.
    - unfold Reusable.YG0d.raZ. rewrite ER1. rewrite lib.Lib.MState.unsigned_lit by lia. lia.
    - transitivity (getr regs3 3); [reflexivity |]. rewrite Hr3. exact Hgp.
    - transitivity (getr regs3 4); [reflexivity | exact Hr4].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - rewrite HspR. pose proof HFRAC as (A0 & sp0 & _ & Hm0 & HspZ0 & _).
      unfold Reusable.YG0d.spZ in HspZ0. rewrite HspZ in HspZ0. subst sp0. exact Hm0.
    - rewrite HspR. unfold Reusable.YCfn.LLVMF_STK, B.Prog.C_reac_ctrl_classify_box_frame.REAC_CTRL_CLASSIFY_BOX_FRAME_STK. lia.
    - rewrite HspR. lia.
    - rewrite HF. unfold ACtlCut.own6. vm_compute. reflexivity.
    - intros H50. exists L. split; [exact Hinb | rewrite Hreq; lia].
    - unfold ACtlCutP.SM.t_g. apply ACtlCutP.SM.fr50_length.
    - intros H50 i Hi.
      rewrite (w4f_f30_aview_bytes W3 m1 phi (ACtlCutP.SM.t_phi (ACtlCut.c_in cx) jj) i Hphi1 ltac:(lia)
        (Hbvis (phi + Z.of_nat i) ltac:(lia))).
      rewrite (B.Prog.Seg.F30.f30_tg _ _ H50). unfold RPS.cp_v, RPS.cp_b.
      rewrite B.Prog.Seg.F32.f32_nth_firstn by lia. reflexivity.
    - apply AFO; [lia | lia | rewrite Efr8; apply w4f_f30_mod8; reflexivity | exact AD448].
    - intros a Ha. apply (w4f_f30_awr cx ly3 S3 W3 m1 md1 k fr a HJ1 HG1). lia.
    - apply AFO; [lia | lia | rewrite Efr8; apply w4f_f30_mod8; reflexivity | exact AD528].
    - intros a Ha. apply (w4f_f30_awr cx ly3 S3 W3 m1 md1 k fr a HJ1 HG1). lia.
    - apply ACtlCutP.SM.OUR_length.
    - intros _. apply AFO; [lia | lia | rewrite Efr8; apply w4f_f30_mod8; reflexivity | exact AD2624].
    - intros _ i Hi.
      rewrite (w4f_f30_aview_bytes W3 m1 (fr + 2624) (ACtlCutP.SM.OUR (ACtlCut.c_in cx)) i HOUR1 ltac:(rewrite ACtlCutP.SM.OUR_length; lia)
        (proj1 (FPR (fr + 2624 + Z.of_nat i) ltac:(lia)))).
      reflexivity.
    - left. lia.
    - right. lia.
    - left. lia.
    - lia. }
  intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hpres2 & HF2 & Hbl2 & Q4 & Q5 & Q6 & Q7).
  rewrite <- SK_TFIB in HJ2.
  assert (HJ2' : AJ cx (ACtlCut.own6 cx) ly2 S2 W2 mem2 md2 k)
    by (eapply Reusable.YCbq.ajournal_mono_k;
        [exact HJ2 | match goal with |- _ + ?e <= _ => assert (Ee : e = 0) by reflexivity; lia end]).
  assert (HF2' : Reusable.YG01.frames S2 = ACtlCut.own6 cx) by (rewrite HF2; exact HF).
  pose proof (proj1 HJ2') as HAR2.
  (* the registers the body reads are callee-saved: kept by the call (aregs_preserved) and by the stretch *)
  assert (RP : forall r, Reusable.YG0d.acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r)).
  { intros r Hr. rewrite (Hpres2 r Hr). unfold Reusable.YG0d.acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (clear - Hr; lia).
    repeat (destruct Hr' as [-> | Hr']; [reflexivity |]). subst r. reflexivity. }
  assert (E2 : getr regs2 2 = getr regs3 2) by exact (RP 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E3 : getr regs2 3 = getr regs3 3) by exact (RP 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E4 : getr regs2 4 = getr regs3 4) by exact (RP 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E8 : getr regs2 8 = getr regs3 8) by exact (RP 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E9 : getr regs2 9 = getr regs3 9) by exact (RP 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E18 : getr regs2 18 = getr regs3 18) by exact (RP 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E19 : getr regs2 19 = getr regs3 19) by exact (RP 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E20 : getr regs2 20 = getr regs3 20) by exact (RP 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E22 : getr regs2 22 = getr regs3 22) by exact (RP 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E24 : getr regs2 24 = getr regs3 24) by exact (RP 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E25 : getr regs2 25 = getr regs3 25) by exact (RP 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E26 : getr regs2 26 = getr regs3 26) by exact (RP 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E27 : getr regs2 27 = getr regs3 27) by exact (RP 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  (* the raw reads the call keeps (TCLS's Q7, acall_kept, through aview_vis_mrd at visible bytes) *)
  pose proof Q7 as (K1 & K2 & K3 & K4 & _ & _).
  rewrite HspR in K1.
  assert (VIS2 : forall x, Reusable.YA0n.w_H W3 x = false -> Reusable.YA0n.w_H W2 x = false).
  { intros x Hx. destruct (Reusable.YA0n.w_H W2 x) eqn:E; [|reflexivity]. rewrite (Hle x E) in Hx. discriminate. }
  assert (K12 : forall x, (sp <= x < ACtlCut.c_sp cx) \/ (fr <= x < fr + 4096 /\ ~ (fr + 448 <= x < fr + 536)) \/
       (ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 512) \/ (phi <= x < phi + Z.max L 1) \/
       (B.ACtlCutP.KNA.KIND_NAME <= x < B.ACtlCutP.KNA.KIND_NAME + 112) ->
       lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs m1 (lib.Lib.Mem.wa x)).
  { intros x Hx. apply (w4f_f30_mrd_eq W3 W2 m1 mem2 x Hle).
    - destruct Hx as [Hx | [Hx | [Hx | [Hx | Hx]]]].
      + exact (proj1 (Hpres x ltac:(lia))).
      + exact (proj1 (FPR x ltac:(lia))).
      + exact (proj1 (FPR x ltac:(lia))).
      + exact (Hbvis x ltac:(lia)).
      + pose proof (B.ProgBridge.img_vis_W W3) as (_ & _ & Hv). apply Hv.
        unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI, B.ACtlCutP.KNA.KIND_NAME in *. lia.
    - destruct Hx as [Hx | [Hx | [Hx | [Hx | Hx]]]].
      + apply K1; lia.
      + apply (K4 6 (ACtlCut.c_fpos cx)); [rewrite HF; left; reflexivity | left | intros [E | (_ & E)]; lia].
        unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite <- Efr.
        change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
      + apply (K4 6 (ACtlCut.c_fpos cx)); [rewrite HF; left; reflexivity | right | intros [E | (_ & E)]; lia].
        unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
        change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
        assert (Reusable.YG0f.shadow_addr fr = ACtlCutP.Sfr fr)
          by (unfold ACtlCutP.Sfr, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, B.AsanRT.shadow_addr,
                B.AsanRT.ASAN_K; lia).
        lia.
      + replace x with (phi + (x - phi)) by lia.
        apply (K2 phi L); [exact Hinb | rewrite Hreq; lia | intros [E | (_ & E)]; lia].
      + apply K3.
        * apply w4f_f30_kn_img. unfold B.ACtlCutP.KNA.KIND_NAME in Hx. lia.
        * exact (proj1 (ctl_kind_name_not_owned x Hx)).
        * exact (proj2 (ctl_kind_name_not_owned x Hx)). }
  assert (KEEP : forall x, (sp <= x < ACtlCut.c_sp cx) \/ (fr <= x < fr + 4096 /\ ~ (fr + 448 <= x < fr + 536)) \/
       (ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 512 /\ ~ (ACtlCutP.Sfr fr + 56 <= x < ACtlCutP.Sfr fr + 67)) \/
       (phi <= x < phi + Z.max L 1) \/ (B.ACtlCutP.KNA.KIND_NAME <= x < B.ACtlCutP.KNA.KIND_NAME + 112) ->
       lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa x) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (lib.Lib.Mem.wa x)).
  { intros x Hx. destruct Hx as [Hx | [Hx | [(Hx & Hx') | [Hx | Hx]]]];
      (rewrite K12; [| first [ left; exact Hx | right; left; exact Hx | right; right; left; exact Hx |
                               right; right; right; left; exact Hx | right; right; right; right; exact Hx ]]);
      apply K01r; unfold B.ACtlCutP.KNA.KIND_NAME in *; lia. }
  (* the owned frame after the call (the post journal's AR) *)
  assert (FPR2 : forall a, fr <= a < fr + 4096 \/ ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
             Reusable.YG0n.apresent (Reusable.YA0n.w_H W2) mem2 a)
    by (intros a Ha; exact (w4f_f30_fpres cx ly2 S2 W2 mem2 md2 k fr a HJ2' HF2' HG1 Ha)).
  assert (HSTK2 : lib.Lib.Frame.stk segs mem2 fr (fr + ACtlCutP.FRAME_BYTES)).
  { apply (w4f_f30_stk (Reusable.YA0n.w_H W2)); [lia | unfold ACtlCutP.FRAME_BYTES; lia |].
    intros a Ha. apply FPR2. unfold ACtlCutP.FRAME_BYTES in Ha. lia. }
  assert (HSH2 : exists sh, lib.Lib.Mem.bytes_at segs mem2 (ACtlCutP.Sfr fr) sh /\
             length sh = Z.to_nat ACtlCutP.FRAME_SHADOW).
  { change (Z.to_nat ACtlCutP.FRAME_SHADOW) with 392%nat.
    apply (w4f_f30_bytes_ex mem2 (ACtlCutP.Sfr fr) 392); [lia | lia |].
    intros i Hi. destruct (FPR2 (ACtlCutP.Sfr fr + Z.of_nat i) ltac:(lia)) as (_ & b & Hb).
    exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity. }
  assert (SPILL : forall off v, ACtlCutP.spill regs3 mem3 off v -> 0 <= off <= 440 ->
             ACtlCutP.spill regs2 mem2 off v).
  { intros off v Hs Hoff. apply (w4f_f30_spill regs3 regs2 mem3 mem2 off v A Hs Hr9 E9); [lia | lia |].
    intros x Hx. apply KEEP. left. lia. }
  assert (ADDR : forall p n, B.AsanRT.addressable mem3 p n -> fr + 2600 <= p -> p + n <= fr + 3136 ->
             B.AsanRT.addressable mem2 p n).
  { intros p n Had Hp1 Hp2. apply (w4f_f30_addr mem3 mem2 _ _ Had). intros x Hx.
    rewrite (w4f_f30_sh_in' fr _ x Efr8). apply KEEP. right; right; left. Z.div_mod_to_equations. lia. }
  assert (HOUR2 : ACtlCutP.OURb cx fr mem2).
  { unfold ACtlCutP.OURb in *. apply (w4f_f30_bytes mem3 mem2 _ _ HOUR). rewrite ACtlCutP.SM.OUR_length.
    intros x Hx. apply KEEP. right; left. lia. }
  assert (HKNT2 : ACtlCutP.KNT mem2).
  { pose proof HKNT as (Kb & _). split.
    - apply (w4f_f30_bytes mem3 mem2 _ _ Kb).
      assert (HL : length B.ACtlCutP.KNA.kind_name_bytes = 112%nat) by reflexivity.
      rewrite HL. intros x Hx. apply KEEP. right; right; right; right. lia.
    - exact (ctl_kind_name_addressable _ _ _ _ _ HAR2). }
  assert (HLK2 : ACtlCutP.LK cx fr jj regs2 mem2)
    by exact (w4f_f30_LK_mem cx fr jj regs3 regs2 mem3 mem2 HLK E27 SPILL HOUR2 ADDR HSTK2 HKNT2).
  (* 3. the successor B82af8_at j *)
  rewrite ER1.
  change (Reusable.YA0n.SRr segs W2 (Reusable.YG0d.cfg_at segs 0x82af8 regs2 mem2 md2) (POST cx)).
  apply (Haf8 cx [Z.of_nat j] fr k ly2 S2 W2 regs2 mem2 md2 HB HJ2' HF2' HG1 Hk);
    [| exact (w4f_ctlrt _ _ _ _ _ _ _ _ HB HJ2')].
  cbn [ACtlCut.cut_body ACtlCut.ix_cut]. unfold ACtlCutP.C_B82af8_at. cbn [ACtlCut.cut_body]. cbv zeta. fold jj.
  unfold ACtlCutP.flen. fold L.
  split; [reflexivity |].
  exists phi.
  refine (conj _ (conj _ (conj Hn (conj Hj (conj _ (conj HLK2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))))))).
  - rewrite Hbl2. exact Hperm.
  - apply (w4f_FRAC_tr _ _ _ regs2 regs3 _ E2 E3 E4 E8 E9 E19 E26).
    apply (w4f_f30_FRAC_mem cx fr fr regs3 mem3 mem2 A HFRAC Hr9); [lia | | exact HSH2].
    intros x Hx. apply KEEP. lia.
  - split; [exact Hphi0 |].
    destruct (Reusable.YG0d.al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 phi L HAR2 ltac:(rewrite Hbl2; exact Hinb))
      as (Hbs2 & _).
    unfold B.ACtlK.a_size.
    apply (w4f_f30_addr_of_range W2 mem2 phi (Z.max L 1)
      (Reusable.YG0v.block_shadow_range _ _ _ _ phi (Z.max L 1) Hbs2 ltac:(lia) ltac:(rewrite Hreq; lia)));
      [lia | lia | unfold B.AsanRT.APPMEM_END; lia |].
    intros x Hx. pose proof HAdphi as (_ & _ & _ & Ha). unfold B.ACtlK.a_size in Ha.
    pose proof (Ha (x - phi) ltac:(lia)) as (Hx' & _). replace (phi + (x - phi)) with x in Hx' by lia. exact Hx'.
  - exact (conj (SPILL _ _ H184 ltac:(lia)) (conj (w4f_rgv_tr regs2 regs3 22 _ E22 Hr22)
      (conj (w4f_rgv_tr regs2 regs3 24 _ E24 Hr24) (conj (SPILL _ _ H272 ltac:(lia))
      (w4f_rgv_tr regs2 regs3 25 _ E25 Hr25))))).
  - exact Q4.
  - exact (SPILL _ _ H144 ltac:(lia)).
  - exact (SPILL _ _ H264 ltac:(lia)).
  - exact (SPILL _ _ H216 ltac:(lia)).
  - unfold ACtlCutP.SM.t_B.
    apply (w4f_f30_bytes_of_aview W2 mem2); [lia | rewrite RPS.ctrlparse_length; lia |].
    intros i Hi. rewrite RPS.ctrlparse_length in Hi. exact (Q5 i Hi).
  - apply (w4f_f30_addr m1 mem2 (fr + 452) 6
      (w4f_f30_addr_sub m1 (fr + 448) 36 (fr + 452) 6 AD448 ltac:(lia) ltac:(lia) ltac:(lia))).
    intros x Hx. rewrite (w4f_f30_sh_in' fr _ x Efr8). apply K12. right; right; left. Z.div_mod_to_equations. lia.
  - exact (ADDR _ _ HAd2624 ltac:(lia) ltac:(lia)).
  - exact (SPILL _ _ H184 ltac:(lia)).
  - exact (w4f_rgv_tr regs2 regs3 25 _ E25 Hr25).
  - exact (SPILL _ _ H192 ltac:(lia)).
  - intros e He. destruct (B.Prog.Seg.F32.f32_cls _ _ _ He) as (_ & _ & Her).
    apply (w4f_f30_u32 (Reusable.YA0n.w_H W2) mem2 (fr + 528) e Her ltac:(lia) ltac:(lia)).
    + intros kk Hkk. apply VIS2. exact (proj1 (FPR (fr + 528 + Z.of_nat kk) ltac:(lia))).
    + exact (Q6 e He).
  - refine (conj (w4f_rgv_tr regs2 regs3 18 _ E18 Hr18) (conj (w4f_rgv_tr regs2 regs3 24 _ E24 Hr24)
      (conj (w4f_rgv_tr regs2 regs3 20 _ E20 Hr20) (conj (SPILL _ _ H152 ltac:(lia)) (conj (SPILL _ _ H312 ltac:(lia))
      (conj _ (conj Hplen (conj (SPILL _ _ H160 ltac:(lia)) HSTK2)))))))).
    apply (w4f_f30_bytes mem3 mem2 _ _ Hphi). intros x Hx. apply KEEP. right; right; right; left. lia.
  - refine (conj (SPILL _ _ H224 ltac:(lia)) (conj (SPILL _ _ H232 ltac:(lia)) (conj _ Hplen))).
    apply (w4f_f30_bytes mem3 mem2 _ _ Hphi). intros x Hx. apply KEEP. right; right; right; left. lia.
  - apply (w4f_IFS_tr _ _ _ regs2 regs3). apply (w4f_f30_IFS_mem _ _ _ regs3 mem3 mem2 HIFS).
    + intros x Hx. apply KEEP. right; left. lia.
    + intros Had. exact (ADDR _ _ Had ltac:(lia) ltac:(lia)).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82af8_at j (0x82af8) --S_F31--> B82b38_at j (t_cls j <> None) | B82b5c_at j (t_cls j = None).
   0x82af8 bnez a0,0x82b5c (a0 = cl_r: taken iff classify = None); 0x82afc-0x82b24 the bytes o + 4 .. o + 6 are
   00 40 ab; li a2,6; ld a0,144(s1) (fr + 452); ld a1,264(s1) (fr + 2624); jal 0x42aac (ra 0x82b38)
   (UB Seg/F31.v:3-14).
   SINK BRANCHES (objdump L85518-L85526): 0x82b04 `bnez a0,82fa4`, 0x82b14 / 0x82b24 `bne a0,a1,82fa4`: not taken
   on the Some arm, classify = Some e makes t_B bytes 4 .. 6 = 00 40 ab (RcClassify.cl_oui) and the body carries
   bytes (fr + 448) (t_B j); discharged INSIDE f31c_evt_pre_F. *)
Lemma seg_F31 : forall POST (j : nat),
  ctl_from POST (ix C_B82b38_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82b5c_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82af8_at [Z.of_nat j]).
Proof.
  intros POST j Hb38 Hb5c cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  unfold ACtlCutP.C_B82af8_at in *. cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc
    ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  set (jj := ACtlCutP.ixn 0 [Z.of_nat j]) in *.
  destruct HBODY as (phi & Hperm & HFRAC & Hn & Hj & HHB & HLK & HFTK & Hr10 & H144 & H264 & H216 & HtB &
    Had452 & Had2624 & H184 & H25 & H192 & Hev & HPT & HFT & HIFS).
  destruct (ACtlCutP.SM.t_cls (ACtlCut.c_in cx) jj) as [e|] eqn:Ecls.
  2: {
    (* t_cls j = None: 0x82af8 -> 0x82b5c, no memory access *)
    apply w4f_enter.
    eapply w4f_run.
    { eapply (B.Prog.Seg.F31F.f31n_evt_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3
        (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
      exact Hr10. }
    { apply B.ProgBridge.fp_avoids_RNG_W. }
    intros ms' md' -> Hs _.
    apply w4f_exit.
    apply (Hb5c cx [Z.of_nat j] fr k ly3 S3 W3 _ mem3 md' HB (w4f_aj_nowrite _ _ _ _ _ _ _ _ _ HJ Hs) HF HG1 Hk);
      [| exact HRT].
    cbn [ACtlCut.cut_body ACtlCut.ix_cut]. unfold ACtlCutP.C_B82b5c_at. cbn [ACtlCut.cut_body]. cbv zeta. fold jj.
    split; [reflexivity |].
    exists phi.
    refine (conj Hperm (conj _ (conj Hn (conj Hj (conj HHB (conj _ (conj _ (conj _ (conj _ _))))))))).
    - apply (w4f_FRAC_tr _ _ _ _ regs3); try reflexivity; exact HFRAC.
    - apply (w4f_LK_tr _ _ _ _ regs3); try reflexivity; exact HLK.
    - apply (w4f_FTK_tr _ _ _ _ regs3); try reflexivity; exact HFTK.
    - apply (w4f_PT32_tr _ _ _ _ _ regs3); try reflexivity; exact HPT.
    - apply (w4f_FTURN_tr _ _ _ _ regs3); try reflexivity; exact HFT.
    - apply (w4f_IFS_tr _ _ _ _ regs3); exact HIFS. }
  (* t_cls j = Some e *)
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _).
  unfold ACtlCutP.ART.APPMEM_END, ACtlCutP.FRAME_BYTES in HspEnd, HfrA.
  pose proof (w4f_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Bfr1 & Bfr2).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  pose proof Hastk as (Hsp16 & _ & Hcl & Hlsp & _). unfold Reusable.YCfn.LLVMF_STK in Hlsp.
  pose proof HB as (((_ & _ & _ & Hgp0 & _) & _) & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  pose proof (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Happ).
  rewrite <- (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) in Happ.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Happ.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Happ.
  assert (Q144 : ACtlCutP.q64 mem3 (A + 144) (fr + 452)) by (apply (w4f_spill regs3 mem3 144 _ A H144 Hr9); lia).
  assert (Q216 : ACtlCutP.q64 mem3 (A + 216) (fr + 448)) by (apply (w4f_spill regs3 mem3 216 _ A H216 Hr9); lia).
  assert (Q264 : ACtlCutP.q64 mem3 (A + 264) (fr + 2624)) by (apply (w4f_spill regs3 mem3 264 _ A H264 Hr9); lia).
  pose proof (B.Prog.Seg.F31.f31_B_src _ _ _ Ecls) as Hsrc.
  pose proof (B.Prog.Seg.F31.f31_B_length (ACtlCut.c_in cx) jj) as HBlen.
  assert (H6 : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (fr + 448 + 4)
                 (firstn 6 (skipn 4 (ACtlCutP.SM.t_B (ACtlCut.c_in cx) jj))))
    by exact (B.Prog.Seg.F31.f31_ba_sub mem3 (fr + 448) _ 4 6 HtB ltac:(lia)).
  (* 0x82af8 -> 0x42aac (ra 0x82b38), memory unchanged *)
  apply w4f_enter.
  eapply w4f_run.
  { eapply (B.Prog.Seg.F31F.f31c_evt_pre_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3
      A (fr + 448) (fr + 2624) _ _ _ (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    - exact Hr9.
    - exact Hr10.
    - lia.
    - lia.
    - replace (fr + 448 + 4) with (fr + 452) by lia. exact Q144.
    - exact Q216.
    - exact Q264.
    - rewrite Hsrc in H6. exact H6.
    - apply B.ProgBridge.rng_of_visible. apply (w4f_vis_stack cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k _ _ HJ);
        unfold Reusable.YCfn.LLVMF_STK; lia.
    - apply B.ProgBridge.rng_of_visible. apply (w4f_vis_stack cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k _ _ HJ);
        unfold Reusable.YCfn.LLVMF_STK; lia.
    - apply B.ProgBridge.rng_of_visible. apply (w4f_vis_stack cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k _ _ HJ);
        unfold Reusable.YCfn.LLVMF_STK; lia.
    - apply B.ProgBridge.rng_of_visible. apply (w4f_vis_frame cx ly3 S3 W3 mem3 md3 k fr _ _ HJ HF HG1); lia. }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' -> Hs _.
  apply w4f_exit.
  match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R1 := R) end.
  change 0x42aac with B.Prog.bcmp_wrap_c.BCMP_WRAP. rewrite <- B_bcmp_tramp_at.
  pose proof (w4f_aj_nowrite _ _ _ _ _ _ _ _ _ HJ Hs) as HJ'.
  assert (HspR1 : Reusable.YG0d.spZ R1 = sp) by exact HspZ.
  (* the bcmp trampoline, x = fr + 452, y = fr + 2624, n = 6 *)
  eapply Reusable.YA0n.SRr_bind.
  { eapply (Reusable.YCbq.aj_bcmp_at segs B LAWS segs_low _ H_bcmp W3 R1 mem3 Reusable.YCfn.LLVMF_STK
      (ACtlCut.c_sp cx) FP (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
      (ACtlCut.own6 cx) ly3 S3 md' k (fr + 448 + 4) (fr + 2624) 6 (sp - ACtlCut.c_sp cx) (Z_to_bv 64 0x82b38) HJ').
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite HspR1. lia.
    - rewrite Zminus_mod, Hspm, Hsp16. reflexivity.
    - lia.
    - unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK. lia.
    - transitivity (getr regs3 3); [reflexivity | rewrite Hr3; exact Hgp0].
    - exact Hr4.
    - reflexivity.
    - apply lib.Reusable.YK0s.ret_ok_even. reflexivity.
    - intros a Ha. split.
      + apply (Reusable.YCbq.aview_some_of_apresent segs).
        apply (w4f_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1). left. lia.
      + rewrite HspR1. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. split.
      + apply (Reusable.YCbq.aview_some_of_apresent segs).
        apply (w4f_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1). left. lia.
      + rewrite HspR1. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. unfold Reusable.YG0d.ESTACK. lia.
    - unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg,
        Reusable.YG0f.kHighMemEnd. lia.
    - unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg,
        Reusable.YG0f.kHighMemEnd. lia.
    - replace (fr + 448 + 4) with (fr + 452) by lia.
      apply (w4f_bcmp_range_addr W3 mem3 (fr + 452) 6); [| exact Had452].
      intros i Hi. refine (proj1 (w4f_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr _ HJ HG1 (or_intror _))).
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
      Z.div_mod_to_equations. lia.
    - intros _. apply (w4f_bcmp_hull_frame cx ly3 S3 W3 mem3 md3 k fr); [exact HJ | exact HG1 | lia | lia | lia].
    - apply (w4f_bcmp_range_addr W3 mem3 (fr + 2624) 6); [| exact Had2624].
      intros i Hi. refine (proj1 (w4f_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr _ HJ HG1 (or_intror _))).
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
      Z.div_mod_to_equations. lia.
    - intros _. apply (w4f_bcmp_hull_frame cx ly3 S3 W3 mem3 md3 k fr); [exact HJ | exact HG1 | lia | lia | lia]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr2 & Hpres2).
  (* the raw bytes the successor body reads, over their visible regions *)
  assert (Hwin : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 8192 <= a < sp) ->
    Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem2 a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha Hna. apply Hfr2; [exact Ha | unfold Reusable.YG0d.ESTACK; lia]. }
  destruct (w4f_bcmp_frame_kept cx ly3 S3 W3 mem3 md3 k fr mem2 sp HJ HF HG1 Hsp4096 ltac:(lia) Hwin)
    as (KS & KF & KSH & KK).
  assert (Hin : In (phi, ACtlCutP.flen cx jj) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
  destruct (w4f_bcmp_block_kept ly3 S3 W3 mem3 md3 mem2 (sp - 8192) sp phi _ HAR Hin ltac:(lia) Hwin) as (KB & KBS).
  assert (Hreq : ACtlCutP.flen cx jj <= Reusable.YG00.req_size (ACtlCutP.flen cx jj) /\
                 B.ACtlK.a_size (ACtlCutP.flen cx jj) = Reusable.YG00.req_size (ACtlCutP.flen cx jj)).
  { unfold B.ACtlK.a_size, Reusable.YG00.req_size.
    destruct (ACtlCutP.flen cx jj =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia. }
  assert (Hpr : forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, mem2 (Z_to_bv 64 a) = Some b).
  { intros a Ha. unfold ACtlCutP.FRAME_BYTES in Ha.
    refine (proj2 (Hpres2 a (w4f_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 _))). left. lia. }
  pose proof (ctl_kind_name_addressable _ _ _ _ _ (proj1 HJ2)) as HKA.
  assert (KSA : MKEPT mem3 mem2 A (ACtlCut.c_sp cx)) by (intros x Hx; apply KS; lia).
  (* the callee-saved registers *)
  assert (E2 : getr regs2 2 = getr regs3 2) by exact (HP 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E3 : getr regs2 3 = getr regs3 3) by exact (HP 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E4 : getr regs2 4 = getr regs3 4) by exact (HP 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E8 : getr regs2 8 = getr regs3 8) by exact (HP 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E9 : getr regs2 9 = getr regs3 9)
    by exact (eq_trans (HP 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) (eq_sym Hr9)).
  assert (E18 : getr regs2 18 = getr regs3 18) by exact (HP 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E19 : getr regs2 19 = getr regs3 19) by exact (HP 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E20 : getr regs2 20 = getr regs3 20) by exact (HP 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E22 : getr regs2 22 = getr regs3 22) by exact (HP 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E24 : getr regs2 24 = getr regs3 24) by exact (HP 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E25 : getr regs2 25 = getr regs3 25) by exact (HP 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E26 : getr regs2 26 = getr regs3 26) by exact (HP 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E27 : getr regs2 27 = getr regs3 27) by exact (HP 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  apply (Hb38 cx [Z.of_nat j] fr k ly3 S3 W3 regs2 mem2 md2 HB HJ2 HF HG1 Hk);
    [| exact (w4f_ctlrt _ _ _ _ _ _ _ _ HB HJ2)].
  cbn [ACtlCut.cut_body ACtlCut.ix_cut]. unfold ACtlCutP.C_B82b38_at. cbn [ACtlCut.cut_body]. cbv zeta. fold jj.
  split; [reflexivity |].
  exists phi.
  refine (conj Hperm (conj _ (conj Hn (conj Hj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ _))))))))))))))).
  - apply (w4f_bcmp_FRAC cx fr fr regs2 regs3 mem3 mem2 E2 E3 E4 E8 E9 E19 E26); [| exact KF | exact KSH | exact HFRAC].
    intros x Hx. apply KS. lia.
  - apply (w4f_bcmp_HB mem3 mem2 phi _); [intros i Hi; apply KBS; lia | exact HHB].
  - exact (w4f_bcmp_LK cx fr jj regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) Hr9 E9 E27 ltac:(lia) ltac:(lia)
      ltac:(lia) KSA KF KSH KK HKA Hpr HLK).
  - exact (w4f_bcmp_FTK cx jj fr regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) Hr9 E9 E22 E24 E25 ltac:(lia) ltac:(lia)
      ltac:(lia) KSA HFTK).
  - rewrite Ecls. discriminate.
  - rewrite Hv. apply (iff_trans Hcmp).
    apply (w4f_bcmp_cmp W3 mem3 (fr + 448 + 4) (fr + 2624) _ _ 6).
    + rewrite length_firstn, length_skipn, HBlen, ACtlCutP.SM.OUR_length. reflexivity.
    + rewrite length_firstn, length_skipn, HBlen. reflexivity.
    + exact H6.
    + exact (proj1 (proj2 (proj2 HLK))).
    + intros i Hi.
      refine (proj1 (w4f_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr (fr + 448 + 4 + i) HJ HG1 _)). left. lia.
    + intros i Hi.
      refine (proj1 (w4f_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr (fr + 2624 + i) HJ HG1 _)). left. lia.
  - exact (w4f_bcmp_sp regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) 184 _ Hr9 E9 ltac:(lia) ltac:(lia) ltac:(lia) KSA
      ltac:(lia) H184).
  - exact (w4f_rgv_tr regs2 regs3 25 _ E25 H25).
  - exact (w4f_bcmp_sp regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) 192 _ Hr9 E9 ltac:(lia) ltac:(lia) ltac:(lia) KSA
      ltac:(lia) H192).
  - intros e' He'. rewrite Ecls in He'.
    apply (w4f_bcmp_u32 mem3 mem2 (fr + 528) e'); [intros x Hx; apply KF; lia | exact (Hev e' He')].
  - apply (w4f_bcmp_PT32 cx jj phi fr regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) Hr9 E9 E18 E20 E24);
      [lia | lia | lia | exact KSA | intros x Hx; apply KB; lia | exact Hpr | exact HPT].
  - apply (w4f_bcmp_FTURN cx jj phi regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) Hr9 E9);
      [lia | lia | lia | exact KSA | intros x Hx; apply KB; lia | exact HFT].
  - exact (w4f_bcmp_IFS cx fr (S jj) regs2 regs3 mem3 mem2 KF KSH HIFS).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82b38_at j (0x82b38) --S_F32 (first entry)--> B82b5c_at j.
   0x82b38 beqz a0,82fa4; ld a0,184(s1); or a0,a0,s9; andi a0,a0,1; beqz a0,82fa4; ld a0,192(s1); lw a0,0(a0);
   li a1,5; bltu a1,a0,82fa4; and the cut 0x82b5c (UB Seg/F32.v:3-15).  No store.
   SINK BRANCHES (objdump L85531-L85539):
   - 0x82b38 `beqz a0,82fa4`: not taken, a0 = the F31 bcmp result is not 0: the source field t_B[4 .. 9] differs
     from our[] on the classify = Some path (C_B82b38_at body: t_cls j <> None and
     (a0 = 0 <-> firstn 6 (skipn 4 (t_B j)) = OUR); the model fact is ctrl's, Seg/F32.v:5).
   - 0x82b48 `beqz a0,82fa4`: not taken, classify = Some e gives tfill j or sum_ok j (FTK's spill 184 and rgv 25).
   - 0x82b58 `bltu a1,a0,82fa4`: not taken, 0 <= e <= 5 (u32 (fr + 528) e in the body, the classify range).
   Discharged INSIDE f32e_evt_F. *)
(* Proof: f32e_evt_F (F32F.v:48) at RNG := RNG_W (w_H W3), lifted by w4f_run; the classify = Some e facts by the
   model lemma B.Prog.Seg.F32.f32_cls (pure SlotModel, F32.v:183); the spills by w4f_spill at FRAC's base A; the
   footprint visible by w4f_vis_stack (spills, the journal's present window) and w4f_vis_frame (fr + 528, the owned
   frame); no store, so the journal moves by w4f_aj_nowrite and ctl_rt is the entry's. *)
Lemma seg_F32_b38 : forall POST (j : nat),
  ctl_from POST (ix C_B82b5c_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82b38_at [Z.of_nat j]).
Proof.
  intros POST j Hb5c cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  unfold ACtlCutP.C_B82b38_at in *. cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc
    ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  set (jj := ACtlCutP.ixn 0 [Z.of_nat j]) in *.
  destruct HBODY as (phi & Hperm & HFRAC & Hn & Hj & HHB & HLK & HFTK & Hcls & Hiff & H184 & H25 & H192 & Hev &
    HPT & HFT & HIFS).
  destruct (ACtlCutP.SM.t_cls (ACtlCut.c_in cx) jj) as [e|] eqn:Ecls; [| contradiction].
  destruct (B.Prog.Seg.F32.f32_cls _ _ _ Ecls) as (HOUR & Hflag & He).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle & HspA &
    HfrA & HA448 & Hsp4096 & HspEnd & _).
  pose proof (bv_unsigned_in_range 64 (getr regs3 2)) as Hspr.
  unfold bv_modulus in Hspr. cbn [Z.of_N] in Hspr. unfold Reusable.YG0d.spZ in HspZ.
  unfold ACtlCutP.ART.APPMEM_END, ACtlCutP.FRAME_BYTES in *.
  pose proof (w4f_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Bfr1 & Bfr2).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  assert (Q184 : ACtlCutP.q64 mem3 (A + 184) (ACtlCutP.SM.b2z (ACtlCutP.SM.t_tfill (ACtlCut.c_in cx) jj)))
    by (apply (w4f_spill regs3 mem3 184 _ A H184 Hr9); lia).
  assert (Q192 : ACtlCutP.q64 mem3 (A + 192) (fr + 528)) by (apply (w4f_spill regs3 mem3 192 _ A H192 Hr9); lia).
  assert (Hne : getr regs3 10 <> Z_to_bv 64 0) by (intros E; exact (HOUR (proj1 Hiff E))).
  apply w4f_enter.
  eapply w4f_run.
  { eapply (B.Prog.Seg.F32F.f32e_evt_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3 A
      (ACtlCutP.SM.b2z (ACtlCutP.SM.t_tfill (ACtlCut.c_in cx) jj))
      (ACtlCutP.SM.b2z (ACtlCutP.SM.t_sum_ok (ACtlCut.c_in cx) jj)) (fr + 528) e
      (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    - exact Hr9.
    - exact H25.
    - exact (lib.Reusable.YK11.bv_eqb_neq _ _ Hne).
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Q184.
    - exact Q192.
    - exact (Hev e eq_refl).
    - unfold ACtlCutP.SM.b2z; destruct (ACtlCutP.SM.t_tfill _ _); [right | left]; reflexivity.
    - unfold ACtlCutP.SM.b2z; destruct (ACtlCutP.SM.t_sum_ok _ _); [right | left]; reflexivity.
    - unfold ACtlCutP.SM.b2z; destruct Hflag as [Hf | Hf]; rewrite Hf; [left | right]; reflexivity.
    - exact He.
    - apply B.ProgBridge.rng_of_visible. apply (w4f_vis_stack cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
    - apply B.ProgBridge.rng_of_visible. apply (w4f_vis_stack cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
    - apply B.ProgBridge.rng_of_visible. apply (w4f_vis_frame cx ly3 S3 W3 mem3 md3 k fr _ _ HJ HF HG1); lia. }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' -> Hs _.
  apply w4f_exit.
  apply (Hb5c cx [Z.of_nat j] fr k ly3 S3 W3 _ mem3 md' HB (w4f_aj_nowrite _ _ _ _ _ _ _ _ _ HJ Hs) HF HG1 Hk);
    [| exact HRT].
  cbn [ACtlCut.cut_body ACtlCut.ix_cut]. unfold ACtlCutP.C_B82b5c_at. cbn [ACtlCut.cut_body]. cbv zeta. fold jj.
  split; [reflexivity |].
  exists phi.
  refine (conj Hperm (conj _ (conj Hn (conj Hj (conj HHB (conj _ (conj _ (conj _ (conj _ _))))))))).
  - apply (w4f_FRAC_tr _ _ _ _ regs3); try reflexivity; exact HFRAC.
  - apply (w4f_LK_tr _ _ _ _ regs3); try reflexivity; exact HLK.
  - apply (w4f_FTK_tr _ _ _ _ regs3); try reflexivity; exact HFTK.
  - apply (w4f_PT32_tr _ _ _ _ _ regs3); try reflexivity; exact HPT.
  - apply (w4f_FTURN_tr _ _ _ _ regs3); try reflexivity; exact HFT.
  - apply (w4f_IFS_tr _ _ _ _ regs3); exact HIFS.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82b5c_at j (0x82b5c) --S_F32 (second entry)--> B82bcc_at j | B82c90_at j.
   0x82b5c li a0,9; bne s8,a0,82c90 (k <> 9); 0x82b64 beqz s2,82fa0 (T67); 0x82b6c bltu a0,s2,82fa0 (T68); the
   instrumented check of Phi + 16, `bne a0,205,82c90`; 0x82b94 bltu (T69); the check of Phi + 17, `bne a0,234,82c90`;
   0x82bb8 sb zero,4(s3) (S(fr) + 4 := 0); ld s7,160(s1) (fr + 32); sd zero,0(s7); mv a0,s7;
   jal reac_box_catalogue (entry 0x84dec, ra 0x82bcc), which returns a0 = CAT = 0x9f620 and writes 11 at fr + 32
   (UB Seg/F32.v:16-31).
   SINK BRANCHES (objdump L85542-L85559):
   - 0x82b64 `beqz s2,82fa0` (plan F.4.1 row 65): not taken, HB's phi <> 0 and PT32's s2 = phi.
   - 0x82b6c / 0x82b94 `bltu a0,s2,82fa0` (rows 66-67): not taken, HB's addressable m phi (a_size len) puts
     phi + max(len, 1) <= APPMEM_END = 2^47, so phi + 16, phi + 17 do not wrap.
   - the report paths of the two checks (0x82b80 -> 0x82dbc -> 0x830ac, 0x82ba8 -> 0x82e10 -> 0x830c4): not taken,
     Phi + 16 / Phi + 17 lie in the live block with len >= 50 (k = 9 reaches them only with 50 <= flen; HB).
   All are discharged INSIDE f32m1_evt_F / f32m2_evt_F / f32c_evt_pre_F. *)
(* Proof: case on t_k j = 9 (F32.f32_k_range / f32_k9_len), then on the Phi bytes 16 / 17 (FTURN's t_phi j through
   F32.f32_tg / f32_ba_sub; their shadow bytes by F32.f32_sh on HB).  Each mismatch arm is f32n_evt_F /
   f32m1_evt_F / f32m2_evt_F at RNG := RNG_W (w_H W3) (the block's bytes visible by AR_blocks_law, their shadow
   bytes by AR_shadow_law, w4f_f32_blk / w4f_f32_blksh); no store, so the journal moves by w4f_aj_nowrite and the
   successor C_B82c90_at gets t_want_m j = 0 from t_rowsel j = false (SlotModel's definition).  The match arm is
   f32c_evt_pre_F (stores S(fr) + 4 and [fr + 32, fr + 40): owned frame and its shadow; AC.GT <= fr by
   w4f_gt_img_top and w4f_f32_fr) and then reac_box_catalogue by its closed footprint contract
   (reac_box_catalogue_F_holds_on through w4f_f32_cat_lift; writes [sp - 16, sp) and [fr + 32, fr + 40)), each lifted
   by w4f_f32_run, the journal moved by YCbq.ajournal_exec over each write set (w4f_f32_awr), ctl_rt_C by
   ctl_rt_C_of_AR; the successor C_B82bcc_at's memory facts cross the composed write set (fl_bytes, w4f_f32_addr,
   F32.f32_stk_keep, w4f_f32_FRAC_mem / LK_mem / IFS_mem).
   Route (C): f32c_evt_pre_F_on and reac_box_catalogue_contract_F_on (both premise shadow_rw DROPPED); the write
   S(fr) + 4 takes its wview from ctl_rt_C's cut-shadow conjunct (w4f_cut_fsh). *)
Lemma seg_F32_b5c : forall POST (j : nat),
  ctl_from POST (ix C_B82bcc_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82c90_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82b5c_at [Z.of_nat j]).
Proof.
  intros POST j Hbcc Hc90 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  unfold ACtlCutP.C_B82b5c_at in *. cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc
    ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  set (jj := ACtlCutP.ixn 0 [Z.of_nat j]) in *.
  destruct HBODY as (phi & Hperm & HFRAC & Hn & Hj & HHB & HLK & HFTK & HPT & HFT & HIFS).
  (* the successor of the three mismatch arms: memory unchanged, the registers the body reads kept *)
  assert (K90 : forall (R : bvmap 5 word) md', ACtlCutP.SM.t_want_m (ACtlCut.c_in cx) jj = 0 ->
     Reusable.YK04.same_but_materialized md3 md' ->
     getr R 2 = getr regs3 2 -> getr R 3 = getr regs3 3 -> getr R 4 = getr regs3 4 -> getr R 8 = getr regs3 8 ->
     getr R 9 = getr regs3 9 -> getr R 18 = getr regs3 18 -> getr R 19 = getr regs3 19 ->
     getr R 20 = getr regs3 20 -> getr R 22 = getr regs3 22 -> getr R 24 = getr regs3 24 ->
     getr R 25 = getr regs3 25 -> getr R 26 = getr regs3 26 -> getr R 27 = getr regs3 27 ->
     Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x82c90 R mem3 md') (POST cx)).
  { intros R md' Hwm Hs E2 E3 E4 E8 E9 E18 E19 E20 E22 E24 E25 E26 E27.
    apply (Hc90 cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HB (w4f_aj_nowrite _ _ _ _ _ _ _ _ _ HJ Hs) HF HG1 Hk);
      [| exact HRT].
    cbn [ACtlCut.cut_body ACtlCut.ix_cut]. unfold ACtlCutP.C_B82c90_at. cbn [ACtlCut.cut_body]. cbv zeta. fold jj.
    split; [reflexivity |].
    exists phi.
    refine (conj Hperm (conj _ (conj Hn (conj Hj (conj HHB (conj _ (conj Hwm (conj _ (conj _ (conj _ _)))))))))).
    - exact (w4f_FRAC_tr _ _ _ R regs3 _ E2 E3 E4 E8 E9 E19 E26 HFRAC).
    - exact (w4f_LK_tr _ _ _ R regs3 _ E9 E27 HLK).
    - exact (w4f_PT32_tr _ _ _ _ R regs3 _ E9 E18 E20 E24 HPT).
    - exact (w4f_FTK_tr _ _ _ R regs3 _ E9 E22 E24 E25 HFTK).
    - exact (w4f_FTURN_tr _ _ _ R regs3 _ E9 HFT).
    - exact (w4f_IFS_tr _ _ _ R regs3 _ HIFS). }
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle & HspA &
    HfrA & HA448 & Hsp4096 & HspEnd & _).
  pose proof HPT as (Hr18 & Hr24 & Hr20 & H152 & H312 & Hphi & Hplen & H160 & Hfstk).
  pose proof HFTK as (H184 & Hr22 & _ & H272 & Hr25).
  pose proof (bv_unsigned_in_range 64 (getr regs3 2)) as Hspr.
  unfold bv_modulus in Hspr. cbn [Z.of_N] in Hspr. unfold Reusable.YG0d.spZ in HspZ.
  unfold ACtlCutP.ART.APPMEM_END, ACtlCutP.FRAME_BYTES, ACtlCutP.flen, ACtlCutP.Sfr in *.
  pose proof (w4f_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Bfr1 & Bfr2).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof (w4f_f32_fr cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Hfrhi & Hfrapp).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hst1 & Hst2 & _) & _).
  unfold Reusable.YCfn.LLVMF_STK in Hst2.
  pose proof (bv_unsigned_in_range 64 (getr (ACtlCut.c_regs cx) 2)) as Hcspr.
  unfold bv_modulus in Hcspr. cbn [Z.of_N] in Hcspr.
  assert (Hcsp : ACtlCut.c_sp cx = bv_unsigned (getr (ACtlCut.c_regs cx) 2)) by reflexivity.
  assert (HSf : 0x7fff8000 <= B.AsanRT.shadow_addr fr /\ B.AsanRT.shadow_addr fr + 512 <= 0x10007fff8000 /\
             (fr + 4096 <= 0x7fff7000 -> B.AsanRT.shadow_addr fr + 512 <= 0x8fff7000) /\
             (0x10007fff8000 <= fr -> 0x2008fff7000 <= B.AsanRT.shadow_addr fr)).
  { unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  pose proof (B.Prog.Seg.F32.f32_k_range (ACtlCut.c_in cx) jj) as Hkr.
  destruct (Z.eq_dec (ACtlCutP.SM.t_k (ACtlCut.c_in cx) jj) 9) as [Ek | Ek].
  2: { (* k <> 9: `bne s8,a0` at 0x82b60 is taken to 0x82c90 *)
    apply w4f_enter. eapply w4f_run.
    { eapply (B.Prog.Seg.F32F.f32n_evt_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3
        (ACtlCutP.SM.t_k (ACtlCut.c_in cx) jj) (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)));
        [exact Hr24 | lia | exact Ek]. }
    { apply B.ProgBridge.fp_avoids_RNG_W. }
    intros ms' md' -> Hs _. apply w4f_exit.
    apply K90; try reflexivity.
    - unfold ACtlCutP.SM.t_want_m, ACtlCutP.SM.t_rowsel.
      replace (ACtlCutP.SM.t_k (ACtlCut.c_in cx) jj =? 9) with false by (symmetry; apply Z.eqb_neq; exact Ek).
      reflexivity.
    - exact Hs.
    - exact (eq_sym Hr24). }
  (* k = 9: the frame is at least 50 bytes long, a live block of the journal, and its bytes 16 / 17 are read *)
  assert (Hlen50 : 50 <= ACtlCutP.SM.t_len (ACtlCut.c_in cx) jj) by (apply B.Prog.Seg.F32.f32_k9_len; exact Ek).
  assert (Hr24k : getr regs3 24 = Z_to_bv 64 9) by (unfold ACtlCut.rgv in Hr24; rewrite Hr24, Ek; reflexivity).
  pose proof HHB as (Hphi0 & HAd).
  pose proof HAd as (Hp0 & _ & Hpe & _). unfold B.ACtlK.a_size in Hpe. rewrite Z.max_l in Hpe by lia.
  unfold B.AsanRT.APPMEM_END in Hpe.
  assert (Hinb : In (phi, ACtlCutP.SM.t_len (ACtlCut.c_in cx) jj) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (w4f_f32_blk cx ly3 S3 W3 mem3 md3 k fr _ _ HJ HF HG1 Hinb) as (Hb0 & Hbc & Hbapp & Hbfr & Hbvis).
  assert (Hreq : Reusable.YG00.req_size (ACtlCutP.SM.t_len (ACtlCut.c_in cx) jj) =
                 ACtlCutP.SM.t_len (ACtlCut.c_in cx) jj)
    by (unfold Reusable.YG00.req_size; destruct (Z.eqb_spec (ACtlCutP.SM.t_len (ACtlCut.c_in cx) jj) 0); lia).
  rewrite Hreq in Hbc, Hbapp, Hbfr, Hbvis.
  assert (Vb : forall o, 0 <= o -> o + 1 <= ACtlCutP.SM.t_len (ACtlCut.c_in cx) jj ->
             B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (phi + o) 1).
  { intros o Ho1 Ho2. split; [lia |]. split; [lia |]. intros a Ha. apply Hbvis. lia. }
  assert (Vs : forall o, 0 <= o < ACtlCutP.SM.t_len (ACtlCut.c_in cx) jj ->
             B.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (Z.shiftr (phi + o) 3 + B.AsanRT.ASAN_K) 1).
  { intros o Ho. apply (w4f_f32_blksh cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k phi _ o HJ Hinb). rewrite Hreq. lia. }
  pose proof (B.Prog.Seg.F32.f32_sh mem3 phi (ACtlCutP.SM.t_len (ACtlCut.c_in cx) jj) 16 HAd ltac:(lia) ltac:(lia))
    as Hsh16.
  pose proof (B.Prog.Seg.F32.f32_sh mem3 phi (ACtlCutP.SM.t_len (ACtlCut.c_in cx) jj) 17 HAd ltac:(lia) ltac:(lia))
    as Hsh17.
  assert (Hplen' : Z.of_nat (length (ACtlCutP.SM.t_phi (ACtlCut.c_in cx) jj)) = ACtlCutP.SM.t_len (ACtlCut.c_in cx) jj)
    by apply B.Prog.Seg.F32.f32_phi_len.
  assert (Hgt : ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj = firstn 50 (ACtlCutP.SM.t_phi (ACtlCut.c_in cx) jj))
    by (apply B.Prog.Seg.F32.f32_tg; exact Hlen50).
  assert (Hb16 : lib.Lib.Mem.bytes_at segs mem3 (phi + 16) [RPS.cp_b (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 16]).
  { pose proof (B.Prog.Seg.F32.f32_ba_sub mem3 phi (ACtlCutP.SM.t_phi (ACtlCut.c_in cx) jj) 16 1 Hphi ltac:(lia))
      as H16.
    rewrite (B.Prog.Seg.F32.f32_fs1 (ACtlCutP.SM.t_phi (ACtlCut.c_in cx) jj) 16) in H16 by lia.
    replace (phi + Z.of_nat 16) with (phi + 16) in H16 by lia.
    unfold RPS.cp_b. rewrite Hgt, B.Prog.Seg.F32.f32_nth_firstn by lia. exact H16. }
  assert (Hb17 : lib.Lib.Mem.bytes_at segs mem3 (phi + 17) [RPS.cp_b (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 17]).
  { pose proof (B.Prog.Seg.F32.f32_ba_sub mem3 phi (ACtlCutP.SM.t_phi (ACtlCut.c_in cx) jj) 17 1 Hphi ltac:(lia))
      as H17.
    rewrite (B.Prog.Seg.F32.f32_fs1 (ACtlCutP.SM.t_phi (ACtlCut.c_in cx) jj) 17) in H17 by lia.
    replace (phi + Z.of_nat 17) with (phi + 17) in H17 by lia.
    unfold RPS.cp_b. rewrite Hgt, B.Prog.Seg.F32.f32_nth_firstn by lia. exact H17. }
  destruct (Z.eq_dec (RPS.cp_v (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 16) 205) as [E16 | E16].
  2: { (* Phi[16] <> 0xcd: `bne a0,a1` at 0x82b8c is taken to 0x82c90 *)
    apply w4f_enter. eapply w4f_run.
    { eapply (B.Prog.Seg.F32F.f32m1_evt_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3 phi
        (RPS.cp_b (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 16) (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
      - exact Hr18.
      - exact Hr24k.
      - exact Hr26.
      - lia.
      - unfold B.AsanRT.APPMEM_END. lia.
      - exact Hsh16.
      - exact Hb16.
      - unfold RPS.cp_v in E16. exact E16.
      - apply B.ProgBridge.rng_of_visible. exact (Vs 16 ltac:(lia)).
      - apply B.ProgBridge.rng_of_visible. exact (Vb 16 ltac:(lia) ltac:(lia)). }
    { apply B.ProgBridge.fp_avoids_RNG_W. }
    intros ms' md' -> Hs _. apply w4f_exit.
    apply K90; try reflexivity.
    - unfold ACtlCutP.SM.t_want_m, ACtlCutP.SM.t_rowsel.
      replace (RPS.cp_v (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 16 =? 205) with false
        by (symmetry; apply Z.eqb_neq; exact E16).
      rewrite andb_false_r. reflexivity.
    - exact Hs. }
  assert (Eb16 : RPS.cp_b (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 16 = Z_to_bv 8 205)
    by (apply (B.Prog.Seg.F32.f32_cp_b _ 16 205 E16); lia).
  destruct (Z.eq_dec (RPS.cp_v (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 17) 234) as [E17 | E17].
  2: { (* Phi[17] <> 0xea: `bne a0,a1` at 0x82bb4 is taken to 0x82c90 *)
    apply w4f_enter. eapply w4f_run.
    { eapply (B.Prog.Seg.F32F.f32m2_evt_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3 phi
        (RPS.cp_b (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 17) (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
      - exact Hr18.
      - exact Hr24k.
      - exact Hr26.
      - lia.
      - unfold B.AsanRT.APPMEM_END. lia.
      - exact Hsh16.
      - rewrite <- Eb16. exact Hb16.
      - exact Hsh17.
      - exact Hb17.
      - unfold RPS.cp_v in E17. exact E17.
      - apply B.ProgBridge.rng_of_visible. exact (Vs 16 ltac:(lia)).
      - apply B.ProgBridge.rng_of_visible. exact (Vb 16 ltac:(lia) ltac:(lia)).
      - apply B.ProgBridge.rng_of_visible. exact (Vs 17 ltac:(lia)).
      - apply B.ProgBridge.rng_of_visible. exact (Vb 17 ltac:(lia) ltac:(lia)). }
    { apply B.ProgBridge.fp_avoids_RNG_W. }
    intros ms' md' -> Hs _. apply w4f_exit.
    apply K90; try reflexivity.
    - unfold ACtlCutP.SM.t_want_m, ACtlCutP.SM.t_rowsel.
      replace (RPS.cp_v (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 17 =? 234) with false
        by (symmetry; apply Z.eqb_neq; exact E17).
      rewrite andb_false_r. reflexivity.
    - exact Hs. }
  (* k = 9, Phi[16] = 0xcd, Phi[17] = 0xea: the catalogue runs and the row loop is entered at 0x82bcc *)
  assert (Eb17 : RPS.cp_b (ACtlCutP.SM.t_g (ACtlCut.c_in cx) jj) 17 = Z_to_bv 8 234)
    by (apply (B.Prog.Seg.F32.f32_cp_b _ 17 234 E17); lia).
  assert (Hrow : ACtlCutP.SM.t_rowsel (ACtlCut.c_in cx) jj = true)
    by (unfold ACtlCutP.SM.t_rowsel; rewrite Ek, E16, E17; reflexivity).
  assert (Hbig : ACtlCutP.SM.t_big (ACtlCut.c_in cx) jj = true)
    by (unfold ACtlCutP.SM.t_big; apply Z.leb_le; exact Hlen50).
  assert (H312' : ACtlCutP.spill regs3 mem3 312 (phi + 18)) by (rewrite Hbig in H312; exact H312).
  assert (Q160 : ACtlCutP.q64 mem3 (A + 160) (fr + 32)) by (apply (w4f_spill regs3 mem3 160 _ A H160 Hr9); lia).
  assert (HWR8 : lib.Lib.Mem.wr_at B.Img0.rsegs mem3 (fr + 32) 8).
  { destruct Hfstk as (Hf0 & Hf1 & Hf). split; [lia |]. split; [lia |].
    intros i Hi. exact (proj1 (Hf (fr + 32 + i) ltac:(lia))). }
  pose proof HRT as (HAC & HSWC & _).
  assert (HWR1 : lib.Lib.Mem.wr_at B.Img0.rsegs mem3 (B.AsanRT.shadow_addr fr + 4) 1).
  { assert (Hin : B.AsanRT.in_shadow (B.AsanRT.shadow_addr fr + 4))
      by (unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
            B.AsanRT.HIGHMEM_BEG; lia).
    destruct (w4f_cut_fsh cx ly3 S3 W3 mem3 md3 k fr (B.AsanRT.shadow_addr fr + 4) HJ HF HG1 HSWC ltac:(lia) Hin)
      as (Hw & _).
    split; [lia |]. split; [lia |]. intros i Hi.
    replace (B.AsanRT.shadow_addr fr + 4 + i) with (B.AsanRT.shadow_addr fr + 4) by lia. exact Hw. }
  assert (HST : lib.Lib.Frame.stk B.Img0.rsegs mem3 (sp - 16) sp)
    by (apply (w4f_f32_stk cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia).
  assert (Hs32 : B.AsanRT.shadow_addr (fr + 32) = B.AsanRT.shadow_addr fr + 4)
    by (unfold B.AsanRT.shadow_addr; Z.div_mod_to_equations; lia).
  assert (Hs39 : B.AsanRT.shadow_addr (fr + 39) = B.AsanRT.shadow_addr fr + 4)
    by (unfold B.AsanRT.shadow_addr; Z.div_mod_to_equations; lia).
  apply w4f_enter. eapply w4f_f32_run.
  { eapply (B.Prog.Seg.F32F.f32c_evt_pre_F_on _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3 A fr
      phi (sp - 16) sp (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    - exact Hr9.
    - exact Hr18.
    - exact Hr19.
    - exact Hr24k.
    - exact Hr26.
    - exact Hr2.
    - lia.
    - unfold B.AsanRT.APPMEM_END. lia.
    - lia.
    - lia.
    - rewrite w4f_gt_img_top. lia.
    - exact Hfr32.
    - intros a Ha. unfold B.Prog.SlotInv.FRAME_BYTES in Ha.
      unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia.
    - unfold B.AsanRT.HIGHMEM_BEG. lia.
    - lia.
    - unfold B.AsanRT.APPMEM_END. lia.
    - exact HspA.
    - left. unfold B.Prog.SlotInv.FRAME_BYTES. lia.
    - exact Hsh16.
    - rewrite <- Eb16. exact Hb16.
    - exact Hsh17.
    - rewrite <- Eb17. exact Hb17.
    - exact Q160.
    - exact HWR8.
    - exact HWR1.
    - exact HST.
    - exact HAC.
    - apply B.ProgBridge.rng_of_visible. exact (Vs 16 ltac:(lia)).
    - apply B.ProgBridge.rng_of_visible. exact (Vb 16 ltac:(lia) ltac:(lia)).
    - apply B.ProgBridge.rng_of_visible. exact (Vs 17 ltac:(lia)).
    - apply B.ProgBridge.rng_of_visible. exact (Vb 17 ltac:(lia) ltac:(lia)).
    - apply B.ProgBridge.rng_of_visible. unfold B.Prog.SlotInv.Sfr.
      apply (w4f_f32_vis cx ly3 S3 W3 mem3 md3 k fr _ _ HJ HG1); [lia | lia | intros a Ha; right; left; lia].
    - apply B.ProgBridge.rng_of_visible.
      apply (w4f_vis_stack cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
    - apply B.ProgBridge.rng_of_visible. apply (w4f_vis_frame cx ly3 S3 W3 mem3 md3 k fr _ _ HJ HF HG1); lia. }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms2 md2 (a1' & a2' & m2 & -> & MU1 & WM1 & ST2 & HAC2 & HSWT2 & HWR2 & HAD2 & HS4 & Hsh2) Hs1 Hhid1 Hgr1.
  unfold B.Prog.SlotInv.Sfr in MU1, HS4, Hsh2.
  (* the journal across the first write set {S(fr) + 4} U [fr + 32, fr + 40) U [sp - 16, sp) *)
  assert (HJ2 : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m2 md2 k).
  { apply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun a => B.AsanRT.shadow_addr fr + 4 <= a < B.AsanRT.shadow_addr fr + 5 \/ fr + 32 <= a < fr + 40 \/
                sp - 16 <= a < sp) HJ).
    - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU1 x); [reflexivity |].
      cbn [lib.Lib.Frame.outside]. repeat split; intro; apply Hx; lia.
    - exact Hgr1.
    - exact Hhid1.
    - exact Hs1.
    - intros a Ha. apply (w4f_f32_awr cx ly3 S3 W3 mem3 md3 k fr a HJ HG1). unfold Reusable.YCfn.LLVMF_STK. lia. }
  (* the callee: reac_box_catalogue at c = fr + 32, lo = sp - 16 *)
  eapply w4f_f32_run.
  { eapply (w4f_f32_cat_lift B.Prog.reac_box_catalogueF.reac_box_catalogue_F_holds_on W3 (fr + 32) (sp - 16) sp).
    - exact HspZ.
    - reflexivity.
    - lia.
    - exact ST2.
    - lia.
    - exact HAC2.
    - intros x Hx. cbn [lib.Lib.Frame.outside].
      unfold B.AsanRT.GOT_CELL_K, B.AsanRT.CELL_K, B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END,
        B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG in Hx.
      repeat split; lia.
    - lia.
    - exact HWR2.
    - left. lia.
    - exact HAD2.
    - apply (w4f_vis_stack cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
    - apply (w4f_vis_frame cx ly3 S3 W3 mem3 md3 k fr _ _ HJ HF HG1); lia.
    - rewrite Hs32. replace (fr + 32 + 7) with (fr + 39) by lia. rewrite Hs39.
      apply (w4f_f32_vis cx ly3 S3 W3 mem3 md3 k fr _ _ HJ HG1); [lia | lia | intros a Ha; right; left; lia]. }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms5 md5 (a1c & a2c & m5 & -> & MU2 & WM2 & ST5 & Hc11) Hs2 Hhid2 Hgr2.
  (* the journal across the callee's write set [sp - 16, sp) U [fr + 32, fr + 40) *)
  assert (HJ5 : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m5 md5 k).
  { apply (Reusable.YCbq.ajournal_exec segs B LAWS segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun a => sp - 16 <= a < sp \/ fr + 32 <= a < fr + 40) HJ2).
    - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU2 x); [reflexivity |].
      cbn [lib.Lib.Frame.outside]. repeat split; intro; apply Hx; lia.
    - exact Hgr2.
    - exact Hhid2.
    - exact Hs2.
    - intros a Ha. apply (w4f_f32_awr cx ly3 S3 W3 mem3 md3 k fr a HJ HG1). unfold Reusable.YCfn.LLVMF_STK. lia. }
  rewrite (lib.Lib.MState.ret_pc_even 0x82bcc) by lia.
  apply w4f_exit.
  (* the memory facts of C_B82bcc_at's body across the composed write set *)
  assert (MU : lib.Lib.Frame.munch [(B.AsanRT.shadow_addr fr + 4, B.AsanRT.shadow_addr fr + 5); (fr + 32, fr + 40);
                 (sp - 16, sp)] mem3 m5).
  { apply (lib.Lib.Frame.munch_trans _ mem3 m2 m5 MU1).
    refine (lib.Lib.Frame.munch_weaken _ _ m2 m5 _ MU2).
    intros x Hx. cbn [lib.Lib.Frame.outside] in *. repeat split; lia. }
  assert (WM : lib.Lib.Frame.wmono B.Img0.rsegs mem3 m5) by exact (lib.Lib.Frame.wmono_trans _ _ _ _ WM1 WM2).
  assert (Hsp5 : forall off v, ACtlCutP.spill regs3 mem3 off v -> 0 <= off <= 440 -> ACtlCutP.spill regs3 m5 off v).
  { intros off v Hs Hoff. apply (w4f_f32_spill _ regs3 mem3 m5 off v A MU Hr9); [lia | lia | | exact Hs].
    intros x Hx. cbn [lib.Lib.Frame.outside]. repeat split; lia. }
  assert (Hadk : forall p n, B.AsanRT.addressable mem3 p n -> (p + n <= fr + 32 \/ fr + 40 <= p) ->
             B.AsanRT.addressable m5 p n).
  { intros p n Hp Hd. apply (w4f_f32_addr fr sp mem3 m5 p n MU Hp Hfr32); [| | exact Hd];
      unfold B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG; lia. }
  assert (Hkb : forall a bs, lib.Lib.Mem.bytes_at segs mem3 a bs ->
             (forall x, a <= x < a + Z.of_nat (length bs) ->
                lib.Lib.Frame.outside [(B.AsanRT.shadow_addr fr + 4, B.AsanRT.shadow_addr fr + 5); (fr + 32, fr + 40);
                  (sp - 16, sp)] x) ->
             lib.Lib.Mem.bytes_at segs m5 a bs).
  { intros a bs Hb Ho. exact (B.Prog.RcAsanFPLib.fl_bytes _ mem3 m5 a bs Hb MU Ho). }
  assert (Hstk5 : lib.Lib.Frame.stk segs m5 fr (fr + 3136)).
  { apply (B.Prog.Seg.F32.f32_stk_keep mem3 m5 fr (fr + 3136) Hfstk WM). intros x Hx.
    destruct (Z_lt_ge_dec x (fr + 32)) as [Hx1 | Hx1]; [| destruct (Z_lt_ge_dec x (fr + 40)) as [Hx2 | Hx2]].
    - destruct Hfstk as (_ & _ & Hf). destruct (Hf x ltac:(lia)) as (_ & b & Hb). exists b.
      rewrite (B.Prog.Seg.F32.f32_mrd_munch _ mem3 m5 x MU ltac:(lia)); [exact Hb |].
      cbn [lib.Lib.Frame.outside]. repeat split; lia.
    - apply (w4f_f32_ba_some m5 (fr + 32) _ x Hc11). rewrite lib.Lib.Mem.length_le8. lia.
    - destruct Hfstk as (_ & _ & Hf). destruct (Hf x ltac:(lia)) as (_ & b & Hb). exists b.
      rewrite (B.Prog.Seg.F32.f32_mrd_munch _ mem3 m5 x MU ltac:(lia)); [exact Hb |].
      cbn [lib.Lib.Frame.outside]. repeat split; lia. }
  assert (Hsh5 : exists sh, lib.Lib.Mem.bytes_at segs m5 (ACtlCutP.Sfr fr) sh /\
             length sh = Z.to_nat ACtlCutP.FRAME_SHADOW).
  { pose proof HFRAC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & (sh & Hsh & Hshl) & _).
    change (Z.to_nat ACtlCutP.FRAME_SHADOW) with 392%nat in Hshl |- *.
    unfold ACtlCutP.Sfr in *.
    assert (Lu : length (lib.Lib.Mem.upd_bytes sh 4 [Z_to_bv 8 0]) = 392%nat)
      by (rewrite lib.Lib.Mem.upd_bytes_length; [exact Hshl | rewrite Hshl; cbn [length]; lia]).
    exists (lib.Lib.Mem.upd_bytes sh 4 [Z_to_bv 8 0]). split; [| exact Lu].
    apply (B.Prog.RcAsanFPLib.fl_bytes _ m2 m5 _ _ (Hsh2 sh Hsh Hshl) MU2).
    rewrite Lu. intros x Hx. cbn [lib.Lib.Frame.outside]. repeat split; lia. }
  assert (HFRAC5 : ACtlCutP.FRAC B cx fr fr regs3 m5).
  { apply (w4f_f32_FRAC_mem cx fr fr regs3 mem3 m5 _ A HFRAC MU Hr9); [lia | | exact Hsh5].
    intros x Hx. cbn [lib.Lib.Frame.outside]. repeat split; lia. }
  pose proof HLK as (_ & _ & HOUR & HFLI).
  pose proof HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (Kb & Ka) & _).
  assert (HKNT5 : ACtlCutP.KNT m5).
  { assert (HL : length B.Prog.reac_ctrl_kind_name_c.kind_name_bytes = 112%nat) by reflexivity.
    split.
    - apply Hkb; [exact Kb |]. rewrite HL. unfold B.Prog.reac_ctrl_kind_name_c.KIND_NAME.
      intros x Hx. cbn [lib.Lib.Frame.outside]. repeat split; lia.
    - apply Hadk; [exact Ka |]. left. unfold B.Prog.reac_ctrl_kind_name_c.KIND_NAME. lia. }
  assert (HOUR5 : ACtlCutP.OURb cx fr m5).
  { unfold ACtlCutP.OURb in *. apply Hkb; [exact HOUR |]. rewrite ACtlCutP.SM.OUR_length.
    intros x Hx. cbn [lib.Lib.Frame.outside]. repeat split; lia. }
  assert (HLK5 : ACtlCutP.LK cx fr jj regs3 m5)
    by exact (w4f_f32_LK_mem cx fr jj regs3 mem3 m5 HLK Hsp5 HOUR5 (fun p n Hp Hpn => Hadk p n Hp (or_intror Hpn))
                Hstk5 HKNT5).
  assert (HIFS5 : ACtlCutP.IFS cx fr (S jj) regs3 m5).
  { apply (w4f_f32_IFS_mem cx fr (S jj) regs3 mem3 m5 _ HIFS MU).
    - intros x Hx. cbn [lib.Lib.Frame.outside]. repeat split; lia.
    - intros Ha. apply Hadk; [exact Ha | right; lia]. }
  assert (Hphi5 : lib.Lib.Mem.bytes_at segs m5 phi (ACtlCutP.SM.t_phi (ACtlCut.c_in cx) jj)).
  { apply Hkb; [exact Hphi |]. intros x Hx. cbn [lib.Lib.Frame.outside]. repeat split; lia. }
  assert (HHB5 : ACtlCutP.HB m5 phi (ACtlCutP.flen cx jj)).
  { split; [exact Hphi0 |]. apply Hadk; [exact HAd |].
    unfold B.ACtlK.a_size, ACtlCutP.flen. rewrite Z.max_l by lia. lia. }
  apply (Hbcc cx [Z.of_nat j] fr k ly3 S3 W3 _ m5 md5 HB HJ5 HF HG1 Hk);
    [| exact (w4f_ctlrt _ _ _ _ _ _ _ _ HB HJ5)].
  cbn [ACtlCut.cut_body ACtlCut.ix_cut]. unfold ACtlCutP.C_B82bcc_at. cbn [ACtlCut.cut_body]. cbv zeta. fold jj.
  split; [reflexivity |].
  exists phi.
  refine (conj Hperm (conj _ (conj Hn (conj Hj (conj HHB5 (conj _ (conj _ (conj Hrow (conj _ (conj _ (conj Hc11
    (conj _ (conj _ (conj _ (conj Hphi5 (conj Hplen (conj _ (conj Hstk5 (conj _ (conj _ _)))))))))))))))))))).
  - apply (w4f_FRAC_tr _ _ _ _ regs3); try reflexivity; exact HFRAC5.
  - apply (w4f_LK_tr _ _ _ _ regs3); try reflexivity; exact HLK5.
  - apply (w4f_FTK_tr _ _ _ _ regs3); try reflexivity.
    exact (conj (Hsp5 _ _ H184 ltac:(lia)) (conj Hr22 (conj Hr24 (conj (Hsp5 _ _ H272 ltac:(lia)) Hr25)))).
  - reflexivity.
  - reflexivity.
  - apply (w4f_rgv_tr _ regs3 18); [reflexivity | exact Hr18].
  - apply (w4f_rgv_tr _ regs3 20); [reflexivity | exact Hr20].
  - apply (w4f_spill_tr _ regs3); [reflexivity | exact (Hsp5 _ _ H152 ltac:(lia))].
  - apply (w4f_spill_tr _ regs3); [reflexivity | exact (Hsp5 _ _ H160 ltac:(lia))].
  - apply (w4f_spill_tr _ regs3); [reflexivity | exact (Hsp5 _ _ H312' ltac:(lia))].
  - apply (w4f_FTURN_tr _ _ _ _ regs3); [reflexivity |].
    pose proof HFT as (S224 & S232 & _ & HFTl).
    exact (conj (Hsp5 _ _ S224 ltac:(lia)) (conj (Hsp5 _ _ S232 ltac:(lia)) (conj Hphi5 HFTl))).
  - apply (w4f_IFS_tr _ _ _ _ regs3). exact HIFS5.
Qed.

(* ACtl.v's seg_F32 (both entries of S_F32): the composition of seg_F32_b5c and seg_F32_b38. *)
Lemma seg_F32 : forall POST (j : nat),
  ctl_from POST (ix C_B82bcc_at [Z.of_nat j]) -> ctl_from POST (ix C_B82c90_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82b38_at [Z.of_nat j]) /\ ctl_from POST (ix C_B82b5c_at [Z.of_nat j]).
Proof.
  intros POST j Hbcc Hc90.
  pose proof (seg_F32_b5c POST j Hbcc Hc90) as Hb5c. split; [exact (seg_F32_b38 POST j Hb5c) | exact Hb5c].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82bcc_at j (0x82bcc) --S_F33--> B82bf4_at j 0.
   0x82bcc beqz a0,82c84 (not taken: a0 = CAT); mv s5,a0; ld a0,0(s7) (= 11); beqz a0,82c84 (not taken); li s9,0;
   mv s7,s5; the row head li a0,296; mulh a1,s9,a0; mul a0,s9,a0; srai a2,a0,63 (UB Seg/F33.v:3-19).  No store.
   SINK BRANCHES: none (objdump L85568-L85577; the two `beqz` go to B82c84_at, dead under the body). *)
(* Proof: f33_evt_F (F33F.v) at RNG := RNG_W (w_H W3); its count read [fr + 32, fr + 40) is in the owned frame
   (w4f_vis_frame: 0 <= fr + 32 and fr + 40 <= 2^64 from the frame's bounds, the use-site discharge of
   f33_evt_of_F_bounded's two bounds); the run's register post gives RL at i = 0 and keeps the rest; no store. *)
Lemma seg_F33 : forall POST (j : nat),
  ctl_from POST (ix C_B82bf4_at [Z.of_nat j; Z.of_nat 0]) -> ctl_from POST (ix C_B82c84_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82bcc_at [Z.of_nat j]).
Proof.
  intros POST j Hbf4 _ cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  unfold ACtlCutP.C_B82bcc_at in *. cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc
    ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  set (jj := ACtlCutP.ixn 0 [Z.of_nat j]) in *.
  destruct HBODY as (phi & Hperm & HFRAC & Hn & Hj & HHB & HLK & HFTK & Hsel & Hr10 & Hr23 & Hq32 & Hr18 & Hr20 &
    H152 & Hphi & Hlen & H160 & Hstk & H312 & HFT & HIFS).
  pose proof (w4f_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Bfr1 & Bfr2).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  apply w4f_enter.
  eapply w4f_run.
  { eapply (B.Prog.Seg.F33F.f33_evt_F regs3 _ _ mem3 (fr + 32) (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    - exact Hr10.
    - exact Hr23.
    - exact (w4f_q64_read _ _ _ Hq32).
    - apply B.ProgBridge.rng_of_visible. apply (w4f_vis_frame cx ly3 S3 W3 mem3 md3 k fr _ _ HJ HF HG1); lia. }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' (R & -> & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E22 & E24 & E26 & E27 & E10 & E11 & E12 &
    E21 & E23 & E25) Hs _.
  apply w4f_exit.
  apply (Hbf4 cx [Z.of_nat j; Z.of_nat 0] fr k ly3 S3 W3 R mem3 md' HB (w4f_aj_nowrite _ _ _ _ _ _ _ _ _ HJ Hs) HF
    HG1); [exact Hk | | exact HRT].
  cbn [ACtlCut.cut_body ACtlCut.ix_cut]. unfold ACtlCutP.C_B82bf4_at. cbn [ACtlCut.cut_body]. cbv zeta.
  change (ACtlCutP.ixn 0 [Z.of_nat j; Z.of_nat 0]) with jj. change (ACtlCutP.ixn 1 [Z.of_nat j; Z.of_nat 0]) with 0%nat.
  split; [reflexivity |].
  pose proof HFTK as (H184 & Hr22 & Hr24 & H272 & Hr25).
  exists phi.
  refine (conj Hperm (conj _ (conj Hn (conj Hj (conj HHB (conj _ (conj _ (conj _ (conj _ (conj I
    (conj _ (conj _ _)))))))))))).
  - apply (w4f_FRAC_tr _ _ _ R regs3); assumption.
  - apply (w4f_LK_tr _ _ _ R regs3); assumption.
  - exact (w4f_rgv_tr R regs3 22 _ E22 Hr22).
  - intros _. exact (w4f_rgv_tr R regs3 24 _ E24 Hr24).
  - exact (w4f_spill_tr R regs3 _ _ _ E9 H272).
  - refine (conj (Nat.le_0_l 10) (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
    + exact E23.
    + exact E25.
    + exact E21.
    + exact E10.
    + exact E11.
    + exact E12.
    + intros i' Hi'. lia.
    + refine (conj Hsel (conj _ (conj _ (conj _ (conj _ (conj Hphi (conj Hlen (conj _ (conj Hq32 Hstk))))))))).
      * exact (w4f_rgv_tr R regs3 18 _ E18 Hr18).
      * exact (w4f_rgv_tr R regs3 20 _ E20 Hr20).
      * exact (w4f_spill_tr R regs3 _ _ _ E9 H152).
      * exact (w4f_spill_tr R regs3 _ _ _ E9 H312).
      * exact (w4f_spill_tr R regs3 _ _ _ E9 H160).
  - apply (w4f_FTURN_tr _ _ _ R regs3); assumption.
  - apply (w4f_IFS_tr _ _ _ R regs3); exact HIFS.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82bf4_at j i (0x82bf4) --S_F34--> B82c24_at j i.
   sb zero,8..11(s3) (the shadow of the row slot [fr + 64, fr + 96) := 0); 0x82c04 bne a1,a2,82fa0 (T70);
   add s8,a0,s5 (s8 = CAT + 296 i); sltu a0,s8,a0; 0x82c10 bnez a0,82fa0 (T71); mv a0,s7; ld s6,152(s1)
   (fr + 64); mv a1,s6; jal declaration_of (entry 0x83114, ra 0x82c24), which returns a0 = 1 and writes the 32
   bytes decl_i i at fr + 64 (UB Seg/F34.v:3-19).
   SINK BRANCHES (objdump L85582-L85585):
   - 0x82c04 `bne a1,a2,82fa0` (plan F.4.1 row 68): not taken, RL pins a1 = a2 = 0 at the cut (rgv 11 0, rgv 12 0).
   - 0x82c10 `bnez a0,82fa0` (row 69): not taken, RL gives s5 = CAT, a0 = CAT_ROW * i with i <= 10, so
     CAT + 296 i <= 0xa01b0 and the carry is 0.
   Discharged INSIDE f34_evt_pre_F.
   Route (C): f34_evt_ro_pre_F_on (premise shadow_rw DROPPED; the four shadow stores' wview from ctl_rt_C's cut-shadow
   conjunct, w4f_cut_fsh); declaration_of by declaration_of_contract_F_on, its region declaration_of_shadow_R
   (CAT + CAT_ROW * i) (fr + 64) from ctl_rt_C's cut-shadow and img-shadow conjuncts (w4f_f34_decl_region) carried to
   the callee entry by the stretch's region transport; the exit's frame-shadow bytes from the exit's own ctl_rt_C
   (w4f_ctlrt), not from the callee's post. *)
Lemma seg_F34 : forall POST (j i : nat),
  ctl_from POST (ix C_B82c24_at [Z.of_nat j; Z.of_nat i]) ->
  ctl_from POST (ix C_B82bf4_at [Z.of_nat j; Z.of_nat i]).
Proof.
  intros POST j i Hc24 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  unfold ACtlCutP.C_B82bf4_at in *. cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc
    ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  set (jj := ACtlCutP.ixn 0 [Z.of_nat j; Z.of_nat i]) in *.
  set (ii := ACtlCutP.ixn 1 [Z.of_nat j; Z.of_nat i]) in *.
  destruct HBODY as (phi & Hperm & HFRAC & Hn & Hj & HHB & HLK & Hr22 & Hr24 & H272 & _ & HRL & HFT & HIFS).
  pose proof HRL as (Hi10 & Hr23 & Hr25 & Hr21 & Hr10 & Hr11 & Hr12 & Hprev & HPTL).
  pose proof HPTL as (Hsel & Hr18 & Hr20 & H152 & H312 & Hphi & Hplen & H160 & Hq32 & Hstk).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _).
  destruct HRT as (HAC & HSWC & HIMG & HRO).
  unfold ACtlCutP.ART.APPMEM_END, ACtlCutP.FRAME_BYTES in HspEnd, HfrA.
  pose proof (bv_unsigned_in_range 64 (getr regs3 2)) as Hspr. unfold bv_modulus in Hspr. cbn [Z.of_N] in Hspr.
  unfold Reusable.YG0d.spZ in HspZ.
  pose proof (w4f_f34_frame_geo cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Bfr0 & Bfr1 & Bfra).
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _).
  destruct Hastk as (_ & _ & Hcl & Hslo & Hshi & Hshi47 & _).
  unfold Reusable.YCfn.LLVMF_STK in Hslo.
  assert (Hq8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (Hq : 8 * (fr / 8) = fr) by (clear - Hq8; Z.div_mod_to_equations; lia).
  assert (HS : ACtlCutP.Sfr fr = fr / 8 + 2147450880) by reflexivity.
  assert (HG : w4f_f34_G fr sp) by (unfold w4f_f34_G; lia).
  assert (Hshin : forall kk, 0 <= kk < 512 -> B.AsanRT.in_shadow (ACtlCutP.Sfr fr + kk)).
  { intros kk Hkk. rewrite HS. unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END,
      B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG. lia. }
  assert (Happs : forall kk, 0 <= kk <= 32 -> B.AsanRT.app_mem (fr + 64 + kk)).
  { intros kk Hkk. unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. lia. }
  assert (Hal : (ACtlCutP.SM.CAT + ACtlCutP.SM.CAT_ROW * Z.of_nat ii) mod 8 = 0).
  { unfold ACtlCutP.SM.CAT, ACtlCutP.SM.CAT_ROW.
    replace (652832 + 296 * Z.of_nat ii) with ((81604 + 37 * Z.of_nat ii) * 8) by lia. apply Z.mod_mul. lia. }
  assert (ECAT : ACtlCutP.SM.CAT = 652832) by reflexivity.
  assert (ECATR : ACtlCutP.SM.CAT_ROW = 296) by reflexivity.
  (* the stretch's inputs *)
  assert (Q152 : ACtlCutP.q64 mem3 (A + 152) (fr + 64)) by (apply (w4f_spill regs3 mem3 152 _ A H152 Hr9); lia).
  destruct (B.Prog.Seg.F34.f34_rw_of_stk mem3 (fr + 64) (fr + 96)
     (B.Prog.Seg.F34.f34_sub_stk mem3 fr (fr + 3136) (fr + 64) (fr + 96) Hstk ltac:(lia) ltac:(lia) ltac:(lia))
     ltac:(lia)) as (ob & Hoblen & Hob).
  destruct (B.Prog.Seg.F34.f34_row ii ltac:(lia)) as (Himg & Hok & Hrlen).
  pose proof (w4f_f34_row_bytes cx _ ly3 S3 W3 mem3 md3 k ii HB HJ Hi10) as Hrow.
  destruct (w4f_f34_cat_facts ly3 S3 W3 mem3 md3 HAR) as (Hcadr & Hcvis).
  assert (Hraddr : B.AsanRT.addressable mem3 (ACtlCutP.SM.CAT + ACtlCutP.SM.CAT_ROW * Z.of_nat ii) 296).
  { apply (B.AsanRTFacts.addressable_sub mem3 _ _ _ _ Hcadr); unfold ACtlCutP.SM.CAT_N; lia. }
  (* 1. the stretch 0x82bf4 -> 0x83114 *)
  apply w4f_enter.
  eapply w4f_run.
  { eapply (B.Prog.Seg.F34F.f34_evt_ro_pre_F_on _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3
       (ACtlCutP.Sfr fr) A ACtlCutP.SM.CAT (ACtlCutP.SM.CAT_ROW * Z.of_nat ii) (fr + 64) sp
       (ACtlCut.c_sp cx - 32768) (ACtlCutP.SM.rowb (Z.of_nat ii)) ob (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    - exact Hr2.
    - exact Hr9.
    - exact Hr19.
    - exact Hr10.
    - exact Hr11.
    - exact Hr12.
    - exact Hr21.
    - exact Hr23.
    - rewrite HS. lia.
    - rewrite HS. unfold B.AsanRT.HIGHMEM_BEG. lia.
    - intros kk Hkk. replace (ACtlCutP.Sfr fr + 8 + kk) with (ACtlCutP.Sfr fr + (8 + kk)) by lia.
      exact (proj1 (w4f_cut_fsh cx ly3 S3 W3 mem3 md3 k fr (ACtlCutP.Sfr fr + (8 + kk)) HJ HF HG1 HSWC
                      ltac:(unfold ACtlCutP.Sfr; lia) (Hshin (8 + kk) ltac:(lia)))).
    - intros kk Hkk. replace (ACtlCutP.Sfr fr + 8 + kk) with (ACtlCutP.Sfr fr + (8 + kk)) by lia.
      exact (Hshin (8 + kk) ltac:(lia)).
    - lia.
    - unfold B.AsanRT.APPMEM_END. lia.
    - intros kk Hkk. apply Happs. lia.
    - apply Happs. lia.
    - intros kk Hkk. exact (w4f_f34_slot_sh fr kk Hq8 Hkk).
    - exact Hob.
    - exact Hoblen.
    - exact Q152.
    - unfold B.AsanRT.HIGHMEM_BEG. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Hal.
    - exact Hrlen.
    - exact Hok.
    - exact Hrow.
    - exact Hraddr.
    - apply (w4f_f34_stk_present cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
    - unfold B.AsanRT.HIGHMEM_BEG. lia.
    - lia.
    - unfold B.AsanRT.APPMEM_END. lia.
    - left. lia.
    - lazymatch goal with |- ?x <= _ => assert (Ex : x = 6283264) by reflexivity; rewrite Ex; lia end.
    - exact HRO.
    - exact HAC.
    - apply B.ProgBridge.rng_of_visible. apply (w4f_f34_vis_fsh cx ly3 S3 W3 mem3 md3 k fr _ _ HJ HF HG1); lia.
    - apply B.ProgBridge.rng_of_visible. apply (w4f_vis_stack cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k _ _ HJ);
        unfold Reusable.YCfn.LLVMF_STK; lia. }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' (m1 & -> & MU1 & WM1 & RO1 & SW1 & ST1 & BR1 & OB1 & AR1 & AO1) Hs1 Hhid1.
  assert (J1 : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m1 md' k).
  { apply (w4f_f34_aj_step cx _ ly3 S3 W3 mem3 md3 m1 md' k _ HJ MU1 WM1 Hhid1 Hs1).
    - intros a Ha. destruct (w4f_f34_not_out _ _ Ha) as (l & h & Hin & Hb). cbn [In] in Hin.
      destruct Hin as [E|[]]. injection E as <- <-. rewrite HS in Hb.
      assert (Ei : Reusable.YImgTop.IMG_TOP = 6283264) by reflexivity. lia.
    - intros a Ha. destruct (w4f_f34_not_out _ _ Ha) as (l & h & Hin & Hb). cbn [In] in Hin.
      destruct Hin as [E|[]]. injection E as <- <-.
      right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
      right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
      change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. rewrite HS in Hb. lia. }
  assert (AC1 : B.AsanRT.asan_cells m1).
  { apply (B.AsanRTFacts.asan_cells_kept _ mem3 m1 HAC MU1). cbn [lib.Lib.Frame.disjoint_from]. rewrite HS.
    unfold B.AsanRT.RT_LO, B.AsanRT.RT_HI. split; [left; lia | exact I]. }
  (* 2. declaration_of *)
  assert (Usp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply lib.Lib.MState.unsigned_lit; lia).
  assert (Ua0 : bv_unsigned (Z_to_bv 64 (ACtlCutP.SM.CAT + ACtlCutP.SM.CAT_ROW * Z.of_nat ii)) =
                ACtlCutP.SM.CAT + ACtlCutP.SM.CAT_ROW * Z.of_nat ii) by (apply lib.Lib.MState.unsigned_lit; lia).
  assert (Ua1 : bv_unsigned (Z_to_bv 64 (fr + 64)) = fr + 64) by (apply lib.Lib.MState.unsigned_lit; lia).
  eapply w4f_run.
  { eapply (w4f_f34_decl_lift declaration_of_F_holds_on (Reusable.YA0n.w_H W3) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              _ _ _ _ _ _ m1 (ACtlCut.c_sp cx - 32768) (ACtlCutP.SM.rowb (Z.of_nat ii)) ob).
    - rewrite Usp. exact ST1.
    - rewrite Usp. lia.
    - rewrite Ua0. exact Hal.
    - exact Hrlen.
    - rewrite Ua0. exact BR1.
    - rewrite Ua1. exact OB1.
    - rewrite Ua0, Ua1. right. lia.
    - rewrite Ua0, Usp. left. lia.
    - rewrite Ua1, Usp. left. lia.
    - exact RO1.
    - rewrite Ua1. assert (Ei : Reusable.YImgTop.IMG_TOP = 6283264) by reflexivity. lia.
    - exact AC1.
    - rewrite Ua0, Ua1. apply SW1.
      apply (B.ShadowRwOn.shadow_rw_on_mono
               (fun a => B.ACtlRtC.cut_shadow B ly3 S3 a \/ B.ACtlRtC.img_shadow a)).
      + intros a Ha.
        exact (w4f_f34_decl_region ly3 S3 (ACtlCut.c_fpos cx) fr ii a ltac:(rewrite HF; left; reflexivity) Efr
                 Hfr32 ltac:(lia) ltac:(lia) Ha).
      + exact (B.ShadowRwOn.shadow_rw_on_union _ _ mem3 HSWC HIMG).
    - unfold B.AsanRT.HIGHMEM_BEG. lia.
    - rewrite Usp. unfold B.AsanRT.APPMEM_END. lia.
    - rewrite Ua0. exact AR1.
    - rewrite Ua1. exact AO1.
    - rewrite Ua1. apply Happs. lia.
    - rewrite Ua1. right. unfold B.AsanRT.RT_HI. lia.
    - rewrite Usp. apply (w4f_vis_stack cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k _ _ HJ);
        unfold Reusable.YCfn.LLVMF_STK; lia.
    - rewrite Usp. apply (w4f_f34_vis_stksh cx _ ly3 S3 W3 mem3 md3 k _ _ HJ); unfold Reusable.YCfn.LLVMF_STK; lia.
    - exact (B.ProgBridge.rt_vis_W W3).
    - exact (B.ProgBridge.img_vis_W W3).
    - rewrite Ua0. apply (B.ProgBridge.range_visible_sub _ _ _ _ _ (B.ProgBridge.img_vis_W W3));
        unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI; lia.
    - rewrite Ua0. destruct (w4f_f34_rowsh_in (Z.of_nat ii) ltac:(lia)) as (R1 & R2 & R3).
      apply (B.ProgBridge.range_visible_sub _ _ _ _ _ Hcvis);
        unfold ACtlCutP.SM.CAT, ACtlCutP.SM.CAT_ROW, ACtlCutP.SM.CAT_N; [exact R1 | exact R2 | exact R3].
    - rewrite Ua1. apply (w4f_vis_frame cx ly3 S3 W3 mem3 md3 k fr _ _ HJ HF HG1); lia.
    - rewrite Ua1. destruct (w4f_f34_slotsh_in fr Hq8 ltac:(lia)) as (R1 & R2 & R3).
      apply (w4f_f34_vis_fsh cx ly3 S3 W3 mem3 md3 k fr _ _ HJ HF HG1); [exact R1 | exact R2 | exact R3]. }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms'' md'' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> &
    MU2 & WM2 & RO2 & ST2 & RW2 & BA2 & AC2 & SW2) Hs2 Hhid2.
  rewrite Usp, Ua1 in MU2. rewrite Usp in ST2. rewrite Ua1 in RW2. rewrite Hok in RW2 |- *.
  assert (MU2' : lib.Lib.Frame.munch [(sp - 2256, sp); (fr + 64, fr + 96)] m1 m2).
  { intros x Hx. apply MU2. cbn [lib.Lib.Frame.outside] in Hx |- *. destruct Hx as (Hx1 & Hx2 & _).
    split; [exact Hx1 | split; [lia | exact I]]. }
  assert (J2 : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m2 md'' k).
  { apply (w4f_f34_aj_step cx _ ly3 S3 W3 m1 md' m2 md'' k _ J1 MU2' WM2 Hhid2 Hs2).
    - intros a Ha. destruct (w4f_f34_not_out _ _ Ha) as (l & h & Hin & Hb). cbn [In] in Hin.
      assert (Ei : Reusable.YImgTop.IMG_TOP = 6283264) by reflexivity.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
    - intros a Ha. destruct (w4f_f34_not_out _ _ Ha) as (l & h & Hin & Hb). cbn [In] in Hin.
      destruct Hin as [E|[E|[]]]; injection E as <- <-.
      + left. unfold Reusable.YCfn.LLVMF_STK. lia.
      + right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
        left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
        change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia. }
  pose proof (w4f_ctlrt _ _ _ _ _ _ _ _ HB J2) as HRT2.
  pose proof HRT2 as (_ & HSWC2 & _).
  (* the memory of the exit cut against the entry's *)
  assert (MUa : lib.Lib.Frame.munch (w4f_f34_WR fr sp) mem3 m2).
  { intros x Hx. unfold w4f_f34_WR in Hx. cbn [lib.Lib.Frame.outside] in Hx. destruct Hx as (Hx1 & Hx2 & Hx3 & _).
    rewrite (MU2' x ltac:(cbn [lib.Lib.Frame.outside]; split; [exact Hx2 | split; [exact Hx3 | exact I]])).
    apply MU1. cbn [lib.Lib.Frame.outside]. split; [exact Hx1 | exact I]. }
  pose proof (lib.Lib.Frame.wmono_trans B.Img0.rsegs _ _ _ WM1 WM2) as WMa.
  destruct RW2 as (((Hdlen & _) & Hdbb) & _).
  cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hdbb. rewrite app_nil_r in Hdbb.
  pose proof (w4f_f34_stk_m fr sp mem3 m2 _ HG MUa WMa Hstk Hdbb Hdlen) as Hstk2.
  assert (Hsh2 : exists sh, lib.Lib.Mem.bytes_at segs m2 (ACtlCutP.Sfr fr) sh /\
                   length sh = Z.to_nat ACtlCutP.FRAME_SHADOW).
  { assert (Hst : lib.Lib.Frame.stk B.Img0.rsegs m2 (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 392)).
    { split; [rewrite HS; lia|]. split; [rewrite HS; lia|]. intros a Ha.
      pose proof (Hshin (a - ACtlCutP.Sfr fr) ltac:(lia)) as Hi.
      replace (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) with a in Hi by lia.
      exact (w4f_cut_fsh cx ly3 S3 W3 m2 md'' k fr a J2 HF HG1 HSWC2 ltac:(unfold ACtlCutP.Sfr in *; lia) Hi). }
    destruct (lib.Lib.Frame.stk_bytes B.Img0.rsegs m2 _ _ Hst ltac:(lia)) as (sh & Hl & Hb).
    exists sh. split; [exact Hb|]. rewrite Hl. change ACtlCutP.FRAME_SHADOW with 392. f_equal. lia. }
  assert (Hadr2 : B.AsanRT.addressable m2 (fr + 64) 32).
  { apply (B.AsanRTFacts.addressable_kept m1 m2 _ _ AO1).
    apply (B.AsanRTFacts.munch_meta _ m1 m2 MU2'). cbn [B.AsanRTFacts.all_app].
    unfold B.AsanRTFacts.app_ivl. split; [intros a Ha | split; [intros a Ha | exact I]];
      unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END; lia. }
  (* the turn's heap block *)
  assert (Hin_phi : In (phi, ACtlCutP.flen cx jj) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hin_phi) as (_ & Hp4096 & Hpceil & Hpapp & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi _ 6 _ HAR Hin_phi Hin6) as Hpsep.
  rewrite <- Efr in Hpsep. unfold Reusable.YG0f.zdisjoint in Hpsep. cbn [fst snd] in Hpsep.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hpsep.
  pose proof (B.Prog.Seg.F34.f34_rowsel_len (ACtlCut.c_in cx) jj Hsel) as Hlen50.
  assert (Ereq : Reusable.YG00.req_size (ACtlCutP.flen cx jj) = ACtlCutP.flen cx jj).
  { unfold Reusable.YG00.req_size, ACtlCutP.flen. destruct (Z.eqb_spec (ACtlCutP.SM.t_len (ACtlCut.c_in cx) jj) 0);
      [lia | reflexivity]. }
  rewrite Ereq in Hpceil, Hpapp, Hpsep.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hpapp.
  unfold ACtlCutP.flen in Hpceil, Hpapp, Hpsep.
  (* the body facts on the exit memory, entry registers *)
  assert (HFRAC2 : ACtlCutP.FRAC B cx fr fr regs3 m2)
    by exact (w4f_f34_FRAC_m cx fr fr regs3 mem3 m2 sp HG MUa HspZ ltac:(lia) Hsh2 HFRAC).
  assert (HLK2 : ACtlCutP.LK cx fr jj regs3 m2)
    by exact (w4f_f34_LK_m cx fr jj regs3 mem3 m2 sp A HG MUa Hr9 HspA ltac:(lia) Hstk2 HLK).
  assert (H272' : ACtlCutP.spill regs3 m2 272 (ACtlCutP.SM.t_k (ACtlCut.c_in cx) jj))
    by (w4f_f34_sp HG MUa Hr9).
  assert (HPTL2 : ACtlCutP.PTL cx jj phi fr regs3 m2)
    by (apply (w4f_f34_PTL_m cx jj phi fr regs3 mem3 m2 sp A HG MUa Hr9 HspA); try lia; exact Hstk2 || exact HPTL).
  assert (HFT2 : ACtlCutP.FTURN cx jj phi regs3 m2)
    by (apply (w4f_f34_FTURN_m cx jj phi fr regs3 mem3 m2 sp A HG MUa Hr9 HspA); try lia; exact HFT).
  assert (HIFS2 : ACtlCutP.IFS cx fr (S jj) regs3 m2) by exact (w4f_f34_IFS_m cx fr (S jj) regs3 mem3 m2 sp HG MUa HIFS).
  assert (HHB2 : ACtlCutP.HB m2 phi (ACtlCutP.flen cx jj)).
  { destruct HHB as (Hp0 & Hpadr). split; [exact Hp0|].
    eapply w4f_f34_addr_m; [exact HG | exact MUa | exact Hpadr |]. unfold B.ACtlK.a_size, ACtlCutP.flen. lia. }
  (* 3. the exit cut *)
  assert (Ert : lib.Lib.MState.ret_pc (Z_to_bv 64 0x82c24) = Z_to_bv 64 0x82c24) by (apply bv_eq; vm_compute; reflexivity).
  rewrite Ert.
  apply w4f_exit.
  apply (Hc24 cx [Z.of_nat j; Z.of_nat i] fr k ly3 S3 W3 _ m2 md'' HB J2 HF HG1 Hk); [| exact HRT2].
  cbn [ACtlCut.cut_body ACtlCut.ix_cut]. unfold ACtlCutP.C_B82c24_at. cbn [ACtlCut.cut_body]. cbv zeta.
  change (ACtlCutP.ixn 0 [Z.of_nat j; Z.of_nat i]) with jj. change (ACtlCutP.ixn 1 [Z.of_nat j; Z.of_nat i]) with ii.
  split; [reflexivity |].
  unfold ACtlCut.rgv in Hr9, Hr19.
  split.
  - apply (w4f_FRAC_tr _ _ _ _ regs3); [rewrite Hr2; reflexivity | reflexivity | reflexivity | reflexivity |
      rewrite Hr9; reflexivity | rewrite Hr19; reflexivity | reflexivity | exact HFRAC2].
  - exists phi. refine (conj Hperm (conj Hn (conj Hj (conj HHB2 (conj Hr18 (conj Hr20 (conj _ _))))))).
    + apply (w4f_FTURN_tr _ _ _ _ regs3); [rewrite Hr9; reflexivity | exact HFT2].
    + refine (conj _ (conj Hi10 (conj _ (conj I (conj _ (conj eq_refl (conj Hdbb (conj Hadr2 _)))))))).
      * apply (w4f_LK_tr _ _ _ _ regs3); [rewrite Hr9; reflexivity | reflexivity | exact HLK2].
      * apply (w4f_spill_tr _ regs3); [rewrite Hr9; reflexivity | exact H272'].
      * refine (conj Hi10 (conj eq_refl (conj _ (conj Hr25 (conj eq_refl (conj eq_refl (conj Hprev _))))))).
        -- unfold ACtlCut.rgv. transitivity (Z_to_bv 64 (ACtlCutP.SM.CAT_ROW * Z.of_nat ii + ACtlCutP.SM.CAT));
             [reflexivity | f_equal; lia].
        -- apply (w4f_PTL_tr _ _ _ _ _ regs3); [rewrite Hr9; reflexivity | reflexivity | reflexivity | exact HPTL2].
      * apply (w4f_IFS_tr _ _ _ _ regs3). exact HIFS2.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82c24_at j i (0x82c24) --S_F35--> B82c38_at j i.
   0x82c24 beqz a0,82c5c (not taken: a0 = 1); li a2,32; ld a0,312(s1) (phi + 18); mv a1,s6 (fr + 64);
   jal 0x42aac (ra 0x82c38) (UB Seg/F35.v:3-11).  The other form exits (B82bf4_at j (S i), B82ca0_at j) lie behind
   the `beqz`, which the body's rgv 10 1 refutes; they are premises only because ACtl.v's seg_F35 has them.
   SINK BRANCHES: none (objdump L85590-L85594). *)
Lemma seg_F35 : forall POST (j i : nat),
  ctl_from POST (ix C_B82bf4_at [Z.of_nat j; Z.of_nat (S i)]) ->
  ctl_from POST (ix C_B82c38_at [Z.of_nat j; Z.of_nat i]) -> ctl_from POST (ix C_B82ca0_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82c24_at [Z.of_nat j; Z.of_nat i]).
Proof.
  intros POST j i _ Hc38 _ cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  unfold ACtlCutP.C_B82c24_at in *. cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc
    ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  set (jj := ACtlCutP.ixn 0 [Z.of_nat j; Z.of_nat i]) in *.
  set (ii := ACtlCutP.ixn 1 [Z.of_nat j; Z.of_nat i]) in *.
  destruct HBODY as (HFRAC & phi & Hperm & Hn & Hj & HHB & Hr18 & Hr20 & HFT & HLK & Hi10 & H272 & _ & HRLc & Hr10 &
    Hdecl & Had64 & HIFS).
  pose proof HRLc as (_ & Hr23 & Hr24 & Hr25 & Hr21 & Hr22 & _ & HPTL).
  pose proof HPTL as (Hsel & _ & _ & _ & H312 & Hphi & _ & _ & _ & _).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _).
  unfold ACtlCutP.ART.APPMEM_END, ACtlCutP.FRAME_BYTES in HspEnd, HfrA.
  pose proof (w4f_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Bfr1 & Bfr2).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  pose proof Hastk as (Hsp16 & _ & Hcl & Hlsp & _). unfold Reusable.YCfn.LLVMF_STK in Hlsp.
  pose proof HB as (((_ & _ & _ & Hgp0 & _) & _) & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  pose proof (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Happ).
  rewrite <- (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) in Happ.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Happ.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Happ.
  (* the live block phi: len >= 50 on the row path, its 32 block bytes at phi + 18 *)
  assert (Hin : In (phi, ACtlCutP.flen cx jj) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hin)
    as (_ & Hp4096 & Hpc & Happb & Hpresb & _ & Hn0).
  assert (Hreq : ACtlCutP.flen cx jj <= Reusable.YG00.req_size (ACtlCutP.flen cx jj) /\
                 B.ACtlK.a_size (ACtlCutP.flen cx jj) = Reusable.YG00.req_size (ACtlCutP.flen cx jj)).
  { unfold B.ACtlK.a_size, Reusable.YG00.req_size.
    destruct (ACtlCutP.flen cx jj =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia. }
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Happb.
  assert (Hlen50 : 50 <= ACtlCutP.flen cx jj) by exact (B.Prog.Seg.F34.f34_rowsel_len _ _ Hsel).
  pose proof (B.Prog.Seg.F35.f35_phi_len (ACtlCut.c_in cx) jj) as HphiL.
  assert (HphiL50 : (50 <= length (ACtlCutP.SM.t_phi (ACtlCut.c_in cx) jj))%nat)
    by (unfold ACtlCutP.flen in Hlen50; lia).
  assert (Hblk : ACtlCutP.SM.t_blk (ACtlCut.c_in cx) jj =
                 firstn 32 (skipn 18 (ACtlCutP.SM.t_phi (ACtlCut.c_in cx) jj)))
    by (apply B.Prog.Seg.F35.f35_blk; exact HphiL50).
  assert (HBL : lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (phi + 18) (ACtlCutP.SM.t_blk (ACtlCut.c_in cx) jj)).
  { rewrite Hblk. exact (B.Prog.Seg.F35.f35_ba_sub mem3 phi _ 18 32 Hphi ltac:(lia)). }
  assert (HblkL : length (ACtlCutP.SM.t_blk (ACtlCut.c_in cx) jj) = 32%nat)
    by (rewrite Hblk, length_firstn, length_skipn; lia).
  assert (HdeclL : length (ACtlCutP.SM.decl_i (Z.of_nat ii)) = 32%nat)
    by (apply B.Prog.Seg.F34.f34_decl_len; lia).
  assert (Q312 : ACtlCutP.q64 mem3 (A + 312) (phi + 18)) by (apply (w4f_spill regs3 mem3 312 _ A H312 Hr9); lia).
  (* 0x82c24 -> 0x42aac (ra 0x82c38), memory unchanged *)
  apply w4f_enter.
  eapply w4f_run.
  { eapply (B.Prog.Seg.F35F.f35_evt_pre_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3
      A (phi + 18) (fr + 64) (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    - exact Hr9.
    - exact Hr10.
    - exact Hr22.
    - lia.
    - lia.
    - exact Q312.
    - apply B.ProgBridge.rng_of_visible. apply (w4f_vis_stack cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k _ _ HJ);
        unfold Reusable.YCfn.LLVMF_STK; lia. }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' -> Hs _.
  apply w4f_exit.
  match goal with |- Reusable.YA0n.SRr _ _ (Reusable.YG0d.cfg_at _ _ ?R _ _) _ => set (R1 := R) end.
  change 0x42aac with B.Prog.bcmp_wrap_c.BCMP_WRAP. rewrite <- B_bcmp_tramp_at.
  pose proof (w4f_aj_nowrite _ _ _ _ _ _ _ _ _ HJ Hs) as HJ'.
  assert (HspR1 : Reusable.YG0d.spZ R1 = sp) by exact HspZ.
  (* the bcmp trampoline, x = phi + 18, y = fr + 64, n = 32 *)
  eapply Reusable.YA0n.SRr_bind.
  { eapply (Reusable.YCbq.aj_bcmp_at segs B LAWS segs_low _ H_bcmp W3 R1 mem3 Reusable.YCfn.LLVMF_STK
      (ACtlCut.c_sp cx) FP (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
      (ACtlCut.own6 cx) ly3 S3 md' k (phi + 18) (fr + 64) 32 (sp - ACtlCut.c_sp cx) (Z_to_bv 64 0x82c38) HJ').
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite HspR1. lia.
    - rewrite Zminus_mod, Hspm, Hsp16. reflexivity.
    - lia.
    - unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK. lia.
    - transitivity (getr regs3 3); [reflexivity | rewrite Hr3; exact Hgp0].
    - exact Hr4.
    - reflexivity.
    - apply lib.Reusable.YK0s.ret_ok_even. reflexivity.
    - intros a Ha. split.
      + apply (Reusable.YCbq.aview_some_of_apresent segs). exact (proj1 (Hpresb a ltac:(lia))).
      + rewrite HspR1. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. split.
      + apply (Reusable.YCbq.aview_some_of_apresent segs).
        apply (w4f_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1). left. lia.
      + rewrite HspR1. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. unfold Reusable.YG0d.ESTACK. lia.
    - intros a Ha. unfold Reusable.YG0d.ESTACK. lia.
    - unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg,
        Reusable.YG0f.kHighMemEnd. lia.
    - unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg,
        Reusable.YG0f.kHighMemEnd. lia.
    - apply (Reusable.YCbq.range_addressable_of_block segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx jj));
        [exact HAR | exact Hin | lia | lia].
    - intros _. apply (Reusable.YCbq.shadow_hull_vis_of_block segs B LAWS ly3 S3 W3 mem3 md3 phi
        (ACtlCutP.flen cx jj)); [exact HAR | exact Hin | lia | lia | lia].
    - apply (w4f_bcmp_range_addr W3 mem3 (fr + 64) 32); [| exact Had64].
      intros i' Hi'. refine (proj1 (w4f_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr _ HJ HG1 (or_intror _))).
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
      Z.div_mod_to_equations. lia.
    - intros _. apply (w4f_bcmp_hull_frame cx ly3 S3 W3 mem3 md3 k fr); [exact HJ | exact HG1 | lia | lia | lia]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr2 & Hpres2).
  (* the raw bytes the successor body reads, over their visible regions *)
  assert (Hwin : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 8192 <= a < sp) ->
    Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem2 a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha Hna. apply Hfr2; [exact Ha | unfold Reusable.YG0d.ESTACK; lia]. }
  destruct (w4f_bcmp_frame_kept cx ly3 S3 W3 mem3 md3 k fr mem2 sp HJ HF HG1 Hsp4096 ltac:(lia) Hwin)
    as (KS & KF & KSH & KK).
  destruct (w4f_bcmp_block_kept ly3 S3 W3 mem3 md3 mem2 (sp - 8192) sp phi _ HAR Hin ltac:(lia) Hwin) as (KB & KBS).
  assert (Hpr : forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> exists b, mem2 (Z_to_bv 64 a) = Some b).
  { intros a Ha. unfold ACtlCutP.FRAME_BYTES in Ha.
    refine (proj2 (Hpres2 a (w4f_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr a HJ HG1 _))). left. lia. }
  pose proof (ctl_kind_name_addressable _ _ _ _ _ (proj1 HJ2)) as HKA.
  assert (KSA : MKEPT mem3 mem2 A (ACtlCut.c_sp cx)) by (intros x Hx; apply KS; lia).
  assert (KBF : MKEPT mem3 mem2 phi (phi + ACtlCutP.flen cx jj)) by (intros x Hx; apply KB; lia).
  (* the callee-saved registers *)
  assert (E2 : getr regs2 2 = getr regs3 2) by exact (HP 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E3 : getr regs2 3 = getr regs3 3) by exact (HP 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E4 : getr regs2 4 = getr regs3 4) by exact (HP 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E8 : getr regs2 8 = getr regs3 8) by exact (HP 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E9 : getr regs2 9 = getr regs3 9)
    by exact (eq_trans (HP 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) (eq_sym Hr9)).
  assert (E18 : getr regs2 18 = getr regs3 18) by exact (HP 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E19 : getr regs2 19 = getr regs3 19) by exact (HP 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E20 : getr regs2 20 = getr regs3 20) by exact (HP 20 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E21 : getr regs2 21 = getr regs3 21) by exact (HP 21 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E22 : getr regs2 22 = getr regs3 22)
    by exact (eq_trans (HP 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) (eq_sym Hr22)).
  assert (E23 : getr regs2 23 = getr regs3 23) by exact (HP 23 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E24 : getr regs2 24 = getr regs3 24) by exact (HP 24 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E25 : getr regs2 25 = getr regs3 25) by exact (HP 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E26 : getr regs2 26 = getr regs3 26) by exact (HP 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E27 : getr regs2 27 = getr regs3 27) by exact (HP 27 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  apply (Hc38 cx [Z.of_nat j; Z.of_nat i] fr k ly3 S3 W3 regs2 mem2 md2 HB HJ2 HF HG1 Hk);
    [| exact (w4f_ctlrt _ _ _ _ _ _ _ _ HB HJ2)].
  cbn [ACtlCut.cut_body ACtlCut.ix_cut]. unfold ACtlCutP.C_B82c38_at. cbn [ACtlCut.cut_body]. cbv zeta.
  fold jj ii.
  split; [reflexivity |].
  split.
  { apply (w4f_bcmp_FRAC cx fr fr regs2 regs3 mem3 mem2 E2 E3 E4 E8 E9 E19 E26); [| exact KF | exact KSH | exact HFRAC].
    intros x Hx. apply KS. lia. }
  exists phi.
  refine (conj Hperm (conj Hn (conj Hj (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hi10 (conj _ (conj I (conj _
    (conj _ (conj _ (conj _ _))))))))))))))).
  - apply (w4f_bcmp_HB mem3 mem2 phi _); [intros i' Hi'; apply KBS; lia | exact HHB].
  - exact (w4f_rgv_tr regs2 regs3 18 _ E18 Hr18).
  - exact (w4f_rgv_tr regs2 regs3 20 _ E20 Hr20).
  - exact (w4f_bcmp_FTURN cx jj phi regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) Hr9 E9 ltac:(lia) ltac:(lia)
      ltac:(lia) KSA KBF HFT).
  - exact (w4f_bcmp_LK cx fr jj regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) Hr9 E9 E27 ltac:(lia) ltac:(lia)
      ltac:(lia) KSA KF KSH KK HKA Hpr HLK).
  - exact (w4f_bcmp_sp regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) 272 _ Hr9 E9 ltac:(lia) ltac:(lia) ltac:(lia) KSA
      ltac:(lia) H272).
  - exact (w4f_bcmp_RLc cx jj ii phi fr regs2 regs3 mem3 mem2 A (ACtlCut.c_sp cx) Hr9 E9 E18 E20 E21 E22 E23 E24
      E25 ltac:(lia) ltac:(lia) ltac:(lia) KSA KBF KF Hpr HRLc).
  - rewrite Hv. apply (iff_trans Hcmp).
    apply (w4f_bcmp_cmp W3 mem3 (phi + 18) (fr + 64) _ _ 32).
    + rewrite HblkL, HdeclL. reflexivity.
    + rewrite HblkL. reflexivity.
    + exact HBL.
    + exact Hdecl.
    + intros i' Hi'. exact (proj1 (proj1 (Hpresb (phi + 18 + i') ltac:(lia)))).
    + intros i' Hi'.
      refine (proj1 (w4f_bcmp_frame_present cx ly3 S3 W3 mem3 md3 k fr (fr + 64 + i') HJ HG1 _)). left. lia.
  - apply (w4f_bcmp_bytes mem3 mem2 (fr + 64) _); [intros x Hx; apply KF; rewrite HdeclL in Hx; lia | exact Hdecl].
  - apply (w4f_bcmp_addr mem3 mem2 (fr + 64) 32); [| exact Had64]. intros i' Hi'. apply KSH.
    unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr. Z.div_mod_to_equations. lia.
  - exact (w4f_bcmp_IFS cx fr (S jj) regs2 regs3 mem3 mem2 KF KSH HIFS).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82c38_at j i (0x82c38) --S_F36--> B82bf4_at j (S i) | B82ca0_at j.
   0x82c38 bnez s8,82c40 (taken: s8 = CAT + 296 i <> 0); sb s11,8..11(s3) (the row slot's shadow := 0xf8);
   li s6,1; beqz a0,82c88 (hit: the block is row i's declaration) else the latch 0x82c70-0x82c80 (a0 = [fr + 32]
   = 11; s9 := i + 1; s7 += 296; bltu s9,a0,82be4 -> the row head -> 0x82bf4 at row i + 1, or i = 10: 0x82c84
   li s7,0); 0x82c88 sb s11,4(s3); j 82c94; 0x82c94 mv a0,s2; mv a1,s4; jal reac_box_catalogue_match (entry
   0x84e40, ra 0x82ca0) (UB Seg/F36.v:3-25).
   SINK BRANCH (objdump L85596): 0x82c3c `beqz a0,82fa0` (plan F.4.1 row 70): never executed, the guard
   `bnez s8` is taken because RLc pins s8 = CAT + 296 i with CAT = 0x9f620 <> 0; discharged INSIDE f36_evt_pre_F. *)
(* Proof: f36_evt_pre_F (the four shadow bytes [Sfr fr + 8, Sfr fr + 12) of the owned frame; journal by
   w4f_f36_aj_store, body bytes kept off the write by w4f_f36_munchK / w4f_f36_R_off, FRAC's shadow bytes by
   w4f_f36_sh_store), then on a0 (the F35 bcmp's result, the body's a0 = 0 <-> t_blk j = decl_i i):
   HIT   f36_evt_hit_F, then the tail (f36_evt_c24_F, f36_evt_call_pre_F, w4f_f36_match) with
         s7 = CAT + 296 i = t_want_m j (B.Prog.Seg.Tac_f36.f36_want_m_hit: rowsel from PTL, the earlier rows from RLc);
   MISS, i < 10: f36_evt_next_F (the reads [A + 160, A + 168) and [fr + 32, fr + 40) from PTL's spill 160 and
         q64 (fr + 32) 11) and the cut B82bf4_at j (S i): RL (S i) from the run's registers, RLc's earlier rows and
         this miss;
   MISS, i = 10: f36_evt_last_F, then the tail with s7 = 0 = t_want_m j (B.Prog.Seg.Tac_f36.f36_want_m_miss). *)
Lemma seg_F36 : forall POST (j i : nat),
  ctl_from POST (ix C_B82bf4_at [Z.of_nat j; Z.of_nat (S i)]) ->
  ctl_from POST (ix C_B82ca0_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82c38_at [Z.of_nat j; Z.of_nat i]).
Proof.
  intros POST j i Hbf4 Hca0 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  unfold ACtlCutP.C_B82c38_at in *. cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc
    ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  change (ACtlCutP.ixn 0 [Z.of_nat j; Z.of_nat i]) with (Z.to_nat (Z.of_nat j)) in *.
  change (ACtlCutP.ixn 1 [Z.of_nat j; Z.of_nat i]) with (Z.to_nat (Z.of_nat i)) in *.
  rewrite !Nat2Z.id in *.
  destruct HBODY as (HFRAC & HP).
  destruct HP as (phi & Hperm & Hn & Hj & HHB & Hr18 & Hr20 & HFT & HLK & Hi10 & H272 & _ & HRLc & Hiff & _ & _ &
    HIFS).
  pose proof HRLc as (_ & Hr23 & Hr24 & Hr25 & Hr21 & _ & Hprev & HPTL).
  pose proof HPTL as (Hsel & _ & _ & H152 & _ & _ & _ & H160 & Hq32 & _).
  pose proof HLK as (_ & _ & _ & (Hr27 & _)).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _ & _ & _ & _ & _ & Hsh & _).
  unfold ACtlCutP.ART.APPMEM_END, ACtlCutP.FRAME_BYTES in *.
  pose proof (w4f_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Bfr1 & Bfr2).
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof (bv_unsigned_in_range 64 (getr regs3 2)) as Hspr.
  unfold bv_modulus in Hspr. cbn [Z.of_N] in Hspr. unfold Reusable.YG0d.spZ in HspZ.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
  destruct Hstk0 as (_ & _ & Hslo0 & Hslo1 & Hshi0 & Hshi1 & _).
  unfold Reusable.YCfn.LLVMF_STK in *.
  assert (Hfapp : Reusable.YG0f.in_app fr 4096).
  { destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR
                ltac:(rewrite HF; left; reflexivity)) as (_ & _ & Happ).
    rewrite Efr. exact Happ. }
  assert (Hin3 : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hin3) as (_ & _ & _ & Hpapp & _ & _ & Hlen).
  pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx j) ltac:(lia)) as Hrq.
  unfold ACtlCutP.flen in *.
  assert (HSf : 0x7fff8000 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 512 <= 0x10007fff8000)
    by (unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia).
  assert (NI : forall x, fr <= x < fr + 3136 -> ~ Reusable.YG0d.in_img segs x).
  { intros x Hx. apply (Reusable.YCbq.frm_img segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) x HAR);
      [rewrite HF; left; reflexivity |].
    rewrite <- Efr. change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia. }
  assert (Roff : forall x, w4f_f36_R cx A fr phi (ACtlCutP.SM.t_len (ACtlCut.c_in cx) j) x ->
                           0 <= x < 2 ^ 64 /\ ~ (ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 328))
    by (intros x Hx; exact (w4f_f36_R_off cx A fr phi (ACtlCutP.SM.t_len (ACtlCut.c_in cx) j) _ x Hfapp Hpapp
                              ltac:(lia) ltac:(lia) ltac:(lia) Hx)).
  destruct (w4f_f36_stk_fsh cx ly3 S3 W3 mem3 md3 k fr (ACtlCutP.Sfr fr + 8) (ACtlCutP.Sfr fr + 12) HJ HG1)
    as (Hst8 & Hv8); [unfold ACtlCutP.Sfr in *; lia .. |].
  (* 0x82c38 .. 0x82c54: the four shadow stores and s6 := 1 *)
  apply w4f_enter.
  eapply w4f_run.
  { eapply (B.Prog.Seg.Tac_f36F.f36_evt_pre_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (ACtlCutP.Sfr fr) (ACtlCutP.SM.CAT + ACtlCutP.SM.CAT_ROW * Z.of_nat i)
              (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    - exact Hr19.
    - exact Hr24.
    - exact Hr27.
    - unfold ACtlCutP.SM.CAT, ACtlCutP.SM.CAT_ROW. lia.
    - exact Hst8.
    - apply B.ProgBridge.rng_of_visible. replace 4 with (ACtlCutP.Sfr fr + 12 - (ACtlCutP.Sfr fr + 8)) by lia.
      exact Hv8. }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms1 md1 (m1 & -> & MU1 & WM1 & ST1 & _) Hs1 Hhid1.
  assert (HJ1 : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m1 md1 k).
  { apply (w4f_f36_aj_store cx ly3 S3 W3 mem3 m1 md3 md1 k fr (ACtlCutP.Sfr fr + 8) (ACtlCutP.Sfr fr + 12)
             HJ HF HG1); [unfold ACtlCutP.Sfr in *; lia .. | | | |].
    - exact MU1.
    - exact ST1.
    - exact Hhid1.
    - exact Hs1. }
  pose proof HJ1 as (HAR1 & _).
  assert (K1 : forall x, w4f_f36_R cx A fr phi (ACtlCutP.SM.t_len (ACtlCut.c_in cx) j) x -> w4f_f36_K mem3 m1 x).
  { intros x Hx. destruct (Roff x Hx) as (Hx1 & Hx2).
    apply (w4f_f36_munchK mem3 m1 _ _ x MU1 Hx1). lia. }
  pose proof (w4f_f36_sh_store mem3 m1 fr _ _ Hsh MU1 ST1 ltac:(lia)) as Hsh1.
  (* The tail from 0x82c88 (HIT and the last row's MISS): the shadow store Sfr fr + 4, the call, the cut. *)
  assert (TAIL : forall (R1 : bvmap 5 word) md1',
    AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m1 md1' k ->
    getr R1 2 = getr regs3 2 -> getr R1 3 = getr regs3 3 -> getr R1 4 = getr regs3 4 -> getr R1 8 = getr regs3 8 ->
    getr R1 9 = getr regs3 9 -> getr R1 18 = getr regs3 18 -> getr R1 19 = getr regs3 19 ->
    getr R1 20 = getr regs3 20 -> getr R1 26 = getr regs3 26 -> getr R1 27 = getr regs3 27 ->
    ACtlCut.rgv R1 22 1 -> ACtlCut.rgv R1 23 (ACtlCutP.SM.t_want_m (ACtlCut.c_in cx) j) ->
    Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x82c88 R1 m1 md1') (POST cx)).
  { intros R1 md1' HJm E2 E3 E4 E8 E9 E18 E19 E20 E26 E27 Hs6 Hs7.
    destruct (w4f_f36_stk_fsh cx ly3 S3 W3 m1 md1' k fr (ACtlCutP.Sfr fr + 4) (ACtlCutP.Sfr fr + 5) HJm HG1)
      as (Hst4 & Hv4); [unfold ACtlCutP.Sfr in *; lia .. |].
    apply w4f_enter.
    eapply w4f_run.
    { eapply (B.Prog.Seg.Tac_f36F.f36_evt_c24_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                (ACtlCutP.Sfr fr) (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
      - rewrite <- Hr19. exact E19.
      - exact Hst4.
      - apply B.ProgBridge.rng_of_visible. replace 1 with (ACtlCutP.Sfr fr + 5 - (ACtlCutP.Sfr fr + 4)) by lia.
        exact Hv4. }
    { apply B.ProgBridge.fp_avoids_RNG_W. }
    intros ms2 md2 (m2 & -> & (MU2 & WM2 & ST2 & _)) Hs2 Hhid2.
    assert (HJ2 : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m2 md2 k).
    { apply (w4f_f36_aj_store cx ly3 S3 W3 m1 m2 md1' md2 k fr (ACtlCutP.Sfr fr + 4) (ACtlCutP.Sfr fr + 5)
               HJm HF HG1); [unfold ACtlCutP.Sfr in *; lia .. | | | |].
      - exact MU2.
      - exact ST2.
      - exact Hhid2.
      - exact Hs2. }
    pose proof HJ2 as (HAR2 & _).
    assert (Kc : forall x, w4f_f36_R cx A fr phi (ACtlCutP.SM.t_len (ACtlCut.c_in cx) j) x -> w4f_f36_K mem3 m2 x).
    { intros x Hx. destruct (Roff x Hx) as (Hx1 & Hx2).
      rewrite (w4f_f36_munchK m1 m2 _ _ x MU2 Hx1 ltac:(lia)). exact (K1 x Hx). }
    pose proof (w4f_f36_sh_store m1 m2 fr _ _ Hsh1 MU2 ST2 ltac:(lia)) as Hsh2.
    pose proof (ctl_kind_name_addressable ly3 S3 W3 m2 md2 HAR2) as KNA2.
    eapply w4f_run.
    { eapply B.Prog.Seg.Tac_f36F.f36_evt_call_pre_F. }
    { apply B.ProgBridge.fp_avoids_RNG_W. }
    intros ms3 md3' -> Hs3 _.
    apply w4f_exit.
    eapply (w4f_f36_match POST j j cx fr k ly3 S3 W3 _ m2 md3' phi (eq_sym (Nat2Z.id j)) Hca0 HB).
    - exact (w4f_aj_nowrite _ _ _ _ _ _ _ _ _ HJ2 Hs3).
    - exact HF.
    - exact HG1.
    - exact Hk.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact Hperm.
    - eapply (w4f_f36_FRAC_tr cx fr fr _ regs3 mem3 m2 A phi _); [exact E2 | exact E3 | exact E4 | exact E8 |
        exact E9 | exact E19 | exact E26 | exact Hr9 | lia | exact Kc | exact Hsh2 | exact HFRAC].
    - exact Hn.
    - exact Hj.
    - exact (w4f_rgv_tr _ regs3 18 _ E18 Hr18).
    - exact (w4f_rgv_tr _ regs3 20 _ E20 Hr20).
    - eapply (w4f_f36_FTURN_tr cx _ phi _ regs3 mem3 m2 A fr); [exact E9 | exact Hr9 | lia | lia | lia | exact Kc |
        exact HFT].
    - eapply (w4f_f36_LK_tr cx fr _ _ regs3 mem3 m2 A phi _); [exact E9 | exact E27 | exact Hr9 | lia .. |
        exact Kc | exact NI | exact KNA2 | exact HLK].
    - eapply (w4f_f36_spill_tr _ regs3 mem3 m2 272 _ A); [exact E9 | exact Hr9 | lia | lia | | exact H272].
      intros x Hx. apply Kc. unfold w4f_f36_R. lia.
    - exact Hs7.
    - eapply (w4f_f36_spill_tr _ regs3 mem3 m2 152 _ A); [exact E9 | exact Hr9 | lia | lia | | exact H152].
      intros x Hx. apply Kc. unfold w4f_f36_R. lia.
    - eapply (w4f_f36_spill_tr _ regs3 mem3 m2 160 _ A); [exact E9 | exact Hr9 | lia | lia | | exact H160].
      intros x Hx. apply Kc. unfold w4f_f36_R. lia.
    - exact (B.Prog.SlotInv.t_want_eq _ _).
    - eapply (w4f_f36_IFS_tr cx fr _ _ regs3 mem3 m2 A phi _); [exact Hfr32 | lia | lia | exact Kc | exact HIFS].
    - exact Hs6. }
  destruct (Z.eq_dec (bv_unsigned (getr regs3 10)) 0) as [E0 | E0].
  - (* HIT: the block is row i's declaration *)
    assert (Ha0 : getr regs3 10 = Z_to_bv 64 0) by (apply bv_eq; rewrite E0; reflexivity).
    assert (Hblk : ACtlCutP.SM.t_blk (ACtlCut.c_in cx) j = ACtlCutP.SM.decl_i (Z.of_nat i)) by exact (proj1 Hiff Ha0).
    assert (Hwm : ACtlCutP.SM.t_want_m (ACtlCut.c_in cx) j = ACtlCutP.SM.CAT + ACtlCutP.SM.CAT_ROW * Z.of_nat i)
      by exact (B.Prog.Seg.Tac_f36.f36_want_m_hit _ _ _ Hsel Hi10 Hprev Hblk).
    eapply w4f_run.
    { eapply B.Prog.Seg.Tac_f36F.f36_evt_hit_F. exact Ha0. }
    { apply B.ProgBridge.fp_avoids_RNG_W. }
    intros ms2 md2 -> Hs2 _.
    apply w4f_exit.
    apply (TAIL _ md2 (w4f_aj_nowrite _ _ _ _ _ _ _ _ _ HJ1 Hs2)); try reflexivity.
    unfold ACtlCut.rgv. rewrite Hwm. exact Hr23.
  - (* MISS *)
    assert (Hne : getr regs3 10 <> Z_to_bv 64 0) by (intros E; apply E0; rewrite E; reflexivity).
    assert (Hnb : ACtlCutP.SM.t_blk (ACtlCut.c_in cx) j <> ACtlCutP.SM.decl_i (Z.of_nat i))
      by (intros E; exact (Hne (proj2 Hiff E))).
    assert (Q160 : ACtlCutP.q64 m1 (A + 160) (fr + 32)).
    { apply (w4f_f36_q64_tr mem3 m1); [intros x Hx; apply K1; unfold w4f_f36_R; lia |].
      apply (w4f_spill regs3 mem3 160 _ A H160 Hr9); lia. }
    assert (Q32 : ACtlCutP.q64 m1 (fr + 32) 11).
    { apply (w4f_f36_q64_tr mem3 m1); [intros x Hx; apply K1; unfold w4f_f36_R; lia | exact Hq32]. }
    assert (V160 : ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + 160) 8).
    { apply B.ProgBridge.rng_of_visible. apply (w4f_vis_stack cx (ACtlCut.own6 cx) ly3 S3 W3 m1 md1 k _ _ HJ1);
        unfold Reusable.YCfn.LLVMF_STK; lia. }
    assert (V32 : ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (fr + 32) 8).
    { apply B.ProgBridge.rng_of_visible. apply (w4f_vis_frame cx ly3 S3 W3 m1 md1 k fr _ _ HJ1 HF HG1); lia. }
    destruct (Nat.lt_ge_cases i 10) as [Hlt | Hge].
    + (* the next row *)
      eapply w4f_run.
      { eapply (B.Prog.Seg.Tac_f36F.f36_evt_next_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  m1 A (fr + 32) i (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
        - exact Hr9.
        - exact (lib.Reusable.YK11.bv_eqb_neq _ _ Hne).
        - exact Hr25.
        - exact Hr23.
        - exact Hlt.
        - exact (w4f_q64_read _ _ _ Q160).
        - exact (w4f_q64_read _ _ _ Q32).
        - exact V160.
        - exact V32. }
      { apply B.ProgBridge.fp_avoids_RNG_W. }
      intros ms2 md2 -> Hs2 _.
      apply w4f_exit.
      apply (Hbf4 cx [Z.of_nat j; Z.of_nat (S i)] fr k ly3 S3 W3 _ m1 md2 HB
               (w4f_aj_nowrite _ _ _ _ _ _ _ _ _ HJ1 Hs2) HF HG1);
        [| | exact (w4f_ctlrt _ _ _ _ _ _ _ _ HB HJ1)].
      * cbn [ACtlCut.cut_kmax ACtlCut.ix_cut]. unfold ACtlCutP.C_B82bf4_at. cbn [ACtlCut.cut_kmax].
        change (ACtlCutP.ixn 0 [Z.of_nat j; Z.of_nat (S i)]) with (Z.to_nat (Z.of_nat j)).
        rewrite Nat2Z.id. exact Hk.
      * cbn [ACtlCut.cut_body ACtlCut.ix_cut]. unfold ACtlCutP.C_B82bf4_at. cbn [ACtlCut.cut_body]. cbv zeta.
        change (ACtlCutP.ixn 0 [Z.of_nat j; Z.of_nat (S i)]) with (Z.to_nat (Z.of_nat j)).
        change (ACtlCutP.ixn 1 [Z.of_nat j; Z.of_nat (S i)]) with (Z.to_nat (Z.of_nat (S i))).
        rewrite !Nat2Z.id.
        split; [reflexivity |].
        exists phi.
        refine (conj Hperm (conj _ (conj Hn (conj Hj (conj _ (conj _ (conj _ (conj _ (conj _ (conj I
          (conj _ (conj _ _)))))))))))).
        -- eapply (w4f_f36_FRAC_tr cx fr fr _ regs3 mem3 m1 A phi _); [reflexivity .. | exact Hr9 | lia | exact K1 |
             exact Hsh1 | exact HFRAC].
        -- exact (w4f_f36_HB ly3 S3 W3 m1 md1 phi _ HAR1 Hin3).
        -- eapply (w4f_f36_LK_tr cx fr _ _ regs3 mem3 m1 A phi _); [reflexivity | reflexivity | exact Hr9 | lia .. |
             exact K1 | exact NI | exact (ctl_kind_name_addressable ly3 S3 W3 m1 md1 HAR1) | exact HLK].
        -- reflexivity.
        -- intros E. discriminate E.
        -- eapply (w4f_f36_spill_tr _ regs3 mem3 m1 272 _ A); [reflexivity | exact Hr9 | lia | lia | | exact H272].
           intros x Hx. apply K1. unfold w4f_f36_R. lia.
        -- refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
           ++ lia.
           ++ reflexivity.
           ++ reflexivity.
           ++ exact Hr21.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ intros i' Hi'. destruct (Nat.eq_dec i' i) as [-> | Hii]; [exact Hnb | apply Hprev; lia].
           ++ eapply (w4f_f36_PTL_tr cx _ phi fr _ regs3 mem3 m1 A); [reflexivity | reflexivity | reflexivity |
                exact Hr9 | lia .. | exact K1 | exact NI | exact HPTL].
        -- eapply (w4f_f36_FTURN_tr cx _ phi _ regs3 mem3 m1 A fr); [reflexivity | exact Hr9 | lia | lia | lia |
             exact K1 | exact HFT].
        -- eapply (w4f_f36_IFS_tr cx fr _ _ regs3 mem3 m1 A phi _); [exact Hfr32 | lia | lia | exact K1 | exact HIFS].
    + (* the last row: no row matched *)
      assert (Ei : i = 10%nat) by lia. subst i.
      assert (Hwm : ACtlCutP.SM.t_want_m (ACtlCut.c_in cx) j = 0).
      { apply (B.Prog.Seg.Tac_f36.f36_want_m_miss _ _ Hsel).
        intros i' Hi'. destruct (Nat.eq_dec i' 10) as [-> | Hii]; [exact Hnb | apply Hprev; lia]. }
      eapply w4f_run.
      { eapply (B.Prog.Seg.Tac_f36F.f36_evt_last_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  m1 A (fr + 32) (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
        - exact Hr9.
        - exact (lib.Reusable.YK11.bv_eqb_neq _ _ Hne).
        - exact Hr25.
        - exact (w4f_q64_read _ _ _ Q160).
        - exact (w4f_q64_read _ _ _ Q32).
        - exact V160.
        - exact V32. }
      { apply B.ProgBridge.fp_avoids_RNG_W. }
      intros ms2 md2 (s7' & ->) Hs2 _.
      apply w4f_exit.
      apply (TAIL _ md2 (w4f_aj_nowrite _ _ _ _ _ _ _ _ _ HJ1 Hs2)); try reflexivity.
      unfold ACtlCut.rgv. rewrite Hwm. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82c84_at j (0x82c84) --S_F36_c20--> B82ca0_at j.
   0x82c84 li s7,0; 0x82c88 sb s11,4(s3); j 82c94; mv a0,s2; mv a1,s4; jal reac_box_catalogue_match (ra 0x82ca0)
   (UB Seg/F36.v:19-25).  SINK BRANCHES: none. *)
(* Proof: f36_evt_c20_F, f36_evt_c24_F (the one shadow byte Sfr fr + 4 of the owned frame: stk and rng from
   w4f_f36_stk_fsh, the journal by w4f_f36_aj_store, FRAC's shadow bytes by w4f_f36_sh_store, every other body
   byte kept off the write by w4f_f36_munchK / w4f_f36_R_off), f36_evt_call_pre_F, then w4f_f36_match with
   s7 = 0 = t_want_m j (the body) and t_want j = t_want_m j (B.Prog.SlotInv.t_want_eq). *)
Lemma seg_F36_c20 : forall POST (j : nat),
  ctl_from POST (ix C_B82ca0_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82c84_at [Z.of_nat j]).
Proof.
  intros POST j Hca0 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  unfold ACtlCutP.C_B82c84_at in *. cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc
    ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  destruct HBODY as (phi & Hperm & HFRAC & Hn & Hj & HHB & HLK & H272 & _ & Hwm & HPTL & HFT & HIFS & Hr22).
  pose proof HPTL as (_ & Hr18 & Hr20 & H152 & _ & _ & _ & H160 & _).
  pose proof HFRAC as (A & sp & Hr2 & Hspm & HspZ & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA448 & Hsp4096 & HspEnd & _ & _ & _ & _ & _ & Hsh & _).
  unfold ACtlCutP.ART.APPMEM_END, ACtlCutP.FRAME_BYTES in *.
  pose proof (w4f_frame_bounds cx ly3 S3 W3 mem3 md3 k fr HJ HF HG1) as (Bfr1 & Bfr2).
  pose proof (w4f_frame_at cx ly3 S3 W3 mem3 md3 k fr HJ HG1) as Efr.
  pose proof lib.Reusable.YM05.alloc_ceiling_val as Hceil.
  pose proof (bv_unsigned_in_range 64 (getr regs3 2)) as Hspr.
  unfold bv_modulus in Hspr. cbn [Z.of_N] in Hspr. unfold Reusable.YG0d.spZ in HspZ.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
  destruct Hstk0 as (_ & _ & Hslo0 & Hslo1 & Hshi0 & Hshi1 & _).
  unfold Reusable.YCfn.LLVMF_STK in *.
  assert (Hfapp : Reusable.YG0f.in_app fr 4096).
  { destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR
                ltac:(rewrite HF; left; reflexivity)) as (_ & _ & Happ).
    rewrite Efr. exact Happ. }
  assert (Hin3 : In (phi, ACtlCutP.flen cx (ACtlCutP.ixn 0 [Z.of_nat j])) (Reusable.YG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hin3) as (_ & _ & _ & Hpapp & _ & _ & Hlen).
  pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx (ACtlCutP.ixn 0 [Z.of_nat j])) ltac:(lia)) as Hrq.
  unfold ACtlCutP.flen in *.
  assert (HSf : 0x7fff8000 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 512 <= 0x10007fff8000)
    by (unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia).
  assert (NI : forall x, fr <= x < fr + 3136 -> ~ Reusable.YG0d.in_img segs x).
  { intros x Hx. apply (Reusable.YCbq.frm_img segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) x HAR);
      [rewrite HF; left; reflexivity |].
    rewrite <- Efr. change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia. }
  destruct (w4f_f36_stk_fsh cx ly3 S3 W3 mem3 md3 k fr (ACtlCutP.Sfr fr + 4) (ACtlCutP.Sfr fr + 5) HJ HG1)
    as (Hst4 & Hv4); [unfold ACtlCutP.Sfr in *; lia .. |].
  apply w4f_enter.
  eapply w4f_run.
  { eapply B.Prog.Seg.Tac_f36F.f36_evt_c20_F. }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms1 md1 -> Hs1 _.
  eapply w4f_run.
  { eapply (B.Prog.Seg.Tac_f36F.f36_evt_c24_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (ACtlCutP.Sfr fr) (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    - exact Hr19.
    - exact Hst4.
    - apply B.ProgBridge.rng_of_visible. replace 1 with (ACtlCutP.Sfr fr + 5 - (ACtlCutP.Sfr fr + 4)) by lia.
      exact Hv4. }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms2 md2 (m2 & -> & (MU & WM & ST & _)) Hs2 Hhid2.
  assert (HJ2 : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m2 md2 k).
  { apply (w4f_f36_aj_store cx ly3 S3 W3 mem3 m2 md1 md2 k fr (ACtlCutP.Sfr fr + 4) (ACtlCutP.Sfr fr + 5)
             (w4f_aj_nowrite _ _ _ _ _ _ _ _ _ HJ Hs1) HF HG1); [unfold ACtlCutP.Sfr in *; lia .. | | | |].
    - exact MU.
    - exact ST.
    - exact Hhid2.
    - exact Hs2. }
  pose proof HJ2 as (HAR2 & _).
  assert (Kc : forall x, w4f_f36_R cx A fr phi (ACtlCutP.SM.t_len (ACtlCut.c_in cx) (ACtlCutP.ixn 0 [Z.of_nat j])) x ->
                         w4f_f36_K mem3 m2 x).
  { intros x Hx.
    destruct (w4f_f36_R_off cx A fr phi (ACtlCutP.SM.t_len (ACtlCut.c_in cx) (ACtlCutP.ixn 0 [Z.of_nat j])) _ x
                Hfapp Hpapp ltac:(lia) ltac:(lia) ltac:(lia) Hx) as (Hx1 & Hx2).
    apply (w4f_f36_munchK mem3 m2 _ _ x MU Hx1). lia. }
  pose proof (w4f_f36_sh_store mem3 m2 fr _ _ Hsh MU ST ltac:(lia)) as Hsh2.
  pose proof (ctl_kind_name_addressable ly3 S3 W3 m2 md2 HAR2) as KNA2.
  eapply w4f_run.
  { eapply B.Prog.Seg.Tac_f36F.f36_evt_call_pre_F. }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms3 md3' -> Hs3 _.
  apply w4f_exit.
  eapply (w4f_f36_match POST j _ cx fr k ly3 S3 W3 _ m2 md3' phi eq_refl Hca0 HB).
  - exact (w4f_aj_nowrite _ _ _ _ _ _ _ _ _ HJ2 Hs3).
  - exact HF.
  - exact HG1.
  - exact Hk.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Hperm.
  - eapply (w4f_f36_FRAC_tr cx fr fr _ regs3 mem3 m2 A phi _); [reflexivity .. | exact Hr9 | lia | exact Kc |
      exact Hsh2 | exact HFRAC].
  - exact Hn.
  - exact Hj.
  - exact (w4f_rgv_tr _ regs3 18 _ eq_refl Hr18).
  - exact (w4f_rgv_tr _ regs3 20 _ eq_refl Hr20).
  - eapply (w4f_f36_FTURN_tr cx _ phi _ regs3 mem3 m2 A fr); [reflexivity | exact Hr9 | lia | lia | lia | exact Kc |
      exact HFT].
  - eapply (w4f_f36_LK_tr cx fr _ _ regs3 mem3 m2 A phi _); [reflexivity | reflexivity | exact Hr9 | lia .. |
      exact Kc | exact NI | exact KNA2 | exact HLK].
  - eapply (w4f_f36_spill_tr _ regs3 mem3 m2 272 _ A); [reflexivity | exact Hr9 | lia | lia | | exact H272].
    intros x Hx. apply Kc. unfold w4f_f36_R. lia.
  - unfold ACtlCut.rgv. rewrite Hwm. reflexivity.
  - eapply (w4f_f36_spill_tr _ regs3 mem3 m2 152 _ A); [reflexivity | exact Hr9 | lia | lia | | exact H152].
    intros x Hx. apply Kc. unfold w4f_f36_R. lia.
  - eapply (w4f_f36_spill_tr _ regs3 mem3 m2 160 _ A); [reflexivity | exact Hr9 | lia | lia | | exact H160].
    intros x Hx. apply Kc. unfold w4f_f36_R. lia.
  - exact (B.Prog.SlotInv.t_want_eq _ _).
  - eapply (w4f_f36_IFS_tr cx fr _ _ regs3 mem3 m2 A phi _); [exact Hfr32 | lia | lia | exact Kc | exact HIFS].
  - exact (w4f_rgv_tr _ regs3 22 _ eq_refl Hr22).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82c90_at j (0x82c90) --S_F36_c2c--> B82ca0_at j.
   0x82c90 li s7,0; 0x82c94 mv a0,s2; mv a1,s4; jal reac_box_catalogue_match (ra 0x82ca0) (UB Seg/F36.v:22-25).
   SINK BRANCHES: none. *)
(* Proof: f36_evt_c2c_F then f36_evt_call_pre_F at RNG := RNG_W (w_H W3) (no memory access, journal by
   w4f_aj_nowrite), then w4f_f36_match: s7 = 0 = t_want_m j (the body), t_want j = t_want_m j
   (B.Prog.SlotInv.t_want_eq, pure SlotModel), the rest of the cut body carried. *)
Lemma seg_F36_c2c : forall POST (j : nat),
  ctl_from POST (ix C_B82ca0_at [Z.of_nat j]) ->
  ctl_from POST (ix C_B82c90_at [Z.of_nat j]).
Proof.
  intros POST j Hca0 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HG1 Hk HBODY HRT.
  unfold ACtlCutP.C_B82c90_at in *. cbn [ACtlCut.cut_body ACtlCut.ix_cut ACtlCut.cut_own ACtlCut.cut_pc
    ACtlCut.cut_kmax] in *.
  destruct HBODY as [-> HBODY]. cbv zeta in HBODY.
  destruct HBODY as (phi & Hperm & HFRAC & Hn & Hj & HHB & HLK & Hwm & HPT & HFTK & HFT & HIFS).
  pose proof HPT as (Hr18 & _ & Hr20 & H152 & _ & _ & _ & H160 & _).
  pose proof HFTK as (_ & Hr22 & _ & H272 & _).
  apply w4f_enter.
  eapply w4f_run.
  { eapply B.Prog.Seg.Tac_f36F.f36_evt_c2c_F. }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' -> Hs _.
  eapply w4f_run.
  { eapply B.Prog.Seg.Tac_f36F.f36_evt_call_pre_F. }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms'' md'' -> Hs' _.
  apply w4f_exit.
  eapply (w4f_f36_match POST j _ cx fr k ly3 S3 W3 _ mem3 md'' phi eq_refl Hca0 HB).
  - exact (w4f_aj_nowrite _ _ _ _ _ _ _ _ _ (w4f_aj_nowrite _ _ _ _ _ _ _ _ _ HJ Hs) Hs').
  - exact HF.
  - exact HG1.
  - exact Hk.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Hperm.
  - apply (w4f_FRAC_tr _ _ _ _ regs3); try reflexivity; exact HFRAC.
  - exact Hn.
  - exact Hj.
  - exact (w4f_rgv_tr _ regs3 18 _ eq_refl Hr18).
  - exact (w4f_rgv_tr _ regs3 20 _ eq_refl Hr20).
  - apply (w4f_FTURN_tr _ _ _ _ regs3); try reflexivity; exact HFT.
  - apply (w4f_LK_tr _ _ _ _ regs3); try reflexivity; exact HLK.
  - exact (w4f_spill_tr _ regs3 _ _ _ eq_refl H272).
  - unfold ACtlCut.rgv. rewrite Hwm. reflexivity.
  - exact (w4f_spill_tr _ regs3 _ _ _ eq_refl H152).
  - exact (w4f_spill_tr _ regs3 _ _ _ eq_refl H160).
  - exact (B.Prog.SlotInv.t_want_eq _ _).
  - apply (w4f_IFS_tr _ _ _ _ regs3); exact HIFS.
  - exact (w4f_rgv_tr _ regs3 22 _ eq_refl Hr22).
Qed.

End W4f.

(* Stage lemmas of this file (all Qed), named as ACtl.v's stage hypotheses ([j] = [Z.of_nat j],
   [j; i] = [Z.of_nat j; Z.of_nat i]):
     seg_F30     : forall POST j, ctl_from POST (ix C_B82af8_at [j]) -> ctl_from POST (ix C_B82abc_at [j])
     seg_F31     : forall POST j, ctl_from POST (ix C_B82b38_at [j]) -> ctl_from POST (ix C_B82b5c_at [j]) ->
                                  ctl_from POST (ix C_B82af8_at [j])
     seg_F32     : forall POST j, ctl_from POST (ix C_B82bcc_at [j]) -> ctl_from POST (ix C_B82c90_at [j]) ->
                                  ctl_from POST (ix C_B82b38_at [j]) /\ ctl_from POST (ix C_B82b5c_at [j])
       (from seg_F32_b38 : .. (ix C_B82b5c_at [j]) -> .. (ix C_B82b38_at [j]) and
             seg_F32_b5c : .. (ix C_B82bcc_at [j]) -> .. (ix C_B82c90_at [j]) -> .. (ix C_B82b5c_at [j]))
     seg_F33     : forall POST j, ctl_from POST (ix C_B82bf4_at [j; 0]) -> ctl_from POST (ix C_B82c84_at [j]) ->
                                  ctl_from POST (ix C_B82bcc_at [j])
     seg_F34     : forall POST j i, ctl_from POST (ix C_B82c24_at [j; i]) -> ctl_from POST (ix C_B82bf4_at [j; i])
     seg_F35     : forall POST j i, ctl_from POST (ix C_B82bf4_at [j; S i]) -> ctl_from POST (ix C_B82c38_at [j; i]) ->
                                    ctl_from POST (ix C_B82ca0_at [j]) -> ctl_from POST (ix C_B82c24_at [j; i])
     seg_F36     : forall POST j i, ctl_from POST (ix C_B82bf4_at [j; S i]) -> ctl_from POST (ix C_B82ca0_at [j]) ->
                                    ctl_from POST (ix C_B82c38_at [j; i])
     seg_F36_c20 : forall POST j, ctl_from POST (ix C_B82ca0_at [j]) -> ctl_from POST (ix C_B82c84_at [j])
     seg_F36_c2c : forall POST j, ctl_from POST (ix C_B82ca0_at [j]) -> ctl_from POST (ix C_B82c90_at [j])
   Trap / sink obligations: S_F31 (0x82b04, 0x82b14, 0x82b24 -> 0x82fa4), S_F32 (0x82b38, 0x82b48, 0x82b58 ->
   0x82fa4; rows 65-67 -> 0x82fa0; two report paths), S_F34 (rows 68-69), S_F36 (row 70), each discharged inside
   its `_F` stretch from the cut-body conjuncts named at the stage. *)

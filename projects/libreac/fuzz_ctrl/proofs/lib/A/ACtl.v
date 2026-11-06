(* lib/A/ACtl.v -- the TOP and the COMPOSITION of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (libreac
   v1.9.0, ASan build), in the released cgif_file_fuzzer form.  Written by a Theorem Labs lane; single
   writer.  It states every segment's stage as a named Section hypothesis, PROVES the loop combinators and the
   backward chain, and PROVES the step from the chain to the core's lib contract A.ACfn.tfib_lib_contract_x.

   PROVENANCE
   - brief: top-compose.md (a working note, not in this delivery).
   - RULE 24 (released proofs first): proof-index LLVMFuzzerTestOneInput (index v5, built 2026-10-28
     20:16:23Z from e966c513ee6, ossv/recipes@a8831f7c5c), second-agent check a Theorem Labs lane 21:10Z CONFIRM:
     cgif/cgif_file_fuzzer is the only released ASan donor on this branch, LPS and framework.  This file follows
     that donor's own composition, proofs/cgif/cgif_file_fuzzer/lib/A/ACfj.v at origin/ossv/recipes c8557374ad2e:
     the loop lemma rt_G_allX (:157-163), the leaf lx_leaf_fail (:180-207), tfib_lib_x_body (:230-257) and
     tfib_lib_x (:258).  ctrl's own assembly of the same cuts, lib/A/Prog/Seg/Slot.v (not in this delivery) from a working branch
     6a74d5929d2 (S_ forms, vac_*, turn_* / loop_*, slot_entry), is the
     segment graph and the proof pattern of the loops.
   - cut layer: lib/A/ACtlCut.v (ctlcx, ctl_base, ctlcut, ctl_from, ix_cut / ctl_from_ix, ctl_post, ctl_rt) and
     lib/A/ACtlCutP.v (the cut records C_<cut>), a working branch 6446767144e plus the worktree's
     uncommitted edits (segs = the core's list, the core's arities, the cut state pinned by
     cfg_at, ix_cut, SK, asyms from YG0f).  Segment rows: the translation
     llvmf-cgif-walk-plan.md section 2.3 with Appendix B (a working note, not in this delivery), with the loops section 3,
     pieces section 5 and proved v1.9 runs Appendix A.
   - route (lead, 22:15Z, via a Theorem Labs lane): route (a).  ctrl's proved v1.9 segment runs are re-run in footprint form
     (_F over StepF) and the cut glue lifts each through a Theorem Labs lane's bridge into a stage.  The comment line
     "glue:" above each stage hypothesis names the proved run(s) its glue lifts (segment file, seg_ lemma and its
     line and commit from section 2.3, run lemmas from Appendix A).  U = 6a74d5929d2, E = e8259d2f41e.

   WHAT IS A HYPOTHESIS HERE, AND WHAT IS NOT
   - 94 stage hypotheses seg_<NAME>, one per live segment of section 2.3, in continuation form (the donor's rt_A2 /
     rt_B shape, A/ACf0.v:173, A/ACf1.v:499): forall POST, the exits' ctl_from -> the entry's ctl_from.  A W piece
     owes each one.  Three rows of section 2.3 have no hypothesis: S_Y2 (its entry C_A82bac is gone, Appendix B
     21:30Z and ACtlCutP.v's note, the class-full arm is discharged) and S_F36_82814 / S_F36_82820 (section 2.3
     "NOT USED by the composition", section 4 "dropped"; their entries C_A828c0_at / C_A828cc_at are reached by
     no segment).  Segment R1 is stated as its loop TURN (seg_R1_turn, ctrl's r1_turn R1.v:1275); its section-2.3
     form seg_R1 is PROVED below from that turn by the our[] combinator.
  - 12 non-stage hypotheses: RELRO_IMG (the read-only span is image bytes) and its three table bounds
    RELRO_KIND_NAME / RELRO_CAT / RELRO_FRAMES, LAWS (the core's AR laws) and MO_LE (the meter's mo_le, a Theorem Labs lane),
    the core's two symbol records for B, TFIB_SYMS and TFIB_LIB (porter 23:10Z; ctl_lib_x stays generic in B and
    takes both), KREPLY / KPARSE (the two callee constants' v1.9.0 values), LS_LEAF (the lib shape's tree is one
    leaf) and CHAIN_OF_CUT (the frame-pointer chain and call trace at an allocator call, ACtlCut.v section 1b).
  - batch 4's glue hypotheses (section 1c below), the names the stage glue files pass: AFREE4, MT_FREE, AMALLOC4,
    MO_MALLOC_OK, BLKSH, AIL, QMARK_ROW and the strcmp entry pin A_strcmp_tramp_at (all discharged at the top,
    section 9), batch 5's ASM6 (discharged at the top by the CtlTop Let CtrlB_asm6), and TPARSE, TREPLY,
    GLOBS_A_MARKED, batch 5's NAME_GLOB, TBUILD, CLS, CM_SPEC, AMEMCHR_SITE, H_strcmp (open).
    IMG_SHADOW_VIS is not a hypothesis: it is a Theorem Labs lane's proved ctrl_img_shadow_vis, bound by a Let.  Nor is
    CTLRT_ENTRY (route (C)'s ctl_rt_C at the entry): it is the proved A.ACtlTopFacts.ctlrt_C_entry, bound by a Let.
     Their reasons are at their declarations.  ctl_lib_x is closed `Proof using All`, so every Section hypothesis
     is an argument of ctl_lib_x.  ajournal_fp_nil is NOT a hypothesis: it is
     the donor's lemma and proof, copied verbatim below over the core's helpers (porter 22:43Z).
   - no Axiom, no Parameter, no Admitted, no admit.

   THREE DEPARTURES FROM THE BRIEF'S WORDING, EACH FORCED BY THE TYPES
   1. The exit post.  ctl_post (ACtlCut.v section 6) packs the leaf existentially.  The contract's goal is
      srealizes ... (LIBK pl (m_fs md) K), and for fuzz_ctrl's shape (ag_shape checksum_shape, ZTraceSpec.v:16:
      LIBK pl fs K = K (LL 0 fs [])) that fixes the leaf to LL 0 (m_fs md) [].  An existential leaf with the post's
      [sink_token] journal does not give m_fs md' = m_fs md, so the top cannot be closed from ctl_post.  The donor
      fixes the same leaf inside the walk's continuation (ACfj.v:186, HLEAF (LL 0 (m_fs (c_md cx)) [])).  So the
      exit stage seg_Y3 reaches ctl_post_leaf below (ctl_post with that leaf), the backward chain is proved for
      every POST, the brief's statement ctl_walk : ctl_from ... ctl_post C_ENTRY is derived from it by
      ctl_from_mono, and the top consumes ctl_walk_leaf.
   2. SK and FP are instantiated once, in the notation block of section 1, not declared: the journal's sink head
      is the core's A.AE2k.tfib_sink_head (the head the core's post journal uses), and the walk runs with FP = []
      as the donor's does.  A stage lemma proved for every SK and FP discharges its hypothesis by instantiation.
   3. srz_enter (donor A/ACfh.v:47, outside the core list) is not needed: the top applies SRr's own definition
      (Reusable.YA0n.SRr, donor YA0n.v:34-37) to the entry AI fact, which is srz_enter's whole proof (ACfh.v:50).
      So it is neither imported nor a hypothesis.

   NAMES THIS FILE TAKES FROM THE CORE (the relocated cgif core, porter's flat layout; nothing here is restated)
     A.ACfn      tfib_lib_contract_x (the statement proved), tfib_lib_post_x (ctl_post_leaf), A_LLVMF, RA_LLVMF,
                 LLVMF_STK, EV_LIB
     A.AB1v      tfibsegs, the core's segment list (donor A/AB1v.v:11; the porter confirms the name)
     A.AE2k      tfib_sink_head, the core's sink head (donor AE2k.v:44)
     A.AF0m      CtrlTSyms, the donor's TfibSyms (donor AF0m.v:292) under the core's name (AF0m.v:293)
     A.ACeh      TfibLib, the donor's ACeh.v:25 record (the core's ACeh.v:26)
     Reusable.YK11   FPState                         Reusable.YM05  RunCeil
     Reusable.YG0f   asyms (donor YG0f.v:154)        Reusable.YC5d  ameter_ops
     Reusable.YG0d   cfg_at, spZ, in_img, AR_laws     Reusable.YI16  sink_head
     Reusable.YCbq   ajournal, ajournal_init (donor YCbq.v:383-392), aos_step_mono (:65), fp_spares_closed (:87),
                     sink_closed_nil (:99)
     Reusable.YI04   inFP_nil (donor YI04.v:390; in YCbq's closure; ctrl's kept lib/Reusable/YI04.v:393)
     Reusable.YA0n   world, SRr_mono (donor YA0n.v:47-52), SRr (by its definition, YA0n.v:34-37)
     Reusable.YO09   lib_shape, LIBK, LL (donor YO09.v:14-16)
   From LinuxProcessSemantics (as the donor's ACfn.v imports them): config, m_fs, Segment.  From A.ACtlK:
   EV_LLVMF.  From A.ACtlCut: ctlcx, mkCtlCx, ctlcut, mkCtlCut, cut_pc / cut_own / cut_kmax / cut_body, ix_cut,
   the c_* fields, ctl_base, ctl_from, ctl_post, ctl_chain, ctl_trace_in, rgv.  From A.ACtlRtC: ctl_rt_C.  From
   A.ACtlTopFacts: ctlrt_C_entry.  From A.ACtlCutP: the 97 records C_<cut> bound
   below, ixn, RS, RB, LI, LK.
   SHADOWED NAMES (a Theorem Labs lane via the porter, 21:37Z): lib/Lib's copies of the four shadowed machine names are never
   Required here; the only one used, cfg_at, is Reusable.YG0d-qualified.  Check (nothing outside comments):
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtl.v
   CLOSURE: this file Requires no forbidden module itself (SlotInv.v, lib/AZ/**, AsanRTInv.v, Contract.v,
   FrameAPI.v, AZ/AS/SpinAlg, A/W6, MemNorm.v).  Measured after batch 4 with ACtlCutP.v's header scan (which now
   reads absolute Requires too): ACtlCut.v's closure is 165 files, none forbidden; ACtlCutP.v's is 278 files and
   ACtl.v's 414, both with the same 62 forbidden files: lib/A/Contract.v and what it Requires (lib/A/MemNorm.v,
   lib/A/Reusable/*, lib/AZ/LibA / lib/AZ/Spec), reached through lib/A/Prog/bcmp_wrap_c.v:59 `From ...lib.A Require
   Contract.` (its IMG_HI is Contract.GT; added after the planning-core measurement of 212 files, none forbidden),
   and for ACtl.v also lib/A/MemNorm.v through batch 4's A.ProgWorld (ProgWorld.v:786).  Batch 4's own Requires
   (ProgWorld, the C_<f> specs, ACtlCutC) are the glue's statements of record.

   BUILD STATE: type-check on the interim core (a working branch, merged on this branch at
   f06258db897 and again at 15e182dd785, batch 5), `cb build` on the packed fuzz_ctrl base 23b918fe0c2e with NO
   port_core_refused substitution and NO AD2l stand-in; the closure reaches no stand-in. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* Every unit module is Required by its EXACT prefix (the directory of the copy it loads; batch 4, a Theorem Labs lane 09:1xZ:
   a Theorem Labs lane's gate rule (c) fails a partial path that matches two copies).  Each line below names the one file the
   earlier partial form loaded: no two files under lib/ match any of them. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YK18.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0n YG0d YC5d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v ACfn AE2k ACtlK ACtlCut ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AF0m ACeh.
(* ctrl's pure input model (already in A.ACtlCutP's closure), Required only, for RELRO_CAT's CAT / CAT_N / CAT_ROW. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel.
(* section 9 only: the core's bundle, its AR laws and its trivial meter *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AD2l.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0q YCbp.
(* lib/Lib/Mem.v, Required only (never Imported), for the saved-register bytes in CHAIN_OF_CUT's premise.  Required
   and written in the full form: lib/A/Bz/Lib, lib/B/Bz/Lib and lib/AZ/Lib hold twins of Mem, and a partial
   `Lib.Mem` can bind one of them (batch 3, item 8). *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
(* Batch 4 (section 1c): the glue's Section hypotheses name these modules.  The core's rules and records:
   YC5d (afree04_rule / amalloc04_rule, mo_ok), YE01 (asink_img_laws), YG0v (range_addressable), YK04
   (same_but_materialized); a Theorem Labs lane's world statements (ProgWorld) and their proofs (ProgWorldShadow); the callee
   specs C_<f> of five Theorem Labs lanes; CtrlRo (globs_marked, img_shadow_vis) and a Theorem Labs lane's proof of the
   latter (ACtlCutC); the "?" string's address (reac_ctrl_kind_name_c.QMARK) and ctrl A's strcmp trampoline
   (strcmp_wrap_c.STRCMP_WRAP); a Theorem Labs lane's strcmp rule (AStrcmpDef).  Section 9 only: YG05 (model_laws_ok),
   YConstIn (the const-row membership decision) and the core's sink laws for B (AD1u). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YE01 YG0v YK04 AStrcmpDef YG05 YConstIn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorld ProgWorldShadow ACtlCutC AD1u.
(* Route (C) (a Theorem Labs lane truth audit 11:02Z, a Theorem Labs lane 11:10Z): the cut's narrowed runtime conjunct ctl_rt_C (a Theorem Labs lane) and
   its proof at the entry (ctlrt_C_entry). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlRtC ACtlTopFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_ctrl_parse C_reac_ctrl_identity_reply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_ctrl_build_as C_reac_ctrl_classify_box_frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_box_catalogue_match CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_kind_name_c strcmp_wrap_c.
(* Batch 5: a Theorem Labs lane's proved lib record at CtrlB (A.ACtlBCode.actlb_libS, the top's TFIB_LIB), and ctrl's synth row
   readers RcSynth.has / rname, which NAME_GLOB (section 1c) names. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlBCode.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.
(* Section 9: a Theorem Labs lane's fake-stack malloc rule of class 6 at CtrlB (the Let CtrlB_asm6). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Rt Require StackMalloc6.
Import ListNotations.
Local Open Scope Z_scope.

(* ctrl's vacuity splitter (Slot.v:384-387): split every conjunction and existential in the context.  A Section
   hypothesis that is a conjunction (RELRO_KIND_NAME, RELRO_CAT, RELRO_FRAMES) is left whole: destruct does not
   clear a section variable, so ctrl's plain `repeat` split it again forever (measured, batch 3: the vac_split of
   ctl_from_our hit a 120 s Timeout; the build without a timeout ran 67 min).  vac_gone fails, and so undoes the
   destruct, when the hypothesis H of the type T it split is still there. *)
Ltac vac_gone H T := tryif (let T' := type of H in constr_eq T T') then fail else idtac.
Ltac vac_split := repeat match goal with
  | H : exists _, _ |- _ => let T := type of H in destruct H; vac_gone H T
  | H : _ /\ _ |- _ => let T := type of H in destruct H; vac_gone H T
  end.

(* The walk meets the core's event bound through its own measured need (ACtlK.v:37-42 defers this here, where
   the core's name is in scope). *)
Lemma ev_llvmf_le : A.ACtlK.EV_LLVMF <= A.ACfn.EV_LIB.
Proof. unfold A.ACtlK.EV_LLVMF, A.ACfn.EV_LIB. lia. Qed.

(* The loop indices of ACtlCutP.v (ixn, :376) at a concrete index list. *)
Lemma ixn0 : forall b : nat, ACtlCutP.ixn 0 [Z.of_nat b] = b.
Proof. intros b. exact (Nat2Z.id b). Qed.
Lemma ixn1 : forall j i : nat, ACtlCutP.ixn 1 [Z.of_nat j; Z.of_nat i] = i.
Proof. intros j i. exact (Nat2Z.id i). Qed.

(* ajournal_fp_nil, COPIED VERBATIM from the donor, proofs/cgif/cgif_file_fuzzer/lib/A/ACfh.v:29-43 at
   origin/ossv/recipes c8557374ad2e (its sections: d with {fx} {rc} {SK} :24-25, e with segs / B :26-28); only the
   module paths change, and the Section's sink head is passed BY NAME, `(SK := SK)`, to ajournal and
   fp_spares_closed (porter 00:59Z: an implicit sink head can elaborate to a global instance such as YI5b's
   src0_sink_head).  A/ACfh.v does not join the core (porter 22:43Z: its closure pulls 26 non-core files),
   but this proof uses only the core's ajournal and four helpers, each named through the core:
     Reusable.YCbq.aos_step_mono     donor YCbq.v:65
     Reusable.YCbq.sink_closed_nil   donor YCbq.v:99
     Reusable.YCbq.fp_spares_closed  donor YCbq.v:87 (Section e, implicit {SK})
     Reusable.YI04.inFP_nil          donor YI04.v:390 (YCbq Requires YI04; ctrl's kept copy, lib/Reusable/YI04.v:393)
   The walk runs with FP = [] (section 1 of Section Ctl); the exit stage seg_Y3 lifts its journal to the post's
   [sink_token] with this lemma, as the donor's lx_leaf_fail does (ACfj.v:194). *)
Section FpNil. Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}.
Context {SK : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : Reusable.YG0f.asyms.
Lemma ajournal_fp_nil : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply Reusable.YCbq.aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (Reusable.YCbq.sink_closed_nil Ho)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi _; apply (F2 p n i H1 H2 Hi); apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.inFP_nil|].
split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply (Reusable.YCbq.fp_spares_closed (SK := SK)); intros Ho; exact (Reusable.YCbq.sink_closed_nil Ho)|].
split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.inFP_nil|].
split; [intros p n i H1 H2 Hi; exfalso; exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.inFP_nil _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.
End e.
End FpNil.

(* The core's segment list, as ACtlCut.v:73 binds it (its notation is Local there). *)
Local Notation segs := A.AB1v.tfibsegs.

Section Ctl.

(* ACtlCut.v's Section shape (its contexts and variables, in its order), with SK and FP instantiated in the
   notation block below instead of declared (section 1), plus ACtlCutP.v's two callee constants (ACtlCutP.v:369-378:
   C_A81bd8 takes them; their v1.9.0 values are pinned by KREPLY / KPARSE below). *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
(* The read-only span [RLO, RHI) is inside the loaded image (a Theorem Labs lane's shared form).  The core's arodata_okS
   of the pre (A.ACfn.tfib_lib_pre_x, ACfn.v:41) speaks of that span, and a glue step that reads a byte of it
   needs it to be an image byte.  in_img is Reusable.YG0d's (YG0d.v:471, a Section j definition over segs).
   Discharged where RLO / RHI are fixed (section 9 below, at the core's 0x9e380 / 0xa07c8). *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
(* The three .data.rel.ro tables the program READS, as the twin of RELRO_IMG for a span ro_agree cannot cover.
   PT_LOAD [0x9e348, 0xa1000) is RW (a Theorem Labs lane, ctrlcore/progreads-A.tsv (a working note, not in this delivery) and ctrl-core-cells.md section 7 (a working note, not in this delivery)), so a
   read of one of these tables is not an image-read-only byte and needs its own bound.  All three lie inside the
   same [RLO, RHI), so each is discharged in section 9 at the core's 0x9e380 / 0xa07c8 by unfold + lia.
   KIND_NAME [0x9e760, +112) feeds reac_ctrl_kind_name's stages (seg_F7, seg_F8, seg_P11); BOX_CATALOGUE =
   A.Prog.SlotModel.CAT [0x9e800, + CAT_N * CAT_ROW = 11 * 296 = 3256) feeds reac_box_catalogue's (seg_R1_turn) and
   a Theorem Labs lane's catalogue hand; CTRL_FRAMES [0x9f7e0, +264) feeds the frame-table stages.  Addition from
   a Theorem Labs lane's RELRO_CAT request widened by a Theorem Labs lane's measurement (a Theorem Labs lane 04:59Z): no existing statement
   changes.  Text: a Theorem Labs lane's RELRO hunk (a working branch 8c94b04d4eb), except that RELRO_CAT is
   written in a Theorem Labs lane's SYMBOLIC form (CAT_N * CAT_ROW, SlotModel.v:39-41), the exact text two of a Theorem Labs lane's stages
   already use (a Theorem Labs lane, 05:5xZ). *)
Hypothesis RELRO_KIND_NAME : RLO <= 0x9e760 /\ 0x9e760 + 112 <= RHI.
Hypothesis RELRO_CAT : RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI.
Hypothesis RELRO_FRAMES : RLO <= 0x9f7e0 /\ 0x9f7e0 + 264 <= RHI.
(* The core's AR law record (the Section hypothesis of YCbq Section a0, YCbq.v:207, and of YG0d Section j): the
   glue lemmas that discharge the stage hypotheses take it (ACtlG/A5.v:151, for ajournal_exec and frames_bounds),
   as the donor's walk does (A/ACfj.v:99, A/ACf2.v:47).  Discharged in section 9 by Reusable.YG0q.AR_laws_ok. *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
(* The meter (a Theorem Labs lane's request, 03:56Z; its exact text, from its Y3 glue lane, lib/A/ACtlG/Y3.v at
   a working branch b890ce26836 :170).  ctl_lib_x's post (tfib_lib_post_x) has the conjunct
   `mo_le MT S S' (XN_LIB n)`, and nothing in the cut layer carries a meter fact: ctl_base has only
   `mo_ok MT S (XM_LIB n)`, and no cut body or ctl_from premise names MT.  The meter is trivial for ctrl, but MT is
   a Variable here, so no stage can prove it.  Discharged in section 9 at MT := Reusable.YCbp.ameter_triv
   (YCbp.v:17-18, mo_le := fun _ _ _ => True) by mo_le_triv. *)
Hypothesis MO_LE : forall (S S' : Reusable.YG00.astate) (m : Z), Reusable.YC5d.mo_le MT S S' m.
(* The core's symbol facts for B, as named Section hypotheses (porter 23:10Z), in the donor's place: its Section h
   takes them (root A/ACfj.v:91-95), and the stage lemmas that discharge the stage hypotheses below read them.
   ctl_lib_x stays generic in B; section 9 instantiates B := A.AD2l.CtrlB (AD2l.v:14) and supplies both.
   - TFIB_SYMS: the donor's TfibSyms (proofs/cgif/cgif_file_fuzzer/lib/A/AF0m.v:292 at c8557374ad2e) under the
     core's name A.AF0m.CtrlTSyms (AF0m.v:2986).  a Theorem Labs lane 23:06Z: am_const gives ctrl's rows only under it.
   - TFIB_LIB: the donor's TfibLib (A/ACeh.v:25), the core's A.ACeh.TfibLib (ACeh.v:26).
   No stage hypothesis states either, so ctl_lib_x takes them through `Proof using All` below. *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis TFIB_LIB : A.ACeh.TfibLib B.
Variable REAC_CTRL_IDENTITY_REPLY_K : Z.
Variable REAC_CTRL_PARSE_BC : Z.
(* The two callee constants, pinned to their v1.9.0 values.
   (a) They stay Variables, not names from their home files: lib/A/Prog/reac_ctrl_identity_reply_c.v and
       lib/A/Prog/reac_ctrl_parse_c.v each reach lib/AZ/LibA/AcctCore.v, which the porter forbids in a port file
       (ACtlCutP.v:369-376).
   (b) The values are v1.9's: 9072 is asserted `by reflexivity` at Seg/F9.v:640 and Seg/P5.v:740; 0x21200 is the
       address of .str.4 (0x211e0 in v1.8), Seg/P5.v:1162.
   (c) They are needed because cut C_A81bd8's body asserts `addressable` at both (ACtlCutP.v:1870-1871).
   Discharged by eq_refl in the top (section 9), which instantiates both Variables at these literals. *)
Hypothesis KREPLY : REAC_CTRL_IDENTITY_REPLY_K = 9072.
Hypothesis KPARSE : REAC_CTRL_PARSE_BC = 0x21200.

(* ---------------------------------------------------------------------------------------------------------
   1c. Batch 4: the Section hypotheses the stage glue files pass (a Theorem Labs lane's 19 discharge calls, a Theorem Labs lane's R7,
   a Theorem Labs lane's Free81920, a Theorem Labs lane's P12), each text COPIED from the named file at its pushed sha, the core's twin
   modules written in the full form, except A_strcmp_tramp_at, which is new here: the file named at :306-307, in its version at the working branch named there (a version not in this delivery), keeps the trampoline entry a free Variable and pins it to no address, while the lib/B/ACtlW2b.v of this delivery pins image B's entry at :341 (B_strcmp_tramp_at).  Discharged at the top (section 9): AFREE4, MT_FREE, AMALLOC4, MO_MALLOC_OK,
   BLKSH, AIL, QMARK_ROW, A_strcmp_tramp_at.  Batch 5: ASM6 (A1's), discharged at the top by the CtlTop Let
   CtrlB_asm6 (A.Rt.StackMalloc6.disco_stack_malloc6).  OPEN (the reason at each): TPARSE, TREPLY, GLOBS_A_MARKED,
   NAME_GLOB (batch 5), TBUILD, CLS, CM_SPEC, AMEMCHR_SITE, H_strcmp.  A new Section CONJUNCTION would make vac_split
   loop (batch 3), so none of these is a top-level conjunction or existential. *)
(* The core's free rule (a Theorem Labs lane's F37.v Section GlueF37 at a working branch 121bf608343; donor
   A/ACfj.v:110).  Top: Reusable.YCbp.afree04_rule_triv at the core's afree_realizes. *)
Hypothesis AFREE4 : Reusable.YC5d.afree04_rule (SK := A.AE2k.tfib_sink_head) segs B MT.
(* The trivial meter (F37.v; the core's text A/AD1m.v:29).  Top: fun _ _ => I at ameter_triv.  Free81920.v's
   MOK_FREE is (MT_FREE _ _). *)
Hypothesis MT_FREE : forall S m, Reusable.YC5d.mo_ok MT S m.
(* The core's malloc rule and its meter obligation (a Theorem Labs lane's lib/A/ACtlG/R7.v at a working branch
   e4c3f328f3c).  Top: Reusable.YCbp.amalloc04_rule_triv at the core's amalloc_realizes / fun _ _ => I. *)
Hypothesis AMALLOC4 : Reusable.YC5d.amalloc04_rule (SK := A.AE2k.tfib_sink_head) segs B MT.
Hypothesis MO_MALLOC_OK : forall (S : Reusable.YG00.astate) (n : Z), Reusable.YC5d.mo_ok MT S (Reusable.YC5d.mo_malloc MT n).
(* The fake-stack malloc rule of class 6 (batch 5; a Theorem Labs lane's text, lib/A/ACtlG/A1.v:288 at
   a working branch 35e7be65fb5): the A1 glue needs it at the frame request 0x80f50.  Top: the CtlTop
   Let CtrlB_asm6, A.Rt.StackMalloc6.disco_stack_malloc6 at CtrlB (section 9). *)
Hypothesis ASM6 : Reusable.YG0d.astack_malloc_realizes segs B 6.
(* ONE name for a Theorem Labs lane's ctl_block_shadow_of_AR_stmt (R7.v / Free81920.v text at their pushed sha; its text here: ProgWorld.v:849).  Top: a Theorem Labs lane's proof
   A.ProgWorldShadow.ctl_block_shadow_of_AR (on this base). *)
Hypothesis BLKSH : A.ProgWorld.ctl_block_shadow_of_AR_stmt B.
(* The sink's image laws (a Theorem Labs lane's Y3.v).  Top: the core's A.AD1u.tfib_AIL at CtrlB's syms. *)
Hypothesis AIL : Reusable.YE01.asink_img_laws (SK := A.AE2k.tfib_sink_head) segs B A.AE2k.tfib_K.
(* The constant-shadow row of the "?" string, 0x7fffc23c := 2 (a Theorem Labs lane's P12.v at a working branch
   d8cb9c69f58; its KNA = A.Prog.reac_ctrl_kind_name_c).  Top: the record AF0m's Tfib_const_shadow row (AF0m.v:2179),
   decided by YConstIn's existsb_row_In and vm_compute (qmark_row_ctrl). *)
Hypothesis QMARK_ROW : forall ly,
  In (Reusable.YG0f.z1 (Reusable.YG0f.ANum (Reusable.YG0f.shadow_addr A.Prog.reac_ctrl_kind_name_c.QMARK)) 2) (A.AF0m.Tfib_const ly).
(* ctrl A's __wrap_strcmp trampoline (image B's lib/B/ACtlW2b.v at a working branch 5826fdf4d4d,
   switched to A): the entry stays a Variable, pinned to A.Prog.strcmp_wrap_c.STRCMP_WRAP = 0x42964.  Top: the
   entry 0x42964 and eq_refl. *)
Variable A_strcmp_tramp_entry : Z.
Hypothesis A_strcmp_tramp_at : A_strcmp_tramp_entry = A.Prog.strcmp_wrap_c.STRCMP_WRAP.
(* The callee specs, at the walk's sink head, B and read-only span.  OPEN: this file applies no owner's pb_ proof of TPARSE (a Theorem Labs lane),
   TBUILD (a Theorem Labs lane), CLS or CM_SPEC (a Theorem Labs lane), though such proofs are on this base (C_reac_ctrl_parseP.v:210, reac_ctrl_build_asG.v:585, reac_ctrl_classify_box_frame_glue.v:1105, reac_box_catalogue_match_glue.v:2948).  a Theorem Labs lane's pb_reac_ctrl_identity_reply IS (C_reac_ctrl_identity_reply.v),
   but it takes PALib, PALibF, astack_malloc_realizes 1, stack_malloc_progressP, astack_free_law and frame_flag_lawP
   at B, which this base does not prove at CtrlB, so TREPLY stays OPEN rather than trade one hypothesis for six. *)
Hypothesis TPARSE : A.Prog.C_reac_ctrl_parse.treac_ctrl_parse_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI.
Hypothesis TREPLY : A.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI.
(* The image's registered-globals list, to be named by its owner; a Theorem Labs lane's pb_ needs the switch table (0x21980, 56) and the
   catalogue (0x9e800, 3256) in it.  OPEN, as is its start-up certificate GLOBS_A_MARKED (a Theorem Labs lane 09:4xZ). *)
Variable GLOBS_A : list (Z * Z).
Hypothesis GLOBS_A_MARKED : A.Prog.CtrlRo.globs_marked segs B GLOBS_A.
(* The catalogue rows' names lie in GLOBS_A (batch 5, a Theorem Labs lane 13:1xZ; byte-identical to a Theorem Labs lane's R6 text).  OPEN at
   the top, as GLOBS_A_MARKED: GLOBS_A is still a free Variable there. *)
Hypothesis NAME_GLOB : forall i, 0 <= i < 11 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.has (A.Prog.SlotModel.rowb i) <> 0 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (A.Prog.SlotModel.rowb i) <> 0 -> exists q sz, In (q, sz) GLOBS_A /\ q <= OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (A.Prog.SlotModel.rowb i) /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (A.Prog.SlotModel.rowb i) + Z.of_nat (length (A.Prog.SlotModel.img_cstr (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (A.Prog.SlotModel.rowb i)) 16)) <= q + sz.
(* reac_ctrl_build_as at its entry 0x848ac = BASE + AF_reac_ctrl_build_as (C_reac_ctrl_build_as.v:59-72). *)
Hypothesis TBUILD : A.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_spec (SK := A.AE2k.tfib_sink_head) B GLOBS_A 0x848ac RLO RHI.
(* a Theorem Labs lane's classify spec, under a Theorem Labs lane's name CLS (F30.v at a working branch). *)
Hypothesis CLS : A.Prog.C_reac_ctrl_classify_box_frame.treac_ctrl_classify_box_frame_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI.
(* The registered-globals list a Theorem Labs lane's F36 glue passes with CM_SPEC (a Theorem Labs lane 09:4xZ: "GLOBS := the singleton
   list, CM_GLOB := left; reflexivity"): the box catalogue.  Section-local Lets, because A_CM_TBL takes the
   Section's RunCeil instance.  TBUILD's list is the separate GLOBS_A above; the two may later be unified into
   GLOBS_A. *)
Let GLOBS : list (Z * Z) :=
  [(A.Prog.C_reac_box_catalogue_match.A_CM_TBL, A.Prog.C_reac_box_catalogue_match.CM_ROWS)].
Let CM_GLOB : In (A.Prog.C_reac_box_catalogue_match.A_CM_TBL, A.Prog.C_reac_box_catalogue_match.CM_ROWS) GLOBS :=
  or_introl eq_refl.
(* a Theorem Labs lane's catalogue-match spec at the singleton list GLOBS (F36's text). *)
Hypothesis CM_SPEC : A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI
  [(A.Prog.C_reac_box_catalogue_match.A_CM_TBL, A.Prog.C_reac_box_catalogue_match.CM_ROWS)].
(* The memchr site rule at 0x42974 with c := 0, n := 17 (a Theorem Labs lane's X1.v; a Theorem Labs lane's amemchr_realizesM).  Text
   verbatim with X1.v's module aliases written out (RA0n / RG0d / RG0v / RG0n / RG0f / RK04 = Reusable.<X>, RK11 =
   the core's YK11 in the full form).  OPEN: no memchr rule of the core is on this base. *)
Hypothesis AMEMCHR_SITE : forall ly S (W : Reusable.YA0n.world segs) (regs : bvmap 5 word) (mem : word -> option byte) md x,
  Reusable.YG0d.ecall_pre segs B ly S W regs mem md ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 10 = Reusable.YG0d.w64 x ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 11 = Reusable.YG0d.w64 0 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 12 = Reusable.YG0d.w64 17 ->
  0 <= 0 < 256 -> 0 <= 17 < 2 ^ 32 -> 0 < x -> x + 17 <= 2 ^ 63 ->
  Reusable.YG0d.src_ok segs W regs mem x 17 -> Reusable.YG0d.amem_range x 17 ->
  Reusable.YG0v.range_addressable (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) Reusable.YG0f.SHADOW_OFF x 17 ->
  (0 < 17 -> Reusable.YG0d.shadow_hull_vis (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) x 17) ->
  (forall a, 0x10350 <= a < 0x10370 ->
     Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a))) ->
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs 0x42974 regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = Reusable.YG0d.cfg_at segs (Reusable.YG0d.raZ regs) regs' mem' md' /\
       Reusable.YG0n.AR segs B ly S W mem' md' /\ Reusable.YG0d.aregs_preserved regs regs' /\ Reusable.YK04.same_but_materialized md md' /\
       (exists k, Reusable.YG0d.first_byte segs W mem x 17 0 k /\
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 10 = (if k <? 17 then Reusable.YG0d.w64 (x + k) else Reusable.YG0d.w64 0)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (Reusable.YG0d.spZ regs - Reusable.YG0d.ESTACK <= a < Reusable.YG0d.spZ regs) ->
          Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem' a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a) /\
       (forall a, Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem a -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem' a)).
(* The shared strcmp rule at the trampoline (image B's ACtlW2b.v H_strcmp, switched to A; a Theorem Labs lane's R21.v states
   the same rule with its body at 0x42964).  OPEN, though a Theorem Labs lane's ctrl_strcmp_tramp (:467 of
   lib/A/Rt/Strcmp.v) is on the base. *)
Hypothesis H_strcmp : Reusable.AStrcmpDef.astrcmp_realizes segs B A_strcmp_tramp_entry.
(* The image's shadow is mapped (a Theorem Labs lane's F34.v name).  NOT a hypothesis: a Theorem Labs lane's PROVED
   A.ACtlCutC.ctrl_img_shadow_vis (lib/A/ACtlCutC.v at a working branch c0f1486102e), so F34's discharge
   call `... IMG_SHADOW_VIS` passes this term. *)
Let IMG_SHADOW_VIS : A.Prog.CtrlRo.img_shadow_vis segs B := A.ACtlCutC.ctrl_img_shadow_vis B TFIB_SYMS LAWS.

(* ---------------------------------------------------------------------------------------------------------
   1. The cut layer with its Section arguments absorbed once (the only place they appear).  After ACtlCut.v's
   End CtlCut: ctlcx / ctlcut and their fields take nothing, ctl_base takes B MT XM_LIB RLO RHI, ctl_from
   B MT XM_LIB RLO RHI FP, ctl_post B MT XN_LIB (ACtlCut.v:248-252).  The walk is instantiated HERE, once:
   - the journal's sink head SK := A.AE2k.tfib_sink_head, the core's (donor AE2k.v:44, ofl_head = ctrl's
     A ofl_head; porter 22:42Z), by NAME, so instance search never picks YL0j's global src0_sink_head.  It is the
     instance the core's tfib_lib_post_x journal is elaborated with (donor ACfn.v:14 Imports AE2k, whose
     instance is #[export]), so the walk's journal and the post's are over the same head;
   - the freed-block list FP := [], as the donor walks (ACfj.v:208-228); the exit stage reaches the post's
     [sink_token] through ajournal_fp_nil (copied above Section Ctl).
   A stage lemma proved for every SK and FP discharges its hypothesis here by instantiation. *)
Local Notation ctlcx := ACtlCut.ctlcx.
Local Notation ctlcut := ACtlCut.ctlcut.
Local Notation cut_pc := ACtlCut.cut_pc.
Local Notation cut_own := ACtlCut.cut_own.
Local Notation cut_kmax := ACtlCut.cut_kmax.
Local Notation cut_body := ACtlCut.cut_body.
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation c_md := ACtlCut.c_md.
Local Notation c_mem := ACtlCut.c_mem.
Local Notation CB cx := (ACtlCut.ctl_base B MT XM_LIB RLO RHI cx).
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation ctl_post := (ACtlCut.ctl_post B MT XN_LIB).

(* The cut records of ACtlCutP.v this file names (97 of 99: C_A828c0_at and C_A828cc_at are reached by no
   segment, see the header). *)
Local Notation C_ENTRY := (ACtlCutP.C_ENTRY B).
Local Notation C_A80f54 := (ACtlCutP.C_A80f54 B).
Local Notation C_A80f88 := (ACtlCutP.C_A80f88 B).
Local Notation C_A810e4 := (ACtlCutP.C_A810e4 B).
Local Notation C_A81400_at := (ACtlCutP.C_A81400_at B).
Local Notation C_A81414 := (ACtlCutP.C_A81414 B).
Local Notation C_A814f8 := (ACtlCutP.C_A814f8 B).
Local Notation C_A8152c := (ACtlCutP.C_A8152c B).
Local Notation C_A81578 := (ACtlCutP.C_A81578 B).
Local Notation C_A81588 := (ACtlCutP.C_A81588 B).
Local Notation C_A815cc_at := (ACtlCutP.C_A815cc_at B).
Local Notation C_A815ec_at := (ACtlCutP.C_A815ec_at B).
Local Notation C_A81640_at := (ACtlCutP.C_A81640_at B).
Local Notation C_A81658_at := (ACtlCutP.C_A81658_at B).
Local Notation C_A81680_at := (ACtlCutP.C_A81680_at B).
Local Notation C_A816c4_at := (ACtlCutP.C_A816c4_at B).
Local Notation C_A81708_at := (ACtlCutP.C_A81708_at B).
Local Notation C_A81734_at := (ACtlCutP.C_A81734_at B).
Local Notation C_A81768_at := (ACtlCutP.C_A81768_at B).
Local Notation C_A817c8_at := (ACtlCutP.C_A817c8_at B).
Local Notation C_A817ec_at := (ACtlCutP.C_A817ec_at B).
Local Notation C_A8183c_at := (ACtlCutP.C_A8183c_at B).
Local Notation C_A81858_at := (ACtlCutP.C_A81858_at B).
Local Notation C_A818d0_at := (ACtlCutP.C_A818d0_at B).
Local Notation C_A818e8_at := (ACtlCutP.C_A818e8_at B).
Local Notation C_A81924_at := (ACtlCutP.C_A81924_at B).
Local Notation C_A81ac0 := (ACtlCutP.C_A81ac0 B).
Local Notation C_A81ac8 := (ACtlCutP.C_A81ac8 B).
Local Notation C_A81b10 := (ACtlCutP.C_A81b10 B).
Local Notation C_A81b14 := (ACtlCutP.C_A81b14 B).
Local Notation C_A81b80 := (ACtlCutP.C_A81b80 B).
Local Notation C_A81b90 := (ACtlCutP.C_A81b90 B).
Local Notation C_A81bd8 := (ACtlCutP.C_A81bd8 B REAC_CTRL_IDENTITY_REPLY_K REAC_CTRL_PARSE_BC).
Local Notation C_A81bf8 := (ACtlCutP.C_A81bf8 B).
Local Notation C_A81c20 := (ACtlCutP.C_A81c20 B).
Local Notation C_A81c34 := (ACtlCutP.C_A81c34 B).
Local Notation C_A81c4c := (ACtlCutP.C_A81c4c B).
Local Notation C_A81c60 := (ACtlCutP.C_A81c60 B).
Local Notation C_A81c84 := (ACtlCutP.C_A81c84 B).
Local Notation C_A81d40_at := (ACtlCutP.C_A81d40_at B).
Local Notation C_A81da4_at := (ACtlCutP.C_A81da4_at B).
Local Notation C_A81dd0_at := (ACtlCutP.C_A81dd0_at B).
Local Notation C_A81dfc_at := (ACtlCutP.C_A81dfc_at B).
Local Notation C_A81e54_at := (ACtlCutP.C_A81e54_at B).
Local Notation C_A81e84_at := (ACtlCutP.C_A81e84_at B).
Local Notation C_A81e88_at := (ACtlCutP.C_A81e88_at B).
Local Notation C_A81ea4_at := (ACtlCutP.C_A81ea4_at B).
Local Notation C_A81ea8_at := (ACtlCutP.C_A81ea8_at B).
Local Notation C_A81ec0_at := (ACtlCutP.C_A81ec0_at B).
Local Notation C_A81f54_at := (ACtlCutP.C_A81f54_at B).
Local Notation C_A81f64_at := (ACtlCutP.C_A81f64_at B).
Local Notation C_A81f7c_at := (ACtlCutP.C_A81f7c_at B).
Local Notation C_A81f88_at := (ACtlCutP.C_A81f88_at B).
Local Notation C_A81ff4_at := (ACtlCutP.C_A81ff4_at B).
Local Notation C_A8206c_at := (ACtlCutP.C_A8206c_at B).
Local Notation C_A820ac_at := (ACtlCutP.C_A820ac_at B).
Local Notation C_A820f8_at := (ACtlCutP.C_A820f8_at B).
Local Notation C_A820fc_at := (ACtlCutP.C_A820fc_at B).
Local Notation C_A82138_at := (ACtlCutP.C_A82138_at B).
Local Notation C_A82154_at := (ACtlCutP.C_A82154_at B).
Local Notation C_A82174_at := (ACtlCutP.C_A82174_at B).
Local Notation C_A82178_at := (ACtlCutP.C_A82178_at B).
Local Notation C_A821d0_at := (ACtlCutP.C_A821d0_at B).
Local Notation C_A8229c_at := (ACtlCutP.C_A8229c_at B).
Local Notation C_A822a0_at := (ACtlCutP.C_A822a0_at B).
Local Notation C_A823e8_at := (ACtlCutP.C_A823e8_at B).
Local Notation C_A82400_at := (ACtlCutP.C_A82400_at B).
Local Notation C_A82418_at := (ACtlCutP.C_A82418_at B).
Local Notation C_A824b4_at := (ACtlCutP.C_A824b4_at B).
Local Notation C_A82554_at := (ACtlCutP.C_A82554_at B).
Local Notation C_A825a0_at := (ACtlCutP.C_A825a0_at B).
Local Notation C_A825c8_at := (ACtlCutP.C_A825c8_at B).
Local Notation C_A825d4_at := (ACtlCutP.C_A825d4_at B).
Local Notation C_A825f4_at := (ACtlCutP.C_A825f4_at B).
Local Notation C_A82604_at := (ACtlCutP.C_A82604_at B).
Local Notation C_A8265c_at := (ACtlCutP.C_A8265c_at B).
Local Notation C_A826d4_at := (ACtlCutP.C_A826d4_at B).
Local Notation C_A82750_at := (ACtlCutP.C_A82750_at B).
Local Notation C_A8275c_at := (ACtlCutP.C_A8275c_at B).
Local Notation C_A82798_at := (ACtlCutP.C_A82798_at B).
Local Notation C_A827d8_at := (ACtlCutP.C_A827d8_at B).
Local Notation C_A82800_at := (ACtlCutP.C_A82800_at B).
Local Notation C_A8285c_at := (ACtlCutP.C_A8285c_at B).
Local Notation C_A8286c_at := (ACtlCutP.C_A8286c_at B).
Local Notation C_A82888_at := (ACtlCutP.C_A82888_at B).
Local Notation C_A8289c_at := (ACtlCutP.C_A8289c_at B).
Local Notation C_A828a0_at := (ACtlCutP.C_A828a0_at B).
Local Notation C_A828bc_at := (ACtlCutP.C_A828bc_at B).
Local Notation C_A828c8_at := (ACtlCutP.C_A828c8_at B).
Local Notation C_A828d8_at := (ACtlCutP.C_A828d8_at B).
Local Notation C_A82940_at := (ACtlCutP.C_A82940_at B).
Local Notation C_A82964_at := (ACtlCutP.C_A82964_at B).
Local Notation C_A82b04 := (ACtlCutP.C_A82b04 B).
Local Notation C_A82b20 := (ACtlCutP.C_A82b20 B).
Local Notation C_Jrel := (ACtlCutP.C_Jrel B).
Local Notation C_A82b9c := (ACtlCutP.C_A82b9c B).
Local Notation C_A82bb0 := (ACtlCutP.C_A82bb0 B).

(* ---------------------------------------------------------------------------------------------------------
   2. A cut at ONE index is ACtlCut.v's ix_cut (ACtlCut.v:210-212, with ctl_from_ix :214-222; the same name and
   statement in image B's twin): ctl_from quantifies the index list idx, so `ctl_from POST X` holds at every index
   at once (ctrl's `forall b, Hat .. b`), and `ctl_from POST (ix_cut X i0)` is ctrl's `Hat .. i0`.  The index
   shapes of ACtlCut.v section 3: [Z.of_nat b] / [Z.of_nat j], [Z.of_nat j; Z.of_nat i] for the row cuts, [t] as
   Z for A81400_at (whose body reads it with ixz). *)
(* The our[] head at turn t: ctrl's Inv_A81414_at t (Seg/R1.v:1275, plan section 3 "head A81414_at t").
   C_A81414 states its turn t existentially (ACtlCutP.v:1138) and pins it in register 11 = t + 1 (:1143), so the
   one-turn cut is C_A81414 with that pin and the turn range of its body. *)
Definition C_A81414_at (t : Z) : ctlcut :=
  ACtlCut.mkCtlCut (cut_pc C_A81414) (cut_own C_A81414) (cut_kmax C_A81414)
    (fun cx idx bl fr sel regs m =>
       (0 <= t <= 5 /\ ACtlCut.rgv regs 11 (t + 1)) /\ cut_body C_A81414 cx idx bl fr sel regs m).

(* The exit post the top consumes: ACtlCut.v's ctl_post with its leaf fixed to the one fuzz_ctrl's tree takes
   (departure 1; the donor's leaf, ACfj.v:186).  The post is the core's tfib_lib_post_x, applied as the donor
   applies it (ACfj.v:238: B MT XN_LIB, then the entry arguments). *)
Definition ctl_post_leaf (cx : ctlcx) : Reusable.YA0n.world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k,
    c' = Reusable.YG0d.cfg_at segs A.ACfn.RA_LLVMF regs' mem' md' /\
    A.ACfn.tfib_lib_post_x B MT XN_LIB
      (ACtlCut.c_regs cx) (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
      (c_mem cx) (c_md cx) (ACtlCut.c_p cx) (ACtlCut.c_n cx) (ACtlCut.c_M cx)
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.LL 0 (m_fs (c_md cx)) [])
      ly' S' W' regs' mem' md' k.

(* ---------------------------------------------------------------------------------------------------------
   3. Generic facts about ctl_from. *)

(* The donor's rt_from_mono (ACfj.v:86-93). *)
Lemma ctl_from_mono : forall (P Q : ctlcx -> Reusable.YA0n.world segs -> config -> Prop) (X : ctlcut),
  (forall cx W c, CB cx -> P cx W c -> Q cx W c) -> CF P X -> CF Q X.
Proof.
  intros P Q X HPQ HR cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hb Hrt.
  eapply Reusable.YA0n.SRr_mono; [exact (HR cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hb Hrt)|].
  intros W' c' _ HP. exact (HPQ cx W' c' HB HP).
Qed.

(* A cut whose body never holds is reached by nothing: the base of every loop (ctrl's vac_*, Slot.v:392-408). *)
Lemma ctl_from_vac : forall POST (X : ctlcut),
  (forall cx idx bl fr regs m, ~ cut_body X cx idx bl fr fr regs m) -> CF POST X.
Proof.
  intros POST X HV cx idx fr k ly3 S3 W3 regs3 mem3 md3 _ _ _ _ _ Hb _.
  exfalso. exact (HV _ _ _ _ _ _ Hb).
Qed.

(* The our[] head at every turn gives C_A81414: its body's own turn t is in range and pinned in register 11. *)
Lemma ctl_from_our : forall POST,
  (forall t, 0 <= t <= 5 -> CF POST (C_A81414_at t)) -> CF POST C_A81414.
Proof.
  intros POST HT cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  pose proof Hbody as Hb.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81414] in Hb.
  destruct Hb as (t & Hb). vac_split.
  assert (Ht : 0 <= t <= 5) by (split; assumption).
  refine (HT t Ht cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk _ Hrt).
  split; [split; [exact Ht | assumption] | exact Hbody].
Qed.

(* The vacuous heads past the last turn.  Bounds from ctrl's own bodies: RB `b <= 6` (SlotInv.v:830,
   ACtlCutP.v:477, inside RS of C_A815cc_at :1255), LK `j <= 255` (SlotInv.v:898, ACtlCutP.v:535, inside LI of
   C_A81d40_at :1934), `i <= 10` (SlotInv.v:2956, ACtlCutP.v:2774, C_A8286c_at). *)
Lemma vac_A815cc : forall POST b, (6 < b)%nat -> CF POST (ix_cut C_A815cc_at [Z.of_nat b]).
Proof.
  intros POST b Hb. apply ctl_from_vac. intros cx idx bl fr regs m H.
  cbv beta iota zeta delta [ACtlCut.ix_cut ACtlCut.cut_body ACtlCutP.C_A815cc_at ACtlCutP.RS ACtlCutP.RB] in H.
  vac_split. subst idx.
  match goal with Hr : (ACtlCutP.ixn 0 _ <= 6)%nat |- _ => rewrite ixn0 in Hr; clear - Hb Hr; lia end.
Qed.

Lemma vac_A81d40 : forall POST j, (255 < j)%nat -> CF POST (ix_cut C_A81d40_at [Z.of_nat j]).
Proof.
  intros POST j Hj. apply ctl_from_vac. intros cx idx bl fr regs m H.
  cbv beta iota zeta delta [ACtlCut.ix_cut ACtlCut.cut_body ACtlCutP.C_A81d40_at ACtlCutP.LI ACtlCutP.LK] in H.
  vac_split. subst idx.
  match goal with Hr : (ACtlCutP.ixn 0 _ <= 255)%nat |- _ => rewrite ixn0 in Hr; clear - Hj Hr; lia end.
Qed.

Lemma vac_A8286c : forall POST j i, (10 < i)%nat -> CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat i]).
Proof.
  intros POST j i Hi. apply ctl_from_vac. intros cx idx bl fr regs m H.
  cbv beta iota zeta delta [ACtlCut.ix_cut ACtlCut.cut_body ACtlCutP.C_A8286c_at] in H.
  vac_split. subst idx.
  match goal with Hr : (ACtlCutP.ixn 1 _ <= 10)%nat |- _ => rewrite ixn1 in Hr; clear - Hi Hr; lia end.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   4. The non-stage hypotheses LS_LEAF and CHAIN_OF_CUT, and the proved CTLRT_ENTRY. *)

(* The lib shape's tree is one leaf: LIBK pl fs K = K (LL 0 fs []).  ACtlCut.v abstracts the shape
   ({LS : ...} in its Section), and the contract's goal is stated through LIBK, so the top needs this fact about
   LS.  It holds by reflexivity at fuzz_ctrl's image-A shape ag_shape checksum_shape (lib/A/CtrlTFIB.v:23;
   lib/AgreeShape.v:9-10 copies LIBK; lib/A/ZTraceSpec.v:14-20 defines it, transparent).  Discharged where LS is
   instantiated. *)
Hypothesis LS_LEAF : forall pl fs K, @OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.LIBK LS pl fs K = K (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.LL 0 fs []).

(* The carried ctrl runtime facts at the entry, in route (C)'s narrowed form: ctl_rt_C at the entry state.  Route (C)
   because a Theorem Labs lane's truth audit (11:02Z) found the full ctl_rt form, and AR_states_vis0_shadow, false at an AR state.
   NOT a hypothesis: proved from the entry's AR and arodata_okS (both in ctl_base's lib pre) by a Theorem Labs lane's
   A.ProgWorldCtlRtC.ctl_rt_C_of_AR (CtrlTSyms + AR_laws only; no AR_states_vis0_shadow, no AR_states_owned_ro), as
   A.ACtlTopFacts.ctlrt_C_entry at this Section's TFIB_SYMS and LAWS.  The Let's type is the statement, so it checks
   ctlrt_C_entry against it. *)
Let CTLRT_ENTRY : forall cx : ctlcx, CB cx ->
  A.ACtlRtC.ctl_rt_C B (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (c_mem cx) :=
  A.ACtlTopFacts.ctlrt_C_entry B MT XM_LIB RLO RHI TFIB_SYMS LAWS.

(* The frame-pointer chain and the call trace at an allocator call (ACtlCut.v section 1b): at every owning cut the
   caller-side facts give a chain_pre of the caller's chain and its call trace in the core's universe, at the four
   allocator sites of the walk (plan section 2.5) -- malloc / free of the round trip (0x8163c / 0x81920, returns
   0x81640 / 0x81924) and malloc / free of the frame loop (0x81da0 / 0x8293c, returns 0x81da4 / 0x82940).  The
   saved-register bytes are FRAC's (ACtlCutP.saved_bytes, ctrl's SlotInv.v:275-279, written out because this file
   states the premise itself); s0 = S and the spill-base window (S - 4096 < sp, sp + 416 <= S) are FRAC's too (A's
   window is 416, image B's is 448).  Statement: the image-B twin's CHAIN_OF_CUT (lib/B/ACtl.v at
   a working branch 6adbb8c9272) with A names, over the walk's journal (sink head as in CF, FP
   quantified).  A HYPOTHESIS, not a lemma: its proof needs the entry chain of the core's afn_pre, the journal's
   kept view above S and the bridge from lib/Lib's bytes_at to the core's aview (a Theorem Labs lane's ProgBridge /
   ProgWorld do not state it). *)
Hypothesis CHAIN_OF_CUT : forall (FP : list (Z * Z)) (cx : ctlcx) own ly3 S3 W3 mem3 md3 k (regsT : bvmap 5 word)
    (pc0 ra : Z),
  CB cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 k ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regsT 8 = Z_to_bv 64 (ACtlCut.c_sp cx) ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regsT 1 = Z_to_bv 64 ra ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs mem3 (ACtlCut.c_sp cx - 104)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 27) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 26) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 25) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 24) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 23) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 22) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 21) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 20) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 19) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 18) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 9) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 8) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 A.ACfn.RA_LLVMF)) ->
  ACtlCut.c_sp cx - 4096 < Reusable.YG0d.spZ regsT -> Reusable.YG0d.spZ regsT + 416 <= ACtlCut.c_sp cx ->
  In (pc0, ra) [(Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81640);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x81924);
                (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81da4);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x82940)] ->
  exists ch, ACtlCut.ctl_chain ly3 W3 mem3 regsT ch /\ ACtlCut.ctl_trace_in B pc0 regsT ch.

(* ---------------------------------------------------------------------------------------------------------
   5. The stage hypotheses, one per live segment of plan section 2.3, grouped by W piece in section 5's order.
   Exits are section 2.3's (with Appendix B); a loop-carried exit gives the next turn's index; a two-entry
   segment (F4, F12, F32) concludes both entries, as ctrl's S_F4 / S_F12 / S_F32 do (Slot.v:130, :163, :218).
   The stage files keep the record names; POST is quantified, the exit stage seg_Y3 alone fixes it. *)

(* ===== W0 prologue: ENTRY -> A810e4 (A1, A2, A3) ===== *)
(* glue: Seg/A1.v seg_A1 :1019 @E via _F; runs a1_store_evt :97, a1_tail_evt :197, a1_req_evt :785 *)
(* Batch 4 (B5.2; image B's twin): the entry stage concludes only for posts that do not read c_fpos (premise on POST,
   ACtlCut.cx_set_fpos): A1's frame request at 0x80f50 picks the frame position, which no entry fact ties to
   c_fpos cx (found by the ENTRY glue, lib/A/ACtlG/A1.v:26-29; the donor's entry segment has
   `exists fpos`, cgif A/ACfj.v:252). *)
Hypothesis seg_A1 : forall POST, (forall cx p, POST (ACtlCut.cx_set_fpos cx p) = POST cx) -> CF POST C_A80f54 -> CF POST C_A80f88 -> CF POST C_ENTRY.
(* glue: Seg/A2.v seg_A2 :237 @E via _F; runs a2_side_evt :221 (a2_real_evt :184 is the discharged class-full arm) *)
Hypothesis seg_A2 : forall POST, CF POST C_A80f88 -> CF POST C_A80f54.
(* glue: Seg/A3.v seg_A3 :547 @U via _F; runs lib_evt_cut :83, f8_call :147, a3_evt :217 *)
Hypothesis seg_A3 : forall POST, CF POST C_A810e4 -> CF POST C_A80f88.

(* ===== W1 pre-loop: A810e4 -> A815cc_at 0, A81b14, Jrel (A4, A5, R1, R2-R5) ===== *)
(* glue: Seg/A4.v seg_A4 :860 @U via _F; runs a4_evt :168 *)
Hypothesis seg_A4 : forall POST, CF POST (ix_cut C_A81400_at [0]) -> CF POST C_Jrel -> CF POST C_A810e4.
(* glue: Seg/A5.v seg_A5 :68 @E via _F; runs a5_evt :37 *)
Hypothesis seg_A5 : forall POST (t : Z), CF POST C_A81414 -> CF POST (ix_cut C_A81400_at [t]).
(* glue: Seg/R1.v r1_turn :1275 @U via _F (seg_R1 :2160 closes the loop; here loop_our does); runs r1_z_evt :189, r1_ld_evt :239, r1_mode_evt :341, r1_spill_evt :427, r1_shadow_evt :493, r1_call_evt :564 *)
Hypothesis seg_R1_turn : forall POST (t : Z),
  (t < 5 -> CF POST (C_A81414_at (t + 1))) -> CF POST C_A81b14 -> CF POST C_A814f8 -> CF POST (C_A81414_at t).
(* glue: Seg/R2.v seg_R2 :350 @U via _F; runs r2_evt :196 *)
Hypothesis seg_R2 : forall POST, CF POST C_A8152c -> CF POST C_A814f8.
(* glue: Seg/R3.v seg_R3 :750 @U via _F; runs r3_evt :311 *)
Hypothesis seg_R3 : forall POST, CF POST C_A81578 -> CF POST C_A8152c.
(* glue: Seg/R4.v seg_R4 :436 @U via _F; runs r4_evt :193 *)
Hypothesis seg_R4 : forall POST, CF POST C_A81588 -> CF POST C_A81578.
(* glue: Seg/R5.v seg_R5 :444 @U via _F; runs inline in seg_R5 (Appendix A: no stated evt run lemma) *)
Hypothesis seg_R5 : forall POST, CF POST (ix_cut C_A815cc_at [Z.of_nat 0]) -> CF POST C_A81588.

(* ===== W2 round trip, turn b: A815cc_at b -> A815cc_at (S b), A81ac0, A81ac8, A81b10 (R6-R21) ===== *)
(* glue: Seg/R6.v seg_R6 :1175 @U via _F; runs inline in seg_R6 (Appendix A: no stated evt run lemma) *)
Hypothesis seg_R6 : forall POST (b : nat), CF POST (ix_cut C_A815ec_at [Z.of_nat b]) -> CF POST (ix_cut C_A815cc_at [Z.of_nat b]).
(* glue: Seg/R7.v seg_R7 :1136 @E via _F; runs r7_evt :61, r7_latch_evt :222, Seg/R7tail.v r7_tail_evt :533 @E *)
Hypothesis seg_R7 : forall POST (b : nat),
  CF POST (ix_cut C_A81640_at [Z.of_nat b]) -> CF POST (ix_cut C_A815cc_at [Z.of_nat (S b)]) -> CF POST C_A81ac0 -> CF POST C_A81b10 ->
  CF POST (ix_cut C_A815ec_at [Z.of_nat b]).
(* glue: Seg/R8.v seg_R8 :837 @U via _F; runs r8_evt :128 *)
Hypothesis seg_R8 : forall POST (b : nat), CF POST (ix_cut C_A81658_at [Z.of_nat b]) -> CF POST (ix_cut C_A81640_at [Z.of_nat b]).
(* glue: Seg/R9.v seg_R9 :2240 @U via _F; runs r9_st :1065, r9_call :1258, r9_calln :1322 *)
Hypothesis seg_R9 : forall POST (b : nat), CF POST (ix_cut C_A81680_at [Z.of_nat b]) -> CF POST (ix_cut C_A81658_at [Z.of_nat b]).
(* glue: Seg/R10.v seg_R10 :38 @U via _F; runs Seg/R10A.v r10a_evt0 :108, r10a_evt12 :168, r10a_head34 :219, r10a_call34 :1060, Seg/R10B.v r10b_evt :734 *)
Hypothesis seg_R10 : forall POST (b : nat),
  CF POST (ix_cut C_A816c4_at [Z.of_nat b]) -> CF POST (ix_cut C_A81708_at [Z.of_nat b]) -> CF POST (ix_cut C_A81768_at [Z.of_nat b]) ->
  CF POST (ix_cut C_A817c8_at [Z.of_nat b]) -> CF POST (ix_cut C_A817ec_at [Z.of_nat b]) -> CF POST (ix_cut C_A81680_at [Z.of_nat b]).
(* glue: Seg/R11.v seg_R11 :67 @U via _F; runs r11_evt :34, Seg/RNIng.v rn_ing_evt :248 *)
Hypothesis seg_R11 : forall POST (b : nat), CF POST (ix_cut C_A81734_at [Z.of_nat b]) -> CF POST (ix_cut C_A816c4_at [Z.of_nat b]).
(* glue: Seg/R12.v seg_R12 :57 @U via _F; runs r12_evt :33, Seg/RNIng.v rn_ing_evt :248 *)
Hypothesis seg_R12 : forall POST (b : nat), CF POST (ix_cut C_A81734_at [Z.of_nat b]) -> CF POST (ix_cut C_A81708_at [Z.of_nat b]).
(* glue: Seg/R13.v seg_R13 :58 @U via _F; runs r13_evt :18, Seg/R15.v rfree_evt :40 *)
Hypothesis seg_R13 : forall POST (b : nat), CF POST (ix_cut C_A81924_at [Z.of_nat b]) -> CF POST (ix_cut C_A81734_at [Z.of_nat b]).
(* glue: Seg/R14.v seg_R14 :1129 @U via _F; runs r14_head :671, r14_call :712, Seg/B3Loop.v b3_loop1 :170 *)
Hypothesis seg_R14 : forall POST (b : nat), CF POST (ix_cut C_A8183c_at [Z.of_nat b]) -> CF POST (ix_cut C_A81768_at [Z.of_nat b]).
(* glue: Seg/R15.v seg_R15 :856 @U via _F; runs r15_evt :25, rfree_evt :40 *)
Hypothesis seg_R15 : forall POST (b : nat), CF POST (ix_cut C_A81924_at [Z.of_nat b]) -> CF POST (ix_cut C_A817c8_at [Z.of_nat b]).
(* glue: Seg/R16.v seg_R16 :92 @U via _F; runs r16_run :28, Seg/B3Loop.v b3_loop2 :195, Seg/R15.v rfree_evt :40 *)
Hypothesis seg_R16 : forall POST (b : nat), CF POST (ix_cut C_A81924_at [Z.of_nat b]) -> CF POST (ix_cut C_A817ec_at [Z.of_nat b]).
(* glue: Seg/R17.v seg_R17 :391 @U via _F; runs r17_evt :170 *)
Hypothesis seg_R17 : forall POST (b : nat), CF POST (ix_cut C_A81858_at [Z.of_nat b]) -> CF POST (ix_cut C_A8183c_at [Z.of_nat b]).
(* glue: Seg/R18.v seg_R18 :1075 @U via _F; runs r18_evt :505 *)
Hypothesis seg_R18 : forall POST (b : nat), CF POST (ix_cut C_A818d0_at [Z.of_nat b]) -> CF POST (ix_cut C_A81858_at [Z.of_nat b]).
(* glue: Seg/R19.v seg_R19 :647 @U via _F; runs r19_run :33, r19_evt :154 *)
Hypothesis seg_R19 : forall POST (b : nat), CF POST (ix_cut C_A818e8_at [Z.of_nat b]) -> CF POST (ix_cut C_A818d0_at [Z.of_nat b]).
(* glue: Seg/R20.v seg_R20 :512 @U via _F; runs r20_evt :62, Seg/R15.v rfree_evt :40 *)
Hypothesis seg_R20 : forall POST (b : nat), CF POST (ix_cut C_A81924_at [Z.of_nat b]) -> CF POST (ix_cut C_A818e8_at [Z.of_nat b]).
(* glue: Seg/R21.v seg_R21 :1912 @U via _F; runs r21_latch_next :113, r21_latch_last :145 *)
Hypothesis seg_R21 : forall POST (b : nat),
  CF POST (ix_cut C_A815cc_at [Z.of_nat (S b)]) -> CF POST C_A81ac0 -> CF POST C_A81ac8 -> CF POST (ix_cut C_A81924_at [Z.of_nat b]).

(* ===== W3 between loops: A81ac0 / A81ac8 / A81b10 / A81b14 -> A81d40_at 0, A82b04 (P1-P12) ===== *)
(* glue: Seg/P1.v seg_P1 :1084 @U via _F; runs p1_beqz :157, p1_evt :174, p1_evt_ro :383 *)
Hypothesis seg_P1 : forall POST, CF POST C_A81b10 -> CF POST C_A81ac0.
(* glue: Seg/P1.v seg_P1_70 :728 @U via _F; runs p1_beqz :157, p1_evt :174, p1_evt_ro :383 *)
Hypothesis seg_P1_70 : forall POST, CF POST C_A81b10 -> CF POST C_A81ac8.
(* glue: Seg/P2.v seg_P2 :119 @U via _F; runs inline in seg_P2 (Appendix A: no stated evt run lemma) *)
Hypothesis seg_P2 : forall POST, CF POST C_A81b14 -> CF POST C_A81b10.
(* glue: Seg/P3.v seg_P3 :732 @U via _F; runs p3_evt :153, p3_run :346, p3_evt_ro :463 *)
Hypothesis seg_P3 : forall POST, CF POST C_A81b80 -> CF POST C_A81b14.
(* glue: Seg/P4.v seg_P4 :360 @U via _F; runs p4_evt :26, p4_evt_ro :214 *)
Hypothesis seg_P4 : forall POST, CF POST C_A81b90 -> CF POST C_A81b80.
(* glue: Seg/P5.v seg_P5 :720 @U via _F; runs p5_memset_ro :310, p5_evt :376 *)
Hypothesis seg_P5 : forall POST, CF POST C_A81bd8 -> CF POST C_A81b90.
(* glue: Seg/P6.v seg_P6 :1135 @U via _F; runs p6_evt :184, p6_evt_ro :591 *)
Hypothesis seg_P6 : forall POST, CF POST C_A81bf8 -> CF POST C_A81bd8.
(* glue: Seg/P7.v seg_P7 :557 @U via _F; runs p7_run :210, p7_evt :463 *)
Hypothesis seg_P7 : forall POST, CF POST C_A81c20 -> CF POST C_A81bf8.
(* glue: Seg/P8.v seg_P8 :86 @U via _F; runs p8_evt :45 *)
Hypothesis seg_P8 : forall POST, CF POST C_A81c34 -> CF POST C_A81c20.
(* glue: Seg/P9.v seg_P9 :85 @U via _F; runs p9_evt :43 *)
Hypothesis seg_P9 : forall POST, CF POST C_A81c4c -> CF POST C_A81c34.
(* glue: Seg/P10.v seg_P10 :228 @U via _F; runs p10_evt :169 *)
Hypothesis seg_P10 : forall POST, CF POST C_A81c60 -> CF POST C_A81c4c.
(* glue: Seg/P11.v seg_P11 :231 @U via _F; runs p11_evt :171 *)
Hypothesis seg_P11 : forall POST, CF POST C_A81c84 -> CF POST C_A81c60.
(* glue: Seg/P12.v seg_P12 :861 @U via _F; runs p12_run :123, p12_evt_a :709, p12_evt_b0 :753, p12_evt_b1 :781 *)
Hypothesis seg_P12 : forall POST, CF POST (ix_cut C_A81d40_at [Z.of_nat 0]) -> CF POST C_A82b04 -> CF POST C_A81c84.

(* ===== W4 frame turn j: A81d40_at j -> A81d40_at (S j), A82b04 (F1-F38, rows inside) ===== *)
(* ----- W4a: F1-F6_e28 ----- *)
(* glue: Seg/F1.v seg_F1 :1653 @U via _F; runs f1_chk0 :185, f1_chk1 :217, f1_tail :250, f1_evt :284 *)
Hypothesis seg_F1 : forall POST (j : nat), CF POST (ix_cut C_A81da4_at [Z.of_nat j]) -> CF POST (ix_cut C_A81d40_at [Z.of_nat j]).
(* glue: Seg/F2.v seg_F2 :829 @U via _F; runs f2_evt :290, f2z_evt :415, f2_run :458 *)
Hypothesis seg_F2 : forall POST (j : nat),
  CF POST (ix_cut C_A81dd0_at [Z.of_nat j]) -> CF POST (ix_cut C_A81e54_at [Z.of_nat j]) -> CF POST (ix_cut C_A81da4_at [Z.of_nat j]).
(* glue: Seg/F3.v seg_F3 :1990 @U via _F; runs f3_st :963, f3_call :1021, f3_calln :1083 *)
Hypothesis seg_F3 : forall POST (j : nat), CF POST (ix_cut C_A81dfc_at [Z.of_nat j]) -> CF POST (ix_cut C_A81dd0_at [Z.of_nat j]).
(* glue: Seg/F4.v seg_F4 :3618 @U via _F; runs f4_dbc_st :1332, f4_dbc_call :2183, f4_dbc_calln :2246 *)
Hypothesis seg_F4 : forall POST (j : nat),
  CF POST (ix_cut C_A81e88_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ea4_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ea8_at [Z.of_nat j]) ->
  CF POST (ix_cut C_A81e84_at [Z.of_nat j]) -> CF POST (ix_cut C_A81dfc_at [Z.of_nat j]) /\ CF POST (ix_cut C_A81e54_at [Z.of_nat j]).
(* glue: Seg/F5.v seg_F5 :927 @U via _F; runs inline in seg_F5 (Appendix A: no stated evt run lemma) *)
Hypothesis seg_F5 : forall POST (j : nat), CF POST (ix_cut C_A81f54_at [Z.of_nat j]) -> CF POST (ix_cut C_A81e84_at [Z.of_nat j]).
(* glue: Seg/F5.v seg_F5_df0 :766 @U via _F; runs inline in seg_F5_df0 (Appendix A: no stated evt run lemma) *)
Hypothesis seg_F5_df0 : forall POST (j : nat), CF POST (ix_cut C_A81f54_at [Z.of_nat j]) -> CF POST (ix_cut C_A81e88_at [Z.of_nat j]).
(* glue: Seg/F5.v seg_F5_e0c :1111 @U via _F; runs inline in seg_F5_e0c (Appendix A: no stated evt run lemma) *)
Hypothesis seg_F5_e0c : forall POST (j : nat), CF POST (ix_cut C_A81ec0_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ea4_at [Z.of_nat j]).
(* glue: Seg/F5.v seg_F5_e10 :1009 @U via _F; runs inline in seg_F5_e10 (Appendix A: no stated evt run lemma) *)
Hypothesis seg_F5_e10 : forall POST (j : nat), CF POST (ix_cut C_A81ec0_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ea8_at [Z.of_nat j]).
(* glue: Seg/F6.v seg_F6_e28 :2727 @U via _F; runs f6_loop :398, f6_e28_evt :483 *)
Hypothesis seg_F6_e28 : forall POST (j : nat), CF POST (ix_cut C_A81f54_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ec0_at [Z.of_nat j]).
(* ----- W4b: F6_ebc-F12 ----- *)
(* glue: Seg/F6.v seg_F6_ebc :2534 @U via _F; runs f6_ebc_evt :1418 *)
Hypothesis seg_F6_ebc : forall POST (j : nat), CF POST (ix_cut C_A81f64_at [Z.of_nat j]) -> CF POST (ix_cut C_A81f54_at [Z.of_nat j]).
(* glue: Seg/F7.v seg_F7 :444 @U via _F; runs f7_evt :381 *)
Hypothesis seg_F7 : forall POST (j : nat), CF POST (ix_cut C_A81f7c_at [Z.of_nat j]) -> CF POST (ix_cut C_A81f64_at [Z.of_nat j]).
(* glue: Seg/F8.v seg_F8 :434 @U via _F; runs f8_evt :384 *)
Hypothesis seg_F8 : forall POST (j : nat), CF POST (ix_cut C_A81f88_at [Z.of_nat j]) -> CF POST (ix_cut C_A81f7c_at [Z.of_nat j]).
(* glue: Seg/F9.v seg_F9 :3346 @U via _F; runs f9_evtA :176, f9_evtB :602 *)
Hypothesis seg_F9 : forall POST (j : nat), CF POST (ix_cut C_A81ff4_at [Z.of_nat j]) -> CF POST (ix_cut C_A81f88_at [Z.of_nat j]).
(* glue: Seg/F10.v seg_F10 :147 @U via _F; runs inline in seg_F10 (Appendix A: no stated evt run lemma) *)
Hypothesis seg_F10 : forall POST (j : nat),
  CF POST (ix_cut C_A8206c_at [Z.of_nat j]) -> CF POST (ix_cut C_A820ac_at [Z.of_nat j]) -> CF POST (ix_cut C_A820fc_at [Z.of_nat j]) ->
  CF POST (ix_cut C_A81ff4_at [Z.of_nat j]).
(* glue: Seg/F11.v seg_F11_fd4 :1355 @U via _F; runs f11_loop :273, f11_fd4_evt :357 *)
Hypothesis seg_F11_fd4 : forall POST (j : nat), CF POST (ix_cut C_A820ac_at [Z.of_nat j]) -> CF POST (ix_cut C_A8206c_at [Z.of_nat j]).
(* glue: Seg/F11.v seg_F11_014 :643 @U via _F; runs f11_014_evt :442 *)
Hypothesis seg_F11_014 : forall POST (j : nat), CF POST (ix_cut C_A820f8_at [Z.of_nat j]) -> CF POST (ix_cut C_A820ac_at [Z.of_nat j]).
(* glue: Seg/F12.v seg_F12 :1695 @U via _F; runs inline in seg_F12 (Appendix A: no stated evt run lemma) *)
Hypothesis seg_F12 : forall POST (j : nat),
  CF POST (ix_cut C_A82138_at [Z.of_nat j]) -> CF POST (ix_cut C_A820fc_at [Z.of_nat j]) /\ CF POST (ix_cut C_A820f8_at [Z.of_nat j]).
(* ----- W4c: F13-F17b ----- *)
(* glue: Seg/F13.v seg_F13 :960 @U via _F; runs sl_run_lib :736, f13_evt :757, f13_evt_ro :838 *)
Hypothesis seg_F13 : forall POST (j : nat), CF POST (ix_cut C_A82154_at [Z.of_nat j]) -> CF POST (ix_cut C_A82138_at [Z.of_nat j]).
(* glue: Seg/F14.v seg_F14 :325 @U via _F; runs f14_evt_e0 :76, f14_evt_dc :106, f14_evt_dc_ro :206, sl_run_lib :303 *)
Hypothesis seg_F14 : forall POST (j : nat),
  CF POST (ix_cut C_A82178_at [Z.of_nat j]) -> CF POST (ix_cut C_A82174_at [Z.of_nat j]) -> CF POST (ix_cut C_A82154_at [Z.of_nat j]).
(* glue: Seg/F15.v seg_F15 :457 @U via _F; runs f15_evt_dc :166, f15_evt_c4 :185, f15_evt_34 :206, f15_run :278 *)
Hypothesis seg_F15 : forall POST (j : nat), CF POST (ix_cut C_A82178_at [Z.of_nat j]) -> CF POST (ix_cut C_A82174_at [Z.of_nat j]).
(* glue: Seg/F15.v seg_F15b :542 @U via _F; runs f15_evt_dc :166, f15_evt_c4 :185, f15_evt_34 :206, f15_run :278 *)
Hypothesis seg_F15b : forall POST (j : nat),
  CF POST (ix_cut C_A821d0_at [Z.of_nat j]) -> CF POST (ix_cut C_A822a0_at [Z.of_nat j]) -> CF POST (ix_cut C_A82178_at [Z.of_nat j]).
(* glue: Seg/F16.v seg_F16 :826 @U via _F; runs f16_loop :276, f16_p284 :386, f16_p270 :424, f16_p250 :457, f16_p238 :490, f16_p210 :526, f16_evt :570 *)
Hypothesis seg_F16 : forall POST (j : nat), CF POST (ix_cut C_A8229c_at [Z.of_nat j]) -> CF POST (ix_cut C_A821d0_at [Z.of_nat j]).
(* glue: PROVED (comment corrected 04:53Z; it used to read "NO PROVED v1.9 RUN TO LIFT", which stopped being true at
   a Theorem Labs lane's F17 proof d65d18383b1).  Seg/F17.v seg_F17 :2007; F17.v's own image-A branch ended in `fail.`
   (in a version not in this delivery, plan M12) and its runs f17_lib_evt :508 / f17_mcpy_evt (not in this delivery) did not close the segment, so the glue's
   run came from a NEW file: a Theorem Labs lane's Seg/F17Fs.v f17_bltz_F / f17_bltz_of_F (an earlier version, blob 7c3b68f65e6, not in this delivery) for the one
   instruction 0x8229c `bltz a0`, not taken under the entry body's 0 <= v0 < 2^63.  Discharged by
   a Theorem Labs lane's lib/A/ACtlG/F17.v glue_seg_F17 (a working branch 775e7e341a5) *)
Hypothesis seg_F17 : forall POST (j : nat), CF POST (ix_cut C_A822a0_at [Z.of_nat j]) -> CF POST (ix_cut C_A8229c_at [Z.of_nat j]).
(* glue: Seg/F17.v seg_F17b :1383; its form in a version not in this delivery stopped at `fail.` (plan M12), and that version's f17_mcpy_evt was proved but unused.
   The old "NO PROVED v1.9 RUN TO LIFT" prefix was removed 04:53Z: a Theorem Labs lane proved F17b on v1.9 at d65d18383b1 and
   a Theorem Labs lane's F17b lane wrote the glue, lib/A/ACtlG/F17b.v:258 glue_seg_F17b *)
Hypothesis seg_F17b : forall POST (j : nat), CF POST (ix_cut C_A823e8_at [Z.of_nat j]) -> CF POST (ix_cut C_A822a0_at [Z.of_nat j]).
(* ----- W4d: F18-F29 ----- *)
(* glue: Seg/F18.v seg_F18 :931 @U via _F; runs f18_evt :57, f18_evt0 :151, f18_evt_ro :261, sl_run_lib :329 *)
Hypothesis seg_F18 : forall POST (j : nat),
  CF POST (ix_cut C_A82400_at [Z.of_nat j]) -> CF POST (ix_cut C_A8275c_at [Z.of_nat j]) -> CF POST (ix_cut C_A823e8_at [Z.of_nat j]).
(* glue: Seg/F19.v seg_F19 :230 @U via _F; runs f19_evt :62, f19_evt_ro :160 *)
Hypothesis seg_F19 : forall POST (j : nat), CF POST (ix_cut C_A82418_at [Z.of_nat j]) -> CF POST (ix_cut C_A82400_at [Z.of_nat j]).
(* glue: Seg/F20.v seg_F20 :397 @U via _F; runs sl_run_lib :206, f20_call_evt :341 *)
Hypothesis seg_F20 : forall POST (j : nat), CF POST (ix_cut C_A824b4_at [Z.of_nat j]) -> CF POST (ix_cut C_A82418_at [Z.of_nat j]).
(* glue: Seg/F21.v seg_F21 :433 @U via _F; runs sl_run_lib :210, f21_t2 :244, f21_evt :360 *)
Hypothesis seg_F21 : forall POST (j : nat),
  CF POST (ix_cut C_A82554_at [Z.of_nat j]) -> CF POST (ix_cut C_A825a0_at [Z.of_nat j]) -> CF POST (ix_cut C_A824b4_at [Z.of_nat j]).
(* glue: Seg/F22.v seg_F22 :364 @U via _F; runs f22_loop :191, f22_run_lib :281, f22_tail :302 *)
Hypothesis seg_F22 : forall POST (j : nat), CF POST (ix_cut C_A825a0_at [Z.of_nat j]) -> CF POST (ix_cut C_A82554_at [Z.of_nat j]).
(* glue: Seg/F23.v seg_F23 :815 @U via _F; runs f23_run_lib :356, f23_evt :607 *)
Hypothesis seg_F23 : forall POST (j : nat), CF POST (ix_cut C_A825c8_at [Z.of_nat j]) -> CF POST (ix_cut C_A825a0_at [Z.of_nat j]).
(* glue: Seg/F24.v seg_F24 :916 @U via _F; runs b7_run_lib :298, f24_evt :828 *)
Hypothesis seg_F24 : forall POST (j : nat), CF POST (ix_cut C_A825d4_at [Z.of_nat j]) -> CF POST (ix_cut C_A825c8_at [Z.of_nat j]).
(* glue: Seg/F25.v seg_F25 :279 @U via _F; runs f25_evt :101 *)
Hypothesis seg_F25 : forall POST (j : nat), CF POST (ix_cut C_A825f4_at [Z.of_nat j]) -> CF POST (ix_cut C_A825d4_at [Z.of_nat j]).
(* glue: Seg/F26.v seg_F26 :99 @U via _F; runs f26_evt :41 *)
Hypothesis seg_F26 : forall POST (j : nat), CF POST (ix_cut C_A82604_at [Z.of_nat j]) -> CF POST (ix_cut C_A825f4_at [Z.of_nat j]).
(* glue: NO PROVED v1.9 RUN TO LIFT -- Seg/F27.v seg_F27 :139 has no stated evt run lemma (Appendix A; a Theorem Labs lane 22:15Z) *)
Hypothesis seg_F27 : forall POST (j : nat),
  CF POST (ix_cut C_A8265c_at [Z.of_nat j]) -> CF POST (ix_cut C_A82750_at [Z.of_nat j]) -> CF POST (ix_cut C_A82604_at [Z.of_nat j]).
(* glue: Seg/F28a.v seg_F28a :326 @U via _F; runs f28_body :232, f28_turn :272 *)
Hypothesis seg_F28a : forall POST (j : nat), CF POST (ix_cut C_A826d4_at [Z.of_nat j]) -> CF POST (ix_cut C_A8265c_at [Z.of_nat j]).
(* glue: Seg/F28b.v seg_F28b :475 @U via _F; runs f28b_run :392 *)
Hypothesis seg_F28b : forall POST (j : nat), CF POST (ix_cut C_A82750_at [Z.of_nat j]) -> CF POST (ix_cut C_A826d4_at [Z.of_nat j]).
(* glue: Seg/F29.v seg_F29 :763 @U via _F; runs f29_evt :527, sl_run_lib :566 *)
Hypothesis seg_F29 : forall POST (j : nat), CF POST (ix_cut C_A8275c_at [Z.of_nat j]) -> CF POST (ix_cut C_A82750_at [Z.of_nat j]).
(* ----- W4e: F30-F36 and the rows ----- *)
(* glue: Seg/F30.v seg_F30 :1392 @U via _F; runs f30_stores :289, f30_evt_call :504, f30_call_norm :583 *)
Hypothesis seg_F30 : forall POST (j : nat), CF POST (ix_cut C_A82798_at [Z.of_nat j]) -> CF POST (ix_cut C_A8275c_at [Z.of_nat j]).
(* glue: Seg/F31.v seg_F31 :550 @U via _F; runs f31n_evt :343, f31c_evt :368, f31c_norm :483 *)
Hypothesis seg_F31 : forall POST (j : nat),
  CF POST (ix_cut C_A827d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A82800_at [Z.of_nat j]) -> CF POST (ix_cut C_A82798_at [Z.of_nat j]).
(* glue: Seg/F32.v seg_F32 :1353 @U via _F; runs f32_evt_a :1004, f32_evt_n :1034, f32_chk16 :1054, f32_chk17 :1093, f32_evt_m :1137 *)
Hypothesis seg_F32 : forall POST (j : nat),
  CF POST (ix_cut C_A828c8_at [Z.of_nat j]) -> CF POST (ix_cut C_A8285c_at [Z.of_nat j]) ->
  CF POST (ix_cut C_A827d8_at [Z.of_nat j]) /\ CF POST (ix_cut C_A82800_at [Z.of_nat j]).
(* glue: Seg/F33.v seg_F33 :189 @U via _F; runs f33_evt :153 *)
Hypothesis seg_F33 : forall POST (j : nat),
  CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat 0]) -> CF POST (ix_cut C_A828bc_at [Z.of_nat j]) -> CF POST (ix_cut C_A8285c_at [Z.of_nat j]).
(* glue: Seg/F34.v seg_F34 :1053 @U via _F; runs f34_evt :189 *)
Hypothesis seg_F34 : forall POST (j i : nat), CF POST (ix_cut C_A82888_at [Z.of_nat j; Z.of_nat i]) -> CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat i]).
(* glue: Seg/F35.v seg_F35 :652 @U via _F; runs f35_evt :485, f35_call :571 *)
Hypothesis seg_F35 : forall POST (j i : nat),
  CF POST (ix_cut C_A8289c_at [Z.of_nat j; Z.of_nat i]) -> CF POST (ix_cut C_A828a0_at [Z.of_nat j; Z.of_nat i]) -> CF POST (ix_cut C_A82888_at [Z.of_nat j; Z.of_nat i]).
(* glue: Seg/F36.v seg_F36_827f0 :3352 @U via _F; runs f36_evt_hit :374, f36_evt_miss :390, f36_evt_back :407, f36_evt_out :443, f36_evt_call :573, f36_call_norm :757, f36_run_lib :1496 *)
Hypothesis seg_F36_827f0 : forall POST (j i : nat),
  CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A82964_at [Z.of_nat j]) -> CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat (S i)]) ->
  CF POST (ix_cut C_A8289c_at [Z.of_nat j; Z.of_nat i]).
(* glue: Seg/F36.v seg_F36_827f4 :3347 @U via _F; runs f36_evt_hit :374, f36_evt_miss :390, f36_evt_back :407, f36_evt_out :443, f36_evt_call :573, f36_call_norm :757, f36_run_lib :1496 *)
Hypothesis seg_F36_827f4 : forall POST (j i : nat),
  CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat (S i)]) -> CF POST (ix_cut C_A828a0_at [Z.of_nat j; Z.of_nat i]).
(* glue: Seg/F36.v seg_F36_82810 :2999 @U via _F; runs f36_evt_82810 :479, f36_evt_call :573, f36_call_norm :757 *)
Hypothesis seg_F36_82810 : forall POST (j : nat), CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A828bc_at [Z.of_nat j]).
(* glue: Seg/F36.v seg_F36_8281c :3050 @U via _F; runs f36_evt_8281c :491, f36_evt_call :573, f36_call_norm :757 *)
Hypothesis seg_F36_8281c : forall POST (j : nat), CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A828c8_at [Z.of_nat j]).
(* glue: Seg/F36.v seg_F36_828b8 :3361 @U via _F; runs f36_evt_828b8 :535, f36_evt_call :573, f36_call_norm :757 *)
Hypothesis seg_F36_828b8 : forall POST (j : nat), CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A82964_at [Z.of_nat j]).
(* ----- W4f: F37-F38 ----- *)
(* glue: Seg/F37.v seg_F37 :787 @U via _F; runs f37_evt_body :448, f37_run_lib :492 *)
Hypothesis seg_F37 : forall POST (j : nat), CF POST (ix_cut C_A82940_at [Z.of_nat j]) -> CF POST (ix_cut C_A828d8_at [Z.of_nat j]).
(* glue: Seg/F38.v seg_F38 :513 @U via _F; runs f38_evt_x :180, f38_evt_b :197, f38_evt_e :226, f38_run_lib :264 *)
Hypothesis seg_F38 : forall POST (j : nat),
  CF POST (ix_cut C_A81d40_at [Z.of_nat (S j)]) -> CF POST C_A82b04 -> CF POST (ix_cut C_A82940_at [Z.of_nat j]).

(* ===== W5 tail: A82b04 -> Post (X1, X2, Jrel, Y1, Y3) ===== *)
(* glue: Seg/X12.v seg_X1 :849 @U via _F; runs x12_store_evt :273, x12_b_evt :329, x12_a_evt :360 *)
Hypothesis seg_X1 : forall POST, CF POST C_A82b20 -> CF POST C_Jrel -> CF POST C_A82b04.
(* glue: Seg/X12.v seg_X2 :814 @U via _F; runs x12_x2_evt :469 *)
Hypothesis seg_X2 : forall POST, CF POST C_Jrel -> CF POST C_A82b20.
(* glue: Seg/YTail.v seg_Jrel :1523 @U via _F; runs jrel_evt_side :1270 (jrel_evt_real :1239 is the discharged class-full arm) *)
Hypothesis seg_Jrel : forall POST, CF POST C_A82b9c -> CF POST C_Jrel.
(* glue: Seg/YTail.v seg_Y1 :995 @U via _F; runs y1_evt :883 *)
Hypothesis seg_Y1 : forall POST, CF POST C_A82bb0 -> CF POST C_A82b9c.
(* glue: Seg/YTail.v seg_Y3 :343 @U via _F; runs y3_evt :169, sl_run_lib :44 *)
Hypothesis seg_Y3 : CF ctl_post_leaf C_A82bb0.

(* ---------------------------------------------------------------------------------------------------------
   6. The loop combinators, in the donor's rt_G_allX pattern (ACfj.v:157-163): induction on the remaining turns
   m, the base case vacuous past the last turn (or, for our[], the last turn's own exits), the step one turn of
   stage hypotheses, the back edge at the head cut with the next index.  Measures from ctrl's own text. *)

(* --- The rows (plan section 3 loop 13), inside the frame turn: head A8286c_at j i, latches F36_827f0 /
   F36_827f4.  Measure 11 - i: ctrl Slot.v:426 `(11 <= i + k)%nat` and :431 `IND 11%nat i`, bound `i <= 10`
   (SlotInv.v:2956). *)
Lemma turn_rows : forall POST (j i : nat),
  CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A82964_at [Z.of_nat j]) ->
  CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat (S i)]) -> CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat i]).
Proof.
  intros POST j i H8d8 H964 HS.
  pose proof (seg_F36_827f4 POST j i H8d8 HS) as H8a0.
  pose proof (seg_F36_827f0 POST j i H8d8 H964 HS) as H89c.
  exact (seg_F34 POST j i (seg_F35 POST j i H89c H8a0)).
Qed.

Lemma loop_rows : forall POST (j : nat), CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A82964_at [Z.of_nat j]) ->
  forall (m i : nat), (11 <= i + m)%nat -> CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat i]).
Proof.
  intros POST j H8d8 H964. induction m as [|m IH]; intros i Hm.
  - apply vac_A8286c. lia.
  - destruct (Nat.lt_ge_cases 10 i) as [Hi|Hi]; [exact (vac_A8286c POST j i Hi)|].
    exact (turn_rows POST j i H8d8 H964 (IH (S i) ltac:(lia))).
Qed.

(* --- The frame loop (loop 7): head A81d40_at j, latch F38.  Measure 256 - j: ctrl Slot.v:490
   `(256 <= j + k)%nat` and :495 `IND 256%nat j`, bound LK `j <= 255` (SlotInv.v:898).  One turn is ctrl's
   turn_frames (Slot.v:435-485) with the row loop at i = 0 (Slot.v:444). *)
Lemma turn_frames : forall POST (j : nat), CF POST C_A82b04 ->
  CF POST (ix_cut C_A81d40_at [Z.of_nat (S j)]) -> CF POST (ix_cut C_A81d40_at [Z.of_nat j]).
Proof.
  intros POST j Hb04 HS.
  pose proof (seg_F38 POST j HS Hb04) as H940.
  pose proof (seg_F37 POST j H940) as H8d8.
  pose proof (seg_F36_828b8 POST j H8d8) as H964.
  pose proof (seg_F36_8281c POST j H8d8) as H8c8.
  pose proof (seg_F36_82810 POST j H8d8) as H8bc.
  pose proof (seg_F33 POST j (loop_rows POST j H8d8 H964 11 0 ltac:(lia)) H8bc) as H85c.
  destruct (seg_F32 POST j H8c8 H85c) as [H7d8 H800].
  pose proof (seg_F31 POST j H7d8 H800) as H798.
  pose proof (seg_F30 POST j H798) as H75c.
  pose proof (seg_F29 POST j H75c) as H750.
  pose proof (seg_F28b POST j H750) as H6d4.
  pose proof (seg_F28a POST j H6d4) as H65c.
  pose proof (seg_F27 POST j H65c H750) as H604.
  pose proof (seg_F26 POST j H604) as H5f4.
  pose proof (seg_F25 POST j H5f4) as H5d4.
  pose proof (seg_F24 POST j H5d4) as H5c8.
  pose proof (seg_F23 POST j H5c8) as H5a0.
  pose proof (seg_F22 POST j H5a0) as H554.
  pose proof (seg_F21 POST j H554 H5a0) as H4b4.
  pose proof (seg_F20 POST j H4b4) as H418.
  pose proof (seg_F19 POST j H418) as H400.
  pose proof (seg_F18 POST j H400 H75c) as H3e8.
  pose proof (seg_F17b POST j H3e8) as H2a0.
  pose proof (seg_F17 POST j H2a0) as H29c.
  pose proof (seg_F16 POST j H29c) as H1d0.
  pose proof (seg_F15b POST j H1d0 H2a0) as H178.
  pose proof (seg_F15 POST j H178) as H174.
  pose proof (seg_F14 POST j H178 H174) as H154.
  pose proof (seg_F13 POST j H154) as H138.
  destruct (seg_F12 POST j H138) as [H0fc H0f8].
  pose proof (seg_F11_014 POST j H0f8) as H0ac.
  pose proof (seg_F11_fd4 POST j H0ac) as H06c.
  pose proof (seg_F10 POST j H06c H0ac H0fc) as Hff4.
  pose proof (seg_F9 POST j Hff4) as Hf88.
  pose proof (seg_F8 POST j Hf88) as Hf7c.
  pose proof (seg_F7 POST j Hf7c) as Hf64.
  pose proof (seg_F6_ebc POST j Hf64) as Hf54.
  pose proof (seg_F6_e28 POST j Hf54) as Hec0.
  pose proof (seg_F5_e10 POST j Hec0) as Hea8.
  pose proof (seg_F5_e0c POST j Hec0) as Hea4.
  pose proof (seg_F5_df0 POST j Hf54) as He88.
  pose proof (seg_F5 POST j Hf54) as He84.
  destruct (seg_F4 POST j He88 Hea4 Hea8 He84) as [Hdfc He54].
  pose proof (seg_F3 POST j Hdfc) as Hdd0.
  pose proof (seg_F2 POST j Hdd0 He54) as Hda4.
  exact (seg_F1 POST j Hda4).
Qed.

Lemma loop_frames : forall POST, CF POST C_A82b04 ->
  forall (m j : nat), (256 <= j + m)%nat -> CF POST (ix_cut C_A81d40_at [Z.of_nat j]).
Proof.
  intros POST Hb04. induction m as [|m IH]; intros j Hm.
  - apply vac_A81d40. lia.
  - destruct (Nat.lt_ge_cases 255 j) as [Hj|Hj]; [exact (vac_A81d40 POST j Hj)|].
    exact (turn_frames POST j Hb04 (IH (S j) ltac:(lia))).
Qed.

(* --- The round trip (loop 4): head A815cc_at b, latches R7 (n_b = 0 skip) and R21.  Measure 7 - b: ctrl
   Slot.v:527 `(7 <= b + k)%nat` and :532 `IND 7%nat b`, bound RB `b <= 6` (SlotInv.v:830); the image's
   `li a1,7` at 0x81954 (ACtlK.v:37-38).  One turn is ctrl's turn_rt (Slot.v:500-521); the loop's exits A81ac0 /
   A81ac8 / A81b10 are taken at b = 6 inside R7 / R21 and are supplied from before the loop (Slot.v:555-558). *)
Lemma turn_rt : forall POST (b : nat), CF POST C_A81ac0 -> CF POST C_A81ac8 -> CF POST C_A81b10 ->
  CF POST (ix_cut C_A815cc_at [Z.of_nat (S b)]) -> CF POST (ix_cut C_A815cc_at [Z.of_nat b]).
Proof.
  intros POST b Hac0 Hac8 Hb10 HS.
  pose proof (seg_R21 POST b HS Hac0 Hac8) as H924.
  pose proof (seg_R20 POST b H924) as H8e8.
  pose proof (seg_R19 POST b H8e8) as H8d0.
  pose proof (seg_R18 POST b H8d0) as H858.
  pose proof (seg_R17 POST b H858) as H83c.
  pose proof (seg_R16 POST b H924) as H7ec.
  pose proof (seg_R15 POST b H924) as H7c8.
  pose proof (seg_R14 POST b H83c) as H768.
  pose proof (seg_R13 POST b H924) as H734.
  pose proof (seg_R12 POST b H734) as H708.
  pose proof (seg_R11 POST b H734) as H6c4.
  pose proof (seg_R10 POST b H6c4 H708 H768 H7c8 H7ec) as H680.
  pose proof (seg_R9 POST b H680) as H658.
  pose proof (seg_R8 POST b H658) as H640.
  pose proof (seg_R7 POST b H640 HS Hac0 Hb10) as H5ec.
  exact (seg_R6 POST b H5ec).
Qed.

Lemma loop_rt : forall POST, CF POST C_A81ac0 -> CF POST C_A81ac8 -> CF POST C_A81b10 ->
  forall (m b : nat), (7 <= b + m)%nat -> CF POST (ix_cut C_A815cc_at [Z.of_nat b]).
Proof.
  intros POST Hac0 Hac8 Hb10. induction m as [|m IH]; intros b Hm.
  - apply vac_A815cc. lia.
  - destruct (Nat.lt_ge_cases 6 b) as [Hb|Hb]; [exact (vac_A815cc POST b Hb)|].
    exact (turn_rt POST b Hac0 Hac8 Hb10 (IH (S b) ltac:(lia))).
Qed.

(* --- The outer our[] loop (loops 2, 3): head A81414_at t, back edge 0x81488 -> 0x81400 inside the turn,
   exits A81b14 / A814f8 after turn 5.  Measure 5 - t: ctrl Seg/R1.v:2165-2166 (induction on Z.to_nat (5 - t))
   with the turn r1_turn (:1275, `t < 5 ->` the next turn), range `0 <= t <= 5` (SlotInv.v:1109,
   ACtlCutP.v:1141).  The base case is the last turn, closed by the loop's exit cuts.  The inner our[] loop is
   run level inside the turn's runs (plan section 3), so it has no cut-level combinator. *)
Lemma loop_our : forall POST, CF POST C_A814f8 -> CF POST C_A81b14 ->
  forall (m : nat) (t : Z), 0 <= t <= 5 -> 5 - t <= Z.of_nat m -> CF POST (C_A81414_at t).
Proof.
  intros POST H4f8 Hb14. induction m as [|m IH]; intros t Ht Hm.
  - apply (seg_R1_turn POST t); [| exact Hb14 | exact H4f8].
    intros Hlt. exfalso. change (Z.of_nat 0) with 0 in Hm. lia.
  - apply (seg_R1_turn POST t); [| exact Hb14 | exact H4f8].
    intros Hlt. rewrite Nat2Z.inj_succ in Hm. apply IH; lia.
Qed.

(* Segment R1 in its section-2.3 form, PROVED (ctrl's seg_R1, R1.v:2160-2170). *)
Lemma seg_R1 : forall POST, CF POST C_A814f8 -> CF POST C_A81b14 -> CF POST C_A81414.
Proof.
  intros POST H4f8 Hb14. apply ctl_from_our. intros t Ht.
  apply (loop_our POST H4f8 Hb14 (Z.to_nat (5 - t)) t Ht). rewrite Z2Nat.id by lia. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   7. The composition: backwards from the exit cut C_A82bb0 to the entry cut C_ENTRY, in ctrl's discharge order
   (Slot.v:537-568: release, epilogue, frame loop, P12 .. P1, round trip, R5 .. R1, A5 .. A1), for every POST. *)
Lemma ctl_walk_from : forall POST, (forall cx p, POST (ACtlCut.cx_set_fpos cx p) = POST cx) ->
  CF POST C_A82bb0 -> CF POST C_ENTRY.
Proof.
  intros POST HPF Hbb0.
  pose proof (seg_Y1 POST Hbb0) as Hb9c.
  pose proof (seg_Jrel POST Hb9c) as Hjrel.
  pose proof (seg_X2 POST Hjrel) as Hb20.
  pose proof (seg_X1 POST Hb20 Hjrel) as Hb04.
  pose proof (seg_P12 POST (loop_frames POST Hb04 256 0 ltac:(lia)) Hb04) as Hc84.
  pose proof (seg_P11 POST Hc84) as Hc60.
  pose proof (seg_P10 POST Hc60) as Hc4c.
  pose proof (seg_P9 POST Hc4c) as Hc34.
  pose proof (seg_P8 POST Hc34) as Hc20.
  pose proof (seg_P7 POST Hc20) as Hbf8.
  pose proof (seg_P6 POST Hbf8) as Hbd8.
  pose proof (seg_P5 POST Hbd8) as Hb90.
  pose proof (seg_P4 POST Hb90) as Hb80.
  pose proof (seg_P3 POST Hb80) as Hb14.
  pose proof (seg_P2 POST Hb14) as Hb10.
  pose proof (seg_P1_70 POST Hb10) as Hac8.
  pose proof (seg_P1 POST Hb10) as Hac0.
  pose proof (seg_R5 POST (loop_rt POST Hac0 Hac8 Hb10 7 0 ltac:(lia))) as H588.
  pose proof (seg_R4 POST H588) as H578.
  pose proof (seg_R3 POST H578) as H52c.
  pose proof (seg_R2 POST H52c) as H4f8.
  pose proof (seg_R1 POST H4f8 Hb14) as H414.
  pose proof (seg_A5 POST 0 H414) as H400.
  pose proof (seg_A4 POST H400 Hjrel) as H0e4.
  pose proof (seg_A3 POST H0e4) as Hf88.
  pose proof (seg_A2 POST Hf88) as Hf54.
  exact (seg_A1 POST HPF Hf54 Hf88).
Qed.

(* The walk at the exit post the top consumes.  ctl_post_leaf reads c_regs, c_ly, c_S, c_W, c_mem, c_md, c_p, c_n
   and c_M, never c_fpos, so seg_A1's premise holds by reflexivity. *)
Lemma ctl_walk_leaf : CF ctl_post_leaf C_ENTRY.
Proof. exact (ctl_walk_from ctl_post_leaf (fun cx p => eq_refl) seg_Y3). Qed.

(* The brief's statement: the walk at ACtlCut.v's own exit post. *)
Lemma ctl_walk : CF ctl_post C_ENTRY.
Proof.
  apply (ctl_from_mono ctl_post_leaf ctl_post C_ENTRY); [| exact ctl_walk_leaf].
  intros cx W' c' _ (ly' & S' & regs' & mem' & md' & k & Ec & Hpost).
  exists (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.LL 0 (m_fs (c_md cx)) []), ly', S', regs', mem', md', k.
  exact (conj Ec Hpost).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   8. The top: the core's lib contract (the donor's tfib_lib_x_body / tfib_lib_x, ACfj.v:230-259).  The entry
   context is the contract's own arguments with the engine's sp anchor; the journal starts in its initial form
   (ajournal_init, at the core's sink head and FP = []); the walk runs from C_ENTRY at index [], k = 0, whose
   configuration cfg_at segs (cut_pc C_ENTRY) regs mem md is the contract's start cfg_at segs A_LLVMF regs mem md
   (0x80edc both); SRr's definition applied to the entry AI fact is srz_enter; the leaf is LL 0 (m_fs md) []. *)
Theorem ctl_lib_x : A.ACfn.tfib_lib_contract_x B MT XM_LIB XN_LIB RLO RHI.
Proof using All.
  unfold A.ACfn.tfib_lib_contract_x.
  intros ly S W regs mem md p n pl M K HAI HPRE HK.
  rewrite LS_LEAF.
  pose proof HPRE as (HAFN & _ & _ & _ & _ & _ & _ & Hfr0 & _).
  pose (cx := ACtlCut.mkCtlCx ly S W regs mem md p n pl M 0
                (32 * ((Reusable.YG0d.spZ regs + -128) / 32))).
  assert (HB : CB cx) by (split; [exact HPRE | reflexivity]).
  assert (HWALK : Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs A.ACfn.A_LLVMF regs mem md)
                    (ctl_post_leaf cx)).
  { refine (ctl_walk_leaf cx [] 0 0 ly S W regs mem md HB _ Hfr0
              (fun cid pos (H : In (cid, pos) []) => False_ind _ H) _ _ (CTLRT_ENTRY cx HB)).
    - first [ exact (Reusable.YCbq.ajournal_init (SK := A.AE2k.tfib_sink_head)
                       segs B A.ACfn.LLVMF_STK [] ly S W regs mem md [] HAFN)
            | (eapply (Reusable.YCbq.ajournal_init (SK := A.AE2k.tfib_sink_head)); exact HAFN) ].
    - exact (Z.le_refl 0).
    - (* C_ENTRY's body: the live list, the sp anchor and (batch 4, B5.1) regs = c_regs cx at regs3 := c_regs cx *)
      split; [apply Permutation_refl | split; reflexivity]. }
  apply (HWALK HAI).
  intros W' c' Hwle HAI' (ly' & S' & regs' & mem' & md' & k & Ec & Hpost).
  apply (HK _ W' c' Hwle HAI').
  exists ly', S', regs', mem', md', k.
  exact (conj Ec Hpost).
Qed.

End Ctl.

(* ---------------------------------------------------------------------------------------------------------
   9. THE TOP AT THE CORE'S OWN SYMBOL BUNDLE (porter a Theorem Labs lane 23:10Z; mirrors image B's twin, lib/B/ACtl.v
   section 9 at a working branch 6adbb8c9272).  B := A.AD2l.CtrlB (AD2l.v:18, the relocated
   donor TfibB), TFIB_SYMS := A.AD2l.CtrlB_syms (AD2l.v:72, the donor's TfibB_syms) and TFIB_LIB := CtrlB_libS,
   with the meter and bounds fixed as the donor's AD2o.v:30-35 fixes them: MT := Reusable.YCbp.ameter_triv
   (YCbp.v:17), XM_LIB = XN_LIB := XL0 (the donor's A/ACfi.v:56; ACfi is cgif's unit file and does not join the
   core, so XL0 is restated here), RLO / RHI := 0x9e380 / 0xa07c8, the core's read-only span of record (its
   in_ro_tfa, ACeh.v:44 and AD1r.v:205: .data.rel.ro + .got, AB1w.v:16-17; A.ACfn names no RLO / RHI).  The six
   hypotheses before the symbol records are discharged here: RELRO_IMG at those bounds by relro_img_ctrl
   (segment 2 of tfibsegs is [0x9e000, 0xa1000), the image's third PT_LOAD), RELRO_KIND_NAME / RELRO_CAT /
   RELRO_FRAMES at those bounds by relro_kind_name_ctrl / relro_cat_ctrl / relro_frames_ctrl (unfold + lia), LAWS
   by the core's Reusable.YG0q.AR_laws_ok (YG0q.v:803), and MO_LE at ameter_triv by mo_le_triv.  The two callee
   constants are instantiated at 9072 / 0x21200, and KREPLY / KPARSE are eq_refl.
   CtrlB_libS is the port of the donor's A/ACfi.v:25 (TfibB_libS : TfibLib TfibB).  Batch 5: it is no longer a
   hypothesis; it is a Theorem Labs lane's PROVED A.ACtlBCode.actlb_libS (lib/A/ACtlBCode.v, a working branch
   d6d78eefbce, on this base through the interim merge 15e182dd785), bound by a Let.
   BATCH 4 (section 1c), discharged here: AFREE4 / AMALLOC4 by the core's Reusable.YCbp.afree04_rule_triv /
   amalloc04_rule_triv (YCbp.v:30-47) over tfibsegs' segs_low (A.ACeh.tfib_segs_low), api_env (A.ACeh.tl_env of
   CtrlB_libS), the AR laws, model_laws (Reusable.YG05.model_laws_ok of CtrlTSyms' ts_universe) and the core's
   afree_realizes / amalloc_realizes at CtrlB, which the base does NOT prove (the core states them, YG0d.v:254 /
   :270; CtrlClose carries them as Section hypotheses), so they are this Section's NAMED hypotheses CtrlB_afree /
   CtrlB_amalloc, beside CtrlB_libS; MT_FREE and MO_MALLOC_OK by `fun _ _ => I` (ameter_triv's mo_ok is True); BLKSH
   by a Theorem Labs lane's A.ProgWorldShadow.ctl_block_shadow_of_AR; AIL by the core's A.AD1u.tfib_AIL; QMARK_ROW by
   qmark_row_ctrl (the record AF0m's Tfib_const_shadow row, decided by vm_compute); the strcmp entry at 0x42964
   with A_strcmp_tramp_at by eq_refl.  Batch 5: ASM6 by the Let CtrlB_asm6 : astack_malloc_realizes segs CtrlB 6,
   A.Rt.StackMalloc6.disco_stack_malloc6 at CtrlB, its AR laws and CtrlB_syms (lib/A/Rt/StackMalloc6.v on this unit,
   (an earlier version, blob 011e76fce0c, not in this delivery), from a working branch 055c2ebca7f).
   Still open, so arguments of ctl_lib_x_CtrlB: TPARSE, TREPLY, GLOBS_A with GLOBS_A_MARKED and NAME_GLOB, TBUILD,
   CLS, CM_SPEC, AMEMCHR_SITE, H_strcmp (reasons in section 1c).  CTLRT_ENTRY is
   not an argument: Section Ctl binds it to the proved A.ACtlTopFacts.ctlrt_C_entry (section 4). *)
Definition XL0 : Z -> Z := fun _ => 0.

Lemma relro_img_ctrl : forall a, 0x9e380 <= a < 0xa07c8 -> Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha. unfold Reusable.YG0d.in_img.
  assert (Hb : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs) 2 =
               Some (0x9e000, 0x3000)) by (vm_compute; reflexivity).
  rewrite nth_error_map in Hb. destruct (nth_error segs 2) as [sg|] eqn:E; [|discriminate Hb].
  cbn in Hb. injection Hb as H1 H2.
  exists sg. split; [exact (nth_error_In _ 2 E) | rewrite H1, H2; lia].
Qed.

Lemma relro_kind_name_ctrl : 0x9e380 <= 0x9e760 /\ 0x9e760 + 112 <= 0xa07c8.
Proof. lia. Qed.

Lemma relro_cat_ctrl : 0x9e380 <= A.Prog.SlotModel.CAT /\
  A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= 0xa07c8.
Proof. unfold A.Prog.SlotModel.CAT, A.Prog.SlotModel.CAT_N, A.Prog.SlotModel.CAT_ROW. lia. Qed.

Lemma relro_frames_ctrl : 0x9e380 <= 0x9f7e0 /\ 0x9f7e0 + 264 <= 0xa07c8.
Proof. lia. Qed.

Lemma mo_le_triv : forall (S S' : Reusable.YG00.astate) (m : Z),
  Reusable.YC5d.mo_le Reusable.YCbp.ameter_triv S S' m.
Proof. intros S S' m. exact I. Qed.

(* QMARK_ROW at the record core: the row `z1 (ANum 0x7fffc23c) 0x2` is in Tfib_const_shadow (AF0m.v:2179), and
   Tfib_const ly does not depend on ly (AF0m.v:2954), so membership is one boolean search, closed by vm_compute
   (lib/Reusable/YConstIn.v's existsb_row_In). *)
Lemma qmark_row_ctrl : forall ly,
  In (Reusable.YG0f.z1 (Reusable.YG0f.ANum (Reusable.YG0f.shadow_addr A.Prog.reac_ctrl_kind_name_c.QMARK)) 2) (A.AF0m.Tfib_const ly).
Proof. intros ly. apply Reusable.YConstIn.existsb_row_In. vm_compute. reflexivity. Qed.

Section CtlTop.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
(* a Theorem Labs lane's proved lib record at CtrlB (see above). *)
Let CtrlB_libS : A.ACeh.TfibLib A.AD2l.CtrlB := A.ACtlBCode.actlb_libS.
(* The core's allocator realizes facts at CtrlB (YG0d.v:254, :270): not proved on this base (see above). *)
Hypothesis CtrlB_afree : Reusable.YG0d.afree_realizes segs A.AD2l.CtrlB.
Hypothesis CtrlB_amalloc : Reusable.YG0d.amalloc_realizes segs A.AD2l.CtrlB.
(* The fake-stack malloc rule of class 6 at CtrlB (YG0d.v:285), Section Ctl's ASM6: a Theorem Labs lane's disco_stack_malloc6
   (see above). *)
Let CtrlB_asm6 : Reusable.YG0d.astack_malloc_realizes segs A.AD2l.CtrlB 6 :=
  A.Rt.StackMalloc6.disco_stack_malloc6 fx A.AD2l.CtrlB (Reusable.YG0q.AR_laws_ok segs A.AD2l.CtrlB) A.AD2l.CtrlB_syms.
Let ctrlB_ml := Reusable.YG05.model_laws_ok (Reusable.YG0f.as_universe A.AD2l.CtrlB) (A.AF0m.ts_universe A.AD2l.CtrlB A.AD2l.CtrlB_syms).

(* The top at CtrlB.  Its remaining arguments are Section Ctl's others over CtrlB, in declaration order: the open
   nine (TPARSE .. H_strcmp, with the Variable GLOBS_A and batch 5's NAME_GLOB), LS_LEAF, CHAIN_OF_CUT and the 94 stage
   hypotheses.  The two callee constants are no longer among them: they are instantiated here at 9072 / 0x21200,
   with KREPLY / KPARSE by eq_refl; nor is the strcmp entry, instantiated at 0x42964. *)
Definition ctl_lib_x_CtrlB :=
  ctl_lib_x (fx := fx) (rc := rc) (LS := LS) A.AD2l.CtrlB Reusable.YCbp.ameter_triv XL0 XL0 0x9e380 0xa07c8
    relro_img_ctrl relro_kind_name_ctrl relro_cat_ctrl relro_frames_ctrl
    (Reusable.YG0q.AR_laws_ok segs A.AD2l.CtrlB) mo_le_triv A.AD2l.CtrlB_syms CtrlB_libS
    9072 0x21200 eq_refl eq_refl
    (Reusable.YCbp.afree04_rule_triv (SK := A.AE2k.tfib_sink_head) segs A.AD2l.CtrlB A.ACeh.tfib_segs_low
       (A.ACeh.tl_env A.AD2l.CtrlB CtrlB_libS) (Reusable.YG0q.AR_laws_ok segs A.AD2l.CtrlB) ctrlB_ml CtrlB_afree)
    (fun _ _ => I)
    (Reusable.YCbp.amalloc04_rule_triv (SK := A.AE2k.tfib_sink_head) segs A.AD2l.CtrlB A.ACeh.tfib_segs_low
       (A.ACeh.tl_env A.AD2l.CtrlB CtrlB_libS) (Reusable.YG0q.AR_laws_ok segs A.AD2l.CtrlB) ctrlB_ml CtrlB_amalloc)
    (fun _ _ => I)
    CtrlB_asm6
    (A.ProgWorldShadow.ctl_block_shadow_of_AR A.AD2l.CtrlB)
    (A.AD1u.tfib_AIL A.AD2l.CtrlB A.AD2l.CtrlB_syms)
    qmark_row_ctrl
    0x42964 eq_refl.
End CtlTop.

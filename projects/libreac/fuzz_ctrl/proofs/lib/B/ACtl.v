(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 507 of its 559 lines of code are new or changed and 3060 lines of the source are left out. *)
(* lib/B/ACtl.v -- the TOP and the COMPOSITION of fuzz_ctrl image B's (asan-ubsan) walk of LLVMFuzzerTestOneInput
   (libreac v1.9.0), in the released cgif_file_fuzzer form.  Written by a Theorem Labs lane as the image-B twin of
   a Theorem Labs lane's lib/A/ACtl.v (a working branch e76ced8e847 with a Theorem Labs lane's frame-law fix b535733d786);
   single writer.  It states every segment's stage as a named Section hypothesis, PROVES the loop combinators and
   the backward chain, and PROVES the step from the chain to the core's lib contract
   Reusable.YCfn.tfib_lib_contract_x.  Section 9 instantiates that top at the B core's own symbol bundle CtrlB
   (porter 23:10Z; agreed with a Theorem Labs lane 23:53Z, mirrored in image A).

   PROVENANCE
   - RULE 24 (released proofs first): proof-index LLVMFuzzerTestOneInput (index v5, built 2026-10-28
     20:16:23Z from e966c513ee6, ossv/recipes@a8831f7c5c), second-agent check a Theorem Labs lane 21:10Z CONFIRM:
     cgif/cgif_file_fuzzer is the only released ASan donor on this branch, LPS and framework.  This file follows
     that donor's own composition, proofs/cgif/cgif_file_fuzzer/lib/A/ACfj.v at origin/ossv/recipes c8557374ad2e
     (image B's twin: the root YCfj.v): the loop lemma rt_G_allX (:157-163), the leaf lx_leaf_fail (:180-207),
     tfib_lib_x_body (:230-257) and tfib_lib_x (:258).  ctrl's own assembly of the same cuts, lib/B/Prog/Seg/Slot.v
     at 3803efccea0 (S_ forms :48-259, vac_* :381-397, turn_* / loop_* :400-516, slot_entry :520-551), is the
     segment graph and the proof pattern of the loops.
   - cut layer: lib/B/ACtlCut.v (ctlcx, ctl_base, ctlcut, ctl_from, ix_cut / ctl_from_ix, ctl_post, ctl_rt) and
     lib/B/ACtlCutP.v (the cut records C_<cut>), written in the same commit as this file.  Segment rows: the
     translation llvmf-B-walk-plan.md section 2.3 (a working note, not in this delivery) (90 rows), with the loops section 3
     and pieces section 5 (W4a-W4g).
   - route (lead, 22:15Z, via a Theorem Labs lane): route (a).  ctrl's proved v1.9 segment runs are re-run in footprint form
     (_F over StepF) and the cut glue lifts each through the bridge into a stage.  The comment line "glue:" above
     each stage hypothesis names the proved run(s) its glue lifts (segment file, seg_ lemma, its line and commit,
     and the run lemmas, from section 2.3 column 7).  UB = 3803efccea0, EB = d574f6c66de (A5 / R1 / R2: WIP,
     iteration-only, build not checked).

   WHAT IS A HYPOTHESIS HERE, AND WHAT IS NOT
   - 89 stage hypotheses seg_<NAME>, one per live segment of section 2.3, in continuation form (the donor's rt_A2 /
     rt_B shape, A/ACf0.v:173, A/ACf1.v:499), each exactly ctrl's S_<NAME> (Slot.v:48-259) over the cut records:
     forall POST, the exits' ctl_from -> the entry's ctl_from.  A W piece owes each one.  One row of section 2.3
     has no hypothesis: S_Y2 (its entry C_B82f58 is gone: the class-full arm is discharged, ACtlCutP.v's note), and
     for the same reason seg_Jrel has no B82f58 premise.  Image B's R1 owns the our[] loop inside its segment lemma
     (Slot.v:13-14; R1.v:41-42 through EB A5.v b_loop :2423), so seg_R1 is ctrl's whole S_R1 and this file has no
     our[] turn and no our[] combinator (image A states R1 as its turn, ctrl A's r1_turn).
   - 6 non-stage hypotheses of Section Ctl: RELRO_IMG (the read-only span lies in the image, a Theorem Labs lane's shared
     form), TFIB_SYMS and TFIB_LIB (the core's two symbol records for B, image A's names), LS_LEAF (the lib
     shape's tree is one leaf), CTLRT_ENTRY (the carried runtime facts at the entry) and CHAIN_OF_CUT (the
     frame-pointer chain and call trace at an allocator call, from ACtlCut.v section
     1b's ctl_chain / ctl_trace_in; the bridge that would prove it is not on this branch); and 1 of section 9:
     CtrlB_libS (TfibLib at the B core's CtrlB, until it is proved).  Their reasons are at their declarations.
     ctl_lib_x is closed `Proof using All`, so every Section hypothesis, the stage ones included, is an argument
     of ctl_lib_x and shows in Print Assumptions (a Theorem Labs lane 23:53Z: no Aborted lemma; an unprovable step is a named
     hypothesis).  ACtlCut.ajournal_fp_nil is NOT a hypothesis: it is the donor's lemma and proof, copied verbatim into
     ACtlCut.v (section FpNil) so the stage files can use it without Requiring this file (porter 22:43Z).
   - no Axiom, no Parameter, no Admitted, no admit.

   THREE DEPARTURES FROM THE BRIEF'S WORDING, EACH FORCED BY THE TYPES (as image A's)
   1. The exit post.  ctl_post (ACtlCut.v section 6) packs the leaf existentially.  The contract's goal is
      srealizes ... (LIBK pl (m_fs md) K), and for fuzz_ctrl's shape (ag_shape checksum_shape, lib/B/ZTraceSpec.v:14-20:
      LIBK pl fs K = K (LL 0 fs [])) that fixes the leaf to LL 0 (m_fs md) [].  An existential leaf with the post's
      [sink_token] journal does not give m_fs md' = m_fs md, so the top cannot be closed from ctl_post.  The donor
      fixes the same leaf inside the walk's continuation (ACfj.v:186, HLEAF (LL 0 (m_fs (c_md cx)) [])).  So the
      exit stage seg_Y3 reaches ctl_post_leaf below (ctl_post with that leaf), the backward chain is proved for
      every POST, ctl_walk : ctl_from ... ctl_post C_ENTRY is derived from it by ctl_from_mono, and the top
      consumes ctl_walk_leaf.
   2. SK and FP are instantiated once, in the notation block of section 1, not declared: the journal's sink head
      is the core's Reusable.YE2k.tfib_sink_head (the head the core's post journal uses), and the walk runs with
      FP = [] as the donor's does.  A stage lemma proved for every SK and FP discharges its hypothesis by
      instantiation.
   3. srz_enter (donor A/ACfh.v:47, outside the core list) is not needed: the top applies SRr's own definition
      (Reusable.YA0n.SRr, donor YA0n.v:34-37) to the entry AI fact, which is srz_enter's whole proof (ACfh.v:50).
      So it is neither imported nor a hypothesis.

   NAMES THIS FILE TAKES FROM THE CORE (the relocated cgif core, porter's flat layout; nothing here is restated)
     Reusable.YCfn   tfib_lib_contract_x (the statement proved), tfib_lib_post_x (ctl_post_leaf), A_LLVMF,
                     RA_LLVMF, LLVMF_STK, EV_LIB (the donor's root YCfn.v, image B's twin of A/ACfn.v)
     Reusable.YB1v   tfibsegs, the core's segment list (donor root YB1v.v:11; porter 22:45Z)
     Reusable.YE2k   tfib_sink_head, the core's sink head (donor root YE2k.v:44, ofl_head 0x5fcd48 = ctrl's B)
     Reusable.YK11   FPState                         Reusable.YM05  RunCeil
     Reusable.YG0f   asyms (donor YG0f.v:154)        Reusable.YC5d  ameter_ops
     Reusable.YG0d   cfg_at, spZ                     Reusable.YI16  sink_head
     Reusable.YCbq   ajournal, ajournal_init (donor YCbq.v:383-392), aos_step_mono (:65), fp_spares_closed (:87),
                     sink_closed_nil (:99)
     Reusable.YI04   inFP_nil (donor YI04.v:390; in YCbq's closure; ctrl's kept lib/Reusable/YI04.v:393)
     Reusable.YA0n   world, SRr_mono (donor YA0n.v:47-52), SRr (by its definition, YA0n.v:34-37)
     Reusable.YO09   lib_shape, LIBK, LL (donor YO09.v:14-16)
     Reusable.YF0m   CtrlTSyms (TFIB_SYMS's type)   Reusable.YCeg  TfibLib (TFIB_LIB's type; lib_const_addr)
     Reusable.YD2l   CtrlB, CtrlB_syms (section 9;  Reusable.YCbp  ameter_triv (section 9)
                     a Theorem Labs lane 00:13Z: B core layout; YD2l.v:14 / :68)
                     -- the B core's names, by analogy with the image-A planning core (AF0m / ACeg / AD2l, YCbp);
                     the porter confirms them when the B core lands.
   From LinuxProcessSemantics (as the donor's YCfn.v imports them): config, m_fs, Segment.  From B.ACtlK:
   EV_LLVMF.  From B.ACtlCut: ctlcx, mkCtlCx, ctlcut, mkCtlCut, cut_pc / cut_own / cut_kmax / cut_body, ix_cut,
   the c_* fields, ctl_base, ctl_from, ctl_post, ctl_rt, ctl_chain, ctl_trace_in.  From B.ACtlCutP: the 90 records C_<cut> bound below,
   ixn, RS, RB, LI, RL.
   SHADOWED NAMES (a Theorem Labs lane via the porter, 21:37Z): lib/Lib's copies of the four shadowed machine names are never
   Required here; the only one used, cfg_at, is Reusable.YG0d-qualified.  Check (nothing outside comments):
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/B/ACtl.v
   CLOSURE: this file Requires no forbidden module itself (SlotInv.v, lib/AZ/**, AsanRTInv.v, Contract.v,
   FrameAPI.v, AZ/AS/SpinAlg, A/W6, MemNorm.v), and neither does B.ACtlCutP (it restates rt_disjoint).

   BUILD STATE (honest, at writing; now stale: the relocated B core is in this tree, lib/Reusable/YCfn.v, lib/Reusable/YD2l.v and the other files at :65-82): the relocated core had not landed (a Theorem Labs lane 21:22Z: no cb base), so this file, like
   ACtlCut.v and ACtlCutP.v, does not compile yet.  It is a labelled stand-in, written so the first scratch
   typecheck has the least to fix.  Nothing here was built, committed or pushed. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YK18.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YI16 YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YCfn Reusable.YE2k.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCeg Reusable.YD2l Reusable.YF0m Reusable.YCbp.
(* lib/Lib/Mem.v, Required only (never Imported), for the saved-register bytes in CHAIN_OF_CUT's premise. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlK B.ACtlCut B.ACtlCutP.
(* a Theorem Labs lane's image-B ProgWorld (VIS0 / OWNED_RO texts; ctlrt_of_AR_stmt in B.ProgWorld, proved in B.ProgWorldCtlRt). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld.
Import ListNotations.
Local Open Scope Z_scope.

(* ctrl's vacuity splitter (Slot.v:374-377): split every conjunction and existential in the context. *)
Ltac vac_split := repeat match goal with
  | H : exists _, _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  end.

(* The walk meets the core's event bound through its own measured need (ACtlK.v defers this here, where the
   core's name is in scope). *)
Lemma ev_llvmf_le : B.ACtlK.EV_LLVMF <= Reusable.YCfn.EV_LIB.
Proof. unfold B.ACtlK.EV_LLVMF, Reusable.YCfn.EV_LIB. lia. Qed.

(* The loop indices of ACtlCutP.v (ixn) at a concrete index list. *)
Lemma ixn0 : forall b : nat, ACtlCutP.ixn 0 [Z.of_nat b] = b.
Proof. intros b. exact (Nat2Z.id b). Qed.
Lemma ixn1 : forall j i : nat, ACtlCutP.ixn 1 [Z.of_nat j; Z.of_nat i] = i.
Proof. intros j i. exact (Nat2Z.id i). Qed.


(* The core's segment list, as ACtlCut.v binds it (its notation is Local there). *)
Local Notation segs := Reusable.YB1v.tfibsegs.

Section Ctl.

(* ACtlCut.v's Section shape (its contexts and variables, in its order), with SK and FP instantiated in the
   notation block below instead of declared (section 1).  Image B has no callee-constant Variables: its
   ACtlCutP.v keeps reac_ctrl_identity_reply_c / reac_ctrl_parse_c as qualified modules (their closures are clean
   at 23a791566db, ACtlCutP.v's CLOSURE). *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
(* The read-only span [RLO, RHI) of the lib contract lies inside the image's loaded segments: a Theorem Labs lane's shared
   form (a Theorem Labs lane 00:35Z, both images), which the stages read where a read-only byte must be an image byte.  The top at
   the B core's values discharges it by relro_img_CtrlB (section 9). *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
(* The core's two symbol records for B, as named Section hypotheses (porter 23:10Z; image A's names, a Theorem Labs lane
   8d0116e86e0): the donor's Section h takes them the same way (root YCfj.v:91-95, `Hypothesis TL : TfibLib B`;
   HB as AD2o.v:31 binds it), the stage lemmas that discharge the stage hypotheses below read them, and
   ctl_lib_x stays generic in B.  Section 9 supplies TFIB_SYMS := CtrlB_syms and TFIB_LIB := CtrlB_libS. *)
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.
Hypothesis TFIB_LIB : Reusable.YCeg.TfibLib B.

(* ---------------------------------------------------------------------------------------------------------
   1. The cut layer with its Section arguments absorbed once (the only place they appear).  After ACtlCut.v's
   End CtlCut: ctlcx / ctlcut and their fields take nothing, ctl_base takes B MT XM_LIB RLO RHI, ctl_from
   B MT XM_LIB RLO RHI FP, ctl_post B MT XN_LIB (ACtlCut.v's closing note).  The walk is instantiated HERE, once:
   - the journal's sink head SK := Reusable.YE2k.tfib_sink_head, the core's (donor root YE2k.v:44, ofl_head =
     ctrl's B ofl_head 0x5fcd48; porter 22:45Z), by NAME, so instance search never picks YL0j's global
     src0_sink_head.  It is the instance the core's tfib_lib_post_x journal is elaborated with (donor YCfn.v Imports
     YE2k, whose instance is #[export]), so the walk's journal and the post's are over the same head;
   - the freed-block list FP := [], as the donor walks (ACfj.v:208-228); the exit stage reaches the post's
     [sink_token] through ACtlCut.ajournal_fp_nil.
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
  (ACtlCut.ctl_from (SK := Reusable.YE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation ctl_post := (ACtlCut.ctl_post B MT XN_LIB).

(* The cut records of ACtlCutP.v this file names: all 90 (every one is the entry or an exit of a stage). *)
Local Notation C_ENTRY := (ACtlCutP.C_ENTRY B).
Local Notation C_B81090 := (ACtlCutP.C_B81090 B).
Local Notation C_B810c4 := (ACtlCutP.C_B810c4 B).
Local Notation C_B81220 := (ACtlCutP.C_B81220 B).
Local Notation C_B81548_at := (ACtlCutP.C_B81548_at B).
Local Notation C_B81550 := (ACtlCutP.C_B81550 B).
Local Notation C_B815fc := (ACtlCutP.C_B815fc B).
Local Notation C_B81640 := (ACtlCutP.C_B81640 B).
Local Notation C_B8168c := (ACtlCutP.C_B8168c B).
Local Notation C_B8169c := (ACtlCutP.C_B8169c B).
Local Notation C_B816ec_at := (ACtlCutP.C_B816ec_at B).
Local Notation C_B81710_at := (ACtlCutP.C_B81710_at B).
Local Notation C_B81764_at := (ACtlCutP.C_B81764_at B).
Local Notation C_B8177c_at := (ACtlCutP.C_B8177c_at B).
Local Notation C_B817a4_at := (ACtlCutP.C_B817a4_at B).
Local Notation C_B817ec_at := (ACtlCutP.C_B817ec_at B).
Local Notation C_B81834_at := (ACtlCutP.C_B81834_at B).
Local Notation C_B81860_at := (ACtlCutP.C_B81860_at B).
Local Notation C_B818a8_at := (ACtlCutP.C_B818a8_at B).
Local Notation C_B81914_at := (ACtlCutP.C_B81914_at B).
Local Notation C_B8194c_at := (ACtlCutP.C_B8194c_at B).
Local Notation C_B819a8_at := (ACtlCutP.C_B819a8_at B).
Local Notation C_B819d0_at := (ACtlCutP.C_B819d0_at B).
Local Notation C_B81a50_at := (ACtlCutP.C_B81a50_at B).
Local Notation C_B81a68_at := (ACtlCutP.C_B81a68_at B).
Local Notation C_B81aa0_at := (ACtlCutP.C_B81aa0_at B).
Local Notation C_B81ac0_at := (ACtlCutP.C_B81ac0_at B).
Local Notation C_B81c58 := (ACtlCutP.C_B81c58 B).
Local Notation C_B81c60 := (ACtlCutP.C_B81c60 B).
Local Notation C_B81ca8 := (ACtlCutP.C_B81ca8 B).
Local Notation C_B81cb0 := (ACtlCutP.C_B81cb0 B).
Local Notation C_B81d18 := (ACtlCutP.C_B81d18 B).
Local Notation C_B81d28 := (ACtlCutP.C_B81d28 B).
Local Notation C_B81d68 := (ACtlCutP.C_B81d68 B).
Local Notation C_B81d80 := (ACtlCutP.C_B81d80 B).
Local Notation C_B81da8 := (ACtlCutP.C_B81da8 B).
Local Notation C_B81dbc := (ACtlCutP.C_B81dbc B).
Local Notation C_B81dd4 := (ACtlCutP.C_B81dd4 B).
Local Notation C_B81de8 := (ACtlCutP.C_B81de8 B).
Local Notation C_B81e08 := (ACtlCutP.C_B81e08 B).
Local Notation C_B81ec4_at := (ACtlCutP.C_B81ec4_at B).
Local Notation C_B81f50_at := (ACtlCutP.C_B81f50_at B).
Local Notation C_B81f78_at := (ACtlCutP.C_B81f78_at B).
Local Notation C_B81fbc_at := (ACtlCutP.C_B81fbc_at B).
Local Notation C_B82048_at := (ACtlCutP.C_B82048_at B).
Local Notation C_B82098_at := (ACtlCutP.C_B82098_at B).
Local Notation C_B8215c_at := (ACtlCutP.C_B8215c_at B).
Local Notation C_B82174_at := (ACtlCutP.C_B82174_at B).
Local Notation C_B82180_at := (ACtlCutP.C_B82180_at B).
Local Notation C_B821ec_at := (ACtlCutP.C_B821ec_at B).
Local Notation C_B8226c_at := (ACtlCutP.C_B8226c_at B).
Local Notation C_B82304_at := (ACtlCutP.C_B82304_at B).
Local Notation C_B82308_at := (ACtlCutP.C_B82308_at B).
Local Notation C_B82340_at := (ACtlCutP.C_B82340_at B).
Local Notation C_B8235c_at := (ACtlCutP.C_B8235c_at B).
Local Notation C_B82378_at := (ACtlCutP.C_B82378_at B).
Local Notation C_B8237c_at := (ACtlCutP.C_B8237c_at B).
Local Notation C_B823d8_at := (ACtlCutP.C_B823d8_at B).
Local Notation C_B82464_at := (ACtlCutP.C_B82464_at B).
Local Notation C_B82468_at := (ACtlCutP.C_B82468_at B).
Local Notation C_B82634_at := (ACtlCutP.C_B82634_at B).
Local Notation C_B8264c_at := (ACtlCutP.C_B8264c_at B).
Local Notation C_B82668_at := (ACtlCutP.C_B82668_at B).
Local Notation C_B82728_at := (ACtlCutP.C_B82728_at B).
Local Notation C_B827f8_at := (ACtlCutP.C_B827f8_at B).
Local Notation C_B8283c_at := (ACtlCutP.C_B8283c_at B).
Local Notation C_B82844_at := (ACtlCutP.C_B82844_at B).
Local Notation C_B82878_at := (ACtlCutP.C_B82878_at B).
Local Notation C_B82888_at := (ACtlCutP.C_B82888_at B).
Local Notation C_B828a4_at := (ACtlCutP.C_B828a4_at B).
Local Notation C_B828b4_at := (ACtlCutP.C_B828b4_at B).
Local Notation C_B8292c_at := (ACtlCutP.C_B8292c_at B).
Local Notation C_B82aa4_at := (ACtlCutP.C_B82aa4_at B).
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
Local Notation C_B82d1c_at := (ACtlCutP.C_B82d1c_at B).
Local Notation C_B82eac := (ACtlCutP.C_B82eac B).
Local Notation C_B82ecc := (ACtlCutP.C_B82ecc B).
Local Notation C_Jrel := (ACtlCutP.C_Jrel B).
Local Notation C_B82f48 := (ACtlCutP.C_B82f48 B).
Local Notation C_B82f5c := (ACtlCutP.C_B82f5c B).

(* ---------------------------------------------------------------------------------------------------------
   2. A cut at ONE index is ACtlCut.v's ix_cut (with ctl_from_ix; the same name and statement as image A's):
   ctl_from quantifies the index list idx, so `ctl_from POST X` holds at every index at once (ctrl's
   `forall b, Hat .. b`), and `ctl_from POST (ix_cut X i0)` is ctrl's `Hat .. i0`.  The index shapes of ACtlCut.v
   section 3: [Z.of_nat b] / [Z.of_nat j], [Z.of_nat j; Z.of_nat i] for the row cuts, [t] as Z for B81548_at
   (whose body reads it with ixz). *)

(* The exit post the top consumes: ACtlCut.v's ctl_post with its leaf fixed to the one fuzz_ctrl's tree takes
   (departure 1; the donor's leaf, ACfj.v:186).  The post is the core's tfib_lib_post_x, applied as the donor
   applies it (ACfj.v:238: B MT XN_LIB, then the entry arguments). *)
Definition ctl_post_leaf (cx : ctlcx) : Reusable.YA0n.world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k,
    c' = Reusable.YG0d.cfg_at segs Reusable.YCfn.RA_LLVMF regs' mem' md' /\
    Reusable.YCfn.tfib_lib_post_x B MT XN_LIB
      (ACtlCut.c_regs cx) (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
      (c_mem cx) (c_md cx) (ACtlCut.c_p cx) (ACtlCut.c_n cx) (ACtlCut.c_M cx)
      (lib.Reusable.YO09.LL 0 (m_fs (c_md cx)) [])
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

(* A cut whose body never holds is reached by nothing: the base of every loop (ctrl's vac_*, Slot.v:381-397). *)
Lemma ctl_from_vac : forall POST (X : ctlcut),
  (forall cx idx bl fr regs m, ~ cut_body X cx idx bl fr fr regs m) -> CF POST X.
Proof.
  intros POST X HV cx idx fr k ly3 S3 W3 regs3 mem3 md3 _ _ _ _ _ Hb _.
  exfalso. exact (HV _ _ _ _ _ _ Hb).
Qed.

(* The vacuous heads past the last turn.  Bounds from ctrl's own bodies: RB `b <= 6` (inside RS of C_B816ec_at),
   LI `j <= 255` (C_B81ec4_at), RL `i <= 10` (C_B82bf4_at); ctrl's vac_B81688 / vac_B81e54 / vac_B82b90,
   Slot.v:381-397 (patched-image names of the same cuts). *)
Lemma vac_B816ec : forall POST b, (6 < b)%nat -> CF POST (ix_cut C_B816ec_at [Z.of_nat b]).
Proof.
  intros POST b Hb. apply ctl_from_vac. intros cx idx bl fr regs m H.
  cbv beta iota zeta delta [ACtlCut.ix_cut ACtlCut.cut_body ACtlCutP.C_B816ec_at ACtlCutP.RS ACtlCutP.RB] in H.
  vac_split. subst idx.
  match goal with Hr : (ACtlCutP.ixn 0 _ <= 6)%nat |- _ => rewrite ixn0 in Hr; clear - Hb Hr; lia end.
Qed.

Lemma vac_B81ec4 : forall POST j, (255 < j)%nat -> CF POST (ix_cut C_B81ec4_at [Z.of_nat j]).
Proof.
  intros POST j Hj. apply ctl_from_vac. intros cx idx bl fr regs m H.
  cbv beta iota zeta delta [ACtlCut.ix_cut ACtlCut.cut_body ACtlCutP.C_B81ec4_at ACtlCutP.LI] in H.
  vac_split. subst idx.
  match goal with Hr : (ACtlCutP.ixn 0 _ <= 255)%nat |- _ => rewrite ixn0 in Hr; clear - Hj Hr; lia end.
Qed.

Lemma vac_B82bf4 : forall POST j i, (10 < i)%nat -> CF POST (ix_cut C_B82bf4_at [Z.of_nat j; Z.of_nat i]).
Proof.
  intros POST j i Hi. apply ctl_from_vac. intros cx idx bl fr regs m H.
  cbv beta iota zeta delta [ACtlCut.ix_cut ACtlCut.cut_body ACtlCutP.C_B82bf4_at ACtlCutP.RL] in H.
  vac_split. subst idx.
  match goal with Hr : (ACtlCutP.ixn 1 _ <= 10)%nat |- _ => rewrite ixn1 in Hr; clear - Hi Hr; lia end.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   4. The non-stage hypotheses of the walk (RELRO_IMG, TFIB_SYMS and TFIB_LIB are declared with the Variables
   above). *)

(* The lib shape's tree is one leaf: LIBK pl fs K = K (LL 0 fs []).  ACtlCut.v abstracts the shape
   ({LS : ...} in its Section), and the contract's goal is stated through LIBK, so the top needs this fact about
   LS.  It holds by reflexivity at fuzz_ctrl's image-B shape ag_shape checksum_shape (lib/B/CtrlTFIB_B.v:23;
   lib/AgreeShape.v:9-10 copies LIBK; lib/B/ZTraceSpec.v:14-20 defines it, transparent).  Discharged where LS is
   instantiated. *)
Hypothesis LS_LEAF : forall pl fs K, @lib.Reusable.YO09.LIBK LS pl fs K = K (lib.Reusable.YO09.LL 0 fs []).

(* The carried ctrl runtime facts at the entry, in route (C)'s narrowed form (11:15Z; a Theorem Labs lane's truth audit found the
   full ctl_rt form false at an AR state): ctl_rt_C at the entry state.  Proved from the entry's AR and arodata_okS
   by a Theorem Labs lane's B.ProgWorldCtlRtC.ctl_rt_C_of_AR (CtrlTSyms + AR_laws only; no AR_states_vis0_shadow, no
   AR_states_owned_ro), in lib/B/ACtlTopFacts.v. *)
Hypothesis CTLRT_ENTRY : forall cx : ctlcx, CB cx ->
  B.ACtlRtC.ctl_rt_C B (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (c_mem cx).

(* The frame-pointer chain and the call trace at an allocator call (ACtlCut.v section 1b): at every owning cut the
   caller-side facts give a chain_pre of the caller's chain and its call trace in the core's universe, at the four
   allocator sites of the walk -- malloc / free of the round trip (returns 0x81764 / 0x81aa0, the cuts B81764_at /
   B81aa0_at) and of the frame loop (0x81f50 / 0x82d1c, B81f50_at / B82d1c_at).  The saved-register bytes are
   FRAC's (ACtlCutP.v's saved_bytes, ctrl's SlotInv.v:275-279, written out); s0 = S and the spill-base window
   (S - 4096 < sp, sp + 448 <= S) are FRAC's too.  Statement: a Theorem Labs lane's HCHAIN (lib/B/ACtlW2a.v section 2,
   ffb9cb21497), over the walk's journal (sink head and FP as in CF, FP quantified).  A HYPOTHESIS, not a lemma:
   its proof needs the entry chain of the core's afn_pre, the journal's kept view above S and the bridge from
   lib/Lib's bytes_at to the core's aview (a Theorem Labs lane's lib/B/ProgBridge.v / lib/B/ProgWorld.v). *)
Hypothesis CHAIN_OF_CUT : forall (FP : list (Z * Z)) (cx : ctlcx) own ly3 S3 W3 mem3 md3 k (regsT : bvmap 5 word)
    (pc0 ra : Z),
  CB cx ->
  Reusable.YCbq.ajournal (SK := Reusable.YE2k.tfib_sink_head) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 k ->
  lib.Reusable.YK11.getr regsT 8 = Z_to_bv 64 (ACtlCut.c_sp cx) ->
  lib.Reusable.YK11.getr regsT 1 = Z_to_bv 64 ra ->
  lib.Lib.Mem.bytes_at segs mem3 (ACtlCut.c_sp cx - 104)
    (lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 27) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 26) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 25) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 24) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 23) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 22) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 21) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 20) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 19) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 18) ++
     lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 9) ++ lib.Lib.Mem.le8 (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 8) ++
     lib.Lib.Mem.le8 (Z_to_bv 64 Reusable.YCfn.RA_LLVMF)) ->
  ACtlCut.c_sp cx - 4096 < Reusable.YG0d.spZ regsT -> Reusable.YG0d.spZ regsT + 448 <= ACtlCut.c_sp cx ->
  In (pc0, ra) [(Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81764);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x81aa0);
                (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81f50);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x82d1c)] ->
  exists ch, ACtlCut.ctl_chain ly3 W3 mem3 regsT ch /\ ACtlCut.ctl_trace_in B pc0 regsT ch.

(* ---------------------------------------------------------------------------------------------------------
   5. The stage hypotheses, one per live segment of plan section 2.3, grouped by W piece in section 5's order.
   Each is ctrl's S_ form (Slot.v:48-259) over the cut records; a loop-carried exit gives the next turn's index;
   the two-entry segment F32 concludes both entries, as ctrl's S_F32 does (Slot.v:221-223).  The stage files keep
   the record names; POST is quantified, the exit stage seg_Y3 alone fixes it. *)

(* ===== W0 prologue: ENTRY -> B81220 (A1, A2, A3) ===== *)
(* glue: Seg/A1.v seg_A1 :687 @UB via _F; runs a1_pro :397 *)
(* 06:31Z: the entry stage concludes only for posts that do not read c_fpos (premise on POST; ACtlCut.cx_set_fpos): the allocator
   at 0x8108c picks the frame position (found by a Theorem Labs lane; the donor's entry segment has `exists fpos`). *)
Hypothesis seg_A1 : forall POST, (forall cx p, POST (ACtlCut.cx_set_fpos cx p) = POST cx) ->
  CF POST C_B81090 -> CF POST C_B810c4 -> CF POST C_ENTRY.
(* glue: Seg/A2.v seg_A2 :344 @UB via _F; runs a2_side_evt :112, a2_real_evt :132 *)
Hypothesis seg_A2 : forall POST, CF POST C_B810c4 -> CF POST C_B81090.
(* glue: Seg/A3.v seg_A3 :778 @UB via _F; runs a3_lib_evt :93, a3_evt_mid :286, a3_evt :428 *)
Hypothesis seg_A3 : forall POST, CF POST C_B81220 -> CF POST C_B810c4.

(* ===== W1 pre-loop: B81220 -> B816ec_at 0, B81cb0, Jrel (A4, A5, R1-R5) ===== *)
(* glue: Seg/A4.v seg_A4 :739 @UB via _F; runs a4_evt :128 *)
Hypothesis seg_A4 : forall POST, CF POST (ix_cut C_B81548_at [0]) -> CF POST C_Jrel -> CF POST C_B81220.
(* glue: Seg/A5.v seg_A5 :2436 @EB via _F (WIP / iteration-only, build not checked); runs b_ld_evt :156, b_hd_ld_evt :226, b_z_evt :259, b_tail_evt :304, b_mode_evt :379, b_cat_evt :456 *)
Hypothesis seg_A5 : forall POST (t : Z),
  CF POST C_B81550 -> CF POST C_B815fc -> CF POST C_B81cb0 -> CF POST (ix_cut C_B81548_at [t]).
(* glue: Seg/R1.v seg_R1 :38 @EB via _F (WIP / iteration-only, build not checked); runs none stated; EB A5.v `b_turn_gen`:1460, `b_loop`:2423 *)
Hypothesis seg_R1 : forall POST, CF POST C_B815fc -> CF POST C_B81cb0 -> CF POST C_B81550.
(* glue: Seg/R2.v seg_R2 :995 @EB via _F (WIP / iteration-only, build not checked); runs r2_evt :199 *)
Hypothesis seg_R2 : forall POST, CF POST C_B81640 -> CF POST C_B815fc.
(* glue: Seg/R3.v seg_R3 :714 @UB via _F; runs r3_evt :229 *)
Hypothesis seg_R3 : forall POST, CF POST C_B8168c -> CF POST C_B81640.
(* glue: Seg/R4.v seg_R4 :682 @UB via _F; runs r4_evt :102 *)
Hypothesis seg_R4 : forall POST, CF POST C_B8169c -> CF POST C_B8168c.
(* glue: Seg/R5.v seg_R5 :606 @UB via _F; runs r5_evt :248 *)
Hypothesis seg_R5 : forall POST, CF POST (ix_cut C_B816ec_at [Z.of_nat 0]) -> CF POST C_B8169c.

(* ===== W2 round trip, turn b: B816ec_at b -> B816ec_at (S b), B81c58, B81c60, B81ca8 (R6-R21, R21_a5c) ===== *)
(* glue: Seg/R6.v seg_R6 :1165 @UB via _F; runs none stated; inline under `r6_run :647` *)
Hypothesis seg_R6 : forall POST (b : nat),
  CF POST (ix_cut C_B81710_at [Z.of_nat b]) -> CF POST (ix_cut C_B816ec_at [Z.of_nat b]).
(* glue: Seg/R7.v seg_R7 :790 @UB via _F; runs r7_evt :144, r7_evt0 :165 *)
Hypothesis seg_R7 : forall POST (b : nat),
  CF POST (ix_cut C_B81764_at [Z.of_nat b]) -> CF POST (ix_cut C_B81ac0_at [Z.of_nat b]) ->
  CF POST (ix_cut C_B81710_at [Z.of_nat b]).
(* glue: Seg/R8.v seg_R8 :783 @UB via _F; runs r8_evt :59 *)
Hypothesis seg_R8 : forall POST (b : nat),
  CF POST (ix_cut C_B8177c_at [Z.of_nat b]) -> CF POST (ix_cut C_B81764_at [Z.of_nat b]).
(* glue: Seg/R9.v seg_R9 :919 @UB via _F; runs r9_st :74, r9_call :107 *)
Hypothesis seg_R9 : forall POST (b : nat),
  CF POST (ix_cut C_B817a4_at [Z.of_nat b]) -> CF POST (ix_cut C_B8177c_at [Z.of_nat b]).
(* glue: Seg/R10.v seg_R10 :4381 @UB via _F; runs r10_cfg0 :134, r10_sum12 :196, r10_head_reply :252, r10_head_frag6 :301, r10_head_frag5 :351, r10_reply_call :401 *)
Hypothesis seg_R10 : forall POST (b : nat),
  CF POST (ix_cut C_B817ec_at [Z.of_nat b]) -> CF POST (ix_cut C_B81834_at [Z.of_nat b]) ->
  CF POST (ix_cut C_B818a8_at [Z.of_nat b]) -> CF POST (ix_cut C_B81914_at [Z.of_nat b]) ->
  CF POST (ix_cut C_B8194c_at [Z.of_nat b]) -> CF POST (ix_cut C_B817a4_at [Z.of_nat b]).
(* glue: Seg/R11.v seg_R11 :423 @UB via _F; runs r11_evt :105 *)
Hypothesis seg_R11 : forall POST (b : nat),
  CF POST (ix_cut C_B81860_at [Z.of_nat b]) -> CF POST (ix_cut C_B817ec_at [Z.of_nat b]).
(* glue: Seg/R12.v seg_R12 :340 @UB via _F; runs r12_evt :132 *)
Hypothesis seg_R12 : forall POST (b : nat),
  CF POST (ix_cut C_B81860_at [Z.of_nat b]) -> CF POST (ix_cut C_B81834_at [Z.of_nat b]).
(* glue: Seg/R13.v seg_R13 :460 @UB via _F; runs r13_evt :84 *)
Hypothesis seg_R13 : forall POST (b : nat),
  CF POST (ix_cut C_B81aa0_at [Z.of_nat b]) -> CF POST (ix_cut C_B81860_at [Z.of_nat b]).
(* glue: Seg/R14.v seg_R14 :1256 @UB via _F; runs r14_loop :621, r14_evt :703 *)
Hypothesis seg_R14 : forall POST (b : nat),
  CF POST (ix_cut C_B819a8_at [Z.of_nat b]) -> CF POST (ix_cut C_B818a8_at [Z.of_nat b]).
(* glue: Seg/R15.v seg_R15 :456 @UB via _F; runs r15_evt :80 *)
Hypothesis seg_R15 : forall POST (b : nat),
  CF POST (ix_cut C_B81aa0_at [Z.of_nat b]) -> CF POST (ix_cut C_B81914_at [Z.of_nat b]).
(* glue: Seg/R16.v seg_R16 :735 @UB via _F; runs r16_loop_ind :84, r16_evt :150 *)
Hypothesis seg_R16 : forall POST (b : nat),
  CF POST (ix_cut C_B81aa0_at [Z.of_nat b]) -> CF POST (ix_cut C_B8194c_at [Z.of_nat b]).
(* glue: Seg/R17.v seg_R17 :149 @UB via _F; runs r17_evt :60 *)
Hypothesis seg_R17 : forall POST (b : nat),
  CF POST (ix_cut C_B819d0_at [Z.of_nat b]) -> CF POST (ix_cut C_B819a8_at [Z.of_nat b]).
(* glue: Seg/R18.v seg_R18 :259 @UB via _F; runs r18_evt :115 *)
Hypothesis seg_R18 : forall POST (b : nat),
  CF POST (ix_cut C_B81a50_at [Z.of_nat b]) -> CF POST (ix_cut C_B819d0_at [Z.of_nat b]).
(* glue: Seg/R19.v seg_R19 :257 @UB via _F; runs r19_evt_n :93, r19_evt :157 *)
Hypothesis seg_R19 : forall POST (b : nat),
  CF POST (ix_cut C_B81a68_at [Z.of_nat b]) -> CF POST (ix_cut C_B81a50_at [Z.of_nat b]).
(* glue: Seg/R20.v seg_R20 :246 @UB via _F; runs r20_evt :194 *)
Hypothesis seg_R20 : forall POST (b : nat),
  CF POST (ix_cut C_B81aa0_at [Z.of_nat b]) -> CF POST (ix_cut C_B81a68_at [Z.of_nat b]).
(* glue: Seg/R21.v seg_R21 :661 @UB via _F; runs r21_latch_next :221, r21_latch_last :253, r21_p1_evt_n :475, r21_p1_evt :557 *)
Hypothesis seg_R21 : forall POST (b : nat),
  CF POST (ix_cut C_B816ec_at [Z.of_nat (S b)]) -> CF POST C_B81c58 -> CF POST C_B81ca8 ->
  CF POST (ix_cut C_B81aa0_at [Z.of_nat b]).
(* glue: Seg/R21.v seg_R21_a5c :1206 @UB via _F; runs r21_a5c_next :284, r21_a5c_last :307 *)
Hypothesis seg_R21_a5c : forall POST (b : nat),
  CF POST (ix_cut C_B816ec_at [Z.of_nat (S b)]) -> CF POST C_B81c58 -> CF POST C_B81c60 ->
  CF POST (ix_cut C_B81ac0_at [Z.of_nat b]).

(* ===== W3 between loops: B81c58 / B81c60 / B81ca8 / B81cb0 -> B81ec4_at 0, B82eac (P1, P1_bfc, P2-P12) ===== *)
(* glue: Seg/P1.v seg_P1 :399 @UB via _F; runs p1_evt_bfc :35, p1_evt :136, p1_evt_pc :165 *)
Hypothesis seg_P1 : forall POST, CF POST C_B81ca8 -> CF POST C_B81c58.
(* glue: Seg/P1.v seg_P1_bfc :410 @UB via _F; runs p1_evt_bfc :35, p1_evt :136, p1_evt_pc :165 *)
Hypothesis seg_P1_bfc : forall POST, CF POST C_B81ca8 -> CF POST C_B81c60.
(* glue: Seg/P2.v seg_P2 :90 @UB via _F; runs p2_evt :26 *)
Hypothesis seg_P2 : forall POST, CF POST C_B81cb0 -> CF POST C_B81ca8.
(* glue: Seg/P3.v seg_P3 :268 @UB via _F; runs p3_evt :41 *)
Hypothesis seg_P3 : forall POST, CF POST C_B81d18 -> CF POST C_B81cb0.
(* glue: Seg/P4.v seg_P4 :128 @UB via _F; runs p4_evt :34 *)
Hypothesis seg_P4 : forall POST, CF POST C_B81d28 -> CF POST C_B81d18.
(* glue: Seg/P5.v seg_P5 :216 @UB via _F; runs p5_evt :38 *)
Hypothesis seg_P5 : forall POST, CF POST C_B81d68 -> CF POST C_B81d28.
(* glue: Seg/P6.v seg_P6 :237 @UB via _F; runs p6_evt :97 *)
Hypothesis seg_P6 : forall POST, CF POST C_B81d80 -> CF POST C_B81d68.
(* glue: Seg/P7.v seg_P7 :124 @UB via _F; runs p7_evt :33 *)
Hypothesis seg_P7 : forall POST, CF POST C_B81da8 -> CF POST C_B81d80.
(* glue: Seg/P8.v seg_P8 :101 @UB via _F; runs p8_evt :30 *)
Hypothesis seg_P8 : forall POST, CF POST C_B81dbc -> CF POST C_B81da8.
(* glue: Seg/P9.v seg_P9 :98 @UB via _F; runs p9_evt :29 *)
Hypothesis seg_P9 : forall POST, CF POST C_B81dd4 -> CF POST C_B81dbc.
(* glue: Seg/P10.v seg_P10 :108 @UB via _F; runs p10_evt :30 *)
Hypothesis seg_P10 : forall POST, CF POST C_B81de8 -> CF POST C_B81dd4.
(* glue: Seg/P11.v seg_P11 :184 @UB via _F; runs p11_evt :36 *)
Hypothesis seg_P11 : forall POST, CF POST C_B81e08 -> CF POST C_B81de8.
(* glue: Seg/P12.v seg_P12 :321 @UB via _F; runs p12_ck1 :143, p12_ck2 :167, p12_chk :192, p12_body :225 *)
Hypothesis seg_P12 : forall POST, CF POST (ix_cut C_B81ec4_at [Z.of_nat 0]) -> CF POST C_B82eac -> CF POST C_B81e08.

(* ===== W4 frame turn j: B81ec4_at j -> B81ec4_at (S j), B82eac (F1-F38, rows inside) ===== *)
(* ----- W4a: F1-F6 ----- *)
(* glue: Seg/F1.v seg_F1 :1530 @UB via _F; runs f1_body :149, f1_tail2 :207, f1_tail1 :240, f1_evt :294 *)
Hypothesis seg_F1 : forall POST (j : nat),
  CF POST (ix_cut C_B81f50_at [Z.of_nat j]) -> CF POST C_B82eac -> CF POST (ix_cut C_B81ec4_at [Z.of_nat j]).
(* glue: Seg/F2.v seg_F2 :2580 @UB via _F; runs f2_head0 :80, f2_head1 :109, f2_st :142, f2_parse_at :174, f2_pcall :286, f2_mcpy_evt :346 *)
Hypothesis seg_F2 : forall POST (j : nat),
  CF POST (ix_cut C_B81f78_at [Z.of_nat j]) -> CF POST (ix_cut C_B82048_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B81f50_at [Z.of_nat j]).
(* glue: Seg/F3.v seg_F3 :108 @UB via _F; runs f3_head :26 *)
Hypothesis seg_F3 : forall POST (j : nat),
  CF POST (ix_cut C_B81fbc_at [Z.of_nat j]) -> CF POST (ix_cut C_B82048_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B81f78_at [Z.of_nat j]).
(* glue: Seg/F4.v seg_F4 :183 @UB via _F; runs none in file; inline under F5.v `c_run_lib`:891 *)
Hypothesis seg_F4 : forall POST (j : nat),
  CF POST (ix_cut C_B82098_at [Z.of_nat j]) -> CF POST (ix_cut C_B81fbc_at [Z.of_nat j]).
(* glue: Seg/F5.v seg_F5 :2020 @UB via _F; runs c_evt :797 *)
Hypothesis seg_F5 : forall POST (j : nat),
  CF POST (ix_cut C_B8215c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82048_at [Z.of_nat j]).
(* glue: Seg/F6.v seg_F6 :729 @UB via _F; runs f6_loop :210, f6_run_evt :301 *)
Hypothesis seg_F6 : forall POST (j : nat),
  CF POST (ix_cut C_B8215c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82098_at [Z.of_nat j]).
(* ----- W4b: F7-F12_298 ----- *)
(* glue: Seg/F7.v seg_F7 :419 @UB via _F; runs f7_evt :353 *)
Hypothesis seg_F7 : forall POST (j : nat),
  CF POST (ix_cut C_B82174_at [Z.of_nat j]) -> CF POST (ix_cut C_B8215c_at [Z.of_nat j]).
(* glue: Seg/F8.v seg_F8 :352 @UB via _F; runs f8_evt :301 *)
Hypothesis seg_F8 : forall POST (j : nat),
  CF POST (ix_cut C_B82180_at [Z.of_nat j]) -> CF POST (ix_cut C_B82174_at [Z.of_nat j]).
(* glue: Seg/F9.v seg_F9 :3462 @UB via _F; runs f9_evtA :297, f9_evtB_n :552, f9_evtB :786 *)
Hypothesis seg_F9 : forall POST (j : nat),
  CF POST (ix_cut C_B821ec_at [Z.of_nat j]) -> CF POST (ix_cut C_B82180_at [Z.of_nat j]).
(* glue: Seg/F10.v seg_F10 :189 @UB via _F; runs none stated; stepped inline under Tac_slot.v `sl_run`:156 *)
Hypothesis seg_F10 : forall POST (j : nat),
  CF POST (ix_cut C_B8226c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82308_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B821ec_at [Z.of_nat j]).
(* glue: Seg/F11.v seg_F11 :659 @UB via _F; runs f11_lu_evt :93 *)
Hypothesis seg_F11 : forall POST (j : nat),
  CF POST (ix_cut C_B82304_at [Z.of_nat j]) -> CF POST (ix_cut C_B8226c_at [Z.of_nat j]).
(* glue: Seg/F12.v seg_F12 :1907 @UB via _F; runs f12_evt :633 *)
Hypothesis seg_F12 : forall POST (j : nat),
  CF POST (ix_cut C_B82340_at [Z.of_nat j]) -> CF POST (ix_cut C_B82304_at [Z.of_nat j]).
(* glue: Seg/F12.v seg_F12_298 :1919 @UB via _F; runs f12_evt :633 *)
Hypothesis seg_F12_298 : forall POST (j : nat),
  CF POST (ix_cut C_B82340_at [Z.of_nat j]) -> CF POST (ix_cut C_B82308_at [Z.of_nat j]).
(* ----- W4c: F13-F17, F15b ----- *)
(* glue: Seg/F13.v seg_F13 :1310 @UB via _F; runs f13_evt_n :1109, f13_evt :1178 *)
Hypothesis seg_F13 : forall POST (j : nat),
  CF POST (ix_cut C_B8235c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82340_at [Z.of_nat j]).
(* glue: Seg/F14.v seg_F14 :467 @UB via _F; runs f14_evt_10 :234, f14_evt_0c_n :263, f14_evt_0c :361 *)
Hypothesis seg_F14 : forall POST (j : nat),
  CF POST (ix_cut C_B8237c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82378_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B8235c_at [Z.of_nat j]).
(* glue: Seg/F15.v seg_F15 :687 @UB via _F; runs none stated; stepped inline under Tac_slot.v `sl_run`:156 *)
Hypothesis seg_F15 : forall POST (j : nat),
  CF POST (ix_cut C_B8237c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82378_at [Z.of_nat j]).
(* glue: Seg/F15.v seg_F15b :766 @UB via _F; runs none stated; stepped inline under Tac_slot.v `sl_run`:156 *)
Hypothesis seg_F15b : forall POST (j : nat),
  CF POST (ix_cut C_B823d8_at [Z.of_nat j]) -> CF POST (ix_cut C_B82468_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B8237c_at [Z.of_nat j]).
(* glue: Seg/F16.v seg_F16 :1138 @UB via _F; runs none stated; inline under `f16_run_lib :957` *)
Hypothesis seg_F16 : forall POST (j : nat),
  CF POST (ix_cut C_B82464_at [Z.of_nat j]) -> CF POST (ix_cut C_B823d8_at [Z.of_nat j]).
(* glue: Seg/F17.v seg_F17 :91 @UB via _F; runs none stated; stepped inline under Tac_slot.v `sl_run`:156 *)
Hypothesis seg_F17 : forall POST (j : nat),
  CF POST (ix_cut C_B82468_at [Z.of_nat j]) -> CF POST (ix_cut C_B82464_at [Z.of_nat j]).
(* ----- W4d: F17b ----- *)
(* glue: Seg/F17b.v seg_F17b :706 @UB via _F; runs f17_lu_evt :76 + Tac_f17b.v f17_mc :205 *)
Hypothesis seg_F17b : forall POST (j : nat),
  CF POST (ix_cut C_B82634_at [Z.of_nat j]) -> CF POST (ix_cut C_B82468_at [Z.of_nat j]).
(* ----- W4e: F18-F29, F22t ----- *)
(* glue: Seg/F18.v seg_F18 :786 @UB via _F; runs f18_evt :342, f18_evt_skip :439 *)
Hypothesis seg_F18 : forall POST (j : nat),
  CF POST (ix_cut C_B8264c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82abc_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B82634_at [Z.of_nat j]).
(* glue: Seg/F19.v seg_F19 :212 @UB via _F; runs f19_evt :108 *)
Hypothesis seg_F19 : forall POST (j : nat),
  CF POST (ix_cut C_B82668_at [Z.of_nat j]) -> CF POST (ix_cut C_B8264c_at [Z.of_nat j]).
(* glue: Seg/F20.v seg_F20 :477 @UB via _F; runs lu_evt :64 *)
Hypothesis seg_F20 : forall POST (j : nat),
  CF POST (ix_cut C_B82728_at [Z.of_nat j]) -> CF POST (ix_cut C_B82668_at [Z.of_nat j]).
(* glue: Seg/F21.v seg_F21 :560 @UB via _F; runs lu_evt :66 *)
Hypothesis seg_F21 : forall POST (j : nat),
  CF POST (ix_cut C_B827f8_at [Z.of_nat j]) -> CF POST (ix_cut C_B82844_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B82728_at [Z.of_nat j]).
(* glue: Seg/F22.v seg_F22 :460 @UB via _F; runs f22_loop :218 *)
Hypothesis seg_F22 : forall POST (j : nat),
  CF POST (ix_cut C_B8283c_at [Z.of_nat j]) -> CF POST (ix_cut C_B827f8_at [Z.of_nat j]).
(* glue: Seg/F22.v seg_F22t :558 @UB via _F; runs f22_lu_evt :64 *)
Hypothesis seg_F22t : forall POST (j : nat),
  CF POST (ix_cut C_B82844_at [Z.of_nat j]) -> CF POST (ix_cut C_B8283c_at [Z.of_nat j]).
(* glue: Seg/F23.v seg_F23 :513 @UB via _F; runs f23_evt :297 *)
Hypothesis seg_F23 : forall POST (j : nat),
  CF POST (ix_cut C_B82878_at [Z.of_nat j]) -> CF POST (ix_cut C_B82844_at [Z.of_nat j]).
(* glue: Seg/F24.v seg_F24 :182 @UB via _F; runs f24_evt :99 *)
Hypothesis seg_F24 : forall POST (j : nat),
  CF POST (ix_cut C_B82888_at [Z.of_nat j]) -> CF POST (ix_cut C_B82878_at [Z.of_nat j]).
(* glue: Seg/F25.v seg_F25 :280 @UB via _F; runs f25_evt :125 *)
Hypothesis seg_F25 : forall POST (j : nat),
  CF POST (ix_cut C_B828a4_at [Z.of_nat j]) -> CF POST (ix_cut C_B82888_at [Z.of_nat j]).
(* glue: Seg/F26.v seg_F26 :402 @UB via _F; runs f26_lu_evt :62 *)
Hypothesis seg_F26 : forall POST (j : nat),
  CF POST (ix_cut C_B828b4_at [Z.of_nat j]) -> CF POST (ix_cut C_B828a4_at [Z.of_nat j]).
(* glue: Seg/F27.v seg_F27 :309 @UB via _F; runs none stated; stepped inline under Tac_slot.v `sl_run`:156 *)
Hypothesis seg_F27 : forall POST (j : nat),
  CF POST (ix_cut C_B8292c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82aa4_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B828b4_at [Z.of_nat j]).
(* glue: Seg/F28.v seg_F28 :772 @UB via _F; runs f28_loop :560, f28_tail :686 *)
Hypothesis seg_F28 : forall POST (j : nat),
  CF POST (ix_cut C_B82aa4_at [Z.of_nat j]) -> CF POST (ix_cut C_B8292c_at [Z.of_nat j]).
(* glue: Seg/F29.v seg_F29 :426 @UB via _F; runs f29_evt :145, f29_evt_ro :208 *)
Hypothesis seg_F29 : forall POST (j : nat),
  CF POST (ix_cut C_B82abc_at [Z.of_nat j]) -> CF POST (ix_cut C_B82aa4_at [Z.of_nat j]).
(* ----- W4f: F30-F36_c2c and the rows ----- *)
(* glue: Seg/F30.v seg_F30 :1762 @UB via _F; runs f30s_evt :356, f30s_evt_ro :585, f30_cl_ro :709 *)
Hypothesis seg_F30 : forall POST (j : nat),
  CF POST (ix_cut C_B82af8_at [Z.of_nat j]) -> CF POST (ix_cut C_B82abc_at [Z.of_nat j]).
(* glue: Seg/F31.v seg_F31 :587 @UB via _F; runs f31n_evt :170, f31c_evt :206, f31c_evt_ro :322 *)
Hypothesis seg_F31 : forall POST (j : nat),
  CF POST (ix_cut C_B82b38_at [Z.of_nat j]) -> CF POST (ix_cut C_B82b5c_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B82af8_at [Z.of_nat j]).
(* glue: Seg/F32.v seg_F32 :1890 @UB via _F; runs f32e_evt :326, f32n_evt :364, f32m1_evt :382, f32m2_evt :419, f32c_evt :506 *)
Hypothesis seg_F32 : forall POST (j : nat),
  CF POST (ix_cut C_B82bcc_at [Z.of_nat j]) -> CF POST (ix_cut C_B82c90_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B82b38_at [Z.of_nat j]) /\ CF POST (ix_cut C_B82b5c_at [Z.of_nat j]).
(* glue: Seg/F33.v seg_F33 :137 @UB via _F; runs f33_evt :69 *)
Hypothesis seg_F33 : forall POST (j : nat),
  CF POST (ix_cut C_B82bf4_at [Z.of_nat j; Z.of_nat 0]) -> CF POST (ix_cut C_B82c84_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B82bcc_at [Z.of_nat j]).
(* glue: Seg/F34.v seg_F34 :1055 @UB via _F; runs f34_evt :288, f34_evt_ro :583 *)
Hypothesis seg_F34 : forall POST (j i : nat),
  CF POST (ix_cut C_B82c24_at [Z.of_nat j; Z.of_nat i]) -> CF POST (ix_cut C_B82bf4_at [Z.of_nat j; Z.of_nat i]).
(* glue: Seg/F35.v seg_F35 :543 @UB via _F; runs f35_evt :187, f35_evt_ro :279 *)
Hypothesis seg_F35 : forall POST (j i : nat),
  CF POST (ix_cut C_B82bf4_at [Z.of_nat j; Z.of_nat (S i)]) ->
  CF POST (ix_cut C_B82c38_at [Z.of_nat j; Z.of_nat i]) -> CF POST (ix_cut C_B82ca0_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B82c24_at [Z.of_nat j; Z.of_nat i]).
(* glue: Seg/F36.v seg_F36 :929 @UB via _F; runs none in file; Tac_f36.v f36_run_lib :879, f36_evt_call_ro :1800, f36_evt_pre :1974, f36_evt_hit :2015, f36_evt_next :2038, f36_evt_last :2065, f36_evt_c24 :2089 *)
Hypothesis seg_F36 : forall POST (j i : nat),
  CF POST (ix_cut C_B82bf4_at [Z.of_nat j; Z.of_nat (S i)]) -> CF POST (ix_cut C_B82ca0_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B82c38_at [Z.of_nat j; Z.of_nat i]).
(* glue: Seg/F36.v seg_F36_c20 :863 @UB via _F; runs none in file; Tac_f36.v f36_run_lib :879, f36_evt_call_ro :1800, f36_evt_c24 :2089, f36_evt_c20 :2121 *)
Hypothesis seg_F36_c20 : forall POST (j : nat),
  CF POST (ix_cut C_B82ca0_at [Z.of_nat j]) -> CF POST (ix_cut C_B82c84_at [Z.of_nat j]).
(* glue: Seg/F36.v seg_F36_c2c :719 @UB via _F; runs none in file; Tac_f36.v f36_run_lib :879, f36_evt_call_ro :1800, f36_evt_c2c :2110 *)
Hypothesis seg_F36_c2c : forall POST (j : nat),
  CF POST (ix_cut C_B82ca0_at [Z.of_nat j]) -> CF POST (ix_cut C_B82c90_at [Z.of_nat j]).
(* ----- W4g: F37-F38 ----- *)
(* glue: Seg/F37.v seg_F37 :762 @UB via _F; runs f37_evt :292 *)
Hypothesis seg_F37 : forall POST (j : nat),
  CF POST (ix_cut C_B82d1c_at [Z.of_nat j]) -> CF POST (ix_cut C_B82ca0_at [Z.of_nat j]).
(* glue: Seg/F38.v seg_F38 :153 @UB via _F; runs none stated; stepped inline under Tac_slot.v `sl_run`:156 *)
Hypothesis seg_F38 : forall POST (j : nat),
  CF POST (ix_cut C_B81ec4_at [Z.of_nat (S j)]) -> CF POST C_B82eac -> CF POST (ix_cut C_B82d1c_at [Z.of_nat j]).

(* ===== W5 tail: B82eac -> Post (X1, X2, Jrel, Y1, Y3) ===== *)
(* glue: Seg/X12.v seg_X1 :858 @UB via _F; runs x12_store_evt :303, x12_b_evt :360, x12_a_evt :393 *)
Hypothesis seg_X1 : forall POST, CF POST C_B82ecc -> CF POST C_Jrel -> CF POST C_B82eac.
(* glue: Seg/X12.v seg_X2 :821 @UB via _F; runs x12_store_evt :303, x12_x2_evt :503 *)
Hypothesis seg_X2 : forall POST, CF POST C_Jrel -> CF POST C_B82ecc.
(* glue: Seg/YTail.v seg_Jrel :1406 @UB via _F; runs jrel_evt_real :1102, jrel_evt_side :1133; its exit B82f58 is the discharged class-full arm (no record, ACtlCutP.v's note), so it is not a premise *)
Hypothesis seg_Jrel : forall POST, CF POST C_B82f48 -> CF POST C_Jrel.
(* glue: Seg/YTail.v seg_Y1 :854 @UB via _F; runs y1_evt :743 *)
Hypothesis seg_Y1 : forall POST, CF POST C_B82f5c -> CF POST C_B82f48.
(* glue: Seg/YTail.v seg_Y3 :241 @UB via _F; runs y3_evt :66 *)
Hypothesis seg_Y3 : CF ctl_post_leaf C_B82f5c.

(* ---------------------------------------------------------------------------------------------------------
   6. The loop combinators, in the donor's rt_G_allX pattern (ACfj.v:157-163): induction on the remaining turns
   m, the base case vacuous past the last turn, the step one turn of stage hypotheses, the back edge at the head
   cut with the next index.  Measures and turn bodies from ctrl's own text (Slot.v:400-516). *)

(* --- The rows (loop_rows), inside the frame turn: head B82bf4_at j i, latches F35 / F36 (row i + 1), exit
   B82ca0_at j.  Measure 11 - i: ctrl Slot.v:412 `(11 <= i + k)%nat`, bound RL `i <= 10`. *)
Lemma turn_rows : forall POST (j i : nat), CF POST (ix_cut C_B82ca0_at [Z.of_nat j]) ->
  CF POST (ix_cut C_B82bf4_at [Z.of_nat j; Z.of_nat (S i)]) -> CF POST (ix_cut C_B82bf4_at [Z.of_nat j; Z.of_nat i]).
Proof.
  intros POST j i Hca0 HS.
  pose proof (seg_F36 POST j i HS Hca0) as Hc38.
  exact (seg_F34 POST j i (seg_F35 POST j i HS Hc38 Hca0)).
Qed.

Lemma loop_rows : forall POST (j : nat), CF POST (ix_cut C_B82ca0_at [Z.of_nat j]) ->
  forall (m i : nat), (11 <= i + m)%nat -> CF POST (ix_cut C_B82bf4_at [Z.of_nat j; Z.of_nat i]).
Proof.
  intros POST j Hca0. induction m as [|m IH]; intros i Hm.
  - apply vac_B82bf4. lia.
  - destruct (Nat.lt_ge_cases 10 i) as [Hi|Hi]; [exact (vac_B82bf4 POST j i Hi)|].
    exact (turn_rows POST j i Hca0 (IH (S i) ltac:(lia))).
Qed.

(* --- The frame loop (loop_frames): head B81ec4_at j, latch F38, exit B82eac.  Measure 256 - j: ctrl
   Slot.v:471 `(256 <= j + k)%nat`, bound LI `j <= 255`.  One turn is ctrl's turn_frames (Slot.v:421-466) with the
   row loop at i = 0 (Slot.v:428). *)
Lemma turn_frames : forall POST (j : nat), CF POST C_B82eac ->
  CF POST (ix_cut C_B81ec4_at [Z.of_nat (S j)]) -> CF POST (ix_cut C_B81ec4_at [Z.of_nat j]).
Proof.
  intros POST j Heac HS.
  pose proof (seg_F38 POST j HS Heac) as Hd1c.
  pose proof (seg_F37 POST j Hd1c) as Hca0.
  pose proof (seg_F36_c20 POST j Hca0) as Hc84.
  pose proof (seg_F33 POST j (loop_rows POST j Hca0 11 0 ltac:(lia)) Hc84) as Hbcc.
  pose proof (seg_F36_c2c POST j Hca0) as Hc90.
  destruct (seg_F32 POST j Hbcc Hc90) as [Hb38 Hb5c].
  pose proof (seg_F31 POST j Hb38 Hb5c) as Haf8.
  pose proof (seg_F30 POST j Haf8) as Habc.
  pose proof (seg_F29 POST j Habc) as Haa4.
  pose proof (seg_F28 POST j Haa4) as H92c.
  pose proof (seg_F27 POST j H92c Haa4) as H8b4.
  pose proof (seg_F26 POST j H8b4) as H8a4.
  pose proof (seg_F25 POST j H8a4) as H888.
  pose proof (seg_F24 POST j H888) as H878.
  pose proof (seg_F23 POST j H878) as H844.
  pose proof (seg_F22t POST j H844) as H83c.
  pose proof (seg_F22 POST j H83c) as H7f8.
  pose proof (seg_F21 POST j H7f8 H844) as H728.
  pose proof (seg_F20 POST j H728) as H668.
  pose proof (seg_F19 POST j H668) as H64c.
  pose proof (seg_F18 POST j H64c Habc) as H634.
  pose proof (seg_F17b POST j H634) as H468.
  pose proof (seg_F17 POST j H468) as H464.
  pose proof (seg_F16 POST j H464) as H3d8.
  pose proof (seg_F15b POST j H3d8 H468) as H37c.
  pose proof (seg_F15 POST j H37c) as H378.
  pose proof (seg_F14 POST j H37c H378) as H35c.
  pose proof (seg_F13 POST j H35c) as H340.
  pose proof (seg_F12_298 POST j H340) as H308.
  pose proof (seg_F12 POST j H340) as H304.
  pose proof (seg_F11 POST j H304) as H26c.
  pose proof (seg_F10 POST j H26c H308) as H1ec.
  pose proof (seg_F9 POST j H1ec) as H180.
  pose proof (seg_F8 POST j H180) as H174.
  pose proof (seg_F7 POST j H174) as H15c.
  pose proof (seg_F6 POST j H15c) as H098.
  pose proof (seg_F5 POST j H15c) as H048.
  pose proof (seg_F4 POST j H098) as Hfbc.
  pose proof (seg_F3 POST j Hfbc H048) as Hf78.
  pose proof (seg_F2 POST j Hf78 H048) as Hf50.
  exact (seg_F1 POST j Hf50 Heac).
Qed.

Lemma loop_frames : forall POST, CF POST C_B82eac ->
  forall (m j : nat), (256 <= j + m)%nat -> CF POST (ix_cut C_B81ec4_at [Z.of_nat j]).
Proof.
  intros POST Heac. induction m as [|m IH]; intros j Hm.
  - apply vac_B81ec4. lia.
  - destruct (Nat.lt_ge_cases 255 j) as [Hj|Hj]; [exact (vac_B81ec4 POST j Hj)|].
    exact (turn_frames POST j Heac (IH (S j) ltac:(lia))).
Qed.

(* --- The round trip (loop_rt): head B816ec_at b, latches R21 and R21_a5c (the n_b = 0 skip lands in R21_a5c's
   entry B81ac0_at at the same b).  Measure 7 - b: ctrl Slot.v:510 `(7 <= b + k)%nat`, bound RB `b <= 6`; the
   image's `li a0,7` at 0x81ac4 (ACtlK.v).  One turn is ctrl's turn_rt (Slot.v:482-504); the loop's exits B81c58 /
   B81c60 / B81ca8 are taken at b = 6 inside R21 / R21_a5c and are supplied from before the loop
   (Slot.v:538-541). *)
Lemma turn_rt : forall POST (b : nat), CF POST C_B81c58 -> CF POST C_B81c60 -> CF POST C_B81ca8 ->
  CF POST (ix_cut C_B816ec_at [Z.of_nat (S b)]) -> CF POST (ix_cut C_B816ec_at [Z.of_nat b]).
Proof.
  intros POST b Hc58 Hc60 Hca8 HS.
  pose proof (seg_R21_a5c POST b HS Hc58 Hc60) as Hac0.
  pose proof (seg_R21 POST b HS Hc58 Hca8) as Haa0.
  pose proof (seg_R20 POST b Haa0) as Ha68.
  pose proof (seg_R19 POST b Ha68) as Ha50.
  pose proof (seg_R18 POST b Ha50) as H9d0.
  pose proof (seg_R17 POST b H9d0) as H9a8.
  pose proof (seg_R16 POST b Haa0) as H94c.
  pose proof (seg_R15 POST b Haa0) as H914.
  pose proof (seg_R14 POST b H9a8) as H8a8.
  pose proof (seg_R13 POST b Haa0) as H860.
  pose proof (seg_R12 POST b H860) as H834.
  pose proof (seg_R11 POST b H860) as H7ec.
  pose proof (seg_R10 POST b H7ec H834 H8a8 H914 H94c) as H7a4.
  pose proof (seg_R9 POST b H7a4) as H77c.
  pose proof (seg_R8 POST b H77c) as H764.
  pose proof (seg_R7 POST b H764 Hac0) as H710.
  exact (seg_R6 POST b H710).
Qed.

Lemma loop_rt : forall POST, CF POST C_B81c58 -> CF POST C_B81c60 -> CF POST C_B81ca8 ->
  forall (m b : nat), (7 <= b + m)%nat -> CF POST (ix_cut C_B816ec_at [Z.of_nat b]).
Proof.
  intros POST Hc58 Hc60 Hca8. induction m as [|m IH]; intros b Hm.
  - apply vac_B816ec. lia.
  - destruct (Nat.lt_ge_cases 6 b) as [Hb|Hb]; [exact (vac_B816ec POST b Hb)|].
    exact (turn_rt POST b Hc58 Hc60 Hca8 (IH (S b) ltac:(lia))).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   7. The composition: backwards from the exit cut C_B82f5c to the entry cut C_ENTRY, in ctrl's discharge order
   (Slot.v:520-551: release, epilogue, frame loop, P12 .. P1, round trip, R5 .. R1, A5 .. A1; without ctrl's
   seg_Y2, whose entry is the discharged class-full arm), for every POST. *)
Lemma ctl_walk_from : forall POST, (forall cx p, POST (ACtlCut.cx_set_fpos cx p) = POST cx) ->
  CF POST C_B82f5c -> CF POST C_ENTRY.
Proof.
  intros POST HPF Hf5c.
  pose proof (seg_Y1 POST Hf5c) as Hf48.
  pose proof (seg_Jrel POST Hf48) as Hjrel.
  pose proof (seg_X2 POST Hjrel) as Hecc.
  pose proof (seg_X1 POST Hecc Hjrel) as Heac.
  pose proof (seg_P12 POST (loop_frames POST Heac 256 0 ltac:(lia)) Heac) as He08.
  pose proof (seg_P11 POST He08) as Hde8.
  pose proof (seg_P10 POST Hde8) as Hdd4.
  pose proof (seg_P9 POST Hdd4) as Hdbc.
  pose proof (seg_P8 POST Hdbc) as Hda8.
  pose proof (seg_P7 POST Hda8) as Hd80.
  pose proof (seg_P6 POST Hd80) as Hd68.
  pose proof (seg_P5 POST Hd68) as Hd28.
  pose proof (seg_P4 POST Hd28) as Hd18.
  pose proof (seg_P3 POST Hd18) as Hcb0.
  pose proof (seg_P2 POST Hcb0) as Hca8.
  pose proof (seg_P1_bfc POST Hca8) as Hc60.
  pose proof (seg_P1 POST Hca8) as Hc58.
  pose proof (seg_R5 POST (loop_rt POST Hc58 Hc60 Hca8 7 0 ltac:(lia))) as H69c.
  pose proof (seg_R4 POST H69c) as H68c.
  pose proof (seg_R3 POST H68c) as H640.
  pose proof (seg_R2 POST H640) as H5fc.
  pose proof (seg_R1 POST H5fc Hcb0) as H550.
  pose proof (seg_A5 POST 0 H550 H5fc Hcb0) as H548.
  pose proof (seg_A4 POST H548 Hjrel) as H220.
  pose proof (seg_A3 POST H220) as H0c4.
  pose proof (seg_A2 POST H0c4) as H090.
  exact (seg_A1 POST HPF H090 H0c4).
Qed.

(* The walk at the exit post the top consumes. *)
Lemma ctl_walk_leaf : CF ctl_post_leaf C_ENTRY.
Proof. exact (ctl_walk_from ctl_post_leaf (fun cx p => eq_refl) seg_Y3). Qed.

(* The brief's statement: the walk at ACtlCut.v's own exit post. *)
Lemma ctl_walk : CF ctl_post C_ENTRY.
Proof.
  apply (ctl_from_mono ctl_post_leaf ctl_post C_ENTRY); [| exact ctl_walk_leaf].
  intros cx W' c' _ (ly' & S' & regs' & mem' & md' & k & Ec & Hpost).
  exists (lib.Reusable.YO09.LL 0 (m_fs (c_md cx)) []), ly', S', regs', mem', md', k.
  exact (conj Ec Hpost).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   8. The top: the core's lib contract (the donor's tfib_lib_x_body / tfib_lib_x, ACfj.v:230-259).  The entry
   context is the contract's own arguments with the engine's sp anchor; the journal starts in its initial form
   (ajournal_init, at the core's sink head and FP = []); the walk runs from C_ENTRY at index [], k = 0, whose
   configuration cfg_at segs (cut_pc C_ENTRY) regs mem md is the contract's start cfg_at segs A_LLVMF regs mem md
   (0x81018 both); the frame law is vacuous there (C_ENTRY owns nothing); SRr's definition applied to the entry
   AI fact is srz_enter; the leaf is LL 0 (m_fs md) []. *)
Theorem ctl_lib_x : Reusable.YCfn.tfib_lib_contract_x B MT XM_LIB XN_LIB RLO RHI.
Proof using All.
  unfold Reusable.YCfn.tfib_lib_contract_x.
  intros ly S W regs mem md p n pl M K HAI HPRE HK.
  rewrite LS_LEAF.
  pose proof HPRE as (HAFN & _ & _ & _ & _ & _ & _ & Hfr0 & _).
  pose (cx := ACtlCut.mkCtlCx ly S W regs mem md p n pl M 0
                (32 * ((Reusable.YG0d.spZ regs + -128) / 32))).
  assert (HB : CB cx) by (split; [exact HPRE | reflexivity]).
  assert (HWALK : Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs Reusable.YCfn.A_LLVMF regs mem md)
                    (ctl_post_leaf cx)).
  { refine (ctl_walk_leaf cx [] 0 0 ly S W regs mem md HB _ Hfr0
              (fun cid pos (H : In (cid, pos) []) => False_ind _ H) _ _ (CTLRT_ENTRY cx HB)).
    - first [ exact (Reusable.YCbq.ajournal_init (SK := Reusable.YE2k.tfib_sink_head)
                       segs B Reusable.YCfn.LLVMF_STK [] ly S W regs mem md [] HAFN)
            | (eapply (Reusable.YCbq.ajournal_init (SK := Reusable.YE2k.tfib_sink_head)); exact HAFN) ].
    - exact (Z.le_refl 0).
    - split; [apply Permutation_refl | split; reflexivity]. }
  apply (HWALK HAI).
  intros W' c' Hwle HAI' (ly' & S' & regs' & mem' & md' & k & Ec & Hpost).
  apply (HK _ W' c' Hwle HAI').
  exists ly', S', regs', mem', md', k.
  exact (conj Ec Hpost).
Qed.

End Ctl.

(* ---------------------------------------------------------------------------------------------------------
   9. THE TOP AT THE B CORE'S OWN SYMBOL BUNDLE (porter a Theorem Labs lane 23:10Z; agreed with a Theorem Labs lane 23:53Z, mirrored
   in image A with A.AD2l.CtrlB, whose closure is a separate piece there).  B := CtrlB of the B core (the relocated
   donor root YD2l.v:11 TfibB, in Reusable.YD2l at YD2l.v:14, not Reusable.YF0m as a Theorem Labs lane planned at 00:13Z), TFIB_SYMS := CtrlB_syms (the core's, donor
   root YD2l.v:69 TfibB_syms) and TFIB_LIB := CtrlB_libS, with the meter and bounds fixed as
   the donor's AD2o.v:30-31 / LIBX fix them: MT := ameter_triv (donor YCbp.v:16), XM_LIB = XN_LIB := XL0 (donor root
   YCfi.v:54; YCfi is cgif's unit file and does not join the core, so XL0 is restated here), RLO / RHI :=
   0x9f1a0 / 0xa15e8, .data.rel.ro's start to the GNU_RELRO filesz end (a Theorem Labs lane 00:35Z; readelf: .init_array 0x9f168
   + 0x20, .fini_array 0x9f188 + 0x10, .preinit_array 0x9f198 + 0x8, .data.rel.ro 0x9f1a0 + 0x16f0, .got 0xa0890 +
   0xd58, .relro_padding from 0xa15e8; constants-B.md (a working note, not in this delivery)).  RELRO_IMG at those values is relro_img_CtrlB below, proved
   as the donor's TfibB_libS proves its errno-in-image field (root YCfi.v:29-33): [0x9f1a0, 0xa15e8) lies in
   segment 2 of tfibsegs = (0x9f000, 0x3000), the pinned image's third PT_LOAD (readelf: LOAD vaddr 0x9f168, memsz
   0x2e98, page-rounded to [0x9f000, 0xa2000)); also lib/AZ/BothW/BImg.v:29.
   CtrlB_libS is the image-B port of the donor's root YCfi.v:23-41 (TfibB_libS : TfibLib TfibB, image A's
   A/ACfi.v:25).  Until it is proved it is a NAMED Section hypothesis here (a Theorem Labs lane 23:53Z: no Aborted lemma), so it
   shows in Print Assumptions of ctl_lib_x_CtrlB.  Its one image-specific input is the B core's lib_const_addr,
   ruled from nm (a Theorem Labs lane 23:53Z): KIND_NAME [0x9f580, 0x9f580 + 0xa0), BOX_CATALOGUE [0x9f620, 0x9f620 + 0xfe0),
   CTRL_FRAMES [0xa0600, 0xa0600 + 0x160) -- the three tables the walk's callees read; with errno 0x5dc5ac inside
   segment 3 of tfibsegs = (0xa2000, 0x55c000) (the pinned image's fourth PT_LOAD, page-rounded; also
   lib/AZ/BothW/BImg.v (not in this delivery)).  The proof, once the B core's TfibLib and Tfib_owned_static land, is the donor's text
   with those values. *)
Definition XL0 : Z -> Z := fun _ => 0.

Lemma relro_img_CtrlB : forall a, 0x9f1a0 <= a < 0xa15e8 -> Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha. unfold Reusable.YG0d.in_img.
  assert (Hb : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs) 2 =
               Some (0x9f000, 0x3000)) by (vm_compute; reflexivity).
  rewrite nth_error_map in Hb. destruct (nth_error segs 2) as [sg|] eqn:E; [|discriminate Hb].
  cbn in Hb. injection Hb as H1 H2.
  exists sg. split; [exact (nth_error_In _ 2 E) | rewrite H1, H2; lia].
Qed.

Section CtlTop.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Hypothesis CtrlB_libS : Reusable.YCeg.TfibLib Reusable.YD2l.CtrlB.

(* The top at CtrlB.  Its remaining arguments are Section Ctl's other hypotheses over CtrlB, in declaration order:
   LS_LEAF, CTLRT_ENTRY, CHAIN_OF_CUT and the 89 stage hypotheses.  (Image A states the same instantiation of the generic ctl_lib_x,
   lib/A/ACtl.v:1196; image B states it here, a Theorem Labs lane 23:53Z.) *)
Definition ctl_lib_x_CtrlB :=
  ctl_lib_x (fx := fx) (rc := rc) (LS := LS) Reusable.YD2l.CtrlB Reusable.YCbp.ameter_triv XL0 XL0 0x9f1a0 0xa15e8
    relro_img_CtrlB Reusable.YD2l.CtrlB_syms CtrlB_libS.
End CtlTop.

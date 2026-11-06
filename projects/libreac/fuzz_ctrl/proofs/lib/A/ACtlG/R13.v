(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 507 of its 559 lines of code are new or changed and 3060 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtl.v, with its module names, addresses and numbers changed; 146 of its 169 lines of code are new or changed and 536 lines of the source are left out. *)
(* lib/A/ACtlG/R13.v -- GLUE for stage seg_R13 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:690).
   Written by a Theorem Labs lane's glue lane (piece W2a: R6 R7 R8 R9 R13); single writer.  The pattern is
   glue-pattern.md (a working note, not in this delivery) (worked example lib/A/ACtlG/A5.v).
   rule 24: no function proved (stage glue of a walk; kind: segment lemma).

   WHAT IT PROVES
     glue_seg_R13 : forall POST (b : nat), CF POST (ix_cut C_A81924_at [Z.of_nat b]) ->
                                           CF POST (ix_cut C_A81734_at [Z.of_nat b])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_R13.  Segment R13 (lib/A/Prog/Seg/R13.v, seg_R13 :58): 0x81734 `li a1,1` and 0x81738 `beq a0,a1,8191c` (a0 is
   the reac_identity_ingest result 1, X81734's `a0v regs 1`, so the branch is taken and the abort pair at 0x8173c is
   not reached), then 0x8191c `mv a0,s8` and 0x81920 `jal wrapper_free` (R15.v rfree_evt :40), which stops AT the
   allocator entry 0x53378 with ra = 0x81924; the free of the round-trip buffer (phi, rnb cx b) and its return to
   the exit cut C_A81924_at are the shared free-site lemma of the four segments R13 / R15 / R16 / R20 (plan 2.5,
   "ONE lemma shared by the four"), A.ACtlG.Free81920.glue_free_81920 (a Theorem Labs lane's file, the core's afree04_rule).

   THE PROOF (glue-pattern.md section 3 and section 9)
   G1  unfold the entry cut C_A81734_at at [Z.of_nat b] (ACtlCutP.v:1441-1460): ix_cut's index equation, the body's
       let b := ixn 0 idx (Nat2Z.id), its 28 conjuncts and X81734 (a0 = 1, s8 = phi, RB at the turn-(S b) records).
   G2  the run's one premise a0 = 1 is X81734's a0v; no memory premise, no rng premise (R13F.v / R15F.v: neither run
       makes a data access).
   G3  ProgBridge.cfg_at_MS turns the cut's cfg_at into MS regs3 ..; YA0nR.SRr_xregs_eqv moves the walk to the
       canonical map mkR_of regs3 (Regs6ss.mkR_of_eqv), whose 31 registers instantiate r13_evt_F by unification.
   G4  two register-only lifts at the empty footprint (Kit.kit_RNG0, fp_avoids vacuous): YA0nR.SRr_fevt over
       R13F.r13_evt_F (0x81734 -> 0x8191c, only a1 changes), then over R15F.rfree_evt_F (0x8191c -> 0x53378,
       ra := 0x81924, a0 := s8), each through ProgBridge.fevt_of_evtF (rsegs = tfibsegs by conversion,
       ProgBridge.tfibsegs_rsegs).  The second run starts at the first run's explicit end map, so no second
       register move is needed.
   G5  at 0x53378 the state is cfg_at segs 0x53378 RT mem3 md'' (cfg_at_MS read backwards), RT the end map: every
       register but 1, 10, 11 is regs3's (by conversion), getr RT 1 = 0x81924, getr RT 10 = s8 = phi.  The shared
       free lemma then takes: the journal at k stepped twice over the empty write set (memory unchanged, the model
       materialized twice: YCbq.ajournal_exec with Wr := False, as A5.v), frames / frame law unchanged, k <= 2b+1
       (the entry's kmax), the Permutation of the live list (the entry body's), and C_A81924_at's body at the CALL
       map RT and the unchanged memory with bl := the entry blocks: FRAC through its seven registers
       (Kit.kit_frac_move), RB through 22 / 25 / 23, spills / PRO / RXS through register 9, every memory conjunct
       unchanged.

   SECTION HYPOTHESES (exact text below).  All are ACtl.v's own, for those A.ACtlG.Free81920's (
   Free81920.v (at head lib/A/ACtlG/Free81920.v:175-199; from a working branch a8f81298e30)) glue_free_81920 takes (MT_FREE for its MOK_FREE), copied verbatim and passed to glue_free_81920; this stage adds none of its own.
   - LAWS: the core's AR law record (YCbq.v:207), as A5.v and ACtl.v:183 take it.
   - TFIB_SYMS: the core's symbol record for B (ACtl.v:191).
   - AFREE4: the core's free rule afree04_rule (YC5d.v:76), sink head explicit (the donor walk's Section hypothesis,
     ACfj.v:99-112; glue-pattern.md section 9).
   - MT_FREE: ACtl.v's own (ACtl.v:279, same text), every meter fact mo_ok; glue_free_81920's MOK_FREE is its
     instance at mo_free MT.
   - CHAIN_OF_CUT: the frame-pointer chain and call trace at an allocator call (ACtl.v:434, its text).
   Route (C): VIS0 / OWNED_RO are gone, here and in Free81920 (its exit's ctl_rt_C is
   ProgWorldCtlRtC.ctl_rt_C_of_AR); BLKSH is gone too (Free81920 cites the PROVED
   A.ProgWorldShadow.ctl_block_shadow_of_AR, a Theorem Labs lane 13:12Z); glue_free_81920 takes none of the three.
   The KitMem.v helpers the free step uses (kitmem_bytes_at_mrd / kitmem_addressable_mrd / kitmem_rw_cells_mrd) are
   cited by name inside Free81920.v (a Theorem Labs lane's KitMem.v, a working branch 4a56e997c0f).

   CLOSURE: every Require is qualified; the six modules that exist twice (YI04 YI16 YK11 YK1b YM05 YO09) are named
   fully qualified (a Theorem Labs lane 03:5xZ).  Requires the _F files R13F.v / R15F.v of record (glue base 46eb24cd4b3) and
   so their closure; the frame-route blob list is in the commit message.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at only as Y11.* (the core's lib/Reusable/YK11) / Reusable.YG0d.*.

   BUILD STATE: see the commit message (type-check on the planning core with the workspace-only substitution of the
   port_core_refused_* names; values do not count). *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.AF0m A.Img0 A.AsanRT A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.R13F A.Prog.Seg.R15F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.Free81920.
Import ListNotations.
Local Open Scope Z_scope.

Module Y11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module Y1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
(* lib/Lib's modules, named absolutely: lib/A/Bz/Lib/ and lib/A/Tk/UL/ twins (MState, Mem, Step, Cells, ...) are in
   this file's closure, so a partial `Lib.MState` is ambiguous (measured: it did not match the runs' MS). *)
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LStep := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueR13.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : Y11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :240, :248), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
(* ACtl.v's local notations (ACtl.v:380, :387-389), verbatim, so that CHAIN_OF_CUT below is ACtl.v's text. *)
Local Notation ctlcx := ACtlCut.ctlcx.
Local Notation c_md := ACtlCut.c_md.
Local Notation c_mem := ACtlCut.c_mem.
Local Notation CB cx := (ACtlCut.ctl_base B MT XM_LIB RLO RHI cx).
Local Notation C_A81734_at := (ACtlCutP.C_A81734_at B).
Local Notation C_A81924_at := (ACtlCutP.C_A81924_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses: ACtl.v's own, the ones glue_free_81920 takes (sources in the header). *)

Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis AFREE4 : Reusable.YC5d.afree04_rule (SK := A.AE2k.tfib_sink_head) segs B MT.
Hypothesis MT_FREE : forall S m, Reusable.YC5d.mo_ok MT S m.
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
   The stage. *)
Lemma glue_seg_R13 : forall POST (b : nat), CF POST (ix_cut C_A81924_at [Z.of_nat b]) -> CF POST (ix_cut C_A81734_at [Z.of_nat b]).
Proof.
  intros POST b HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat b] (ix_cut, ACtlCut.v:232-234; C_A81734_at, ACtlCutP.v:1441-1460). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81734_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hb6 & HHB & R23 & Hour & Hout & Hcur & S112 & S128 & HPRO & S104 & S96 &
    S64 & S144 & S192 & Hidb & Hjk72 & S280 & S240 & Hjy & Hjk32 & S152 & R21 & Had & HRXS & HX8).
  destruct HX8 as (Ha0 & R24 & HRB).
  cbv beta iota delta [ACtlCut.cut_kmax ACtlCut.ix_cut ACtlCutP.C_A81734_at ACtlCutP.ixn nth] in Hk.
  rewrite Nat2Z.id in Hk.
  (* G3: the cut's configuration in the run's state form, then the walk moved to the canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81734_at [Z.of_nat b])) with 0x81734.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 Y11.fp_regs
           (Z_to_bv 64 0x81734) Y11.fp_csr None mem3 (Y11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  (* G4 (first run): 0x81734 li a1,1 ; beq a0,a1,8191c -- register only, empty footprint. *)
  unfold LR6.mkR_of.
  eapply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx)).
  { apply A.ProgBridge.fevt_of_evtF. apply A.Prog.Seg.R13F.r13_evt_F.
    (* G2: a0 = 1 is X81734's a0v (YK11.getr regs3 10 is reg_get regs3 10 by conversion) *)
    exact Ha0. }
  { intros ? ? Hr0. unfold A.ACtlG.Kit.kit_RNG0 in Hr0. destruct Hr0. }
  intros ms1 md1 HQ1 Hsbm1.
  destruct HQ1 as (a1' & ->).
  (* G4 (second run): 0x8191c mv a0,s8 ; jal wrapper_free -- register only, stops at the allocator entry. *)
  eapply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md1 A.ACtlG.Kit.kit_RNG0 _ (POST cx)).
  { apply A.ProgBridge.fevt_of_evtF. apply A.Prog.Seg.R15F.rfree_evt_F. }
  { intros ? ? Hr0. unfold A.ACtlG.Kit.kit_RNG0 in Hr0. destruct Hr0. }
  intros ms2 md2 HQ2 Hsbm2.
  destruct HQ2 as (a0' & -> & Ea0). subst a0'.
  (* G5: the state at the allocator entry is the core's cfg_at at the run's end map RT (cfg_at_MS backwards). *)
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (LMS.MS ?R _ _ _ _ _ _) _) _ => set (RT := R) end.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x53378 RT mem3 md2) (POST cx)).
  (* the registers the exit body reads are regs3's (RT differs from mkR_of regs3 only at 1, 10, 11) *)
  assert (K2 : Y11.getr RT 2 = Y11.getr regs3 2) by reflexivity.
  assert (K3 : Y11.getr RT 3 = Y11.getr regs3 3) by reflexivity.
  assert (K4 : Y11.getr RT 4 = Y11.getr regs3 4) by reflexivity.
  assert (K8 : Y11.getr RT 8 = Y11.getr regs3 8) by reflexivity.
  assert (K9 : Y11.getr RT 9 = Y11.getr regs3 9) by reflexivity.
  assert (K19 : Y11.getr RT 19 = Y11.getr regs3 19) by reflexivity.
  assert (K21 : Y11.getr RT 21 = Y11.getr regs3 21) by reflexivity.
  assert (K22 : Y11.getr RT 22 = Y11.getr regs3 22) by reflexivity.
  assert (K23 : Y11.getr RT 23 = Y11.getr regs3 23) by reflexivity.
  assert (K25 : Y11.getr RT 25 = Y11.getr regs3 25) by reflexivity.
  assert (K26 : Y11.getr RT 26 = Y11.getr regs3 26) by reflexivity.
  assert (K1 : Y11.getr RT 1 = Z_to_bv 64 0x81924) by reflexivity.
  assert (K10 : Y11.getr RT 10 = Z_to_bv 64 phi).
  { transitivity (Y11.getr regs3 24); [reflexivity | exact R24]. }
  assert (Hsp : forall off v, ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill RT mem3 off v).
  { intros off v (Ab & HAb & Hq). exists Ab. split; [|exact Hq]. unfold ACtlCut.rgv in *. rewrite K9. exact HAb. }
  assert (HPRO' : ACtlCutP.PRO cx fr RT mem3).
  { unfold ACtlCutP.PRO, ACtlCutP.spill, ACtlCut.rgv in HPRO |- *. rewrite K9. exact HPRO. }
  assert (HRXS' : ACtlCutP.RXS cx fr RT mem3).
  { unfold ACtlCutP.RXS, ACtlCutP.spill, ACtlCut.rgv in HRXS |- *. rewrite K9. exact HRXS. }
  assert (HRB' : ltac:(match type of HRB with
                       | ACtlCutP.RB ?c ?f ?bb ?i ?g _ ?m => exact (ACtlCutP.RB c f bb i g RT m) end)).
  { unfold ACtlCutP.RB, ACtlCutP.CUR, ACtlCut.rgv in HRB |- *. rewrite K22, K25, K23. exact HRB. }
  apply (A.ACtlG.Free81920.glue_free_81920 B MT XM_LIB RLO RHI LAWS TFIB_SYMS AFREE4 (fun S => MT_FREE S _)
           CHAIN_OF_CUT POST b cx fr k ly3 S3 W3 RT mem3 md2 phi HX HB).
  - (* journal: no byte written, the model materialized twice (ajournal_exec, YCbq.v:636-643, as A5.v) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False)
      (mdc := md1);
      [| intros x _; reflexivity | apply Y1b.mem_grows_refl | intros x _; reflexivity | exact Hsbm2
       | intros a Ha; destruct Ha].
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply Y1b.mem_grows_refl | intros x _; reflexivity | exact Hsbm1
       | intros a Ha; destruct Ha].
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law *)
    exact HL.
  - (* the event bound: the entry's kmax 2b+1 *)
    exact Hk.
  - (* the live list: the entry body's *)
    exact HP.
  - (* C_A81924_at's body (ACtlCutP.v:1683-1706) at the call map RT, the unchanged memory, bl := entry blocks *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81924_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    split; [apply Permutation_refl|].
    split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 RT mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
    split; [exact Hn|]. split; [exact Hb6|].
    split; [unfold ACtlCut.rgv; rewrite K23; exact R23|].
    split; [exact Hour|]. split; [exact Hout|].
    split; [exact HRB'|].
    split; [exact (Hsp _ _ S128)|].
    split; [exact HPRO'|].
    split; [exact (Hsp _ _ S104)|]. split; [exact (Hsp _ _ S96)|]. split; [exact (Hsp _ _ S64)|].
    split; [unfold ACtlCut.rgv; rewrite K21; exact R21|].
    split; [exact (Hsp _ _ S112)|]. split; [exact (Hsp _ _ S144)|]. split; [exact (Hsp _ _ S192)|].
    split; [exact Hidb|]. split; [exact Hjk72|].
    split; [exact (Hsp _ _ S280)|]. split; [exact (Hsp _ _ S240)|].
    split; [exact Hjy|]. split; [exact Hjk32|].
    split; [exact (Hsp _ _ S152)|].
    split; [exact Had|].
    exact HRXS'.
  - exact K1.
  - exact K10.
Qed.

End GlueR13.

Print Assumptions glue_seg_R13.

(* Gate check (a Theorem Labs lane 07:18Z): the Section's classes are the CORE copies of the twin modules (lib/Reusable). *)
Locate CM05.RunCeil.
Locate CO09.lib_shape.
Locate Y11.FPState.

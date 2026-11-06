(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 507 of its 559 lines of code are new or changed and 3060 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtl.v, with its addresses and numbers changed; 121 of its 137 lines of code are new or changed and 543 lines of the source are left out. *)
(* lib/A/ACtlG/R15.v -- GLUE for stage seg_R15 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:694):
     glue_seg_R15 : forall POST (b : nat),
       CF POST (ix_cut C_A81924_at [Z.of_nat b]) -> CF POST (ix_cut C_A817c8_at [Z.of_nat b])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []).  Written by a Theorem Labs lane's glue lane;
   single writer.  rule 24: no function proved (stage glue of a walk).

   SEGMENT R15 (Seg/R15.v seg_R15 :856; the round trip's n_b = 0 exit of the block-sum test): 0x817c8 `beqz a0,8191c`
   with a0 = 0 (taken), then 0x8191c `mv a0,s8` ; 0x81920 `jal wrapper_free` (ra := 0x81924, a0 := s8 = phi), then the
   free.  Runs (a Theorem Labs lane's re-run, lib/A/Prog/Seg/R15F.v): r15_evt_F (:28) and rfree_evt_F (:44); neither touches
   memory, so both have no rng premise and are lifted at the empty footprint.

   THE PROOF (glue-pattern.md sections 3 and 9)
   G1  the entry cut C_A817c8_at [b] (ACtlCutP.v:1498): 26 conjuncts after its block phi.
   G2  no numeric premise: r15_evt_F needs a0 = 0 (the body's a0v regs 0); rfree_evt_F needs nothing.
   G3  cfg_at_MS, then the walk moved from the cut's map regs3 to the runs' explicit map mkR (reg_get regs3 1) ..
       (reg_get regs3 31) = Regs6ss.mkR_of regs3 (Reusable.YA0nR.SRr_xregs_eqv).
   G4  both runs lifted by Reusable.YA0nR.SRr_fevt at Kit.kit_RNG0 (the second starts at the first's end state, the
       same explicit map); the journal crosses each by ajournal_exec over the empty write set (model materialized).
   G5  the free at 0x53378 is the shared site lemma A.ACtlG.Free81920.glue_free_81920 (plan section 2.5: one lemma for
       R13 / R15 / R16 / R20), at the end map R (ra 0x81924, a0 = s8 = phi, every other register regs3's), with
       C_A81924_at's body at regs3 (it is the entry body without HB / s8 / a0, its block list the entry blocks)
       moved to R by Free81920.body924_regs (R keeps the callee-saved registers).

   SECTION HYPOTHESES: ACtl.v's Section hypotheses of the same name and text (LAWS, TFIB_SYMS, AFREE4, MT_FREE,
   CHAIN_OF_CUT), passed to glue_free_81920 (its MOK_FREE is (fun S => MT_FREE S _), as ACtl.v:277-278 says);
   sources in Free81920.v's header.  Route (C): the cut's ctl_rt_C is not opened here (no shadow byte is read before
   the free), and the free lemma supplies the exit's ctl_rt_C; VIS0 / OWNED_RO are gone.

   CLOSURE: every project Require is qualified; the six core modules with a lib/A twin (YK11 YK1b YM05 YO09 ...) by
   absolute name.  No statement names a frame-route identifier.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are Reusable.YK11 (alias CK11 = the core's module) / Reusable.YG0d;
   lib/Lib's Regs6ss / Mem / Step / Cells / Frame through the aliases LR6 / LMem / LStep / LCells / LFrame (lib/A/Bz/Lib
   twins are in the closure).

   BUILD STATE (route (C), type-check): rc=0 on a working branch (a working branch 1899bed1aee merged) through
   cb (BASE row 23b918fe0c2e, a build machine), no substitution; the build of record
   (cbrec) is named in the commit.  Print Assumptions glue_seg_R15 = Rocq primitives + functional_extensionality_dep.
   No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG0f YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0d YC5d YCbq.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.AF0m A.Img0 A.AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP A.ProgBridge A.ProgWorld.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.Free81920 A.Prog.Seg.R15F.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's YK11 and lib/Lib's modules by their full paths (ctrl's lib/A/Reusable and lib/A/Bz/Lib twins are in
   this file's closure, so the partial names are ambiguous). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LStep := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LFrame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueR15.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :242, :248), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A817c8_at := (ACtlCutP.C_A817c8_at B).
Local Notation C_A81924_at := (ACtlCutP.C_A81924_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses: ACtl.v's of these names and texts (Free81920.v's, with its MOK_FREE given by MT_FREE). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis AFREE4 : Reusable.YC5d.afree04_rule (SK := A.AE2k.tfib_sink_head) segs B MT.
Hypothesis MT_FREE : forall S m, Reusable.YC5d.mo_ok MT S m.
Hypothesis CHAIN_OF_CUT : forall (FP : list (Z * Z)) (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 k
    (regsT : bvmap 5 word) (pc0 ra : Z),
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) own ly3 S3 W3 mem3 md3 k ->
  CK11.getr regsT 8 = Z_to_bv 64 (ACtlCut.c_sp cx) ->
  CK11.getr regsT 1 = Z_to_bv 64 ra ->
  LMem.bytes_at segs mem3 (ACtlCut.c_sp cx - 104)
    (LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 27) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 26) ++
     LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 25) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 24) ++
     LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 23) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 22) ++
     LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 21) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 20) ++
     LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 19) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 18) ++
     LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 9) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 8) ++
     LMem.le8 (Z_to_bv 64 A.ACfn.RA_LLVMF)) ->
  ACtlCut.c_sp cx - 4096 < Reusable.YG0d.spZ regsT -> Reusable.YG0d.spZ regsT + 416 <= ACtlCut.c_sp cx ->
  In (pc0, ra) [(Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81640);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x81924);
                (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81da4);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x82940)] ->
  exists ch, ACtlCut.ctl_chain ly3 W3 mem3 regsT ch /\ ACtlCut.ctl_trace_in B pc0 regsT ch.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_R15 : forall POST (b : nat),
  CF POST (ix_cut C_A81924_at [Z.of_nat b]) -> CF POST (ix_cut C_A817c8_at [Z.of_nat b]).
Proof.
  intros POST b HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [b] *)
  destruct Hbody as [Hidx Hb]. subst idx.
  assert (Eix : ACtlCutP.ixn 0 [Z.of_nat b] = b) by (unfold ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A817c8_at] in Hb.
  rewrite Eix in Hb.
  destruct Hb as (phi & Hperm & HFRAC & (Hcn & Hb6 & HHB & R23 & HOUR & HOUTA & HCUR) & HRB & R24 & Ha0 &
    S128 & HPRO & S104 & S96 & S64 & R21 & S112 & S144 & S192 & HC2688 & HC2768 & S280 & S240 & HC3040 & HC3056 &
    S152 & HA2176 & HRXS).
  change (k <= 2 * Z.of_nat (ACtlCutP.ixn 0 [Z.of_nat b]) + 1) in Hk. rewrite Eix in Hk.
  (* C_A81924_at's body at the entry map and memory: the entry body without HB / s8 / a0 *)
  assert (H924 : ACtlCut.cut_body C_A81924_at cx [Z.of_nat b]
                   (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) fr fr regs3 mem3).
  { cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81924_at]. rewrite Eix.
    exact (conj (Permutation_refl _) (conj HFRAC (conj Hcn (conj Hb6 (conj R23 (conj HOUR (conj HOUTA (conj HRB
      (conj S128 (conj HPRO (conj S104 (conj S96 (conj S64 (conj R21 (conj S112 (conj S144 (conj S192 (conj HC2688
      (conj HC2768 (conj S280 (conj S240 (conj HC3040 (conj HC3056 (conj S152 (conj HA2176 HRXS))))))))))))))))))))))))). }
  (* G3: the cut's configuration in the runs' state form, the walk moved to the runs' explicit map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A817c8_at [Z.of_nat b])) with 0x817c8.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x817c8) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  (* G4, run 1: 0x817c8 beqz a0 (a0 = 0) -> 0x8191c, register-only *)
  pose proof (A.Prog.Seg.R15F.r15_evt_F A.ACtlG.Kit.kit_RNG0
    (reg_get regs3 1) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6)
    (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10) (reg_get regs3 11) (reg_get regs3 12)
    (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16) (reg_get regs3 17) (reg_get regs3 18)
    (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21) (reg_get regs3 22) (reg_get regs3 23) (reg_get regs3 24)
    (reg_get regs3 25) (reg_get regs3 26) (reg_get regs3 27) (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30)
    (reg_get regs3 31) CK11.fp_regs CK11.fp_csr mem3 Ha0) as HRUN1.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN1) as HFS1.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS1.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx) HFS1).
  { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
  intros ms1 md1 Ems1 Hsbm1. subst ms1.
  assert (HJ1 : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 mem3 md1 k).
  { eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl
      | intros x _; reflexivity | exact Hsbm1 | intros a Ha; destruct Ha]. }
  (* G4, run 2: 0x8191c mv a0,s8 ; 0x81920 jal wrapper_free -> 0x53378, register-only *)
  pose proof (A.Prog.Seg.R15F.rfree_evt_F A.ACtlG.Kit.kit_RNG0
    (reg_get regs3 1) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6)
    (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10) (reg_get regs3 11) (reg_get regs3 12)
    (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16) (reg_get regs3 17) (reg_get regs3 18)
    (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21) (reg_get regs3 22) (reg_get regs3 23) (reg_get regs3 24)
    (reg_get regs3 25) (reg_get regs3 26) (reg_get regs3 27) (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30)
    (reg_get regs3 31) CK11.fp_regs CK11.fp_csr mem3) as HRUN2.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN2) as HFS2.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS2.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md1 A.ACtlG.Kit.kit_RNG0 _ (POST cx) HFS2).
  { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
  intros ms2 md2 (a0' & Ems2 & Ea0') Hsbm2. subst ms2 a0'.
  assert (HJ2 : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 mem3 md2 k).
  { eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ1 | intros x _; reflexivity | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl
      | intros x _; reflexivity | exact Hsbm2 | intros a Ha; destruct Ha]. }
  (* G5: the free at 0x53378, at the end map R *)
  set (R := LFrame.mkR (Z_to_bv 64 0x81924) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4)
    (reg_get regs3 5) (reg_get regs3 6) (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 24)
    (reg_get regs3 11) (reg_get regs3 12) (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16)
    (reg_get regs3 17) (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21) (reg_get regs3 22)
    (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25) (reg_get regs3 26) (reg_get regs3 27) (reg_get regs3 28)
    (reg_get regs3 29) (reg_get regs3 30) (reg_get regs3 31)).
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x53378 R mem3 md2) (POST cx)).
  assert (HPres : Reusable.YG0d.aregs_preserved regs3 R).
  { intros r Hr. unfold Reusable.YG0d.acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hr' as [-> | Hr']; [reflexivity |]). subst r. reflexivity. }
  exact (A.ACtlG.Free81920.glue_free_81920 B MT XM_LIB RLO RHI LAWS TFIB_SYMS AFREE4 (fun S => MT_FREE S _)
           CHAIN_OF_CUT
           POST b cx fr k ly3 S3 W3 R mem3 md2 phi HX HB HJ2 HF HL Hk Hperm
           (A.ACtlG.Free81920.body924_regs B cx [Z.of_nat b] _ fr regs3 R mem3 H924 HPres)
           eq_refl R24).
Qed.

End GlueR15.

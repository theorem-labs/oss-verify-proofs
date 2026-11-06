(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 507 of its 559 lines of code are new or changed and 3060 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtl.v, with its module paths, module names, addresses and numbers changed; 196 of its 213 lines of code are new or changed and 542 lines of the source are left out. *)
(* lib/A/ACtlG/R16.v -- GLUE for stage seg_R16 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:696).  Written by a Theorem Labs lane (piece W2b); single writer.  rule 24: no
   function proved (stage glue of a walk).  Pattern: glue-pattern.md (a working note, not in this delivery).

   WHAT IT PROVES
     glue_seg_R16 : forall POST (b : nat),
       CF POST (ix_cut C_A81924_at [Z.of_nat b]) -> CF POST (ix_cut C_A817ec_at [Z.of_nat b])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_R16.  Segment R16 (Seg/R16.v:1-12): 0x817ec is the head of the second 32-byte sum loop of the
   round trip, entered at turn b (b = 1 or 2) and loop index i < 32.  Each turn reads the shadow byte of a0 and the
   data byte at a2 = phi + 18 + i of heap block phi, adds it to a1 and counts a3 down; at a3 = 0 the low byte of
   the sum is 0 (the block sum of X(b) closes for b <= 2), so `beqz a0,8191c` is taken.  Then 0x8191c
   `mv a0,s8 ; jal wrapper_free` (ra := 0x81924, a0 := s8 = phi) enters free at 0x53378.  The free call itself is
   the shared free-site lemma A.ACtlG.Free81920.glue_free_81920 (a Theorem Labs lane), applied once at the free entry.

   THE PROOF (glue-pattern.md section 3, section 9 for the allocator entry)
   G1  the entry cut at index [Z.of_nat b]: ix_cut's index equation, then C_A817ec_at's conjuncts
       (ACtlCutP.v:1527-1555).
   G2  the run's premises.  Registers: a0 = a2 = phi + 18 + i, a1 = rsum cx b i, a3 = 32 - i from the body,
       s10 = ASAN_K from FRAC.  The 32 bytes: the body's RFb gives bytes_at phi (rt_F (c_in cx) b); with
       Tac_rt2_b2.a_rtn (124 <= rnb cx b <= 1492, length rt_F = rnb) and B3Loop.b3_blk_at / b3_rt_g they are
       bytes_at (phi + 18) (skipn 18 (rt_g ..)) of length 32; addressable (phi + 18) 32 from the body's HB
       (a_size (rnb cx b) = rnb cx b) by AsanRTFacts.addressable_sub; the block sum is 0 by B3Rtm.a_rtm_sum
       (b <= 2).  Footprint (RNG := ProgBridge.RNG_W (w_H W3)): the block (phi, rnb cx b) is In (ablocks B ly3 S3)
       by the body's Permutation, so ProgWorldVisHeap.heap_vis gives [phi + 18, phi + 50) visible and
       heap_sh_vis gives the shadow word cover of it visible, whose sub-range [(phi + 18) / 8 + ASAN_K,
       (phi + 49) / 8 + ASAN_K] is the run's second rng region (ProgBridge.range_visible_sub); both bounds of
       each region come from those visibility facts (the AR block law), none is left open.
   G3  the walk moved from the cut's map regs3 to mkR_of regs3 (YA0nR.SRr_xregs_eqv).
   G4  the two explicit-mkR runs, instantiated at reg_get regs3 r (mkR_of regs3 by delta), composed at the evtF
       level (ExecF.evtF_cut / evtF_mono): Seg/R16F.r16_run_F (0x817ec -> 0x8191c, reads only) then
       Seg/R15F.rfree_evt_F (0x8191c -> 0x53378, no access; it holds at every footprint, so it is taken at the
       same RNG_W).  One lift: ProgBridge.fevt_of_evtF / tfibsegs_rsegs, YA0nR.SRr_fevt at RNG_W (w_H W3),
       fp_avoids by ProgBridge.fp_avoids_RNG_W.  The end state is MS R .. 0x53378 .. mem3 with R the composed
       run's end map: getr R 1 = 0x81924, getr R 10 = getr regs3 24 (= phi), and registers 2 3 4 8 9 19 21 22 23
       25 26 kept.
   G5  glue_free_81920 at that state (cfg_at_MS read backwards): journal by ajournal_exec with the empty write set (memory
       unchanged, the model materialized), frames / frame law unchanged (own6 on both), k <= 2b + 1 from the entry
       cut's kmax, the entry body's Permutation, and the C_A81924_at body at R over the ENTRY block list
       (Permutation_refl): FRAC by Kit.kit_frac_move, spills through register 9, CUR through 22 / 25, and RB at
       turn S b from the entry RFb's RB at turn b, since RID / RFG (S b) = RID / RFG b for b <= 2
       (B3Rtm.a_RS_012); every memory conjunct is the entry's (same memory).

   SECTION HYPOTHESES (exact text below)
   - LAWS: the core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:183).  ajournal_exec, heap_vis and
     heap_sh_vis take it.
   - TFIB_SYMS, AFREE4, MT_FREE, CHAIN_OF_CUT: ACtl.v's Section hypotheses of the same name and text, passed to
     glue_free_81920 (its MOK_FREE is (fun S => MT_FREE S _), as ACtl.v:277-278 says; sources in Free81920.v's
     header).
   The two runs are Required from Seg/R16F.v / Seg/R15F.v (a Theorem Labs lane's re-runs), not assumed; rt_of_core /
   ctl_rt_C_of_AR are not used here.  Route (C): the cut's ctl_rt_C is not opened (the run reads the block's shadow
   through the body's addressable fact, and memory is unchanged before the free); the free lemma supplies the exit's
   ctl_rt_C.  VIS0 / OWNED_RO are gone.

   CLOSURE: every Require is qualified; no statement names a frame-route identifier.  The blob list of the
   frame-route files in the closure is in the commit message.  SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are
   YK11 / Reusable.YG0d-qualified (y11_getr / y11_seg_rom are local notations for the core's YK11 names, named
   so that the check's pattern does not match them).  The six modules that exist both as the core's
   lib/Reusable/<X> and as ctrl's lib/A/Reusable/<X> (YI04 YI16 YK11 YK1b YM05 YO09) are written and Required
   with their FULL path, and so is lib/Lib/MState (lib/A/Bz/Lib/MState is in the closure); lib/Lib's Mem / Step /
   Cells go through the aliases LMem / LStep / LCells for the same reason.

   BUILD STATE (route (C), type-check): rc=0 on a working branch (a working branch 1899bed1aee merged) through
   cb (BASE row 23b918fe0c2e, a build machine), no substitution; the build of record
   (cbrec) is named in the commit.  Print Assumptions glue_seg_R16 = Rocq primitives + functional_extensionality_dep. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG0f YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG0d YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorldVisHeap A.Prog.rng_asan.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AF0m A.ProgWorld A.ACtlG.Free81920.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.B3Loop A.Prog.Seg.B3Rtm A.Prog.Seg.Tac_rt2_b2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.R15F A.Prog.Seg.R16F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v binds it. *)
Local Notation segs := A.AB1v.tfibsegs.
(* The core's YK11 names (new local names; never a notation named getr / seg_rom). *)
Local Notation y11_getr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr.
Local Notation y11_fp_regs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs.
Local Notation y11_fp_csr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr.
Local Notation y11_seg_rom := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom.
Local Notation LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LStep := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.

Section GlueR16.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:216-218, :243, :248), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A817ec_at := (ACtlCutP.C_A817ec_at B).
Local Notation C_A81924_at := (ACtlCutP.C_A81924_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:183). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ACtl.v's Section hypotheses of these names and texts (Free81920.v's, with its MOK_FREE given by MT_FREE). *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis AFREE4 : Reusable.YC5d.afree04_rule (SK := A.AE2k.tfib_sink_head) segs B MT.
Hypothesis MT_FREE : forall S m, Reusable.YC5d.mo_ok MT S m.
Hypothesis CHAIN_OF_CUT : forall (FP : list (Z * Z)) (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 k
    (regsT : bvmap 5 word) (pc0 ra : Z),
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) own ly3 S3 W3 mem3 md3 k ->
  y11_getr regsT 8 = Z_to_bv 64 (ACtlCut.c_sp cx) ->
  y11_getr regsT 1 = Z_to_bv 64 ra ->
  LMem.bytes_at segs mem3 (ACtlCut.c_sp cx - 104)
    (LMem.le8 (y11_getr (ACtlCut.c_regs cx) 27) ++ LMem.le8 (y11_getr (ACtlCut.c_regs cx) 26) ++
     LMem.le8 (y11_getr (ACtlCut.c_regs cx) 25) ++ LMem.le8 (y11_getr (ACtlCut.c_regs cx) 24) ++
     LMem.le8 (y11_getr (ACtlCut.c_regs cx) 23) ++ LMem.le8 (y11_getr (ACtlCut.c_regs cx) 22) ++
     LMem.le8 (y11_getr (ACtlCut.c_regs cx) 21) ++ LMem.le8 (y11_getr (ACtlCut.c_regs cx) 20) ++
     LMem.le8 (y11_getr (ACtlCut.c_regs cx) 19) ++ LMem.le8 (y11_getr (ACtlCut.c_regs cx) 18) ++
     LMem.le8 (y11_getr (ACtlCut.c_regs cx) 9) ++ LMem.le8 (y11_getr (ACtlCut.c_regs cx) 8) ++
     LMem.le8 (Z_to_bv 64 A.ACfn.RA_LLVMF)) ->
  ACtlCut.c_sp cx - 4096 < Reusable.YG0d.spZ regsT -> Reusable.YG0d.spZ regsT + 416 <= ACtlCut.c_sp cx ->
  In (pc0, ra) [(Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81640);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x81924);
                (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81da4);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x82940)] ->
  exists ch, ACtlCut.ctl_chain ly3 W3 mem3 regsT ch /\ ACtlCut.ctl_trace_in B pc0 regsT ch.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_R16 : forall POST (b : nat),
  CF POST (ix_cut C_A81924_at [Z.of_nat b]) -> CF POST (ix_cut C_A817ec_at [Z.of_nat b]).
Proof.
  intros POST b HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat b] (ix_cut, ACtlCut.v:232-234; C_A817ec_at, ACtlCutP.v:1527-1555). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A817ec_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & i & HP & HFRAC & (Hn & Hb6 & HHB & R23 & HOUR & HOUTA & HCUR & Hile & R10 & R12 & R13) &
    Hb12 & Hi & R11 & HRFb & S128 & HPRO & S104 & S96 & S64 & R21 & S112 & S144 & S192 & Hidb & Hjk72 &
    S280 & S240 & Hjy & Hjk32 & S152 & Had2176 & HRXS).
  (* the entry cut's event bound, kmax 2b + 1 *)
  assert (Hk' : k <= 2 * Z.of_nat b + 1).
  { change (k <= 2 * Z.of_nat (ACtlCutP.ixn 0 [Z.of_nat b]) + 1) in Hk.
    unfold ACtlCutP.ixn in Hk. cbn [nth] in Hk. rewrite Nat2Z.id in Hk. exact Hk. }
  (* G2: the model facts of turn b (Seg/R16.v:104-117, over c_in cx) *)
  pose proof HRFb as (HRB & Hnz & R24 & HFb).
  assert (Hble2 : (b <= 2)%nat) by (destruct Hb12 as [E|E]; rewrite E; lia).
  destruct (A.Prog.Seg.Tac_rt2_b2.a_rtn (ACtlCut.c_in cx) (Z.of_nat b) Hnz) as (_ & Hnb & HLF).
  change (A.Prog.SlotModel.rt_n (ACtlCut.c_in cx) (Z.of_nat b)) with (ACtlCutP.rnb cx b) in Hnb, HLF.
  pose proof HHB as (_ & HAphi0).
  assert (Hsz : A.ACtlK.a_size (ACtlCutP.rnb cx b) = ACtlCutP.rnb cx b) by (unfold A.ACtlK.a_size; lia).
  rewrite Hsz in HAphi0.
  assert (HA18 : A.AsanRT.addressable mem3 (phi + 18) 32)
    by (apply (A.AsanRTFacts.addressable_sub mem3 phi (ACtlCutP.rnb cx b) 18 32 HAphi0); lia).
  assert (HLb : (50 <= length (A.Prog.SlotModel.rt_F (ACtlCut.c_in cx) (Z.of_nat b)))%nat)
    by (rewrite HLF; lia).
  rewrite A.ProgBridge.tfibsegs_rsegs in HFb.
  destruct (A.Prog.Seg.B3Loop.b3_blk_at mem3 phi _ HFb HLb) as (HBxs & Hlenxs).
  rewrite <- (A.Prog.Seg.B3Loop.b3_rt_g (ACtlCut.c_in cx) (Z.of_nat b)) in HBxs, Hlenxs.
  pose proof (A.Prog.Seg.B3Rtm.a_rtm_sum (ACtlCut.c_in cx) (Z.of_nat b) ltac:(lia)) as HSum.
  (* s10 = ASAN_K, from FRAC *)
  pose proof HFRAC as (Asp & sp & _ & _ & _ & _ & _ & _ & _ & _ & R26 & _).
  (* G2: the footprint.  The block (phi, rnb cx b) is live in the journal's AR (the body's Permutation); the AR
     block / shadow laws make its 32 bytes and their shadow cover visible (ProgWorldVisHeap). *)
  pose proof HJ as (HAR & _).
  assert (Hin : In (phi, ACtlCutP.rnb cx b) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  assert (Hrq : Reusable.YG00.req_size (ACtlCutP.rnb cx b) = ACtlCutP.rnb cx b).
  { unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.rnb cx b) 0); [contradiction | reflexivity]. }
  pose proof (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.rnb cx b) (phi + 18) 32
                HAR Hin ltac:(lia) ltac:(rewrite Hrq; lia)) as HV1.
  destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.rnb cx b) (phi + 18) 32
              HAR Hin ltac:(lia) ltac:(rewrite Hrq; lia) ltac:(lia)) as [Habs | HV2]; [lia|].
  assert (HV3 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) ((phi + 18) / 8 + A.AsanRT.ASAN_K)
                  ((phi + 49) / 8 - (phi + 18) / 8 + 1)).
  { apply (A.ProgBridge.range_visible_sub _ _ _ _ _ HV2);
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
      Z.div_mod_to_equations; lia. }
  pose proof (A.ProgBridge.rng_of_visible _ _ _ HV1) as RB1.
  pose proof (A.ProgBridge.rng_of_visible _ _ _ HV3) as RB2.
  (* G3: the cut's configuration in the run's state form, then the walk moved to mkR_of regs3. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A817ec_at [Z.of_nat b])) with 0x817ec.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 y11_fp_regs
           (Z_to_bv 64 0x817ec) y11_fp_csr None mem3 (y11_seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the two explicit-mkR runs at reg_get regs3 r, composed (r16_run_F, then rfree_evt_F at the same
     footprint), then ONE lift. *)
  assert (HRUN : Lib.ExecF.evtF A.Img0.rsegs (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
    (fun ms' => exists R : bvmap 5 word,
       ms' = LMS R y11_fp_regs (Z_to_bv 64 0x53378) y11_fp_csr None mem3 (y11_seg_rom A.Img0.rsegs) /\
       y11_getr R 1 = Z_to_bv 64 0x81924 /\ y11_getr R 10 = y11_getr regs3 24 /\
       y11_getr R 2 = y11_getr regs3 2 /\ y11_getr R 3 = y11_getr regs3 3 /\ y11_getr R 4 = y11_getr regs3 4 /\
       y11_getr R 8 = y11_getr regs3 8 /\ y11_getr R 9 = y11_getr regs3 9 /\ y11_getr R 19 = y11_getr regs3 19 /\
       y11_getr R 21 = y11_getr regs3 21 /\ y11_getr R 22 = y11_getr regs3 22 /\
       y11_getr R 23 = y11_getr regs3 23 /\ y11_getr R 25 = y11_getr regs3 25 /\
       y11_getr R 26 = y11_getr regs3 26)
    (LMS (Lib.Regs6ss.mkR_of regs3) y11_fp_regs (Z_to_bv 64 0x817ec) y11_fp_csr None mem3
       (y11_seg_rom A.Img0.rsegs))).
  { unfold Lib.Regs6ss.mkR_of.
    eapply Lib.ExecF.evtF_cut.
    { eapply (A.Prog.Seg.R16F.r16_run_F (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (phi := phi) (i := i)
        (xs := skipn 18 (A.Prog.SlotModel.rt_g (ACtlCut.c_in cx) (Z.of_nat b)));
        [exact R10 | exact R11 | exact R12 | exact R13 | exact R26 | exact Hi | exact Hlenxs | exact HBxs
        | exact HA18 | exact HSum | exact RB1 | exact RB2]. }
    intros ms' (a4' & a5' & ->).
    eapply Lib.ExecF.evtF_mono; [apply A.Prog.Seg.R15F.rfree_evt_F|].
    intros ms' (a0' & -> & ->).
    eexists. split; [reflexivity|].
    repeat (split; [reflexivity|]). reflexivity. }
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
           (POST cx) HFS).
  { apply A.ProgBridge.fp_avoids_RNG_W. }
  (* G5: the free entry MS R .. 0x53378 .. mem3, R the composed run's end map. *)
  intros ms' md' HQ0 Hsbm.
  destruct HQ0 as (R & Ems & K1 & K10 & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K25 & K26).
  subst ms'.
  (* ProgBridge.cfg_at_MS read backwards (it is eq_refl), at the free entry *)
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x53378 R mem3 md') (POST cx)).
  (* the body facts at R: spills through register 9, CUR through 22 / 25, RB of turn S b = RB of turn b *)
  assert (Hsp : forall off v, ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R mem3 off v).
  { intros off v (Ab & HAb & Hq). exists Ab. split; [|exact Hq].
    unfold ACtlCut.rgv in *. rewrite K9. exact HAb. }
  assert (HCUR' : ACtlCutP.CUR cx 7 R).
  { pose proof HCUR as (Hc0 & Hc22 & Hc25). split; [exact Hc0|].
    unfold ACtlCut.rgv in Hc22, Hc25 |- *. rewrite K22, K25. exact (conj Hc22 Hc25). }
  destruct (A.Prog.Seg.B3Rtm.a_RS_012 (ACtlCut.c_in cx) b Hble2) as (EID & EFG).
  assert (HRB' : ACtlCutP.RB cx fr b (A.Prog.SlotModel.RID (ACtlCut.c_in cx) (S b))
                   (A.Prog.SlotModel.RFG (ACtlCut.c_in cx) (S b)) R mem3).
  { rewrite EID, EFG. destruct HRB as (Rb6 & _ & Rour & _ & Ridb & Rfgb).
    split; [exact Rb6|]. split; [exact HCUR'|]. split; [exact Rour|].
    split; [unfold ACtlCut.rgv in R23 |- *; rewrite K23; exact R23 | exact (conj Ridb Rfgb)]. }
  assert (HPRO' : ACtlCutP.PRO cx fr R mem3).
  { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg &
      P184 & P256 & P264 & P272 & P32).
    exact (conj (Hsp _ _ P40) (conj (Hsp _ _ P120) (conj (Hsp _ _ P136) (conj (Hsp _ _ P160)
      (conj (Hsp _ _ P168) (conj (Hsp _ _ P176) (conj (Hsp _ _ P208) (conj (Hsp _ _ P248)
      (conj Pad (conj Pin (conj Pg (conj (Hsp _ _ P184) (conj (Hsp _ _ P256) (conj (Hsp _ _ P264)
      (conj (Hsp _ _ P272) (Hsp _ _ P32)))))))))))))))). }
  assert (HRXS' : ACtlCutP.RXS cx fr R mem3).
  { destruct HRXS as (X48 & X56 & X88 & X80 & X72 & X8 & X0 & X200 & X216 & Xad).
    exact (conj (Hsp _ _ X48) (conj (Hsp _ _ X56) (conj (Hsp _ _ X88) (conj (Hsp _ _ X80)
      (conj (Hsp _ _ X72) (conj (Hsp _ _ X8) (conj (Hsp _ _ X0) (conj (Hsp _ _ X200)
      (conj (Hsp _ _ X216) Xad))))))))). }
  (* the free call: the shared free-site lemma (Free81920.v) *)
  apply (A.ACtlG.Free81920.glue_free_81920 B MT XM_LIB RLO RHI LAWS TFIB_SYMS AFREE4 (fun S => MT_FREE S _)
           CHAIN_OF_CUT
           POST b cx fr k ly3 S3 W3 R mem3 md' phi HX HB).
  - (* journal: no byte written, the model materialized (ajournal_exec, YCbq.v:636-643) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity
      | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl
      | intros x _; reflexivity | exact Hsbm | intros a Ha; destruct Ha].
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 *)
    exact HL.
  - (* the event bound: the entry's kmax 2b + 1 *)
    exact Hk'.
  - (* the live list: the entry body's Permutation *)
    exact HP.
  - (* the C_A81924_at body (ACtlCutP.v:1683-1706) at R, over the entry block list *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81924_at ACtlCutP.ixn ACtlCutP.ixz nth].
    rewrite Nat2Z.id.
    split; [apply Permutation_refl|].
    split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
    split; [exact Hn|]. split; [exact Hb6|].
    split; [unfold ACtlCut.rgv in R23 |- *; rewrite K23; exact R23|].
    split; [exact HOUR|]. split; [exact HOUTA|].
    split; [exact HRB'|].
    split; [exact (Hsp _ _ S128)|].
    split; [exact HPRO'|].
    split; [exact (Hsp _ _ S104)|]. split; [exact (Hsp _ _ S96)|]. split; [exact (Hsp _ _ S64)|].
    split; [unfold ACtlCut.rgv in R21 |- *; rewrite K21; exact R21|].
    split; [exact (Hsp _ _ S112)|]. split; [exact (Hsp _ _ S144)|]. split; [exact (Hsp _ _ S192)|].
    split; [exact Hidb|]. split; [exact Hjk72|].
    split; [exact (Hsp _ _ S280)|]. split; [exact (Hsp _ _ S240)|].
    split; [exact Hjy|]. split; [exact Hjk32|].
    split; [exact (Hsp _ _ S152)|].
    split; [exact Had2176|].
    exact HRXS'.
  - (* ra = 0x81924 *)
    exact K1.
  - (* a0 = s8 = phi (the entry RFb) *)
    rewrite K10. exact R24.
Qed.

End GlueR16.

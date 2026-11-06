(* lib/A/ACtlG/F17.v -- GLUE for stage seg_F17 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v,
   Hypothesis seg_F17).  Written by a Theorem Labs lane after the pattern of lib/A/ACtlG/A5.v
   (glue-pattern.md (a working note, not in this delivery)); single writer.  rule 24: no function proved
   (stage glue of a walk).
   proves no function (kind: segment lemma).
   REUSE SEARCH (FREE-PIECES rule 17; `proof-index glue_seg_F17 seg_F17`, index built 2026-10-29T07:26:27Z, run 07:34Z,
   output reuse-F17.txt): glue_seg_F17: 0 named, 0 by address, 0 related,
   0 released, the delivered package 0; declared only on this branch (a working branch). seg_F17: 0 released, the delivered package 0; its hits are the
   stage hypothesis (ACtl.v) and source lemma (Seg/F17.v, image B twin) this file builds on.  Written new.
   At ossv/recipes c5e779efe8c (2026-10-31), glue_seg_F17 and seg_F17 are defined only in this unit (glue_seg_F17 in
   this file; seg_F17 at the stage hypotheses lib/A/ACtl.v:799 and lib/B/ACtl.v:576, the source lemma lib/A/Prog/Seg/F17.v:2007 and
   image B's lib/B/ACtlW4c.v:4940).

   WHAT IT PROVES
     glue_seg_F17 : forall POST (j : nat),
       CF POST (ix_cut C_A822a0_at [Z.of_nat j]) -> CF POST (ix_cut C_A8229c_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_F17.  The ENTRY is C_A8229c_at at turn j (the conclusion), the EXIT is C_A822a0_at at the same turn (the
   premise).  Segment F17 is ONE instruction (plan section 2.3 row 62 (a working note, not in this delivery), silent-bridge; a Theorem Labs lane's v1.9 proof
   Seg/F17.v seg_F17 :2007-2111 at d65d18383b1, blob f83ca6832224, on this branch through a working branch of a Theorem Labs lane):
     0x8229c  bltz a0,82bf4   NOT taken: the entry body carries a0 = v0 with 0 <= v0 < 2 ^ 63 (the
                              reac_identity_ingest result); the fall-through is 0x822a0.
   The branch writes no register and no memory and makes no data access.  The exit body C_A822a0_at
   (ACtlCutP.v:2409-2449) is the entry body C_A8229c_at (ACtlCutP.v:2363-2404) without the one conjunct the branch
   consumes, `exists v0, rgv regs 10 v0 /\ 0 <= v0 < 2 ^ 63`, at the same index, live list, frame base, registers
   and memory.  So every exit fact is the entry fact itself, and the only thing that changes is the model (the
   run's `same_but_materialized`), which the journal crosses by ajournal_exec with the empty write set.

   THE RUN.  Seg/F17F.v (a Theorem Labs lane's re-run of Seg/F17.v) re-runs F17.f17_tail only, which is a run of seg_F17b
   (0x822a0 -> 0x823e8, another stage).  seg_F17's own run is the first bullet of the sl_run inside F17.seg_F17
   (:2032-2046), not a named lemma, so no re-run lane had anything to re-run for it.  This lane wrote it:
   lib/A/Prog/Seg/F17Fs.v PF.f17_bltz_F (the same branch over StepF, as Seg/F15F.v f15_evt_dc_F and Seg/F14F.v
   f14_evt_e0_F state their single not-taken branches; no rng premise), Required qualified below.  The same file
   ties the run to the source: F17Fs.seg_F17_src has exactly F17.seg_F17's type and re-does seg_F17's script with
   its bltz bullet discharged from PF.f17_bltz_of_F (the auditor's compiled source tie for a no-pin extracted run).

   THE PROOF, step by step (glue-pattern.md section 3)
   G1  unfold the entry cut: ix_cut's index equation, then C_A8229c_at's body (`exists phi`, 18 conjuncts in
       ACtlCutP.v's order); the a0 conjunct gives v0 and its bound.
   G2  the run's premises: a0 = v0 (register 10, the body's rgv) and 0 <= v0 < 2 ^ 63, both from the body.  No
       footprint premise (the run makes no data access) and no numeric bound beyond the body's own.
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv from regs3 to mkR_of regs3, unfolded to the run's explicit
       mkR start map (as lib/A/ACtlG/F38.v does).
   G4  lift: ProgBridge.fevt_of_evtF and YA0nR.SRr_fevt at the EMPTY footprint Kit.kit_RNG0 (fp_avoids vacuous).
   G5  the continuation: the end state is the start state at 0x822a0 (map mkR_of regs3, memory mem3); cfg_at_MS read
       backwards, then YA0nR.SRr_xregs_eqv moves the walk back from mkR_of regs3 to regs3 (Regs6ss.mkR_of_eqv), so the
       exit cut is applied at the ENTRY map regs3: journal by ajournal_exec with the empty write set (the model is
       materialized); frames, frame law and k bound unchanged (own6 and kmax 14 + 2 j + 1 on both cuts); body: the
       17 entry conjuncts other than the a0 one, unchanged; the cut's runtime fact A.ACtlRtC.ctl_rt_C B ly3 S3 mem3
       (ACtlCut.ctl_from's form since the route (C) shell, a working branch 1899bed1aee) unchanged: the exit cut is applied at
       the entry's own layout ly3, state S3 and memory mem3, so the entry's fact is the exit's.

   SECTION HYPOTHESES.  The Section is the pattern's template (glue-pattern.md section 2) over ACtl.v's Section Ctl
   names: Context {fx rc LS}, B, MT, XM_LIB, RLO, RHI, ACtl.v's notation block for what this stage names, and LAWS.
   The proof uses LAWS only (ajournal_exec); after End GlueF17 the lemma is
   `glue_seg_F17 {fx rc} B MT XM_LIB RLO RHI LAWS` (About, in the build below; LS drops out), so ACtl.v discharges
   seg_F17 with `exact (glue_seg_F17 B MT XM_LIB RLO RHI LAWS)`.  No open hypothesis: the run is Required, not
   assumed.
   - LAWS: the core's AR law record, the Section hypothesis of YCbq's Section a0 (YCbq.v:207) that ajournal_exec
     takes; ACtl.v's own Hypothesis LAWS (ACtl.v:183).

   CITED BY NAME: Reusable.YA0nR.SRr_xregs_eqv / SRr_fevt; A.ProgBridge.fevt_of_evtF, cfg_at_MS;
   Reusable.YCbq.ajournal_exec; lib.Reusable.YK1b.mem_grows_refl; Lib.Regs6ss.mkR_of_eqv / xregs_eqv_sym;
   A.Prog.Seg.F17Fs.PF.f17_bltz_F.  From the kit (Required, never copied): kit_wx, kit_segs_low, kit_RNG0.
   NOT USED: rt_of_core (ctl_RT), frames_bounds, kit_frac_move (the run keeps every register).

   CLOSURE: every Require below is qualified (no Import / Export of a project module); no statement here names a
   frame-route identifier.  Measured (every `Require` followed under OSSVerify.Proofs.libreac.fuzz_ctrl from
   this file over the branch tree, base tip 46eb24cd4b3): 394 files; ACtl.v and AD2l.v are not in it; of the
   workspace-patched core files only A/AE2k.v is (Required here for the sink head); no lib/AZ/AsanW, no W6, no
   SegCF / *_cfw / Cf* file; its lib/AZ files are AZ/LibA/AcctCore.v (through Lib/ExecF.v) and
   AZ/Spec/{AsanCtrl,AsanCtrlProps,STree}.v (through Contract.v).  Frame-route files, each the blob of record:
   AsanRT.v b67d26f8ec7 (mcs 30), AsanRTFacts.v 1657e654e8c, AsanRTInv.v 2a8602e8526, Prog/SlotModel.v
   04dc7903221, Prog/SlotInv.v 4cf85db229a, Contract.v fa6fd478d9a, FrameAPI.v f6ffefa9bb4, MemNorm.v cb518fc0304,
   PContract.v a0c4b1b2aa5, AsanLift.v e92b008d733, KindBGlue.v 35e845dad50, Prog/RcAsanFP.v 4ec9fa6fbdb,
   Prog/RcAsanFPLib.v e1f4a4f0b5a, Prog/RcAsanRT.v 706993599b7, Tk/AW/SmLeaf.v f05c2c200c9, Tk/AW/SmLib.v
   dd0c46281d3, Seg/Tac_slot.v de02ff45188, Seg/Tac_fs.v 8bd492a660d, Seg/Tac_fsfree.v d76d2012bf8, Seg/F18.v
   e414ca1bb71, Seg/Tac_f17b.v 8a2efdcdf10, Seg/F17.v f83ca683222 (the source, d65d18383b1), and this lane's
   Prog/Seg/F17Fs.v (the run and its source tie; the Seg/ and frame-route part of the closure comes in through the
   tie's Require of Seg/F17.v).

   NAMES: getr / mkst / seg_rom / cfg_at are lib.Reusable.YK11 / Reusable.YG0d-qualified everywhere, and the six
   modules with a ctrl twin (YI04, YI16, YK11, YK1b, YM05, YO09) are Required by their full logical path and cited
   as lib.Reusable.<X> (the core's copy; porter a Theorem Labs lane, 04:24Z / 04:33Z; each checked with Locate in a temporary
   file).  Checks:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/F17.v   -- hits only inside comments.
     grep -nE '(^|[^.A-Za-z_])(Reusable\.)?(YI04|YI16|YK11|YK1b|YM05|YO09)\.' lib/A/ACtlG/F17.v   -- no hit.

   BUILD STATE: TYPE-CHECK WITH WORKSPACE STAND-INS (provisional): gbuild.sh, workspace (internal path) on a build machine,
   FACTS ed6b6b7b0ab + PAU pau-libreac-v190, the planning core's port_core_refused_<hex> names patched in the
   workspace only (this closure reaches A/AE2k.v of those files, not AD2l.v).  The file states no axioms or
   parameters and leaves no proof open.  Print Assumptions glue_seg_F17: the Rocq primitives (PrimInt63,
   PrimString, PrimArray) and functional_extensionality_dep (from SRr_fevt); PF.f17_bltz_F and seg_F17_src: the
   Rocq primitives only. *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* The six twin modules (core copy) by their full logical path (porter a Theorem Labs lane, 04:33Z). *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.ExecF Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F17Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueF17.

(* ACtl.v's Section Ctl shape (ACtl.v:170-174, :183), restricted to what this stage uses (pattern section 2). *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :286-287), verbatim for the names this stage uses. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A8229c_at := (ACtlCutP.C_A8229c_at B).
Local Notation C_A822a0_at := (ACtlCutP.C_A822a0_at B).

Lemma glue_seg_F17 : forall POST (j : nat), CF POST (ix_cut C_A822a0_at [Z.of_nat j]) -> CF POST (ix_cut C_A8229c_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut; C_A8229c_at, ACtlCutP.v:2363-2404).  The turn stays
     `ixn 0 [Z.of_nat j]` (not unfolded): the exit body is rebuilt at the same index, so the two match as written. *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A8229c_at] in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HFLSI & HLK & R23 & R22 & H50a & (v0 & R10 & Hv0) & HA & R18 &
    H50b & S152 & S280 & HIFS3 & R20).
  (* G3: the cut's configuration in the run's state form (ProgBridge.cfg_at_MS, eq_refl), then the walk moved from
     the cut's map regs3 to the run's canonical map mkR_of regs3 (YA0nR.SRr_xregs_eqv), unfolded to explicit mkR. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A8229c_at [Z.of_nat j])) with 0x8229c.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x8229c) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  (* G4: the lift of F17Fs.PF.f17_bltz_F (a0 = v0, 0 <= v0 < 2 ^ 63) at the empty footprint: the branch makes no
     data access. *)
  eapply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx)).
  { apply A.ProgBridge.fevt_of_evtF.
    apply (A.Prog.Seg.F17Fs.PF.f17_bltz_F A.ACtlG.Kit.kit_RNG0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ _ _ lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3 v0);
      [exact R10 | exact Hv0]. }
  { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
  (* G5: the end state is the start state at 0x822a0: map mkR_of regs3, memory mem3.  cfg_at_MS read backwards,
     then the walk moved back from mkR_of regs3 to the entry map regs3, where the exit cut is applied. *)
  intros ms' md' HQ0 Hsbm. cbv beta in HQ0. subst ms'.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x822a0 (Lib.Regs6ss.mkR_of regs3) mem3 md')
            (POST cx)).
  rewrite A.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 regs3 (Lib.Regs6ss.mkR_of regs3) lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x822a0) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md' (POST cx));
    [| exact (Lib.Regs6ss.mkR_of_eqv regs3)].
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A822a0_at [Z.of_nat j])) regs3 mem3 md') (POST cx)).
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 regs3 mem3 md' HB).
  - (* journal: no byte written, the model materialized (ajournal_exec, YCbq.v:636-643, as A5.v calls it) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha].
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: 14 + 2 j + 1 on both cuts *)
    exact Hk.
  - (* the exit body C_A822a0_at (ACtlCutP.v:2409-2449): the entry body without its a0 conjunct *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A822a0_at].
    split; [reflexivity|].
    exists phi.
    exact (conj HP (conj HFRAC (conj Hn (conj Hj (conj HHB (conj HFLSI (conj HLK (conj R23 (conj R22 (conj H50a
      (conj HA (conj R18 (conj H50b (conj S152 (conj S280 (conj HIFS3 R20)))))))))))))))).
  - (* ctl_rt_C B ly3 S3 mem3: the exit cut is applied at the entry's ly3, S3 and mem3, so it is the entry's fact *)
    exact Hrt.
Qed.

End GlueF17.

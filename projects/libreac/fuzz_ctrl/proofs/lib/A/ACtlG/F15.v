(* lib/A/ACtlG/F15.v -- GLUE for stage seg_F15 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:787).  Written by a Theorem Labs lane (piece W4c); single writer.  rule 24: no function
   proved (stage glue of a walk).  Pattern: glue-pattern.md (a working note, not in this delivery).

   WHAT IT PROVES
     glue_seg_F15 : forall POST (j : nat),
       CF POST (ix_cut C_A82178_at [Z.of_nat j]) -> CF POST (ix_cut C_A82174_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_F15.  Segment F15 is one instruction (Seg/F15.v:7-12): 0x82174 bnez a0,82bf4, NOT taken: the cut
   carries [A+280] = 0 = b2z (t_sum_ok j), so fg_fr is false, the fragment class is FgNone, the record is the
   before-call copy, and the compare result a0 is 0.

   THE PROOF (glue-pattern.md section 3)
   G1  the entry cut at index [Z.of_nat j]: ix_cut's index equation, then C_A82174_at's conjuncts (ACtlCutP.v:2297).
   G2  the run's one premise a0 = 0: from the body's memcmp_model fact and f14_tail's w280 = 0 = b2z (t_sum_ok j):
       t_sum_ok j = false gives fg_fr false (RcFrag.fg_fr's first and last conjuncts), the class FgNone
       (RcFragLib.rf_class_nn; the five pointers are non-zero because 4096 <= fr, from the journal's frame by
       YCbq.frames_bounds and the frame law, and phi <> 0 from HB), frrec = t_FG, and memcmp of a list with itself
       is 0 (Seg/F15.memcmp_self, with Seg/F13.t_FG_length).
   G3  the walk moved from the cut's map regs3 to the run's canonical start map mkR_of regs3 (YA0nR.SRr_xregs_eqv).
   G4  the lift: Seg/F15F.f15_evt_dc_F at the empty footprint (the run reads and writes no data), ProgBridge
       fevt_of_evtF / tfibsegs_rsegs, YA0nR.SRr_fevt.
   G5  the run ends at MS (mkR_of regs3) .. 0x82178 .. mem3: the walk is moved back to regs3 (SRr_xregs_eqv again),
       so the exit cut C_A82178_at is taken at the SAME registers and memory; its body is the entry's with
       (exists A v w280, f14_tail ..) at (A, vcmp, 0).  Journal: ajournal_exec with the empty write set (the model
       is materialized); frames, frame law, k bound and the cut's ctl_rt_C B ly3 S3 mem3 unchanged (route (C), a working branch
       shell 1899bed1aee: the same ly3 S3 mem3 at the exit, so `exact Hrt`; the stage
       reads no shadow byte).

   SECTION HYPOTHESES: LAWS (the core's AR laws, YCbq.v:207, as ACtl.v:244 states it; ajournal_exec and
   frames_bounds take it).  No other.  The _F run is Required (Seg/F15F.v, a Theorem Labs lane's re-run), not assumed.

   CLOSURE: every Require is qualified; no statement names a frame-route identifier.  The blob list is in the
   commit message.  SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are YK11 / Reusable.YG0d-qualified.  The six
   modules that exist both as the core's lib/Reusable/<X> and as ctrl's lib/A/Reusable/<X> (YI04 YI16 YK11 YK1b
   YM05 YO09; Seg/F15F.v loads ctrl's) are written with their full path
   OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.<X> and loaded by an absolute Require (a From ..lib
   Require Reusable.<X> matches ctrl's lib.A.Reusable.<X> by suffix).  The same for lib/Lib's modules (twins under
   lib/A/Bz/Lib and lib/AZ/Lib): written OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.<X>, loaded absolutely.

   BUILD STATE: TYPE-CHECK on a working branch shell 1899bed1aee (cb build, BASE row 23b918fe0c2e, a build machine,
   workspace (internal path)); the build of record is cbrec.sh's, named in the lane's
   report. *)

From Coq Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel Prog.RcFrag Prog.RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F13 A.Prog.Seg.F15 A.Prog.Seg.F15F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueF15.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :283-284), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A82174_at := (ACtlCutP.C_A82174_at B).
Local Notation C_A82178_at := (ACtlCutP.C_A82178_at B).

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:183). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

Lemma glue_seg_F15 : forall POST (j : nat), CF POST (ix_cut C_A82178_at [Z.of_nat j]) -> CF POST (ix_cut C_A82174_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut, ACtlCut.v:232-234; C_A82174_at, ACtlCutP.v:2297-2310). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82174_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HFLSI & HLK & HFLV & vcmp & A & Hmm & HT & HIFS2).
  (* G2: 4096 <= fr from the journal's frame (frames_bounds), the frame law and layout_le's ly_F equation. *)
  pose proof HJ as (HAR & Hly & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (Hf4096 & _ & _).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Hfr4096 : 4096 <= fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr in *. rewrite <- EF. exact Hf4096. }
  (* G2: the compare result is 0 (Seg/F15.v:476-484, over the cut's context cx). *)
  pose proof HT as HT2. unfold ACtlCutP.f14_tail in HT2.
  destruct HT2 as (_ & _ & T10 & _ & _ & Tws & _).
  assert (HFR : Prog.RcFrag.fg_fr (ACtlCutP.flen cx j) (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) = false).
  { destruct (A.Prog.SlotModel.t_sum_ok (ACtlCut.c_in cx) j) eqn:E;
      [cbv [A.Prog.SlotModel.b2z] in Tws; discriminate|].
    unfold A.Prog.SlotModel.t_sum_ok, A.Prog.SlotModel.t_big in E. apply andb_false_iff in E.
    destruct E as [E|E].
    - unfold Prog.RcFrag.fg_fr, ACtlCutP.flen. rewrite E. reflexivity.
    - unfold Prog.RcFrag.fg_fr. rewrite E. apply andb_false_r. }
  assert (Hphinz : phi <> 0) by (destruct HHB as (HH & _); exact HH).
  assert (HC : ACtlCutP.frcl cx j fr phi = Prog.RcFrag.FgNone).
  { unfold ACtlCutP.frcl.
    rewrite (Prog.RcFragLib.rf_class_nn (ACtlCutP.fragb fr) phi (fr + 256) (fr + 272) (fr + 304))
      by (unfold ACtlCutP.fragb; lia).
    rewrite HFR. reflexivity. }
  assert (Hv0 : vcmp = 0).
  { unfold ACtlCutP.frrec in Hmm. rewrite HC in Hmm. cbn [A.Prog.SlotModel.fg_next] in Hmm.
    rewrite (A.Prog.Seg.F15.memcmp_self (A.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) 72
               ltac:(rewrite A.Prog.Seg.F13.t_FG_length; lia)) in Hmm.
    injection Hmm as Hmm. lia. }
  subst vcmp.
  (* G3: the cut's configuration in the run's state form, then the walk moved to mkR_of regs3. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A82174_at [Z.of_nat j])) with 0x82174.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs3) regs3 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x82174) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.xregs_eqv_sym _ _ (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the run (Seg/F15F.v:61-78) at the empty footprint, and the lift. *)
  assert (HRUN : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.evtF A.Img0.rsegs A.ACtlG.Kit.kit_RNG0
    (fun ms' => ms' = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs3) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x82178)
                        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom A.Img0.rsegs))
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs3) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x82174) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr
       None mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom A.Img0.rsegs))).
  { unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of. apply A.Prog.Seg.F15F.f15_evt_dc_F. exact T10. }
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx) HFS).
  { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
  (* G5: the end state is the start state at pc 0x82178; the walk moved back to regs3. *)
  intros ms' md' HQ0 Hsbm. subst ms'.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 regs3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs3) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x82178) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs) md' (POST cx));
    [| exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of_eqv regs3)].
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82178_at [Z.of_nat j])) regs3 mem3 md')
            (POST cx)).
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 regs3 mem3 md' HB).
  - (* journal: no byte written, the model materialized (ajournal_exec, YCbq.v:636-643) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha].
  - exact HF.
  - exact HL.
  - exact Hk.
  - (* the exit body, C_A82178_at (ACtlCutP.v:2314-2325), at the same registers and memory *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A82178_at ACtlCutP.ixn ACtlCutP.ixz nth].
    split; [reflexivity|].
    rewrite Nat2Z.id.
    exists phi.
    split; [exact HP|]. split; [exact HFRAC|]. split; [exact Hn|]. split; [exact Hj|].
    split; [exact HHB|]. split; [exact HFLSI|]. split; [exact HLK|]. split; [exact HFLV|].
    split; [exists A, 0, 0; exact HT | exact HIFS2].
  - exact Hrt.
Qed.

End GlueF15.

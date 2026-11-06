(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R6.v, with its module names and numbers changed; 1086 of its 1232 lines of code are new or changed and 1651 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R7tail.v; 1150 of its 1202 lines of code are new or changed and 1180 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/R7.v, with its module names changed; 329 of its 397 lines of code are new or changed and 1134 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/P1_70.v, with its addresses changed; 44 of its 89 lines of code are new or changed and 352 lines of the source are left out. *)
(* lib/A/ACtlG/P1.v -- GLUE for stage seg_P1 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:711):
     glue_seg_P1 : forall POST, CF POST C_A81b10 -> CF POST C_A81ac0
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_P1.  Written by a Theorem Labs lane's glue lane (piece W3a: P1, P1_70, P2, P4); single writer.
   rule 24: no function proved (stage glue of a walk).

   THE SEGMENT (Seg/P1.v at U 6a74d5929d2, seg_P1 :1084, "composed from seg_P1_70", plan section 2.3 row 27):
   0x81ac0 `beqz a0,0x81ac8` with a0 = 0 (the cut's a0v regs 0), one register-only step to 0x81ac8, then segment
   P1_70 (0x81ac8 -> 0x81b10).  So the stage is the beqz step composed with glue_seg_P1_70 (ACtlG/P1_70.v).

   THE RUN LIFTED: a Theorem Labs lane's P1F.p1_beqz_F (lib/A/Prog/Seg/P1F.v:38): no data access, so it is lifted with
   YA0nR.SRr_fevt at the empty footprint Kit.kit_RNG0 (as the pilot A5).  Its end state is the run's canonical
   register map with the same registers; the walk moves back to the cut's map by YA0nR.SRr_xregs_eqv.

   THE PROOF
   G1  the entry cut C_A81ac0 (ACtlCutP.v:1710-1726): its a0v regs 0 conjunct is p1_beqz_F's premise.
   G3  cfg_at_MS; the walk moved to the canonical map mkR_of regs3.
   G4  p1_beqz_F at kit_RNG0, lifted by SRr_fevt.
   G5  the walk moved back to regs3; the exit is C_A81ac8 at the same cx, fr, k, ly3, S3, W3, regs3, mem3 and the
       materialized model: journal by YCbq.ajournal_exec with the empty write set (as A5); frames, frame law, k
       unchanged; C_A81ac8's body is C_A81ac0's, conjunct for conjunct (ACtlCutP.v:1714-1726 / :1734-1746); ctl_rt
       unchanged.  The rest of the segment is glue_seg_P1_70.

   SECTION HYPOTHESES: LAWS (ACtl.v:183), which glue_seg_P1_70 also takes; nothing else is open.

   CLOSURE: every Require is qualified; the six doubled Reusable modules and lib/Lib by absolute path.

   BUILD STATE: see the commit message (type-check only until the core builds as committed). *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* the doubled modules by absolute name (porter 04:33Z) *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG01 Reusable.YG0f Reusable.YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.P1F.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.P1_70.
Import ListNotations.
Local Open Scope Z_scope.

(* The doubled modules, by full path (a Theorem Labs lane 03:5xZ). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
(* Every `Lib.<X>` below is the unit's top-level lib/Lib module (lib/A/Bz/Lib has twins). *)
Module Lib.
  Module ExecF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
  Module Regs6ss := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
  Module Frame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
End Lib.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueP1.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:217-218, :249-251), verbatim. *)
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81ac0 := (ACtlCutP.C_A81ac0 B).
Local Notation C_A81ac8 := (ACtlCutP.C_A81ac8 B).
Local Notation C_A81b10 := (ACtlCutP.C_A81b10 B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses: LAWS (ACtl.v:183). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.


(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_P1 : forall POST, CF POST C_A81b10 -> CF POST C_A81ac0.
Proof.
  intros POST HX.
  (* the rest of the segment, 0x81ac8 -> 0x81b10 *)
  pose proof (A.ACtlG.P1_70.glue_seg_P1_70 B MT XM_LIB RLO RHI LAWS POST HX) as HX70.
  intros cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut (ACtlCutP.v:1710-1726): a0 = 0 *)
  pose proof Hbody as Hb.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81ac0] in Hb.
  destruct Hb as (_ & _ & _ & _ & _ & _ & _ & HA0 & _).
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A81ac0) with 0x81ac0.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81ac0) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the beqz step, register-only, at the empty footprint *)
  pose proof (A.Prog.Seg.P1F.p1_beqz_F A.ACtlG.Kit.kit_RNG0
    (CK11.getr regs3 1) (CK11.getr regs3 2) (CK11.getr regs3 3) (CK11.getr regs3 4) (CK11.getr regs3 5)
    (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8) (CK11.getr regs3 9) (CK11.getr regs3 10)
    (CK11.getr regs3 11) (CK11.getr regs3 12) (CK11.getr regs3 13) (CK11.getr regs3 14) (CK11.getr regs3 15)
    (CK11.getr regs3 16) (CK11.getr regs3 17) (CK11.getr regs3 18) (CK11.getr regs3 19) (CK11.getr regs3 20)
    (CK11.getr regs3 21) (CK11.getr regs3 22) (CK11.getr regs3 23) (CK11.getr regs3 24) (CK11.getr regs3 25)
    (CK11.getr regs3 26) (CK11.getr regs3 27) (CK11.getr regs3 28) (CK11.getr regs3 29) (CK11.getr regs3 30)
    (CK11.getr regs3 31) CK11.fp_regs CK11.fp_csr mem3 HA0) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx) HFS).
  { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
  intros ms' md' Ems Hsbm. subst ms'.
  (* G5: the walk moved back from the canonical map to the cut's map regs3, at 0x81ac8 *)
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 regs3 _ CK11.fp_regs (Z_to_bv 64 0x81ac8) CK11.fp_csr None mem3
           (CK11.seg_rom segs) md' (POST cx));
    [| exact (Lib.Regs6ss.mkR_of_eqv regs3)].
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A81ac8) regs3 mem3 md') (POST cx)).
  apply (HX70 cx idx fr k ly3 S3 W3 regs3 mem3 md' HB).
  - (* journal: no byte written, the model materialized (ajournal_exec, YCbq.v:636-643, as A5) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply CK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha].
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: kmax 14 on both cuts *)
    exact Hk.
  - (* C_A81ac8's body is C_A81ac0's (ACtlCutP.v:1734-1746 / :1714-1726) *)
    exact Hbody.
  - (* ctl_rt: the memory is the entry cut's *)
    exact Hrt.
Qed.

End GlueP1.

Print Assumptions glue_seg_P1.

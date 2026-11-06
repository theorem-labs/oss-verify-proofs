(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R6.v, with its module names and numbers changed; 1086 of its 1232 lines of code are new or changed and 1651 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R7tail.v; 1150 of its 1202 lines of code are new or changed and 1180 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/R7.v, with its module names changed; 329 of its 397 lines of code are new or changed and 1134 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/P1_70.v, with its addresses and numbers changed; 63 of its 98 lines of code are new or changed and 362 lines of the source are left out. *)
(* lib/A/ACtlG/A2.v -- GLUE for stage seg_A2 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:649,
   `Hypothesis seg_A2 : forall POST, CF POST C_A80f88 -> CF POST C_A80f54`).  Written by a Theorem Labs lane
   (piece W0/W1); single writer.  The pattern is
   glue-pattern.md (a working note, not in this delivery), the worked example lib/A/ACtlG/A5.v.
   rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_A2 : forall POST, CF POST C_A80f88 -> CF POST C_A80f54
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_A2.  Segment A2 is 0x80f54 -> 0x80f88, the two arms after the class-6 frame request (Seg/A2.v:183-235):
     0x80f54 mv s5,a0   0x80f58 j   0x80f60 mv s6,s5   0x80f64 bnez s5   (taken: the side-stack arm, a0 <> 0).

   RULE 24 (released proofs first): proof-index LLVMFuzzerTestOneInput (index v5, built 2026-10-28 20:16:23Z
   from e966c513ee6, ossv/recipes@a8831f7c5c), second-agent check a Theorem Labs lane 21:10Z CONFIRM: the released ASan
   donor is cgif/cgif_file_fuzzer at origin/ossv/recipes c8557374ad2e; its walk lifts no outside-proved run, so this
   glue has no donor counterpart.  Its pieces are the donor's SRr (YA0n) and ajournal_exec (YCbq), a Theorem Labs lane's
   kit and bridge (Reusable/YA0nR.v SRr_xregs_eqv / SRr_fevt; A/ProgBridge.v fevt_of_evtF, tfibsegs_rsegs,
   cfg_at_MS), a Theorem Labs lane's footprint run, and the shared kits lib/A/ACtlG/Kit.v and lib/A/ACtlG/KitMem.v.

   THE RUN.  a Theorem Labs lane's mechanical v1.9 re-run A.Prog.Seg.A2F.a2_side_evt_F (Seg/A2F.v (at head lib/A/Prog/Seg/A2F.v:128-146) (an earlier version, blob adddec57ad2, not in this delivery)),
   Required, not assumed: the side-stack arm a2_side_evt (Seg/A2.v:221, blob
   283929a6248 (the blob this tree had at release c5e779efe8c)) under StepF.  It is register-only (premise rows
   segment-F-premises-A.tsv:12 (a working note, not in this delivery): no rng premise), so it is lifted at the EMPTY footprint Kit.kit_RNG0.
   The real-stack arm a2_real_evt (a0 = 0) is NOT used: the shell passes sel = fr (ACtlCut.v:223), the entry body
   pins a0 = sel (C_A80f54's a0v regs sel, ACtlCutP.v:1098), and the owned class-6 frame has 4096 <= fr
   (KitMem.kitmem_own6, from the journal's frames_bounds), so a0 <> 0 at every entry state: ctrl's seg_A2
   (Seg/A2.v:237-451) case-splits on a0, the cut layer has already discharged the class-full arm (ACtlCut.v:166-174).
   The run is stated over ctrl's lib/A/Reusable/YK11 class FPState; its fx is instantiated with
   `A.Reusable.YK11.mkFP CK11.fp_regs CK11.fp_csr` (CK11 = the core's YK11), and its post is then rewritten with
   `change` from ctrl's getr / seg_rom / fp_regs / fp_csr to the core's (same bodies; the projections reduce by iota).

   THE PROOF, step by step (glue-pattern.md section 3)
   G1  unfold the entry cut C_A80f54 (ACtlCutP.v:1089-1101): live list, PREFC, a0 = fr, 0 <= fr < 2^64, s7 = p,
       s8 = n, the input bytes, their addressability.
   G2  the run's premises: a0 = fr (the body's a0v), and fr <> 0 as a bv inequality from 4096 <= fr
       (KitMem.kitmem_own6 at the own6 journal, the frame list and the frame law); fr mod 32 = 0 for the exit body
       from the same lemma (the AR frame-alignment law al_frames).
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv from the cut's map regs3 to the run's mkR_of regs3.
   G4  ProgBridge.fevt_of_evtF + tfibsegs_rsegs, then YA0nR.SRr_fevt at Kit.kit_RNG0 (fp_avoids vacuous).
   G5  the exit cut C_A80f88 (ACtlCutP.v:1105-1117) at the run's end map R, the same cx, idx, fr, k, ly3, S3, W3,
       mem3 and the materialized model md':
         journal  ajournal_exec with the empty write set (memory unchanged, model materialized), as A5.v;
         frames, frame law, k bound   unchanged (own6 and kmax 0 on both cuts);
         body     live list unchanged; PREFC through registers 2 3 4 8 9 26 (the run keeps them; PREFC reads no
                  other register, ACtlCutP.v:1021-1032), by unfold + rewrite; s6 = s5 = fr from the run (s5 is ctrl's
                  selector register, and sel = fr); fr mod 32 from G2; the existential A := fr + FRAME_BYTES (the
                  exit body's only use of A is `fr + FRAME_BYTES <= A`); s7 / s8 through the run's keeps; the
                  input bytes and their addressability over the same memory;
         ctl_rt_C unchanged: route (C)'s A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (a working branch), at the same state and memory;
                  this stage reads none of its facts.  The entry body's last conjunct (the frame's trailer word,
                  batch 4 B5.3) is carried inside Hina to the exit's identical tail.

   SECTION HYPOTHESES
   - LAWS : Reusable.YG0d.AR_laws segs B -- the core's AR law record (YCbq Section a0's hypothesis), which
     ajournal_exec and kitmem_own6 take; ACtl.v:185 states the same hypothesis and discharges it in its section 9.
   No other hypothesis: the run is Required from Seg/A2F.v and has no premise the cut does not give.

   NOT USED: rt_of_core (the run has no runtime premise); the Seg/*.v keep lemmas (the run writes no memory);
   ProgWorld.ajournal_of_fsteps (no byte written, ajournal_exec with the empty write set suffices).

   CLOSURE (glue closure rule, a Theorem Labs lane 23:32Z, porter 23:38Z / 23:40Z): every Require is qualified (no Import /
   Export of a project module); no statement here names a frame-route identifier.  The six module names that exist
   both as the core's lib/Reusable/<X> and as ctrl's lib/A/Reusable/<X> (YI04 YI16 YK11 YK1b YM05 YO09) are loaded
   by absolute Require lines and written through the fully qualified aliases CK11 / CK1b / CM05 / CO09 below; lib/Lib's
   modules through LMState / LRegs; ctrl's YK11 (the run's) through AK11.  Frame-route files of record in the closure
   (through Seg/A2F.v), blobs at the glue worktree HEAD 729ec17cb79: Seg/A2F.v adddec57ad2, Seg/A2.v 283929a6248,
   SlotInv.v 4cf85db229a, Seg/Tac_slot.v de02ff45188, SlotModel.v 04dc7903221, AsanRT.v b67d26f8ec7 (mcs 30),
   AsanRTInv.v 2a8602e8526, Contract.v fa6fd478d9a, FrameAPI.v f6ffefa9bb4, MemNorm.v cb518fc0304.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are fully qualified (through CK11 / AK11) or Reusable.YG0d-qualified
   everywhere.  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/A2.v   -- hits only inside comments.

   BUILD STATE (honest): type-check on a working branch shell merged on this branch (cb build); the build of
   record is cbrec's (log and .prov named in the commit).  Print Assumptions glue_seg_A2: lib/A/ACtlG/L3W01Audit.v.
   No Axiom, no Parameter, no Admitted, no admit. *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.A2F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

(* The twin-safe module names (fully qualified). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module AK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Module LMState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LRegs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.

(* The core's segment list, as ACtlCut.v:76 and ACtl.v:165 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueA2.

(* ACtl.v's Section shape (ACtl.v:172-176), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:219-220, :226-227), verbatim. *)
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A80f54 := (ACtlCutP.C_A80f54 B).
Local Notation C_A80f88 := (ACtlCutP.C_A80f88 B).

(* The core's AR laws (YCbq.v Section a0's hypothesis; ACtl.v:185). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_A2 : forall POST, CF POST C_A80f88 -> CF POST C_A80f54.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut C_A80f54 (ACtlCutP.v:1089-1101). *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A80f54] in Hbody.
  destruct Hbody as (HP & HPREF & Ha0 & Hsel & R23 & R24 & Hinb & Hina).
  (* G2: fr is the owned class-6 frame: 4096 <= fr and fr mod 32 = 0 (KitMem.kitmem_own6), so a0 = fr <> 0. *)
  destruct (A.ACtlG.KitMem.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (_ & _ & Hfr4096 & Hfr32 & _ & _).
  assert (E0 : bv_eqb (Z_to_bv 64 fr) (Z_to_bv 64 0) = false).
  { unfold bv_eqb. rewrite !LMState.unsigned_lit by lia. apply Z.eqb_neq. lia. }
  (* G3: the cut's configuration in the run's state form, the walk moved to the run's map mkR_of regs3. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A80f54) with 0x80f54.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRegs.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x80f54) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRegs.xregs_eqv_sym _ _ (LRegs.mkR_of_eqv regs3))].
  (* G4: the run (ctrl's YK11 instance built from the core's fp state) and the lift at the empty footprint. *)
  pose proof (@A.Prog.Seg.A2F.a2_side_evt_F (AK11.mkFP CK11.fp_regs CK11.fp_csr) A.ACtlG.Kit.kit_RNG0
    regs3 mem3 fr Ha0 E0) as HRUN.
  change (@AK11.fp_regs (AK11.mkFP CK11.fp_regs CK11.fp_csr)) with (@CK11.fp_regs fx) in HRUN.
  change (@AK11.fp_csr (AK11.mkFP CK11.fp_regs CK11.fp_csr)) with (@CK11.fp_csr fx) in HRUN.
  change (@AK11.getr) with (@CK11.getr) in HRUN.
  change (@AK11.seg_rom) with (@CK11.seg_rom) in HRUN.
  (* glue base batch 5's A2F.v states the post with lib.Lib's PropExec copy (LPE.getr / LPE.seg_rom, A2F.v:126-137
     at c903fcfd291); same bodies as the core's YK11 ones, so the same `change` *)
  change (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.getr) with (@CK11.getr) in HRUN.
  change (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.seg_rom) with (@CK11.seg_rom) in HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx) HFS).
  { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
  (* G5: the continuation, at the run's end state MS R .. 0x80f88 .. mem3. *)
  intros ms' md' HQ0 Hsbm.
  destruct HQ0 as (R & pc' & mem' & Ems & Hpc & Hmem & K22 & K21 & K2 & K3 & K4 & K8 & K9 & K23 & K24 & K26).
  subst ms' pc' mem'.
  (* ProgBridge.cfg_at_MS read backwards (it is eq_refl), at the exit cut's pc *)
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A80f88) R mem3 md') (POST cx)).
  apply (HX cx idx fr k ly3 S3 W3 R mem3 md' HB).
  - (* journal: no byte written, the model materialized (ajournal_exec, as A5.v and YCbq.v call it) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply CK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha].
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: kmax 0 on both cuts *)
    exact Hk.
  - (* the exit body, C_A80f88 (ACtlCutP.v:1105-1117), at sel = fr *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A80f88].
    split; [exact HP|].
    split.
    { (* PREFC reads registers 2 (also through spZ), 3, 4, 8, 9 and 26 only, all kept by the run *)
      unfold ACtlCutP.PREFC, ACtlCut.rgv, Reusable.YG0d.spZ in *.
      rewrite K2, K3, K4, K8, K9, K26. exact HPREF. }
    exists (fr + ACtlCutP.FRAME_BYTES).
    split; [exact K22|].
    split; [exact Hfr32|].
    split; [exact K21|].
    split; [exact Hsel|].
    split; [lia|].
    split; [unfold ACtlCut.rgv; rewrite K23; exact R23|].
    split; [unfold ACtlCut.rgv; rewrite K24; exact R24|].
    split; [exact Hinb | exact Hina].
  - (* ctl_rt_C: the entry cut's state (ly3, S3) and memory *)
    exact Hrt.
Qed.

End GlueA2.

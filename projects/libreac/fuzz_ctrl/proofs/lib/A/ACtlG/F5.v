(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 507 of its 559 lines of code are new or changed and 3060 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtl.v, with its module paths and module names changed; 86 of its 101 lines of code are new or changed and 544 lines of the source are left out. *)
(* lib/A/ACtlG/F5.v -- GLUE for stage seg_F5 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:751).
   Written by a Theorem Labs lane; single writer.  rule 24: no function proved (kind: segment
   lemma) -- a glue stage of image A's entry walk.

   WHAT IT PROVES
     glue_seg_F5 : forall POST (j : nat),
       CF POST (ix_cut C_A81f54_at [Z.of_nat j]) -> CF POST (ix_cut C_A81e84_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_F5.  Segment F5 is 0x81e84 -> 0x81e88, one register-only instruction, 0x81e84 mv s8,a0
   (a0 = t_k j = 0 on the short arm), followed by the join stage seg_F5_df0 (0x81e88 -> 0x81f54).  The plain
   frame-route proof is lib/A/Prog/Seg/F5.v:927-1003 (seg_F5).

   THE PROOF, step by step (A5.v's G1-G5, glue-pattern.md section 3 (a working note, not in this delivery))
   G0  from the hypothesis CF f54, the join cut CF e88 by A.ACtlG.F5_df0.glue_seg_F5_df0 (a Theorem Labs lane).
   G1  unfold the entry cut: ix_cut's index equation, then C_A81e84_at (ACtlCutP.v:2024-2033): FRAC and b5_body
       with flen < 50, rgv 10 t_k, u32 [fr+176], IDj, b5_F17, b5_PF; Z.to_nat (Z.of_nat j) = j.
   G2  the run's premise rgv 10 0 from rgv 10 t_k and t_k j = 0 (Seg/F5.v f5_k, flen < 50).
   G3  ProgBridge.cfg_at_MS, then the walk moved to the run's canonical map (YA0nR.SRr_xregs_eqv).
   G4  the run Seg/F5F.seg_F5_run_F at fx := A.Reusable.YK11.mkFP fp_regs fp_csr, lifted with
       ProgBridge.fevt_of_evtF + tfibsegs_rsegs + YA0nR.SRr_fevt at the empty footprint Kit.kit_RNG0.
   G5  the join cut C_A81e88_at at the run's end map R and the same memory mem3:
         journal  ajournal_exec with the empty write set (the model is materialized), as A5.v:206-208;
         frames, frame law, k bound   unchanged (own6, the same kmax on both cuts);
         FRAC     Kit.kit_frac_move (registers 2 3 4 8 9 19 26 kept);
         FLSI LK b5_C   A.ACtlG.F5_e10.f5g_move (registers 2 9 18 21 23 kept);
         HB, u32, IDj   unchanged memory; flen < 50 unchanged; rgv 24 t_k from R24 = 0 = t_k;
         b5_F17, b5_PF  through register 9 (s1), memory unchanged;
         ctl_rt_C the entry's A.ACtlRtC.ctl_rt_C B ly3 S3 mem3: the join cut has the same ly3 S3 and memory
                  (route (C) L3: Hrt is not opened, it is passed on as it is).

   SECTION HYPOTHESES
   - LAWS: the core's AR law record (YCbq.v:207), as ACtl.v:183 states it (ajournal_exec and glue_seg_F5_df0
     take it).
   - The other ACtl.v Section Ctl entries (RELRO_IMG, TFIB_SYMS, TFIB_LIB, XN_LIB, the REAC_* variables) are
     copied verbatim and vanish at End Section (unused).
   CITED BY NAME: A.ACtlG.F5_df0.glue_seg_F5_df0; the run A.Prog.Seg.F5F.seg_F5_run_F (F5F.v:136, blob 336a376f81d
   on the base); A.Prog.Seg.F5.f5_k; A.ACtlG.F5_e10.f5g_move; A.ACtlG.Kit.kit_wx / kit_segs_low / kit_frac_move /
   kit_RNG0; Reusable.YA0nR.SRr_xregs_eqv / SRr_fevt; A.ProgBridge.fevt_of_evtF / tfibsegs_rsegs / cfg_at_MS;
   Reusable.YCbq.ajournal_exec.

   CLOSURE: every project Require below is qualified (no Import / Export of a project module); no STATEMENT names a
   frame-route identifier (Seg/F5.v and F5F.v are cited inside the proof only).  The core's twin modules are
   Required from the prefix ...fuzz_ctrl.lib.Reusable and written lib.Reusable.X, ctrl's from
   ...fuzz_ctrl.lib.A.Reusable and written A.Reusable.X (a Theorem Labs lane 04:2xZ and the porter's amendment 04:33Z: the
   unprefixed spelling of a twin resolves to ctrl's copy in a file that Requires ACtlCutP).

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are lib.Reusable.YK11 / A.Reusable.YK11 / Reusable.YG0d-qualified
   everywhere.  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/F5.v   -- hits only inside comments.

   ROUTE (C) L3 (a Theorem Labs lane, 2026-10-29; recipe L3-recipe.md (a working note, not in this delivery)):
   ctl_from hands the stage Hrt : A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (a working branch's shell).  The stage never opens Hrt
   (no destruct, no use of a shadow part); the join cut needs ctl_rt_C B ly3 S3 mem3 again (same state, same
   memory), so the proof is unchanged: `exact Hrt`.  No VIS0 / OWNED_RO / AR_VIS0 / AR_OWNED_RO hypothesis and no
   stage-level ctlrt_of_AR.  The run's contract takes no mem_inv premise.

   BUILD STATE: type-check with cb build --fresh (BASE 23b918fe0c2e) on a working branch 1899bed1aee merged with
   a working branch; the lane report names the cbrec record (.prov), the .vo mtime and Print Assumptions of
   glue_seg_F5 (Rocq primitives and functional_extensionality_dep only).  No Axiom, no Parameter, no Admitted, no
   admit; LAWS stays a Section hypothesis. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.ACtlCut A.ACtlCutP A.AF0m A.ACeh.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F5 A.Prog.Seg.F5F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.F5_e10 A.ACtlG.F5_df0.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueF5.

(* ACtl.v's Section Ctl shape (ACtl.v:170-194), verbatim with the core's twins written lib.Reusable.X. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis RELRO_KIND_NAME : RLO <= 0x9e760 /\ 0x9e760 + 112 <= RHI.
Hypothesis RELRO_CAT : RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI.
Hypothesis RELRO_FRAMES : RLO <= 0x9f7e0 /\ 0x9f7e0 + 264 <= RHI.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis MO_LE : forall (S S' : Reusable.YG00.astate) (m : Z), Reusable.YC5d.mo_le MT S S' m.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis TFIB_LIB : A.ACeh.TfibLib B.
Variable REAC_CTRL_IDENTITY_REPLY_K : Z.
Variable REAC_CTRL_PARSE_BC : Z.
Hypothesis KREPLY : REAC_CTRL_IDENTITY_REPLY_K = 9072.
Hypothesis KPARSE : REAC_CTRL_PARSE_BC = 0x21200.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :267-268, :272), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81e84_at := (ACtlCutP.C_A81e84_at B).
Local Notation C_A81e88_at := (ACtlCutP.C_A81e88_at B).
Local Notation C_A81f54_at := (ACtlCutP.C_A81f54_at B).

Lemma glue_seg_F5 : forall POST (j : nat), CF POST (ix_cut C_A81f54_at [Z.of_nat j]) -> CF POST (ix_cut C_A81e84_at [Z.of_nat j]).
Proof.
  intros POST j HX.
  (* G0: the join cut at 0x81e88 (stage seg_F5_df0). *)
  assert (HX88 : CF POST (ix_cut C_A81e88_at [Z.of_nat j]))
    by (apply A.ACtlG.F5_df0.glue_seg_F5_df0; [exact LAWS | exact HX]).
  intros cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut, ACtlCut.v:232-234; C_A81e84_at, ACtlCutP.v:2024-2033). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81e84_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HPerm & Hcn & Hj255 & HHB & HFLSI & HLK & HC & Hlen50 & R10 & Hu32 & HID & HF17 &
    HPF).
  (* G2: a0 = t_k j = 0 on the short arm. *)
  pose proof (A.Prog.Seg.F5.f5_k (ACtlCut.c_in cx) j Hlen50) as Hk0.
  rewrite Hk0 in R10.
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81e84_at [Z.of_nat j])) with 0x81e84.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x81e84) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the register-only run, lifted at the empty footprint. *)
  pose proof (@A.Prog.Seg.F5F.seg_F5_run_F
                (A.Reusable.YK11.mkFP lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr) regs3 mem3
                A.ACtlG.Kit.kit_RNG0 R10) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx) HFS).
  { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
  (* G5: the continuation at the run's end state MS R .. 0x81e88 .. mem3. *)
  intros ms' md' HQ0 Hsbm.
  destruct HQ0 as (R & pc' & mem' & Ems & Hpc & Hmem & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K26 & K23 & K18 & K24).
  subst ms' pc' mem'.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81e88_at [Z.of_nat j]))
            R mem3 md') (POST cx)).
  destruct (A.ACtlG.F5_e10.f5g_move cx j phi fr regs3 R mem3 K2 K9 K18 K21 K23 HFLSI HLK HC)
    as (HFLSI' & HLK' & HC').
  apply (HX88 cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HB).
  - (* journal: no byte written, the model materialized (ajournal_exec, as A5.v:206-208) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha].
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: the same kmax on both cuts *)
    exact Hk.
  - (* the join body, C_A81e88_at (ACtlCutP.v:2037-2046), at the same index *)
    split; [reflexivity|].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81e88_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
    unfold ACtlCutP.b5_body. exists phi. cbv beta.
    split; [exact HPerm|]. split; [exact Hcn|]. split; [exact Hj255|].
    split; [exact HHB|]. split; [exact HFLSI'|]. split; [exact HLK'|]. split; [exact HC'|].
    split; [exact Hlen50|].
    split; [rewrite Hk0; exact K24|].
    split; [exact Hu32|]. split; [exact HID|].
    split.
    { destruct HF17 as (A7 & H97 & HA7 & Hq7).
      exists A7. split; [exact (eq_trans K9 H97)|]. split; [exact HA7 | exact Hq7]. }
    destruct HPF as (A9 & H99 & HPF9).
    exists A9. split; [exact (eq_trans K9 H99) | exact HPF9].
  - (* ctl_rt_C: the same ly3 S3 and memory as the entry cut *)
    exact Hrt.
Qed.

End GlueF5.

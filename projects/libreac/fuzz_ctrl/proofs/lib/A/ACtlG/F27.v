(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 4006 of its 4152 lines of code are new or changed and 2320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4b.v, with its module paths and module names changed; 782 of its 845 lines of code are new or changed and 4089 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F12.v; 222 of its 251 lines of code are new or changed and 816 lines of the source are left out. *)
(* lib/A/ACtlG/F27.v -- GLUE for stage seg_F27 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:826-827),
   written in the route (C) form of a working branch shell (a working branch 1899bed1aee: ctl_from carries
   A.ACtlRtC.ctl_rt_C B ly3 S3 mem3).  Written by a Theorem Labs lane; single writer.  proves no function (kind:
   segment lemma); rule 24: no function proved.  Pattern: glue-pattern.md sections 1-8 (a working note, not in this delivery);
   template: this branch's read-only arm ACtlG/F18.v (f18_evt0_F, lifted by SRr_fevt).

   WHAT IT PROVES
     glue_seg_F27 : forall POST (j : nat),
       CF POST (ix_cut C_A8265c_at [Z.of_nat j]) -> CF POST (ix_cut C_A82750_at [Z.of_nat j]) -> CF POST (ix_cut C_A82604_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_F27.  Segment F27 (Seg/F27.v:1-17) is 0x82604 -> 0x8265c (t_rp = 0) or 0x82604 -> 0x82750 (t_rp <> 0): a
   register-only, read-only stretch (no store, no call, no instrumented check).

   THE _F RUNS (Required, not assumed): a Theorem Labs lane's lib/A/Prog/Seg/F27F.v (an earlier version, blob 35e3622a4b, not in this delivery) (on a working branch, = the blob at
   a working branch): f27_r0_run_F (the r = 0 arm, reads the spill [A + 136]) and f27_rm_run_F (the
   r <> 0 arm, reads the spills [A + 136] / [A + 176] and the three ports words at fr + 128 / 132 / 136).  Both posts
   keep the memory (mem' = mem), so the exit state is the entry's ly3 S3 W3 mem3.

   THE PROOF
   G1  the entry cut C_A82604_at (ACtlCutP.v:2757-2767): ix_cut's index equation, FRAC, the b7_body (FLSI, B7K) and
       the arm facts (s9 = t_rp, s4 = a0 = t_unk, PORTS, FIRSTb).  The B7K spills [A + 136] / [A + 176] are taken at
       FRAC's spill base A (both bases are register 9; their ranges force the same Z).
   G2  the run's premises: registers from the body; the spill reads by F27.f27_rd8 and the ports reads by
       F27.f27_rd4 from the body's bytes; t_rp / t_unk by F27.b7_unk_rp0 / b7_unk_rpm (SlotModel); footprint
       RNG := ProgBridge.RNG_W (w_H W3): the spills by ProgWorldVisWin.win_vis (the journal's stack window,
       c_sp - 4096 < sp <= A, A + 416 <= c_sp from FRAC), the ports words by ProgWorldVisFrame.frame_vis (the owned
       class-6 frame: the frame law, layout_le's ly_F, frames_bounds' AR).
   G3  cfg_at_MS, then the walk moved from regs3 to the run's start map mkR_of regs3 (YA0nR.SRr_xregs_eqv).  The run's
       FPState is ctrl's A.Reusable.YK11 class, instantiated at A.Reusable.YK11.mkFP fp_regs fp_csr (the core's
       projections; glue-pattern section 6).
   G4  lift: ProgBridge.fevt_of_evtF, YA0nR.SRr_fevt (read-only run), fp_avoids by ProgBridge.fp_avoids_RNG_W.
   G5  the exit cut at the run's end map R and the unchanged memory: journal by YCbq.ajournal_exec with the empty
       write set (F18's evt0 arm); frames / frame law / k bound unchanged; FRAC by Kit.kit_frac_move; FLSI / B7K / LT /
       LK moved to R by the local register lemmas below (they read registers 9, 18, 21-24 only, all kept by the run);
       the 0x8265c arm's new registers from the run's post; the 0x82750 arm's FLS from B7K (B7Cuts.b7_a826a4's proof
       over ACtlCutP: t_big from 50 <= flen, s9 = fr + 64 from the run).
       ctl_rt_C B ly3 S3 mem3 at the exit: the entry's Hrt (same layout, state and memory; route (C) recipe section
       2(d), "keep the state").
   INSTRUCTIONS THIS GLUE STEPS ITSELF: none (both arms are F27F's).

   LOCAL LEMMAS (Qed): glue_f27_spill_regs / glue_f27_rgv / glue_f27_flsi_regs / glue_f27_lt_regs /
   glue_f27_b7k_regs move ACtlCutP's spill, rgv, FLSI, LT and B7K along a register map that keeps the registers they
   read (B7Cuts.b7_flsi_regs / b7_B7K_regs restated over ACtlCutP's transcription, which is not convertible with
   SlotInv's: a Theorem Labs lane's F19.v header).

   SECTION HYPOTHESES (exact text below; each is in the route (C) walk's ACtl.v Section with the same name and text)
   - LAWS : Reusable.YG0d.AR_laws segs B (ACtl.v:244).
   So ACtl.v discharges seg_F27 by `glue_seg_F27 B MT XM_LIB RLO RHI LAWS` (fx / rc implicit; LS is not used).
   CITED, PROVED (not hypotheses): F27F.f27_r0_run_F / f27_rm_run_F; F27.f27_rd8 / f27_rd4 / b7_unk_rp0 / b7_unk_rpm;
   win_vis / frame_vis (ProgWorldVis*.v); SRr_xregs_eqv / SRr_fevt (YA0nR.v); fevt_of_evtF, cfg_at_MS, RNG_W,
   fp_avoids_RNG_W, rng_of_visible (ProgBridge.v); frames_bounds, ajournal_exec (YCbq.v); Kit.kit_wx / kit_segs_low /
   kit_frac_move.  NOT USED: TFIB_SYMS, CTLRT_ENTRY, CHAIN_OF_CUT, any callee hypothesis (no call), any shadow region
   (no shadow byte is read or written).

   CLOSURE: every Require is qualified; no statement names a frame-route identifier (F27F / F27 / SlotModel /
   A.Reusable.YK11 appear only inside Qed proofs).  Frame-route files Required, blobs on a working branch 1899bed1aee:
   Seg/F27F.v 35e3622a4b, Seg/F27.v c521acaf7a.
   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are fully qualified everywhere. *)

From Coq Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0n Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisWin A.ProgWorldVisFrame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel A.Prog.Seg.F27 A.Prog.Seg.F27F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:80 and ACtl.v:203 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* lib/Lib's modules, by their full paths (lib/A/Bz/Lib and lib/AZ/Lib carry files of the same names). *)
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.

(* ---------------------------------------------------------------------------------------------------------
   Local register lemmas: ACtlCutP's body predicates along a register map that keeps the registers they read. *)

(* A spill reads register 9 only (ACtlCutP.v:537-538). *)
Lemma glue_f27_spill_regs : forall (regs regs' : bvmap 5 word) (m : word -> option byte) (off v : Z),
  CK11.getr regs' 9 = CK11.getr regs 9 ->
  A.ACtlCutP.spill regs m off v -> A.ACtlCutP.spill regs' m off v.
Proof.
  intros regs regs' m off v E (A & HA & Hq). exists A. split; [|exact Hq].
  unfold A.ACtlCut.rgv in *. rewrite E. exact HA.
Qed.

(* A register pin along a map that keeps that register. *)
Lemma glue_f27_rgv : forall (regs regs' : bvmap 5 word) (r : bv 5) (v : Z),
  CK11.getr regs' r = CK11.getr regs r -> A.ACtlCut.rgv regs r v -> A.ACtlCut.rgv regs' r v.
Proof. intros regs regs' r v E H. unfold A.ACtlCut.rgv in *. rewrite E. exact H. Qed.

(* FLSI (ACtlCutP.v:760-763) reads register 9 only, through its spills (B7Cuts.b7_flsi_regs over ACtlCutP). *)
Lemma glue_f27_flsi_regs : forall (cx : A.ACtlCut.ctlcx) (j : nat) (fr : Z) (regs regs' : bvmap 5 word)
    (m : word -> option byte),
  A.ACtlCutP.FLSI cx j fr regs m -> CK11.getr regs' 9 = CK11.getr regs 9 -> A.ACtlCutP.FLSI cx j fr regs' m.
Proof.
  intros cx j fr regs regs' m H E9.
  unfold A.ACtlCutP.FLSI, A.ACtlCutP.FLSH, A.ACtlCutP.PRO, A.ACtlCutP.FLC in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with
         | |- _ /\ _ => split
         | |- A.ACtlCutP.spill _ _ _ _ => apply (glue_f27_spill_regs regs regs' m _ _ E9); assumption
         | |- _ => assumption
         end.
Qed.

(* LT = IFS cx fr (S j) (ACtlCutP.v:807-808) reads register 9 only, through FSb's two spills. *)
Lemma glue_f27_lt_regs : forall (cx : A.ACtlCut.ctlcx) (fr : Z) (j : nat) (regs regs' : bvmap 5 word)
    (m : word -> option byte),
  A.ACtlCutP.LT cx fr j regs m -> CK11.getr regs' 9 = CK11.getr regs 9 -> A.ACtlCutP.LT cx fr j regs' m.
Proof.
  intros cx fr j regs regs' m H E9.
  unfold A.ACtlCutP.LT, A.ACtlCutP.IFS, A.ACtlCutP.FSj, A.ACtlCutP.FSb in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with
         | |- _ /\ _ => split
         | |- A.ACtlCutP.spill _ _ _ _ => apply (glue_f27_spill_regs regs regs' m _ _ E9); assumption
         | |- _ => assumption
         end.
Qed.

(* B7K (ACtlCutP.v:1024-1033) reads registers 9 (spills, LT), 18, 21 (LK), 22, 23 and 24 (B7Cuts.b7_B7K_regs over
   ACtlCutP). *)
Lemma glue_f27_b7k_regs : forall (cx : A.ACtlCut.ctlcx) (j : nat) (phi fr : Z) (regs regs' : bvmap 5 word)
    (m : word -> option byte),
  A.ACtlCutP.B7K cx j phi fr regs m ->
  CK11.getr regs' 9 = CK11.getr regs 9 -> CK11.getr regs' 18 = CK11.getr regs 18 ->
  CK11.getr regs' 21 = CK11.getr regs 21 -> CK11.getr regs' 22 = CK11.getr regs 22 ->
  CK11.getr regs' 23 = CK11.getr regs 23 -> CK11.getr regs' 24 = CK11.getr regs 24 ->
  A.ACtlCutP.B7K cx j phi fr regs' m.
Proof.
  intros cx j phi fr regs regs' m H E9 E18 E21 E22 E23 E24.
  pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT & _).
  pose proof (glue_f27_lt_regs _ _ _ regs regs' m HLT E9) as HLT'.
  unfold A.ACtlCutP.B7K, A.ACtlCutP.LK, A.ACtlCutP.B7SPL in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with
         | |- _ /\ _ => split
         | |- A.ACtlCutP.spill _ _ _ _ => apply (glue_f27_spill_regs regs regs' m _ _ E9); assumption
         | |- A.ACtlCut.rgv _ _ _ =>
             first [ apply (glue_f27_rgv regs regs' _ _ E18); assumption
                   | apply (glue_f27_rgv regs regs' _ _ E21); assumption
                   | apply (glue_f27_rgv regs regs' _ _ E22); assumption
                   | apply (glue_f27_rgv regs regs' _ _ E23); assumption
                   | apply (glue_f27_rgv regs regs' _ _ E24); assumption ]
         | |- _ => assumption
         end.
Qed.

Section GlueF27.

(* ACtl.v's Section shape (ACtl.v:210-214), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:373, :377-378), verbatim, and this stage's three cuts (ACtl.v:457, :458, :460). *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A82604_at := (ACtlCutP.C_A82604_at B).
Local Notation C_A8265c_at := (ACtlCutP.C_A8265c_at B).
Local Notation C_A82750_at := (ACtlCutP.C_A82750_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypothesis (ACtl.v:237, same name and text). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_F27 : forall POST (j : nat),
  CF POST (ix_cut C_A8265c_at [Z.of_nat j]) -> CF POST (ix_cut C_A82750_at [Z.of_nat j]) -> CF POST (ix_cut C_A82604_at [Z.of_nat j]).
Proof.
  intros POST j H65c H750 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut, ACtlCut.v:253-255; C_A82604_at, ACtlCutP.v:2757-2767). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82604_at ACtlCutP.ixn ACtlCutP.ixz nth
                            ACtlCutP.b7_body] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HP & Hn & Hj & HHB & HFLSI & HK & Hs25 & Hs20 & Ha10 & HPO & HFI & Had1 & Had2).
  pose proof HK as (HLK & H23 & H22 & Hphi0 & Hphi50 & Hflen & Hblk & S280 & H24 & H18 & S152 & Hg & Hph & Hlen &
    HLT & HS136 & HS120 & HS176).
  (* FRAC's spill base A and sp (ACtlCutP.v:1063-1078) *)
  pose proof HFRAC as (A & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hf32 & HA32 & HAS & HspA &
    HfrA & HA416 & HSlo & HSapp & _).
  assert (HspR : 0 <= sp < 2 ^ 64).
  { rewrite <- HspZ. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (CK11.getr regs3 2)) as Hr. unfold bv_modulus in Hr. exact Hr. }
  unfold A.AsanRT.APPMEM_END in HSapp.
  (* the B7K spills at FRAC's spill base: both bases are register 9, their own ranges force the same Z *)
  assert (EA : forall A1 off v, ACtlCut.rgv regs3 9 A1 -> ACtlCutP.q64 mem3 (A1 + off) v -> 0 <= off <= 408 ->
                 ACtlCutP.q64 mem3 (A + off) v).
  { intros A1 off v H91 Hq Hoff.
    pose proof Hq as (Hq0 & Hq1 & _). rewrite LMem.length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
    unfold ACtlCut.rgv in R9, H91. rewrite R9 in H91.
    apply (f_equal bv_unsigned) in H91. rewrite !Z_to_bv_unsigned in H91. unfold bv_wrap in H91.
    change (bv_modulus 64) with (2 ^ 64) in H91.
    assert (E : A1 = A) by (Z.div_mod_to_equations; lia).
    subst A1. exact Hq. }
  destruct HS136 as (A1 & H91 & Hq136). apply (EA A1 136 _ H91) in Hq136; [|lia]. clear A1 H91.
  destruct HS176 as (A1 & H91 & Hq176). apply (EA A1 176 _ H91) in Hq176; [|lia]. clear A1 H91.
  pose proof (A.Prog.Seg.F27.f27_rd8 mem3 _ _ Hq136 (LMem.length_le8 _)) as RD136.
  (* the journal: AR and the layout's ly_F; the owned class-6 frame at fr *)
  pose proof HJ as (HAR & Hly & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Efr3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  assert (Hfs6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  (* the footprint RNG_W (w_H W3): the journal's stack window and the owned frame are visible *)
  set (RNG := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (Hwin : forall lo len, ACtlCut.c_sp cx - 32768 <= lo -> lo + len <= ACtlCut.c_sp cx -> LEF.rng RNG lo len).
  { intros lo len H1 H2. apply A.ProgBridge.rng_of_visible.
    apply (A.ProgWorldVisWin.win_vis B _ _ _ _ _ _ _ _ _ _ _ _ _ _ k _ _ HJ); unfold A.ACfn.LLVMF_STK; lia. }
  assert (Hfrm : forall lo len, fr <= lo -> lo + len <= fr + 4096 -> LEF.rng RNG lo len).
  { intros lo len H1 H2. apply A.ProgBridge.rng_of_visible.
    destruct (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) lo len HAR Hin6
                ltac:(rewrite Efr3; lia) ltac:(rewrite Efr3, Hfs6; lia)) as (HV & _).
    exact HV. }
  (* G3: the cut's configuration in the run's state form, then the walk moved to mkR_of regs3. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A82604_at [Z.of_nat j])) with 0x82604.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 CK11.fp_regs (Z_to_bv 64 0x82604)
           CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  destruct (Z.eq_dec (A.Prog.SlotModel.t_rp (ACtlCut.c_in cx) j) 0) as [Er | Er].
  - (* ---- t_rp = 0: f27_r0_run_F, exit C_A8265c_at (ACtlCutP.v:2771-2782) ---- *)
    destruct (A.Prog.Seg.F27.b7_unk_rp0 _ _ Er) as (Hu & _).
    rewrite Er in Hs25.
    (* G4: the run at the core's FP registers, lifted read-only *)
    eapply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 RNG _ (POST cx)).
    { apply A.ProgBridge.fevt_of_evtF.
      exact (@A.Prog.Seg.F27F.f27_r0_run_F
               (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.mkFP CK11.fp_regs CK11.fp_csr)
               regs3 mem3 A fr phi (A.Prog.SlotModel.t_unk (ACtlCut.c_in cx) j) RNG
               Hs25 Hs20 Ha10 R9 H22 ltac:(lia) RD136 (Hwin (A + 136) 8 ltac:(lia) ltac:(lia))). }
    { apply A.ProgBridge.fp_avoids_RNG_W. }
    intros ms' md' Hms' Hsbm.
    destruct Hms' as (R & pc' & mem' & Ems & Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR26 & HR20 & HR21 &
      HR22 & HR23 & HR24 & HR18 & HR7 & HR10 & HR14 & HR15 & HR11 & HR12 & HR13 & HR16).
    subst ms' pc' mem'.
    (* G5: ProgBridge.cfg_at_MS read backwards (eq_refl), at the exit cut's pc and the run's end map R *)
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A8265c_at [Z.of_nat j])) R mem3 md') (POST cx)).
    apply (H65c cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HB).
    + (* journal: no byte written, the model materialized (ajournal_exec, YCbq.v:636-643) *)
      eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity
        | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl
        | intros x _; reflexivity | exact Hsbm | intros a Ha; destruct Ha].
    + exact HF.
    + exact HL.
    + exact Hk.
    + (* the exit body: memory unchanged; registers kept or set by the run *)
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A8265c_at ACtlCutP.ixn ACtlCutP.ixz nth
                                ACtlCutP.b7_body].
      split; [reflexivity|]. rewrite Nat2Z.id.
      split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC HR2 HR3 HR4 HR8 HR9 HR19 HR26)|].
      exists phi.
      split; [exact HP|]. split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [exact (glue_f27_flsi_regs cx j fr regs3 R mem3 HFLSI HR9)|].
      split; [exact (glue_f27_b7k_regs cx j phi fr regs3 R mem3 HK HR9 HR18 HR21 HR22 HR23 HR24)|].
      split; [exact Er|]. split; [lia|].
      split; [exact (glue_f27_rgv regs3 R 20 _ HR20 Hs20)|].
      split; [exact HR7|]. split; [exact HPO|]. split; [exact HFI|].
      split; [exact HR10|]. split; [exact HR14|]. split; [exact HR15|].
      split; [exact HR11|]. split; [exact HR12|]. split; [exact HR13|]. exact HR16.
    + (* ctl_rt_C at the exit: same layout, state and memory as the entry *)
      exact Hrt.
  - (* ---- t_rp <> 0: t_rp = t_unk = -1, the three ports words are -7; f27_rm_run_F, exit C_A82750_at
       (ACtlCutP.v:2802-2812) ---- *)
    destruct (A.Prog.Seg.F27.b7_unk_rpm _ _ Er) as (Er' & Eu).
    destruct (proj2 HPO Er) as (P0 & P4 & P8).
    pose proof (A.Prog.Seg.F27.f27_rd8 mem3 _ _ Hq176 (LMem.length_le8 _)) as RD176.
    pose proof (A.Prog.Seg.F27.f27_rd4 mem3 _ _ P0 (LMem.length_le4 _)) as RD0.
    pose proof (A.Prog.Seg.F27.f27_rd4 mem3 _ _ P4 (LMem.length_le4 _)) as RD4.
    pose proof (A.Prog.Seg.F27.f27_rd4 mem3 _ _ P8 (LMem.length_le4 _)) as RD8.
    rewrite Er' in Hs25. rewrite Eu in Hs20, Ha10.
    (* G4: the run at the core's FP registers, lifted read-only *)
    eapply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 RNG _ (POST cx)).
    { apply A.ProgBridge.fevt_of_evtF.
      exact (@A.Prog.Seg.F27F.f27_rm_run_F
               (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.mkFP CK11.fp_regs CK11.fp_csr)
               regs3 mem3 A fr RNG Hs25 Hs20 Ha10 R9 RD136 RD176 RD0 RD4 RD8
               (Hwin (A + 136) 8 ltac:(lia) ltac:(lia)) (Hwin (A + 176) 8 ltac:(lia) ltac:(lia))
               (Hfrm (fr + 128) 4 ltac:(lia) ltac:(lia)) (Hfrm (fr + 132) 4 ltac:(lia) ltac:(lia))
               (Hfrm (fr + 136) 4 ltac:(lia) ltac:(lia))). }
    { apply A.ProgBridge.fp_avoids_RNG_W. }
    intros ms' md' Hms' Hsbm.
    destruct Hms' as (R & pc' & mem' & Ems & Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR26 & HR21 & HR22 &
      HR23 & HR24 & HR18 & HR25).
    subst ms' pc' mem'.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82750_at [Z.of_nat j])) R mem3 md') (POST cx)).
    apply (H750 cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HB).
    + eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity
        | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl
        | intros x _; reflexivity | exact Hsbm | intros a Ha; destruct Ha].
    + exact HF.
    + exact HL.
    + exact Hk.
    + (* the exit body: B7Cuts.b7_a826a4's assembly over ACtlCutP at the run's end map *)
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A82750_at ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      assert (HFLSI' : ACtlCutP.FLSI cx j fr R mem3) by exact (glue_f27_flsi_regs cx j fr regs3 R mem3 HFLSI HR9).
      assert (Ebig : A.Prog.SlotModel.t_big (ACtlCut.c_in cx) j = true).
      { unfold A.Prog.SlotModel.t_big. apply Z.leb_le. exact Hflen. }
      exists phi.
      split; [exact HP|].
      split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC HR2 HR3 HR4 HR8 HR9 HR19 HR26)|].
      split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|]. split; [exact HFLSI'|].
      split.
      { destruct HLK as (Hj' & R21 & HOUR). split; [exact Hj'|].
        split; [exact (glue_f27_rgv regs3 R 21 _ HR21 R21) | exact HOUR]. }
      split.
      { unfold ACtlCutP.FLS. rewrite Ebig.
        split; [exact HFLSI'|].
        split; [exact (glue_f27_rgv regs3 R 18 _ HR18 H18)|].
        split; [exact (glue_f27_rgv regs3 R 22 _ HR22 H22)|].
        split; [exact (glue_f27_rgv regs3 R 23 _ HR23 H23)|].
        split; [exact (glue_f27_rgv regs3 R 24 _ HR24 H24)|].
        split; [exact HR25|].
        split; [intros _; exact (conj Hphi0 (conj Hphi50 (conj Hg (conj Hph Hlen))))|].
        split; [exact (glue_f27_spill_regs regs3 R mem3 _ _ HR9 S152)
               | exact (glue_f27_spill_regs regs3 R mem3 _ _ HR9 S280)]. }
      exact (glue_f27_lt_regs cx fr j regs3 R mem3 HLT HR9).
    + exact Hrt.
Qed.

End GlueF27.

(* lib/A/ACtlG/F36_827f0.v -- GLUE for stage seg_F36_827f0 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v (at head lib/A/ACtl.v:853-855) (an earlier version, blob a3c6b7b35017, not in this delivery), Hypothesis seg_F36_827f0).  Written by a Theorem Labs lane
   after the pattern glue-pattern.md (a working note, not in this delivery) (G1-G5;
   worked examples lib/A/ACtlG/A5.v, F33.v, F38.v); single writer.  rule 24: no function proved (stage glue of a walk
   from already-proved runs).

   WHAT IT PROVES
     glue_seg_F36_827f0 : forall POST (j i : nat),
       CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A82964_at [Z.of_nat j]) ->
       CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat (S i)]) ->
       CF POST (ix_cut C_A8289c_at [Z.of_nat j; Z.of_nat i])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []): exactly ACtl.v's Section hypothesis
   seg_F36_827f0.  ENTRY C_A8289c_at [j; i] (ACtlCutP.v C_A8289c_at: RL, `getr regs 10 = 0 <-> t_blk = decl_i i`,
   bytes_at (fr + 64) (decl_i i), addressable (fr + 64) 32, LT).  The segment is 0x8289c `beqz a0,82964`:
     a0 = 0 (row i is the block's declaration): taken to 0x82964 = the EXIT C_A82964_at [j], with
       rgv 20 (t_want_m) = CAT + CAT_ROW i (RL's s4; Seg/F36.v f36_want_m_hit :352: row i matched, the earlier rows
       did not);
     a0 <> 0: falls to 0x828a0 = C_A828a0_at [j; i] (t_blk <> decl_i i), the entry of the stage glue_seg_F36_827f4
       (lib/A/ACtlG/F36_827f4.v, lane STORE), which takes the other two exits.
   Source: Seg/F36.v seg_F36_827f0_810 :3243-3345 (the same split on a0, the same model facts) and seg_F36_827f0
   :3352 (its composition with seg_F36_82810, which here sits inside glue_seg_F36_827f4).

   THE RUNS: lib/A/Prog/Seg/F36F.v f36_evt_hit_F / f36_evt_miss_F (Required qualified; re-runs of Seg/F36.v's
   f36_evt_hit / f36_evt_miss).  Both are one branch: no memory access, and the end map IS the start map.  Lifted at
   the empty footprint A.ACtlG.Kit.kit_RNG0.

   THE PROOF (glue-pattern.md section 3)
   G1  the entry cut at [Z.of_nat j; Z.of_nat i]: ix_cut's index equation, then C_A8289c_at's conjuncts (phi, the
       live list, FRAC, c_n bound, j <= 255, HB, FLSI, LK, RL, the a0 iff, the declaration bytes, addressable, LT);
       ixn 0 / ixn 1 are j / i by Nat2Z.id.  RL gives i <= 10, s4 = CAT + CAT_ROW i, s8 = CAT_N - i, the earlier
       rows' mismatch, t_rowsel = true and FLSX.
   G2  the split on bv_unsigned a0 = 0 (a Z decision).  a0 = 0: the hit run's premise x10 = 0 is that fact (by
       Lib.MState.Z_to_bv_bv_unsigned), and the iff gives t_blk = decl_i i.  a0 <> 0: the miss run takes
       v := bv_unsigned a0 with 0 < v < 2 ^ 64 (bv_unsigned_in_range), and the iff gives t_blk <> decl_i i.
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv to the runs' canonical map Regs6ss.mkR_of regs3.
   G4  ProgBridge.fevt_of_evtF and YA0nR.SRr_fevt at Kit.kit_RNG0 (fp_avoids vacuous).
   G5  the end state is MS (mkR_of regs3) .. pc' .. mem3 (the run keeps every register), so the walk is moved BACK
       to the entry map regs3 by SRr_xregs_eqv (proof Regs6ss.mkR_of_eqv regs3), and the exit cut is taken at regs3
       itself: every body fact of the entry is a fact of the exit map, no register move is needed.  Journal:
       ajournal_exec with the empty write set; frames / frame law / k bound unchanged (own6, kmax 14 + 2 j + 1 on
       all three cuts); ctl_rt_C unchanged.
       hit:  C_A82964_at [j]: FLSX from RL, rgv 20 (t_want_m) from RL's s4 and f36_want_m_hit.
       miss: C_A828a0_at [j; i]: RL as is, t_blk <> decl_i i, addressable (fr + 64) 32; then glue_seg_F36_827f4.

   ROUTE (C) (L3; the walk shell from a working branch 8ce82d7e310; ACtlCut.v (at head lib/A/ACtlCut.v:243)): ctl_from's runtime premise is
   A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (was ACtlCut.ctl_rt mem3).  Neither run reads a shadow byte and both exits keep
   ly3, S3 and the memory, so each passes the entry's Hrt as it is; VIS0 / OWNED_RO are gone from the Section with
   glue_seg_F36_827f4's switch.

   SECTION HYPOTHESES.  The Section mirrors ACtl.v's Section Ctl (ACtl.v:183-238 at a3c6b7b35017) in its order; the
   proof uses LAWS (ajournal_exec) and, through lane STORE's glue_seg_F36_827f4 (lib/A/ACtlG/F36_827f4.v, Required),
   the Section hypotheses lane CALL's glue_seg_F36_82820 takes and this file passes on: RELRO_CAT (the one shared
   text, owner a Theorem Labs lane) and CM_SPEC (a Theorem Labs lane's own
   A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec at ACtl.v's singleton list, ACtl.v:335-336 at
   blob d2b31b2cade), each cited BY NAME; GLOBS / CM_GLOB are not taken (glue_seg_F36_82810, reached through
   glue_seg_F36_827f4, fixes them as Section Lets, as ACtl.v:330-333).  The other Section variables / hypotheses
   are unused and drop at End Section.

   CITED BY NAME: YA0nR.SRr_xregs_eqv / SRr_fevt; A.ProgBridge.fevt_of_evtF / cfg_at_MS; YCbq.ajournal_exec;
   YK1b.mem_grows_refl; Regs6ss.mkR_of / mkR_of_eqv / xregs_eqv_sym; Lib.MState.Z_to_bv_bv_unsigned; Seg/F36F.v
   f36_evt_hit_F / f36_evt_miss_F; Seg/F36.v f36_want_m_hit (stated over SlotModel only); from the kit (Required,
   never copied): kit_wx, kit_segs_low, kit_RNG0.  No local helper: the move back to regs3 (G5) makes F36_8281c.v's
   bundle moves unnecessary here.

   CLOSURE: every project Require below is qualified, with the FULL directory in its From clause; no statement here
   names a frame-route identifier.  The closure reaches the frame route only through Seg/F36F.v and Seg/F36.v
   (closure rule 1).

   NAMES: every lib/Reusable and lib/Lib module is named through a full-path Module alias (R_<X> for
   OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.<X>, L_<X> for ...lib.Lib.<X>), never by a partial path
   (a Theorem Labs lane 05:28Z: 160 lib/Reusable and 15 lib/Lib modules have twins).

   FRAC's trailer conjunct q64 m (fr + 4088) (flag_addr ..) (Batch3, d36efc6152d): neither run writes memory or a
   register, and the exits are taken at the entry's map and memory, so FRAC is carried as one conjunct (exact HFRAC),
   never restated.

   BUILD STATE: type-check on 5da74c9c931, closure reaches no stand-in (glue base 121bf608343: AE2k / AF0m /
   AF0l / ACej / ACeh compiled from their own text, no port_core_refused substitution); reac_box_catalogue_match_c.v
   is the base's own ccd3e1f3c75.  No Axiom, no Parameter, no Admitted, no admit. *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG0f YG0d YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k AF0m ACeh ACtlCut ACtlCutP ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel C_reac_box_catalogue_match.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F36 F36F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit F36_827f4 F36_82820.
(* lib/A/Prog/YC4b.v:23 (reached through a Theorem Labs lane's C_reac_box_catalogue_match.v) sets Zify.zify_convert_to_euclidean_division_equations_flag
   to false only Locally, so it does not reach this file. lia here needs the flag true: false is its Stdlib default in Rocq 9.2, and a Required file's global
   `Ltac ... ::=` can also set it (both measured: a Local redefinition does not pass through Require, a global one does). False takes mod / div away from lia
   (build 20261029T091735Z: `No applicable tactic` at F36_82820.v:300).  The value these proofs were checked with (true) is restored for THIS file only. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Open Scope Z_scope.

(* Full-path Module aliases of the lib/Reusable and lib/Lib modules this file names. *)
Module R_YK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module R_YK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module R_YM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module R_YO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module R_YA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module R_YA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module R_YG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module R_YG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module R_YC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Module R_YCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module L_MState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module L_Regs6ss := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueF36_827f0.

(* ACtl.v's Section Ctl (ACtl.v:183-238 at a3c6b7b35017) in its order, RELRO_CAT in ACtl.v's exact text and name.
   Batch3's other new entries (RELRO_KIND_NAME, RELRO_FRAMES, MO_LE, KREPLY, KPARSE) are left out: this stage never
   uses them, and as Section facts in scope a tactic (lia) could pick one up and so change the lemma's arguments. *)
Context {fx : R_YK11.FPState} {rc : R_YM05.RunCeil} {LS : R_YO09.lib_shape}.
Variable B : R_YG0f.asyms.
Variable MT : R_YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> R_YG0d.in_img segs a.
Hypothesis RELRO_CAT : RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI.
Hypothesis LAWS : R_YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis TFIB_LIB : A.ACeh.TfibLib B.
Variable REAC_CTRL_IDENTITY_REPLY_K : Z.
Variable REAC_CTRL_PARSE_BC : Z.

(* ACtl.v's notation block, verbatim for the names this stage uses. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A8286c_at := (ACtlCutP.C_A8286c_at B).
Local Notation C_A8289c_at := (ACtlCutP.C_A8289c_at B).
Local Notation C_A828a0_at := (ACtlCutP.C_A828a0_at B).
Local Notation C_A828d8_at := (ACtlCutP.C_A828d8_at B).
Local Notation C_A828cc_at := (ACtlCutP.C_A828cc_at B).
Local Notation C_A82964_at := (ACtlCutP.C_A82964_at B).

(* What lane CALL's glue_seg_F36_82820 takes, cited BY NAME (one text each): CM_SPEC is ACtl.v:335-336's text
   (blob d2b31b2cade); glue_seg_F36_82810 fixes GLOBS / CM_GLOB at ACtl.v's singleton list. *)
Hypothesis CM_SPEC : A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI
  [(A.Prog.C_reac_box_catalogue_match.A_CM_TBL, A.Prog.C_reac_box_catalogue_match.CM_ROWS)].

Lemma glue_seg_F36_827f0 : forall POST (j i : nat),
  CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A82964_at [Z.of_nat j]) -> CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat (S i)]) ->
  CF POST (ix_cut C_A8289c_at [Z.of_nat j; Z.of_nat i]).
Proof.
  intros POST j i H8d8 H964 H86c.
  pose proof (A.ACtlG.F36_827f4.glue_seg_F36_827f4 B MT XM_LIB RLO RHI RELRO_IMG RELRO_CAT LAWS TFIB_SYMS
                CM_SPEC POST j i H8d8 H86c) as H8a0.
  intros cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j; Z.of_nat i] (ix_cut; C_A8289c_at). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A8289c_at ACtlCutP.ixn nth] in Hb.
  rewrite !Znat.Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HFLSI & HLK & HRL & Hiff & Hrow & Had & HLT).
  pose proof HRL as (Hi10 & H20 & H24 & Hprev & Hsel & HFLSX).
  (* G3: the cut's configuration in the runs' state form, the walk moved to the runs' canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A8289c_at [Z.of_nat j; Z.of_nat i])) with 0x8289c.
  apply (R_YA0nR.SRr_xregs_eqv segs W3 (L_Regs6ss.mkR_of regs3) regs3 R_YK11.fp_regs
           (Z_to_bv 64 0x8289c) R_YK11.fp_csr None mem3 (R_YK11.seg_rom segs) md3 (POST cx));
    [| exact (L_Regs6ss.xregs_eqv_sym _ _ (L_Regs6ss.mkR_of_eqv regs3))].
  unfold L_Regs6ss.mkR_of.
  (* G2: the split on a0 (x10). *)
  destruct (Z.eq_dec (bv_unsigned (R_YK11.getr regs3 10)) 0) as [E0|E0].
  - (* a0 = 0: row i is the block's declaration; f36_evt_hit_F, beqz taken to 0x82964 = EXIT C_A82964_at [j] *)
    assert (H10 : R_YK11.getr regs3 10 = Z_to_bv 64 0).
    { rewrite <- (L_MState.Z_to_bv_bv_unsigned (R_YK11.getr regs3 10)), E0. reflexivity. }
    assert (Ed : A.Prog.SlotModel.t_blk (ACtlCut.c_in cx) j = A.Prog.SlotModel.decl_i (Z.of_nat i))
      by exact (proj1 Hiff H10).
    (* G4: the lift at the empty footprint *)
    eapply (R_YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx)).
    { apply A.ProgBridge.fevt_of_evtF.
      apply (A.Prog.Seg.F36F.f36_evt_hit_F A.ACtlG.Kit.kit_RNG0). exact H10. }
    { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
    (* G5: the end state MS (mkR_of regs3) .. 0x82964 .. mem3; back to regs3, then the exit cut there *)
    intros ms' md' HQ0 Hsbm. cbv beta in HQ0. subst ms'.
    change (R_YA0n.SRr segs W3 (R_YG0d.cfg_at segs 0x82964 (L_Regs6ss.mkR_of regs3) mem3 md') (POST cx)).
    rewrite A.ProgBridge.cfg_at_MS.
    apply (R_YA0nR.SRr_xregs_eqv segs W3 regs3 (L_Regs6ss.mkR_of regs3) R_YK11.fp_regs
             (Z_to_bv 64 0x82964) R_YK11.fp_csr None mem3 (R_YK11.seg_rom segs) md' (POST cx));
      [| exact (L_Regs6ss.mkR_of_eqv regs3)].
    change (R_YA0n.SRr segs W3
              (R_YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82964_at [Z.of_nat j])) regs3 mem3 md') (POST cx)).
    apply (H964 cx [Z.of_nat j] fr k ly3 S3 W3 regs3 mem3 md' HB).
    + (* journal: no byte written, the model materialized (ajournal_exec) *)
      eapply (R_YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply R_YK1b.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha].
    + (* frames: own6 on both cuts *)
      exact HF.
    + (* the frame law: own6 on both cuts *)
      exact HL.
    + (* the event bound: 14 + 2 j + 1 on both cuts *)
      exact Hk.
    + (* the exit body, C_A82964_at [j] *)
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A82964_at ACtlCutP.ixn nth].
      split; [reflexivity|].
      rewrite !Znat.Nat2Z.id.
      exists phi.
      split; [exact HP|]. split; [exact HFRAC|].
      split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [exact HFLSI|]. split; [exact HLK|]. split; [exact HFLSX|].
      split; [|exact HLT].
      (* s4 = CAT + CAT_ROW i = t_want_m: row i matched, the earlier rows did not *)
      unfold ACtlCut.rgv in H20 |- *. rewrite H20.
      rewrite (A.Prog.Seg.F36.f36_want_m_hit (ACtlCut.c_in cx) j i Hsel Hi10 Hprev Ed).
      reflexivity.
    + (* ctl_rt_C B ly3 S3 mem3: ly3, S3 and the memory are the entry cut's *)
      exact Hrt.
  - (* a0 <> 0: f36_evt_miss_F, falls to 0x828a0 = C_A828a0_at [j; i]; then glue_seg_F36_827f4 *)
    assert (Ed : A.Prog.SlotModel.t_blk (ACtlCut.c_in cx) j <> A.Prog.SlotModel.decl_i (Z.of_nat i)).
    { intros HC. apply E0. rewrite (proj2 Hiff HC). reflexivity. }
    assert (Hv : 0 < bv_unsigned (R_YK11.getr regs3 10) < 2 ^ 64).
    { pose proof (bv_unsigned_in_range _ (R_YK11.getr regs3 10)) as Hr.
      unfold bv_modulus in Hr. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr. lia. }
    (* G4: the lift at the empty footprint *)
    eapply (R_YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx)).
    { apply A.ProgBridge.fevt_of_evtF.
      apply (A.Prog.Seg.F36F.f36_evt_miss_F A.ACtlG.Kit.kit_RNG0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               _ _ _ _ _ R_YK11.fp_regs R_YK11.fp_csr mem3 (bv_unsigned (R_YK11.getr regs3 10))).
      - exact (eq_sym (L_MState.Z_to_bv_bv_unsigned (R_YK11.getr regs3 10))).
      - exact Hv. }
    { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
    (* G5: the end state MS (mkR_of regs3) .. 0x828a0 .. mem3; back to regs3, then the cut there *)
    intros ms' md' HQ0 Hsbm. cbv beta in HQ0. subst ms'.
    change (R_YA0n.SRr segs W3 (R_YG0d.cfg_at segs 0x828a0 (L_Regs6ss.mkR_of regs3) mem3 md') (POST cx)).
    rewrite A.ProgBridge.cfg_at_MS.
    apply (R_YA0nR.SRr_xregs_eqv segs W3 regs3 (L_Regs6ss.mkR_of regs3) R_YK11.fp_regs
             (Z_to_bv 64 0x828a0) R_YK11.fp_csr None mem3 (R_YK11.seg_rom segs) md' (POST cx));
      [| exact (L_Regs6ss.mkR_of_eqv regs3)].
    change (R_YA0n.SRr segs W3
              (R_YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A828a0_at [Z.of_nat j; Z.of_nat i])) regs3 mem3 md')
              (POST cx)).
    apply (H8a0 cx [Z.of_nat j; Z.of_nat i] fr k ly3 S3 W3 regs3 mem3 md' HB).
    + (* journal: no byte written, the model materialized (ajournal_exec) *)
      eapply (R_YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply R_YK1b.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha].
    + (* frames: own6 on both cuts *)
      exact HF.
    + (* the frame law: own6 on both cuts *)
      exact HL.
    + (* the event bound: 14 + 2 j + 1 on both cuts *)
      exact Hk.
    + (* the body of C_A828a0_at [j; i] *)
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A828a0_at ACtlCutP.ixn nth].
      split; [reflexivity|].
      rewrite !Znat.Nat2Z.id.
      exists phi.
      split; [exact HP|]. split; [exact HFRAC|].
      split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [exact HFLSI|]. split; [exact HLK|]. split; [exact HRL|].
      split; [exact Ed|]. split; [exact Had | exact HLT].
    + (* ctl_rt_C B ly3 S3 mem3: ly3, S3 and the memory are the entry cut's *)
      exact Hrt.
Qed.

End GlueF36_827f0.

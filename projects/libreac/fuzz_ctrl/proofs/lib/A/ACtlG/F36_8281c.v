(* lib/A/ACtlG/F36_8281c.v -- GLUE for stage seg_F36_8281c of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v (at head lib/A/ACtl.v:862) (an earlier version, blob a3c6b7b35017, not in this delivery), Hypothesis seg_F36_8281c).  Written by a Theorem Labs lane
   after the pattern glue-pattern.md (a working note, not in this delivery) (G1-G5; worked
   examples lib/A/ACtlG/A5.v, F33.v, F38.v); single writer.  rule 24: no function proved (stage glue of a walk from
   an already-proved run).

   WHAT IT PROVES
     glue_seg_F36_8281c : forall POST (j : nat),
       CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A828c8_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []): exactly ACtl.v's Section hypothesis
   seg_F36_8281c.  ENTRY C_A828c8_at [j] (ACtlCutP.v C_A828c8_at: FLS, t_rowsel = false).  The segment is the one
   instruction 0x828c8 `li s4,0` (-> 0x828cc), then the call stretch 0x828cc -> 0x828d8, which is the stage
   glue_seg_F36_82820 (lib/A/ACtlG/F36_82820.v, lane CALL): this file proves CF POST (ix_cut C_A828cc_at [j]) ->
   CF POST (ix_cut C_A828c8_at [j]) and composes it with that stage, as Seg/F36.v seg_F36_8281c :3050-3099 composes
   its run with seg_F36_82820 :2353.

   THE RUN: lib/A/Prog/Seg/F36F.v f36_evt_8281c_F (Required qualified; re-run of Seg/F36.v's f36_evt_8281c), register
   only: the end map is the start map with x20 := 0, the memory is unchanged.  No memory access, so the run is
   lifted at the empty footprint A.ACtlG.Kit.kit_RNG0.

   THE PROOF (glue-pattern.md section 3)
   G1  the entry cut at [Z.of_nat j]: ix_cut's index equation, then C_A828c8_at's conjuncts (phi, the live list,
       FRAC, c_n bound, j <= 255, HB, FLSI, LK, FLS, t_rowsel = false, LT); ixn 0 [Z.of_nat j] = j by Nat2Z.id.
   G2  the run has no premise.
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv to the run's canonical map Regs6ss.mkR_of regs3.
   G4  ProgBridge.fevt_of_evtF and YA0nR.SRr_fevt at Kit.kit_RNG0 (fp_avoids vacuous).
   G5  the end state is MS R .. 0x828cc .. mem3, R the run's explicit map (x20 = 0, every other register regs3's):
       the exit cut C_A828cc_at [j] (ACtlCutP.v C_A828cc_at) is taken there.  Journal: ajournal_exec with the empty
       write set; frames / frame law / k bound unchanged (own6, kmax 14 + 2 j + 1 on both cuts); body: memory
       conjuncts unchanged, FRAC by Kit.kit_frac_move (cited by name; FRAC is never restated here), FLSI / LK / LT
       along registers 9 / 21 / 9, FLSX from the entry's FLS (f36_flsx_of_fls: FLSX is FLS without the s8 = x24
       pin) moved along registers 9 18 22 23 25, rgv R 20 (t_want_m) from x20 = 0 and t_rowsel = false (Seg/F36.v
       f36_want_m_unsel :368); ctl_rt_C unchanged.

   ROUTE (C) (L3; ACtlCut.v (at head lib/A/ACtlCut.v:243; from a working branch 8ce82d7e310)): ctl_from's runtime premise is
   A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (was ACtlCut.ctl_rt mem3).  The run reads no shadow byte and the exit keeps ly3,
   S3 and the memory, so it passes the entry's Hrt as it is; VIS0 / OWNED_RO are gone from the Section with
   glue_seg_F36_82820's switch (its exit is A.ProgWorldCtlRtC.ctl_rt_C_of_AR, which needs neither).

   LOCAL HELPERS (outside the Section; not in the kit; also Required by F36_82810.v): f36_flsi_move, f36_flsx_move,
   f36_lk_move, f36_lt_move (the transcribed bundles FLSI / FLSX / LK / LT, ACtlCutP.v:556-725, between two
   register maps that agree on the registers those bundles read; F33.v's f33_*_move with f36 names) and
   f36_flsx_of_fls.

   SECTION HYPOTHESES.  The Section mirrors ACtl.v's Section Ctl (ACtl.v:183-238 at a3c6b7b35017) in its order; the
   proof uses LAWS (ajournal_exec) and, through lane CALL's glue_seg_F36_82820 (lib/A/ACtlG/F36_82820.v, Required),
   the Section hypotheses that lemma takes, each cited BY NAME: RELRO_CAT (the one shared text, owner a Theorem Labs lane) and
   CM_SPEC (a Theorem Labs lane's own A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec at ACtl.v's singleton
   list, ACtl.v:335-336 at blob d2b31b2cade); GLOBS / CM_GLOB (A.ACtlG.F36_82820.cm_glob_stmt) are Section Lets, as
   ACtl.v:330-333 (the singleton list; or_introl eq_refl).
   The other Section variables / hypotheses are unused and drop at End Section.

   CITED BY NAME: YA0nR.SRr_xregs_eqv / SRr_fevt; A.ProgBridge.fevt_of_evtF / cfg_at_MS; YCbq.ajournal_exec;
   YK1b.mem_grows_refl; Regs6ss.mkR_of / mkR_of_eqv / xregs_eqv_sym; Seg/F36F.v f36_evt_8281c_F; Seg/F36.v
   f36_want_m_unsel (stated over SlotModel only); from the kit (Required, never copied): kit_wx, kit_segs_low,
   kit_frac_move, kit_RNG0.

   CLOSURE: every project Require below is qualified, with the FULL directory in its From clause; no statement here
   names a frame-route identifier.  The closure reaches the frame route only through Seg/F36F.v and Seg/F36.v
   (closure rule 1).

   NAMES: every lib/Reusable and lib/Lib module is named through a full-path Module alias (R_<X> for
   OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.<X>, L_<X> for ...lib.Lib.<X>), never by a partial path
   (a Theorem Labs lane 05:28Z: 160 lib/Reusable and 15 lib/Lib modules have twins).

   FRAC's trailer conjunct q64 m (fr + 4088) (flag_addr ..) (Batch3, d36efc6152d): the run writes no memory, so FRAC
   moves through Kit.kit_frac_move unchanged (Kit.v eb6f29acab77; Batch3 needed no change to it).

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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit F36_82820.
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

(* ---------------------------------------------------------------------------------------------------------
   The transcribed frame-loop bundles across a register change.  FLSI and LT read register 9 only (their spills),
   LK register 21, FLSX registers 9 18 22 23 25; every other conjunct is about memory or the model. *)
Lemma f36_flsi_move : forall cx j fr (regs regs' : bvmap 5 word) (m : word -> option byte),
  R_YK11.getr regs' 9 = R_YK11.getr regs 9 ->
  ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.FLSI cx j fr regs' m.
Proof.
  intros cx j fr regs regs' m E9 H.
  unfold ACtlCutP.FLSI, ACtlCutP.FLSH, ACtlCutP.PRO, ACtlCutP.FLC, ACtlCutP.spill, ACtlCut.rgv in *.
  rewrite E9. exact H.
Qed.

Lemma f36_flsx_move : forall cx j phi fr (regs regs' : bvmap 5 word) (m : word -> option byte),
  R_YK11.getr regs' 9 = R_YK11.getr regs 9 -> R_YK11.getr regs' 18 = R_YK11.getr regs 18 ->
  R_YK11.getr regs' 22 = R_YK11.getr regs 22 -> R_YK11.getr regs' 23 = R_YK11.getr regs 23 ->
  R_YK11.getr regs' 25 = R_YK11.getr regs 25 ->
  ACtlCutP.FLSX cx j phi fr regs m -> ACtlCutP.FLSX cx j phi fr regs' m.
Proof.
  intros cx j phi fr regs regs' m E9 E18 E22 E23 E25 H.
  unfold ACtlCutP.FLSX, ACtlCutP.FLSI, ACtlCutP.FLSH, ACtlCutP.PRO, ACtlCutP.FLC, ACtlCutP.spill,
    ACtlCut.rgv in *.
  rewrite E9, E18, E22, E23, E25. exact H.
Qed.

Lemma f36_lk_move : forall cx fr j (regs regs' : bvmap 5 word) (m : word -> option byte),
  R_YK11.getr regs' 21 = R_YK11.getr regs 21 ->
  ACtlCutP.LK cx fr j regs m -> ACtlCutP.LK cx fr j regs' m.
Proof.
  intros cx fr j regs regs' m E21 H. unfold ACtlCutP.LK, ACtlCut.rgv in *. rewrite E21. exact H.
Qed.

Lemma f36_lt_move : forall cx fr j (regs regs' : bvmap 5 word) (m : word -> option byte),
  R_YK11.getr regs' 9 = R_YK11.getr regs 9 ->
  ACtlCutP.LT cx fr j regs m -> ACtlCutP.LT cx fr j regs' m.
Proof.
  intros cx fr j regs regs' m E9 H.
  unfold ACtlCutP.LT, ACtlCutP.IFS, ACtlCutP.FSj, ACtlCutP.FSb, ACtlCutP.spill, ACtlCut.rgv in *.
  rewrite E9. exact H.
Qed.

(* FLSX is FLS without its s8 = x24 pin (ACtlCutP.v:683-706); Seg/F36.v's flsx_of_fls. *)
Lemma f36_flsx_of_fls : forall cx j phi fr (regs : bvmap 5 word) (m : word -> option byte),
  ACtlCutP.FLS cx j phi fr regs m -> ACtlCutP.FLSX cx j phi fr regs m.
Proof.
  intros cx j phi fr regs m (HI & H18 & H22 & H23 & _ & H25 & H50 & H152 & H280).
  exact (conj HI (conj H18 (conj H22 (conj H23 (conj H25 (conj H50 (conj H152 H280))))))).
Qed.

Section GlueF36_8281c.

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
Local Notation C_A828c8_at := (ACtlCutP.C_A828c8_at B).
Local Notation C_A828cc_at := (ACtlCutP.C_A828cc_at B).
Local Notation C_A828d8_at := (ACtlCutP.C_A828d8_at B).

(* What lane CALL's glue_seg_F36_82820 (lib/A/ACtlG/F36_82820.v, Required) takes, cited BY NAME from its file: one
   text each, never a second copy; at ACtl.v's singleton list: GLOBS and CM_GLOB are Section Lets as ACtl.v:330-333
   (blob d2b31b2cade), CM_SPEC is ACtl.v:335-336's text. *)
Let GLOBS : list (Z * Z) :=
  [(A.Prog.C_reac_box_catalogue_match.A_CM_TBL, A.Prog.C_reac_box_catalogue_match.CM_ROWS)].
Let CM_GLOB : A.ACtlG.F36_82820.cm_glob_stmt GLOBS := or_introl eq_refl.
Hypothesis CM_SPEC : A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI
  [(A.Prog.C_reac_box_catalogue_match.A_CM_TBL, A.Prog.C_reac_box_catalogue_match.CM_ROWS)].

Lemma glue_seg_F36_8281c : forall POST (j : nat), CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A828c8_at [Z.of_nat j]).
Proof.
  intros POST j H8d8.
  pose proof (A.ACtlG.F36_82820.glue_seg_F36_82820 B MT XM_LIB RLO RHI RELRO_IMG RELRO_CAT LAWS TFIB_SYMS
                GLOBS CM_GLOB CM_SPEC POST j H8d8) as HX.
  intros cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut; C_A828c8_at). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A828c8_at ACtlCutP.ixn nth] in Hb.
  rewrite !Znat.Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HFLSI & HLK & HFLS & Hsel & HLT).
  (* G3: the cut's configuration in the run's state form, the walk moved to the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A828c8_at [Z.of_nat j])) with 0x828c8.
  apply (R_YA0nR.SRr_xregs_eqv segs W3 (L_Regs6ss.mkR_of regs3) regs3 R_YK11.fp_regs
           (Z_to_bv 64 0x828c8) R_YK11.fp_csr None mem3 (R_YK11.seg_rom segs) md3 (POST cx));
    [| exact (L_Regs6ss.xregs_eqv_sym _ _ (L_Regs6ss.mkR_of_eqv regs3))].
  unfold L_Regs6ss.mkR_of.
  (* G4: the lift at the empty footprint (0x828c8 li s4,0 makes no memory access). *)
  eapply (R_YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx)).
  { apply A.ProgBridge.fevt_of_evtF.
    apply (A.Prog.Seg.F36F.f36_evt_8281c_F A.ACtlG.Kit.kit_RNG0). }
  { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
  (* G5: the end state MS R .. 0x828cc .. mem3, R the run's own map: the exit cut C_A828cc_at [j] there. *)
  intros ms' md' HQ0 Hsbm. cbv beta in HQ0. subst ms'.
  match goal with |- context [L_MState.MS ?R0 _ _ _ _ _ _] => set (R := R0) end.
  change (R_YA0n.SRr segs W3
            (R_YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A828cc_at [Z.of_nat j])) R mem3 md') (POST cx)).
  assert (E2 : R_YK11.getr R 2 = R_YK11.getr regs3 2) by reflexivity.
  assert (E3 : R_YK11.getr R 3 = R_YK11.getr regs3 3) by reflexivity.
  assert (E4 : R_YK11.getr R 4 = R_YK11.getr regs3 4) by reflexivity.
  assert (E8 : R_YK11.getr R 8 = R_YK11.getr regs3 8) by reflexivity.
  assert (E9 : R_YK11.getr R 9 = R_YK11.getr regs3 9) by reflexivity.
  assert (E18 : R_YK11.getr R 18 = R_YK11.getr regs3 18) by reflexivity.
  assert (E19 : R_YK11.getr R 19 = R_YK11.getr regs3 19) by reflexivity.
  assert (E21 : R_YK11.getr R 21 = R_YK11.getr regs3 21) by reflexivity.
  assert (E22 : R_YK11.getr R 22 = R_YK11.getr regs3 22) by reflexivity.
  assert (E23 : R_YK11.getr R 23 = R_YK11.getr regs3 23) by reflexivity.
  assert (E25 : R_YK11.getr R 25 = R_YK11.getr regs3 25) by reflexivity.
  assert (E26 : R_YK11.getr R 26 = R_YK11.getr regs3 26) by reflexivity.
  assert (K20 : R_YK11.getr R 20 = Z_to_bv 64 0) by reflexivity.
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HB).
  - (* journal: no byte written, the model materialized (ajournal_exec) *)
    eapply (R_YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply R_YK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha].
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: 14 + 2 j + 1 on both cuts *)
    exact Hk.
  - (* the exit body, C_A828cc_at [j] *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A828cc_at ACtlCutP.ixn nth].
    split; [reflexivity|].
    rewrite !Znat.Nat2Z.id.
    exists phi.
    split; [exact HP|].
    split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC E2 E3 E4 E8 E9 E19 E26)|].
    split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
    split; [exact (f36_flsi_move cx j fr regs3 R mem3 E9 HFLSI)|].
    split; [exact (f36_lk_move cx fr j regs3 R mem3 E21 HLK)|].
    split; [exact (f36_flsx_move cx j phi fr regs3 R mem3 E9 E18 E22 E23 E25
                     (f36_flsx_of_fls cx j phi fr regs3 mem3 HFLS))|].
    split.
    { (* s4 = 0 = t_want_m: the row was not selected *)
      unfold ACtlCut.rgv. rewrite K20, (A.Prog.Seg.F36.f36_want_m_unsel (ACtlCut.c_in cx) j Hsel).
      reflexivity. }
    exact (f36_lt_move cx fr j regs3 R mem3 E9 HLT).
  - (* ctl_rt_C B ly3 S3 mem3: ly3, S3 and the memory are the entry cut's *)
    exact Hrt.
Qed.

End GlueF36_8281c.

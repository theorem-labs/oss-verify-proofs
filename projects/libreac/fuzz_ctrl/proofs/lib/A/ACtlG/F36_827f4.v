(* lib/A/ACtlG/F36_827f4.v -- GLUE for stage seg_F36_827f4 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v, `Hypothesis seg_F36_827f4`, :718-719 at a3c6b7b35017).  Written by a Theorem Labs lane (under
   a Theorem Labs lane), one writer.  Pattern: glue-pattern.md (a working note, not in this delivery) (G1-G5, section 4
   for a run that writes memory); worked example lib/A/ACtlG/A5.v; register end map as lib/A/ACtlG/F38.v.  rule 24:
   no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F36_827f4 : forall POST (j i : nat),
       CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat (S i)]) ->
       CF POST (ix_cut C_A828a0_at [Z.of_nat j; Z.of_nat i])
   with ACtl.v's own CF notation, i.e. exactly ACtl.v's Section hypothesis seg_F36_827f4.  ENTRY C_A828a0_at [j; i]
   (pc 0x828a0, ACtlCutP.v:2843-2856; its RL gives s4 = CAT + CAT_ROW i, s8 = CAT_N - i).  The run 0x828a0 .. 0x828ac
   `sb s11,8(s3)` .. `sb s11,11(s3)` writes the four frame-shadow bytes S(fr) + 8 .. + 11, then s8 -= 1, s4 += 296
   and the latch at 0x828b8 branches on s8:
   - i < 10 (s8 = 11 - i >= 2): A.Prog.Seg.F36F.f36_evt_back_F, back edge to 0x8286c = the EXIT C_A8286c_at
     [j; S i] (ACtlCutP.v:2790-2801): RL at S i from the entry's RL, its row-miss t_blk j <> decl_i i, and
     CAT_ROW = 296; FLSX / LK / LT kept across the stores.
   - i = 10 (s8 = 1): A.Prog.Seg.F36F.f36_evt_out_F, falls to 0x828bc = C_A828bc_at [j] (ACtlCutP.v:2861-2872):
     t_want_m j = 0 because no row matched (Seg/F36.v f36_want_m_miss from the RL's rows 0..9 and the row-10 miss),
     then the dependency glue_seg_F36_82810 (lane REG) reaches the EXIT C_A828d8_at.
   Source proof: Seg/F36.v seg_F36_827f4_810 :3104-3239 and seg_F36_827f4 :3347 (blob 242c29c887f9).

   THE PROOF: G1 the entry body; G2 + G5 by A.ACtlG.F36_82814.f36g_stage at the window [S(fr) + 8, S(fr) + 12)
   (o = 8, e = 12, n = 4); G3 ProgBridge.cfg_at_MS + YA0nR.SRr_xregs_eqv to mkR_of regs3; G4 fevt_of_evtF +
   tfibsegs_rsegs + THE lift YA0nR.SRr_fevt_hid; G5 the run's end map R (registers 20 and 24 written, every other
   one reg_get regs3 r, so getr R r = getr regs3 r holds by reflexivity, as F38.v's K facts) is the exit cut's map.

   ROUTE (C) (L3; ACtlCut.v (at head lib/A/ACtlCut.v:243; from a working branch 8ce82d7e310)): ctl_from's runtime premise is
   A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (was ACtlCut.ctl_rt mem3).  This file reads no shadow byte itself: it hands Hrt
   to f36g_stage (F36_82814.v, whose window read is the (F) disjunct of cut_shadow) and passes f36g_stage's
   ctl_rt_C B ly3 S3 m' to both exits.  VIS0 / OWNED_RO are gone from the Section with glue_seg_F36_82810's switch.

   SECTION HYPOTHESES
   - LAWS : R_YG0d.AR_laws segs B -- ACtl.v's own (ACtl.v:210), the core's AR law record.
   - the Section hypotheses lane CALL's glue_seg_F36_82820 takes, passed on through lane REG's
     glue_seg_F36_82810 (F36_82810.v, Required): RELRO_CAT (the one shared text, owner a Theorem Labs lane) and CM_SPEC
     (a Theorem Labs lane's own A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec at ACtl.v's singleton list,
     ACtl.v:335-336 at blob d2b31b2cade), by NAME.  GLOBS / CM_GLOB are not taken: glue_seg_F36_82810 fixes them
     (Section Lets, as ACtl.v:330-333).
   ACtl.v's Section Ctl (:183-238 at a3c6b7b35017) is mirrored in its order without Batch3's five entries this stage
   never uses (see the Section); the unused entries vanish at End Section.

   CITED BY NAME: A.ACtlG.F36_82814.f36g_stage (this lane); A.Prog.Seg.F36F.f36_evt_back_F / f36_evt_out_F;
   A.Prog.Seg.F36.f36_want_m_miss (outside Seg/F36.v's Section, a pure model fact); R_YA0nR.SRr_fevt_hid /
   SRr_xregs_eqv; A.ProgBridge.fevt_of_evtF / tfibsegs_rsegs / cfg_at_MS / fp_avoids_RNG_W;
   L_Regs6ss.mkR_of_eqv / xregs_eqv_sym; the kit's kit_wx.

   CLOSURE: every project Require names the FULL directory in its From clause; every lib/Reusable and lib/Lib module
   is used through a full-path Module alias (R_<X>, L_<X>) or a full-path notation; no STATEMENT names a frame-route
   identifier.  FRAC is not restated in this file (f36g_stage carries it, its trailer conjunct q64 m (fr + 4088)
   (flag_addr ..) of Batch3 d36efc6152d included).  The lemma is
   `glue_seg_F36_827f4 {fx rc} B MT XM_LIB RLO RHI RELRO_IMG RELRO_CAT LAWS TFIB_SYMS CM_SPEC`
   (About).

   BUILD STATE: type-check on 5da74c9c931, closure reaches no stand-in (glue base 121bf608343: AE2k / AF0m /
   AF0l / ACej / ACeh compiled from their own text, no port_core_refused substitution); reac_box_catalogue_match_c.v
   is the base's own ccd3e1f3c75.  No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI04 YM05 YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG0f YG01 YG0d YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k Img0 ACtlCut ACtlCutP ProgBridge AF0m ACeh.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel C_reac_box_catalogue_match.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F36 F36F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit F36_82814 F36_82810 F36_82820.
(* lib/A/Prog/YC4b.v:23 (reached through a Theorem Labs lane's C_reac_box_catalogue_match.v) sets Zify.zify_convert_to_euclidean_division_equations_flag
   to false only Locally, so it does not reach this file. lia here needs the flag true: false is its Stdlib default in Rocq 9.2, and a Required file's global
   `Ltac ... ::=` can also set it (both measured: a Local redefinition does not pass through Require, a global one does). False takes mod / div away from lia
   (build 20261029T091735Z: `No applicable tactic` at F36_82820.v:300).  The value these proofs were checked with (true) is restored for THIS file only. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* Full-path Module aliases for every lib/Reusable and lib/Lib module this file names: 160 lib/Reusable and
   15 lib/Lib modules have twins (lib/A/Reusable, lib/A/Bz/Lib, ...), so no partial path is used (a Theorem Labs lane
   05:28Z).  R_<X> is lib/Reusable/<X>, L_<X> is lib/Lib/<X>. *)
Module L_MState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module L_Regs6ss := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module R_YA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module R_YA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module R_YC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Module R_YG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module R_YG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation segs := A.AB1v.tfibsegs.
Local Notation getrC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr.
Local Notation fpR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs.
Local Notation fpC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr.
Local Notation romC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom.
Local Notation romA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom.
Local Notation reg_get := LinuxProcessSemantics.Riscv.Sem.reg_get.
Local Notation CAT := A.Prog.SlotModel.CAT.
Local Notation CAT_ROW := A.Prog.SlotModel.CAT_ROW.
Local Notation CAT_N := A.Prog.SlotModel.CAT_N.

Section GlueF36_827f4.

(* ACtl.v's Section Ctl (ACtl.v:183-238 at a3c6b7b35017) in its order, RELRO_CAT in ACtl.v's exact text and name.
   Batch3's other new entries (RELRO_KIND_NAME, RELRO_FRAMES, MO_LE, KREPLY, KPARSE) are left out: this stage never
   uses them, and as Section facts in scope a tactic (lia) could pick one up and so change the lemma's arguments. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
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

(* ACtl.v's notation block, verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A828a0_at := (ACtlCutP.C_A828a0_at B).
Local Notation C_A8286c_at := (ACtlCutP.C_A8286c_at B).
Local Notation C_A828bc_at := (ACtlCutP.C_A828bc_at B).
Local Notation C_A828d8_at := (ACtlCutP.C_A828d8_at B).
Local Notation C_A828cc_at := (ACtlCutP.C_A828cc_at B).

(* What lane CALL's glue_seg_F36_82820 takes, cited BY NAME (one text each): CM_SPEC is ACtl.v:335-336's text
   (blob d2b31b2cade); glue_seg_F36_82810 fixes GLOBS / CM_GLOB at ACtl.v's singleton list. *)
Hypothesis CM_SPEC : A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI
  [(A.Prog.C_reac_box_catalogue_match.A_CM_TBL, A.Prog.C_reac_box_catalogue_match.CM_ROWS)].

Lemma glue_seg_F36_827f4 : forall POST (j i : nat),
  CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat (S i)]) -> CF POST (ix_cut C_A828a0_at [Z.of_nat j; Z.of_nat i]).
Proof.
  intros POST j i HX H7c0.
  pose proof (A.ACtlG.F36_82810.glue_seg_F36_82810 B MT XM_LIB RLO RHI RELRO_IMG RELRO_CAT LAWS TFIB_SYMS
                CM_SPEC POST j HX) as H810.
  intros cx idx fr k ly3 S3 W3 regs3 mem3 md3 Hbase HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j; Z.of_nat i] *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A828a0_at ACtlCutP.ixn nth] in Hb.
  rewrite !Nat2Z.id in Hb.
  destruct Hb as (phi & Hperm & HFRAC & Hcn & Hj & HHB & HFLSI & HLK & HRL & Hne & Had & HLT).
  pose proof HRL as (Hi10 & H20 & H24 & Hprev & Hsel & HFLSX).
  (* G2: f36g_stage at the window [S(fr) + 8, S(fr) + 12) *)
  destruct (A.ACtlG.F36_82814.f36g_stage B MT XM_LIB RLO RHI LAWS cx fr k ly3 S3 W3 regs3 mem3 md3 phi j 8 12 4%nat
              Hbase HJ HF HL Hperm HFRAC HHB HFLSI HLK HFLSX HLT Hrt
              ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia))
    as (E19 & HS0 & HS1 & (bs & HRW) & Hrng & HSTEP).
  assert (R19 : reg_get regs3 19 = Z_to_bv 64 (ACtlCutP.Sfr fr)) by exact E19.
  assert (R20 : reg_get regs3 20 = Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i)) by exact H20.
  (* G3: the cut's configuration in the run's state form, the walk moved to the run's canonical map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A828a0_at [Z.of_nat j; Z.of_nat i])) with 0x828a0.
  apply (R_YA0nR.SRr_xregs_eqv segs W3 (L_Regs6ss.mkR_of regs3) regs3 fpR (Z_to_bv 64 0x828a0) fpC None
           mem3 (romC segs) md3 (POST cx));
    [| exact (L_Regs6ss.xregs_eqv_sym _ _ (L_Regs6ss.mkR_of_eqv regs3))].
  destruct (Nat.eq_dec i 10) as [Ei|Hi].
  - (* i = 10, s8 = 1: the latch falls through to 0x828bc *)
    subst i.
    assert (R24 : reg_get regs3 24 = Z_to_bv 64 1).
    { unfold ACtlCut.rgv in H24. etransitivity; [exact H24|]. f_equal. }
    (* G4: f36_evt_out_F and its lift *)
    pose proof (A.Prog.Seg.F36F.f36_evt_out_F (A.ProgBridge.RNG_W (R_YA0n.w_H W3))
      (reg_get regs3 1) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6)
      (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10) (reg_get regs3 11)
      (reg_get regs3 12) (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16)
      (reg_get regs3 17) (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21)
      (reg_get regs3 22) (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25) (reg_get regs3 26)
      (reg_get regs3 27) (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30) (reg_get regs3 31)
      fpR fpC mem3 (ACtlCutP.Sfr fr) (CAT + CAT_ROW * Z.of_nat 10) bs R19 R24 R20
      ltac:(unfold A.Prog.SlotModel.CAT, A.Prog.SlotModel.CAT_ROW; lia)
      ltac:(unfold A.Prog.SlotModel.CAT, A.Prog.SlotModel.CAT_ROW; lia)
      HRW HS0 HS1 Hrng)
      as HRUN.
    change (romA A.Img0.rsegs) with (romC A.Img0.rsegs) in HRUN.
    pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
    rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
    apply (R_YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3
             (A.ProgBridge.RNG_W (R_YA0n.w_H W3)) _ (POST cx) HFS).
    { apply A.ProgBridge.fp_avoids_RNG_W. }
    intros ms' md' HP Hhid Hsbm.
    destruct HP as (m' & Ems & MU & WM & HCS). subst ms'.
    change (forall x : word, R_YA0n.w_H W3 x = true -> m' x = mem3 x) in Hhid.
    (* G5: the run's end map R is the cut's map at 0x828bc *)
    match goal with
    | |- context [L_MState.MS ?R _ _ _ _ _ _] => set (Rb := R)
    end.
    change (R_YA0n.SRr segs W3
              (R_YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A828bc_at [Z.of_nat j])) Rb m' md') (POST cx)).
    assert (K2 : getrC Rb 2 = getrC regs3 2) by reflexivity.
    assert (K3 : getrC Rb 3 = getrC regs3 3) by reflexivity.
    assert (K4 : getrC Rb 4 = getrC regs3 4) by reflexivity.
    assert (K8 : getrC Rb 8 = getrC regs3 8) by reflexivity.
    assert (K9 : getrC Rb 9 = getrC regs3 9) by reflexivity.
    assert (K18 : getrC Rb 18 = getrC regs3 18) by reflexivity.
    assert (K19 : getrC Rb 19 = getrC regs3 19) by reflexivity.
    assert (K21 : getrC Rb 21 = getrC regs3 21) by reflexivity.
    assert (K22 : getrC Rb 22 = getrC regs3 22) by reflexivity.
    assert (K23 : getrC Rb 23 = getrC regs3 23) by reflexivity.
    assert (K25 : getrC Rb 25 = getrC regs3 25) by reflexivity.
    assert (K26 : getrC Rb 26 = getrC regs3 26) by reflexivity.
    destruct (HSTEP Rb m' md' MU WM HCS Hhid Hsbm K2 K3 K4 K8 K9 K18 K19 K21 K22 K23 K25 K26)
      as (HJ' & HFRAC' & HHB' & HFLSI' & HLK' & HFLSX' & HLT' & Hrt').
    apply (H810 cx [Z.of_nat j] fr k ly3 S3 W3 Rb m' md' Hbase HJ' HF HL Hk); [|exact Hrt'].
    (* the body C_A828bc_at (ACtlCutP.v:2861-2872) at [j] *)
    split; [reflexivity|].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A828bc_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    exists phi.
    split; [exact Hperm|]. split; [exact HFRAC'|]. split; [exact Hcn|]. split; [exact Hj|].
    split; [exact HHB'|]. split; [exact HFLSI'|].
    split; [exact HLK'|]. split; [exact HFLSX'|]. split; [exact Hsel|].
    split; [|exact HLT'].
    (* no row matched: rows 0..9 by RL, row 10 by the entry's miss *)
    apply (A.Prog.Seg.F36.f36_want_m_miss (ACtlCut.c_in cx) j Hsel).
    intros i' Hi'. destruct (Nat.eq_dec i' 10) as [->|Hne']; [exact Hne | apply Hprev; lia].
  - (* i < 10, s8 = 11 - i >= 2: the back edge to 0x8286c with row S i *)
    assert (R24 : reg_get regs3 24 = Z_to_bv 64 (CAT_N - Z.of_nat i)) by exact H24.
    (* G4: f36_evt_back_F and its lift *)
    pose proof (A.Prog.Seg.F36F.f36_evt_back_F (A.ProgBridge.RNG_W (R_YA0n.w_H W3))
      (reg_get regs3 1) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6)
      (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10) (reg_get regs3 11)
      (reg_get regs3 12) (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16)
      (reg_get regs3 17) (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21)
      (reg_get regs3 22) (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25) (reg_get regs3 26)
      (reg_get regs3 27) (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30) (reg_get regs3 31)
      fpR fpC mem3 (ACtlCutP.Sfr fr) (CAT_N - Z.of_nat i) (CAT + CAT_ROW * Z.of_nat i) bs R19 R24 R20
      ltac:(unfold A.Prog.SlotModel.CAT_N; lia)
      ltac:(unfold A.Prog.SlotModel.CAT, A.Prog.SlotModel.CAT_ROW; lia)
      ltac:(unfold A.Prog.SlotModel.CAT, A.Prog.SlotModel.CAT_ROW; lia)
      HRW HS0 HS1 Hrng)
      as HRUN.
    change (romA A.Img0.rsegs) with (romC A.Img0.rsegs) in HRUN.
    pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
    rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
    apply (R_YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3
             (A.ProgBridge.RNG_W (R_YA0n.w_H W3)) _ (POST cx) HFS).
    { apply A.ProgBridge.fp_avoids_RNG_W. }
    intros ms' md' HP Hhid Hsbm.
    destruct HP as (m' & Ems & MU & WM & HCS). subst ms'.
    change (forall x : word, R_YA0n.w_H W3 x = true -> m' x = mem3 x) in Hhid.
    (* G5: the run's end map R is the cut's map at 0x8286c, row S i *)
    match goal with
    | |- context [L_MState.MS ?R _ _ _ _ _ _] => set (Rb := R)
    end.
    change (R_YA0n.SRr segs W3
              (R_YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat (S i)]))
                 Rb m' md') (POST cx)).
    assert (K2 : getrC Rb 2 = getrC regs3 2) by reflexivity.
    assert (K3 : getrC Rb 3 = getrC regs3 3) by reflexivity.
    assert (K4 : getrC Rb 4 = getrC regs3 4) by reflexivity.
    assert (K8 : getrC Rb 8 = getrC regs3 8) by reflexivity.
    assert (K9 : getrC Rb 9 = getrC regs3 9) by reflexivity.
    assert (K18 : getrC Rb 18 = getrC regs3 18) by reflexivity.
    assert (K19 : getrC Rb 19 = getrC regs3 19) by reflexivity.
    assert (K21 : getrC Rb 21 = getrC regs3 21) by reflexivity.
    assert (K22 : getrC Rb 22 = getrC regs3 22) by reflexivity.
    assert (K23 : getrC Rb 23 = getrC regs3 23) by reflexivity.
    assert (K25 : getrC Rb 25 = getrC regs3 25) by reflexivity.
    assert (K26 : getrC Rb 26 = getrC regs3 26) by reflexivity.
    (* the two registers the latch writes: s4 += 296 (the next row), s8 -= 1 *)
    assert (K20 : getrC Rb 20 = Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i + 296)) by reflexivity.
    assert (K24 : getrC Rb 24 = Z_to_bv 64 (CAT_N - Z.of_nat i - 1)) by reflexivity.
    destruct (HSTEP Rb m' md' MU WM HCS Hhid Hsbm K2 K3 K4 K8 K9 K18 K19 K21 K22 K23 K25 K26)
      as (HJ' & HFRAC' & HHB' & HFLSI' & HLK' & HFLSX' & HLT' & Hrt').
    apply (H7c0 cx [Z.of_nat j; Z.of_nat (S i)] fr k ly3 S3 W3 Rb m' md' Hbase HJ' HF HL Hk); [|exact Hrt'].
    (* the body C_A8286c_at (ACtlCutP.v:2790-2801) at [j; S i] *)
    split; [reflexivity|].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A8286c_at ACtlCutP.ixn nth].
    rewrite !Nat2Z.id.
    exists phi.
    split; [exact Hperm|]. split; [exact HFRAC'|]. split; [exact Hcn|]. split; [exact Hj|].
    split; [exact HHB'|]. split; [exact HFLSI'|].
    split; [exact HLK'|]. split; [lia|].
    split; [|exact HLT'].
    (* RL at row S i *)
    split; [lia|].
    split.
    { unfold ACtlCut.rgv. rewrite K20. f_equal. rewrite Nat2Z.inj_succ. unfold A.Prog.SlotModel.CAT_ROW. lia. }
    split.
    { unfold ACtlCut.rgv. rewrite K24. f_equal. rewrite Nat2Z.inj_succ. lia. }
    split.
    { intros i' Hi'. destruct (Nat.eq_dec i' i) as [->|Hne']; [exact Hne | apply Hprev; lia]. }
    split; [exact Hsel | exact HFLSX'].
Qed.

End GlueF36_827f4.

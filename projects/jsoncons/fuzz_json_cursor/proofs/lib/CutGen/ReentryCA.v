(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8PlanKit Pm8L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutShA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module RNA.
Definition mem := (word -> option byte).

Definition reentry_chk (NF : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (s : CC.subst) : bool :=
  (Nat.leb NF (CC.cp_nx c)
   && forallb (fun r => CSL.reg_is (SR.ps_regs ps) r (CC.esubstL NF s (nth r (CC.cp_regs cj) (ELit 0)))) (seq 1 31)
   && forallb (fun X => let X' := CC.ksubstL NF s X in (CC.has_cell (SR.ps_cells ps) X' || CX.fact2_ok (SR.ps_cells ps) X')%bool) (CC.cp_know cj)
   && APC.expr_vars_lt (CC.cp_nx c) (CC.cp_meas c))%bool.

Section Leaf.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBrest : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable Cred : nat -> env -> credit -> Prop.
Variable D0 : Z.
Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBrest FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Variable XI : nat -> env -> list (Z * Z) -> mem -> Model -> Prop.

Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).
Abbreviation AMBX := (CHA.ambX L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 XI).

Theorem reentry_leaf : forall i c ps j cj s,
  nth_error CPS j = Some cj ->
  SR.ps_pc ps = CC.cp_pc cj ->
  reentry_chk NF c ps cj s = true ->
  CHA.goto_amb_chk NF d c (nth i BLS []) (nth j BLS []) (nth i FFS []) (nth j FFS []) s = true ->
  (forall E E' R R' A M model M1 model1,
     CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> XI i E A M model -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
     XI j (CC.env_over NF s E') A M1 model1 /\ CC.meas cj (CC.env_over NF s E') < CC.meas c E) ->
  (forall E E' R' M M' cr, env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr -> Cred j (CC.env_over NF s E') cr) ->
  CCA.leaf_ok (hl_segs L) CPS AMBX K FPI i c ps.
Proof.
  intros i c ps j cj s Hcj Hpc Hchk Hgchk USER CRED fx' E R A M model E' R' M1 model1 HAt [HA HXI] HFP Hag HLF HIH.
  unfold reentry_chk in Hchk.
  apply andb_prop in Hchk as [Hchk Xmv]. apply andb_prop in Hchk as [Hchk Xkn]. apply andb_prop in Hchk as [Xnf Xregs]. apply Nat.leb_le in Xnf.
  pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
  destruct (USER E E' R R' A M model M1 model1 HAt HA HXI Hag HLF) as [HXIj HMEAS].
  assert (X0R : getr R' 0%bv = Z_to_bv 64 0) by (exact (CC.lf_x0 _ _ _ _ _ _ _ HLFv)).
  set (E2 := CC.env_over NF s E').
  rewrite Hpc.
  apply (HIH j cj fx' E2 R' A M1 model1 Hcj).
  -
    split.
    + intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
      * assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er; apply Z.eqb_eq in Er; exact Er). cbn [edenot]. exact X0R.
      * assert (Hr : (1 <= ridx r < 32)%nat).
        { unfold ridx. pose proof (bv_unsigned_in_range _ r) as B. change (bv_modulus 5) with 32 in B.
          unfold bv_eqb in Er. apply Z.eqb_neq in Er. change (bv_unsigned (0%bv : bv 5)) with 0 in Er. lia. }
        rewrite forallb_forall in Xregs. specialize (Xregs (ridx r) ltac:(apply in_seq; lia)).
        apply CSL.reg_is_sound in Xregs. destruct (CC.lf_regs _ _ _ _ _ _ _ HLFv _ _ Xregs) as [_ Hg]. rewrite CC.reg_of_ridx in Hg.
        rewrite Hg. unfold E2. apply CC.esubstL_denot.
    + unfold know_ok. apply Forall_forall. intros X' HX'. rewrite forallb_forall in Xkn. specialize (Xkn X' HX'). cbv zeta in Xkn.
      apply (CC.kentry_ok_ksubstL (hl_segs L) NF s E' _ X'). apply orb_prop in Xkn. destruct Xkn as [Xkn|Xkn].
      * apply CC.has_cell_In in Xkn. exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ Xkn).
      * apply (CX.fact2_ok_sound (hl_segs L) E' _ (SR.ps_cells ps) _ ltac:(unfold know_ok; apply Forall_forall; intros Y HY; exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HY)) Xkn).
  -
    split.
    + exact (CHA.goto_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
               i c ps j s Hgchk CRED E R A M model E' R' M1 model1 HAt HA Hag HLF).
    + exact HXIj.
  - exact HFP.
  - exact HMEAS.
Qed.
End Leaf.
End RNA.

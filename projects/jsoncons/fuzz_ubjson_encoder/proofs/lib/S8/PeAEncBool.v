(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PmModelFactsA PmStep PeStepA PmParKit PeASrcKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrame PeCFrameA PeEncKit PeACReset1 PeAEncScalP PeAEncNull.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_ac374_ac378.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEAENCT.
#[local] Transparent e_end_value.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.

Definition bbyte (v : bool) : Z := if v then 84 else 70.
Definition XB (v : bool) (R : bvmap 5 word) : Prop := getr R (reg 11) = Z_to_bv 64 (PEC.b2z v).

Lemma bool_runP v : PEAENCN.runP 0xac308 0xac35c (bbyte v) (XB v).
Proof.
  unfold PEAENCN.runP, XB. intros fx R M sp ov osk H1 H2 H3 G2 G10 G11 K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17.
  assert (HO : bv_unsigned (getr R (reg 10)) = ov) by (rewrite G10; apply L5.unsigned_lit; exact H2).
  assert (H11 : bv_unsigned (getr R (reg 11)) = PEC.b2z v) by (rewrite G11; apply L5.unsigned_lit; destruct v; cbn; lia).
  destruct v; cbn [PEC.b2z] in H11; cbn [bbyte].
  - pose proof (PEAENCSP.aenTA1_conc fx R M (fun j => match j with 2%nat => sp | 41%nat => osk | _ => 0 end)) as P. cbn beta iota in P. rewrite !HO, !H11 in P.
    L5SAR.feed P ltac:(first [assumption | unfold PEAENCSP.aligned; assumption | lia]).
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & C25 & S24 & S16 & S8).
    exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|].
    split; [intros j Hj; apply KS1; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|].
    split; [exact T1|]. split; [exact T2|]. split; [rewrite T8; exact G10|]. split; [exact T9|]. split; [exact T10|]. split; [exact T11|].
    split; [exact C25|]. split; [exact S24|]. split; [exact S16| exact S8].
  - pose proof (PEAENCSP.aenTA0_conc fx R M (fun j => match j with 2%nat => sp | 41%nat => osk | _ => 0 end)) as P. cbn beta iota in P. rewrite !HO, !H11 in P.
    L5SAR.feed P ltac:(first [assumption | unfold PEAENCSP.aligned; assumption | lia]).
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & C25 & S24 & S16 & S8).
    exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|].
    split; [intros j Hj; apply KS1; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|].
    split; [exact T1|]. split; [exact T2|]. split; [rewrite T8; exact G10|]. split; [exact T9|]. split; [exact T10|]. split; [exact T11|].
    split; [exact C25|]. split; [exact S24|]. split; [exact S16| exact S8].
Qed.

Lemma bool_runE0 : PEAENCN.runE0 0xac35c.
Proof.
  unfold PEAENCN.runE0. intros fx R M sp ov eb r s0v s1v a0v a1v H1 H2 H3 H4 H5 H6 H7 H8 G2 G8 G9 G10 G11 K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 RA.
  pose proof (PEAENCSP.aenTE0_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 38%nat => eb | 44%nat => r | 45%nat => s0v | 46%nat => s1v
      | 55%nat => a0v | 56%nat => a1v | _ => 0 end)) as P. cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PEAENCSP.aligned; assumption]).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11).
  pose proof RA as (Hr1 & Hr2).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac3c4 W_ac374 r F_ac374 eq_refl D_ac374 T1 ltac:(lia) Hr2) as MSR.
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MSR]|].
  split; [intros j Hj; apply KS1; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|].
  split; [exact T2|]. split; [exact T8|]. split; [exact T9| exact T10].
Qed.

Lemma bool_runE1 : PEAENCN.runE1 0xac35c.
Proof.
  unfold PEAENCN.runE1. intros fx R M sp ov eb ed cn r s0v s1v a0v a1v H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 G2 G8 G9 G10 G11
    K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 RA.
  pose proof RA as (Hr1 & Hr2).
  destruct (Z.eq_dec cn 18446744073709551615) as [CW|CNW].
  - rewrite CW in K26.
    pose proof (PEAENCSP.aenTE1w_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 38%nat => eb | 39%nat => ed | 44%nat => r | 45%nat => s0v | 46%nat => s1v
        | 55%nat => a0v | 56%nat => a1v | _ => 0 end)) as P. cbn beta iota in P.
    L5SAR.feed P ltac:(first [assumption | unfold PEAENCSP.aligned; assumption]).
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & C8).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac3c4 W_ac374 r F_ac374 eq_refl D_ac374 T1 ltac:(lia) Hr2) as MSR.
    exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MSR]|].
    split; [intros j Hj; apply KS1; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|].
    split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T10|]. rewrite CW. change ((18446744073709551615 + 1) mod 2 ^ 64) with 0. exact C8.
  - pose proof (PEAENCSP.aenTE1_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 38%nat => eb | 39%nat => ed | 42%nat => cn | 44%nat => r | 45%nat => s0v
        | 46%nat => s1v | 55%nat => a0v | 56%nat => a1v | _ => 0 end)) as P. cbn beta iota in P.
    L5SAR.feed P ltac:(first [assumption | unfold PEAENCSP.aligned; assumption | lia]).
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & C8).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac3c4 W_ac374 r F_ac374 eq_refl D_ac374 T1 ltac:(lia) Hr2) as MSR.
    exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MSR]|].
    split; [intros j Hj; apply KS1; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|].
    split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T10|]. rewrite Z.mod_small by lia. exact C8.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Hypothesis PB : PESKA.push_back_specA RSEGS AD EE L ar HI P.

Theorem v_bool_ok : PECSA.v_bool_spec L ar HI P.
Proof.
  unfold PECSA.v_bool_spec, PECSPA.v_bool_spec, PECSPA.eslot_spec. cbn [pe_bool EE PeCLayoutA.EADDR_A].
  intros PMODE v fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 AB CPRE INCS POK MP NB HB CRED KONT.
  destruct AB as (A11 & _). rewrite L5K.rl11 in A11.
  destruct X as [xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad].
  assert (ESC : e_scalar 1 1 (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad)
          = e_end_value (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + 1) (xhi + 1) xbad)) by reflexivity.
  rewrite ESC in HB, KONT. rewrite eev_hi in HB. cbn [s_hi] in HB.
  exact (PEAENCN.scalar1_core L ar C HI P LY HIok PO PB 0xac308 0xac35c (bbyte v) (XB v) (bool_runP v) bool_runE0 bool_runE1 ltac:(split; [clear; lia| reflexivity]) PMODE
           fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e
           HH AM K0 ENT FRM FRS FOK SP32 A10 A11 CPRE INCS MP HB CRED KONT).
Qed.
End WithHeap.
End PEAENCT.

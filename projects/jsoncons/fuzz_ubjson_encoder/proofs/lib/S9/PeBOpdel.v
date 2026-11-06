(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA HeapIfaceAEx AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_rb00dc_b00e4.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0 L5CoreAB0S9 L5CoreSpecsAB0S9 L5StepARB0S9 HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmStaticsA PmSpecsA PeSpecsAb.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PMBOPD.
Import L5A. Import L5CA. Import L5CSA. Import L5SAR.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Lemma j_to fx R M (pc tgt : Z) (W : bv 32) (imm : bv 21) :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Jal 0 imm, 4%Z) ->
  btgt (Z_to_bv 64 pc) (bv_signed imm) = Z_to_bv 64 tgt -> msteps RSEGS (st fx R pc M) (st fx R tgt M).
Proof.
  intros HF HEC HD HT. eapply mst_step; [reflexivity | | apply mst_refl].
  rewrite (step_jal_x0 RSEGS R _ M (seg_rom RSEGS) _ imm HF HEC HD). rewrite HT. reflexivity.
Qed.
Lemma j_d91b4 fx R M : msteps RSEGS (st fx R 0xd9204 M) (st fx R 0x7a9c0 M).
Proof. apply (j_to fx R M 0xd9204 0x7a9c0 _ _ F_d91b4 eq_refl D_d91b4). apply bv_eq; vm_compute; reflexivity. Qed.
Lemma j_d91b8 fx R M : msteps RSEGS (st fx R 0xd9208 M) (st fx R 0xd9204 M).
Proof. apply (j_to fx R M 0xd9208 0xd9204 _ _ F_d91b8 eq_refl D_d91b8). apply bv_eq; vm_compute; reflexivity. Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.

Lemma opdel_at (pc : Z) :
  (forall fx R M, msteps RSEGS (st fx R pc M) (st fx R 0x7a9c0 M)) -> opdel_spec_at pc L ar HI.
Proof.
  intros JMP fx R M model K LB FF LK cr A q n sp r HH AM HK INQ G10 G1 RA G2 G4 STK KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold OPDEL_SCR, MALLOC_SCR in SLO, DSCR.
  apply (apiece_ro L ar C HI LY HIok LB FF LK cr A M model fx fx R pc R 0x7a9c0 (mrestrict (ahid A model) M) K HH AM (JMP fx R _) (mem_grows_refl _)).
  { intros a Ha. reflexivity. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1.
  assert (E1 : M1 = M) by (apply mem_eq_of_agree; exact FRM1). subst M1.
  pose proof (HAJ.aior_free _ _ _ _ _ HIok) as HF. unfold afree_spec in HF. rewrite (aly_segs L C LY), (aly_free L C LY), (aly_scr_free L C LY) in HF.
  assert (U2 : bv_unsigned (getr R 2%bv) = sp). { rewrite G2. apply L5.unsigned_lit. clear - SLO SHI SPT; lia. }
  eapply (HF fx R M model1 LB FF LK cr A q n K HH1 (proj1 AM1) (proj2 AM1) INQ G10 G4); clear HF.
  - rewrite G1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (destruct RA as [X _]; clear - X; lia). exact (proj2 RA).
  - rewrite U2. pose proof (astack_ok_of_astk L ar C LY M M sp OPDEL_SCR 0 4096 STK (mem_grows_refl M)) as X.
    replace (sp - 0) with sp in X by (clear; lia). apply X. clear; lia. clear; lia. unfold OPDEL_SCR, MALLOC_SCR; clear; lia. exact A16.
  - exact HK.
  - intros R' M' model' A' RP PRES RT2 IA MI2 HH2. rewrite U2 in PRES. rewrite G1.
    apply (KONT fx R' M' model' A' RP).
    + split. { intros a (Ha & Hc & _). apply (proj1 PRES). exact Ha. exact Hc. }
      split. { intros i Hi. apply (proj2 PRES). unfold OPDEL_SCR, MALLOC_SCR in *. clear - Hi; lia. }
      intros a Ha Hc HM. destruct (rng_dec a (sp - 4096) sp) as [I|O]. apply (proj2 PRES). exact I.
      rewrite (proj1 PRES a Ha). exact HM. exact Hc.
    + eapply L5LZ.model_rt_trans. exact RT1. exact RT2.
    + exact IA.
    + split. rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM1). exact MI2.
    + exact HH2.
Qed.

Theorem opdel_ok0 : opdel_spec L ar HI.
Proof. apply opdel_at. intros fx R M. apply j_d91b4. Qed.
Theorem opdel_sized_ok0 : opdel_sized_spec L ar HI.
Proof. apply opdel_at. intros fx R M. eapply msteps_trans. apply j_d91b8. apply j_d91b4. Qed.

End WithIface.

Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Lemma opdel_pma_at (pc : Z) : opdel_spec_at pc L ar HI -> PMSPA.opdel_spec_at PMB.RSEGS L ar HI pc.
Proof.
  intros OK fx R M model K LB FF LK Aw cr q n sp r HH AM HK INQ G10 G1 RA G2 G4 STK KONT.
  exact (OK fx R M model K LB FF LK cr Aw q n sp r HH AM HK INQ G10 G1 RA G2 G4 STK KONT).
Qed.
Theorem opdel_ok : PMB.opdel_spec L ar HI.
Proof.
  apply opdel_pma_at. change (pa_opdel PMB.AD) with 0xd9208.
  apply (opdel_at L ar C HI (PMB.ly_as0 L C LY) HIok). intros fx R M. eapply msteps_trans. apply j_d91b8. apply j_d91b4.
Qed.
Theorem opdel_sized_ok : PMB.opdel_sized_spec L ar HI.
Proof.
  apply opdel_pma_at. change (pa_opdel_sized PMB.AD) with 0xd9204.
  apply (opdel_at L ar C HI (PMB.ly_as0 L C LY) HIok). intros fx R M. apply j_d91b4.
Qed.
End WithHeap.
End SCFG_1.
End PMBOPD.

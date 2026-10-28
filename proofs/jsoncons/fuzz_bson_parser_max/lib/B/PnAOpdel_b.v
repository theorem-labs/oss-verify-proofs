(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA HeapIfaceABx
     AsanAcct. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_rb00dc_b00e4_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PMAOPD.
Import L5A. Import L5CA. Import L5CSA. Import L5SAR.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Lemma j_to fx R M (pc tgt : Z) (W : bv 32) (imm : bv 21) :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Jal 0 imm, 4%Z) ->
  btgt (Z_to_bv 64 pc) (bv_signed imm) = Z_to_bv 64 tgt -> msteps RSEGS (st fx R pc M) (st fx R tgt M).
Proof.
  intros HF HEC HD HT. eapply mst_step; [reflexivity | | apply mst_refl].
  rewrite (step_jal_x0 RSEGS R _ M (seg_rom RSEGS) _ imm HF HEC HD). rewrite HT. reflexivity.
Qed.
Lemma j_d13ac fx R M : msteps RSEGS (st fx R 0xd39a8 M) (st fx R 0x79814 M).
Proof. apply (j_to fx R M 0xd39a8 0x79814 _ _ F_d13ac eq_refl D_d13ac). apply bv_eq; vm_compute; reflexivity. Qed.
Lemma j_d13b0 fx R M : msteps RSEGS (st fx R 0xd39ac M) (st fx R 0xd39a8 M).
Proof. apply (j_to fx R M 0xd39ac 0xd39a8 _ _ F_d13b0 eq_refl D_d13b0). apply bv_eq; vm_compute; reflexivity. Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.

Lemma opdel_at (pc : Z) :
  (forall fx R M, msteps RSEGS (st fx R pc M) (st fx R 0x79814 M)) -> opdel_spec_at pc L ar HI.
Proof.
  intros JMP fx R M model K LB FF LK cr A q n sp r HH AM HK INQ G10 G1 RA G2 G4 STK KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold OPDEL_SCR, MALLOC_SCR in SLO, DSCR.
  apply (apiece_ro L ar C HI LY HIok LB FF LK cr A M model fx fx R pc R 0x79814 (mrestrict (ahid A model) M) K HH AM (JMP fx R _) (mem_grows_refl _)).
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
Proof. apply opdel_at. intros fx R M. apply j_d13ac. Qed.
Theorem opdel_sized_ok0 : opdel_sized_spec L ar HI.
Proof. apply opdel_at. intros fx R M. eapply msteps_trans. apply j_d13b0. apply j_d13ac. Qed.

End WithIface.

(* [comment removed for export] *)
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Lemma opdel_pma_at (pc : Z) : opdel_spec_at pc L ar HI -> PMSPA.opdel_spec_at PMA.RSEGS L ar HI pc.
Proof.
  intros OK fx R M model K LB FF LK Aw cr q n sp r HH AM HK INQ G10 G1 RA G2 G4 STK KONT.
  exact (OK fx R M model K LB FF LK cr Aw q n sp r HH AM HK INQ G10 G1 RA G2 G4 STK KONT).
Qed.
Theorem opdel_ok : PMA.opdel_spec L ar HI.
Proof.
  apply opdel_pma_at. change (pa_opdel PMA.AD) with 0xd39ac.
  apply (opdel_at L ar C HI (PMA.ly_as0 L C LY) HIok). intros fx R M. eapply msteps_trans. apply j_d13b0. apply j_d13ac.
Qed.
Theorem opdel_sized_ok : PMA.opdel_sized_spec L ar HI.
Proof.
  apply opdel_pma_at. change (pa_opdel_sized PMA.AD) with 0xd39a8.
  apply (opdel_at L ar C HI (PMA.ly_as0 L C LY) HIok). intros fx R M. apply j_d13ac.
Qed.
End WithHeap.
End SCFG_1.
End PMAOPD.

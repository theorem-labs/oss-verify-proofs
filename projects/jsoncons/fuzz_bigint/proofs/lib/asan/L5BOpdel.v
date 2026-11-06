(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AsanAcct Bo0_code_b1044_b104c BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5StepAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADEL.
Import L5A. Import L5CA. Import L5CSA. Import L5SA.
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
Lemma j_b0cf0 fx R M : msteps RSEGS (st fx R 0xb1044 M) (st fx R 0x5fed4 M).
Proof. apply (j_to fx R M 0xb1044 0x5fed4 _ _ F_b1044 eq_refl D_b1044). apply bv_eq; vm_compute; reflexivity. Qed.
Lemma j_b0cf4 fx R M : msteps RSEGS (st fx R 0xb1048 M) (st fx R 0xb1044 M).
Proof. apply (j_to fx R M 0xb1048 0xb1044 _ _ F_b1048 eq_refl D_b1048). apply bv_eq; vm_compute; reflexivity. Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Lemma opdel_at (pc : Z) :
  (forall fx R M, msteps RSEGS (st fx R pc M) (st fx R 0x5fed4 M)) -> opdel_spec_at pc L ar HI.
Proof.
  intros JMP fx R M model K LB FF LK cr A q n sp r HH AM HK INQ G10 G1 RA G2 G4 STK KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold OPDEL_SCR, MALLOC_SCR in SLO, DSCR.
  apply (apiece_ro L ar C HI LY HIok LB FF LK cr A M model fx fx R pc R 0x5fed4 (mrestrict (ahid A model) M) K HH AM (JMP fx R _) (mem_grows_refl _)).
  { intros a Ha. reflexivity. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1.
  assert (E1 : M1 = M) by (apply mem_eq_of_agree; exact FRM1). subst M1.
  pose proof (aio_free _ _ _ _ _ HIok) as HF. unfold afree_spec in HF. rewrite (aly_segs L C LY), (aly_free L C LY), (aly_scr_free L C LY) in HF.
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

Theorem opdel_ok : opdel_spec L ar HI.
Proof. apply opdel_at. intros fx R M. apply j_b0cf0. Qed.
Theorem opdel_sized_ok : opdel_sized_spec L ar HI.
Proof. apply opdel_at. intros fx R M. eapply msteps_trans. apply j_b0cf4. apply j_b0cf0. Qed.

End WithIface.
End SCFG_1.
End L5ADEL.

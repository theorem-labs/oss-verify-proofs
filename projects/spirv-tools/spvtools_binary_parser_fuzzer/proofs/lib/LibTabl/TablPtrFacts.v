(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare LibIface LibEff.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablImgP1 TablImgU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Gen.
  Variable SEGS : list Segment.
  Variable L : Layout.
  Variable ti : tabl_img.
  Hypothesis RO : forall a, ti_ro_lo ti <= a < ti_ro_hi ti -> ro_addr L a.
  Hypothesis F : img_facts SEGS ti.
  Hypothesis ALI : ti_insn ti mod 4 = 0.
  Hypothesis ALO : ti_opnd ti mod 4 = 0.
  Hypothesis ALE : ti_ext ti mod 4 = 0.

  Lemma idesc_ptr_gen : forall d op, idesc ti d op -> 0x10000 <= d /\ d + 60 <= 2 ^ 40 /\ d mod 4 = 0.
  Proof using SEGS L ti RO F ALI.
    intros d op Hd. destruct (idesc_facts SEGS L ti RO F d op Hd) as (r & _ & _ & _ & Hlo & Hhi & _).
    split; [exact Hlo|]. split; [exact Hhi|].
    destruct Hd as (i & r' & _ & ->). unfold INSN_STRIDE.
    replace (ti_insn ti + 60 * i) with (ti_insn ti + (15 * i) * 4) by lia. rewrite Z_mod_plus_full. exact ALI.
  Qed.

  Lemma odesc_ptr_gen : forall d t v, odesc ti d t v -> 0x10000 <= d /\ d + 52 <= 2 ^ 40 /\ d mod 4 = 0.
  Proof using SEGS L ti RO F ALO.
    intros d t v Hd. destruct (odesc_facts SEGS L ti RO F d t v Hd) as (r & _ & _ & _ & Hlo & Hhi & _).
    split; [exact Hlo|]. split; [exact Hhi|].
    destruct Hd as (i & r' & _ & ->). unfold OPND_STRIDE.
    replace (ti_opnd ti + 52 * i) with (ti_opnd ti + (13 * i) * 4) by lia. rewrite Z_mod_plus_full. exact ALO.
  Qed.

  Lemma edesc_ptr_gen : forall d e v, edesc ti d e v -> 0x10000 <= d /\ d + 28 <= 2 ^ 40 /\ d mod 4 = 0.
  Proof using SEGS L ti RO F ALE.
    intros d e v Hd. destruct (edesc_facts SEGS L ti RO F d e v Hd) as (r & _ & _ & _ & Hlo & Hhi & _).
    split; [exact Hlo|]. split; [exact Hhi|].
    destruct Hd as (i & r' & _ & ->). unfold EXT_STRIDE.
    replace (ti_ext ti + 28 * i) with (ti_ext ti + (7 * i) * 4) by lia. rewrite Z_mod_plus_full. exact ALE.
  Qed.
End Gen.

Module P1.
  Module Img := TablImgP1.
  Definition idesc_ptr := idesc_ptr_gen _ Img.Ly.L Img.ti Img.rodata Img.IFX eq_refl.
  Definition odesc_ptr := odesc_ptr_gen _ Img.Ly.L Img.ti Img.rodata Img.IFX eq_refl.
  Definition edesc_ptr := edesc_ptr_gen _ Img.Ly.L Img.ti Img.rodata Img.IFX eq_refl.

End P1.

Module U1.
  Module Img := TablImgU1.
  Definition idesc_ptr := idesc_ptr_gen _ Img.Ly.L Img.ti Img.rodata Img.IFX eq_refl.
  Definition odesc_ptr := odesc_ptr_gen _ Img.Ly.L Img.ti Img.rodata Img.IFX eq_refl.
  Definition edesc_ptr := edesc_ptr_gen _ Img.Ly.L Img.ti Img.rodata Img.IFX eq_refl.

End U1.

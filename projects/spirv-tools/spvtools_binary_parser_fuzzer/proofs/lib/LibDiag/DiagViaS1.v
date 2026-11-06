(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim RefMemcpyLib LibIface LibEff S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib S1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagVia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Module Ly := S1Layout.
Abbreviation SEGS := Plain.M.loaded_segments.

Section S1.
Context {AC : AllocCeiling}.
Variable MI : MallocIface SEGS Ly.L.
Variable ST : StaticsIface SEGS Ly.L.
Definition hi_unowned := hi_unowned SEGS Ly.L MI ly_img_low ly_rw_img.
Definition hi_offimg := hi_offimg Ly.L ly_img_low.
Definition hi_not_errno := hi_not_errno Ly.L ly_img_low ly_errno_img.
Definition img_ro_clear_of' := img_ro_clear_of' SEGS Ly.L ST.
Definition sx_inv_via_eff := sx_inv_via_eff SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img ly_rw_not_relro ly_errno_rw.
Definition ro_clear_via_eff := ro_clear_via_eff SEGS Ly.L MI ly_img_low ly_errno_rw.
Definition mdef_via_eff := mdef_via_eff SEGS Ly.L MI ly_img_low ly_rw_img ly_errno_rw.
Definition agree_via_eff := agree_via_eff SEGS Ly.L MI.
Definition agree_hi_via_eff := agree_hi_via_eff SEGS Ly.L MI ly_img_low ly_rw_img ly_errno_img.
Definition eff_widen := eff_widen SEGS Ly.L MI.
Definition eff_of_stores := eff_of_stores SEGS Ly.L MI.
End S1.

Lemma fseg_skip : forall seg rest a n,
  (0 < n)%Z ->
  (a < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) < a + n)%Z ->
  find_segment (seg :: rest) a n = find_segment rest a n.
Proof.
  intros seg rest a n Hn H. cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base seg)) a); destruct (Z.leb_spec (a + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)));
    cbn [andb]; try reflexivity. lia.
Qed.
Lemma fseg_off : forall a n, (0 < n)%Z -> (a + n <= 0x10000 \/ 0x122000 <= a)%Z -> find_segment SEGS a n = None.
Proof.
  intros a n Hn H. unfold Plain.M.loaded_segments, Plain_loaded_segments.
  rewrite 4 fseg_skip; [reflexivity | exact Hn | | exact Hn | | exact Hn | | exact Hn |];
    cbn [seg_base seg_size Plain_segment_000 Plain_segment_001 Plain_segment_002 Plain_segment_003]; lia.
Qed.
Lemma seg_rom_offimg : forall x : word, ~ in_ranges (ly_img Ly.L) (bv_unsigned x) -> seg_rom SEGS x = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. pose proof (u64_range x).
  rewrite fseg_off; [reflexivity | lia |].
  destruct (Z.lt_ge_cases (bv_unsigned x) 0x10000); [left; lia|].
  destruct (Z.lt_ge_cases (bv_unsigned x) 0x122000); [|right; lia].
  exfalso. apply Hx. apply ly_img_iff. lia.
Qed.

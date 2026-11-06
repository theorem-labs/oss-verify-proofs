(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LazyRestrict.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module RefMemImage.
  Module Ref.
    Definition loaded_segments := Asan.M.loaded_segments.
  End Ref.
  Definition RefMemImage_loaded_segments := Asan.Asan_loaded_segments.
  Definition RefMemImage_segment_000 := Asan.Asan_segment_000.
  Definition RefMemImage_segment_001 := Asan.Asan_segment_001.
  Definition RefMemImage_segment_002 := Asan.Asan_segment_002.
  Definition RefMemImage_segment_003 := Asan.Asan_segment_003.
End RefMemImage.

Module AgentMemImage.
  Module Agent.
    Definition loaded_segments := Asan.M.loaded_segments.
  End Agent.
End AgentMemImage.

Definition asegs := RefMemImage.Ref.loaded_segments.

Definition AIMG_LO  : Z := 0x10000.
Definition ARO_HI   : Z := 0x91000.
Definition ATEXT_LO : Z := 0x91000.
Definition ATEXT_HI : Z := 0x17c000.
Definition ARW_LO   : Z := 0x17c000.
Definition ARW1_HI  : Z := 0x185000.
Definition AIMG_TOP : Z := 0x6e6000.

Definition ALOWSH  : word * word := (Z_to_bv 64 0x7fff7000,    Z_to_bv 64 0x10000000).
Definition AHIGHSH : word * word := (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000).
Definition AGAP    : word * word := (Z_to_bv 64 0x8fff7000,    Z_to_bv 64 0x20000000000).
Definition ASHADOW_BASE : Z := 0x7fff8000.

Lemma asegs_below_top : forall seg, In seg asegs ->
  (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= AIMG_TOP)%Z.
Proof. intros seg H. assert (HB : forallb (fun s => Z.leb (Z.add (Z.of_N (seg_base s)) (Z.of_N (seg_size s))) AIMG_TOP) asegs = true) by (vm_compute; reflexivity). rewrite forallb_forall in HB. apply Z.leb_le. exact (HB seg H). Qed.


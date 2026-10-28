(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BazyRestrict.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module RefMemImage.
  Module Ref.
    Definition loaded_segments := AsanUbsan.M.loaded_segments.
  End Ref.
  Definition RefMemImage_loaded_segments := AsanUbsan.AsanUbsan_loaded_segments.
  Definition RefMemImage_segment_000 := AsanUbsan.AsanUbsan_segment_000.
  Definition RefMemImage_segment_001 := AsanUbsan.AsanUbsan_segment_001.
  Definition RefMemImage_segment_002 := AsanUbsan.AsanUbsan_segment_002.
  Definition RefMemImage_segment_003 := AsanUbsan.AsanUbsan_segment_003.
End RefMemImage.

Module AgentMemImage.
  Module Agent.
    Definition loaded_segments := AsanUbsan.M.loaded_segments.
  End Agent.
End AgentMemImage.

Definition asegs := RefMemImage.Ref.loaded_segments.

Definition AIMG_LO  : Z := 0x10000.
Definition ARO_HI   : Z := 0x91000.
Definition ATEXT_LO : Z := 0x91000.
Definition ATEXT_HI : Z := 0x17e000.
Definition ARW_LO   : Z := 0x17e000.
Definition ARW1_HI  : Z := 0x186000.
Definition AIMG_TOP : Z := 0x6e8000.

Definition ALOWSH  : word * word := (Z_to_bv 64 0x7fff7000,    Z_to_bv 64 0x10000000).
Definition AHIGHSH : word * word := (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000).
Definition AGAP    : word * word := (Z_to_bv 64 0x8fff7000,    Z_to_bv 64 0x20000000000).
Definition ASHADOW_BASE : Z := 0x7fff8000.

Lemma asegs_below_top : forall seg, In seg asegs ->
  (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= AIMG_TOP)%Z.
Proof. intros seg H. assert (HB : forallb (fun s => Z.leb (Z.add (Z.of_N (seg_base s)) (Z.of_N (seg_size s))) AIMG_TOP) asegs = true) by (vm_compute; reflexivity). rewrite forallb_forall in HB. apply Z.leb_le. exact (HB seg H). Qed.


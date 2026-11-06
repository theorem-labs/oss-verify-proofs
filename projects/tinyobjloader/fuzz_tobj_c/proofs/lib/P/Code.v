(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Plain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition segs : list Segment := Plain.M.loaded_segments.

Module StrAddr.

  Definition memset_entry : Z := 0x26f98.
  Definition memset_cut_words : Z := 0x27000.
  Definition memset_loop : Z := 0x27070.
  Definition memset_ret : Z := 0x2708c.

  Definition memcpy_entry : Z := 0x26b94.
  Definition memcpy_L1   : Z := 0x26bac.
  Definition memcpy_J48  : Z := 0x26be4.
  Definition memcpy_Je18 : Z := 0x26cb4.
  Definition memcpy_Lal  : Z := 0x26cc0.
  Definition memcpy_Lc2  : Z := 0x26c38.
  Definition memcpy_Lc3  : Z := 0x26d40.
  Definition memcpy_Lc1  : Z := 0x26dd4.
  Definition memcpy_T58  : Z := 0x26bf4.
  Definition memcpy_Ta4  : Z := 0x26e40.
  Definition memcpy_T54  : Z := 0x26cf0.
  Definition memcpy_retA : Z := 0x26f64.
  Definition memcpy_retB : Z := 0x26f94.

  Definition strnlen_entry : Z := 0x27090.
  Definition strnlen_ret : Z := 0x270d0.

  Definition memchr_entry : Z := 0x270d4.
  Definition memchr_L1 : Z := 0x270f0.
  Definition memchr_J84 : Z := 0x27118.
  Definition memchr_L2 : Z := 0x27148.
  Definition memchr_L3 : Z := 0x27174.
  Definition memchr_ret : Z := 0x2718c.
End StrAddr.

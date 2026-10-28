(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition segs : list Segment := Ubsan.M.loaded_segments.

Module StrAddr.

  Definition memset_entry : Z := 0x276d8.
  Definition memset_cut_words : Z := 0x27740.
  Definition memset_loop : Z := 0x277b0.
  Definition memset_ret : Z := 0x277cc.

  Definition memcpy_entry : Z := 0x272d4.
  Definition memcpy_L1   : Z := 0x272ec.
  Definition memcpy_J48  : Z := 0x27324.
  Definition memcpy_Je18 : Z := 0x273f4.
  Definition memcpy_Lal  : Z := 0x27400.
  Definition memcpy_Lc2  : Z := 0x27378.
  Definition memcpy_Lc3  : Z := 0x27480.
  Definition memcpy_Lc1  : Z := 0x27514.
  Definition memcpy_T58  : Z := 0x27334.
  Definition memcpy_Ta4  : Z := 0x27580.
  Definition memcpy_T54  : Z := 0x27430.
  Definition memcpy_retA : Z := 0x276a4.
  Definition memcpy_retB : Z := 0x276d4.

  Definition strnlen_entry : Z := 0x277d0.
  Definition strnlen_ret : Z := 0x27810.

  Definition memchr_entry : Z := 0x27814.
  Definition memchr_L1 : Z := 0x27830.
  Definition memchr_J84 : Z := 0x27858.
  Definition memchr_L2 : Z := 0x27888.
  Definition memchr_L3 : Z := 0x278b4.
  Definition memchr_ret : Z := 0x278cc.
End StrAddr.

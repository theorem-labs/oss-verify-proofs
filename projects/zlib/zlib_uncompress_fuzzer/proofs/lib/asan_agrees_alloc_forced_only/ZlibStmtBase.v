(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ZCEIL : Z := 0x7fff7f800000.

Definition S_ENTRY : list reg := [22; 23; 24; 25; 26; 27]%bv.
Definition S_ALL   : list reg := [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition sregs (regs : bvmap 5 word) (rs : list reg) : list Z :=
  map (fun r => bv_unsigned (getr regs r)) rs.

Definition ZWINV : Type := Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> (word -> option byte) -> Prop.

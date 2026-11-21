(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Malloc Require Import MallocRep F_malloc_free F_malloc_fast MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Malloc Require Import MallocKit_B MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Malloc Require Import MallocKit_B3 F_ntf_D F_ntf_E F_ntf_F.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition nest_frame (st : mstate) (g p : aptr) (j0 j1 : list byte) (raw : word) : list cell :=
  [CB 8 j0; C8 (Z_to_bv 64 (conc st p)); C8 (Z_to_bv 64 (conc st g)); C8 (Z_to_bv 64 CTX); CB 40 j1; C8 raw].

End CANSEC1.

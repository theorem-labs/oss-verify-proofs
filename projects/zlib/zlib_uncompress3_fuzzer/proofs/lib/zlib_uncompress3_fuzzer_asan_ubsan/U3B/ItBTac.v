(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac snez1 r :=
  let v := reg_val r in
  lazymatch v with
  | Z_to_bv 64 (Z.b2z (0 <? ?X)) => replace v with (Z_to_bv 64 1) by (replace (0 <? X) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity)
  end.
Ltac seqz0 r :=
  let v := reg_val r in
  lazymatch v with
  | Z_to_bv 64 (Z.b2z (?X <? 1)) => replace v with (Z_to_bv 64 0) by (replace (X <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)
  end.

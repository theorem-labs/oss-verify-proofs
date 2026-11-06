(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/P/Startup_glue.v, with its module paths changed; 3 of its 13 lines of code are new or changed and 73 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/plugin-hostd/fuzz_command/lib/A/Bz/P/Startup_glue.v at 2d2ff01bb6f; module paths changed to reac-pw/fuzz_headamp; 0 numeral(s) moved from fuzz_command.asan to fuzz_headamp.asan by alreloc a5c53bb2bed4. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.P Require Import Str_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac astep := lstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (envp_addr and auxv_addr over the launch's ProcInput in place of argv and envp). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bk X1bs X1c2 X1bn X1cc X1c6.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1rl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qv X0pw X0qx X0qy.
Import ListNotations.
Open Scope bv_scope.
Import X1bs.Exc.

Section AtMain.
Variables (sp0 : word) (inp : ProcInput).
Notation usp0 := (bv_unsigned sp0).

Definition envp_addr : Z := (usp0 + 8 * (argc inp + 2))%Z.
Definition auxv_addr : Z := (usp0 + 8 * (argc inp + envc inp + 3))%Z.
End AtMain.

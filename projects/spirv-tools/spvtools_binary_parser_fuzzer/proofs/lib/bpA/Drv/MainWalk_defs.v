(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec HSymExec2 HSymExec2Sound HSymRun HSymDrive HSymDriveX.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Import HPropExec.
Import SX2. Import SX2S.

Definition FUELM : nat := 3000.

Definition carryM (r : sym_state * list sidecond * scripts) (kn : list kentry) := carry (s_log (fst (fst r))) kn [].

Definition noscr : scripts := SCR [] [] [].

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

Definition MSTK : Z := 1024.

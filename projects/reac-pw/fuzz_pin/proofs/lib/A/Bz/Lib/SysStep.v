(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/Lib/SysStep.v; 4 of its 16 lines of code are new or changed and 402 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_boxreg/lib/A/Bz/Lib/SysStep.v at origin/ossv/recipes f26f9fbd8777; module paths changed; no numeral changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.Bz Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.Bz.Lib Require Import Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac sys_finish :=
  (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
  | |- _ = _ => cbv delta [mkR]; reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

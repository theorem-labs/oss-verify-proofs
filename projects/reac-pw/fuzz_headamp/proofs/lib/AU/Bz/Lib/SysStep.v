(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/Lib/SysStep.v; 3 of its 16 lines of code are new or changed and 401 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/plugin-hostd/fuzz_command/lib/A/Bz/Lib/SysStep.v at 2d2ff01bb6f; module paths changed to reac-pw/fuzz_headamp; 0 numeral(s) moved from fuzz_command.asan to fuzz_headamp.asan by alreloc a5c53bb2bed4. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/Bz/Lib/SysStep.v of this library by derive_y.py b7b132fb12a7: module paths lib.A -> lib.AU, the image module Asan -> AsanUbsan and Img0 -> Img0U, addresses moved from fuzz_headamp's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/Bz/Lib/SysStep.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz.Lib Require Import Tac.
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

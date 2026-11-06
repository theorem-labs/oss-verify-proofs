(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import STRW_tac InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Clf Require Import CImage C_Lib C_memset C_Startup_A C_Startup_B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Notation CGOT0 := 0x13088%Z (only parsing).      (* [comment removed for export] *)
Notation CGOTCX := 0x130a8%Z (only parsing).     (* [comment removed for export] *)
Notation CGOTINI := 0x130d0%Z (only parsing).    (* [comment removed for export] *)
Notation CGOTFINI := 0x130e0%Z (only parsing).   (* [comment removed for export] *)
Notation CINITARR := 0x13068%Z (only parsing).   (* [comment removed for export] *)
Notation CINITED := 0x14100%Z (only parsing).    (* [comment removed for export] *)
Notation CFINALIZED := 0x14148%Z (only parsing). (* [comment removed for export] *)
Notation CEXITLOCK := 0x142e0%Z (only parsing).  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AtMain.
  Variables (sp0 : word) (argv envp : list (list byte)).
  Notation usp0 := (bv_unsigned sp0).
End AtMain.

Section Proof.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis FITS : entry_stack_fits sp0 argv envp.
  Notation usp0 := (bv_unsigned sp0).
End Proof.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import STRW_tac.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Clf Require Import CImage C_Lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

(* [comment removed for export] *)
Notation CGP := 0x10800%Z (only parsing).        (* [comment removed for export] *)
Notation CLIBC := 0x14300%Z (only parsing).      (* [comment removed for export] *)
Notation CTLL := 0x14158%Z (only parsing).       (* [comment removed for export] *)
Notation CTD := 0x14190%Z (only parsing).        (* [comment removed for export] *)
Notation CTP := 0x14258%Z (only parsing).        (* [comment removed for export] *)
Notation CSYSINFO := 0x142e8%Z (only parsing).   (* [comment removed for export] *)
Notation CDEFSTACK := 0x140f8%Z (only parsing).  (* [comment removed for export] *)
Notation CGOT_DYNAMIC := 0x13080%Z (only parsing).

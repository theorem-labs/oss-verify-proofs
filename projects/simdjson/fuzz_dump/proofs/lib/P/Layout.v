(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation psegs := Image.psegs.

Notation RGP := 0x10800%Z (only parsing).
Notation RLIBC := 0xffcf8%Z (only parsing).
Notation RTLL := 0xffa70%Z (only parsing).
Notation RTD := 0xdf9a0%Z (only parsing).
Notation RTP := 0xdfa68%Z (only parsing).
Notation RSYSINFO := 0xffce0%Z (only parsing).
Notation RDEFSTACK := 0xcdf10%Z (only parsing).
Notation RGOT_DYNAMIC := 0xccaa8%Z (only parsing).
Notation RGOT_SSP := 0xccc30%Z (only parsing).
Notation RGUARD := 0xffcd8%Z (only parsing).
Notation RENVIRON := 0xdf998%Z (only parsing).
Notation RPROGNAME := 0xffce8%Z (only parsing).
Notation RHWCAP := 0xffd60%Z (only parsing).
Notation RGOT3 := 0xccc08%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0xb5e64);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0xb5e58); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0xcde20%Z (only parsing).
Notation RSTDOUT_BUF := 0x100258%Z (only parsing).
Notation RSTDERR := 0xcdd30%Z (only parsing).
Notation F_STDOUT_WRITE := 0xb6690%Z (only parsing).
Notation F_STDIO_WRITE := 0xb5cc8%Z (only parsing).

Definition GLOBALS_TOP : Z := 0x101000.
Definition STATIC_SPLIT : Z := 0xc7000.

Definition got_ssp := 0xccc30%Z.
Definition ssp_guard := 0xffcd8%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells psegs m ssp_guard [C8 canary].

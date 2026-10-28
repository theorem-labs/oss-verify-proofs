(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation bgusegs := ImageBg.bgusegs.

Notation RGP := 0x10800%Z (only parsing).
Notation RLIBC := 0x351228%Z (only parsing).
Notation RTLL := 0x350fa0%Z (only parsing).
Notation RTD := 0x330ed0%Z (only parsing).
Notation RTP := 0x330f98%Z (only parsing).
Notation RSYSINFO := 0x351210%Z (only parsing).
Notation RDEFSTACK := 0x31e3b0%Z (only parsing).
Notation RGOT_DYNAMIC := 0x31c4c8%Z (only parsing).
Notation RGOT_SSP := 0x31ca98%Z (only parsing).
Notation RGUARD := 0x350fd8%Z (only parsing).
Notation RENVIRON := 0x330ec8%Z (only parsing).
Notation RPROGNAME := 0x351218%Z (only parsing).
Notation RHWCAP := 0x351290%Z (only parsing).
Notation RGOT3 := 0x31caa0%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x2b3b98);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x2b3cdc); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x31e2c0%Z (only parsing).
Notation RSTDOUT_BUF := 0x351a80%Z (only parsing).
Notation RSTDERR := 0x31e0e0%Z (only parsing).
Notation F_STDOUT_WRITE := 0x2b559c%Z (only parsing).
Notation F_STDIO_WRITE := 0x2b4984%Z (only parsing).

Definition GLOBALS_TOP : Z := 0x353000.
Definition STATIC_SPLIT : Z := 0x2c0000.

Definition got_ssp := 0x31ca98%Z.
Definition ssp_guard := 0x350fd8%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells bgusegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells bgusegs m ssp_guard [C8 canary].

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation bgpsegs := ImageBg.bgpsegs.

Notation RGP := 0x10800%Z (only parsing).
Notation RLIBC := 0x30ba58%Z (only parsing).
Notation RTLL := 0x30b7d0%Z (only parsing).
Notation RTD := 0x2eb700%Z (only parsing).
Notation RTP := 0x2eb7c8%Z (only parsing).
Notation RSYSINFO := 0x30ba40%Z (only parsing).
Notation RDEFSTACK := 0x2d8be0%Z (only parsing).
Notation RGOT_DYNAMIC := 0x2d6e90%Z (only parsing).
Notation RGOT_SSP := 0x2d7470%Z (only parsing).
Notation RGUARD := 0x30b808%Z (only parsing).
Notation RENVIRON := 0x2eb6f8%Z (only parsing).
Notation RPROGNAME := 0x30ba48%Z (only parsing).
Notation RHWCAP := 0x30bac0%Z (only parsing).
Notation RGOT3 := 0x2d7478%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x26e3b0);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x26e4f4); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x2d8af0%Z (only parsing).
Notation RSTDOUT_BUF := 0x30c2b0%Z (only parsing).
Notation RSTDERR := 0x2d8910%Z (only parsing).
Notation F_STDOUT_WRITE := 0x26fdb4%Z (only parsing).
Notation F_STDIO_WRITE := 0x26f19c%Z (only parsing).

Definition GLOBALS_TOP : Z := 0x30d000.
Definition STATIC_SPLIT : Z := 0x27b000.

Definition got_ssp := 0x2d7470%Z.
Definition ssp_guard := 0x30b808%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells bgpsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells bgpsegs m ssp_guard [C8 canary].

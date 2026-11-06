(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation usegs := Image.usegs.

Notation RGP := 0x10800%Z (only parsing).
Notation RLIBC := 0x1157d8%Z (only parsing).
Notation RTLL := 0x115550%Z (only parsing).
Notation RTD := 0xf5480%Z (only parsing).
Notation RTP := 0xf5548%Z (only parsing).
Notation RSYSINFO := 0x1157c0%Z (only parsing).
Notation RDEFSTACK := 0xe3228%Z (only parsing).
Notation RGOT_DYNAMIC := 0xe1978%Z (only parsing).
Notation RGOT_SSP := 0xe1b58%Z (only parsing).
Notation RGUARD := 0x1157b8%Z (only parsing).
Notation RENVIRON := 0xf5478%Z (only parsing).
Notation RPROGNAME := 0x1157c8%Z (only parsing).
Notation RHWCAP := 0x115840%Z (only parsing).
Notation RGOT3 := 0xe1b30%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0xca104);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0xca0f8); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0xe3138%Z (only parsing).
Notation RSTDOUT_BUF := 0x116138%Z (only parsing).
Notation RSTDERR := 0xe2f58%Z (only parsing).
Notation F_STDOUT_WRITE := 0xcafc0%Z (only parsing).
Notation F_STDIO_WRITE := 0xc9f68%Z (only parsing).

Definition GLOBALS_TOP : Z := 0x117000.
Definition STATIC_SPLIT : Z := 0xdb000.

Definition got_ssp := 0xe1b58%Z.
Definition ssp_guard := 0x1157b8%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].

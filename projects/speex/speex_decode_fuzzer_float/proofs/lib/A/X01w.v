(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs.

Module B_TWIN.

Import ListNotations.
Open Scope bv_scope.

Notation RGOT_SSP := 0xfce58%Z (only parsing).
Notation RGUARD := 0x658cd8%Z (only parsing).
Notation RLIBC := 0x658f28%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
[C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0xed080);
C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0xed1c4); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
CB 80 tail].

Notation RSTDOUT := 0x1008a0%Z (only parsing).
Notation RSTDOUT_BUF := 0x6593a8%Z (only parsing).
Notation RSTDERR := 0x1007b0%Z (only parsing).
Notation F_STDOUT_WRITE := 0xeddf0%Z (only parsing).
Notation F_STDIO_WRITE := 0xed1cc%Z (only parsing).

Definition GLOBALS_TOP : Z := 0x65b000.
Definition STATIC_SPLIT : Z := 0xf7000.

Definition got_ssp := 0xfce58%Z.
Definition ssp_guard := 0x658cd8%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
ro_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ ro_cells bsegs m ssp_guard [C8 canary].
End B_TWIN.

Import ListNotations.
Open Scope bv_scope.

Notation RGOT_SSP := 0xf45d8%Z (only parsing).
Notation RGUARD := 0x650498%Z (only parsing).
Notation RLIBC := 0x6506e8%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
[C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0xe480c);
C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0xe4950); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
CB 80 tail].

Notation RSTDOUT := 0xf8020%Z (only parsing).
Notation RSTDOUT_BUF := 0x650b68%Z (only parsing).
Notation RSTDERR := 0xf7f30%Z (only parsing).
Notation F_STDOUT_WRITE := 0xe557c%Z (only parsing).
Notation F_STDIO_WRITE := 0xe4958%Z (only parsing).

Definition GLOBALS_TOP : Z := 0x652000.
Definition STATIC_SPLIT : Z := 0xef000.

Definition got_ssp := 0xf45d8%Z.
Definition ssp_guard := 0x650498%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
ro_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ ro_cells asegs m ssp_guard [C8 canary].

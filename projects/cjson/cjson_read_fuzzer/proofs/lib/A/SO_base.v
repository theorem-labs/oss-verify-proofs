(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Export Exit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Notation RTD := 0x5dd188%Z (only parsing).          (* [comment removed for export] *)
Notation RTP := 0x5dd250%Z (only parsing).          (* [comment removed for export] *)
Notation RSTDOUT := 0xa6698%Z (only parsing).      (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0x5fd960%Z (only parsing).  (* [comment removed for export] *)
Notation RSTDERR := 0xa65a8%Z (only parsing).      (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x94524%Z (only parsing).   (* [comment removed for export] *)
Notation F_STDIO_WRITE := 0x93b20%Z (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition emit_line : list byte := (Z_to_bv 8 48 :: Z_to_bv 8 10 :: nil)%list.

Ltac exit_lits :=
  unfold ASTDOUT, ASTDOUT_BUF, ASTDERR, ASTDERR_BUF, ASTDIN, ASTDIN_BUF, ASTDOUT_USED, ASTDERR_USED, ASTDIN_USED,
         AF_STDOUT_WRITE, AF_STDIO_WRITE, AF_STDIO_READ, AF_STDIO_EXIT, AEXIT, A_EXIT, AOFL_LOCK, AOFL_HEAD,
         AGOT_GUARD, AGUARD in *.

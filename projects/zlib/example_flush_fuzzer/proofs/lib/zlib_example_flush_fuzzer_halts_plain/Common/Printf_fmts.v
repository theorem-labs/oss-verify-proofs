(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, comments removed. *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import ITree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Common Require Import SoftFloat FmtFp Printf_model.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition FMT_pct_d : list Z := [37; 100; 10; 0].
Definition FMT_usage : list Z := str "usage: %s INPUT" ++ [10; 0].
Definition FMT_too_big : list Z := str "cli: input >= %u bytes, refused" ++ [10; 0].
Definition FMT_cannot_open : list Z := str "cli: cannot open %s" ++ [10; 0].
Definition FMT_read_error : list Z := str "cli: read error on %s" ++ [10; 0].
Definition A_FMT_pct_d : Z := 0x1037b.
Definition A_FMT_usage : Z := 0x1039e.
Definition A_FMT_too_big : Z := 0x10451.
Definition A_FMT_cannot_open : Z := 0x10534.
Definition A_FMT_read_error : Z := 0x10549.

Definition FMT_zerr : list Z := str "%s error: %d" ++ [10; 0].
Definition A_FMT_zerr : Z := 0x102f2.

Example pieces_usage_ex : printf_pieces FMT_usage [PA_s (str "prog")] = Some (pieces_usage (str "prog"), 18).
Proof. vm_compute. reflexivity. Qed.
Example pieces_cannot_open_ex : printf_pieces FMT_cannot_open [PA_s (str "f")] = Some (pieces_cannot_open (str "f"), 19).
Proof. vm_compute. reflexivity. Qed.
Example pieces_read_error_ex : printf_pieces FMT_read_error [PA_s (str "f")] = Some (pieces_read_error (str "f"), 21).
Proof. vm_compute. reflexivity. Qed.

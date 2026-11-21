(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import ITree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import SoftFloat FmtFp Printf_model.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition FMT_pct_d : list Z := [37; 100; 10; 0].
Definition FMT_usage : list Z := str "usage: %s INPUT" ++ [10; 0].
Definition FMT_too_big : list Z := str "cli: input >= %u bytes, refused" ++ [10; 0].
Definition FMT_cannot_open : list Z := str "cli: cannot open %s" ++ [10; 0].
Definition FMT_read_error : list Z := str "cli: read error on %s" ++ [10; 0].
Definition A_FMT_pct_d : Z := 0x10334.
Definition A_FMT_usage : Z := 0x10357.
Definition A_FMT_too_big : Z := 0x103d1.
Definition A_FMT_cannot_open : Z := 0x10488.
Definition A_FMT_read_error : Z := 0x1049d.
Definition A_MSG_oom : Z := 0x10320.
Definition A_MSG_short_hdr : Z := 0x10502.
Definition A_MSG_cfg_overrun : Z := 0x10368.

Example pieces_usage_ex : printf_pieces FMT_usage [PA_s (str "prog")] = Some (pieces_usage (str "prog"), 18).
Proof. vm_compute. reflexivity. Qed.
Example pieces_cannot_open_ex : printf_pieces FMT_cannot_open [PA_s (str "f")] = Some (pieces_cannot_open (str "f"), 19).
Proof. vm_compute. reflexivity. Qed.
Example pieces_read_error_ex : printf_pieces FMT_read_error [PA_s (str "f")] = Some (pieces_read_error (str "f"), 21).
Proof. vm_compute. reflexivity. Qed.
Example pieces_too_big_ex : printf_pieces FMT_too_big [PA_u 67108864] = Some (pieces_too_big, 38).
Proof. vm_compute. reflexivity. Qed.
Example pieces_pct_d_ex1 : printf_pieces FMT_pct_d [PA_i (-2147483648)] = Some (pieces_pct_d (-2147483648), 12).
Proof. vm_compute. reflexivity. Qed.
Example pieces_pct_d_ex2 : printf_pieces FMT_pct_d [PA_i 0] = Some (pieces_pct_d 0, 2).
Proof. vm_compute. reflexivity. Qed.
Example pieces_pct_d_ex3 : printf_pieces FMT_pct_d [PA_i 7] = Some (pieces_pct_d 7, 2).
Proof. vm_compute. reflexivity. Qed.
Example fp_calls_pct_d_ex : fp_calls 4 FMT_pct_d [PA_i 5] = [].
Proof. vm_compute. reflexivity. Qed.
Example pass1_ok_ex : map pass1_ok [FMT_pct_d; FMT_usage; FMT_too_big; FMT_cannot_open; FMT_read_error] = repeat true 5.
Proof. vm_compute. reflexivity. Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import SoftFloat FmtFp Printf_model.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition FMT_pct_d : list Z := [37; 100; 10; 0].                                 (* [comment removed for export] *)
Definition FMT_usage : list Z := str "usage: %s INPUT" ++ [10; 0].                  (* [comment removed for export] *)
Definition FMT_too_big : list Z := str "cli: input >= %u bytes, refused" ++ [10; 0]. (* [comment removed for export] *)
Definition FMT_cannot_open : list Z := str "cli: cannot open %s" ++ [10; 0].       (* [comment removed for export] *)
Definition FMT_read_error : list Z := str "cli: read error on %s" ++ [10; 0].      (* [comment removed for export] *)
Definition A_FMT_pct_d : Z := 0x102c9.
Definition A_FMT_usage : Z := 0x102d6.
Definition A_FMT_too_big : Z := 0x10333.
Definition A_FMT_cannot_open : Z := 0x10420.
Definition A_FMT_read_error : Z := 0x10435.
(* [comment removed for export] *)
Definition A_MSG_oom : Z := 0x102b5.          (* [comment removed for export] *)
Definition A_MSG_short_hdr : Z := 0x1049b.    (* [comment removed for export] *)
Definition A_MSG_cfg_overrun : Z := 0x102e7.  (* [comment removed for export] *)
Definition A_MSG_new_handler : Z := 0x12eff.  (* [comment removed for export] *)

(* [comment removed for export] *)
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

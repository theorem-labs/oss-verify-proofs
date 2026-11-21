(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (9 recorded proofs replaced by computation, vm_compute (pieces_usage_ex, pieces_cannot_open_ex, pieces_read_error_ex and 6 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp Printf_model.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Printf_fmts () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2eq01K46Stdlib7Strings5Ascii5ascii01K46Stdlib7Strings6String6string02C59OSSVerify5KrLib4Spec5Stdio3strC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model=printf_piecesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio<pieces_usageC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib6Common;Printf_fmts9FMT_usageC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model4parg00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01K46Stdlib7Strings6String6string01C59OSSVerify5KrLib4Spec5StdioBpieces_cannot_openC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;Printf_fmts?FMT_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioApieces_read_errorC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;Printf_fmts>FMT_read_errorC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;Printf_fmts;FMT_too_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>pieces_too_bigC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib6Common<Printf_model4parg02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio<pieces_pct_dC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;Printf_fmts9FMT_pct_dC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib6Common<Printf_model8fp_callsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C47Corelib5Lists7ListDef3mapC47Corelib5Lists7ListDef6repeatI47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib6Common<Printf_model8pass1_okC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition FMT_pct_d : list Z := [37; 100; 10; 0].                                 (* [comment removed for export] *)
Definition FMT_usage : list Z := str "usage: %s INPUT" ++ [10; 0].                  (* [comment removed for export] *)
Definition FMT_too_big : list Z := str "cli: input >= %u bytes, refused" ++ [10; 0]. (* [comment removed for export] *)
Definition FMT_cannot_open : list Z := str "cli: cannot open %s" ++ [10; 0].       (* [comment removed for export] *)
Definition FMT_read_error : list Z := str "cli: read error on %s" ++ [10; 0].      (* [comment removed for export] *)
Definition A_FMT_pct_d : Z := 0x10300.
Definition A_FMT_usage : Z := 0x1030d.
Definition A_FMT_too_big : Z := 0x103a7.
Definition A_FMT_cannot_open : Z := 0x103c8.
Definition A_FMT_read_error : Z := 0x103dd.
(* [comment removed for export] *)
Definition A_MSG_oom : Z := 0x102ec.          (* [comment removed for export] *)
Definition A_MSG_short_hdr : Z := 0x103fc.    (* [comment removed for export] *)
Definition A_MSG_cfg_overrun : Z := 0x1031e.  (* [comment removed for export] *)
Definition A_MSG_new_handler : Z := 0x12ed7.  (* [comment removed for export] *)

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

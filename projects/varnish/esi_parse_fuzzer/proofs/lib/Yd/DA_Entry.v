(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Ey6n DA_Eg3i DA_Cells.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MAIN_CELLS : list (Z * list byte) :=
  [ (* [comment removed for export] *) (0xad928, [Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 112; Z_to_bv 8 221; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 188; Z_to_bv 8 222; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 180; Z_to_bv 8 222; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 224; Z_to_bv 8 138; Z_to_bv 8 96; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0xada10, [Z_to_bv 8 40; Z_to_bv 8 217; Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0xada18, [Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 112; Z_to_bv 8 221; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 192; Z_to_bv 8 232; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 180; Z_to_bv 8 222; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 232; Z_to_bv 8 138; Z_to_bv 8 96; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0xadb00, [Z_to_bv 8 24; Z_to_bv 8 218; Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0xadb08, [Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 112; Z_to_bv 8 221; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 156; Z_to_bv 8 221; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 180; Z_to_bv 8 222; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 240; Z_to_bv 8 142; Z_to_bv 8 96; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0xadbf0, [Z_to_bv 8 8; Z_to_bv 8 219; Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0xa9088, [Z_to_bv 8 40; Z_to_bv 8 217; Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0x608648, [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0x60842c, [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0x608430, [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0x608438, [Z_to_bv 8 64; Z_to_bv 8 132; Z_to_bv 8 96; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0x608440, [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0x608448, [Z_to_bv 8 88; Z_to_bv 8 137; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0x608548, [Z_to_bv 8 120; Z_to_bv 8 99; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0x60866b, [Z_to_bv 8 0]);
    (* [comment removed for export] *) (0x608ad0, [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0x5e7a10, [Z_to_bv 8 0]);
    (* [comment removed for export] *) (0x608428, [Z_to_bv 8 0]);
    (* [comment removed for export] *) (0x608450, [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0x608550, [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);
    (* [comment removed for export] *) (0x5e7a14, [Z_to_bv 8 0]) ].

(* [comment removed for export] *)
Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
Lemma MAIN_CELLS_stderr : nth 0 MAIN_CELLS (0, []) = (STDERR_F, cells_bytes (file_cells stderr0)).
Proof. apply (f_equal2 pair); [reflexivity|]. apply bytes_eq_of_unsigned. vm_compute. reflexivity. Qed.
Lemma MAIN_CELLS_stdout : nth 2 MAIN_CELLS (0, []) = (STDOUT_F, cells_bytes (file_cells stdout0)).
Proof. apply (f_equal2 pair); [reflexivity|]. apply bytes_eq_of_unsigned. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Addrs.
  Variable usp : Z.                       (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Definition e_argc : Z := Z.of_nat (length argv).
  Definition e_envc : Z := Z.of_nat (length envp).
  (* [comment removed for export] *)
  Definition e_p0a : Z := usp + 8 * e_argc + 8 * e_envc + 184.
  Definition e_L0 : Z := Z.of_nat (length (nth 0 argv [])).
  Definition e_p1a : Z := e_p0a + e_L0 + 1.
  Definition e_L1 : Z := Z.of_nat (length (nth 1 argv [])).
  Definition e_span : Z := entry_stack_span argv envp.
  Definition STK_LO : Z := usp - 0x800000.
  Definition SPM : Z := usp - 48.          (* [comment removed for export] *)
End Addrs.

(* [comment removed for export] *)
Section SH.
  Context {Clg : Ceiling}.
  Definition STKSH_LO : Z := sh alloc_ceiling.
End SH.
Definition STKSH_HI : Z := 0x10007fff8000.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Record entry_raw (usp : Z) (argv envp : list (list byte)) (fs : Fs)
                 (R : bvmap 5 word) (FULL : word -> option byte) (md : Model) : Prop := {
  (* [comment removed for export] *)
  er_ra : getr R 1 = wz 0x982ac;
  er_sp : getr R 2 = wz (SPM usp);
  er_gp : getr R 3 = wz 0x10800;
  er_tp : getr R 4 = wz TPV;
  er_a0 : getr R 10 = wz (e_argc argv);
  er_a1 : getr R 11 = wz (usp + 8);
  (* [comment removed for export] *)
  er_usp : sp_window_lo <= usp /\ usp + e_span argv envp <= 2^47 /\ usp mod 16 = 0 /\ 0 <= e_span argv envp;
  er_str0 : e_p0a usp argv envp + e_L0 argv + 1 + 16 <= usp + e_span argv envp;
  er_str1 : 2 <= e_argc argv -> e_p1a usp argv envp + e_L1 argv + 1 + 16 <= usp + e_span argv envp;
  (* [comment removed for export] *)
  er_halt : m_halted md = None;
  er_fs : m_fs md = fs;
  er_fds : m_fds md = fds_std;
  (* [comment removed for export] *)
  er_tid : exists tid, 0 < tid < 2^22 /\ bytes_at rsegs FULL TID_CELL (le4 (wz tid));
  (* [comment removed for export] *)
  er_cells : Forall (fun c => bytes_at rsegs FULL (fst c) (snd c)) MAIN_CELLS;
  (* [comment removed for export] *)
  er_wimg : forall a, 0xa8000 <= a < 0x60a000 -> wview rsegs FULL (wz a) <> None;
  er_roimg : forall a, 0x10000 <= a < 0xa8000 -> FULL (wz a) = None;
  (* [comment removed for export] *)
  er_stack : forall a, STK_LO usp <= a < usp -> FULL (wz a) <> None;
  (* [comment removed for export] *)
  er_stkshadow : forall a, STKSH_LO <= a < STKSH_HI -> FULL (wz a) = Some (Z_to_bv 8 0);
  (* [comment removed for export] *)
  er_argv0p : bytes_at rsegs FULL (usp + 8) (le8 (wz (e_p0a usp argv envp)));
  er_argv1p : 2 <= e_argc argv -> bytes_at rsegs FULL (usp + 16) (le8 (wz (e_p1a usp argv envp)));
  er_argv0 : bytes_at rsegs FULL (e_p0a usp argv envp) (nth 0 argv [] ++ [Z_to_bv 8 0]);
  er_argv1 : 2 <= e_argc argv -> bytes_at rsegs FULL (e_p1a usp argv envp) (nth 1 argv [] ++ [Z_to_bv 8 0]);
  (* [comment removed for export] *)
  er_slack0 : exists sl, length sl = 16%nat /\ bytes_at rsegs FULL (e_p0a usp argv envp + e_L0 argv + 1) sl;
  er_slack1 : 2 <= e_argc argv -> exists sl, length sl = 16%nat /\ bytes_at rsegs FULL (e_p1a usp argv envp + e_L1 argv + 1) sl
}.

End CEIL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section EA.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Record entry_A0 (usp span : Z) (A0 : AS) : Prop := {
    ea_live   : forall p, a_live A0 p = None;
    ea_frames : forall ff, a_frame A0 ff = None;
    ea_bytes  : a_livebytes A0 = 0;
    ea_nlive  : a_nlive A0 = 0;
    ea_tiny   : a_tinycred A0 = TINYCRED0;
    ea_secc   : a_seccred A0 = SECCRED0;      (* [comment removed for export] *)
    ea_primc  : a_primcred A0 = PRIMCRED0;    (* [comment removed for export] *)
    (* [comment removed for export] *)
    ea_vis_stack : forall a, usp - 0x800000 <= a < usp + span -> hidc (ahull A0) (wz a) = false;
    ea_vis_stksh : forall a, STKSH_LO <= a < STKSH_HI -> hidc (ahull A0) (wz a) = false
  }.
End EA.

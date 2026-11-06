(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Frame Step Arr.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Cells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AGlofzw ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pa_smalloc (k : Z) : Z :=
  match k with
  | 0 => 0x4280c | 1 => 0x42980 | 7 => 0x42b10 | _ => 0
  end.
Definition pa_smalloc_always (k : Z) : Z :=
  0.  (* [comment removed for export] *)
Definition pa_sfree (k : Z) : Z :=
  match k with
  | 7 => 0x42c8c | _ => 0
  end.

(* [comment removed for export] *)
Definition pa_sites : list Z :=
  [ (* [comment removed for export] *)
    0x8696c; 0x869c0; 0x869e4; 0x86b14;
    (* [comment removed for export] *)
    0x86c4c; 0x86ce0;
    (* [comment removed for export] *)
    0x88bb8; 0x88c1c;
    (* [comment removed for export] *)
    0x88820; 0x885e8;
    (* [comment removed for export] *)
    0x89a94; 0x89b1c; 0x89b50;
    (* [comment removed for export] *)
    0x8a218; 0x8a238;
    (* [comment removed for export] *)
    0x8b158; 0x8b178 ].

(* [comment removed for export] *)
Definition pa_static (a : Z) : Prop :=
     (0xab090 <= a < 0xad740)     (* [comment removed for export] *)
  \/ (0xadc20 <= a < 0xb1ce0)     (* [comment removed for export] *)
  \/ (0xb1d00 <= a < 0xb1d58)     (* [comment removed for export] *)
  \/ (0xb1d58 <= a < 0xb2bb8)     (* [comment removed for export] *)
  \/ (0xb2c30 <= a < 0xb53b8)     (* [comment removed for export] *)
  \/ (0xb53c8 <= a < 0xb6098)     (* [comment removed for export] *)
  \/ (0xb609a <= a < 0xb60a0)     (* [comment removed for export] *)
  \/ (0xb60b8 <= a < 0x146ee8)     (* [comment removed for export] *)
  \/ (0x147008 <= a < 0x5d7a10).    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition pa_shared (a : Z) : Prop :=
     (0xa8000 <= a < 0xaa000)     (* [comment removed for export] *)
  \/ (0xaaec0 <= a < 0xaaec8)     (* [comment removed for export] *)
  \/ (0xaaec8 <= a < 0xab090)     (* [comment removed for export] *)
  \/ (0xad760 <= a < 0xad900)     (* [comment removed for export] *)
  \/ (0xb2bb8 <= a < 0xb2c30)     (* [comment removed for export] *)
  \/ (0xb53b8 <= a < 0xb53c8)     (* [comment removed for export] *)
  \/ (0xb6098 <= a < 0xb609a)     (* [comment removed for export] *)
  \/ (0xb60a0 <= a < 0xb60b8)     (* [comment removed for export] *)
  \/ (0x146ee8 <= a < 0x147008)     (* [comment removed for export] *)
  \/ (0x5e8380 <= a < 0x5e8388)     (* [comment removed for export] *)
  \/ (0x5e83d0 <= a < 0x5e83d8)     (* [comment removed for export] *)
  \/ (0x5e83d8 <= a < 0x5e83e0)     (* [comment removed for export] *)
  \/ (0x5e83e0 <= a < 0x5e83e8)     (* [comment removed for export] *)
  \/ (0x5e83e8 <= a < 0x5e83ec)     (* [comment removed for export] *)
  \/ (0x5e8400 <= a < 0x5e8408)     (* [comment removed for export] *)
  \/ (0x608698 <= a < 0x6086a0)     (* [comment removed for export] *)
  \/ (0x609780 <= a < 0x609788).    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition pa_gdescs : list (Z * Z * Z) :=
  [
    (0x216e0, 23, 64); (0x21720, 72, 128); (0x217a0, 12, 32); (0x217c0, 4, 32);
    (0x217e0, 2, 32); (0x21800, 11, 32); (0x21880, 10, 32); (0x218a0, 21, 64);
    (0x218e0, 13, 32); (0x21900, 26, 64); (0x21940, 14, 32); (0x21960, 12, 32);
    (0x21980, 14, 32); (0x219a0, 12, 32); (0x219c0, 15, 32); (0x219e0, 26, 64);
    (0x21a20, 15, 32); (0x21a40, 15, 32); (0x21a60, 15, 32); (0x21a80, 30, 64);
    (0x21ac0, 15, 32); (0x21ae0, 15, 32); (0x21b00, 15, 32); (0x21b20, 17, 64);
    (0x21b60, 25, 64); (0x21ba0, 13, 32); (0x21bc0, 13, 32); (0x21be0, 30, 64);
    (0x21c20, 26, 64); (0x21c60, 8, 32); (0x21c80, 14, 32); (0x21ca0, 12, 32);
    (0x21cc0, 18, 64); (0x21d00, 13, 32); (0x21d20, 35, 96); (0x21d80, 9, 32);
    (0x21da0, 10, 32); (0x21dc0, 25, 64); (0x21e00, 25, 64); (0x21e40, 17, 64);
    (0x21e80, 11, 32); (0x21ea0, 9, 32); (0x21ec0, 9, 32); (0x21ee0, 10, 32);
    (0x21f00, 15, 32); (0x21f20, 22, 64); (0x21f60, 10, 32); (0x21f80, 7, 32);
    (0x21fa0, 12, 32); (0x21fc0, 30, 64); (0x22000, 6, 32); (0x22020, 20, 64);
    (0x22060, 9, 32); (0x22080, 7, 32); (0x220a0, 14, 32); (0x220c0, 15, 32);
    (0x220e0, 30, 64); (0x22120, 13, 32); (0x22160, 76, 128); (0x221e0, 38, 96);
    (0x22240, 36, 96); (0x222a0, 61, 96); (0x22300, 19, 64); (0x22340, 35, 96);
    (0x223a0, 12, 32); (0x223c0, 6, 32); (0x223e0, 44, 96); (0x22440, 3, 32);
    (0x22480, 12, 32); (0x224a0, 54, 96); (0x22500, 54, 96); (0x22560, 1, 32);
    (0x22580, 9, 32); (0x225a0, 2, 32); (0x225c0, 11, 32); (0x225e0, 13, 32);
    (0x22600, 10, 32); (0x22640, 9, 32); (0x22660, 6, 32); (0x22680, 9, 32);
    (0x226a0, 11, 32); (0x226c0, 12, 32); (0x226e0, 9, 32); (0x22700, 9, 32);
    (0x22720, 8, 32); (0x22740, 18, 64); (0x22780, 12, 32); (0x227a0, 18, 64);
    (0x227e0, 21, 64); (0x22820, 12, 32); (0x22840, 18, 64); (0x22880, 20, 64);
    (0x228c0, 11, 32); (0x228e0, 14, 32); (0x22900, 15, 32); (0x22920, 16, 32);
    (0x22940, 22, 64); (0x22980, 16, 32); (0x229a0, 23, 64); (0x229e0, 23, 64);
    (0x22a20, 18, 64); (0x22a60, 35, 96); (0x22ae0, 24, 64); (0x22b20, 16, 32);
    (0x22b40, 13, 32); (0x22b60, 26, 64); (0x22ba0, 14, 32); (0x22bc0, 17, 64);
    (0x22c00, 17, 64); (0x22c60, 10, 32); (0x22c80, 24, 64); (0x22cc0, 14, 32);
    (0x22ce0, 27, 64); (0x22d20, 6, 32); (0x22d40, 1, 32); (0x22d60, 19, 64);
    (0x22da0, 18, 64); (0x22de0, 16, 32); (0x22e00, 8, 32); (0x22e20, 8, 32);
    (0x22e40, 6, 32); (0x22e60, 9, 32); (0x22e80, 10, 32); (0x22ea0, 11, 32);
    (0x22ec0, 82, 128); (0x22f40, 9, 32); (0x22f60, 81, 128); (0x22fe0, 11, 32);
    (0x23000, 10, 32); (0x23020, 10, 32); (0x23040, 4, 32); (0x23060, 8, 32);
    (0x23080, 13, 32); (0x230a0, 47, 96); (0x23100, 8, 32); (0x23120, 4, 32);
    (0x23140, 10, 32); (0x23160, 9, 32); (0x23180, 14, 32); (0x231a0, 53, 96);
    (0x23200, 11, 32); (0x23220, 39, 96); (0x23280, 8, 32); (0x232a0, 13, 32);
    (0x232c0, 14, 32); (0x232e0, 53, 96); (0x23340, 39, 96); (0x233a0, 12, 32);
    (0x233c0, 28, 64); (0x23400, 20, 64); (0x23440, 39, 96); (0x234a0, 12, 32);
    (0x234c0, 37, 96); (0x23520, 23, 64); (0x23560, 21, 64); (0x235a0, 16, 32);
    (0x235c0, 12, 32); (0x235e0, 26, 64); (0x23620, 15, 32); (0x23640, 12, 32);
    (0x23660, 36, 96); (0x236c0, 40, 96); (0x23720, 33, 96); (0x23780, 26, 64);
    (0x237c0, 11, 32); (0x237e0, 18, 64); (0x23820, 7, 32); (0x23840, 23, 64);
    (0x23880, 9, 32); (0x238a0, 13, 32); (0x238c0, 26, 64); (0x23900, 14, 32);
    (0x23920, 27, 64); (0x23960, 30, 64); (0x239a0, 16, 32); (0x239c0, 3, 32);
    (0x239e0, 11, 32); (0x23a00, 23, 64); (0x23a40, 28, 64); (0x23a80, 16, 32);
    (0x23aa0, 33, 96); (0x23b00, 18, 64); (0x23b40, 7, 32); (0x23b60, 4, 32);
    (0x23b80, 7, 32); (0x23ba0, 7, 32); (0x23bc0, 4, 32); (0x23be0, 6, 32);
    (0x23c00, 5, 32); (0x23c20, 9, 32); (0x23c40, 18, 64); (0x23c80, 8, 32);
    (0x23ca0, 7, 32); (0x23cc0, 8, 32); (0x23ce0, 5, 32); (0x23d00, 9, 32);
    (0x23d20, 15, 32); (0x23d40, 34, 96); (0x23da0, 15, 32); (0x23dc0, 38, 96);
    (0x23e20, 37, 96); (0x23e80, 43, 96); (0x23ee0, 8, 32); (0x23f00, 39, 96);
    (0x23f60, 13, 32); (0x23f80, 9, 32); (0x23fa0, 44, 96); (0x24000, 50, 96);
    (0x24060, 6, 32); (0x24080, 7, 32); (0x240a0, 7, 32); (0x240c0, 5, 32);
    (0x240e0, 5, 32); (0x24100, 6, 32); (0x24120, 51, 96); (0x24180, 55, 96);
    (0x241e0, 9, 32); (0x24200, 19, 64); (0x24240, 14, 32); (0x24260, 32, 64);
    (0x242a0, 34, 96); (0x24300, 30, 64); (0x24340, 15, 32); (0x24360, 38, 96);
    (0x243c0, 10, 32); (0x243e0, 40, 96); (0x24440, 17, 64); (0x24480, 15, 32);
    (0x244a0, 12, 32); (0x244c0, 16, 32); (0x244e0, 13, 32); (0x24500, 32, 64);
    (0x24560, 512, 640); (0x24800, 1024, 1280); (0x24d00, 4096, 5120); (0x26100, 128, 160);
    (0xa8e00, 8, 32); (0xa8e20, 8, 32); (0xa8e40, 8, 32); (0xa8e60, 8, 32);
    (0xa8e80, 8, 32); (0xa8ea0, 8, 32); (0xa8ec0, 8, 32); (0xa8ee0, 8, 32);
    (0xa8f00, 8, 32); (0xa8f20, 8, 32); (0xa8f40, 8, 32); (0xa8f60, 8, 32);
    (0xa8f80, 8, 32); (0xa8fa0, 8, 32); (0xa8fc0, 8, 32); (0xa8fe0, 8, 32);
    (0xad760, 32, 64); (0xad7a0, 112, 160); (0xad840, 64, 96); (0xad8a0, 48, 96);
    (0x5e7a40, 8, 32); (0x5e7a60, 8, 32); (0x5e7aa0, 8, 32) ].

(* [comment removed for export] *)
Definition pa_asan_flags_bytes : list byte := [Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 190; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 85; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 161; Z_to_bv 8 64; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Definition pa_common_flags_bytes : list byte := [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 161; Z_to_bv 8 64; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 30; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 199; Z_to_bv 8 24; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 253; Z_to_bv 8 67; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 161; Z_to_bv 8 64; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 161; Z_to_bv 8 64; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 5; Z_to_bv 8 226; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 119; Z_to_bv 8 144; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0].

(* [comment removed for export] *)
Definition gshadow_entry (d : Z * Z * Z) : Z * list byte :=
  match d with (b, s, r) => (sh b, shpat s ++ repeat (Z_to_bv 8 0xf9) (Z.to_nat ((r - (s + 7) / 8 * 8) / 8))) end.
Definition pa_gshadow : list (Z * list byte) := map gshadow_entry pa_gdescs.

(* [comment removed for export] *)
Definition pa_cells : list (Z * list byte) :=
  [ (0xa9190, le8 (Z_to_bv 64 0xb53b8));   (* [comment removed for export] *)
    (0xb53b8, le8 (Z_to_bv 64 kShadowOffset));   (* [comment removed for export] *)
    (0xa91e8, le8 (Z_to_bv 64 0xb53c0));   (* [comment removed for export] *)
    (0xb53c0, le4 (Z_to_bv 64 1));          (* [comment removed for export] *)
    (0xa91b0, le8 (Z_to_bv 64 0xab038));   (* [comment removed for export] *)
    (0xab038, le8 (Z_to_bv 64 0xa25c8));   (* [comment removed for export] *)
    (0xa91b8, le8 (Z_to_bv 64 0xab030));   (* [comment removed for export] *)
    (0xab030, le8 (Z_to_bv 64 0xa21c4));   (* [comment removed for export] *)
    (0xa9d00, le8 (Z_to_bv 64 0xb6099));   (* [comment removed for export] *)
    (0xb6098, [Z_to_bv 8 1]);               (* [comment removed for export] *)
    (0xb6099, [Z_to_bv 8 1]);               (* [comment removed for export] *)
    (0xa9cf8, le8 (Z_to_bv 64 0x57614));    (* [comment removed for export] *)
    (0xa9df8, le8 (Z_to_bv 64 0xa9088));   (* [comment removed for export] *)
    (0xa9e00, le8 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xa9e10, le8 (Z_to_bv 64 0x24560));    (* [comment removed for export] *)
    (0xa9e18, le8 (Z_to_bv 64 0x5e7a40));   (* [comment removed for export] *)
    (0xa9e20, le8 (Z_to_bv 64 0x5e7a60));   (* [comment removed for export] *)
    (0xa9e38, le8 (Z_to_bv 64 0x608418));   (* [comment removed for export] *)
    (0xa9e90, le8 (Z_to_bv 64 1) ++ le8 (Z_to_bv 64 (-0x800)));  (* [comment removed for export] *)
    (0xa9ea0, le8 (Z_to_bv 64 0x8));        (* [comment removed for export] *)
    (0xa9df0, le8 (Z_to_bv 64 0x10));       (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xb60a0, le8 (Z_to_bv 64 0x7fffffffffff)); (* [comment removed for export] *)
    (0xb60a8, le8 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xb60b0, le8 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xa9198, le8 (Z_to_bv 64 0xb60a8));   (* [comment removed for export] *)
    (0xa91a0, le8 (Z_to_bv 64 0xb60b0));   (* [comment removed for export] *)
    (0xa91a8, le8 (Z_to_bv 64 0xb60a0));   (* [comment removed for export] *)
    (0xa9180, le8 (Z_to_bv 64 0x146ee8));   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xa9178, le8 (Z_to_bv 64 0xab070));   (* [comment removed for export] *)
    (0xab070, le8 (Z_to_bv 64 0x19805));    (* [comment removed for export] *)
    (0xa91d0, le8 (Z_to_bv 64 1));          (* [comment removed for export] *)
    (0xa91d8, le8 (Z_to_bv 64 0x146edc));   (* [comment removed for export] *)
    (0x146edc, le4 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0x608698, le8 (Z_to_bv 64 4096));       (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xb2001, [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);   (* [comment removed for export] *)
    (0xb20ca, [Z_to_bv 8 0; Z_to_bv 8 0]);               (* [comment removed for export] *)
    (0xb2131, [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);   (* [comment removed for export] *)
    (0x144e4a, [Z_to_bv 8 0; Z_to_bv 8 0]);               (* [comment removed for export] *)
    (0xa9188, le8 (Z_to_bv 64 0xb2bb8));   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xaaec8, le8 (Z_to_bv 64 0xa28fc));   (* [comment removed for export] *)
    (0xaaed8, le8 (Z_to_bv 64 0xa26c0));   (* [comment removed for export] *)
    (0xaaee0, le8 (Z_to_bv 64 0xa2194));   (* [comment removed for export] *)
    (0xaaee8, le8 (Z_to_bv 64 0xa20c4));   (* [comment removed for export] *)
    (0xaafd8, le8 (Z_to_bv 64 0xa2814));   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xaaf00, le8 (Z_to_bv 64 0xa79b0));   (* [comment removed for export] *)
    (0xaaf08, le8 (Z_to_bv 64 0x9e778));   (* [comment removed for export] *)
    (0xaaf20, le8 (Z_to_bv 64 0xa1b10));   (* [comment removed for export] *)
    (0xaaf28, le8 (Z_to_bv 64 0x9ea00));   (* [comment removed for export] *)
    (0xaaf30, le8 (Z_to_bv 64 0xa1b2c));   (* [comment removed for export] *)
    (0xaafe0, le8 (Z_to_bv 64 0xa2b38));   (* [comment removed for export] *)
    (0xaaef0, le8 (Z_to_bv 64 0xa20c8));   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xb4c20, [Z_to_bv 8 1]);               (* [comment removed for export] *)
    (0xb4c24, le4 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xb4c1c, [Z_to_bv 8 1]);               (* [comment removed for export] *)
    (0x147260, [Z_to_bv 8 0]);               (* [comment removed for export] *)
    (0xb1d00, le8 (Z_to_bv 64 1));          (* [comment removed for export] *)
    (0xb1d50, [Z_to_bv 8 0]);               (* [comment removed for export] *)
    (0xb2c70, le8 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xa9e68, le8 (Z_to_bv 64 0xa8a18) ++ le8 (Z_to_bv 64 0xa8a08));  (* [comment removed for export] *)
    (0xa8a08, le8 (Z_to_bv 64 0x87728) ++ le8 (Z_to_bv 64 0x36014));    (* [comment removed for export] *)
    (0xa9160, le8 (Z_to_bv 64 0x98890) ++ le8 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xaaec0, le8 (Z_to_bv 64 0xaaec0));   (* [comment removed for export] *)
    (0xa9e28, le8 (Z_to_bv 64 GMETA) ++ le8 (Z_to_bv 64 (GMETA + 64 * 259)));  (* [comment removed for export] *)
    (0xa9170, le8 (Z_to_bv 64 0x144e60));   (* [comment removed for export] *)
    (0x144e60, le8 (Z_to_bv 64 4096));       (* [comment removed for export] *)
    (GMETA, cells_bytes (gtab_cells gtab));  (* [comment removed for export] *)
    (0x8000db84, repeat (Z_to_bv 8 0xf9) 2072); (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xa8e20, le8 (Z_to_bv 64 0x22e00));
    (0xa8e40, le8 (Z_to_bv 64 0x22e40));
    (0xa8e60, le8 (Z_to_bv 64 0x23080));
    (0xa8e80, le8 (Z_to_bv 64 0x22e60));
    (0xa8ea0, le8 (Z_to_bv 64 0x23020));
    (0xa8ec0, le8 (Z_to_bv 64 0x23140));
    (0xa8ee0, le8 (Z_to_bv 64 0x23160));
    (0xa8f00, le8 (Z_to_bv 64 0x23100));
    (0xa8f20, le8 (Z_to_bv 64 0x22fe0));
    (0xa8f40, le8 (Z_to_bv 64 0x23180));
    (0xa8f60, le8 (Z_to_bv 64 0x232a0));
    (0xa8f80, le8 (Z_to_bv 64 0x232c0));
    (0xa8fa0, le8 (Z_to_bv 64 0x233a0));
    (0xa8fc0, le8 (Z_to_bv 64 0x23620));
    (0xa8fe0, le8 (Z_to_bv 64 0x235a0));
    (0xad760, le8 (Z_to_bv 64 0x23b60) ++ le8 (Z_to_bv 64 0xa8e20) ++ le8 (Z_to_bv 64 0x0) ++ le8 (Z_to_bv 64 0xa8e40));
    (0xad7a0, le8 (Z_to_bv 64 0x23b80) ++ le8 (Z_to_bv 64 0xa8e60) ++ le8 (Z_to_bv 64 0x23ba0) ++ le8 (Z_to_bv 64 0xa8e80) ++ le8 (Z_to_bv 64 0x23bc0) ++ le8 (Z_to_bv 64 0xa8ea0) ++ le8 (Z_to_bv 64 0x23be0) ++ le8 (Z_to_bv 64 0xa8ec0) ++ le8 (Z_to_bv 64 0x23c00) ++ le8 (Z_to_bv 64 0xa8ee0) ++ le8 (Z_to_bv 64 0x23c20) ++ le8 (Z_to_bv 64 0xa8f00) ++ le8 (Z_to_bv 64 0x0) ++ le8 (Z_to_bv 64 0xa8f20));
    (0xad840, le8 (Z_to_bv 64 0x23c80) ++ le8 (Z_to_bv 64 0xa8f40) ++ le8 (Z_to_bv 64 0x23ca0) ++ le8 (Z_to_bv 64 0xa8f60) ++ le8 (Z_to_bv 64 0x23cc0) ++ le8 (Z_to_bv 64 0xa8f80) ++ le8 (Z_to_bv 64 0x0) ++ le8 (Z_to_bv 64 0xa8fa0));
    (0xad8a0, le8 (Z_to_bv 64 0x23ce0) ++ le8 (Z_to_bv 64 0xa8fc0) ++ le8 (Z_to_bv 64 0x23d00) ++ le8 (Z_to_bv 64 0xa8fc0) ++ le8 (Z_to_bv 64 0x0) ++ le8 (Z_to_bv 64 0xa8fe0));
    (0x5e8380, le8 (Z_to_bv 64 0x609780));   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xaaf68, le8 (Z_to_bv 64 0xa2ea0));   (* [comment removed for export] *)
    (0xa9e90, le8 (Z_to_bv 64 1) ++ le8 (Z_to_bv 64 0xfffffffffffff800));  (* [comment removed for export] *)
    (0xa91e0, le8 (Z_to_bv 64 0x144e58));   (* [comment removed for export] *)
    (0x144e58, le4 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xa9ea0, le8 (Z_to_bv 64 8));          (* [comment removed for export] *)
    (0x146f71, [Z_to_bv 8 1]);               (* [comment removed for export] *)
    (0x5e83d0, le8 (Z_to_bv 64 0x5e83f8));   (* [comment removed for export] *)
    (0x5e8400, le8 (Z_to_bv 64 0x5e8bd8));   (* [comment removed for export] *)
    (0x5e83e8, le4 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xb2bb8, pa_asan_flags_bytes);         (* [comment removed for export] *)
    (0x146ee8, pa_common_flags_bytes) ].     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition pa_zero_shadow : list (Z * nat) :=
  [ (0x7fffa000, 8926%nat);
    (0x7fffc2e4, 9%nat);
    (0x7fffc2f4, 1%nat);
    (0x7fffc300, 1%nat);
    (0x7fffc304, 13%nat);
    (0x7fffc314, 2%nat);
    (0x7fffc31c, 1%nat);
    (0x7fffc320, 3%nat);
    (0x7fffc328, 1%nat);
    (0x7fffc32c, 1%nat);
    (0x7fffc330, 1%nat);
    (0x7fffc334, 1%nat);
    (0x7fffc338, 1%nat);
    (0x7fffc33c, 3%nat);
    (0x7fffc344, 1%nat);
    (0x7fffc348, 1%nat);
    (0x7fffc34c, 1%nat);
    (0x7fffc350, 3%nat);
    (0x7fffc358, 1%nat);
    (0x7fffc35c, 1%nat);
    (0x7fffc360, 1%nat);
    (0x7fffc364, 2%nat);
    (0x7fffc36c, 3%nat);
    (0x7fffc374, 1%nat);
    (0x7fffc378, 1%nat);
    (0x7fffc37c, 3%nat);
    (0x7fffc384, 3%nat);
    (0x7fffc38c, 1%nat);
    (0x7fffc390, 1%nat);
    (0x7fffc394, 1%nat);
    (0x7fffc398, 2%nat);
    (0x7fffc3a0, 1%nat);
    (0x7fffc3a4, 4%nat);
    (0x7fffc3b0, 1%nat);
    (0x7fffc3b4, 1%nat);
    (0x7fffc3b8, 3%nat);
    (0x7fffc3c0, 3%nat);
    (0x7fffc3c8, 2%nat);
    (0x7fffc3d0, 1%nat);
    (0x7fffc3d4, 1%nat);
    (0x7fffc3d8, 1%nat);
    (0x7fffc3dc, 1%nat);
    (0x7fffc3e0, 1%nat);
    (0x7fffc3e4, 2%nat);
    (0x7fffc3ec, 1%nat);
    (0x7fffc3f4, 1%nat);
    (0x7fffc3f8, 3%nat);
    (0x7fffc404, 2%nat);
    (0x7fffc40c, 1%nat);
    (0x7fffc414, 1%nat);
    (0x7fffc418, 1%nat);
    (0x7fffc41c, 3%nat);
    (0x7fffc424, 1%nat);
    (0x7fffc428, 13%nat);
    (0x7fffc43c, 4%nat);
    (0x7fffc448, 4%nat);
    (0x7fffc454, 7%nat);
    (0x7fffc460, 2%nat);
    (0x7fffc468, 4%nat);
    (0x7fffc474, 1%nat);
    (0x7fffc47c, 5%nat);
    (0x7fffc48c, 5%nat);
    (0x7fffc494, 6%nat);
    (0x7fffc4a0, 6%nat);
    (0x7fffc4b0, 1%nat);
    (0x7fffc4b8, 1%nat);
    (0x7fffc4bc, 1%nat);
    (0x7fffc4c0, 1%nat);
    (0x7fffc4c4, 5%nat);
    (0x7fffc4d0, 1%nat);
    (0x7fffc4d4, 1%nat);
    (0x7fffc4d8, 1%nat);
    (0x7fffc4dc, 1%nat);
    (0x7fffc4e0, 1%nat);
    (0x7fffc4e4, 1%nat);
    (0x7fffc4e8, 2%nat);
    (0x7fffc4f0, 1%nat);
    (0x7fffc4f4, 2%nat);
    (0x7fffc4fc, 2%nat);
    (0x7fffc504, 1%nat);
    (0x7fffc508, 2%nat);
    (0x7fffc510, 2%nat);
    (0x7fffc518, 1%nat);
    (0x7fffc51c, 1%nat);
    (0x7fffc520, 1%nat);
    (0x7fffc524, 2%nat);
    (0x7fffc528, 2%nat);
    (0x7fffc530, 2%nat);
    (0x7fffc534, 2%nat);
    (0x7fffc53c, 2%nat);
    (0x7fffc544, 2%nat);
    (0x7fffc54c, 4%nat);
    (0x7fffc558, 7%nat);
    (0x7fffc564, 2%nat);
    (0x7fffc568, 1%nat);
    (0x7fffc56c, 3%nat);
    (0x7fffc574, 1%nat);
    (0x7fffc578, 2%nat);
    (0x7fffc580, 2%nat);
    (0x7fffc588, 5%nat);
    (0x7fffc590, 3%nat);
    (0x7fffc598, 1%nat);
    (0x7fffc59c, 3%nat);
    (0x7fffc5ac, 2%nat);
    (0x7fffc5b4, 2%nat);
    (0x7fffc5bc, 2%nat);
    (0x7fffc5c0, 1%nat);
    (0x7fffc5c4, 1%nat);
    (0x7fffc5cc, 1%nat);
    (0x7fffc5d0, 1%nat);
    (0x7fffc5d4, 1%nat);
    (0x7fffc5d8, 10%nat);
    (0x7fffc5e8, 1%nat);
    (0x7fffc5ec, 10%nat);
    (0x7fffc5fc, 1%nat);
    (0x7fffc600, 1%nat);
    (0x7fffc604, 1%nat);
    (0x7fffc60c, 1%nat);
    (0x7fffc610, 1%nat);
    (0x7fffc614, 5%nat);
    (0x7fffc620, 1%nat);
    (0x7fffc628, 1%nat);
    (0x7fffc62c, 1%nat);
    (0x7fffc630, 1%nat);
    (0x7fffc634, 6%nat);
    (0x7fffc640, 1%nat);
    (0x7fffc644, 4%nat);
    (0x7fffc650, 1%nat);
    (0x7fffc654, 1%nat);
    (0x7fffc658, 1%nat);
    (0x7fffc65c, 6%nat);
    (0x7fffc668, 4%nat);
    (0x7fffc674, 1%nat);
    (0x7fffc678, 3%nat);
    (0x7fffc680, 2%nat);
    (0x7fffc688, 4%nat);
    (0x7fffc694, 1%nat);
    (0x7fffc698, 4%nat);
    (0x7fffc6a4, 2%nat);
    (0x7fffc6ac, 2%nat);
    (0x7fffc6b4, 2%nat);
    (0x7fffc6b8, 1%nat);
    (0x7fffc6bc, 3%nat);
    (0x7fffc6c4, 1%nat);
    (0x7fffc6c8, 1%nat);
    (0x7fffc6cc, 4%nat);
    (0x7fffc6d8, 5%nat);
    (0x7fffc6e4, 4%nat);
    (0x7fffc6f0, 3%nat);
    (0x7fffc6f8, 1%nat);
    (0x7fffc6fc, 2%nat);
    (0x7fffc708, 2%nat);
    (0x7fffc710, 1%nat);
    (0x7fffc714, 1%nat);
    (0x7fffc718, 3%nat);
    (0x7fffc720, 1%nat);
    (0x7fffc724, 3%nat);
    (0x7fffc72c, 3%nat);
    (0x7fffc734, 2%nat);
    (0x7fffc73c, 1%nat);
    (0x7fffc740, 2%nat);
    (0x7fffc748, 3%nat);
    (0x7fffc750, 2%nat);
    (0x7fffc754, 4%nat);
    (0x7fffc760, 2%nat);
    (0x7fffc784, 1%nat);
    (0x7fffc788, 2%nat);
    (0x7fffc790, 1%nat);
    (0x7fffc798, 1%nat);
    (0x7fffc7a0, 1%nat);
    (0x7fffc7a4, 1%nat);
    (0x7fffc7a8, 4%nat);
    (0x7fffc7b4, 1%nat);
    (0x7fffc7b8, 4%nat);
    (0x7fffc7c4, 4%nat);
    (0x7fffc7d0, 5%nat);
    (0x7fffc7dc, 1%nat);
    (0x7fffc7e0, 4%nat);
    (0x7fffc7ec, 1%nat);
    (0x7fffc7f0, 1%nat);
    (0x7fffc7f4, 5%nat);
    (0x7fffc800, 6%nat);
    (0x7fffc824, 6%nat);
    (0x7fffc830, 6%nat);
    (0x7fffc83c, 1%nat);
    (0x7fffc840, 2%nat);
    (0x7fffc848, 1%nat);
    (0x7fffc84c, 4%nat);
    (0x7fffc854, 4%nat);
    (0x7fffc860, 3%nat);
    (0x7fffc868, 1%nat);
    (0x7fffc86c, 4%nat);
    (0x7fffc878, 1%nat);
    (0x7fffc87c, 5%nat);
    (0x7fffc888, 2%nat);
    (0x7fffc890, 1%nat);
    (0x7fffc894, 1%nat);
    (0x7fffc898, 2%nat);
    (0x7fffc89c, 1%nat);
    (0x7fffc8a0, 4%nat);
    (0x7fffc8a8, 68%nat);
    (0x7fffc8fc, 132%nat);
    (0x7fffc9a0, 512%nat);
    (0x7fffcc20, 16%nat);
    (0x7fffcc34, 66957%nat);
    (0x8000d1c4, 1%nat);
    (0x8000d1c8, 1%nat);
    (0x8000d1cc, 1%nat);
    (0x8000d1d0, 1%nat);
    (0x8000d1d4, 1%nat);
    (0x8000d1d8, 1%nat);
    (0x8000d1dc, 1%nat);
    (0x8000d1e0, 1%nat);
    (0x8000d1e4, 1%nat);
    (0x8000d1e8, 1%nat);
    (0x8000d1ec, 1%nat);
    (0x8000d1f0, 1%nat);
    (0x8000d1f4, 1%nat);
    (0x8000d1f8, 1%nat);
    (0x8000d1fc, 1%nat);
    (0x8000d200, 2288%nat);
    (0x8000daf4, 14%nat);
    (0x8000db08, 8%nat);
    (0x8000db14, 6%nat);
    (0x8000db20, 100%nat);
    (0x8000e39c, 682925%nat);
    (0x800b4f4c, 1%nat);
    (0x800b4f50, 5%nat);
    (0x800b4f58, 17576%nat) ].
Definition pa_zshadow : list (Z * list byte) := map (fun p => (fst p, repeat (Z_to_bv 8 0) (snd p))) pa_zero_shadow.
Definition pa_consts : list (Z * list byte) := pa_cells ++ pa_gshadow ++ pa_zshadow.

Definition LPA : clayout := {|
  cl_segs := rsegs;
  cl_malloc_pc := Z_to_bv 64 0x58970;
  cl_free_pc := Z_to_bv 64 0x5896c;
  cl_calloc_pc := Z_to_bv 64 0x58974;
  cl_realloc_pc := Z_to_bv 64 0x58978;
  cl_smalloc_pc := fun k => Z_to_bv 64 (pa_smalloc k);
  cl_sfree_pc := fun k => Z_to_bv 64 (pa_sfree k);
  cl_tp := Z_to_bv 64 0x5e83d8;
  cl_errno := 0x5e8334;                      (* [comment removed for export] *)
  cl_sites := pa_sites;
  cl_image_lo := 0x10000;
  cl_rw_lo := 0xa8000;
  cl_image_hi := 0x60a000;
  cl_static := pa_static;
  cl_shared := pa_shared;
  cl_consts := pa_consts
|}.

(* [comment removed for export] *)
Definition pa_image_ivs : hull := [(0x10000, 0x35000); (0x35000, 0xa8000); (0xa8000, 0xaa000); (0xaa000, 0x60a000)].

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pa_seg_bases :
  Z.of_N (seg_base Asan.Asan_segment_000) = 0x10000 /\
  Z.of_N (seg_size Asan.Asan_segment_000) = 0x25000 /\
  Z.of_N (seg_base Asan.Asan_segment_001) = 0x35000 /\
  Z.of_N (seg_size Asan.Asan_segment_001) = 0x73000 /\
  Z.of_N (seg_base Asan.Asan_segment_002) = 0xa8000 /\
  Z.of_N (seg_size Asan.Asan_segment_002) = 0x2000 /\
  Z.of_N (seg_base Asan.Asan_segment_003) = 0xaa000 /\
  Z.of_N (seg_size Asan.Asan_segment_003) = 0x560000.
Proof. repeat split; vm_compute; reflexivity. Qed.

Ltac pa_unfold_segs :=
  unfold rsegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments;
  cbn [find_segment];
  replace (Z.of_N (seg_base Asan.Asan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Asan.Asan_segment_000)) with 0x25000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base Asan.Asan_segment_001)) with 0x35000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Asan.Asan_segment_001)) with 0x73000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base Asan.Asan_segment_002)) with 0xa8000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Asan.Asan_segment_002)) with 0x2000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base Asan.Asan_segment_003)) with 0xaa000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Asan.Asan_segment_003)) with 0x560000%Z by (vm_compute; reflexivity).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pa_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x60a000 <= z) ->
  find_segment rsegs z n = None.
Proof.
  intros z n Hn Hz. pa_unfold_segs.
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x25000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x35000 z); destruct (Z.leb_spec0 (z + n) (0x35000 + 0x73000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xa8000 z); destruct (Z.leb_spec0 (z + n) (0xa8000 + 0x2000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xaa000 z); destruct (Z.leb_spec0 (z + n) (0xaa000 + 0x560000)); cbn [andb]; try lia.
  all: reflexivity.
Qed.

Lemma pa_ro_addr_iff : forall a : word, ro_addr rsegs a = true <-> 0x10000 <= bv_unsigned a < 0xa8000.
Proof.
  intros a. pose proof (bv_unsigned_in_range _ a) as R. change (bv_modulus 64) with (2^64) in R.
  set (z := bv_unsigned a) in *. unfold ro_addr. fold z. pa_unfold_segs.
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + 1) (0x10000 + 0x25000)); cbn [andb];
    [replace (seg_writable Asan.Asan_segment_000) with false by (vm_compute; reflexivity); cbn; split; intros; [lia|reflexivity] | | |].
  all: destruct (Z.leb_spec0 0x35000 z); destruct (Z.leb_spec0 (z + 1) (0x35000 + 0x73000)); cbn [andb]; try lia;
    try (replace (seg_writable Asan.Asan_segment_001) with false by (vm_compute; reflexivity); cbn; split; intros; [lia|reflexivity]).
  all: destruct (Z.leb_spec0 0xa8000 z); destruct (Z.leb_spec0 (z + 1) (0xa8000 + 0x2000)); cbn [andb]; try lia;
    try (replace (seg_writable Asan.Asan_segment_002) with true by (vm_compute; reflexivity); cbn; split; intros; [discriminate|lia]).
  all: destruct (Z.leb_spec0 0xaa000 z); destruct (Z.leb_spec0 (z + 1) (0xaa000 + 0x560000)); cbn [andb]; try lia;
    try (replace (seg_writable Asan.Asan_segment_003) with true by (vm_compute; reflexivity); cbn; split; intros; [discriminate|lia]).
  all: split; intros; [discriminate| lia].
Qed.

Lemma pa_ro_addr_false : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x60a000 <= bv_unsigned x) -> ro_addr rsegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite pa_find_segment_none by lia. reflexivity. Qed.
Lemma pa_memory_read_none : forall (x : word) n,
  1 <= Z.of_N n -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x60a000 <= bv_unsigned x) -> memory_read rsegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite pa_find_segment_none by lia. reflexivity. Qed.
Lemma pa_seg_rom_none : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x60a000 <= bv_unsigned x) -> seg_rom rsegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite pa_memory_read_none by (cbn; lia). reflexivity. Qed.
Lemma pa_wview_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x60a000 <= bv_unsigned x) -> wview rsegs m x = m x.
Proof. intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite pa_find_segment_none by lia. reflexivity. Qed.
Lemma pa_mrd_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x60a000 <= bv_unsigned x) -> mrd rsegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply pa_seg_rom_none. exact Hx. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma asI_static_where : forall a, cl_static LPA a -> cl_rw_lo LPA <= a < cl_image_hi LPA.
Proof. cbn [cl_static cl_rw_lo cl_image_hi LPA]. unfold pa_static. lia. Qed.

Lemma asI_shared_where : forall a, cl_shared LPA a -> cl_rw_lo LPA <= a < cl_image_hi LPA.
Proof. cbn [cl_shared cl_rw_lo cl_image_hi LPA]. unfold pa_shared. lia. Qed.

Lemma asI_shared_not_static : forall a, cl_shared LPA a -> ~ cl_static LPA a.
Proof. cbn [cl_shared cl_static LPA]. unfold pa_shared, pa_static. lia. Qed.

Lemma asI_errno_where : cl_rw_lo LPA <= cl_errno LPA /\ cl_errno LPA + 4 <= cl_image_hi LPA.
Proof. cbn [cl_rw_lo cl_errno cl_image_hi LPA]. lia. Qed.

Lemma asI_errno_not_static : forall i, 0 <= i < 4 -> ~ cl_static LPA (cl_errno LPA + i) /\ ~ cl_shared LPA (cl_errno LPA + i).
Proof. cbn [cl_static cl_shared cl_errno LPA]. unfold pa_static, pa_shared. lia. Qed.

(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma asI_layout_order : 4096 <= cl_image_lo LPA <= cl_rw_lo LPA /\ cl_rw_lo LPA <= cl_image_hi LPA
                         /\ cl_image_hi LPA <= kLowShadowMapBeg /\ kHighMemBeg + 65536 <= alloc_ceiling.
Proof. cbn [cl_image_lo cl_rw_lo cl_image_hi LPA]. unfold kLowShadowMapBeg, kHighMemBeg. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. Qed.

Lemma asI_ro_addr_iff : forall a : word, ro_addr (cl_segs LPA) a = true <-> cl_image_lo LPA <= bv_unsigned a < cl_rw_lo LPA.
Proof. cbn [cl_segs cl_image_lo cl_rw_lo LPA]. exact pa_ro_addr_iff. Qed.

Lemma asI_seg_rom_outside : forall a : word, ~ in_image LPA (bv_unsigned a) -> seg_rom (cl_segs LPA) a = None.
Proof.
  unfold in_image. cbn [cl_segs cl_image_lo cl_image_hi LPA]. intros a H.
  pose proof (bv_unsigned_in_range _ a) as R. change (bv_modulus 64) with (2^64) in R.
  apply pa_seg_rom_none. lia.
Qed.

Lemma asI_find_segment_outside : forall a : word, ~ in_image LPA (bv_unsigned a) -> find_segment (cl_segs LPA) (bv_unsigned a) 1 = None.
Proof.
  unfold in_image. cbn [cl_segs cl_image_lo cl_image_hi LPA]. intros a H.
  pose proof (bv_unsigned_in_range _ a) as R. change (bv_modulus 64) with (2^64) in R.
  apply pa_find_segment_none; lia.
Qed.

Lemma asI_wx : wx_segs_nowrap (cl_segs LPA).
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pa_segs_in_hull : forall H, segs_in_hull (pa_image_ivs ++ H) rsegs.
Proof. intros H. apply segs_in_hull_of_prefix. vm_compute. reflexivity. Qed.
Lemma pa_hull_off_segments : forall H, H_off_segments rsegs (hidc (pa_image_ivs ++ H)).
Proof. intros H. apply H_off_segments_hidc. apply pa_segs_in_hull. Qed.
Lemma pa_image_visible : forall H a, in_image LPA a -> hidc (pa_image_ivs ++ H) (Z_to_bv 64 a) = false.
Proof.
  intros H a Ha. unfold hidc. apply Bool.negb_false_iff. unfold in_image in Ha. cbn [cl_image_lo cl_image_hi LPA] in Ha.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 a) with (a mod 2^64). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). rewrite Z.mod_small by lia.
  unfold pa_image_ivs.
  destruct (Z.lt_ge_cases a 0x35000); [apply (in_hullb_intro _ _ 0x10000 0x35000); [cbn; tauto|lia]|].
  destruct (Z.lt_ge_cases a 0xa8000); [apply (in_hullb_intro _ _ 0x35000 0xa8000); [cbn; tauto|lia]|].
  destruct (Z.lt_ge_cases a 0xaa000); [apply (in_hullb_intro _ _ 0xa8000 0xaa000); [cbn; tauto|lia]|].
  apply (in_hullb_intro _ _ 0xaa000 0x60a000); [cbn; tauto|lia].
Qed.

End CEIL.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma pa_sites_ex : In 0x8a238 (cl_sites LPA). Proof. cbn. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pa_site_pcs : list Z := [0x58c14; 0x58ab4; 0x58e48; 0x590e8].
Definition pa_start_keys : list (list Z) := [[0x44620; 0x45970]; [0x44620]].
Definition pa_dkeys : list (list Z) := pa_start_keys ++ site_keys pa_site_pcs pa_sites.

Lemma pa_dkeys_short : Forall (fun k => (1 <= length k <= 255)%nat) pa_dkeys.
Proof.
  unfold pa_dkeys, pa_start_keys, site_keys. apply Forall_forall. intros k Hk.
  apply in_app_iff in Hk as [Hk|Hk]; [cbn in Hk; destruct Hk as [<-|[<-|[]]]; cbn; lia|].
  apply in_flat_map in Hk as (pc & _ & [<-|Hk]); [cbn; lia|]. apply in_map_iff in Hk as (ra & <- & _). cbn; lia.
Qed.
Lemma pa_dkeys_len : (length pa_dkeys <= 2048)%nat.
Proof. vm_compute. lia. Qed.
Lemma pa_dkeys_hashes : NoDup (map depot_hashC pa_dkeys).
Proof. apply znodupb_sound. vm_compute. reflexivity. Qed.
Lemma pa_dkeys_sites : forall pc ra, In pc pa_site_pcs -> In ra (cl_sites LPA) -> In [pc; ra] pa_dkeys /\ In [pc] pa_dkeys.
Proof.
  intros pc ra Hp Hr. unfold pa_dkeys. split; apply in_or_app; right; [apply site_keys_in2| apply site_keys_in1]; assumption.
Qed.
Lemma pa_dkeys_start2 : In [0x44620; 0x45970] pa_dkeys. Proof. cbn. tauto. Qed.
Lemma pa_dkeys_start1 : In [0x44620] pa_dkeys. Proof. cbn. tauto. Qed.
(* [comment removed for export] *)
Lemma pa_sites_range : Forall (fun s => 4096 <= s < 2^47) pa_sites.
Proof. unfold pa_sites. repeat constructor; lia. Qed.
Lemma pa_pcs_not_sites : forall pc, In pc pa_site_pcs -> ~ In pc pa_sites.
Proof. intros pc Hp Hs. cbn in Hp, Hs. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition paS_ivs : list (Z * Z) :=
  [(0xab090, 0xad740); (0xadc20, 0xb1ce0); (0xb1d00, 0xb1d58); (0xb1d58, 0xb2bb8); (0xb2c30, 0xb53b8); (0xb53c8, 0xb6098); (0xb609a, 0xb60a0); (0xb60b8, 0x146ee8); (0x147008, 0x5d7a10)].
Definition paH_ivs : list (Z * Z) :=
  [(0xa8000, 0xaa000); (0xaaec0, 0xaaec8); (0xaaec8, 0xab090); (0xad760, 0xad900); (0xb2bb8, 0xb2c30); (0xb53b8, 0xb53c8); (0xb6098, 0xb609a); (0xb60a0, 0xb60b8); (0x146ee8, 0x147008); (0x5e8380, 0x5e8388); (0x5e83d0, 0x5e83d8); (0x5e83d8, 0x5e83e0); (0x5e83e0, 0x5e83e8); (0x5e83e8, 0x5e83ec); (0x5e8400, 0x5e8408); (0x608698, 0x6086a0); (0x609780, 0x609788)].
Definition in_ivs (ivs : list (Z * Z)) (lo hi : Z) : bool := existsb (fun lh => (fst lh <=? lo) && (hi <=? snd lh)) ivs.
Lemma paS_ivs_sound : forall lo hi a, in_ivs paS_ivs lo hi = true -> lo <= a < hi -> pa_static a.
Proof.
  intros lo hi a H Ha. unfold in_ivs in H. apply existsb_exists in H as ([l h] & Hin & B). cbn [fst snd] in B.
  apply andb_true_iff in B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. unfold pa_static. cbn in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]; injection E as <- <-; lia.
Qed.
Lemma paH_ivs_sound : forall lo hi a, in_ivs paH_ivs lo hi = true -> lo <= a < hi -> pa_shared a.
Proof.
  intros lo hi a H Ha. unfold in_ivs in H. apply existsb_exists in H as ([l h] & Hin & B). cbn [fst snd] in B.
  apply andb_true_iff in B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. unfold pa_shared. cbn in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]]]]]; injection E as <- <-; lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pa_const_placed (c : Z * list byte) : bool :=
  let lo := fst c in let hi := lo + Z.of_nat (length (snd c)) in
  in_ivs paH_ivs lo hi || ((sh 0x10000 <=? lo) && (hi <=? sh 0x60a000)) || in_ivs paS_ivs lo hi.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pa_cell_rom_ok (c : Z * list byte) : bool :=
  if ((fst c <? 0xb1d00) && negb (fst c =? GMETA))%bool then rom_eqb rsegs (fst c) (snd c) else true.
(* [comment removed for export] *)

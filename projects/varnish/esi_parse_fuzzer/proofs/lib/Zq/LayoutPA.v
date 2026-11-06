(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Cells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AGlofzw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pa_smalloc (k : Z) : Z :=
  match k with
  | 0 => 0x426ec | 1 => 0x42860 | 7 => 0x429f0 | _ => 0
  end.
Definition pa_smalloc_always (k : Z) : Z :=
  0.  (* [comment removed for export] *)
Definition pa_sfree (k : Z) : Z :=
  match k with
  | 7 => 0x42b6c | _ => 0
  end.

(* [comment removed for export] *)
Definition pa_sites : list Z :=
  [ (* [comment removed for export] *)
    0x8684c; 0x868a0; 0x868c4; 0x869f4;
    (* [comment removed for export] *)
    0x86b2c; 0x86bc0;
    (* [comment removed for export] *)
    0x88918; 0x88984;
    (* [comment removed for export] *)
    0x8856c; 0x88354;
    (* [comment removed for export] *)
    0x89748;
    (* [comment removed for export] *)
    0x89864; 0x898b8;
    (* [comment removed for export] *)
    0x8a050; 0x8a070;
    (* [comment removed for export] *)
    0x8afa0; 0x8afc0 ].

(* [comment removed for export] *)
Definition pa_static (a : Z) : Prop :=
     (0xaaa70 <= a < 0xad120)     (* [comment removed for export] *)
  \/ (0xad600 <= a < 0xb1500)     (* [comment removed for export] *)
  \/ (0xb1500 <= a < 0xb1558)     (* [comment removed for export] *)
  \/ (0xb1558 <= a < 0xb23b8)     (* [comment removed for export] *)
  \/ (0xb2430 <= a < 0xb4bb8)     (* [comment removed for export] *)
  \/ (0xb4bc8 <= a < 0xb5898)     (* [comment removed for export] *)
  \/ (0xb589a <= a < 0xb58a0)     (* [comment removed for export] *)
  \/ (0xb58b8 <= a < 0x1466e8)     (* [comment removed for export] *)
  \/ (0x146808 <= a < 0x5d7210).    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition pa_shared (a : Z) : Prop :=
     (0xa8000 <= a < 0xaa000)     (* [comment removed for export] *)
  \/ (0xaa8a0 <= a < 0xaa8a8)     (* [comment removed for export] *)
  \/ (0xaa8a8 <= a < 0xaaa70)     (* [comment removed for export] *)
  \/ (0xad140 <= a < 0xad2e0)     (* [comment removed for export] *)
  \/ (0xb23b8 <= a < 0xb2430)     (* [comment removed for export] *)
  \/ (0xb4bb8 <= a < 0xb4bc8)     (* [comment removed for export] *)
  \/ (0xb5898 <= a < 0xb589a)     (* [comment removed for export] *)
  \/ (0xb58a0 <= a < 0xb58b8)     (* [comment removed for export] *)
  \/ (0x1466e8 <= a < 0x146808)     (* [comment removed for export] *)
  \/ (0x5e7b80 <= a < 0x5e7b88)     (* [comment removed for export] *)
  \/ (0x5e7bd0 <= a < 0x5e7bd8)     (* [comment removed for export] *)
  \/ (0x5e7bd8 <= a < 0x5e7be0)     (* [comment removed for export] *)
  \/ (0x5e7be0 <= a < 0x5e7be8)     (* [comment removed for export] *)
  \/ (0x5e7be8 <= a < 0x5e7bec)     (* [comment removed for export] *)
  \/ (0x5e7c00 <= a < 0x5e7c08)     (* [comment removed for export] *)
  \/ (0x607e98 <= a < 0x607ea0)     (* [comment removed for export] *)
  \/ (0x608f80 <= a < 0x608f88).    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition pa_gdescs : list (Z * Z * Z) :=
  [
    (0x21700, 23, 64); (0x217a0, 12, 32); (0x217c0, 4, 32); (0x217e0, 2, 32);
    (0x21800, 11, 32); (0x21820, 10, 32); (0x21860, 13, 32); (0x21880, 26, 64);
    (0x218c0, 14, 32); (0x218e0, 12, 32); (0x21900, 14, 32); (0x21920, 12, 32);
    (0x21940, 15, 32); (0x21960, 26, 64); (0x219a0, 15, 32); (0x219c0, 15, 32);
    (0x219e0, 15, 32); (0x21a00, 30, 64); (0x21a40, 15, 32); (0x21a60, 15, 32);
    (0x21a80, 15, 32); (0x21aa0, 17, 64); (0x21ae0, 25, 64); (0x21b20, 13, 32);
    (0x21b40, 13, 32); (0x21b60, 30, 64); (0x21ba0, 26, 64); (0x21be0, 8, 32);
    (0x21c00, 14, 32); (0x21c20, 12, 32); (0x21c40, 18, 64); (0x21c80, 13, 32);
    (0x21ca0, 35, 96); (0x21d00, 9, 32); (0x21d20, 10, 32); (0x21d40, 25, 64);
    (0x21d80, 25, 64); (0x21dc0, 17, 64); (0x21e00, 11, 32); (0x21e20, 9, 32);
    (0x21e40, 9, 32); (0x21e60, 10, 32); (0x21e80, 15, 32); (0x21ea0, 22, 64);
    (0x21ee0, 10, 32); (0x21f00, 7, 32); (0x21f20, 12, 32); (0x21f40, 30, 64);
    (0x21f80, 6, 32); (0x21fa0, 9, 32); (0x21fc0, 7, 32); (0x21fe0, 14, 32);
    (0x22000, 15, 32); (0x22020, 30, 64); (0x22060, 13, 32); (0x220a0, 76, 128);
    (0x22120, 38, 96); (0x22180, 36, 96); (0x221e0, 61, 96); (0x22240, 19, 64);
    (0x22280, 35, 96); (0x222e0, 12, 32); (0x22300, 44, 96); (0x22360, 3, 32);
    (0x22380, 12, 32); (0x223a0, 54, 96); (0x22400, 54, 96); (0x22460, 1, 32);
    (0x22480, 9, 32); (0x224a0, 2, 32); (0x224c0, 11, 32); (0x224e0, 13, 32);
    (0x22500, 10, 32); (0x22540, 9, 32); (0x22580, 9, 32); (0x225a0, 11, 32);
    (0x225c0, 12, 32); (0x225e0, 9, 32); (0x22600, 9, 32); (0x22620, 8, 32);
    (0x22640, 18, 64); (0x22680, 12, 32); (0x226a0, 18, 64); (0x226e0, 21, 64);
    (0x22720, 12, 32); (0x22740, 18, 64); (0x22780, 20, 64); (0x227c0, 11, 32);
    (0x227e0, 14, 32); (0x22800, 15, 32); (0x22820, 16, 32); (0x22840, 22, 64);
    (0x22880, 16, 32); (0x228a0, 23, 64); (0x228e0, 23, 64); (0x22920, 18, 64);
    (0x22960, 35, 96); (0x229e0, 16, 32); (0x22a00, 13, 32); (0x22a20, 26, 64);
    (0x22a60, 14, 32); (0x22a80, 17, 64); (0x22ac0, 17, 64); (0x22b00, 10, 32);
    (0x22b40, 14, 32); (0x22b60, 27, 64); (0x22ba0, 6, 32); (0x22bc0, 1, 32);
    (0x22be0, 19, 64); (0x22c20, 18, 64); (0x22c60, 16, 32); (0x22c80, 8, 32);
    (0x22ca0, 8, 32); (0x22cc0, 6, 32); (0x22ce0, 9, 32); (0x22d00, 10, 32);
    (0x22d20, 11, 32); (0x22d40, 82, 128); (0x22dc0, 9, 32); (0x22de0, 81, 128);
    (0x22e60, 11, 32); (0x22e80, 10, 32); (0x22ea0, 10, 32); (0x22ec0, 4, 32);
    (0x22ee0, 8, 32); (0x22f00, 13, 32); (0x22f20, 47, 96); (0x22f80, 8, 32);
    (0x22fa0, 4, 32); (0x22fc0, 10, 32); (0x22fe0, 9, 32); (0x23000, 14, 32);
    (0x23020, 53, 96); (0x23080, 11, 32); (0x230a0, 39, 96); (0x23100, 8, 32);
    (0x23120, 13, 32); (0x23140, 14, 32); (0x23160, 53, 96); (0x231c0, 39, 96);
    (0x23220, 12, 32); (0x23240, 28, 64); (0x23280, 20, 64); (0x232c0, 39, 96);
    (0x23320, 12, 32); (0x23340, 37, 96); (0x233a0, 23, 64); (0x233e0, 21, 64);
    (0x23420, 16, 32); (0x23440, 12, 32); (0x23460, 26, 64); (0x234a0, 15, 32);
    (0x234c0, 12, 32); (0x234e0, 36, 96); (0x23540, 40, 96); (0x235a0, 33, 96);
    (0x23600, 26, 64); (0x23640, 11, 32); (0x23660, 18, 64); (0x236a0, 7, 32);
    (0x236c0, 23, 64); (0x23700, 9, 32); (0x23720, 13, 32); (0x23740, 26, 64);
    (0x23780, 14, 32); (0x237a0, 27, 64); (0x237e0, 30, 64); (0x23820, 16, 32);
    (0x23840, 3, 32); (0x23860, 11, 32); (0x23880, 23, 64); (0x238c0, 28, 64);
    (0x23900, 16, 32); (0x23920, 33, 96); (0x23980, 18, 64); (0x239c0, 7, 32);
    (0x239e0, 4, 32); (0x23a00, 7, 32); (0x23a20, 7, 32); (0x23a40, 4, 32);
    (0x23a60, 6, 32); (0x23a80, 5, 32); (0x23aa0, 9, 32); (0x23ac0, 18, 64);
    (0x23b00, 8, 32); (0x23b20, 7, 32); (0x23b40, 8, 32); (0x23b60, 5, 32);
    (0x23b80, 9, 32); (0x23ba0, 15, 32); (0x23bc0, 34, 96); (0x23c20, 15, 32);
    (0x23c40, 38, 96); (0x23ca0, 37, 96); (0x23d00, 43, 96); (0x23d60, 8, 32);
    (0x23d80, 39, 96); (0x23de0, 13, 32); (0x23e00, 9, 32); (0x23e20, 44, 96);
    (0x23e80, 50, 96); (0x23ee0, 6, 32); (0x23f00, 7, 32); (0x23f20, 7, 32);
    (0x23f40, 5, 32); (0x23f60, 5, 32); (0x23f80, 6, 32); (0x23fa0, 51, 96);
    (0x24000, 55, 96); (0x24060, 9, 32); (0x24080, 19, 64); (0x240c0, 14, 32);
    (0x240e0, 32, 64); (0x24120, 34, 96); (0x24180, 30, 64); (0x241c0, 15, 32);
    (0x241e0, 38, 96); (0x24240, 10, 32); (0x24260, 40, 96); (0x242c0, 17, 64);
    (0x24300, 15, 32); (0x24320, 12, 32); (0x24340, 16, 32); (0x24360, 13, 32);
    (0x24380, 32, 64); (0x243c0, 512, 640); (0x24660, 1024, 1280); (0x24b60, 4096, 5120);
    (0x25f60, 128, 160); (0xa87e0, 8, 32); (0xa8800, 8, 32); (0xa8820, 8, 32);
    (0xa8840, 8, 32); (0xa8860, 8, 32); (0xa8880, 8, 32); (0xa88a0, 8, 32);
    (0xa88c0, 8, 32); (0xa88e0, 8, 32); (0xa8900, 8, 32); (0xa8920, 8, 32);
    (0xa8940, 8, 32); (0xa8960, 8, 32); (0xa8980, 8, 32); (0xa89a0, 8, 32);
    (0xa89c0, 8, 32); (0xad140, 32, 64); (0xad180, 112, 160); (0xad220, 64, 96);
    (0xad280, 48, 96); (0x5e7240, 8, 32); (0x5e7260, 8, 32); (0x5e72a0, 8, 32) ].

(* [comment removed for export] *)
Definition pa_asan_flags_bytes : list byte := [Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 190; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 85; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 182; Z_to_bv 8 64; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Definition pa_common_flags_bytes : list byte := [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 182; Z_to_bv 8 64; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 30; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 199; Z_to_bv 8 24; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 68; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 182; Z_to_bv 8 64; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 182; Z_to_bv 8 64; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 46; Z_to_bv 8 226; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 140; Z_to_bv 8 144; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0].

(* [comment removed for export] *)
Definition gshadow_entry (d : Z * Z * Z) : Z * list byte :=
  match d with (b, s, r) => (sh b, shpat s ++ repeat (Z_to_bv 8 0xf9) (Z.to_nat ((r - (s + 7) / 8 * 8) / 8))) end.
Definition pa_gshadow : list (Z * list byte) := map gshadow_entry pa_gdescs.

(* [comment removed for export] *)
Definition pa_cells : list (Z * list byte) :=
  [ (0xa8b70, le8 (Z_to_bv 64 0xb4bb8));   (* [comment removed for export] *)
    (0xb4bb8, le8 (Z_to_bv 64 kShadowOffset));   (* [comment removed for export] *)
    (0xa8bc8, le8 (Z_to_bv 64 0xb4bc0));   (* [comment removed for export] *)
    (0xb4bc0, le4 (Z_to_bv 64 1));          (* [comment removed for export] *)
    (0xa8b90, le8 (Z_to_bv 64 0xaaa18));   (* [comment removed for export] *)
    (0xaaa18, le8 (Z_to_bv 64 0xa1f90));   (* [comment removed for export] *)
    (0xa8b98, le8 (Z_to_bv 64 0xaaa10));   (* [comment removed for export] *)
    (0xaaa10, le8 (Z_to_bv 64 0xa1b8c));   (* [comment removed for export] *)
    (0xa96e0, le8 (Z_to_bv 64 0xb5899));   (* [comment removed for export] *)
    (0xb5898, [Z_to_bv 8 1]);               (* [comment removed for export] *)
    (0xb5899, [Z_to_bv 8 1]);               (* [comment removed for export] *)
    (0xa96d8, le8 (Z_to_bv 64 0x574f4));    (* [comment removed for export] *)
    (0xa97d8, le8 (Z_to_bv 64 0xa8a68));   (* [comment removed for export] *)
    (0xa97e0, le8 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xa97f0, le8 (Z_to_bv 64 0x243c0));    (* [comment removed for export] *)
    (0xa97f8, le8 (Z_to_bv 64 0x5e7240));   (* [comment removed for export] *)
    (0xa9800, le8 (Z_to_bv 64 0x5e7260));   (* [comment removed for export] *)
    (0xa9818, le8 (Z_to_bv 64 0x607c18));   (* [comment removed for export] *)
    (0xa9870, le8 (Z_to_bv 64 1) ++ le8 (Z_to_bv 64 (-0x800)));  (* [comment removed for export] *)
    (0xa9880, le8 (Z_to_bv 64 0x8));        (* [comment removed for export] *)
    (0xa97d0, le8 (Z_to_bv 64 0x10));       (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xb58a0, le8 (Z_to_bv 64 0x7fffffffffff)); (* [comment removed for export] *)
    (0xb58a8, le8 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xb58b0, le8 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xa8b78, le8 (Z_to_bv 64 0xb58a8));   (* [comment removed for export] *)
    (0xa8b80, le8 (Z_to_bv 64 0xb58b0));   (* [comment removed for export] *)
    (0xa8b88, le8 (Z_to_bv 64 0xb58a0));   (* [comment removed for export] *)
    (0xa8b60, le8 (Z_to_bv 64 0x1466e8));   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xa8b58, le8 (Z_to_bv 64 0xaaa50));   (* [comment removed for export] *)
    (0xaaa50, le8 (Z_to_bv 64 0x1981a));    (* [comment removed for export] *)
    (0xa8bb0, le8 (Z_to_bv 64 1));          (* [comment removed for export] *)
    (0xa8bb8, le8 (Z_to_bv 64 0x1466dc));   (* [comment removed for export] *)
    (0x1466dc, le4 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0x607e98, le8 (Z_to_bv 64 4096));       (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xb1801, [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);   (* [comment removed for export] *)
    (0xb18ca, [Z_to_bv 8 0; Z_to_bv 8 0]);               (* [comment removed for export] *)
    (0xb1931, [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]);   (* [comment removed for export] *)
    (0x14464a, [Z_to_bv 8 0; Z_to_bv 8 0]);               (* [comment removed for export] *)
    (0xa8b68, le8 (Z_to_bv 64 0xb23b8));   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xaa8a8, le8 (Z_to_bv 64 0xa22c4));   (* [comment removed for export] *)
    (0xaa8b8, le8 (Z_to_bv 64 0xa2088));   (* [comment removed for export] *)
    (0xaa8c0, le8 (Z_to_bv 64 0xa1b5c));   (* [comment removed for export] *)
    (0xaa8c8, le8 (Z_to_bv 64 0xa1a8c));   (* [comment removed for export] *)
    (0xaa9b8, le8 (Z_to_bv 64 0xa21dc));   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xaa8e0, le8 (Z_to_bv 64 0xa7378));   (* [comment removed for export] *)
    (0xaa8e8, le8 (Z_to_bv 64 0x9e140));   (* [comment removed for export] *)
    (0xaa900, le8 (Z_to_bv 64 0xa14d8));   (* [comment removed for export] *)
    (0xaa908, le8 (Z_to_bv 64 0x9e3c8));   (* [comment removed for export] *)
    (0xaa910, le8 (Z_to_bv 64 0xa14f4));   (* [comment removed for export] *)
    (0xaa9c0, le8 (Z_to_bv 64 0xa2500));   (* [comment removed for export] *)
    (0xaa8d0, le8 (Z_to_bv 64 0xa1a90));   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xb4420, [Z_to_bv 8 1]);               (* [comment removed for export] *)
    (0xb4424, le4 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xb441c, [Z_to_bv 8 1]);               (* [comment removed for export] *)
    (0x146a60, [Z_to_bv 8 0]);               (* [comment removed for export] *)
    (0xb1500, le8 (Z_to_bv 64 1));          (* [comment removed for export] *)
    (0xb1550, [Z_to_bv 8 0]);               (* [comment removed for export] *)
    (0xb2470, le8 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xa9848, le8 (Z_to_bv 64 0xa83e0) ++ le8 (Z_to_bv 64 0xa83d0));  (* [comment removed for export] *)
    (0xa83d0, le8 (Z_to_bv 64 0x87644) ++ le8 (Z_to_bv 64 0x35ef4));    (* [comment removed for export] *)
    (0xa8b40, le8 (Z_to_bv 64 0x98258) ++ le8 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xaa8a0, le8 (Z_to_bv 64 0xaa8a0));   (* [comment removed for export] *)
    (0xa9808, le8 (Z_to_bv 64 GMETA) ++ le8 (Z_to_bv 64 (GMETA + 64 * 252)));  (* [comment removed for export] *)
    (0xa8b50, le8 (Z_to_bv 64 0x144660));   (* [comment removed for export] *)
    (0x144660, le8 (Z_to_bv 64 4096));       (* [comment removed for export] *)
    (GMETA, cells_bytes (gtab_cells gtab));  (* [comment removed for export] *)
    (0x8000dac0, repeat (Z_to_bv 8 0xf9) 2016); (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xa8800, le8 (Z_to_bv 64 0x22c80));
    (0xa8820, le8 (Z_to_bv 64 0x22cc0));
    (0xa8840, le8 (Z_to_bv 64 0x22f00));
    (0xa8860, le8 (Z_to_bv 64 0x22ce0));
    (0xa8880, le8 (Z_to_bv 64 0x22ea0));
    (0xa88a0, le8 (Z_to_bv 64 0x22fc0));
    (0xa88c0, le8 (Z_to_bv 64 0x22fe0));
    (0xa88e0, le8 (Z_to_bv 64 0x22f80));
    (0xa8900, le8 (Z_to_bv 64 0x22e60));
    (0xa8920, le8 (Z_to_bv 64 0x23000));
    (0xa8940, le8 (Z_to_bv 64 0x23120));
    (0xa8960, le8 (Z_to_bv 64 0x23140));
    (0xa8980, le8 (Z_to_bv 64 0x23220));
    (0xa89a0, le8 (Z_to_bv 64 0x234a0));
    (0xa89c0, le8 (Z_to_bv 64 0x23420));
    (0xad140, le8 (Z_to_bv 64 0x239e0) ++ le8 (Z_to_bv 64 0xa8800) ++ le8 (Z_to_bv 64 0x0) ++ le8 (Z_to_bv 64 0xa8820));
    (0xad180, le8 (Z_to_bv 64 0x23a00) ++ le8 (Z_to_bv 64 0xa8840) ++ le8 (Z_to_bv 64 0x23a20) ++ le8 (Z_to_bv 64 0xa8860) ++ le8 (Z_to_bv 64 0x23a40) ++ le8 (Z_to_bv 64 0xa8880) ++ le8 (Z_to_bv 64 0x23a60) ++ le8 (Z_to_bv 64 0xa88a0) ++ le8 (Z_to_bv 64 0x23a80) ++ le8 (Z_to_bv 64 0xa88c0) ++ le8 (Z_to_bv 64 0x23aa0) ++ le8 (Z_to_bv 64 0xa88e0) ++ le8 (Z_to_bv 64 0x0) ++ le8 (Z_to_bv 64 0xa8900));
    (0xad220, le8 (Z_to_bv 64 0x23b00) ++ le8 (Z_to_bv 64 0xa8920) ++ le8 (Z_to_bv 64 0x23b20) ++ le8 (Z_to_bv 64 0xa8940) ++ le8 (Z_to_bv 64 0x23b40) ++ le8 (Z_to_bv 64 0xa8960) ++ le8 (Z_to_bv 64 0x0) ++ le8 (Z_to_bv 64 0xa8980));
    (0xad280, le8 (Z_to_bv 64 0x23b60) ++ le8 (Z_to_bv 64 0xa89a0) ++ le8 (Z_to_bv 64 0x23b80) ++ le8 (Z_to_bv 64 0xa89a0) ++ le8 (Z_to_bv 64 0x0) ++ le8 (Z_to_bv 64 0xa89c0));
    (0x5e7b80, le8 (Z_to_bv 64 0x608f80));   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (0xaa948, le8 (Z_to_bv 64 0xa2868));   (* [comment removed for export] *)
    (0xa9870, le8 (Z_to_bv 64 1) ++ le8 (Z_to_bv 64 0xfffffffffffff800));  (* [comment removed for export] *)
    (0xa8bc0, le8 (Z_to_bv 64 0x144658));   (* [comment removed for export] *)
    (0x144658, le4 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xa9880, le8 (Z_to_bv 64 8));          (* [comment removed for export] *)
    (0x146771, [Z_to_bv 8 1]);               (* [comment removed for export] *)
    (0x5e7bd0, le8 (Z_to_bv 64 0x5e7bf8));   (* [comment removed for export] *)
    (0x5e7c00, le8 (Z_to_bv 64 0x5e83d8));   (* [comment removed for export] *)
    (0x5e7be8, le4 (Z_to_bv 64 0));          (* [comment removed for export] *)
    (0xb23b8, pa_asan_flags_bytes);         (* [comment removed for export] *)
    (0x1466e8, pa_common_flags_bytes) ].     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition pa_zero_shadow : list (Z * nat) :=
  [ (0x7fffa000, 8930%nat);
    (0x7fffc2e8, 13%nat);
    (0x7fffc300, 1%nat);
    (0x7fffc304, 1%nat);
    (0x7fffc308, 5%nat);
    (0x7fffc310, 3%nat);
    (0x7fffc318, 1%nat);
    (0x7fffc31c, 1%nat);
    (0x7fffc320, 1%nat);
    (0x7fffc324, 1%nat);
    (0x7fffc328, 1%nat);
    (0x7fffc32c, 3%nat);
    (0x7fffc334, 1%nat);
    (0x7fffc338, 1%nat);
    (0x7fffc33c, 1%nat);
    (0x7fffc340, 3%nat);
    (0x7fffc348, 1%nat);
    (0x7fffc34c, 1%nat);
    (0x7fffc350, 1%nat);
    (0x7fffc354, 2%nat);
    (0x7fffc35c, 3%nat);
    (0x7fffc364, 1%nat);
    (0x7fffc368, 1%nat);
    (0x7fffc36c, 3%nat);
    (0x7fffc374, 3%nat);
    (0x7fffc37c, 1%nat);
    (0x7fffc380, 1%nat);
    (0x7fffc384, 1%nat);
    (0x7fffc388, 2%nat);
    (0x7fffc390, 1%nat);
    (0x7fffc394, 4%nat);
    (0x7fffc3a0, 1%nat);
    (0x7fffc3a4, 1%nat);
    (0x7fffc3a8, 3%nat);
    (0x7fffc3b0, 3%nat);
    (0x7fffc3b8, 2%nat);
    (0x7fffc3c0, 1%nat);
    (0x7fffc3c4, 1%nat);
    (0x7fffc3c8, 1%nat);
    (0x7fffc3cc, 1%nat);
    (0x7fffc3d0, 1%nat);
    (0x7fffc3d4, 2%nat);
    (0x7fffc3dc, 1%nat);
    (0x7fffc3e4, 1%nat);
    (0x7fffc3e8, 3%nat);
    (0x7fffc3f4, 1%nat);
    (0x7fffc3fc, 1%nat);
    (0x7fffc400, 1%nat);
    (0x7fffc404, 3%nat);
    (0x7fffc40c, 1%nat);
    (0x7fffc410, 13%nat);
    (0x7fffc424, 4%nat);
    (0x7fffc430, 4%nat);
    (0x7fffc43c, 7%nat);
    (0x7fffc448, 2%nat);
    (0x7fffc450, 4%nat);
    (0x7fffc45c, 1%nat);
    (0x7fffc460, 5%nat);
    (0x7fffc470, 1%nat);
    (0x7fffc474, 6%nat);
    (0x7fffc480, 6%nat);
    (0x7fffc490, 1%nat);
    (0x7fffc498, 1%nat);
    (0x7fffc49c, 1%nat);
    (0x7fffc4a0, 1%nat);
    (0x7fffc4a4, 5%nat);
    (0x7fffc4ac, 5%nat);
    (0x7fffc4b4, 1%nat);
    (0x7fffc4b8, 1%nat);
    (0x7fffc4bc, 1%nat);
    (0x7fffc4c0, 1%nat);
    (0x7fffc4c4, 1%nat);
    (0x7fffc4c8, 2%nat);
    (0x7fffc4d0, 1%nat);
    (0x7fffc4d4, 2%nat);
    (0x7fffc4dc, 2%nat);
    (0x7fffc4e4, 1%nat);
    (0x7fffc4e8, 2%nat);
    (0x7fffc4f0, 2%nat);
    (0x7fffc4f8, 1%nat);
    (0x7fffc4fc, 1%nat);
    (0x7fffc500, 1%nat);
    (0x7fffc504, 2%nat);
    (0x7fffc508, 2%nat);
    (0x7fffc510, 2%nat);
    (0x7fffc514, 2%nat);
    (0x7fffc51c, 2%nat);
    (0x7fffc524, 2%nat);
    (0x7fffc52c, 4%nat);
    (0x7fffc538, 6%nat);
    (0x7fffc540, 1%nat);
    (0x7fffc544, 3%nat);
    (0x7fffc54c, 1%nat);
    (0x7fffc550, 2%nat);
    (0x7fffc558, 2%nat);
    (0x7fffc560, 1%nat);
    (0x7fffc564, 5%nat);
    (0x7fffc56c, 3%nat);
    (0x7fffc57c, 2%nat);
    (0x7fffc584, 2%nat);
    (0x7fffc58c, 2%nat);
    (0x7fffc590, 1%nat);
    (0x7fffc594, 1%nat);
    (0x7fffc59c, 1%nat);
    (0x7fffc5a0, 1%nat);
    (0x7fffc5a4, 1%nat);
    (0x7fffc5a8, 10%nat);
    (0x7fffc5b8, 1%nat);
    (0x7fffc5bc, 10%nat);
    (0x7fffc5cc, 1%nat);
    (0x7fffc5d0, 1%nat);
    (0x7fffc5d4, 1%nat);
    (0x7fffc5dc, 1%nat);
    (0x7fffc5e0, 1%nat);
    (0x7fffc5e4, 5%nat);
    (0x7fffc5f0, 1%nat);
    (0x7fffc5f8, 1%nat);
    (0x7fffc5fc, 1%nat);
    (0x7fffc600, 1%nat);
    (0x7fffc604, 6%nat);
    (0x7fffc610, 1%nat);
    (0x7fffc614, 4%nat);
    (0x7fffc620, 1%nat);
    (0x7fffc624, 1%nat);
    (0x7fffc628, 1%nat);
    (0x7fffc62c, 6%nat);
    (0x7fffc638, 4%nat);
    (0x7fffc644, 1%nat);
    (0x7fffc648, 3%nat);
    (0x7fffc650, 2%nat);
    (0x7fffc658, 4%nat);
    (0x7fffc664, 1%nat);
    (0x7fffc668, 4%nat);
    (0x7fffc674, 2%nat);
    (0x7fffc67c, 2%nat);
    (0x7fffc684, 2%nat);
    (0x7fffc688, 1%nat);
    (0x7fffc68c, 3%nat);
    (0x7fffc694, 1%nat);
    (0x7fffc698, 1%nat);
    (0x7fffc69c, 4%nat);
    (0x7fffc6a8, 5%nat);
    (0x7fffc6b4, 4%nat);
    (0x7fffc6c0, 3%nat);
    (0x7fffc6c8, 1%nat);
    (0x7fffc6cc, 2%nat);
    (0x7fffc6d8, 2%nat);
    (0x7fffc6e0, 1%nat);
    (0x7fffc6e4, 1%nat);
    (0x7fffc6e8, 3%nat);
    (0x7fffc6f0, 1%nat);
    (0x7fffc6f4, 3%nat);
    (0x7fffc6fc, 3%nat);
    (0x7fffc704, 2%nat);
    (0x7fffc70c, 1%nat);
    (0x7fffc710, 2%nat);
    (0x7fffc718, 3%nat);
    (0x7fffc720, 2%nat);
    (0x7fffc724, 4%nat);
    (0x7fffc730, 2%nat);
    (0x7fffc754, 1%nat);
    (0x7fffc758, 2%nat);
    (0x7fffc760, 1%nat);
    (0x7fffc768, 1%nat);
    (0x7fffc770, 1%nat);
    (0x7fffc774, 1%nat);
    (0x7fffc778, 4%nat);
    (0x7fffc784, 1%nat);
    (0x7fffc788, 4%nat);
    (0x7fffc794, 4%nat);
    (0x7fffc7a0, 5%nat);
    (0x7fffc7ac, 1%nat);
    (0x7fffc7b0, 4%nat);
    (0x7fffc7bc, 1%nat);
    (0x7fffc7c0, 1%nat);
    (0x7fffc7c4, 5%nat);
    (0x7fffc7d0, 6%nat);
    (0x7fffc7f4, 6%nat);
    (0x7fffc800, 6%nat);
    (0x7fffc80c, 1%nat);
    (0x7fffc810, 2%nat);
    (0x7fffc818, 1%nat);
    (0x7fffc81c, 4%nat);
    (0x7fffc824, 4%nat);
    (0x7fffc830, 3%nat);
    (0x7fffc838, 1%nat);
    (0x7fffc83c, 4%nat);
    (0x7fffc848, 1%nat);
    (0x7fffc84c, 5%nat);
    (0x7fffc858, 2%nat);
    (0x7fffc860, 1%nat);
    (0x7fffc864, 1%nat);
    (0x7fffc868, 2%nat);
    (0x7fffc86c, 1%nat);
    (0x7fffc870, 4%nat);
    (0x7fffc878, 64%nat);
    (0x7fffc8c8, 132%nat);
    (0x7fffc96c, 512%nat);
    (0x7fffcbec, 16%nat);
    (0x7fffcc00, 66813%nat);
    (0x8000d100, 1%nat);
    (0x8000d104, 1%nat);
    (0x8000d108, 1%nat);
    (0x8000d10c, 1%nat);
    (0x8000d110, 1%nat);
    (0x8000d114, 1%nat);
    (0x8000d118, 1%nat);
    (0x8000d11c, 1%nat);
    (0x8000d120, 1%nat);
    (0x8000d124, 1%nat);
    (0x8000d128, 1%nat);
    (0x8000d12c, 1%nat);
    (0x8000d130, 1%nat);
    (0x8000d134, 1%nat);
    (0x8000d138, 1%nat);
    (0x8000d13c, 2288%nat);
    (0x8000da30, 14%nat);
    (0x8000da44, 8%nat);
    (0x8000da50, 6%nat);
    (0x8000da5c, 100%nat);
    (0x8000e2a0, 682921%nat);
    (0x800b4e4c, 1%nat);
    (0x800b4e50, 5%nat);
    (0x800b4e58, 17832%nat) ].
Definition pa_zshadow : list (Z * list byte) := map (fun p => (fst p, repeat (Z_to_bv 8 0) (snd p))) pa_zero_shadow.
Definition pa_consts : list (Z * list byte) := pa_cells ++ pa_gshadow ++ pa_zshadow.

Definition LPA : clayout := {|
  cl_segs := rsegs;
  cl_malloc_pc := Z_to_bv 64 0x58850;
  cl_free_pc := Z_to_bv 64 0x5884c;
  cl_calloc_pc := Z_to_bv 64 0x58854;
  cl_realloc_pc := Z_to_bv 64 0x58858;
  cl_smalloc_pc := fun k => Z_to_bv 64 (pa_smalloc k);
  cl_sfree_pc := fun k => Z_to_bv 64 (pa_sfree k);
  cl_tp := Z_to_bv 64 0x5e7bd8;
  cl_errno := 0x5e7b34;                      (* [comment removed for export] *)
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
  Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_000) = 0x10000 /\
  Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_000) = 0x25000 /\
  Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_001) = 0x35000 /\
  Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_001) = 0x73000 /\
  Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_002) = 0xa8000 /\
  Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_002) = 0x2000 /\
  Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_003) = 0xaa000 /\
  Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_003) = 0x560000.
Proof. repeat split; vm_compute; reflexivity. Qed.

Ltac pa_unfold_segs :=
  unfold rsegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments;
  cbn [find_segment];
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_000)) with 0x25000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_001)) with 0x35000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_001)) with 0x73000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_002)) with 0xa8000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_002)) with 0x2000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_003)) with 0xaa000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_003)) with 0x560000%Z by (vm_compute; reflexivity).

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
    [replace (seg_writable AsanUbsan.AsanUbsan_segment_000) with false by (vm_compute; reflexivity); cbn; split; intros; [lia|reflexivity] | | |].
  all: destruct (Z.leb_spec0 0x35000 z); destruct (Z.leb_spec0 (z + 1) (0x35000 + 0x73000)); cbn [andb]; try lia;
    try (replace (seg_writable AsanUbsan.AsanUbsan_segment_001) with false by (vm_compute; reflexivity); cbn; split; intros; [lia|reflexivity]).
  all: destruct (Z.leb_spec0 0xa8000 z); destruct (Z.leb_spec0 (z + 1) (0xa8000 + 0x2000)); cbn [andb]; try lia;
    try (replace (seg_writable AsanUbsan.AsanUbsan_segment_002) with true by (vm_compute; reflexivity); cbn; split; intros; [discriminate|lia]).
  all: destruct (Z.leb_spec0 0xaa000 z); destruct (Z.leb_spec0 (z + 1) (0xaa000 + 0x560000)); cbn [andb]; try lia;
    try (replace (seg_writable AsanUbsan.AsanUbsan_segment_003) with true by (vm_compute; reflexivity); cbn; split; intros; [discriminate|lia]).
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
Lemma pa_sites_ex : In 0x8a070 (cl_sites LPA). Proof. cbn. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pa_site_pcs : list Z := [0x58af4; 0x58994; 0x58d28; 0x58fc8].
Definition pa_start_keys : list (list Z) := [[0x44500; 0x45850]; [0x44500]].
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
Lemma pa_dkeys_start2 : In [0x44500; 0x45850] pa_dkeys. Proof. cbn. tauto. Qed.
Lemma pa_dkeys_start1 : In [0x44500] pa_dkeys. Proof. cbn. tauto. Qed.
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
  [(0xaaa70, 0xad120); (0xad600, 0xb1500); (0xb1500, 0xb1558); (0xb1558, 0xb23b8); (0xb2430, 0xb4bb8); (0xb4bc8, 0xb5898); (0xb589a, 0xb58a0); (0xb58b8, 0x1466e8); (0x146808, 0x5d7210)].
Definition paH_ivs : list (Z * Z) :=
  [(0xa8000, 0xaa000); (0xaa8a0, 0xaa8a8); (0xaa8a8, 0xaaa70); (0xad140, 0xad2e0); (0xb23b8, 0xb2430); (0xb4bb8, 0xb4bc8); (0xb5898, 0xb589a); (0xb58a0, 0xb58b8); (0x1466e8, 0x146808); (0x5e7b80, 0x5e7b88); (0x5e7bd0, 0x5e7bd8); (0x5e7bd8, 0x5e7be0); (0x5e7be0, 0x5e7be8); (0x5e7be8, 0x5e7bec); (0x5e7c00, 0x5e7c08); (0x607e98, 0x607ea0); (0x608f80, 0x608f88)].
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
  if ((fst c <? 0xb1500) && negb (fst c =? GMETA))%bool then rom_eqb rsegs (fst c) (snd c) else true.
(* [comment removed for export] *)

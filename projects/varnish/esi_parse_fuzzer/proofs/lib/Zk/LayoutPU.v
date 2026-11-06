(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition pu_static (a : Z) : Prop := 0x627f8 <= a < 0x62ba4.

(* [comment removed for export] *)
Definition pu_shared (a : Z) : Prop :=
  a = 0x6278b \/ (0x627b8 <= a < 0x627c0) \/ (0x62768 <= a < 0x62770) \/ (0x307c8 <= a < 0x307d0).

Definition LayoutPU : AllocLayout := {|
  al_segs := rsegs;
  al_malloc_pc := Z_to_bv 64 0x23364;
  al_free_pc := Z_to_bv 64 0x23224;
  al_calloc_pc := Z_to_bv 64 0x230ec;
  al_realloc_pc := Z_to_bv 64 0x24bd0;
  al_tp := Z_to_bv 64 0x424f8;              (* [comment removed for export] *)
  al_static := pu_static;
  al_shared := pu_shared;
  al_image_lo := 0x10000;
  al_rw_lo := 0x30000;
  al_image_hi := 0x64000;                   (* [comment removed for export] *)
|}.

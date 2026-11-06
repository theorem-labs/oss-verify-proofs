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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition p0_static (a : Z) : Prop := 0x62458 <= a < 0x62804.

(* [comment removed for export] *)
Definition p0_shared (a : Z) : Prop :=
  a = 0x623eb \/ (0x62418 <= a < 0x62420) \/ (0x623c8 <= a < 0x623d0) \/ (0x30428 <= a < 0x30430).

Definition LayoutP0 : AllocLayout := {|
  al_segs := rsegs;
  al_malloc_pc := Z_to_bv 64 0x22fc4;
  al_free_pc := Z_to_bv 64 0x22e84;
  al_calloc_pc := Z_to_bv 64 0x22d4c;
  al_realloc_pc := Z_to_bv 64 0x24830;
  al_tp := Z_to_bv 64 0x42158;              (* [comment removed for export] *)
  al_static := p0_static;
  al_shared := p0_shared;
  al_image_lo := 0x10000;
  al_rw_lo := 0x30000;
  al_image_hi := 0x63000;                   (* [comment removed for export] *)
|}.

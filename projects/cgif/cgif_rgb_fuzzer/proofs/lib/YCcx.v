(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0h YG0d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition RRFC_malloc_ra : Z := 0x818f4.
Definition RRFC_free_ra : Z := 0x819e8.
Definition rrfc_trace (pc0 site nb : Z) : list Z := pc0 :: site :: (if nb =? pc0 then [] else [nb]).
Definition rrfc_universe (B : asyms) (nb : Z) : Prop :=
4096 <= nb ->
In (rrfc_trace (pc_malloc_ra0 (as_code B)) RRFC_malloc_ra nb) (as_universe B) /\
In (rrfc_trace (pc_free_ra0 (as_code B)) RRFC_free_ra nb) (as_universe B).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec StoreOk.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition cell (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

(* [comment removed for export] *)
Definition zero_bytes (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Definition img_clear (M : word -> option byte) (lo hi : Z) : Prop :=
  forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.

(* [comment removed for export] *)
Definition bytes_at (M : word -> option byte) (a : Z) (bs : list byte) : Prop :=
  forall i, 0 <= i < Z.of_nat (length bs) -> M (Z_to_bv 64 (a + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).

(* [comment removed for export] *)
Definition stack_writable (M : word -> option byte) (sp0 : word) : Prop :=
  forall d m, 0 <= d -> d + Z.of_nat m <= 8388608 ->
    store_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 8388608 + d)) m = true.

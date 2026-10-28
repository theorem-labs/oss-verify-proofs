(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Cells Step ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition lib0_statics (m : mem) : Prop :=
  (* [comment removed for export] *)
  rw_cells asegs m 0x5a9f40 [C8 (Z_to_bv 64 0x1fbf20)] /\ rw_cells asegs m 0x5a9f60 [C8 (Z_to_bv 64 0x1fc320)]
  /\ rw_cells asegs m 0x5a9f80 [C8 (Z_to_bv 64 0x1fc430)] /\ rw_cells asegs m 0x5a9fc0 [C8 (Z_to_bv 64 0x1c1918)]
  /\ rw_cells asegs m 0xb9f7c0 [C1 (Z_to_bv 8 0)]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xb9f200 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0xb9f2a0 [C8 z64]
  /\ rw_cells asegs m 0xb9f2c0 [C4 z64] /\ rw_cells asegs m 0xb9f2e0 [C4 z64]
  /\ rw_cells asegs m 0xb9f300 [C4 z64] /\ rw_cells asegs m 0xb9f320 [C4 z64]
  /\ rw_cells asegs m 0xb9f220 [C8 z64] /\ rw_cells asegs m 0xb9f240 [C8 z64]
  /\ rw_cells asegs m 0xb9f260 [C4 z64] /\ rw_cells asegs m 0xb9f1c0 [C1 (Z_to_bv 8 0)]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x5a9f20 [C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0xffffffff)]
  /\ rw_cells asegs m 0xb9f4a0 [C4 z64] /\ rw_cells asegs m 0xb9f4c0 [C4 z64] /\ rw_cells asegs m 0xb9f4e0 [C8 z64]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xb9f500 [C4 z64] /\ rw_cells asegs m 0xb9f520 [C4 z64] /\ rw_cells asegs m 0xb9f540 [C1 (Z_to_bv 8 0)]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xb9f820 [C4 z64] /\ rw_cells asegs m 0xb9f7e0 [C8 z64] /\ rw_cells asegs m 0xb9f800 [C8 z64] /\ rw_cells asegs m 0xb9f840 [C4 z64]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xb9f740 [C4 z64] /\ rw_cells asegs m 0xb9f720 [C4 z64] /\ rw_cells asegs m 0xb9f760 [C4 z64]
  /\ rw_cells asegs m 0xb9f780 [C4 z64] /\ rw_cells asegs m 0xb9f7a0 [C4 z64] /\ rw_cells asegs m 0xb9f560 [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0xb9f580 [C8 z64] /\ rw_cells asegs m 0xb9f588 [C8 z64] /\ rw_cells asegs m 0xb9f5f0 [C8 z64]
  /\ rw_cells asegs m 0xb9f628 [C8 z64] /\ rw_cells asegs m 0xb9f630 [C8 z64] /\ rw_cells asegs m 0xb9f638 [C8 z64] /\ rw_cells asegs m 0xb9f640 [C8 z64]
  /\ rw_cells asegs m 0xb9f648 [C8 z64] /\ rw_cells asegs m 0xb9f650 [C8 z64] /\ rw_cells asegs m 0xb9f658 [C8 z64] /\ rw_cells asegs m 0xb9f660 [C8 z64]
  /\ rw_cells asegs m 0xb9f668 [C8 z64] /\ rw_cells asegs m 0xb9f670 [C8 z64] /\ rw_cells asegs m 0xb9f678 [C8 z64] /\ rw_cells asegs m 0xb9f680 [C8 z64]
  /\ rw_cells asegs m 0xb9f688 [C8 z64] /\ rw_cells asegs m 0xb9f690 [C8 z64] /\ rw_cells asegs m 0xb9f698 [C8 z64] /\ rw_cells asegs m 0xb9f6a0 [C8 z64]
  /\ rw_cells asegs m 0xb9f6a8 [C8 z64] /\ rw_cells asegs m 0xb9f6b0 [C8 z64] /\ rw_cells asegs m 0xb9f6b8 [C8 z64]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xb9f860 [C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
Definition lib0_keys (m : mem) : Prop :=
  exists (nk j1 : Z) (w sh oldcb : word) (u : byte),
    0 <= nk /\ 1 <= j1 /\ j1 + 3 < 128
    /\ rw_cells asegs m 0xbc5258 [C4 (Z_to_bv 64 nk)] /\ rw_cells asegs m 0xbc5260 [C4 z64; C4 z64; C4 sh]
    /\ rw_cells asegs m (0xbc4e58 + 8 * nk) [C8 w] /\ ((j1 = nk /\ w = z64) \/ (j1 = nk + 1 /\ bv_unsigned w <> 0))
    /\ rw_cells asegs m (0xbc4e58 + 8 * j1) [C8 z64] /\ rw_cells asegs m (0xbc4e58 + 8 * (j1 + 1)) [C8 z64]
    /\ rw_cells asegs m (0xbc4e58 + 8 * (j1 + 2)) [C8 z64] /\ rw_cells asegs m (0xbc4e58 + 8 * (j1 + 3)) [C8 z64]
    /\ rw_cells asegs m (0xbc5298 + 8 * j1) [C8 z64] /\ rw_cells asegs m (0xbc5298 + 8 * (j1 + 2)) [C8 z64] /\ rw_cells asegs m (0xbc5298 + 8 * (j1 + 3)) [C8 z64]
    /\ rw_cells asegs m (0xba3ef0 + -96) [C8 oldcb] /\ rw_cells asegs m (0xba3ef0 + -150) [C1 u].

Definition LIB0_A (m : mem) : Prop := lib0_statics m /\ lib0_keys m.

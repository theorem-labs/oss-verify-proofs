(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Cells Step ImageA.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition lib0_statics (m : mem) : Prop :=
  (* [comment removed for export] *)
  rw_cells bsegs m 0x5e21e0 [C8 (Z_to_bv 64 0x1fb31c)] /\ rw_cells bsegs m 0x5e2200 [C8 (Z_to_bv 64 0x1fb72c)]
  /\ rw_cells bsegs m 0x5e2220 [C8 (Z_to_bv 64 0x1fb83c)] /\ rw_cells bsegs m 0x5e2240 [C8 (Z_to_bv 64 0x1bc8d0)]
  /\ rw_cells bsegs m 0xbd2040 [C1 (Z_to_bv 8 0)]
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbd1a00 [C1 (Z_to_bv 8 0)] /\ rw_cells bsegs m 0xbd1aa0 [C8 z64]
  /\ rw_cells bsegs m 0xbd1ac0 [C4 z64] /\ rw_cells bsegs m 0xbd1ae0 [C4 z64]
  /\ rw_cells bsegs m 0xbd1b00 [C4 z64] /\ rw_cells bsegs m 0xbd1b20 [C4 z64]
  /\ rw_cells bsegs m 0xbd1a20 [C8 z64] /\ rw_cells bsegs m 0xbd1a40 [C8 z64]
  /\ rw_cells bsegs m 0xbd1a60 [C4 z64] /\ rw_cells bsegs m 0xbd19c0 [C1 (Z_to_bv 8 0)]
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x5e21a0 [C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0xffffffff)]
  /\ rw_cells bsegs m 0xbd1ca0 [C4 z64] /\ rw_cells bsegs m 0xbd1cc0 [C4 z64] /\ rw_cells bsegs m 0xbd1ce0 [C8 z64]
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbd1d00 [C4 z64] /\ rw_cells bsegs m 0xbd1d20 [C4 z64] /\ rw_cells bsegs m 0xbd1d40 [C1 (Z_to_bv 8 0)]
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbd2000 [C4 z64] /\ rw_cells bsegs m 0xbd1fc0 [C8 z64] /\ rw_cells bsegs m 0xbd1fe0 [C8 z64] /\ rw_cells bsegs m 0xbd2020 [C4 z64]
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbd1f40 [C4 z64] /\ rw_cells bsegs m 0xbd1f20 [C4 z64] /\ rw_cells bsegs m 0xbd1f60 [C4 z64]
  /\ rw_cells bsegs m 0xbd1f80 [C4 z64] /\ rw_cells bsegs m 0xbd1fa0 [C4 z64] /\ rw_cells bsegs m 0xbd1d60 [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0xbd1d80 [C8 z64] /\ rw_cells bsegs m 0xbd1d88 [C8 z64] /\ rw_cells bsegs m 0xbd1df0 [C8 z64]
  /\ rw_cells bsegs m 0xbd1e28 [C8 z64] /\ rw_cells bsegs m 0xbd1e30 [C8 z64] /\ rw_cells bsegs m 0xbd1e38 [C8 z64] /\ rw_cells bsegs m 0xbd1e40 [C8 z64]
  /\ rw_cells bsegs m 0xbd1e48 [C8 z64] /\ rw_cells bsegs m 0xbd1e50 [C8 z64] /\ rw_cells bsegs m 0xbd1e58 [C8 z64] /\ rw_cells bsegs m 0xbd1e60 [C8 z64]
  /\ rw_cells bsegs m 0xbd1e68 [C8 z64] /\ rw_cells bsegs m 0xbd1e70 [C8 z64] /\ rw_cells bsegs m 0xbd1e78 [C8 z64] /\ rw_cells bsegs m 0xbd1e80 [C8 z64]
  /\ rw_cells bsegs m 0xbd1e88 [C8 z64] /\ rw_cells bsegs m 0xbd1e90 [C8 z64] /\ rw_cells bsegs m 0xbd1e98 [C8 z64] /\ rw_cells bsegs m 0xbd1ea0 [C8 z64]
  /\ rw_cells bsegs m 0xbd1ea8 [C8 z64] /\ rw_cells bsegs m 0xbd1eb0 [C8 z64] /\ rw_cells bsegs m 0xbd1eb8 [C8 z64]
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbd2060 [C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
Definition lib0_keys (m : mem) : Prop :=
  exists (nk j1 : Z) (w sh oldcb : word) (u : byte),
    0 <= nk /\ 1 <= j1 /\ j1 + 3 < 128
    /\ rw_cells bsegs m 0xbf7a58 [C4 (Z_to_bv 64 nk)] /\ rw_cells bsegs m 0xbf7a60 [C4 z64; C4 z64; C4 sh]
    /\ rw_cells bsegs m (0xbf7658 + 8 * nk) [C8 w] /\ ((j1 = nk /\ w = z64) \/ (j1 = nk + 1 /\ bv_unsigned w <> 0))
    /\ rw_cells bsegs m (0xbf7658 + 8 * j1) [C8 z64] /\ rw_cells bsegs m (0xbf7658 + 8 * (j1 + 1)) [C8 z64]
    /\ rw_cells bsegs m (0xbf7658 + 8 * (j1 + 2)) [C8 z64] /\ rw_cells bsegs m (0xbf7658 + 8 * (j1 + 3)) [C8 z64]
    /\ rw_cells bsegs m (0xbf7a98 + 8 * j1) [C8 z64] /\ rw_cells bsegs m (0xbf7a98 + 8 * (j1 + 2)) [C8 z64] /\ rw_cells bsegs m (0xbf7a98 + 8 * (j1 + 3)) [C8 z64]
    /\ rw_cells bsegs m (0xbd66f0 + -96) [C8 oldcb] /\ rw_cells bsegs m (0xbd66f0 + -150) [C1 u].

Definition LIB0_A (m : mem) : Prop := lib0_statics m /\ lib0_keys m.

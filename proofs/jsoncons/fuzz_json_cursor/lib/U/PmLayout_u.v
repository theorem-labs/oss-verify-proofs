(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmLayout.
Record pm0_layout (L : heap_layout) : Prop := LAY {
  ly_segs : hl_segs L = PML.RSEGS;
  ly_malloc : hl_malloc L = PML.PC_MALLOC;
  ly_free : hl_free L = PML.PC_FREE;
  ly_aligned : hl_aligned_alloc L = 0xa9148;
  ly_tp : hl_tp L = PML.TP;
  ly_errno : hl_errno L = 0xd675c;
  ly_img_lo : hl_img_lo L = 0x10000;
  ly_img_hi : hl_img_hi L = 0xf8000;
  ly_stack : hl_stack L = PML.HEAP_STACK;
  ly_ro : forall a, hl_alloc_ro L a -> (hl_img_lo L <= a < hl_img_hi L) \/ hl_sptop L <= a;
  ly_static : forall a, hl_alloc_static L a -> 0xf6c08 <= a < 0xf6fb0;

  ly_kpm : 0 <= hl_k_per_malloc L;
  ly_bov : 0 <= hl_b_overhead L;
  ly_ro_img : forall a, hl_alloc_ro L a -> hl_img_lo L <= a < hl_img_hi L -> a < 0xbd000 \/ 0xc3a48 <= a < 0xc3a50 \/ 0xf6a70 <= a }.
End PmLayout.

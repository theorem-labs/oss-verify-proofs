(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIface PmLibDefs.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmLayout.
Record pm0_layout (L : heap_layout) : Prop := LAY {
  ly_segs : hl_segs L = PML.RSEGS;
  ly_malloc : hl_malloc L = PML.PC_MALLOC;             (* [comment removed for export] *)
  ly_free : hl_free L = PML.PC_FREE;                   (* [comment removed for export] *)
  ly_aligned : hl_aligned_alloc L = 0xabfb0;
  ly_tp : hl_tp L = PML.TP;                            (* [comment removed for export] *)
  ly_errno : hl_errno L = 0xd957c;                     (* [comment removed for export] *)
  ly_img_lo : hl_img_lo L = 0x10000;
  ly_img_hi : hl_img_hi L = 0xfb000;
  ly_stack : hl_stack L = PML.HEAP_STACK;              (* [comment removed for export] *)
  ly_ro : forall a, hl_alloc_ro L a -> (hl_img_lo L <= a < hl_img_hi L) \/ hl_sptop L <= a;
  ly_static : forall a, hl_alloc_static L a -> 0xf9a28 <= a < 0xf9dd0;
  (* [comment removed for export] *)
  ly_kpm : 0 <= hl_k_per_malloc L;
  ly_bov : 0 <= hl_b_overhead L;
  ly_ro_img : forall a, hl_alloc_ro L a -> hl_img_lo L <= a < hl_img_hi L -> a < 0xc0000 \/ 0xc6830 <= a < 0xc6838 \/ 0xf9890 <= a }.
End PmLayout.

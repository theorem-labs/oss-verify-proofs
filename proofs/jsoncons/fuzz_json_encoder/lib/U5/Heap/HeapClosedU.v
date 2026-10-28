(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The ubsan heap instance closed over its model-bounds hypothesis: everything the ubsan library and driver need
   from the heap (HeapIfaceU.heap_iface_u_ok) for the layout L0U and the invariant HIU. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRes.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.MB Require Import ModelBounds.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require Import PmHeapInst6_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapInstU HeapMallocU HeapAlignedU HeapFreeU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem HIU_ok_closed : forall (sptop : Z) (scfg : SpuriousCfg),
  sc_alloc scfg = false -> heap_iface_u_ok (L0U sptop) scfg (HIU sptop).
Proof.
  intros sptop scfg Halloc.
  pose proof (fun R => @model_bounds_proof R) as MB.
  constructor; [constructor|].
  - eapply HIU_malloc; eauto.
  - eapply HIU_aligned; eauto.
  - eapply HIU_free; eauto.
  - assert (H : free_null_spec (L0 sptop) scfg) by (eapply HI0_free_null; eauto). exact H.
  - exact (HIU_frame sptop).
  - exact (HIU_wf sptop).
  - exact (HIU_perm sptop).
  - eapply HIU_malloc_u; eauto.
Qed.

Corollary HIU_iface_ok_closed : forall (sptop : Z) (scfg : SpuriousCfg),
  sc_alloc scfg = false -> heap_iface_ok (L0U sptop) scfg (HIU sptop).
Proof. intros sptop scfg Halloc. exact (hiu_ok _ _ _ (HIU_ok_closed sptop scfg Halloc)). Qed.

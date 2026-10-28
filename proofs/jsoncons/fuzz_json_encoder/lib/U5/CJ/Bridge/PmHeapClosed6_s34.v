(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRes.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require Import PmHeapInst6_s34.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.MB Require Import ModelBounds.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem HI0_ok_closed : forall (sptop : Z) (scfg : SpuriousCfg),
  sc_alloc scfg = false -> heap_iface_ok (L0 sptop) scfg (HI0 sptop).
Proof. intros sptop scfg Halloc. exact (HI0_ok sptop scfg Halloc (fun R => @model_bounds_proof R)). Qed.

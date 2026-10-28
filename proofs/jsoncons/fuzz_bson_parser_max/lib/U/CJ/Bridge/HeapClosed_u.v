(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Bridge Require Import BrRes. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Bridge Require Import HeapInst0_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.MB Require Import ModelBounds.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.

Section BmKitW. Context {bmK : BMode}.   (* [comment removed for export] *)
Theorem HI0_ok_closed : forall (sptop : Z) (scfg : SpuriousCfg),
  sc_alloc scfg = false -> heap_iface_ok (L0 sptop) scfg (HI0 sptop).
Proof. intros sptop scfg Halloc. exact (HI0_ok sptop scfg Halloc (fun R => @model_bounds_proof R)). Qed.

End BmKitW.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import HeapIface.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import BrRes HeapInst0 HeapInst1.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.MB Require Import ModelBounds.

Theorem HI0_ok_closed : forall (sptop : Z) (scfg : SpuriousCfg),
  sc_alloc scfg = false -> heap_iface_ok (L0 sptop) scfg (HI0 sptop).
Proof. intros sptop scfg Halloc. exact (HI0_ok sptop scfg Halloc (fun R => @model_bounds_proof R)). Qed.

Theorem HI1_ok_closed : forall (sptop : Z) (scfg : SpuriousCfg),
  sc_alloc scfg = false -> heap_iface_ok (L1 sptop) scfg (HI1 sptop).
Proof. intros sptop scfg Halloc. exact (HI1_ok sptop scfg Halloc (fun R => @model_bounds_proof R)). Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare ShapeAlg PureModel VmLedger AllocIface.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocIfaceX
  MallocInv_aslot_iface MallocInv_malloc_iface MallocInv_aslot MallocInv_mal6 MallocInv_calloc2 MallocInv_freetopX AllocBase AllocCalloc MallocAllocLayout MallocGlue.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MallocLayout V2Ref_malloc V2Ref_free V2Ref_calloc.
Import ListNotations.
Local Open Scope Z_scope.

Definition u16_alloc_slot_okW (HT : HeapTop) : alloc_slot_specW (ML:=LU16) (HT:=HT) := alloc_slot_okW (HT:=HT).

Definition u16_free_okX (HT : HeapTop) := free_okX (ML:=LU16) (HT:=HT).

Definition u16_malloc_okX (HT : HeapTop) := malloc_okX (ML:=LU16) (HT:=HT) (u16_alloc_slot_okW HT).
Definition u16_calloc_okX (HT : HeapTop) := calloc_okX (ML:=LU16) (HT:=HT) (u16_malloc_okX HT).

Definition u16_base : AllocBase (AL:=mallocng_alloc_layout (ML:=LU16)) :=
  mallocng_base (ML:=LU16) u16_malloc_okX u16_free_okX (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)).
Definition u16_calloc : AllocCalloc (AL:=mallocng_alloc_layout (ML:=LU16)) (CL:=mallocng_calloc_layout (ML:=LU16)) :=
  mallocng_calloc (ML:=LU16) u16_malloc_okX u16_free_okX u16_calloc_okX
    (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)) (fun fx => calloc_refines (fx:=fx)).

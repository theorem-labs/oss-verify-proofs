(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac AEvt HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_layout.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc Prog KInv KStep Malloc_iface MallocBlocks MallocHINV MallocFacts_nodup.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMalloc_iface HP_RMalloc_ifaceP U_heap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_heap_laws () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_layout.U_layout"; "RocqVerifyHarness.AgentSubmission.U.U_heap.U_HI"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"].


Section PHeapLaws.
Variable sp0 : word.
Local Notation U_layout := (U_layout.U_layout sp0).
Local Notation U_HI := (U_heap.U_HI sp0).

#[using="Type"] Theorem U_heap_perm : ltac2:(CDefT.buildp (gd_tbl_P_heap_laws ()) "Ph,(0.$1.(2.Vsp0,)(3.Vsp0,))PLB,(4.$5.)PLB',(4.$5.)Pm,P,(6.&40.)(7.(6.&8.))Pmo,$8.P,(9.$1.(2.Vsp0,)(3.Vsp0,)R5.R4.R2.R1.)P,(:.$5.R5.R4.)(;.(0.$1.(2.Vsp0,)(3.Vsp0,))Lh',(0.$1.(2.Vsp0,)(3.Vsp0,))(<.(9.$1.(2.Vsp0,)(3.Vsp0,)R1.R6.R5.R4.)(=.$>.(?.$1.(2.Vsp0,)(3.Vsp0,)R1.)(?.$1.(2.Vsp0,)(3.Vsp0,)R8.))))")
(* [comment removed for export] *).
Proof.
  cbn. (intros h LB LB' m mo dd_H; ddestruct dd_H as (ELB & RH & OW & REST); intros HP). subst LB.
  ddestruct (Permutation_map_inv bview (h_blocks h) (Permutation_sym HP)) as (L' & -> & PL).
  exists (mkHST (h_rc h) (h_s h) L' (h_top h)). split; [| reflexivity].
  split; [reflexivity|]. split; [exact (RHEAP_perm _ _ _ _ RH PL)|]. split; [| exact REST].
  eapply OWN_perm; [apply Permutation_map; exact PL| exact OW].
Qed.



(* [comment removed for export] *)
#[using="Type"] Theorem U_heap_nodup : forall h LB m mo,
  HeapIface.HEAP usegs U_layout U_HI h LB m mo -> List.NoDup (map fst LB).
Proof.
  cbn. (intros h LB m mo dd_H; ddestruct dd_H as (-> & RH & _)). ddestruct RH as (st & LB0 & HP & _ & _ & [_ AR]).
  rewrite map_map. change (fun x => fst (bview x)) with blk_addr.
  eapply Permutation_NoDup; [apply Permutation_map; exact HP|].
  exact (MallocFacts_nodup.areach_addr_nodup _ _ AR).
Qed.

End PHeapLaws.

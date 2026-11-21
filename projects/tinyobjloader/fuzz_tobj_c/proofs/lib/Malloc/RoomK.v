(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made from Malloc/RoomS.v for LPS 727298f3: Malloc/ContractDrv.v's room [vm_room] is RoomS's [vm_roomS] ([vm_room_S]), and the room lemmas the existence proofs use are RoomS's, read through it. *)
(* The room lemmas of the existence family ([vm_room], Malloc/ContractDrv.v), each RoomS.v's
   [vm_roomS] lemma read through [vm_room_S].  A separate file because RoomS.v requires
   Malloc/VmRoom.v, which is upstream of it, and Malloc/TRRulesK.v needs these. *)
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocLayout FreeGap ContractDrv VmRoom RoomS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* The two rooms have the same five conjuncts; [vm_room] puts the count bound first. *)
Lemma vm_room_S : forall md X, vm_room md X <-> vm_roomS md X.
Proof.
  intros md X. unfold vm_room, vm_roomS, lcount, ledger, ROOMC, PG, PGSZ.
  split; intros (A & B & C & D & E); repeat split; assumption.
Qed.

(* LPS 08b1429: refusability is asked of Linux's placement at the hint ([vm_place_available]); a gap
   at or above 2^45 that ends below [alloc_top] lies in Linux's bottom-up window. *)
Lemma vm_room_place_available : forall md X len hint (a : word),
  vm_room md X -> 0 < bv_unsigned len ->
  bv_unsigned a mod page_size = 0 -> 2 ^ 45 <= bv_unsigned a ->
  bv_unsigned a + mmap_nZ len <= alloc_top (m_vmmaps md) ->
  region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a (mmap_n len) = true ->
  vm_place_available (m_vmmaps md) (kb_thp (m_kernel md)) hint (mmap_nZ len) = true.
Proof.
  intros md X len hint a HR Hlen Hal Hlo Hhi Hfree. pose proof HR as (_ & _ & _ & _ & HT).
  pose proof WTOP_facts as (W1 & W2 & W3).
  destruct (mmap_nZ_page_len len Hlen) as [Hnpos Hnal]. unfold PG in Hnpos, Hnal.
  apply (vm_place_available_of_gap _ _ _ _ a); [lia | exact Hnal | exact Hal | unfold task_unmapped_base; lia | lia | exact Hfree].
Qed.

Theorem vm_room_rw_not_refusable : forall md X len flags hint,
  vm_room md X -> 0 < bv_unsigned len -> mmap_nZ len <= X -> mmap_noreserve_b flags = false ->
  mmap_grant_refusable flags hint md (mmap_nZ len) = false.
Proof.
  intros md X len flags hint HR. apply (vm_roomS_rw_not_refusable md X len flags hint).
  apply vm_room_S. exact HR.
Qed.

Theorem vm_room_none_not_refusable : forall md X len hint,
  vm_room md X -> 0 < bv_unsigned len -> mmap_nZ len <= X ->
  mmap_reserve_refusable hint md (mmap_nZ len) = false.
Proof.
  intros md X len hint HR. apply (vm_roomS_none_not_refusable md X len hint).
  apply vm_room_S. exact HR.
Qed.

Theorem vm_room_grant_rw : forall md X len a hint flags,
  vm_room md X -> 0 < bv_unsigned len -> mmap_nZ len <= X ->
  mmap_place_ok hint flags md len a ->
  vm_room (with_vmmaps (mmap_rw_vm (m_vmmaps md) len a) md) (X - mmap_nZ len).
Proof.
  intros md X len a hint flags HR Hlen HX Hpl. apply vm_room_S.
  exact (vm_roomS_grant_rw md X len a hint flags (proj1 (vm_room_S md X) HR) Hlen HX Hpl).
Qed.

Theorem vm_room_grant_none : forall md X len a hint,
  vm_room md X -> 0 < bv_unsigned len -> mmap_nZ len <= X ->
  mmap_place_ok_none hint md len a ->
  vm_room (with_vmmaps (mmap_none_vm (m_vmmaps md) len a) md) (X - mmap_nZ len).
Proof.
  intros md X len a hint HR Hlen HX Hpl. apply vm_room_S.
  exact (vm_roomS_grant_none md X len a hint (proj1 (vm_room_S md X) HR) Hlen HX Hpl).
Qed.

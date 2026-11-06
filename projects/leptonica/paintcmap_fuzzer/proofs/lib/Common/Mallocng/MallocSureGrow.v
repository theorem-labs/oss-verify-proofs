(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg VmLedger.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocInv_defs MallocInv_word MallocInv_vm MallocInv_budget MallocInv_vmfree
  MallocInv_ameta_iface MallocInv_ametax_iface MallocSureLedger MallocSureInv.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.
Local Abbreviation u := bv_unsigned (only parsing).

Lemma grow_mmap : forall A A' h (p L : Z),
  VMok A h -> 0 <= p -> 0 <= L -> p + L <= 2^64 - 1 -> a_areas A' = a_areas A -> spare A <= spare A' ->
  sgrow 1 L 0 A A' h (vm_mmap (Z_to_bv 64 p) (Z_to_bv 64 L) h).
Proof.
  intros A A' h p L HV Hp HL Hpl Ea Hsp.
  assert (HuP : u (Z_to_bv 64 p) = p) by (apply uZ; lia). assert (HuL : u (Z_to_bv 64 L) = L) by (apply uZ; lia).
  constructor; cbn [vm_maps vm_init_sp vm_reserved vm_limit vm_mmap length]; try reflexivity.
  - rewrite Nat2Z.inj_succ. lia.
  - pose proof (backed_mmap_le h (Z_to_bv 64 p) (Z_to_bv 64 L) (vm_maps_nw A h HV) ltac:(rewrite HuP, HuL; lia)) as BM.
    rewrite HuL in BM. exact BM.
  - rewrite Ea. lia.
  - unfold muse. rewrite Ea. lia.
  - rewrite Ea. lia.
  - rewrite Nat2Z.inj_succ, Ea. lia.
Qed.

Lemma length_map_remove_le : forall l (a : word), (length (map_remove l a) <= length l)%nat.
Proof.
  intros l a. unfold map_remove. induction l as [|q r IH]; cbn [List.filter length]; [lia|].
  destruct (negb (bv_eqb (fst q) a)); cbn [length]; lia.
Qed.

(* [comment removed for export] *)
Lemma length_map_remove_lt : forall l (a n : word), In (a, n) l -> (length (map_remove l a) < length l)%nat.
Proof.
  intros l a n. unfold map_remove. induction l as [|q r IH]; intros Hin; [destruct Hin|].
  cbn [List.filter length]. destruct Hin as [-> | Hin].
  - cbn [fst]. replace (bv_eqb a a) with true by (symmetry; apply bv_eqb_eq; reflexivity). cbn [negb].
    pose proof (length_map_remove_le r a) as LE. unfold map_remove in LE. lia.
  - specialize (IH Hin). destruct (negb (bv_eqb (fst q) a)); cbn [length]; lia.
Qed.

(* [comment removed for export] *)
Lemma grow_munmap : forall A A' h (a n : word),
  VMok A h -> In (a, n) (vm_maps h) -> a_areas A' = a_areas A -> spare A <= spare A' ->
  sgrow (-1) 0 0 A A' h (vm_munmap a n h).
Proof.
  intros A A' h a n HV Hin Ea Hsp. pose proof (length_map_remove_lt (vm_maps h) a n Hin) as LT.
  constructor; cbn [vm_maps vm_init_sp vm_reserved vm_limit vm_munmap]; try reflexivity.
  - lia.
  - pose proof (backed_munmap_le h a n (vm_maps_nw A h HV) (vm_na_nw A h HV) (maps_pw_pw' _ (vm_pw A h HV)) Hin). lia.
  - rewrite Ea. lia.
  - unfold muse. rewrite Ea. lia.
  - rewrite Ea. lia.
  - rewrite Ea. lia.
Qed.

End WithLayout.

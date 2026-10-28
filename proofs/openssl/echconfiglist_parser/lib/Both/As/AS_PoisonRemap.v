(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv AllocWalkKit F_memset.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_PoisonShadow AW_SysconfPg AW_PoisonRemap1 SecLazy AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)

Lemma zfill_u8arr : forall (a n : word) m,
  bv_unsigned a + bv_unsigned n <= 2^64 -> 12599296 <= bv_unsigned a ->
  u8arr asegs (zfill a n m) (bv_unsigned a) (repeat (b8 0) (Z.to_nat (bv_unsigned n))).
Proof.
  intros a n m NW HI. pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 n).
  split.
  - split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi.
    rewrite nth_error_repeat by exact Hi.
    unfold mrd. rewrite (zfill_in a n m) by (rewrite wa_unsigned by lia; lia). reflexivity.
  - split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi. unfold wview.
    rewrite (zfill_in a n m) by (rewrite wa_unsigned by lia; lia). discriminate.
Qed.

(* [comment removed for export] *)
Lemma relazy_mem_zfill : forall (S : list (word * word)) (a n : word) (m : word -> option byte),
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> in_rangesb x S = true) ->
  (fun x : word => if zin_rangeb (bv_unsigned x) (a, n) && in_rangesb x S then Some (Z_to_bv 8 0) else m x) = zfill a n m.
Proof.
  intros S a n m WIN. apply functional_extensionality. intros x. unfold zfill, AllocSim.zmem, zin_rangeb. cbn [fst snd].
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n)); cbn [andb]; try reflexivity.
  rewrite WIN by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition prm_model (mo : Model) (pb pe : Z) (mo' : Model) : Prop :=
  let h := m_vmmaps mo in let h' := m_vmmaps mo' in
     nonvm_same mo mo'
  /\ vm_maps h' = vm_maps h
  /\ vm_reserved h' = vm_reserved h /\ vm_limit h' = vm_limit h /\ vm_mmap_base h' = vm_mmap_base h
  /\ vm_brk h' = vm_brk h /\ vm_start_brk h' = vm_start_brk h
  /\ vm_noaccess h' = maps_subtract (vm_noaccess h) pb pe
  /\ eager_used mo' <= eager_used mo.

Lemma prm_model_mat : forall mo pb pe mo1 mo2, prm_model mo pb pe mo1 -> same_but_materialized mo1 mo2 -> prm_model mo pb pe mo2.
Proof.
  intros mo pb pe mo1 mo2 (NV & REST) SB. unfold prm_model.
  rewrite (same_but_materialized_vmmaps _ _ SB), (same_but_materialized_eager _ _ SB).
  split; [| exact REST]. eapply nonvm_same_trans; [exact NV| apply nonvm_same_mat; exact SB].
Qed.

(* [comment removed for export] *)
Definition prm_L (L : list (word * word)) (pb pe : Z) : list (word * word) := (wz pb, wz (pe - pb)) :: maps_subtract L pb pe.

End HCW.

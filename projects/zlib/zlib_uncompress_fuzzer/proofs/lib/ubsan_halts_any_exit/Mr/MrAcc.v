(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import VmMapsDisjoint.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require MmapSim RefNodes AsanCeil.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Mr Require Import MrFeasLift2 MrRoom MrAccSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition acc (C U : Z) (mo : Model) : Prop := MrAccSpec.accs C U mo.

Lemma acc_unfold : forall C U mo, acc C U mo <->
  AsanCeil.init_sp_ok (m_vmmaps mo) /\
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) /\
  Z.of_nat (length (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo))) <= C /\
  MrAccSpec.mapped mo <= U /\
  vm_wf (m_vmmaps mo).
Proof. intros. reflexivity. Qed.

Lemma acc_room : forall C U B mo, acc C U mo -> C <= 40000 -> U + B + 4096 <= vm_limit (m_vmmaps mo) -> room B mo.
Proof.
  intros C U B mo (H1 & H2 & H3 & H4 & _) HC HU. pose proof (MrAccSpec.backing_le_mapped mo) as Hb.
  unfold room. split; [exact H1|]. split; [exact H2|]. split; lia.
Qed.

Lemma acc_mono : forall C U C' U' mo, acc C U mo -> C <= C' -> U <= U' -> acc C' U' mo.
Proof. exact MrAccSpec.accs_mono. Qed.

Lemma acc_of_empty : forall C mo,
  AsanCeil.init_sp_ok (m_vmmaps mo) ->
  vm_maps (m_vmmaps mo) = [] -> m_vm_materialized mo = [] ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved (m_vmmaps mo)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps mo))) <= C ->
  acc C 0 mo.
Proof.
  intros C mo Hsp Hm Hmat Hsm Hc. unfold acc, MrAccSpec.accs, MrAccSpec.small, MrAccSpec.mapped.
  rewrite Hm, Hmat, app_nil_r. cbn [live_bytes length].
  split; [exact Hsp|]. split; [exact Hsm|]. split; [exact Hc|]. split; [lia|].
  unfold vm_wf, maps_wf, sizes_nonzero, page_owner_unique. rewrite Hm. split; [constructor|]. intros p _. cbn. lia.
Qed.

Lemma acc_same_vm : forall C U mo mo',
  m_vmmaps mo' = m_vmmaps mo -> m_vm_materialized mo' = m_vm_materialized mo -> acc C U mo -> acc C U mo'.
Proof. intros C U mo mo' Hv Hm H. unfold acc, MrAccSpec.accs, MrAccSpec.mapped in *. rewrite Hv, Hm. exact H. Qed.

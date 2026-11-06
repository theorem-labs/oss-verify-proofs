(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState NodesM DecodeM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue MPath Room Grant.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import EdDefs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma grant_ok_base_ok : forall mo a nZ, grant_ok mo a nZ -> vm_base_ok (m_vmmaps mo) nZ a = true.
Proof.
  intros mo a nZ (G1 & G2 & G3 & G4 & _). unfold vm_base_ok.
  rewrite (proj2 (Z.eqb_eq _ _) G1), (proj2 (Z.ltb_lt _ _) G2), (proj2 (Z.leb_le _ _) G3), G4. reflexivity.
Qed.

Lemma grant_ok_gap : forall mo a nZ, grant_ok mo a nZ -> vm_gap_available (m_vmmaps mo) nZ = true.
Proof. intros mo a nZ G. exact (vm_find_base_complete _ _ a (grant_ok_base_ok mo a nZ G)). Qed.

Lemma room_grant50 : forall mo j nZ,
  room mo j -> 0 <= j <= 28 -> mo_ok mo -> ceil_ok (m_vmmaps mo) -> 0 <= nZ <= 2 ^ 27 ->
  exists a, grant_ok mo a nZ.
Proof.
  intros mo j nZ [Rs Rc Rl Rm] Hj Hmo Hck Hn.
  apply (grant_exists mo nZ ltac:(lia) Rs); [lia | exact Hck|].
  apply grant_budget_intro; [exact Hmo|]. nia.
Qed.

Lemma room_gap : forall mo j nZ,
  room mo j -> 0 <= j <= 28 -> mo_ok mo -> ceil_ok (m_vmmaps mo) -> 0 <= nZ <= 2 ^ 27 ->
  vm_gap_available (m_vmmaps mo) nZ = true.
Proof. intros mo j nZ R Hj Hmo Hck Hn. destruct (room_grant50 mo j nZ R Hj Hmo Hck Hn) as [a G]. exact (grant_ok_gap mo a nZ G). Qed.

Lemma room_grant_not_refusable : forall mo j nZ,
  room mo j -> 0 <= j <= 28 -> mo_ok mo -> ceil_ok (m_vmmaps mo) -> 0 <= nZ <= 2 ^ 27 ->
  mmap_grant_refusable (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) mo nZ = false.
Proof.
  intros mo j nZ R Hj Hmo Hck Hn. unfold mmap_grant_refusable.
  rewrite (room_gap mo j nZ R Hj Hmo Hck Hn). cbn [negb orb]. rewrite orb_false_r.
  destruct (room_grant50 mo j nZ R Hj Hmo Hck Hn) as [a (_ & _ & _ & _ & G5)].
  unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with false. cbn iota.
  rewrite (proj2 (Z.leb_le _ _) G5). reflexivity.
Qed.

Lemma room_reserve_not_refusable : forall mo j nZ,
  room mo j -> 0 <= j <= 28 -> mo_ok mo -> ceil_ok (m_vmmaps mo) -> 0 <= nZ <= 2 ^ 27 ->
  mmap_reserve_refusable mo nZ = false.
Proof. intros mo j nZ R Hj Hmo Hck Hn. unfold mmap_reserve_refusable. rewrite (room_gap mo j nZ R Hj Hmo Hck Hn). reflexivity. Qed.

Lemma room_mprotect_not_refusable : forall mo j addr n,
  room mo j -> 0 <= j <= 28 -> mo_ok mo -> mprotect_refusable mo addr n = false.
Proof.
  intros mo j addr n [Rs Rc Rl Rm] Hj Hmo. unfold mprotect_refusable.
  rewrite (mprotect_budget_ok_intro mo addr n Hmo ltac:(nia)). reflexivity.
Qed.

Lemma mmap_errnos_when_false : forall e, In e (mmap_errnos_when false) -> False.
Proof. intros e H. exact H. Qed.

End CEIL.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the room lemmas take a positive page-aligned length and give Linux's placement available at hint 0 (grant_ok_place, room_place, replacing grant_ok_base_ok, grant_ok_gap and room_gap), and the two refusal guards take the hint. *)
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

(** A grant at Linux's address (hint 0) makes the placement available. *)
Lemma grant_ok_place : forall mo a nZ, 0 < nZ -> nZ mod page_size = 0 -> grant_ok mo a nZ ->
  vm_place_available (m_vmmaps mo) (kb_thp (m_kernel mo)) (Z_to_bv 64 0) nZ = true.
Proof.
  intros mo a nZ Hn Hnal (_ & _ & _ & _ & _ & G6).
  exact (vm_place_available_intro _ _ _ _ a Hn Hnal G6).
Qed.

Lemma room_grant50 : forall mo j nZ,
  room mo j -> 0 <= j <= 28 -> mo_ok mo -> ceil_ok (m_vmmaps mo) -> 0 < nZ <= 2 ^ 27 -> nZ mod page_size = 0 ->
  exists a, grant_ok mo a nZ.
Proof.
  intros mo j nZ [Rs Rc Rl Rm] Hj Hmo Hck Hn Hnal.
  apply (grant_exists mo nZ ltac:(lia) Hnal Rs); [lia | exact Hck|].
  apply grant_budget_intro; [exact Hmo|]. nia.
Qed.

Lemma room_place : forall mo j nZ,
  room mo j -> 0 <= j <= 28 -> mo_ok mo -> ceil_ok (m_vmmaps mo) -> 0 < nZ <= 2 ^ 27 -> nZ mod page_size = 0 ->
  vm_place_available (m_vmmaps mo) (kb_thp (m_kernel mo)) (Z_to_bv 64 0) nZ = true.
Proof.
  intros mo j nZ R Hj Hmo Hck Hn Hnal. destruct (room_grant50 mo j nZ R Hj Hmo Hck Hn Hnal) as [a G].
  exact (grant_ok_place mo a nZ ltac:(lia) Hnal G).
Qed.

Lemma room_grant_not_refusable : forall mo j nZ,
  room mo j -> 0 <= j <= 28 -> mo_ok mo -> ceil_ok (m_vmmaps mo) -> 0 < nZ <= 2 ^ 27 -> nZ mod page_size = 0 ->
  mmap_grant_refusable (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0) mo nZ = false.
Proof.
  intros mo j nZ R Hj Hmo Hck Hn Hnal. unfold mmap_grant_refusable.
  rewrite (room_place mo j nZ R Hj Hmo Hck Hn Hnal). cbn [negb orb]. rewrite orb_false_r.
  destruct (room_grant50 mo j nZ R Hj Hmo Hck Hn Hnal) as [a (_ & _ & _ & _ & G5 & _)].
  unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with false. cbn iota.
  rewrite (proj2 (Z.leb_le _ _) G5). reflexivity.
Qed.

Lemma room_reserve_not_refusable : forall mo j nZ,
  room mo j -> 0 <= j <= 28 -> mo_ok mo -> ceil_ok (m_vmmaps mo) -> 0 < nZ <= 2 ^ 27 -> nZ mod page_size = 0 ->
  mmap_reserve_refusable (Z_to_bv 64 0) mo nZ = false.
Proof.
  intros mo j nZ R Hj Hmo Hck Hn Hnal. unfold mmap_reserve_refusable.
  rewrite (room_place mo j nZ R Hj Hmo Hck Hn Hnal). reflexivity.
Qed.

Lemma room_mprotect_not_refusable : forall mo j addr n,
  room mo j -> 0 <= j <= 28 -> mo_ok mo -> mprotect_refusable mo addr n = false.
Proof.
  intros mo j addr n [Rs Rc Rl Rm] Hj Hmo. unfold mprotect_refusable.
  rewrite (mprotect_budget_ok_intro mo addr n Hmo ltac:(nia)). reflexivity.
Qed.

Lemma mmap_errnos_when_false : forall e, In e (mmap_errnos_when false) -> False.
Proof. intros e H. exact H. Qed.

End CEIL.

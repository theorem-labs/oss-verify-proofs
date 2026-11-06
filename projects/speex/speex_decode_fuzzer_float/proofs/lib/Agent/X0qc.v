(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1pv X1pn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qm X0qn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Export X0px.
Import ListNotations.
Open Scope Z_scope.

Definition HINV_from {RCEIL : RunCeiling} (resv : list (Z * Z)) (st : mstate) (pbrk : Z) (LB : list block) : Prop :=
brk_link st pbrk /\ AREACH_from resv st LB.
Notation HINV := (HINV_from agent_reserved).

Lemma HINV_from_init {RCEIL : RunCeiling} : forall resv pbrk, HINV_from resv (minit 0 alloc_ceiling resv) pbrk [].
Proof. intros. split; [exact I | apply areach_init]. Qed.

Lemma HINV_init {RCEIL : RunCeiling} : forall pbrk, HINV (minit 0 alloc_ceiling agent_reserved) pbrk [].
Proof. intros. apply HINV_from_init. Qed.

Lemma brk_link_ps_iff : forall st s, brk_link_ps st s <-> brk_link st (ps_brk s).
Proof. intros st s. unfold brk_link_ps, brk_link. destruct (c_brk (ctx st)); tauto. Qed.

Definition live_at0 (LB : list block) (c : cptr) : Prop :=
exists b, In b LB /\ blk_slot b = c /\ snd (blk_id b) = 0.

Definition RGA (st : mstate) (hdr : gmap cptr Z) (LB : list block) : Prop :=
(forall (c : cptr) q, hdr !! c = Some q -> 0 <= q < 2 ^ 16)
/\ (forall b, In b LB ->
if slot_top st (blk_slot b)
then 0 <= snd (blk_id b) /\ blk_addr b = conc st (blk_slot b) + UNIT * snd (blk_id b)
/\ hdr !! (blk_slot b) = Some (snd (blk_id b))
else snd (blk_id b) = -1)
/\ (forall (c : cptr) g i, (s_slots st) !! c = Some (g, i) -> m_maplen (get_meta_rec st g) <> 0 ->
~ live_at0 LB c ->
match hdr !! c with
| None => cell_read (get_shadow st (fst c)) (snd c - 3) = Known 0
| Some q => HB st c q
end).

Definition RBIG : Z := 1024.

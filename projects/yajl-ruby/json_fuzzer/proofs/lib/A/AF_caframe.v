(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanWf1 AsanFrame AsanBudget.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_ca_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Variable E : aenv.

(* [comment removed for export] *)
Definition dk_of (s : astate) :=
  (as_ndepot_ins s, as_keys s, as_frames s, as_node_blocks s, as_store_blocks s, as_store_stored s, as_chunks s, as_dead s, as_tq s, as_gq s).
Definition DK d (s : astate) : Prop := dk_of s = d.
Ltac dk_same := match goal with H : DK ?d ?st |- DK ?d _ => unfold DK, dk_of in *; cbn; first [exact H | destruct st; cbn in *; exact H] end.

Lemma ensure_dk : forall d c nf, presW (DK d) (ensure_free_array_space E c nf).
Proof. intros; unfold ensure_free_array_space. pw; try apply call_mmap_fixed_W; dk_same. Qed.
Lemma populate_dk : forall d c r, presW (DK d) (populate_free_array E c r).
Proof. intros; unfold populate_free_array. pw; try apply call_mmap_fixed_W; try apply ensure_dk; dk_same. Qed.
Lemma gfa_dk : forall d c n, presW (DK d) (get_from_allocator E c n).
Proof. intros; unfold get_from_allocator. pw; try apply populate_dk; dk_same. Qed.
Lemma refill_dk : forall d c, presW (DK d) (refill E c).
Proof. intros; unfold refill, init_cache. pw; try apply gfa_dk; dk_same. Qed.
Lemma cache_pop_dk : forall d c, presW (DK d) (cache_pop E c).
Proof. intros; unfold cache_pop. pw; try apply refill_dk; dk_same. Qed.
Lemma sec_alloc_dk : forall d nd, presW (DK d) (sec_alloc E nd).
Proof. intros; unfold sec_alloc. pw; try apply call_mmap_anon_W; try apply call_mmap_fixed_W; dk_same. Qed.
Lemma ca_op_dk : forall d n, presW (DK d) (ca_op E n).
Proof. intros; unfold ca_op. pw; [dk_same| apply cache_pop_dk| apply sec_alloc_dk]. Qed.

(* [comment removed for export] *)
Lemma ca_op_np : forall s0 n, hoareW (fun s => s = s0) (ca_op E n) (fun s' _ => as_nprim_ever s' = as_nprim_ever s0 + bprim n).
Proof.
  intros s0 n. unfold ca_op, bprim. apply hoareW_upd_bind. apply hoareW_pre. intros s (s1 & -> & ->).
  assert (E1 : as_nprim_ever (upd_nprimc (from_primary n) (malloc_class n) s0) = as_nprim_ever s0 + (if from_primary n then 1 else 0)).
  { unfold upd_nprimc. destruct (from_primary n); destruct s0; cbn; lia. }
  destruct (from_primary n).
  - eapply hoareW_conseq; [apply (cache_pop_np E (as_nprim_ever s0 + 1))| cbn beta; intros s ->; unfold NP; exact E1| cbn beta; intros s r H; exact H].
  - eapply hoareW_conseq; [apply (sec_alloc_np E (as_nprim_ever s0 + 0))| cbn beta; intros s ->; unfold NP; exact E1| cbn beta; intros s r H; exact H].
Qed.

(* [comment removed for export] *)
Definition RS (R : list Z) (s : astate) : Prop := as_residue s = R.
Ltac rs_same := match goal with H : RS ?d ?st |- RS ?d _ => unfold RS in *; cbn; first [exact H | destruct st; cbn in *; exact H] end.
Lemma ensure_rs : forall d c nf, presW (RS d) (ensure_free_array_space E c nf).
Proof. intros; unfold ensure_free_array_space. pw; try apply call_mmap_fixed_W; rs_same. Qed.
Lemma populate_rs : forall d c r, presW (RS d) (populate_free_array E c r).
Proof. intros; unfold populate_free_array. pw; try apply call_mmap_fixed_W; try apply ensure_rs; rs_same. Qed.
Lemma gfa_rs : forall d c n, presW (RS d) (get_from_allocator E c n).
Proof. intros; unfold get_from_allocator. pw; try apply populate_rs; rs_same. Qed.
Lemma refill_rs : forall d c, presW (RS d) (refill E c).
Proof. intros; unfold refill, init_cache. pw; try apply gfa_rs; rs_same. Qed.
Lemma cache_pop_rs : forall d c, presW (RS d) (cache_pop E c).
Proof. intros; unfold cache_pop. pw; try apply refill_rs; rs_same. Qed.

(* [comment removed for export] *)
Lemma ca_op_residue : forall s0 n, hoareW (fun s => s = s0) (ca_op E n)
  (fun s' r => if from_primary n then as_residue s' = as_residue s0
               else match r with None => as_residue s' = as_residue s0
                                 | Some ab => as_residue s' = as_residue s0 ++ residue_pages (ab - kPageSize) (map_size n) end).
Proof.
  intros s0 n. unfold ca_op. apply hoareW_upd_bind. apply hoareW_pre. intros s (s1 & -> & ->).
  set (s1 := upd_nprimc (from_primary n) (malloc_class n) s0).
  assert (R1 : as_residue s1 = as_residue s0) by (subst s1; unfold upd_nprimc; destruct (from_primary n); destruct s0; reflexivity).
  destruct (from_primary n) eqn:PR.
  - eapply hoareW_conseq; [apply (cache_pop_rs (as_residue s0) (malloc_class n))| cbn beta; intros s ->; exact R1| cbn beta; intros s r H; exact H].
  - eapply hoareW_conseq; [apply (sec_alloc_frame E s1)| cbn beta; intros s ->; reflexivity|].
    cbn beta. intros s [ab|] X; [| rewrite X; exact R1]. destruct X as [_ X2]. rewrite X2, R1. unfold map_size.
    replace (ab - kPageSize) with (ab - kPageSize) by reflexivity. reflexivity.
Qed.
End RC__1.

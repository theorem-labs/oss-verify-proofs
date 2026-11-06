(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import List ZArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics StackLayout.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.

Class Guard : Type := mkGuard { guard_val : word; secret_val : word }.

(* [comment removed for export] *)
Definition ssp_guard_val {G : Guard} : word := @guard_val G.
Arguments ssp_guard_val {G} : simpl never.
Definition malloc_secret_val {G : Guard} : word := @secret_val G.
Arguments malloc_secret_val {G} : simpl never.

(* [comment removed for export] *)
Definition guard_of (g s : word) : Guard := mkGuard g s.

Lemma ssp_guard_val_of : forall g s, @ssp_guard_val (guard_of g s) = g.
Proof. reflexivity. Qed.
Lemma malloc_secret_val_of : forall g s, @malloc_secret_val (guard_of g s) = s.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition rnd_secret (rnd : bv 128) : word := bv_extract 64 64 rnd.

(* [comment removed for export] *)
Lemma ssp_bv_extract_extract : forall (n : N) (b : bv n) (s1 l1 s2 l2 : N),
  (s1 + l1 <= l2)%N ->
  bv_extract s1 l1 (bv_extract s2 l2 b) = bv_extract (s1 + s2) l1 b.
Proof.
  intros n b s1 l1 s2 l2 Hl. apply bv_eq. rewrite !bv_extract_unsigned.
  apply Z.bits_inj'. intros i Hi.
  rewrite !bv_wrap_spec by lia. rewrite !Z.shiftr_spec by lia. rewrite bv_wrap_spec by lia. rewrite Z.shiftr_spec by lia.
  destruct (bool_decide (i < Z.of_N l1)%Z) eqn:E; cbn [andb]; [|reflexivity].
  apply bool_decide_eq_true in E. rewrite (bool_decide_true (i + Z.of_N s1 < Z.of_N l2)%Z) by lia. cbn [andb].
  f_equal. lia.
Qed.

Lemma rnd_secret_le8 : forall rnd, le8 (rnd_secret rnd) = firstn 8 (skipn 8 (at_random_bytes rnd)).
Proof.
  intros rnd. unfold at_random_bytes, rnd_secret, le8. rewrite <- n_to_le_8_spec. unfold word_le8.
  cbn [firstn skipn]. rewrite !ssp_bv_extract_extract by lia. reflexivity.
Qed.

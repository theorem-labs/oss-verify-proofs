(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AsVocab AsAinvDefs3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma RoundUp_ge : forall x m, 0 < m -> x <= RoundUp x m.
Proof. intros x m Hm. (lazymatch goal with |- ?G => let G' := eval unfold RoundUp in G in change_no_check G' end). nia. Qed.
Lemma RoundUp_lt : forall x m, 0 < m -> RoundUp x m < x + m.
Proof. intros x m Hm. (lazymatch goal with |- ?G => let G' := eval unfold RoundUp in G in change_no_check G' end). nia. Qed.
Lemma RoundUp_mod : forall x m, 0 < m -> RoundUp x m mod m = 0.
Proof. intros x m Hm. (lazymatch goal with |- ?G => let G' := eval unfold RoundUp in G in change_no_check G' end). apply Z_mod_mult. Qed.



Ltac leb_cases :=
  repeat match goal with |- context [if ?a <=? ?b then _ else _] => destruct (Z.leb_spec a b) end;
  repeat match goal with |- context [?a <=? ?b] => destruct (Z.leb_spec a b) end.

Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. (lazymatch goal with |- ?G => let G' := eval unfold rz_log in G in change_no_check G' end). leb_cases; lia. Qed.

Lemma rz_cases : forall n, rz n = 16 \/ rz n = 32 \/ rz n = 64 \/ rz n = 128 \/ rz n = 256 \/ rz n = 512 \/ rz n = 1024 \/ rz n = 2048.
Proof.
  intros n. (lazymatch goal with |- ?G => let G' := eval unfold rz, rz_log in G in change_no_check G' end). leb_cases; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia.
Qed.
Lemma rz_range : forall n, 16 <= rz n <= 2048.
Proof. intros n. destruct (rz_cases n) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; lia. Qed.
Lemma rz_mod16 : forall n, rz n mod 16 = 0.
Proof. intros n. destruct (rz_cases n) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; reflexivity. Qed.
Lemma rz_big : forall n, 64512 < n -> rz n = 2048.
Proof. intros n H. (lazymatch goal with |- ?G => let G' := eval unfold rz, rz_log in G in change_no_check G' end). leb_cases; try lia; reflexivity. Qed.

Lemma rounded_ge : forall n, n <= rounded n /\ 8 <= rounded n /\ rounded n mod 8 = 0 /\ rounded n < Z.max n 8 + 8.
Proof.
  intros n. (lazymatch goal with |- ?G => let G' := eval unfold rounded in G in change_no_check G' end). pose proof (RoundUp_ge (Z.max n 8) 8 ltac:(lia)). pose proof (RoundUp_lt (Z.max n 8) 8 ltac:(lia)).
  pose proof (RoundUp_mod (Z.max n 8) 8 ltac:(lia)). lia.
Qed.

Lemma is_primary_iff : forall n, 1 <= n -> (is_primary n = true <-> n <= 64512).
Proof.
  intros n Hn. (lazymatch goal with |- ?G => let G' := eval unfold is_primary, needed in G in change_no_check G' end). pose proof (rounded_ge n) as (R1 & R2 & R3 & R4).
  unfold rz, rz_log, rounded, RoundUp in *. leb_cases; split; intros; first [reflexivity | lia | discriminate | exfalso; lia].
Qed.

(* [comment removed for export] *)
Ltac eval_csize :=
  match goal with |- context [csize (Zpos ?p)] => let v := eval vm_compute in (csize (Zpos p)) in change (csize (Zpos p)) with v end.

Lemma csize_pos : forall c, 1 <= c <= 30 -> 32 <= csize c <= 65536 /\ csize c mod 16 = 0.
Proof.
  intros c Hc.
  assert (K : c <= 16 \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24
              \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
  destruct K as [LE|K].
  - (lazymatch goal with |- ?G => let G' := eval unfold csize in G in change_no_check G' end). destruct (Z.leb_spec c 16); [|lia]. split; [lia|]. replace (32 * c) with ((2 * c) * 16) by lia. apply Z_mod_mult.
  - destruct K as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]; subst c; eval_csize; (split; [lia|reflexivity]).
Qed.

Lemma class_of_range : forall s, 1 <= s <= 65536 -> 1 <= class_of s <= 30.
Proof.
  intros s Hs. (lazymatch goal with |- ?G => let G' := eval unfold class_of in G in change_no_check G' end). leb_cases; try lia.
Qed.

Lemma csize_class_of : forall s, 1 <= s <= 65536 -> s <= csize (class_of s).
Proof.
  intros s Hs. (lazymatch goal with |- ?G => let G' := eval unfold class_of in G in change_no_check G' end). leb_cases; try eval_csize; try lia.
  (* [comment removed for export] *)
  (lazymatch goal with |- ?G => let G' := eval unfold csize in G in change_no_check G' end). destruct (Z.leb_spec ((s + 31) / 32) 16); [lia|exfalso; lia].
Qed.

(* [comment removed for export] *)
Lemma prim_user_in_chunk : forall n, 1 <= n -> is_primary n = true ->
  rz n + n <= csize (class_of (needed n)) /\ 1 <= class_of (needed n) <= 30.
Proof.
  intros n Hn HP. pose proof (rounded_ge n) as (R1 & _). pose proof (rz_range n).
  assert (NB : 1 <= needed n <= 65536).
  { unfold is_primary in HP. apply Z.leb_le in HP. unfold needed in *. lia. }
  pose proof (csize_class_of (needed n) NB). pose proof (class_of_range (needed n) NB). unfold needed in *. lia.
Qed.

Lemma sec_map_size_ge : forall n, 1 <= n -> n + PG + rz n <= sec_map_size n /\ sec_map_size n mod PG = 0
  /\ sec_map_size n <= n + 3 * PG + 2 * rz n + 15.
Proof.
  intros n Hn. (lazymatch goal with |- ?G => let G' := eval unfold sec_map_size, sec_needed, sec_user_off in G in change_no_check G' end). pose proof (rounded_ge n) as (R1 & R2 & R3 & R4).
  pose proof (rz_range n).
  pose proof (RoundUp_ge (rounded n + 2 * rz n) PG ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)).
  pose proof (RoundUp_lt (rounded n + 2 * rz n) PG ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)).
  pose proof (RoundUp_mod (rounded n + 2 * rz n) PG ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)).
  unfold PG in *. split; [lia|]. split; [|lia].
  match goal with H : RoundUp ?x 4096 mod 4096 = 0 |- _ =>
    rewrite Z.add_mod by lia; rewrite H; reflexivity end.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Notation zlenF l := (FseNCount.Zlength l).

(* [comment removed for export] *)
Lemma sv_byte : forall s j, 0 <= s < 256 -> 0 <= j < 8 -> (Z.shiftr (s * 72340172838076673) (8 * j)) mod 256 = s.
Proof.
  assert (B : forallb (fun s => forallb (fun j => (Z.shiftr (s * 72340172838076673) (8 * j)) mod 256 =? s) (zseq 8 0)) (zseq 256 0) = true)
    by (vm_compute; reflexivity).
  intros s j Hs Hj. rewrite forallb_forall in B. specialize (B s ltac:(apply zseq_In_iff; lia)).
  rewrite forallb_forall in B. apply Z.eqb_eq. apply B. apply zseq_In_iff. lia.
Qed.

(* [comment removed for export] *)
Lemma land_m8 : forall x, 0 <= x < 1024 -> Z.land x 18446744073709551608 = 8 * (x / 8).
Proof.
  assert (B : forallb (fun x => Z.land x 18446744073709551608 =? 8 * (x / 8)) (zseq 1024 0) = true) by (vm_compute; reflexivity).
  intros x Hx. rewrite forallb_forall in B. apply Z.eqb_eq. apply B. apply zseq_In_iff. lia.
Qed.

(* [comment removed for export] *)
Definition wr8m (l : list Z) (p s : Z) : list Z :=
  Zupd (p + 3) s (Zupd (p + 2) s (Zupd (p + 1) s (Zupd p s (Zupd (p + 7) s (Zupd (p + 6) s (Zupd (p + 5) s (Zupd (p + 4) s l))))))).

Lemma Zupd_len : forall i v (l : list Z), zlenF (Zupd i v l) = zlenF l.
Proof. intros. unfold FseNCount.Zlength. rewrite FseLemmas.Zupd_length. reflexivity. Qed.

Lemma wr8m_eq : forall l p s, 0 <= p -> p + 8 <= zlenF l -> wr8m l p s = write8 l p s.
Proof.
  intros l p s Hp Hl.
  assert (TL : 5 <= 5 <= 9) by lia.
  apply (nth_ext _ _ 0 0).
  - unfold wr8m, write8. rewrite !FseLemmas.Zupd_length. reflexivity.
  - intros n Hn. unfold wr8m in Hn. rewrite !FseLemmas.Zupd_length in Hn.
    change (nth n (wr8m l p s) 0) with (Znth (Z.of_nat n) (wr8m l p s)) at 1 || idtac.
    assert (E : forall l', nth n l' 0 = Znth (Z.of_nat n) l') by (intros; unfold Znth; rewrite Nat2Z.id; reflexivity).
    rewrite !E. unfold wr8m, write8.
    repeat (rewrite (Znth_Zupd_eq 5 TL) by (rewrite ?Zupd_len; unfold FseNCount.Zlength in *; lia)).
    repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end; try reflexivity; lia.
Qed.

Lemma write8_bytes : forall l p s, 0 <= s < 256 -> Forall (fun v => 0 <= v < 256) l -> Forall (fun v => 0 <= v < 256) (write8 l p s).
Proof.
  intros l p s Hs F.
  assert (U : forall i (l' : list Z), Forall (fun v => 0 <= v < 256) l' -> Forall (fun v => 0 <= v < 256) (Zupd i s l')).
  { intros i l' F'. unfold Zupd. generalize (Z.to_nat i). intros n. revert n. induction F' as [|x t Hx Ht IH]; intros [|n]; cbn [upd_nat]; constructor; auto. }
  unfold write8. repeat apply U. exact F.
Qed.

(* [comment removed for export] *)
Fixpoint lay_k (j : nat) (l : list Z) (p s : Z) : list Z :=
  match j with O => l | S j' => lay_k j' (write8 l p s) (p + 8) s end.

Lemma lay_more_k : forall (j f : nat) l pos s i n, (j <= f)%nat -> i + 8 * Z.of_nat j >= n -> (j = 0%nat \/ i + 8 * (Z.of_nat j - 1) < n) ->
  lay_more f l pos s i n = lay_k j l (pos + i) s.
Proof.
  induction j as [|j IH]; intros f l pos s i n Hf Hge Hlt.
  - destruct f as [|f]; cbn [lay_more lay_k]; [reflexivity|]. destruct (Z.ltb_spec i n); [lia| reflexivity].
  - destruct f as [|f]; [lia|]. cbn [lay_more lay_k]. destruct (Z.ltb_spec i n) as [L|L]; [|lia].
    rewrite (IH f (write8 l (pos + i) s) pos s (i + 8) n) by lia. f_equal. lia.
Qed.

Lemma lay_k_length : forall j l p s, length (lay_k j l p s) = length l.
Proof. induction j as [|j IH]; intros; cbn [lay_k]; [reflexivity|]. rewrite IH. apply write8_length. Qed.

Lemma lay_k_bytes : forall j l p s, 0 <= s < 256 -> Forall (fun v => 0 <= v < 256) l -> Forall (fun v => 0 <= v < 256) (lay_k j l p s).
Proof. induction j as [|j IH]; intros l p s Hs F; cbn [lay_k]; [exact F|]. apply IH; [exact Hs|]. apply write8_bytes; assumption. Qed.

Lemma lay_more_bytes : forall f l pos s i n, 0 <= s < 256 -> Forall (fun v => 0 <= v < 256) l -> Forall (fun v => 0 <= v < 256) (lay_more f l pos s i n).
Proof.
  induction f as [|f IH]; intros l pos s i n Hs F; cbn [lay_more]; [exact F|].
  destruct (i <? n); [|exact F]. apply IH; [exact Hs|]. apply write8_bytes; assumption.
Qed.

Lemma lay_symbols_bytes : forall norm f s pos l, 0 <= s -> s + Z.of_nat f <= 256 -> Forall (fun v => 0 <= v < 256) l ->
  Forall (fun v => 0 <= v < 256) (fst (lay_symbols f norm s pos l)).
Proof.
  intros norm. induction f as [|f IH]; intros s pos l Hs Hf F; cbn [lay_symbols fst]; [exact F|].
  apply IH; [lia | lia |]. apply lay_more_bytes; [lia|]. apply write8_bytes; [lia| exact F].
Qed.

Lemma lay_more_length : forall f l pos s i n, length (lay_more f l pos s i n) = length l.
Proof.
  induction f as [|f IH]; intros; cbn [lay_more]; [reflexivity|]. destruct (i <? n); [|reflexivity]. rewrite IH. apply write8_length.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Wf_Z Wellfounded.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxOrder.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module LXOW.
Import LXO.

Lemma lex_lt_nil_r : forall a, ~ lex_lt a [].
Proof. intros [|c cr] H; cbn in H; exact H. Qed.

Lemma lex_lt_nil_l : forall b, ~ lex_lt [] b.
Proof. intros [|s sr] H; cbn in H; exact H. Qed.

Lemma lex_lt_length : forall a b, lex_lt a b -> length a = length b.
Proof.
  induction a as [|c cr IH]; intros [|s sr] H; cbn in H; try contradiction.
  cbn. destruct H as [(_ & _ & Hl & _) | (_ & _ & Hl)]; [rewrite Hl; reflexivity | rewrite (IH sr Hl); reflexivity].
Qed.

(* [comment removed for export] *)
Lemma acc_lex_len : forall n (l : list Z), length l = n -> Acc lex_lt l.
Proof.
  induction n as [|n IHn]; intros l Hl.
  - destruct l; [|discriminate]. constructor. intros y Hy. exfalso. exact (lex_lt_nil_r y Hy).
  - destruct l as [|s sr]; [discriminate|]. cbn in Hl. injection Hl as Hl. revert sr Hl.
    (* [comment removed for export] *)
    induction (Z.lt_wf 0 s) as [s _ IHs]. intros sr Hl.
    assert (Hacc : Acc lex_lt sr) by (apply IHn; exact Hl).
    revert Hl. induction Hacc as [sr _ IHt]. intros Hl.
    constructor. intros [|c cr] Hy; [exfalso; exact (lex_lt_nil_l _ Hy)|]. cbn in Hy.
    destruct Hy as [(Hc0 & Hcs & Hlen & _) | (Hc0 & Hcs & Hlex)].
    + apply (IHs c); [lia | congruence].
    + subst c. apply IHt; [exact Hlex|]. rewrite (lex_lt_length cr sr Hlex). exact Hl.
Qed.

Theorem lex_lt_wf : well_founded lex_lt.
Proof. intros l. exact (acc_lex_len (length l) l eq_refl). Qed.

Lemma acc_mu_nonnil : forall l, Acc lex_lt l -> l <> [] -> Acc mu_lt l.
Proof.
  intros l Hacc. induction Hacc as [l _ IH]. intros Hne.
  constructor. intros y Hy. destruct Hy as [(Hl & _ & _) | Hlex]; [congruence|].
  apply IH; [exact Hlex|]. intros ->. exact (lex_lt_nil_l _ Hlex).
Qed.

Theorem mu_lt_wf : well_founded mu_lt.
Proof.
  intros l. destruct l as [|z r].
  - constructor. intros y Hy. destruct Hy as [(_ & Hne & _) | Hlex]; [|exfalso; exact (lex_lt_nil_r _ Hlex)].
    apply acc_mu_nonnil; [apply lex_lt_wf | exact Hne].
  - apply acc_mu_nonnil; [apply lex_lt_wf | discriminate].
Qed.

End LXOW.

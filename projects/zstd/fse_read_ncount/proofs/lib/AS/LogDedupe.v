(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import PropExec CatExec MemSplit AxSymExec3 AxSymExec3Sound AsanPlanCore.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC.
Open Scope Z_scope.
Lemma dd_key_some : forall a p, dd_key a = Some p -> a = SA (ELit 0) (Zpos p).
Proof.
intros [b k] p H. unfold dd_key in H.
repeat match type of H with context [match ?t with _ => _ end] => destruct t; try discriminate end.
injection H as <-. reflexivity.
Qed.
Lemma dd_has_add : forall s a w a' w',
dd_has (dd_add s a w) a' w' = true -> (a' = a /\ w' = w) \/ dd_has s a' w' = true.
Proof.
intros s a w a' w' H. unfold dd_has, dd_add in *.
destruct (dd_key a) as [p|] eqn:Ka; destruct (dd_key a') as [p'|] eqn:Ka'; cbn [dd_lit dd_oth] in H.
- destruct (Pos.eq_dec p' p) as [->|Hne].
+ rewrite pt_gss in H. cbn [existsb] in H. apply orb_prop in H as [H|H].
* left. apply Nat.eqb_eq in H. split; [|exact H]. rewrite (dd_key_some _ _ Ka), (dd_key_some _ _ Ka'). reflexivity.
* right. revert H. destruct (pt_get (dd_lit s) p); intro H; [exact H | discriminate].
+ right. rewrite pt_gso in H by exact Hne. exact H.
- right. exact H.
- right. exact H.
- cbn [existsb fst snd] in H. apply orb_prop in H as [H|H]; [left | right; exact H].
apply andb_prop in H as [H1 H2]. apply saddr_eqb_eq in H1. apply Nat.eqb_eq in H2. split; assumption.
Qed.
Definition dd_cov (E : env) (s : ddseen) (x : word) : Prop :=
exists a w, dd_has s a w = true
/\ bv_unsigned (adenot E a) <= bv_unsigned x < bv_unsigned (adenot E a) + Z.of_nat w.
Lemma dd_cov_empty : forall E x, ~ dd_cov E (DDS PTLeaf []) x.
Proof.
intros E x (a & w & H & _). unfold dd_has in H. cbn [dd_lit dd_oth] in H.
destruct (dd_key a); [rewrite pt_get_leaf in H|]; cbn in H; discriminate.
Qed.
Lemma mem_denot_dd_go : forall E base log s, log_flat E log ->
forall x, ~ dd_cov E s x -> mem_denot E base (log_dd_go s log) x = mem_denot E base log x.
Proof.
intros E base log. induction log as [|[a w v] older IH]; intros s Hlf x Hx; [reflexivity|].
cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfa & Hlf').
assert (HA : bv_unsigned (adenot E a) + Z.of_nat (length (word_to_le_bytes w (edenot E v))) <= 2 ^ 64).
{ rewrite length_N_to_le_bytes, (flat_u E a _ Hfa). destruct Hfa as (?&?&?&?). lia. }
assert (Hnew : forall a' w', dd_has (dd_add s a w) a' w' = true ->
bv_unsigned (adenot E a') <= bv_unsigned x < bv_unsigned (adenot E a') + Z.of_nat w' ->
bv_unsigned (adenot E a) <= bv_unsigned x < bv_unsigned (adenot E a) + Z.of_nat w).
{ intros a' w' Hh' Hr. apply dd_has_add in Hh' as [[-> ->]|Hh']; [exact Hr|].
exfalso. apply Hx. exists a', w'. split; assumption. }
cbn [log_dd_go]. destruct (dd_has s a w) eqn:Hh; cbn [mem_denot].
-
rewrite wbytes_outside; [apply IH; assumption | exact HA |].
rewrite length_N_to_le_bytes.
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (adenot E a))) as [L|G]; [left; exact L|].
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (adenot E a) + Z.of_nat w)) as [L2|G2]; [|right; exact G2].
exfalso. apply Hx. exists a, w. split; [exact Hh | lia].
-
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (adenot E a))) as [L|G].
+ rewrite !wbytes_outside by (first [exact HA | left; exact L]).
apply IH; [exact Hlf'|]. intros (a' & w' & Hh' & Hr). pose proof (Hnew a' w' Hh' Hr). lia.
+ destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (adenot E a) + Z.of_nat w)) as [L2|G2].
* rewrite !wbytes_inside by (first [exact HA | rewrite length_N_to_le_bytes; lia]). reflexivity.
* rewrite !wbytes_outside by (first [exact HA | right; rewrite length_N_to_le_bytes; exact G2]).
apply IH; [exact Hlf'|]. intros (a' & w' & Hh' & Hr). pose proof (Hnew a' w' Hh' Hr). lia.
Qed.
Lemma mem_denot_dd : forall E base log, log_flat E log -> mem_denot E base (log_dd log) = mem_denot E base log.
Proof.
intros E base log Hlf. apply functional_extensionality. intro x.
apply mem_denot_dd_go; [exact Hlf | apply dd_cov_empty].
Qed.
Lemma log_flat_dd_go : forall E log s, log_flat E log -> log_flat E (log_dd_go s log).
Proof.
intros E log. induction log as [|[a w v] older IH]; intros s H; [exact I|].
cbn [log_flat] in H. destruct H as (H1 & H2 & H3). cbn [log_dd_go].
destruct (dd_has s a w); [apply IH; exact H3|].
cbn [log_flat]. split; [exact H1|]. split; [exact H2|]. apply IH. exact H3.
Qed.
Lemma log_flat_dd : forall E log, log_flat E log -> log_flat E (log_dd log).
Proof. intros E log H. apply log_flat_dd_go. exact H. Qed.

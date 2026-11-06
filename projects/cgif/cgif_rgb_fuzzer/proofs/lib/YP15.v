(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP14.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition pix (fmt : Z) (img : list Z) (i : Z) : list Z := skipn (Z.to_nat (fmt * i)) img.

Definition pcolour (fmt : Z) (img : list Z) (i : Z) : colour := px_colour (pix fmt img i).
Definition popaque (fmt : Z) (img : list Z) (i : Z) : bool := opaque fmt (pix fmt img i).





Fixpoint bump (c : colour) (ent : list entry) : list entry :=
match ent with
| [] => [(c, 1)]
| (c', f) :: r => if colour_eqb c' c then (c', f + 1) :: r else (c', f) :: bump c r
end.
Fixpoint hist_n (fmt : Z) (img : list Z) (n : nat) : list entry :=
match n with
| O => []
| S n' => if popaque fmt img (Z.of_nat n') then bump (pcolour fmt img (Z.of_nat n')) (hist_n fmt img n')
else hist_n fmt img n'
end.
Definition hist (fmt : Z) (img : list Z) (n : Z) : list entry := hist_n fmt img (Z.to_nat n).
Fixpoint nopaque_n (fmt : Z) (img : list Z) (n : nat) : Z :=
match n with
| O => 0
| S n' => (if popaque fmt img (Z.of_nat n') then 1 else 0) + nopaque_n fmt img n'
end.
Definition nopaque (fmt : Z) (img : list Z) (n : Z) : Z := nopaque_n fmt img (Z.to_nat n).























Lemma perm_zsum : forall (l l' : list entry), Permutation l l' -> zsum (map snd l) = zsum (map snd l').
Proof.
intros l l' HP. induction HP; cbn; try lia.
Qed.

Definition hist_rel (H : htab) (fmt : Z) (img : list Z) (n : Z) : Prop :=
exists ent, ht_inv H ent /\ Permutation ent (hist fmt img n).







Definition has_alpha (fmt : Z) (img : list Z) (n : Z) : bool := negb (nopaque fmt img n =? n).




Definition used_below (H : htab) (j : Z) : list Z := filter (fun x => negb (usedz H x =? 0)) (zseq 0 j).
Definition ent_of (H : htab) (x : Z) : entry := (key H x, freq H x).
Definition ents_below (H : htab) (j : Z) : list entry := map (ent_of H) (used_below H j).
Lemma used_below_In : forall H j x, In x (used_below H j) <-> 0 <= x < j /\ usedz H x <> 0.
Proof.
intros H j x. unfold used_below. rewrite filter_In, In_zseq, Bool.negb_true_iff, Z.eqb_neq. lia.
Qed.
Lemma used_below_NoDup : forall H j, NoDup (used_below H j).
Proof. intros. unfold used_below. apply NoDup_filter. apply zseq_NoDup. Qed.

Lemma used_below_succ : forall H j, 0 <= j ->
used_below H (j + 1) = used_below H j ++ (if usedz H j =? 0 then [] else [j]).
Proof.
intros H j Hj. unfold used_below. rewrite zseq_succ, filter_app by lia. cbn. destruct (usedz H j =? 0); reflexivity.
Qed.
Lemma ents_below_0 : forall H, ents_below H 0 = [].
Proof. reflexivity. Qed.
Lemma ents_below_unused : forall H j, 0 <= j -> usedz H j = 0 -> ents_below H (j + 1) = ents_below H j.
Proof.
intros H j Hj Hz. unfold ents_below. rewrite used_below_succ, Hz by lia. cbn. rewrite app_nil_r. reflexivity.
Qed.
Lemma ents_below_used : forall H j, 0 <= j -> usedz H j <> 0 ->
ents_below H (j + 1) = ents_below H j ++ [(key H j, freq H j)].
Proof.
intros H j Hj Hu. unfold ents_below. rewrite used_below_succ by lia.
destruct (Z.eqb_spec (usedz H j) 0); [lia|]. rewrite map_app. reflexivity.
Qed.
Lemma used_below_le_cnt : forall H ent j, ht_inv H ent -> 0 <= j <= ht_T H ->
Z.of_nat (length (used_below H j)) <= ht_cnt H.
Proof.
intros H ent j INV Hj. destruct INV as ((L1 & _) & (_ & _ & C3) & _). rewrite <- C3.
apply cnt1_nodup_bound; [apply used_below_NoDup|].
intros p Hp. apply used_below_In in Hp. unfold usedz in Hp. rewrite L1. lia.
Qed.
Lemma ents_below_len : forall H j, elen (ents_below H j) = Z.of_nat (length (used_below H j)).
Proof. intros. unfold elen, ents_below. rewrite length_map. reflexivity. Qed.
Lemma ht_empty_inv : forall (T' : Z) frN keysN palN colidxN,
0 < T' -> zlen frN = T' -> zlen keysN = 3 * T' -> zlen palN = 3 * T' -> zlen colidxN = T' ->
Forall (fun v => 0 <= v < 256) keysN -> Forall (fun v => 0 <= v < 256) palN ->
ht_inv (mkHT frN keysN (repeat 0 (Z.to_nat T')) palN colidxN 0 T') [].
Proof.
intros T' frN keysN palN colidxN HT Hf Hk Hp Hc Hkb Hpb.
set (K := mkHT frN keysN (repeat 0 (Z.to_nat T')) palN colidxN 0 T').
assert (Hu0 : forall h, usedz K h = 0).
{ intros h. unfold usedz, K. cbn [ht_used]. unfold getz. destruct (Nat.lt_ge_cases (Z.to_nat h) (Z.to_nat T')).
- apply nth_repeat_lt. assumption.
- rewrite nth_overflow; [reflexivity|]. rewrite repeat_length. assumption. }
assert (Hno : forall h, ~ in_slot K h) by (intros h [_ Hu]; apply Hu; apply Hu0).
unfold ht_inv, K. cbn [ht_used ht_keys ht_frequ ht_colidx ht_pal ht_cnt ht_T].
split; [unfold zlen in *; rewrite repeat_length; lia|].
split; [rewrite cnt1_repeat0; cbn; lia|].
split; [split; [intros h Hh; left; apply Hu0| split; assumption]|].
split; [intros h Hin; exfalso; exact (Hno h Hin)|].
split; [intros i Hi; lia|].
split; [intros h h' Hin; exfalso; exact (Hno h Hin)|].
intros h j Hin; exfalso; exact (Hno h Hin).
Qed.

Section a.
Variable H : htab.
Variable ent : list entry.
Hypothesis INV : ht_inv H ent.
Theorem rehash_step_used : forall K j,
ht_inv K (ents_below H j) -> 0 <= j < ht_T H -> usedz H j <> 0 -> ht_cnt H < ht_T K ->
exists h, find_slot K (key H j) = Some h /\ 0 <= h < ht_T K /\ usedz K h = 0 /\
ht_cnt K + 1 <= ht_cnt H /\
ht_inv (ht_ins K h (key H j) (freq H j)) (ents_below H (j + 1)).
Proof.
intros K j HK Hj Hu HcT.
destruct (find_slot_exists K _ HK (key H j)) as (h & Hfs & Hh).
assert (Hjin : in_slot H j) by (split; assumption).
assert (Hfree : usedz K h = 0).
{ destruct (inv_used01 K _ HK h Hh) as [Hz|H1]; [exact Hz|]. exfalso.
assert (Hk : has_key (ents_below H j) (key H j)).
{ apply (proj1 (find_slot_has_key K _ HK _ h Hfs)). rewrite H1. lia. }
unfold has_key, ents_below in Hk. rewrite map_map, in_map_iff in Hk. destruct Hk as (x & Ex & Hx).
cbn in Ex. apply used_below_In in Hx as [Hxj Hxu].
destruct INV as (_ & _ & _ & _ & _ & I7 & _).
assert (x = j) by (apply I7; [split; [lia| exact Hxu]| exact Hjin| exact Ex]). lia. }
pose proof (used_below_le_cnt H ent (j + 1) INV ltac:(lia)) as Hlen.
rewrite used_below_succ in Hlen by lia. destruct (Z.eqb_spec (usedz H j) 0); [lia|].
rewrite length_app in Hlen. cbn [length] in Hlen.
destruct (inv_cnt K _ HK) as [HeK HcK]. rewrite ents_below_len in HeK.
exists h. split; [exact Hfs|]. split; [exact Hh|]. split; [exact Hfree|]. split; [lia|].
rewrite ents_below_used by lia. apply (ht_ins_inv K _ HK); try assumption.
- destruct INV as ((_ & L2 & _) & _ & (_ & B2 & _) & _). unfold key. apply col_at_ok; [exact B2| lia| lia].
- destruct INV as (_ & _ & _ & I4 & _). destruct (I4 j Hjin) as (_ & _ & Hf). exact Hf.
- lia.
Qed.
Lemma rehash_step_unused : forall K j, ht_inv K (ents_below H j) -> 0 <= j -> usedz H j = 0 ->
ht_inv K (ents_below H (j + 1)).
Proof. intros K j HK Hj Hz. rewrite ents_below_unused by assumption. exact HK. Qed.

Theorem rehash_done : Permutation ent (ents_below H (ht_T H)).
Proof.
pose proof (ent_NoDup H ent INV) as Hnd.
apply NoDup_Permutation_bis.
- eapply NoDup_map_inv with (f := fst). exact Hnd.
- pose proof (used_below_le_cnt H ent (ht_T H) INV) as Hlen. destruct (inv_cnt H ent INV) as [He Hc].
unfold ents_below. rewrite length_map. unfold elen in He. lia.
- intros cf Hin. apply In_nth_error in Hin as [n Hn].
destruct (ent_nth H ent INV (Z.of_nat n) cf ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia)) as (x & Hx & _ & -> & _).
unfold ents_below. apply in_map_iff. exists x. split; [reflexivity|].
apply used_below_In. destruct Hx as [Hx0 Hxu]. auto.
Qed.

End a.

Definition dense (ent : list entry) : list Z := map snd ent.
Definition pcols (ent : list entry) : list colour := map fst ent.










(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FMapPositive.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0t.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tabs_rel (idl : Z) (X : lzw_abs) (LC : list Z) (s : lzw_st) : Prop :=
(forall q, 0 <= q < 4096 -> nth (Z.to_nat q) (la_LI X) 0 = zm_get (l_lidx s) q) /\
(forall q, 0 <= q < 4096 -> nth (Z.to_nat q) (la_LM X) 0 = zm_get (l_lmap s) q) /\
(forall q, 0 <= q < 4096 -> nth (Z.to_nat q) LC 0 = zm_get (l_lcol s) q) /\
(forall m c, 1 <= m < la_mp X -> 0 <= c < idl -> nth (Z.to_nat ((m - 1) * idl + c)) (la_TM X) 0 = zm_get (l_tmap s) ((m - 1) * idl + c)) /\
(forall p c, 0 <= p < idl -> 0 <= c < idl -> nth (Z.to_nat (p * idl + c)) (la_TI X) 0 = zm_get (l_init s) (p * idl + c)) /\
la_dp X = l_dictPos s /\ la_mp X = l_mapPos s.
Lemma child_abs_model : forall idl X LC s q c,
tabs_rel idl X LC s -> 0 <= q < 4096 -> 0 <= c < idl -> nth (Z.to_nat q) (la_LM X) 0 < la_mp X -> 0 <= nth (Z.to_nat q) (la_LM X) 0 ->
child_abs idl X LC q c = lzw_child idl q c s.
Proof.
intros idl X LC s q c (RLI & RLM & RLC & RTM & _) Hq Hc Hlt H0.
unfold child_abs, lzw_child. rewrite (RLI q Hq), (RLC q Hq), <- (RLM q Hq).
destruct (negb (zm_get (l_lidx s) q =? 0) && (zm_get (l_lcol s) q =? c)); [reflexivity|].
destruct (Z.eqb_spec (nth (Z.to_nat q) (la_LM X) 0) 0) as [E | NE]; [reflexivity|].
apply RTM; lia.
Qed.
Lemma init_child_model : forall idl X LC s p c,
tabs_rel idl X LC s -> 0 <= p < idl -> 0 <= c < idl -> nth (Z.to_nat (p * idl + c)) (la_TI X) 0 = zm_get (l_init s) (p * idl + c).
Proof. intros idl X LC s p c (_ & _ & _ & _ & RTI & _) Hp Hc. exact (RTI p c Hp Hc). Qed.
Lemma zkey_inj : forall a b, 0 <= a -> 0 <= b -> zkey a = zkey b -> a = b.
Proof. intros a b Ha Hb H. unfold zkey in H. apply Z2Pos.inj in H; lia. Qed.
Lemma zm_get_set : forall m k v k', 0 <= k -> 0 <= k' -> zm_get (zm_set m k v) k' = if k' =? k then v else zm_get m k'.
Proof.
intros m k v k' Hk Hk'. unfold zm_get, zm_set. destruct (Z.eqb_spec k' k) as [-> | NE].
- rewrite PositiveMapAdditionalFacts.gsspec. destruct (PositiveMap.E.eq_dec (zkey k) (zkey k)) as [_ | N]; [reflexivity | exfalso; apply N; reflexivity].
- rewrite PositiveMapAdditionalFacts.gsspec. destruct (PositiveMap.E.eq_dec (zkey k') (zkey k)) as [E | _]; [exfalso; apply NE; apply zkey_inj; assumption | reflexivity].
Qed.
Lemma tabs_rel_add_init : forall idl X LC s p c,
tabs_rel idl X LC s -> 0 < idl -> 0 <= p < idl -> 0 <= c < idl -> (Z.to_nat (p * idl + c) < length (la_TI X))%nat ->
tabs_rel idl (mkLA (updn (la_TI X) (Z.to_nat (p * idl + c)) (la_dp X)) (la_LM X) (la_LI X) (la_TM X) (la_s X + 1) (la_lp X + 1) (la_dp X + 1) (la_mp X) (la_Cn X + 1) (la_R X))
LC (lzw_add_init idl p c (lzw_emit p s)).
Proof.
intros idl X LC s p c (RLI & RLM & RLC & RTM & RTI & Edp & Emp) Hidl Hp Hc Hlen.
unfold tabs_rel, lzw_add_init, lzw_emit. cbn [la_TI la_LM la_LI la_TM la_dp la_mp l_init l_lmap l_lcol l_lidx l_tmap l_dictPos l_mapPos].
split; [exact RLI|]. split; [exact RLM|]. split; [exact RLC|]. split; [exact RTM|]. split; [|split; [rewrite Edp; reflexivity | exact Emp]].
intros p' c' Hp' Hc'. assert (K0 : 0 <= p * idl + c) by nia. assert (K0' : 0 <= p' * idl + c') by nia.
rewrite zm_get_set by assumption. rewrite nth_updn.
destruct (Z.eqb_spec (p' * idl + c') (p * idl + c)) as [E | NE].
- rewrite E, Nat.eqb_refl. cbn [andb]. apply Nat.ltb_lt in Hlen. rewrite Hlen. exact Edp.
- replace (Nat.eqb (Z.to_nat (p' * idl + c')) (Z.to_nat (p * idl + c))) with false by (symmetry; apply Nat.eqb_neq; intros Q; apply NE; apply Z2Nat.inj in Q; lia).
cbn [andb]. exact (RTI p' c' Hp' Hc').
Qed.
Lemma tabs_rel_add_first_child : forall idl X LC s q c,
tabs_rel idl X LC s -> 0 <= q < 4096 -> (Z.to_nat q < length (la_LI X))%nat -> (Z.to_nat q < length LC)%nat ->
nth (Z.to_nat q) (la_LM X) 0 = 0 -> nth (Z.to_nat q) (la_LI X) 0 = 0 ->
tabs_rel idl (mkLA (la_TI X) (la_LM X) (updn (la_LI X) (Z.to_nat q) (la_dp X)) (la_TM X) (la_s X + 1) (la_lp X + 1) (la_dp X + 1) (la_mp X) (la_Cn X + 1) (la_R X))
(updn LC (Z.to_nat q) c) (lzw_add_child idl q c (lzw_emit q s)).
Proof.
intros idl X LC s q c (RLI & RLM & RLC & RTM & RTI & Edp & Emp) Hq HlenLI HlenLC HLM0 HLI0.
unfold tabs_rel, lzw_add_child, lzw_emit. cbn [la_TI la_LM la_LI la_TM la_dp la_mp l_init l_lmap l_lcol l_lidx l_tmap l_dictPos l_mapPos].
rewrite <- (RLM q Hq), HLM0, <- (RLI q Hq), HLI0. cbn [Z.eqb]. cbn [l_init l_lmap l_lcol l_lidx l_tmap l_dictPos l_mapPos].
split; [|split; [exact RLM|split; [|split; [exact RTM|split; [exact RTI|split; [rewrite Edp; reflexivity | exact Emp]]]]]].
- intros q' Hq'. rewrite zm_get_set by lia. rewrite nth_updn. destruct (Z.eqb_spec q' q) as [-> | NE].
+ rewrite Nat.eqb_refl. apply Nat.ltb_lt in HlenLI. rewrite HlenLI. exact Edp.
+ replace (Nat.eqb (Z.to_nat q') (Z.to_nat q)) with false by (symmetry; apply Nat.eqb_neq; intros Q; apply NE; apply Z2Nat.inj in Q; lia). exact (RLI q' Hq').
- intros q' Hq'. rewrite zm_get_set by lia. rewrite nth_updn. destruct (Z.eqb_spec q' q) as [-> | NE].
+ rewrite Nat.eqb_refl. apply Nat.ltb_lt in HlenLC. rewrite HlenLC. reflexivity.
+ replace (Nat.eqb (Z.to_nat q') (Z.to_nat q)) with false by (symmetry; apply Nat.eqb_neq; intros Q; apply NE; apply Z2Nat.inj in Q; lia). exact (RLC q' Hq').
Qed.

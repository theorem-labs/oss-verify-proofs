(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM02 YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO0u YO10 YO12 YO14 YO0t YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN25 YN26 YN2q YN2o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma bind_eval {T1 T2} (m : M T1) (k : T1 -> M T2) s a s1 :
m s = IRet (a, s1) -> bind m k s = k a s1.
Proof. intros E. unfold bind. rewrite E. reflexivity. Qed.
Lemma ret_eval {T} (a : T) s : ret a s = IRet (a, s). Proof. reflexivity. Qed.
Lemma get_eval s : get s = IRet (s, s). Proof. reflexivity. Qed.
Lemma modify_eval f s : modify f s = IRet (tt, f s). Proof. reflexivity. Qed.
Lemma getm_eval s p am : MT s p = Some (MUsed am) -> getm p s = IRet (am, s).
Proof. intros H. unfold getm. rewrite (bind_eval _ _ s s s eq_refl). unfold MT in H. rewrite H. reflexivity. Qed.
Lemma setm_eval s p am : setm p am s = IRet (tt, upd_meta p (MUsed am) s).
Proof. reflexivity. Qed.
Lemma get_links_eval s p x : MT s p = Some x -> get_links p s = IRet (links_of x, s).
Proof. intros H. unfold get_links. rewrite (bind_eval _ _ s s s eq_refl). unfold MT in H. rewrite H. reflexivity. Qed.
Lemma set_links_eval s p x pr nx : MT s p = Some x -> set_links p pr nx s = IRet (tt, upd_meta p (with_links x pr nx) s).
Proof. intros H. unfold set_links. rewrite (bind_eval _ _ s s s eq_refl). unfold MT in H. rewrite H. reflexivity. Qed.
Lemma get_head_active_eval s sc : get_head (HActive sc) s = IRet (active_hd s sc, s).
Proof. reflexivity. Qed.
Lemma set_head_active_eval s sc v :
set_head (HActive sc) v s = IRet (tt, set_active (lupd (st_active s) (Z.to_nat sc) v) s).
Proof. reflexivity. Qed.
Lemma massert_true b site s : b = true -> massert b site s = IRet (tt, s).
Proof. intros ->. reflexivity. Qed.
Lemma upd_meta_set_active g x l s : upd_meta g x (set_active l s) = set_active l (upd_meta g x s).
Proof. reflexivity. Qed.
Lemma mupdate_comm l g x h y :
g <> h -> mlookup l g <> None -> mupdate (mupdate l h y) g x = mupdate (mupdate l g x) h y.
Proof.
intros Hne. induction l as [|[q z] t IH]; cbn; intros Hg.
- exfalso. exact (Hg eq_refl).
- destruct (sptr_eqb h q) eqn:E1; destruct (sptr_eqb g q) eqn:E2; cbn; rewrite ?E1, ?E2; try reflexivity.
+ apply sptr_eqb_eq in E1. apply sptr_eqb_eq in E2. exfalso. apply Hne. congruence.
+ rewrite IH; [reflexivity|]. exact Hg.
Qed.
Lemma upd_meta_comm g x h y s : g <> h -> MT s g <> None -> upd_meta g x (upd_meta h y s) = upd_meta h y (upd_meta g x s).
Proof. intros Hne Hg. unfold upd_meta, set_metas. cbn. f_equal. apply mupdate_comm; assumption. Qed.
Lemma active_hd_upd_meta s g x sc : active_hd (upd_meta g x s) sc = active_hd s sc.
Proof. reflexivity. Qed.
Lemma MT_set_active l s p : MT (set_active l s) p = MT s p.
Proof. reflexivity. Qed.
Section e.
Variables (f : nat) (A : astate) (g : sptr) (i : Z) (am : ameta).
Hypothesis Hg : MT A g = Some (MUsed am).
Definition am_lk (pr nx : sptr) : ameta := am_set_links (Some pr) (Some nx) am.
Definition am_B' (pr nx : sptr) : ameta := am_set_freed (Z.lor (am_freed am) (bit i)) (am_lk pr nx).
Definition act_g : list (option sptr) := lupd (st_active A) (Z.to_nat (am_sc am)) (Some g).
Definition A_B3 : astate := upd_meta g (MUsed (am_B' g g)) (set_active act_g A).
Lemma nt_TB_B3 :
nt_mask am = 0 -> (am_sc am) < 48 -> active_hd A (am_sc am) = None -> am_prev am = None -> am_next am = None ->
nt_TB A g i am = IRet (None, A_B3).
Proof.
intros Hm Hsc Hhd Hp Hn. unfold nt_TB, nt_preB. rewrite Hm. cbn [Z.eqb].
erewrite (bind_eval (bind _ _) _ A).
2:{ erewrite (bind_eval _ _ A) by (apply massert_true; apply Z.ltb_lt; exact Hsc).
erewrite (bind_eval _ _ A) by apply get_head_active_eval.
rewrite Hhd. cbn [osptr_eqb].
unfold queue. erewrite (bind_eval _ _ A) by (apply (get_links_eval A g (MUsed am)); exact Hg).
cbn [links_of fst snd]. rewrite Hp, Hn. cbn [osptr_eqb andb].
erewrite (bind_eval _ _ A) by reflexivity.
erewrite (bind_eval _ _ A) by apply get_head_active_eval. rewrite Hhd.
erewrite (bind_eval _ _ A) by (apply set_links_eval; exact Hg).
apply set_head_active_eval. }
unfold nt_setfreed.
erewrite (bind_eval (getm g) _ _).
2:{ apply getm_eval. rewrite MT_set_active, MT_upd_same. reflexivity. }
erewrite (bind_eval (setm g _) _ _) by apply setm_eval. unfold ret. f_equal. f_equal.
unfold A_B3, act_g. cbn [st_active upd_meta set_metas set_active with_links].
rewrite <- upd_meta_set_active, upd_meta_twice. reflexivity.
Qed.
Variables (h hp : sptr) (ah ahp : ameta).
Hypothesis Hhg : h <> g.
Hypothesis Mh : MT A h = Some (MUsed ah).
Hypothesis Ehp : am_prev ah = Some hp.
Definition ah_a : ameta := am_set_links (Some g) (Some g) ah.
Definition A_B4a : astate := upd_meta g (MUsed (am_B' h h)) (upd_meta h (MUsed ah_a) A).
Lemma NN p q z (s0 : astate) : MT s0 p <> None -> MT (upd_meta q z s0) p <> None.
Proof. intros Hp0. rewrite MT_upd. destruct (sptr_eqb p q); [discriminate | exact Hp0]. Qed.
Lemma Ng : MT A g <> None. Proof. rewrite Hg. discriminate. Qed.
Lemma Nh : MT A h <> None. Proof. rewrite Mh. discriminate. Qed.
Lemma Hgh : g <> h. Proof. intros E. exact (Hhg (eq_sym E)). Qed.
Lemma nt_TB_B4a :
nt_mask am = 0 -> (am_sc am) < 48 -> active_hd A (am_sc am) = Some h -> am_prev am = None -> am_next am = None -> hp = h ->
nt_TB A g i am = IRet (None, A_B4a).
Proof.
intros Hm Hsc Hhd Hp Hn Ehph. unfold nt_TB, nt_preB. rewrite Hm. cbn [Z.eqb].
pose proof Ng as Ng'. pose proof Nh as Nh'. pose proof Hgh as Hgh'.
assert (Ehp' : am_prev ah = Some h) by (rewrite Ehp, Ehph; reflexivity). clear Ehph.
erewrite (bind_eval (bind _ _) _ A).
2:{ erewrite (bind_eval _ _ A) by (apply massert_true; apply Z.ltb_lt; exact Hsc).
erewrite (bind_eval _ _ A) by apply get_head_active_eval.
rewrite Hhd. cbn [osptr_eqb]. replace (sptr_eqb h g) with false by (symmetry; apply sptr_eqb_neq; exact Hhg).
unfold queue. erewrite (bind_eval _ _ A) by (apply (get_links_eval A g (MUsed am)); exact Hg).
cbn [links_of fst snd]. rewrite Hp, Hn. cbn [osptr_eqb andb].
erewrite (bind_eval _ _ A) by reflexivity.
erewrite (bind_eval _ _ A) by apply get_head_active_eval. rewrite Hhd.
erewrite (bind_eval _ _ A) by (apply (get_links_eval A h (MUsed ah)); exact Mh).
cbn [links_of fst]. rewrite Ehp'.
erewrite (bind_eval _ _ A) by (apply set_links_eval; exact Hg).
unfold set_next. erewrite (bind_eval (bind _ _) _ _).
2:{ erewrite (bind_eval _ _ _) by (apply (get_links_eval _ h (MUsed ah)); rewrite MT_upd_other by exact Hhg; exact Mh).
cbn [links_of fst]. rewrite Ehp'. apply set_links_eval. rewrite MT_upd_other by exact Hhg. exact Mh. }
unfold set_prev. erewrite (bind_eval _ _ _) by (apply get_links_eval; apply MT_upd_same).
cbn [links_of with_links snd]. apply set_links_eval. apply MT_upd_same. }
unfold nt_setfreed.
erewrite (bind_eval (getm g) _ _).
2:{ apply getm_eval. rewrite !MT_upd_other by exact Hgh'. apply MT_upd_same. }
erewrite (bind_eval (setm g _) _ _) by apply setm_eval. unfold ret. f_equal. f_equal.
unfold A_B4a, ah_a, am_B', am_lk. cbn [with_links]. rewrite upd_meta_twice.
rewrite (upd_meta_comm h _ g) by auto using NN. rewrite upd_meta_twice.
cbn [am_freed am_next am_prev am_set_links am_set_freed]. reflexivity.
Qed.
Hypothesis Mhp : MT A hp = Some (MUsed ahp).
Definition ahp_b : ameta := am_set_links (am_prev ahp) (Some g) ahp.
Definition ah_b : ameta := am_set_links (Some g) (am_next ah) ah.
Definition A_B4b : astate := upd_meta g (MUsed (am_B' hp h)) (upd_meta h (MUsed ah_b) (upd_meta hp (MUsed ahp_b) A)).
Lemma Nhp : MT A hp <> None. Proof. rewrite Mhp. discriminate. Qed.
Lemma nt_TB_B4b :
nt_mask am = 0 -> (am_sc am) < 48 -> active_hd A (am_sc am) = Some h -> am_prev am = None -> am_next am = None -> hp <> h -> hp <> g ->
nt_TB A g i am = IRet (None, A_B4b).
Proof.
intros Hm Hsc Hhd Hp Hn Hph Hpg. unfold nt_TB, nt_preB. rewrite Hm. cbn [Z.eqb].
pose proof Ng as Ng'. pose proof Nh as Nh'. pose proof Nhp as Nhp'. pose proof Hgh as Hgh'.
assert (Hhp : h <> hp) by (intros E; exact (Hph (eq_sym E))). assert (Hgp : g <> hp) by (intros E; exact (Hpg (eq_sym E))).
erewrite (bind_eval (bind _ _) _ A).
2:{ erewrite (bind_eval _ _ A) by (apply massert_true; apply Z.ltb_lt; exact Hsc).
erewrite (bind_eval _ _ A) by apply get_head_active_eval.
rewrite Hhd. cbn [osptr_eqb]. replace (sptr_eqb h g) with false by (symmetry; apply sptr_eqb_neq; exact Hhg).
unfold queue. erewrite (bind_eval _ _ A) by (apply (get_links_eval A g (MUsed am)); exact Hg).
cbn [links_of fst snd]. rewrite Hp, Hn. cbn [osptr_eqb andb].
erewrite (bind_eval _ _ A) by reflexivity.
erewrite (bind_eval _ _ A) by apply get_head_active_eval. rewrite Hhd.
erewrite (bind_eval _ _ A) by (apply (get_links_eval A h (MUsed ah)); exact Mh).
cbn [links_of fst]. rewrite Ehp.
erewrite (bind_eval _ _ A) by (apply set_links_eval; exact Hg).
unfold set_next. erewrite (bind_eval (bind _ _) _ _).
2:{ erewrite (bind_eval _ _ _) by (apply (get_links_eval _ hp (MUsed ahp)); rewrite MT_upd_other by exact Hpg; exact Mhp).
cbn [links_of fst]. apply (set_links_eval _ hp (MUsed ahp)). rewrite MT_upd_other by exact Hpg. exact Mhp. }
unfold set_prev. erewrite (bind_eval _ _ _).
2:{ apply (get_links_eval _ h (MUsed ah)). rewrite MT_upd_other by exact Hhp. rewrite MT_upd_other by exact Hhg. exact Mh. }
cbn [links_of with_links snd]. apply (set_links_eval _ h (MUsed ah)).
rewrite MT_upd_other by exact Hhp. rewrite MT_upd_other by exact Hhg. exact Mh. }
unfold nt_setfreed.
erewrite (bind_eval (getm g) _ _).
2:{ apply getm_eval. rewrite MT_upd_other by exact Hgh'. rewrite MT_upd_other by exact Hgp. apply MT_upd_same. }
erewrite (bind_eval (setm g _) _ _) by apply setm_eval. unfold ret. f_equal. f_equal.
unfold A_B4b, ahp_b, ah_b, am_B', am_lk. cbn [with_links].
rewrite (upd_meta_comm hp _ g) by auto 10 using NN. rewrite (upd_meta_comm h _ g) by auto 10 using NN. rewrite upd_meta_twice.
cbn [am_freed am_next am_prev am_set_links am_set_freed]. reflexivity.
Qed.
End e.
Inductive bpathM := MP0 | MP1V1 | MP1V2 | MP2V2.
Inductive bvarM := MVB1 | MVB2 | MVB3 | MVB4a | MVB4b.
Definition validBM (p : bpathM) (v : bvarM) : bool :=
match p, v with
| MP0, _ => true
| MP1V2, MVB1 | MP2V2, MVB1 => true
| MP1V1, MVB2 => true
| _, _ => false
end.
Section n.
Variables (X : list sptr) (U : Z -> Z) (A : astate) (g : sptr) (i : Z) (am : ameta).
Hypothesis HI : Inv X (Some (g, i)) U A.
Hypothesis Hu : usedX X A g am.
Hypothesis HR2g : (am_prev am, am_next am) <> (None, None) -> active_hd A (am_sc am) <> Some g -> am_freed am <> 0.
Hypothesis HC1 : nt_C1 A g i am = false.
Definition okay_false : Prop :=
nt_mask am + bit i = ones (am_last am) /\ 0 < am_maplen am /\ am_next am = Some g /\
7 <= am_sc am <= 38 /\ 100 <= znth (am_sc am - 7) (st_bounces A).
Definition pfacts (p : bpathM) : Prop :=
match p with
| MP0 => nt_mask am + bit i <> ones (am_last am)
| MP1V1 => okay_false /\ am_last am = 0 /\ class_size (am_sc am) <= am_maplen am * 4096 - UNIT /\
usage_of A (am_sc am) < 9 * (am_last am + 1)
| MP1V2 => okay_false /\ am_last am <> 0 /\ usage_of A (am_sc am) < 9 * (am_last am + 1)
| MP2V2 => okay_false /\ am_last am <> 0 /\ 9 * (am_last am + 1) <= usage_of A (am_sc am) /\ 18 < am_last am
end.
Definition vfacts (v : bvarM) (h hp : sptr) (ah ahp : ameta) : Prop :=
match v with
| MVB1 => nt_mask am <> 0
| MVB2 => nt_mask am = 0 /\ active_hd A (am_sc am) = Some g
| MVB3 => nt_mask am = 0 /\ active_hd A (am_sc am) = None /\ am_prev am = None /\ am_next am = None
| MVB4a => nt_mask am = 0 /\ active_hd A (am_sc am) = Some h /\ h <> g /\ am_prev am = None /\ am_next am = None /\
usedX X A h ah /\ am_sc ah = am_sc am /\ am_prev ah = Some h /\ hp = h
| MVB4b => nt_mask am = 0 /\ active_hd A (am_sc am) = Some h /\ h <> g /\ am_prev am = None /\ am_next am = None /\
usedX X A h ah /\ am_sc ah = am_sc am /\ am_prev ah = Some hp /\ hp <> h /\ hp <> g /\
usedX X A hp ahp /\ am_sc ahp = am_sc am
end.
Lemma sc48 : 0 <= am_sc am < 48.
Proof. exact (proj1 (else_branch_facts X U A g i am HI Hu HC1)). Qed.
Lemma mask_facts :
0 <= i <= am_last am /\ 0 <= am_last am <= 31 /\ 0 <= nt_mask am /\
Z.testbit (nt_mask am) i = false /\
(nt_mask am = 0 -> nt_mask am + bit i = ones (am_last am) -> am_last am = 0) /\
(am_last am = 0 -> nt_mask am = 0).
Proof.
destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & _ & Hal). pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
pose proof (inv_groups HI g am Hu) as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & _) & _).
assert (Hbit : Z.testbit (nt_mask am) i = false).
{ unfold allocated in Hal. unfold nt_mask. rewrite Z.lor_comm. destruct (Z.testbit (Z.lor (am_avail am) (am_freed am)) i); [discriminate | reflexivity]. }
split; [exact Hi|]. split; [exact Glast|]. split; [unfold nt_mask; apply Z.lor_nonneg; lia|]. split; [exact Hbit|]. split.
- intros Hm E. rewrite Hm in E. unfold bit, ones in E.
destruct (Z.eq_dec (am_last am) 0) as [H0|H0]; [exact H0|]. exfalso.
assert (2 ^ i <= 2 ^ am_last am) by (apply Z.pow_le_mono_r; lia).
assert (2 ^ (am_last am + 1) = 2 * 2 ^ am_last am) by (rewrite Z.pow_add_r, Z.pow_1_r by lia; lia).
assert (2 ^ 1 <= 2 ^ am_last am) by (apply Z.pow_le_mono_r; lia). change (2 ^ 1) with 2 in *. lia.
- intros H0. unfold nt_mask. apply mask_zero_of_bits; [apply Z.lor_nonneg; lia|]. intros j Hj. rewrite Z.lor_spec.
destruct (Z.eq_dec j 0) as [->|Hne].
+ assert (i = 0) as Hi0 by lia. rewrite Hi0 in Hbit. unfold nt_mask in Hbit. rewrite Z.lor_spec in Hbit. exact Hbit.
+ destruct (Gabove j ltac:(lia)) as [A1 B1]. rewrite A1, B1. reflexivity.
Qed.
Theorem ntB_cases :
exists p v h hp ah ahp, validBM p v = true /\ pfacts p /\ vfacts v h hp ah ahp.
Proof.
pose proof sc48 as Hsc. pose proof mask_facts as (Hi & Hlast & Hm0 & Hbit & HL0 & HM0).
pose proof (inv_groups HI g am Hu) as (_ & Gml & _ & Gcl & _).
destruct (inv_rings HI) as (_ & AR & _). destruct (AR (am_sc am) Hsc) as (ms & Rg & Mem & Full & Q1 & Q2).
assert (V : exists v h hp ah ahp, vfacts v h hp ah ahp /\
match v with MVB1 => nt_mask am <> 0 | _ => nt_mask am = 0 end /\
match v with MVB3 | MVB4a | MVB4b => am_next am = None | _ => True end).
{ destruct (Z.eq_dec (nt_mask am) 0) as [Hm|Hm].
2:{ exists MVB1, g, g, am, am. cbn. auto. }
assert (Hfr0 : am_freed am = 0) by (unfold nt_mask in Hm; apply Z.lor_eq_0_iff in Hm; exact (proj1 Hm)).
destruct (active_hd A (am_sc am)) as [h|] eqn:Ehd.
- destruct (sptr_eq_dec h g) as [->|Hhg].
+ exists MVB2, g, g, am, am. cbn. auto.
+ assert (Hunl : am_prev am = None /\ am_next am = None).
{ destruct (am_prev am) eqn:Ep; destruct (am_next am) eqn:En; auto; exfalso; (apply HR2g; [discriminate | congruence | exact Hfr0]). }
destruct Hunl as [Hp Hn].
destruct (ring_head_In _ _ _ Rg) as [Hhin _].
destruct (ring_members_used _ _ _ _ _ _ Rg Hhin) as (ah & Uh & Sh).
destruct (ring_head_links _ _ _ _ _ _ Rg Uh) as (rest & Ems & Hpr & Hnx).
set (hp := last rest h) in *.
assert (Hpin : In hp ms) by (rewrite Ems; subst hp; destruct rest as [|r0 rest']; [left; reflexivity | right; apply In_last; discriminate]).
destruct (ring_members_used _ _ _ _ _ _ Rg Hpin) as (ahp & Uhp & Shp).
destruct (sptr_eq_dec hp h) as [E|Hph].
* exists MVB4a, h, h, ah, ahp. cbn. rewrite E in Hpr. repeat split; auto.
* assert (Hpg : hp <> g).
{ intros E. apply (Mem g am Hu eq_refl); [rewrite <- E; exact Hpin | rewrite Hp, Hn; reflexivity]. }
exists MVB4b, h, hp, ah, ahp. cbn. repeat split; auto.
- assert (Hunl : am_prev am = None /\ am_next am = None).
{ destruct (am_prev am) eqn:Ep; destruct (am_next am) eqn:En; auto; exfalso; (apply HR2g; [discriminate | congruence | exact Hfr0]). }
destruct Hunl as [Hp Hn]. exists MVB3, g, g, am, am. cbn. auto. }
destruct V as (v & h & hp & ah & ahp & Vf & Vm & Vn).
unfold nt_C1 in HC1. destruct (nt_mask am + bit i =? ones (am_last am)) eqn:Eall.
- apply Z.eqb_eq in Eall. cbn [andb] in HC1.
unfold okay_to_free in HC1.
destruct (48 <=? am_sc am) eqn:E48; [apply Z.leb_le in E48; lia|].
destruct (stride_of am <? class_size (am_sc am)) eqn:Estr; [discriminate|]. cbn [orb] in HC1. apply Z.ltb_ge in Estr.
destruct (am_maplen am =? 0) eqn:Eml; [discriminate|]. apply Z.eqb_neq in Eml.
destruct (osptr_eqb (am_next am) (Some g)) eqn:Enx; [|discriminate]. cbn [negb] in HC1.
assert (Hnx : am_next am = Some g) by (destruct (am_next am) as [q|]; [cbn in Enx; apply sptr_eqb_eq in Enx; congruence | discriminate]).
unfold is_bouncing, bounce_idx in HC1.
destruct ((7 <=? am_sc am) && (am_sc am <? 39)) eqn:Eb; [|discriminate].
apply andb_prop in Eb as [Eb1 Eb2]. apply Z.leb_le in Eb1. apply Z.ltb_lt in Eb2.
destruct (100 <=? znth (am_sc am - 7) (st_bounces A)) eqn:Ebn; [|discriminate]. apply Z.leb_le in Ebn. cbn [negb] in HC1.
assert (OKF : okay_false) by (unfold okay_false; repeat split; auto; lia).
assert (Hv : v = MVB1 \/ (v = MVB2 /\ am_last am = 0)).
{ destruct v; [left; reflexivity | right; split; [reflexivity | apply HL0; auto] | | |]; exfalso; rewrite Hnx in Vn; discriminate. }
destruct Hv as [-> | [-> L0]].
+ assert (HL : am_last am <> 0) by (intros L0; apply Vm; apply HM0; exact L0).
destruct (Z_lt_dec (usage_of A (am_sc am)) (9 * (am_last am + 1))) as [LT|GE].
* exists MP1V2, MVB1, h, hp, ah, ahp. cbn [validBM pfacts]. auto.
* exists MP2V2, MVB1, h, hp, ah, ahp. cbn [validBM pfacts].
destruct (am_last am + 1 <? 20) eqn:E20.
{ exfalso. apply Z.ltb_lt in E20. replace (9 * (am_last am + 1) <=? usage_of A (am_sc am)) with true in HC1 by (symmetry; apply Z.leb_le; lia). discriminate. }
apply Z.ltb_ge in E20. split; [reflexivity|]. split; [|exact Vf]. split; [exact OKF|]. lia.
+ exists MP1V1, MVB2, h, hp, ah, ahp. cbn [validBM pfacts].
assert (LT : usage_of A (am_sc am) < 9 * (am_last am + 1)).
{ rewrite L0 in HC1 |- *. destruct (9 * (0 + 1) <=? usage_of A (am_sc am)) eqn:E9; [cbn in HC1; discriminate | apply Z.leb_gt in E9; lia]. }
unfold stride_of in Estr. rewrite L0 in Estr. cbn [Z.eqb andb] in Estr.
replace (am_maplen am =? 0) with false in Estr by (symmetry; apply Z.eqb_neq; exact Eml). cbn [negb] in Estr.
split; [reflexivity|]. split; [|exact Vf]. split; [exact OKF|]. lia.
- exists MP0, v, h, hp, ah, ahp. cbn [validBM pfacts]. split; [destruct v; reflexivity|]. split; [apply Z.eqb_neq; exact Eall | exact Vf].
Qed.
End n.
Definition grp_same (a a' : ameta) : Prop :=
am_mem a' = am_mem a /\ am_last a' = am_last a /\ am_sc a' = am_sc a /\ am_maplen a' = am_maplen a /\
am_aidx a' = am_aidx a /\ am_slots a' = am_slots a.
Lemma grp_same_links pr nx a : grp_same a (am_set_links pr nx a).
Proof. destruct a; repeat split; reflexivity. Qed.
Lemma grp_same_freed v a : grp_same a (am_set_freed v a).
Proof. destruct a; repeat split; reflexivity. Qed.
Lemma grp_same_avail v a : grp_same a (am_set_avail v a).
Proof. destruct a; repeat split; reflexivity. Qed.
Lemma grp_same_trans a b c : grp_same a b -> grp_same b c -> grp_same a c.
Proof. unfold grp_same. intros (?&?&?&?&?&?) (?&?&?&?&?&?). repeat split; congruence. Qed.
Lemma group_cells_same q a a' : grp_same a a' -> group_cells q a' = group_cells q a.
Proof. destruct a, a'. intros (E1 & E2 & E3 & E4 & E5 & E6). cbn in E1, E2, E3, E4, E5, E6. subst. reflexivity. Qed.
Lemma group_tail_cells_same a a' : grp_same a a' -> group_tail_cells a' = group_tail_cells a.
Proof. destruct a, a'. intros (E1 & E2 & E3 & E4 & E5 & E6). cbn in E1, E2, E3, E4, E5, E6. subst. reflexivity. Qed.
Lemma used_metasX_upd X s q a a' :
MT s q = Some (MUsed a) ->
exists u1 u2, used_metasX X s = u1 ++ (if memb q X then [] else [(q, a)]) ++ u2 /\
used_metasX X (upd_meta q (MUsed a') s) = u1 ++ (if memb q X then [] else [(q, a')]) ++ u2.
Proof.
intros Mq. destruct (used_metas_upd s q a Mq) as (v1 & v2 & E1 & E2).
unfold used_metasX. rewrite E1, (E2 a'), !filter_app. cbn [List.filter fst].
exists (List.filter (fun gm : sptr * ameta => negb (memb (fst gm) X)) v1), (List.filter (fun gm : sptr * ameta => negb (memb (fst gm) X)) v2).
destruct (memb q X); split; reflexivity.
Qed.
Lemma imageX_upd_meta X s q a a' c :
MT s q = Some (MUsed a) -> grp_same a a' ->
In c (imageX X (upd_meta q (MUsed a') s)) -> In c (meta_slot_cells q (Some (MUsed a'))) \/ In c (imageX X s).
Proof.
intros Mq Hs Hc. unfold imageX in *. rewrite ctx_cells_upd_meta in Hc.
change (st_areas (upd_meta q (MUsed a') s)) with (st_areas s) in Hc.
apply in_app_iff in Hc as [Hc|Hc]; [right; apply in_app_iff; left; exact Hc|].
apply in_app_iff in Hc as [Hc|Hc].
- destruct (areas_cells_upd s q (MUsed a') (st_areas s) c Hc) as [H|H]; [right | left; exact H].
apply in_app_iff. right. apply in_app_iff. left. exact H.
- right. apply in_app_iff. right. apply in_app_iff. right.
destruct (used_metasX_upd X s q a a' Mq) as (u1 & u2 & E1 & E2). rewrite E2 in Hc. rewrite E1.
rewrite !flat_map_app in *. apply in_app_iff in Hc as [H|Hc]; [apply in_app_iff; left; exact H|].
apply in_app_iff. right. apply in_app_iff in Hc as [H|H]; apply in_app_iff; [left | right; exact H].
destruct (memb q X); [destruct H|]. cbn [flat_map fst snd] in *. rewrite (group_cells_same q a a' Hs) in H. exact H.
Qed.
Lemma tail_cellsX_upd_meta X s q a a' c :
MT s q = Some (MUsed a) -> grp_same a a' ->
In c (tail_cellsX X (upd_meta q (MUsed a') s)) -> In c (tail_cellsX X s).
Proof.
intros Mq Hs Hc. unfold tail_cellsX in *.
destruct (used_metasX_upd X s q a a' Mq) as (u1 & u2 & E1 & E2). rewrite E2 in Hc. rewrite E1.
rewrite !flat_map_app in *. apply in_app_iff in Hc as [H|Hc]; [apply in_app_iff; left; exact H|].
apply in_app_iff. right. apply in_app_iff in Hc as [H|H]; apply in_app_iff; [left | right; exact H].
destruct (memb q X); [destruct H|]. cbn [flat_map fst snd] in *. rewrite (group_tail_cells_same a a' Hs) in H. exact H.
Qed.
Definition act_cell (k : nat) (v : option sptr) : mcell := MCell (LCtx (CTX_active + 8 * Z.of_nat k)) 8 (optr v).
Lemma ctx_cells_set_active s k v c :
(k < length (st_active s))%nat ->
In c (ctx_cells (set_active (lupd (st_active s) k v) s)) -> c = act_cell k v \/ In c (ctx_cells s).
Proof.
intros Hk Hc. unfold ctx_cells in *. cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage st_unmap_seq st_bounces set_active] in Hc.
apply in_app_iff in Hc as [H|Hc]; [right; apply in_app_iff; left; exact H|].
apply in_app_iff in Hc as [H|Hc]; [| right; apply in_app_iff; right; apply in_app_iff; right; exact Hc].
apply in_map_iff in H as (j & <- & Hj). rewrite nth_lupd.
destruct (Nat.eqb j k) eqn:E.
- apply Nat.eqb_eq in E. subst j. replace (Nat.ltb k (length (st_active s))) with true by (symmetry; apply Nat.ltb_lt; exact Hk). cbn [andb]. left. reflexivity.
- cbn [andb]. right. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists j. auto.
Qed.
Lemma act_cell_In s k v : (k < 48)%nat -> length (st_active s) = 48%nat -> In (act_cell k v) (ctx_cells (set_active (lupd (st_active s) k v) s)).
Proof.
intros Hk Hlen. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists k.
cbn [st_active set_active]. rewrite nth_lupd, Nat.eqb_refl, Hlen. replace (Nat.ltb k 48) with true by (symmetry; apply Nat.ltb_lt; exact Hk).
split; [reflexivity|]. apply in_seq. lia.
Qed.
Lemma areas_cells_ext' s s' l : st_metas s' = st_metas s -> areas_cells s' l = areas_cells s l.
Proof. intros E. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH. f_equal. unfold area_cells. rewrite E. reflexivity. Qed.
Lemma used_metasX_set_active X l s : used_metasX X (set_active l s) = used_metasX X s.
Proof. reflexivity. Qed.
Lemma imageX_set_active X s k v c :
(k < length (st_active s))%nat ->
In c (imageX X (set_active (lupd (st_active s) k v) s)) -> c = act_cell k v \/ In c (imageX X s).
Proof.
intros Hk Hc. unfold imageX in *. rewrite used_metasX_set_active, (areas_cells_ext' s) in Hc by reflexivity.
change (st_areas (set_active (lupd (st_active s) k v) s)) with (st_areas s) in Hc.
apply in_app_iff in Hc as [Hc|Hc].
- destruct (ctx_cells_set_active s k v c Hk Hc) as [H|H]; [left; exact H | right; apply in_app_iff; left; exact H].
- right. apply in_app_iff. right. exact Hc.
Qed.
Lemma tail_cellsX_set_active X s l : tail_cellsX X (set_active l s) = tail_cellsX X s.
Proof. reflexivity. Qed.
End d.

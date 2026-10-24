(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s
YO11 YO15 YO12 YO0z YO14 YO0u YO0q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Lemma In_zupd_inv (l : list Z) n v u : In u (zupd l n v) -> u = v \/ In u l.
Proof.
revert n. induction l as [|h t IH]; intros [|n] H; cbn in H; try contradiction.
- destruct H as [<-|H]; [left; reflexivity | right; right; exact H].
- destruct H as [<-|H]; [right; left; reflexivity|]. destruct (IH n H) as [E|Hin]; [left; exact E | right; right; exact Hin].
Qed.
Definition Uadd (U : Z -> Z) (sc d : Z) : Z -> Z := fun c => if c =? sc then U c + d else U c.
Lemma Inv_set_usage X R U s sc v :
Inv X R U s -> 0 <= sc < 48 -> 0 <= v ->
Inv X R (Uadd U sc (v - usage_of s sc)) (set_usage (zset sc v (st_usage s)) s).
Proof.
intros HI Hsc Hv.
set (s' := set_usage (zset sc v (st_usage s)) s).
assert (EU : forall p am, usedX X s' p am <-> usedX X s p am) by (intros; unfold usedX, MTX, MT; subst s'; cbn; tauto).
pose proof (inv_ctx HI) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
eapply (Inv_transfer X X R U _ s s' HI EU eq_refl).
- split; [exact C1|]. split; [subst s'; cbn; rewrite length_zset; exact C2|]. split; [exact C3|]. split; [exact C4|].
split; [|exact (conj C6 (conj C7 C8))].
intros u Hu. subst s'. cbn in Hu. unfold zset in Hu. apply In_zupd_inv in Hu. destruct Hu as [->|Hu]; [lia | apply C5; exact Hu].
- exact (inv_keys HI).
- exact (inv_areas HI).
- exact (inv_X HI).
- exact (inv_rings HI).
- intros c Hc. pose proof (inv_usage HI c Hc) as E. unfold Uadd.
change (class_sum X s' c) with (class_sum X s c).
unfold usage_of in *. subst s'. cbn [st_usage set_usage]. rewrite znth_zset by lia. rewrite C2.
destruct (c =? sc) eqn:Ec; cbn [andb].
+ apply Z.eqb_eq in Ec. subst c. destruct (sc <? Z.of_nat 48) eqn:El; [lia | apply Z.ltb_ge in El; lia].
+ exact E.
Qed.
Lemma itok_set_usage_of sc v s (Q : unit * astate -> Prop) :
Q (tt, set_usage (zset sc v (st_usage s)) s) -> itok (set_usage_of sc v s) Q.
Proof. intros H. exact H. Qed.
Section e.
Variables (X : list sptr) (R' : option (sptr * Z)) (U U' : Z -> Z) (s s' : astate) (m : sptr) (am1 : ameta).
Hypothesis HI : Inv (m :: X) None U s.
Hypothesis NX : memb m X = false.
Hypothesis EM : MT s' m = Some (MUsed am1).
Hypothesis EO : forall q, q <> m -> MT s' q = MT s q.
Hypothesis EK : keys s' = keys s.
Hypothesis ER : st_regions s' = st_regions s.
Hypothesis G1 : group_ok X R' s' m am1.
Hypothesis L1 : forall q a, usedX (m :: X) s q a -> prid (am_mem a) = prid (am_mem am1) ->
spans_disjoint a am1 \/ inside X s' a am1 \/ inside X s' am1 a.
Hypothesis M1 : 0 < am_maplen am1 -> forall q a, usedX (m :: X) s q a -> 0 < am_maplen a ->
prid (am_mem a) <> prid (am_mem am1).
Hypothesis P1 : am_aidx am1 < am_last am1 -> forall q a, usedX (m :: X) s q a -> am_sc a = am_sc am1 ->
am_last a <= am_aidx a.
Hypothesis HR' : reserved_ok X R' s'.
Hypothesis R'm : forall p i, R' = Some (p, i) -> p = m.
Lemma ins_used_bwd q a : usedX X s' q a -> (q = m /\ a = am1) \/ (q <> m /\ usedX (m :: X) s q a).
Proof.
intros Hu. pose proof (usedX_MT _ _ _ _ Hu) as [Mq Xq].
destruct (sptr_eq_dec q m) as [->|Hne].
- left. rewrite EM in Mq. injection Mq as ->. auto.
- right. split; [exact Hne|]. apply usedX_intro.
+ rewrite memb_cons, Xq. destruct (sptr_eqb q m) eqn:E; [apply sptr_eqb_eq in E; contradiction | reflexivity].
+ rewrite <- (EO q Hne). exact Mq.
Qed.
Lemma ins_used_fwd q a : usedX (m :: X) s q a -> q <> m /\ usedX X s' q a.
Proof.
intros Hu. pose proof (usedX_MT _ _ _ _ Hu) as [Mq Xq]. rewrite memb_cons in Xq.
apply orb_false_elim in Xq as [E Xq]. apply sptr_eqb_neq in E.
split; [exact E|]. apply usedX_intro; [exact Xq|]. rewrite (EO q E). exact Mq.
Qed.
Lemma ins_used_m a : usedX X s' m a -> a = am1.
Proof. intros Hu. destruct (ins_used_bwd _ _ Hu) as [[_ E] | [Hne _]]; [exact E | exfalso; exact (Hne eq_refl)]. Qed.
Lemma ins_inside a b : inside (m :: X) s a b -> inside X s' a b.
Proof.
intros (j & fr & c & ac & H1 & H2 & H3 & H4 & H5). exists j, fr, c, ac.
repeat split; try tauto. apply ins_used_fwd. exact H4.
Qed.
Lemma ins_group q a : q <> m -> group_ok (m :: X) None s q a -> group_ok X R' s' q a.
Proof.
intros Hne (Gm & Gml & Gsl & Gcl & Gmp & Gns).
split; [exact Gm|]. split; [exact Gml|]. split.
{ intros i Hi. pose proof (Gsl i Hi) as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|].
destruct (ss_fr (nth_slot a i)) as [fr|].
- destruct S3 as (A1 & A2 & A3 & A4). split; [exact A1|]. split; [|exact (conj A3 A4)].
intros E. apply R'm in E. exact (Hne E).
- left. destruct S3 as [S3|S3]; [exact S3 | discriminate]. }
split.
{ destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & C6) | C]; [left | right; exact C].
repeat split; auto. destruct C6 as [C6|C6]; [discriminate | right; exact C6]. }
split.
{ intros Hm. destruct (Gmp Hm) as (r & rg & H). exists r, rg. unfold region_of in *. rewrite ER. exact H. }
intros Hm. destruct (Gns Hm) as [N63 (g' & b & i' & fr' & Hu & Hrest)].
split; [exact N63|]. exists g', b, i', fr'. split; [apply ins_used_fwd; exact Hu | exact Hrest].
Qed.
Lemma ins_groups : forall q a, usedX X s' q a -> group_ok X R' s' q a.
Proof.
intros q a Hu. destruct (ins_used_bwd _ _ Hu) as [[-> ->] | [Hne Hu0]]; [exact G1|].
apply ins_group; [exact Hne|]. exact (inv_groups HI q a Hu0).
Qed.
Lemma ins_laminar : laminar X s'.
Proof.
intros p1 a1 p2 a2 H1 H2 Hne Hr.
destruct (ins_used_bwd _ _ H1) as [[-> ->] | [N1 U1]]; destruct (ins_used_bwd _ _ H2) as [[-> ->] | [N2 U2]].
- exfalso. exact (Hne eq_refl).
- destruct (L1 _ _ U2 (eq_sym Hr)) as [D | [I | I]].
+ left. unfold spans_disjoint in *. tauto.
+ right; right; exact I.
+ right; left; exact I.
- destruct (L1 _ _ U1 Hr) as [D | [I | I]]; [left; exact D | right; left; exact I | right; right; exact I].
- destruct (inv_laminar HI p1 a1 p2 a2 U1 U2 Hne Hr) as [D | [I | I]];
[left; exact D | right; left; apply ins_inside; exact I | right; right; apply ins_inside; exact I].
Qed.
Lemma ins_maps : maps_unique X s'.
Proof.
intros p1 a1 p2 a2 H1 H2 Hm1 Hm2 Hr.
destruct (ins_used_bwd _ _ H1) as [[-> ->] | [N1 U1]]; destruct (ins_used_bwd _ _ H2) as [[-> ->] | [N2 U2]].
- reflexivity.
- exfalso. exact (M1 Hm1 _ _ U2 Hm2 (eq_sym Hr)).
- exfalso. exact (M1 Hm2 _ _ U1 Hm1 Hr).
- eapply (inv_maps HI); eauto.
Qed.
Lemma ins_partial : partial_unique X s'.
Proof.
intros p1 a1 p2 a2 H1 H2 Hsc Hp1 Hp2.
destruct (ins_used_bwd _ _ H1) as [[-> ->] | [N1 U1]]; destruct (ins_used_bwd _ _ H2) as [[-> ->] | [N2 U2]].
- reflexivity.
- exfalso. pose proof (P1 Hp1 _ _ U2 (eq_sym Hsc)). lia.
- exfalso. pose proof (P1 Hp2 _ _ U1 Hsc). lia.
- eapply (inv_partial HI); eauto.
Qed.
Lemma ins_Xok : Xok X s'.
Proof.
intros x Hx.
assert (Hne : x <> m) by (intros ->; apply memb_In in Hx; rewrite Hx in NX; discriminate).
destruct (inv_X HI x (or_intror Hx)) as [Kx Mx]. rewrite EK, (EO x Hne). split; [exact Kx | exact Mx].
Qed.
Theorem Inv_install :
ctx_ok s' -> keys_ok s' -> areas_ok s' -> rings_ok X R' s' -> usage_ok X U' s' -> Inv X R' U' s'.
Proof.
intros C K A RG US.
split; [exact C|]. split; [exact K|]. split; [exact A|].
split; [apply ins_Xok|]. split; [apply ins_groups|]. split; [apply ins_laminar|]. split; [apply ins_maps|].
split; [exact RG|]. split; [exact US|]. split; [exact HR' | apply ins_partial].
Qed.
End e.
Lemma sub_subset_ldiff a b : Z.land a b = b -> a - b = Z.ldiff a b.
Proof.
intros H.
assert (E : Z.ldiff a b + b = a).
{ rewrite Z.add_nocarry_lxor.
2:{ apply bits_inj_nonneg. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.bits_0.
destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
rewrite Z.lxor_lor.
2:{ apply bits_inj_nonneg. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.bits_0.
destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
rewrite <- H at 2. apply Z.lor_ldiff_and. }
lia.
Qed.
Ltac bcase t :=
let E := fresh "E" in
destruct t eqn:E;
[first [apply Z.leb_le in E | apply Z.ltb_lt in E | apply Z.eqb_eq in E]
|first [apply Z.leb_gt in E | apply Z.ltb_ge in E | apply Z.eqb_neq in E]].
Lemma testbit_new_avail ai i : 0 <= ai -> Z.testbit (ones ai - 1) i = (1 <=? i) && (i <=? ai).
Proof.
intros Hai. change 1 with (bit 0) at 1.
rewrite sub_bit_ldiff by (try lia; rewrite testbit_ones by lia; cbn; apply Z.leb_le; lia).
destruct (Z_lt_dec i 0) as [Hi|Hi].
- rewrite testbit_neg_idx by lia. bcase (1 <=? i); [lia | reflexivity].
- rewrite Z.ldiff_spec, testbit_ones, testbit_bit by lia.
bcase (0 <=? i); bcase (i <=? ai); bcase (0 =? i); bcase (1 <=? i); cbn; try reflexivity; lia.
Qed.
Lemma testbit_new_freed la ai i : 0 <= ai <= la -> Z.testbit (ones la - ones ai) i = (ai <? i) && (i <=? la).
Proof.
intros H. rewrite sub_subset_ldiff.
2:{ apply bits_inj_nonneg. intros k Hk. rewrite Z.land_spec, !testbit_ones by lia.
bcase (0 <=? k); bcase (k <=? la); bcase (k <=? ai); cbn; try reflexivity; lia. }
destruct (Z_lt_dec i 0) as [Hi|Hi].
- rewrite testbit_neg_idx by lia. bcase (ai <? i); [lia | reflexivity].
- rewrite Z.ldiff_spec, !testbit_ones by lia.
bcase (0 <=? i); bcase (i <=? la); bcase (i <=? ai); bcase (ai <? i); cbn; try reflexivity; lia.
Qed.
Definition new_am (mem : sptr) (sc cnt aidx maplen : Z) (sl : slotst) : ameta :=
mkAMeta None None mem (ones aidx - 1) (ones (cnt - 1) - ones aidx) (cnt - 1) sc maplen aidx (repeat sl (Z.to_nat cnt)).
Lemma new_am_masks mem sc cnt aidx maplen sl :
1 <= cnt <= 32 -> 0 <= aidx <= cnt - 1 -> masks_ok (new_am mem sc cnt aidx maplen sl).
Proof.
intros Hc Ha. unfold masks_ok, new_am. cbn [am_last am_aidx am_slots am_avail am_freed].
rewrite repeat_length.
pose proof (ones_nonneg aidx ltac:(lia)). pose proof (ones_nonneg (cnt - 1) ltac:(lia)).
assert (Hsub : ones aidx <= ones (cnt - 1)).
{ unfold ones. apply Z.sub_le_mono_r. apply Z.pow_le_mono_r; lia. }
assert (H1 : 1 <= ones aidx) by (unfold ones; assert (2 ^ 1 <= 2 ^ (aidx + 1)) by (apply Z.pow_le_mono_r; lia); lia).
repeat split; try lia.
- intros i Hi Hb. rewrite testbit_new_avail in Hb by lia. rewrite testbit_new_freed by lia.
apply andb_prop in Hb as [_ Hb]. apply Z.leb_le in Hb. apply andb_false_intro1. apply Z.ltb_ge. lia.
- rewrite testbit_new_avail by lia. apply andb_false_intro2. apply Z.leb_gt. lia.
- rewrite testbit_new_freed by lia. apply andb_false_intro2. apply Z.leb_gt. lia.
- intros i Hi. rewrite testbit_new_avail by lia. apply andb_false_intro2. apply Z.leb_gt. lia.
- intros i Hi. rewrite testbit_new_freed by lia. apply andb_true_intro. split; [apply Z.ltb_lt | apply Z.leb_le]; lia.
Qed.
Lemma new_am_allocated mem sc cnt aidx maplen sl i :
1 <= cnt -> 0 <= aidx <= cnt - 1 -> 0 <= i ->
allocated (new_am mem sc cnt aidx maplen sl) i = (i =? 0) || (cnt - 1 <? i).
Proof.
intros Hc Ha Hi. unfold allocated, new_am. cbn [am_avail am_freed].
rewrite Z.lor_spec, testbit_new_avail, testbit_new_freed by lia.
bcase (1 <=? i); bcase (i <=? aidx); bcase (aidx <? i); bcase (i <=? cnt - 1); bcase (i =? 0); bcase (cnt - 1 <? i); cbn; try reflexivity; lia.
Qed.
Lemma new_am_nth_slot mem sc cnt aidx maplen sl i :
0 <= i <= cnt - 1 -> nth_slot (new_am mem sc cnt aidx maplen sl) i = sl.
Proof. intros Hi. unfold nth_slot, new_am. cbn [am_slots]. rewrite nth_repeat'. destruct (Nat.ltb _ _) eqn:E; [reflexivity|]. apply Nat.ltb_ge in E. lia. Qed.
Lemma new_am_stride mem sc cnt aidx maplen sl :
stride_of (new_am mem sc cnt aidx maplen sl) = if (cnt - 1 =? 0) && negb (maplen =? 0) then maplen * 4096 - UNIT else class_size sc.
Proof. reflexivity. Qed.
Lemma fold_sum_delta (f f' : sptr -> Z) m l :
NoDup l -> In m l -> (forall q, q <> m -> f' q = f q) ->
fold_right (fun q acc => f' q + acc) 0 l = fold_right (fun q acc => f q + acc) 0 l + (f' m - f m).
Proof.
intros ND Hin Hf. induction l as [|x t IH]; [destruct Hin|]. cbn [fold_right].
inversion ND as [|x' t' Hx Ht]; subst.
destruct (sptr_eq_dec x m) as [->|Hne].
- assert (E : fold_right (fun q acc => f' q + acc) 0 t = fold_right (fun q acc => f q + acc) 0 t).
{ clear IH Hin ND. induction t as [|y u IH]; [reflexivity|]. cbn [fold_right].
rewrite IH by (intros; try (intros Hy; apply Hx; right; exact Hy); inversion Ht; auto).
rewrite Hf by (intros ->; apply Hx; left; reflexivity). reflexivity. }
rewrite E. lia.
- destruct Hin as [E|Hin]; [exfalso; exact (Hne E)|]. rewrite (IH Ht Hin), (Hf x Hne). lia.
Qed.
Section w.
Variables (X : list sptr) (s s' : astate) (m : sptr) (am1 : ameta).
Hypothesis NX : memb m X = false.
Hypothesis EM : MT s' m = Some (MUsed am1).
Hypothesis EO : forall q, q <> m -> MT s' q = MT s q.
Lemma ux_MTX q : q <> m -> MTX X s' q = MTX (m :: X) s q.
Proof.
intros Hne. unfold MTX. rewrite memb_cons, (EO q Hne).
destruct (sptr_eqb q m) eqn:E; [apply sptr_eqb_eq in E; contradiction | reflexivity].
Qed.
Lemma ux_MTX_m : MTX X s' m = Some (MUsed am1) /\ MTX (m :: X) s m = None.
Proof. unfold MTX. rewrite NX, EM, memb_cons, sptr_eqb_refl. split; reflexivity. Qed.
Lemma ux_flinks q : flinks X s' q = flinks (m :: X) s q.
Proof.
unfold flinks. destruct (sptr_eq_dec q m) as [->|Hne].
- destruct ux_MTX_m as [A B]. rewrite A, B. reflexivity.
- rewrite (ux_MTX q Hne). reflexivity.
Qed.
Lemma ux_alinks c q : am_sc am1 <> c -> alinks X s' c q = alinks (m :: X) s c q.
Proof.
intros Hc. unfold alinks. destruct (sptr_eq_dec q m) as [->|Hne].
- destruct ux_MTX_m as [A B]. rewrite A, B. destruct (am_sc am1 =? c) eqn:E; [apply Z.eqb_eq in E; contradiction | reflexivity].
- rewrite (ux_MTX q Hne). reflexivity.
Qed.
Lemma ux_alinks_m c : am_sc am1 = c -> alinks X s' c m = Some (am_prev am1, am_next am1).
Proof. intros Hc. unfold alinks. destruct ux_MTX_m as [A _]. rewrite A. rewrite (proj2 (Z.eqb_eq _ _) Hc). reflexivity. Qed.
Lemma ux_contrib c q : q <> m -> contrib X s' c q = contrib (m :: X) s c q.
Proof. intros Hne. unfold contrib. rewrite (ux_MTX q Hne). reflexivity. Qed.
Lemma ux_contrib_m c : contrib X s' c m = (if am_sc am1 =? c then am_last am1 + 1 else 0) /\ contrib (m :: X) s c m = 0.
Proof. unfold contrib. destruct ux_MTX_m as [A B]. rewrite A, B. split; reflexivity. Qed.
Lemma ux_class_sum c :
keys s' = keys s -> NoDup (keys s) -> In m (keys s) ->
class_sum X s' c = class_sum (m :: X) s c + (if am_sc am1 =? c then am_last am1 + 1 else 0).
Proof.
intros EK ND Hin. unfold class_sum. rewrite EK.
rewrite (fold_sum_delta (contrib (m :: X) s c) (contrib X s' c) m (keys s) ND Hin (fun q H => ux_contrib c q H)).
destruct (ux_contrib_m c) as [A B]. rewrite A, B. lia.
Qed.
Lemma ux_used_bwd q a : usedX X s' q a -> (q = m /\ a = am1) \/ (q <> m /\ usedX (m :: X) s q a).
Proof.
intros Hu. destruct (sptr_eq_dec q m) as [->|Hne].
- left. unfold usedX in Hu. destruct ux_MTX_m as [A _]. rewrite A in Hu. injection Hu as ->. auto.
- right. split; [exact Hne|]. unfold usedX in *. rewrite <- (ux_MTX q Hne). exact Hu.
Qed.
Lemma ux_used_fwd q a : usedX (m :: X) s q a -> q <> m /\ usedX X s' q a.
Proof.
intros Hu. destruct (sptr_eq_dec q m) as [->|Hne].
- unfold usedX in Hu. destruct ux_MTX_m as [_ B]. rewrite B in Hu. discriminate.
- split; [exact Hne|]. unfold usedX in *. rewrite (ux_MTX q Hne). exact Hu.
Qed.
Lemma ux_used_m : usedX X s' m am1.
Proof. unfold usedX. exact (proj1 ux_MTX_m). Qed.
Lemma ux_free_ring :
st_free_meta_head s' = st_free_meta_head s -> free_ring_ok (m :: X) s -> free_ring_ok X s'.
Proof.
intros EF (ms & Rg & Hall). exists ms. rewrite EF. split.
- eapply ring_ok_ext; [|exact Rg]. intros q _. apply ux_flinks.
- intros q pr nx Hq. destruct (sptr_eq_dec q m) as [->|Hne].
+ destruct ux_MTX_m as [A _]. rewrite A in Hq. discriminate.
+ rewrite (ux_MTX q Hne) in Hq. eapply Hall. exact Hq.
Qed.
Lemma ux_active_other R R' c :
(forall q i, q <> m -> R = Some (q, i) -> R' = Some (q, i)) ->
am_sc am1 <> c -> active_hd s' c = active_hd s c -> active_ring_ok (m :: X) R s c -> active_ring_ok X R' s' c.
Proof.
intros HRR Hc EH (ms & Rg & Mem & Full & Q1 & Q2). exists ms. rewrite EH. split.
- eapply ring_ok_ext; [|exact Rg]. intros q _. apply ux_alinks. exact Hc.
- split; [|split; [|split]]; intros q a Hq Hsc;
(destruct (ux_used_bwd q a Hq) as [[-> ->] | [Hne Hu]]; [exfalso; exact (Hc Hsc)|]); eauto.
intros Hin Hnh HnR. eapply Q2; eauto. intros i E. exact (HnR i (HRR q i Hne E)).
Qed.
Lemma ux_direct : am_prev am1 = None -> am_next am1 = None -> direct_unlinked (m :: X) s -> direct_unlinked X s'.
Proof.
intros P N D q a Hq H63. destruct (ux_used_bwd q a Hq) as [[-> ->] | [Hne Hu]]; [auto|]. exact (D q a Hu H63).
Qed.
End w.
Lemma ctx_ok_upd_meta s g x : ctx_ok s -> In g (keys s) -> ctx_ok (upd_meta g x s).
Proof.
intros C Hg. eapply sbmh_ctx; [apply sbmh_upd_meta; exact Hg | reflexivity | | exact C].
intros Hi. destruct C as (_&_&_&_&_&_&_&_&_&_&_&C12). destruct (C12 Hi) as (Em & _).
exfalso. unfold keys in Hg. rewrite Em in Hg. exact Hg.
Qed.
Definition direct_am (r : nat) (maplen : Z) : ameta := mkAMeta None None (SP r 0) 0 0 0 63 maplen 0 [slot_zero].
Lemma install_direct_spec X U s g r rg maplen (Q : unit * astate -> Prop) :
Inv (g :: X) None U s -> memb g X = false ->
region_of s r = Some rg -> rg_kind rg = RkMap -> rg_live rg = true -> rg_len rg = maplen * PGSZ -> 1 <= maplen ->
(forall q a, usedX (g :: X) s q a -> prid (am_mem a) <> r) ->
(forall s', s' = upd_meta g (MUsed (direct_am r maplen)) s -> Inv X (Some (g, 0)) U s' ->
usedX X s' g (direct_am r maplen) -> ub_same s s' -> Q (tt, s')) ->
itok (setm g (direct_am r maplen) s) Q.
Proof.
intros HI NX Hr Hk Hl Hlen Hml Hfresh HQ.
pose proof (inv_X HI g (or_introl eq_refl)) as [Kg _].
apply itok_setm'. set (s' := upd_meta g (MUsed (direct_am r maplen)) s).
assert (EM : MT s' g = Some (MUsed (direct_am r maplen))) by apply MT_upd_same.
assert (EO : forall q, q <> g -> MT s' q = MT s q) by (intros; apply MT_upd_other; assumption).
assert (Ug : usedX X s' g (direct_am r maplen)) by (apply ux_used_m; assumption).
assert (Hal : allocated (direct_am r maplen) 0 = true) by reflexivity.
apply HQ; [reflexivity| |exact Ug|].
2:{ subst s'. apply ub_same_upd_In; [exact Kg|]. rewrite (ucontrib_exempt_nil _ _ _ _ g g HI (or_introl eq_refl)). reflexivity. }
eapply (Inv_install X (Some (g, 0)) U U s s' g (direct_am r maplen) HI NX EM EO).
- apply keys_upd_In. exact Kg.
- reflexivity.
-
split.
{ unfold masks_ok, direct_am. cbn [am_last am_aidx am_slots am_avail am_freed length].
repeat split; try lia; intros; rewrite ?Z.bits_0; auto. }
split; [cbn; lia|]. split.
{ intros i Hi. cbn [am_last direct_am] in Hi. assert (i = 0) as -> by lia.
unfold slot_ok. change (nth_slot (direct_am r maplen) 0) with slot_zero. cbn [ss_hdr ss_fr slot_zero].
split; [discriminate|]. split; [intros h3 h16 E; injection E as <- <-; lia|]. right. reflexivity. }
split.
{ left. cbn. repeat split; try lia; try reflexivity. left. reflexivity. }
split.
{ intros _. exists r, rg. cbn [am_mem am_maplen am_last direct_am].
split; [reflexivity|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [exact Hlen|].
unfold stride_of, direct_am. cbn [am_last am_maplen am_sc]. split; [|intros _ H; lia].
destruct (maplen =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. cbn [Z.eqb andb negb]. unfold UNIT, PGSZ. lia. }
intros H0. cbn in H0. lia.
- intros q a Hu Hp. exfalso. exact (Hfresh q a Hu Hp).
- intros _ q a Hu _ Hp. exact (Hfresh q a Hu Hp).
- intros H. cbn in H. lia.
- intros p i E. injection E as <- <-. exists (direct_am r maplen). split; [exact Ug|]. cbn [am_last direct_am].
split; [lia|]. split; [reflexivity | exact Hal].
- intros p i E. injection E as <- <-. reflexivity.
- apply ctx_ok_upd_meta; [exact (inv_ctx HI) | exact Kg].
- eapply sbmh_keys; [apply sbmh_upd_meta; exact Kg | exact (inv_keys HI)].
- eapply sbmh_areas; [apply sbmh_upd_meta; exact Kg | exact (inv_areas HI)].
- destruct (inv_rings HI) as (F & A & D). split; [|split].
+ eapply ux_free_ring; eauto.
+ intros c Hc. eapply (ux_active_other X s s' g _ NX EM EO None); eauto; [intros q i _ E; discriminate | cbn; lia].
+ eapply ux_direct; eauto.
- intros c Hc. change (usage_of s' c) with (usage_of s c). rewrite (inv_usage HI c Hc).
rewrite (ux_class_sum X s s' g _ NX EM EO c (keys_upd_In _ _ _ Kg) (proj1 (inv_keys HI)) Kg).
cbn [am_sc direct_am]. destruct (63 =? c) eqn:E; [apply Z.eqb_eq in E; lia | lia].
Qed.
Lemma usage_of_nonneg s sc : ctx_ok s -> 0 <= usage_of s sc.
Proof.
intros (_ & _ & _ & _ & C5 & _). unfold usage_of, znth.
destruct (nth_in_or_default (Z.to_nat sc) (st_usage s) 0) as [H|H]; [apply C5; exact H | rewrite H; lia].
Qed.
Lemma links_fields p n am :
am_mem (am_set_links p n am) = am_mem am /\ am_last (am_set_links p n am) = am_last am /\
am_sc (am_set_links p n am) = am_sc am /\ am_maplen (am_set_links p n am) = am_maplen am /\
am_aidx (am_set_links p n am) = am_aidx am /\ am_avail (am_set_links p n am) = am_avail am /\
am_freed (am_set_links p n am) = am_freed am /\ am_slots (am_set_links p n am) = am_slots am /\
am_prev (am_set_links p n am) = p /\ am_next (am_set_links p n am) = n.
Proof. destruct am; repeat split; reflexivity. Qed.
Lemma ring_ok_single lk m : lk m = Some (Some m, Some m) -> ring_ok lk (Some m) [m].
Proof.
intros H. split; [|reflexivity]. split; [constructor; [intros []|constructor]|]. cbn. split; [exact H | exact I].
Qed.
Lemma empty_ring_class X R U s sc q a :
Inv X R U s -> 0 <= sc < 48 -> active_hd s sc = None -> usedX X s q a -> am_sc a = sc ->
am_avail a = 0 /\ am_freed a = 0 /\ (am_prev a, am_next a) = (None, None) /\ am_aidx a = am_last a.
Proof.
intros HI Hsc Hhd Hu Hsa.
destruct (inv_rings HI) as (_ & A & _). destruct (A sc Hsc) as (ms & Rg & Mem & Full & _).
rewrite Hhd in Rg. apply ring_None in Rg. subst ms.
assert (Hl : (am_prev a, am_next a) = (None, None)).
{ destruct (Mem q a Hu Hsa) as [_ M2]. destruct (am_prev a), (am_next a); try reflexivity; exfalso; apply (M2 ltac:(discriminate)). }
destruct (Full q a Hu Hsa ltac:(intros [])) as [Av Fr].
pose proof (inv_groups HI q a Hu) as ((M1 & M2 & _ & _ & _ & _ & _ & _ & M9) & _).
repeat split; auto; try (injection Hl; auto).
destruct (Z_lt_dec (am_aidx a) (am_last a)) as [Hlt|]; [|lia]. exfalso.
pose proof (M9 (am_last a) ltac:(lia)) as Hb. rewrite Fr, Z.bits_0 in Hb. discriminate.
Qed.
Lemma install_group_spec X U s m sc cnt aidx maplen mem sl (Q : unit * astate -> Prop) :
Inv (m :: X) None U s -> memb m X = false ->
0 <= sc < 48 -> 1 <= cnt <= 32 -> 0 <= aidx <= cnt - 1 -> 0 <= maplen ->
active_hd s sc = None ->
let am1 := new_am mem sc cnt aidx maplen sl in
((sl = slot_zero /\ 0 < maplen) \/ (sl = slot_junk /\ maplen = 0)) ->
class_ok (Some (m, 0)) m am1 ->
mapped_ok s am1 ->
(maplen = 0 -> exists g' am' i' fr', usedX (m :: X) s g' am' /\ 0 <= i' <= am_last am' /\
ss_fr (nth_slot am' i') = Some fr' /\ fr_kind fr' = FGroup /\ mem = slot_start am' i' /\
sc < am_sc am' /\ am_sc am' <> 63 /\ UNIT + class_size sc * cnt - IB <= fr_n fr') ->
(forall q a, usedX (m :: X) s q a -> prid (am_mem a) = prid mem ->
spans_disjoint a am1 \/ inside (m :: X) s am1 a \/
(maplen = 0 /\ exists j fr, 0 <= j <= am_last a /\ ss_fr (nth_slot a j) = Some fr /\ fr_kind fr = FGroup /\
mem = slot_start a j /\ group_extent am1 <= fr_n fr)) ->
(0 < maplen -> forall q a, usedX (m :: X) s q a -> 0 < am_maplen a -> prid (am_mem a) <> prid mem) ->
(forall s', Inv X (Some (m, 0)) U s' -> active_hd s' sc = Some m ->
usedX X s' m (am_set_links (Some m) (Some m) am1) ->
(forall c, 0 <= c -> c <> sc -> active_hd s' c = active_hd s c) ->
st_regions s' = st_regions s -> st_mmap_counter s' = st_mmap_counter s ->
ub_same s s' ->
Q (tt, s')) ->
itok (install_group m sc cnt aidx maplen mem sl s) Q.
Proof.
intros HI NX Hsc Hcnt Haidx Hml Hhd am1 SL CL MP NS LAM MU HQ.
pose proof (inv_X HI m (or_introl eq_refl)) as [Km _].
pose proof (inv_ctx HI) as C0. pose proof C0 as (Clen & _).
assert (Hfr1 : forall i, ss_fr (nth_slot am1 i) = None).
{ intros i. unfold nth_slot, am1, new_am. cbn [am_slots]. rewrite nth_repeat'.
destruct (Nat.ltb _ _); [|reflexivity]. destruct SL as [[-> _]|[-> _]]; reflexivity. }
unfold install_group. mbinds. apply itok_get. msimp. mbinds. apply itok_set_usage_of. msimp.
set (s1 := set_usage (zset sc (usage_of s sc + cnt) (st_usage s)) s).
assert (HI1 : Inv (m :: X) None (Uadd U sc cnt) s1).
{ pose proof (Inv_set_usage (m :: X) None U s sc (usage_of s sc + cnt) HI Hsc
ltac:(pose proof (usage_of_nonneg s sc C0); lia)) as H.
replace (usage_of s sc + cnt - usage_of s sc) with cnt in H by lia. exact H. }
mbinds. apply itok_setm'. msimp. fold am1.
set (s2 := upd_meta m (MUsed am1) s1).
assert (HI2 : Inv (m :: X) None (Uadd U sc cnt) s2).
{ apply Inv_upd_exempt; [exact HI1 | left; reflexivity |]. cbn [am_prev am_next am1 new_am]. auto. }
assert (M2 : MT s2 m = Some (MUsed am1)) by apply MT_upd_same.
assert (EU2 : forall q a, usedX (m :: X) s2 q a <-> usedX (m :: X) s q a).
{ intros q a. unfold s2. rewrite usedX_upd_exempt by (left; reflexivity). unfold s1, usedX, MTX, MT. cbn. tauto. }
assert (Hhd2 : active_hd s2 sc = None) by exact Hhd.
eapply (queue_op (HActive sc) m s2 (MUsed am1) [] (alinks (m :: X) s2 sc)).
- exact M2.
- reflexivity.
- cbn [head_of]. rewrite Hhd2. apply ring_ok_nil.
- intros [].
- intros q l [].
- cbn. rewrite Clen. lia.
- intros s3 Sb Hse Hhd3 M3 EO3 _. cbn [hd last head_of with_links] in Hhd3, M3.
set (am1' := am_set_links (Some m) (Some m) am1) in M3.
pose proof (links_fields (Some m) (Some m) am1) as (Lmem & Llast & Lsc & Lml & Lai & Lav & Lfr & Lsl & Lp & Ln). fold am1' in Lmem, Llast, Lsc, Lml, Lai, Lav, Lfr, Lsl, Lp, Ln.
assert (EO : forall q, q <> m -> MT s3 q = MT s2 q) by (intros q Hq; apply EO3; intros [E|[]]; exact (Hq (eq_sym E))).
pose proof Sb as (_&Emc&_&_&_&_&_&_&_&Eus&_&_&_&_&Erg&_&EK).
destruct Hse as (HA & HF & HL).
assert (EH : forall c, 0 <= c -> c <> sc -> active_hd s3 c = active_hd s c).
{ intros c Hc Hne. unfold active_hd. rewrite HA; [reflexivity|]. intros sc' E. injection E as <-. intros E. apply Hne. lia. }
assert (U3 : usedX X s3 m am1') by (apply (ux_used_m X s2 s3 m am1' NX M3)).
assert (Hal0 : allocated am1' 0 = true).
{ rewrite <- (strip_allocated am1 am1' 0) by (unfold strip; rewrite <- ?Lsl; destruct am1; reflexivity).
unfold am1. rewrite new_am_allocated by lia. reflexivity. }
assert (Hst : strip am1' = strip am1) by (unfold am1', strip; destruct am1; reflexivity).
apply HQ; [ | exact Hhd3 | exact U3 | exact EH | exact Erg | exact Emc |].
2:{ apply (ub_same_trans s s2).
- apply (ub_same_trans s s1); [apply ub_same_metas; reflexivity|].
unfold s2. apply ub_same_upd_In; [exact Km|]. rewrite (ucontrib_exempt_nil _ _ _ _ m m HI1 (or_introl eq_refl)). cbn.
apply blocks_of_frameless. exact Hfr1.
- eapply ub_same_relinked; [|exact EK]. split; [exact EO3|].
intros q [<-|[]]. exists (MUsed am1), (Some m), (Some m). split; [exact M2|]. split; [exact M3 | discriminate]. }
eapply (Inv_install X (Some (m, 0)) (Uadd U sc cnt) U s2 s3 m am1' HI2 NX M3 EO EK Erg).
+
split.
{ unfold masks_ok. rewrite Llast, Lai, Lsl, Lav, Lfr. apply (new_am_masks mem sc cnt aidx maplen sl); lia. }
split; [rewrite Lml; cbn; exact Hml|]. split.
{ intros i Hi. rewrite Llast in Hi. cbn [am_last am1 new_am] in Hi.
unfold slot_ok. rewrite (strip_nth_slot _ _ i Hst), (strip_allocated _ _ i Hst), Lml.
unfold am1. rewrite new_am_nth_slot by lia. rewrite new_am_allocated by lia. cbn [am_maplen new_am].
destruct SL as [[-> Hpos]|[-> Hz]]; cbn [ss_hdr ss_fr slot_zero slot_junk].
- split; [discriminate|]. split; [intros h3 h16 E; injection E as <- <-; lia|].
destruct (Z.eq_dec i 0) as [->|Hne]; [right; reflexivity | left]. bcase (i =? 0); bcase (cnt - 1 <? i); cbn; try reflexivity; lia.
- split; [auto|]. split; [discriminate|].
destruct (Z.eq_dec i 0) as [->|Hne]; [right; reflexivity | left]. bcase (i =? 0); bcase (cnt - 1 <? i); cbn; try reflexivity; lia. }
split.
{ replace (class_ok (Some (m, 0)) m am1') with (class_ok (Some (m, 0)) m am1); [exact CL|]. unfold am1'; destruct am1; reflexivity. }
split.
{ intros Hm. rewrite Lml in Hm. destruct (MP Hm) as (r & rg & H1 & H2 & H3). exists r, rg.
rewrite Lmem, Lml, Llast, (strip_stride _ _ Hst). unfold region_of in *. rewrite Erg. unfold s2, s1 in *. cbn. cbn in H2. auto. }
intros Hm. rewrite Lml in Hm. cbn [am_maplen am1 new_am] in Hm. rewrite Lsc, Lmem, Llast. cbn [am_sc am_mem am_last am1 new_am].
destruct (NS Hm) as (g' & am' & i' & fr' & U' & Hi' & F' & K' & Mem' & Sc' & N63 & Fit).
split; [lia|]. exists g', am', i', fr'.
split; [apply (ux_used_fwd X s2 s3 m am1' NX M3 EO); apply EU2; exact U'|].
replace (cnt - 1 + 1) with cnt by lia. repeat split; auto; lia.
+
intros q a Hu Hp. apply EU2 in Hu. rewrite Lmem in Hp.
destruct (LAM q a Hu Hp) as [D | [I | (Hz & j & fr & Hj & Hfr & Hk & Hmem & Hfit)]].
* left. unfold spans_disjoint in *. rewrite Lmem, (strip_extent _ _ Hst). exact D.
* right; right. destruct I as (j & fr & c & ac & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
exists j, fr, c, ac. rewrite Lmem, (strip_extent _ _ Hst).
repeat split; auto; try lia. apply (ux_used_fwd X s2 s3 m am1' NX M3 EO). apply EU2. exact H4.
* right; right. exists j, fr, m, am1'. rewrite Lmem, Lml, (strip_extent _ _ Hst).
repeat split; auto; try lia; unfold am1; cbn [am_mem am_maplen new_am]; lia.
+ intros Hm q a Hu Ha. rewrite Lml in Hm. rewrite Lmem. apply EU2 in Hu. exact (MU Hm q a Hu Ha).
+ intros Hp q a Hu Hsa. rewrite Lai, Llast in Hp. rewrite Lsc in Hsa. cbn [am_sc am_aidx am_last am1 new_am] in Hp, Hsa.
destruct (empty_ring_class _ _ _ _ sc q a HI2 Hsc Hhd2 Hu Hsa) as (_ & _ & _ & E). lia.
+ intros p i E. injection E as <- <-. exists am1'. split; [exact U3|]. rewrite Llast, (strip_nth_slot _ _ 0 Hst).
cbn [am_last am1 new_am]. split; [lia|]. split; [apply Hfr1 | exact Hal0].
+ intros p i E. injection E as <- <-. reflexivity.
+ eapply sbmh_ctx; [exact Sb | exact HL | | exact (inv_ctx HI2)].
intros Hi. exfalso. destruct (inv_ctx HI2) as (_&_&_&_&_&_&_&_&_&_&_&C12). destruct (C12 Hi) as (Em & _).
unfold MT in M2. rewrite Em in M2. discriminate.
+ eapply sbmh_keys; [exact Sb | exact (inv_keys HI2)].
+ eapply sbmh_areas; [exact Sb | exact (inv_areas HI2)].
+ destruct (inv_rings HI2) as (F & A & D). split; [|split].
* eapply (ux_free_ring X s2 s3 m am1' NX M3 EO); [apply HF; discriminate | exact F].
* intros c Hc. destruct (Z.eq_dec c sc) as [->|Hne].
-- exists [m]. rewrite Hhd3. split.
{ apply ring_ok_single. rewrite (ux_alinks_m X s2 s3 m am1' NX M3 sc Lsc), Lp, Ln. reflexivity. }
split.
{ intros q a Hq Hsa. destruct (ux_used_bwd X s2 s3 m am1' NX M3 EO q a Hq) as [[-> ->]|[Hne Hu]].
- rewrite Lp, Ln. split; [intros _; discriminate | intros _; left; reflexivity].
- destruct (empty_ring_class _ _ _ _ sc q a HI2 Hsc Hhd2 Hu Hsa) as (_ & _ & E & _). rewrite E.
split; [intros [E'|[]]; exfalso; exact (Hne (eq_sym E')) | intros H; exfalso; apply H; reflexivity]. }
split.
{ intros q a Hq Hsa Hnin. destruct (ux_used_bwd X s2 s3 m am1' NX M3 EO q a Hq) as [[-> ->]|[Hne Hu]].
- exfalso. apply Hnin. left. reflexivity.
- destruct (empty_ring_class _ _ _ _ sc q a HI2 Hsc Hhd2 Hu Hsa) as (E1 & E2 & _). auto. }
split.
{ intros q a Hq Hsa Hav. destruct (ux_used_bwd X s2 s3 m am1' NX M3 EO q a Hq) as [[-> ->]|[Hne Hu]]; [reflexivity|].
destruct (empty_ring_class _ _ _ _ sc q a HI2 Hsc Hhd2 Hu Hsa) as (E1 & _). exfalso. exact (Hav E1). }
intros q a Hq Hsa Hin Hne _. destruct Hin as [<-|[]]. exfalso. apply Hne. reflexivity.
-- eapply (ux_active_other X s2 s3 m am1' NX M3 EO None); [intros q i _ E; discriminate | rewrite Lsc; cbn; lia | | apply A; exact Hc].
rewrite (EH c ltac:(lia) Hne). reflexivity.
* intros q a Hq H63. destruct (ux_used_bwd X s2 s3 m am1' NX M3 EO q a Hq) as [[-> ->]|[Hne Hu]].
-- rewrite Lsc in H63. cbn in H63. lia.
-- exact (D q a Hu H63).
+ intros c Hc. rewrite (sbmh_usage_of _ _ c Sb). rewrite (inv_usage HI2 c Hc).
rewrite (ux_class_sum X s2 s3 m am1' NX M3 EO c EK (proj1 (inv_keys HI2)) (MT_Some_In_keys _ _ _ M2)).
rewrite Lsc, Llast. cbn [am_sc am_last am1 new_am]. unfold Uadd.
destruct (sc =? c) eqn:E1; destruct (c =? sc) eqn:E2; try lia;
try (apply Z.eqb_eq in E1; apply Z.eqb_neq in E2; lia); try (apply Z.eqb_neq in E1; apply Z.eqb_eq in E2; lia).
Qed.
Definition ctx_frame (s s' : astate) : Prop :=
st_metas s' = st_metas s /\ st_active s' = st_active s /\ st_regions s' = st_regions s /\
st_usage s' = st_usage s /\ st_mmap_counter s' = st_mmap_counter s /\ st_areas s' = st_areas s.
Lemma step_seq_spec X R U s (Q : unit * astate -> Prop) :
Inv X R U s -> (forall s', Inv X R U s' -> ctx_frame s s' -> Q (tt, s')) -> itok (step_seq s) Q.
Proof.
intros HI HQ. unfold step_seq. apply itok_modify. pose proof (inv_ctx HI) as (_&_&_&_&_&_&_&C8&_).
destruct (st_seq s =? 255) eqn:E.
- apply HQ; [|repeat split; reflexivity]. apply Inv_set_seq; [|lia].
destruct repeat0_32_range as [A B]. apply Inv_set_unmap_seq; [exact HI | exact A | exact B].
- apply Z.eqb_neq in E. apply HQ; [|repeat split; reflexivity]. apply Inv_set_seq; [exact HI | lia].
Qed.
Lemma record_seq_spec X R U s sc (Q : unit * astate -> Prop) :
Inv X R U s -> (forall s', Inv X R U s' -> ctx_frame s s' -> Q (tt, s')) -> itok (record_seq sc s) Q.
Proof.
intros HI HQ. unfold record_seq. destruct (bounce_idx sc) as [k|]; [apply itok_modify | apply itok_ret]; (apply HQ; [|repeat split; reflexivity]); [|exact HI].
pose proof (inv_ctx HI) as (_&_&C3&_&_&C6&_&C8&_).
destruct (zset_length32_range _ k _ C3 C6 C8) as [A B]. apply Inv_set_unmap_seq; [exact HI | exact A | exact B].
Qed.
Lemma account_bounce_spec X R U s sc (Q : unit * astate -> Prop) :
Inv X R U s -> (forall s', Inv X R U s' -> ctx_frame s s' -> Q (tt, s')) -> itok (account_bounce sc s) Q.
Proof.
intros HI HQ. unfold account_bounce. destruct (bounce_idx sc) as [k|]; [apply itok_modify | apply itok_ret]; [|apply HQ; [exact HI | repeat split; reflexivity]].
pose proof (inv_ctx HI) as (_&_&_&C4&_&_&C7&_).
destruct (negb (znth k (st_unmap_seq s) =? 0) && (st_seq s - znth k (st_unmap_seq s) <? 10)).
- apply HQ; [|repeat split; reflexivity].
assert (Hv : 0 <= (if znth k (st_bounces s) + 1 <? 100 then znth k (st_bounces s) + 1 else 150) <= 255).
{ pose proof (nth_In_range (st_bounces s) (Z.to_nat k) 0 255 C7 ltac:(lia)) as Hr. unfold znth.
destruct (_ <? 100) eqn:E; [apply Z.ltb_lt in E|]; lia. }
destruct (zset_length32_range _ k _ C4 C7 Hv) as [A B]. apply Inv_set_bounces; [exact HI | exact A | exact B].
- apply HQ; [exact HI | repeat split; reflexivity].
Qed.
Lemma areas_ok_map_region s s' :
areas_ok s ->
st_areas s' = st_areas s -> st_area_head s' = st_area_head s -> st_area_tail s' = st_area_tail s ->
st_meta_alloc_shift s' = st_meta_alloc_shift s -> st_brk s' = st_brk s ->
st_avail_meta_area_count s' = st_avail_meta_area_count s -> st_avail_meta_areas s' = st_avail_meta_areas s ->
(forall k rg, region_of s k = Some rg -> rg_kind rg <> RkMap -> region_of s' k = Some rg) ->
(forall k rg, region_of s' k = Some rg -> rg_kind rg <> RkMap -> region_of s k = Some rg) ->
resv_total s' = resv_total s -> brk_regions s' = brk_regions s ->
(forall k rg, region_of s' k = Some rg -> 0 <= rg_len rg \/ region_of s k = Some rg) ->
areas_ok s'.
Proof.
intros (A1&A2&A3&A4&A5&A6&A7&A8&A9) Ea Eh Et Es Eb Ec Ep Hfwd Hbwd Er Ebr Hlen9. unfold areas_ok.
rewrite Ea, Eh, Et, Es, Eb, Ec, Ep, Er, Ebr.
refine (conj A1 (conj _ (conj A3 (conj A4 (conj _ (conj A6 (conj _ (conj _ _))))))));
[| | | | intros k rg Hk; destruct (Hlen9 k rg Hk) as [H|H]; [exact H | eapply A9; exact H]].
- intros a Ha. destruct (A2 a Ha) as (ra & oa & rga & Ea' & Ho & Hlo & Hrg & Hl & Hhi & Hk).
exists ra, oa, rga. repeat (split; [assumption|]). split; [| split; [exact Hl | split; [exact Hhi | exact Hk]]].
apply Hfwd; [exact Hrg|]. destruct (rg_kind rga); [discriminate|discriminate|destruct Hk].
- intros k rg Hk Hkind. eapply A5; [|exact Hkind]. apply Hbwd; [exact Hk|]. rewrite Hkind. discriminate.
- destruct (st_brk s) as [| |rb pb].
+ exact A7.
+ intros rr Hrr. destruct (A7 rr Hrr) as (Hbr & rg & Hrg & Hrest). split; [exact Hbr|]. exists rg.
split; [|exact Hrest]. apply Hfwd; [exact Hrg|]. destruct (brk_regions_In _ _ Hrr) as (rg' & Hrg' & K'). rewrite Hrg in Hrg'. injection Hrg' as <-. rewrite K'. discriminate.
+ destruct A7 as (Hbr & rg & Hrg & Hrest). split; [exact Hbr|]. exists rg.
split; [|exact Hrest]. apply Hfwd; [exact Hrg|].
assert (Hin : In rb (brk_regions s)) by (rewrite Hbr; left; reflexivity).
destruct (brk_regions_In _ _ Hin) as (rg' & Hrg' & K'). rewrite Hrg in Hrg'. injection Hrg' as <-. rewrite K'. discriminate.
- intros Hc. destruct (A8 Hc) as (r & o & rg & E1 & E2 & E3 & Rest). exists r, o, rg.
split; [exact E1|]. split; [apply Hfwd; [exact E2 | rewrite E3; discriminate] | exact (conj E3 Rest)].
Qed.
Lemma InvMeta_regions' X R U s rs :
(forall q a rg, usedX X s q a -> 0 < am_maplen a -> region_of s (prid (am_mem a)) = Some rg ->
region_of (set_regions rs s) (prid (am_mem a)) = Some rg) ->
InvMeta X R U s -> InvMeta X R U (set_regions rs s).
Proof.
intros Hreg (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
split; [exact M1|]. split.
{ intros g am Hg. pose proof (M2 g am Hg) as (G1 & G2 & G3 & G4 & G5 & G6).
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [|exact G6].
intros Hm. destruct (G5 Hm) as (r & rg & H1 & H2 & H3 & H4 & H5 & H6). exists r, rg.
split; [exact H1|]. split; [|auto]. pose proof (Hreg g am rg Hg Hm) as E. rewrite H1 in E. cbn [prid] in E. apply E. exact H2. }
split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|]. split; [exact M7 | exact M8].
Qed.
Lemma Inv_new_map X R U s len :
Inv X R U s -> 0 <= len -> Inv X R U (set_regions (st_regions s ++ [mkRegion RkMap len [] true]) s).
Proof.
intros HI Hlen0. set (x := mkRegion RkMap len [] true). set (s' := set_regions _ s).
split; [exact (inv_ctx HI)|]. split; [exact (inv_keys HI)|]. split.
- eapply areas_ok_map_region; try exact (inv_areas HI); try reflexivity.
+ intros k rg Hk _. apply region_of_app. exact Hk.
+ intros k rg Hk Hkind. unfold region_of in Hk |- *. subst s'. cbn [st_regions set_regions] in Hk.
rewrite nth_error_app in Hk. destruct (Nat.ltb k (length (st_regions s))) eqn:El; [exact Hk|].
exfalso. destruct (k - length (st_regions s))%nat as [|k']; cbn in Hk; [injection Hk as <-; apply Hkind; reflexivity | destruct k'; discriminate].
+ subst s'. rewrite resv_total_app. cbn. lia.
+ subst s'. rewrite brk_regions_app. cbn. apply app_nil_r.
+ intros k rg Hk. unfold region_of in Hk |- *. subst s'. cbn [st_regions set_regions] in Hk. rewrite nth_error_app in Hk.
destruct (Nat.ltb k (length (st_regions s))); [right; exact Hk|].
destruct (k - length (st_regions s))%nat as [|k']; cbn in Hk; [injection Hk as <-; left; cbn; exact Hlen0 | destruct k'; discriminate].
- apply InvMeta_regions; [|exact (inv_meta HI)]. intros k rg Hk _. apply region_of_app. exact Hk.
Qed.
Lemma new_region_spec X R U s k len (Q : nat * astate -> Prop) :
Inv X R U s ->
(forall s', Inv X R U s' -> s' = set_regions (st_regions s ++ [mkRegion k len [] true]) s -> Q (length (st_regions s), s')) ->
k = RkMap -> 0 <= len ->
itok (new_region k len s) Q.
Proof.
intros HI HQ -> Hlen. unfold new_region. mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp. apply itok_ret.
apply HQ; [apply Inv_new_map; [exact HI | exact Hlen] | reflexivity].
Qed.
Lemma Inv_kill_map X R U s r rg :
Inv X R U s -> region_of s r = Some rg -> rg_kind rg = RkMap ->
(forall q a, usedX X s q a -> 0 < am_maplen a -> prid (am_mem a) <> r) ->
Inv X R U (set_regions (lupd (st_regions s) r (mkRegion RkMap (rg_len rg) [] false)) s).
Proof.
intros HI Hr Hk Hno. set (x := mkRegion RkMap (rg_len rg) [] false). set (s' := set_regions _ s).
assert (ER : forall k, k <> r -> region_of s' k = region_of s k).
{ intros k Hne. subst s'. rewrite region_of_upd. replace (Nat.eqb k r) with false by (symmetry; apply Nat.eqb_neq; exact Hne). reflexivity. }
assert (ERr : region_of s' r = Some x).
{ subst s'. rewrite region_of_upd. rewrite Nat.eqb_refl. replace (Nat.ltb r (length (st_regions s))) with true; [reflexivity|].
symmetry. apply Nat.ltb_lt. eapply region_of_lt. exact Hr. }
split; [exact (inv_ctx HI)|]. split; [exact (inv_keys HI)|]. split.
- eapply areas_ok_map_region; try exact (inv_areas HI); try reflexivity.
+ intros k rg' Hk' Hkind. destruct (Nat.eq_dec k r) as [->|Hne]; [rewrite Hr in Hk'; injection Hk' as <-; contradiction|].
rewrite (ER k Hne). exact Hk'.
+ intros k rg' Hk' Hkind. destruct (Nat.eq_dec k r) as [->|Hne]; [rewrite ERr in Hk'; injection Hk' as <-; exfalso; apply Hkind; reflexivity|].
rewrite <- (ER k Hne). exact Hk'.
+ subst s'. eapply resv_total_upd; [exact Hr|]. rewrite Hk. discriminate.
+ subst s'. eapply brk_regions_upd; [exact Hr|]. rewrite Hk. reflexivity.
+ pose proof (inv_areas HI) as (_&_&_&_&_&_&_&_&A9).
intros k rg' Hk'. destruct (Nat.eq_dec k r) as [->|Hne]; [rewrite ERr in Hk'; injection Hk' as <-; left; unfold x; cbn [rg_len]; eapply A9; exact Hr | right; rewrite <- (ER k Hne); exact Hk'].
- apply InvMeta_regions'; [|exact (inv_meta HI)]. intros q a rg' Hu Hm Hq.
fold s'. rewrite (ER _ (Hno q a Hu Hm)). exact Hq.
Qed.
Lemma upd_region_kill_spec X R U s r rg (Q : unit * astate -> Prop) :
Inv X R U s -> region_of s r = Some rg -> rg_kind rg = RkMap ->
(forall q a, usedX X s q a -> 0 < am_maplen a -> prid (am_mem a) <> r) ->
(forall s', Inv X R U s' -> st_metas s' = st_metas s -> st_active s' = st_active s -> Q (tt, s')) ->
itok (upd_region r (fun rg => mkRegion RkMap (rg_len rg) [] false) s) Q.
Proof.
intros HI Hr Hk Hno HQ. unfold upd_region. apply itok_modify.
unfold region_of in Hr. rewrite (nth_error_nth _ _ (mkRegion RkMap 0 [] false) Hr).
apply HQ; [|reflexivity|reflexivity]. apply (Inv_kill_map X R U s r rg HI Hr Hk Hno).
Qed.
Lemma upd_slot_fields am i x :
am_mem (upd_slot am i x) = am_mem am /\ am_last (upd_slot am i x) = am_last am /\
am_sc (upd_slot am i x) = am_sc am /\ am_maplen (upd_slot am i x) = am_maplen am /\
stride_of (upd_slot am i x) = stride_of am /\ group_extent (upd_slot am i x) = group_extent am /\
(forall j, slot_start (upd_slot am i x) j = slot_start am j).
Proof. destruct am; repeat split; reflexivity. Qed.
Lemma nested_lam X U s2 g idx am hdr n q a sc cnt0 :
Inv X (Some (g, idx)) U s2 -> usedX X s2 g am -> n = stride_of am - IB ->
let am' := upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame 0 n FGroup))) in
let s3 := upd_meta g (MUsed am') s2 in
let am1 := new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk in
0 < group_extent am1 <= n ->
usedX X s3 q a -> prid (am_mem a) = prid (am_mem am) ->
spans_disjoint a am1 \/ inside X s3 am1 a \/
(exists j fr, 0 <= j <= am_last a /\ ss_fr (nth_slot a j) = Some fr /\ fr_kind fr = FGroup /\
slot_start am idx = slot_start a j /\ group_extent am1 <= fr_n fr).
Proof.
intros HI Hg Hn am' s3 am1 Hext Hq Hpr.
pose proof (usedX_MT _ _ _ _ Hg) as [Mg NXg].
destruct (inv_reserved HI g idx eq_refl) as (amg & Hg' & Hidx & Hfr0 & _).
pose proof (usedX_fun _ _ _ _ _ Hg' Hg) as ->.
pose proof (inv_groups HI g am Hg) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
pose proof G as ((_ & _ & Glen & _) & _ & Gsl & _).
pose proof (upd_slot_fields am idx (mkSlot (Some hdr) (Some (mkFrame 0 n FGroup)))) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold am' in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
assert (Emem1 : am_mem am1 = slot_start am idx) by reflexivity.
assert (P1 : poff (am_mem am1) = poff (am_mem am) + UNIT + stride_of am * idx) by (rewrite Emem1; apply poff_slot_start).
apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
-
injection E as <-. right; right. exists idx, (mkFrame 0 n FGroup). rewrite Fl, Fss.
split; [exact Hidx|]. split; [|split; [reflexivity|split; [reflexivity|cbn [fr_n]; lia]]].
unfold am'. rewrite nth_slot_upd_slot by (try lia; rewrite Glen; lia). rewrite Z.eqb_refl. reflexivity.
- destruct (inv_laminar HI q a g am Hq Hg Hne Hpr) as [D | [I | I]].
+ left. unfold spans_disjoint in *. rewrite P1.
assert (0 <= stride_of am * idx) by nia.
assert (stride_of am * idx + stride_of am <= stride_of am * (am_last am + 1)) by nia.
assert (Hspan : poff (am_mem am) + UNIT + stride_of am * idx + group_extent am1 <= poff (am_mem am) + group_extent am).
{ unfold group_extent at 2. unfold UNIT, IB in *. lia. }
unfold UNIT, IB in *. lia.
+
destruct I as (j' & fr' & c & ac & Hj' & Hfr' & Hk' & Uc & Mlc & Memc & Lo & Hi & Fit).
destruct (Z.eq_dec j' idx) as [->|Hjne]; [rewrite Hfr0 in Hfr'; discriminate|].
left. unfold spans_disjoint. rewrite P1.
pose proof (Gsl j' Hj') as (_ & _ & S3). rewrite Hfr' in S3. destruct S3 as (_ & _ & (N' & O' & B' & _) & _).
rewrite Memc, poff_slot_start in Lo, Hi.
destruct (same_group_starts am j' idx Hjne Sp) as [LE|LE]; rewrite !poff_slot_start in LE; unfold UNIT, IB in *; [left | right]; lia.
+
destruct I as (j' & fr' & c & ac & Hj' & Hfr' & Hk' & Uc & Mlc & Memc & Lo & Hi & Fit).
right; left.
assert (Uc3 : exists ac', usedX X s3 c ac' /\ am_mem ac' = am_mem ac /\ group_extent ac' = group_extent ac /\ am_maplen ac' = am_maplen ac).
{ destruct (sptr_eq_dec c g) as [->|Hcg].
- pose proof (usedX_fun _ _ _ _ _ Uc Hg) as ->. exists am'. split; [|auto].
apply usedX_upd. left. auto.
- exists ac. split; [|auto]. apply usedX_upd. right. auto. }
destruct Uc3 as (ac' & Uc' & Em' & Ex' & Ml').
assert (0 <= stride_of am * idx) by nia.
assert (stride_of am * idx + stride_of am <= stride_of am * (am_last am + 1)) by nia.
assert (Hspan : poff (am_mem am) + UNIT + stride_of am * idx + group_extent am1 <= poff (am_mem am) + group_extent am).
{ unfold group_extent at 2. unfold UNIT, IB in *. lia. }
exists j', fr', c, ac'. rewrite Em', Ex', Ml', P1.
repeat split; auto; unfold UNIT, IB in *; lia.
Qed.
Lemma remove_head_notin m X : memb m X = false -> remove sptr_eq_dec m (m :: X) = X.
Proof.
intros H. cbn. destruct (sptr_eq_dec m m) as [_|N]; [|exfalso; exact (N eq_refl)].
apply notin_remove. apply memb_false_notIn. exact H.
Qed.
Lemma land32_range a : 0 <= a -> 0 <= Z.land a (2 ^ 32 - 1) < 2 ^ 32.
Proof.
intros Ha. change (2 ^ 32 - 1) with (Z.ones 32). rewrite Z.land_ones by lia.
apply Z.mod_pos_bound. lia.
Qed.
Lemma padd_0 p : padd p 0 = p.
Proof. destruct p. cbn. f_equal. lia. Qed.
Definition heads_below (s s' : astate) (sc : Z) : Prop :=
forall c, 0 <= c < sc -> active_hd s' c = active_hd s c.
Definition slot_post (X : list sptr) (U : Z -> Z) (s : astate) (sc req : Z) (r : Z * astate) : Prop :=
heads_below s (snd r) sc /\ ub_same s (snd r) /\
((fst r = -1 /\ Inv X None U (snd r)) \/
(0 <= fst r /\ exists g am, Inv X (Some (g, fst r)) U (snd r) /\ active_hd (snd r) sc = Some g /\
usedX X (snd r) g am /\ am_sc am = sc /\ req + IB <= stride_of am /\ fst r <= am_last am)).
Definition group_post (X : list sptr) (U : Z -> Z) (s : astate) (sc req : Z) (r : option sptr * astate) : Prop :=
heads_below s (snd r) sc /\ ub_same s (snd r) /\
match fst r with
| None => Inv X None U (snd r)
| Some m => exists am, Inv X (Some (m, 0)) U (snd r) /\ active_hd (snd r) sc = Some m /\
usedX X (snd r) m am /\ am_sc am = sc /\ req + IB <= stride_of am /\ 0 <= am_last am
end.
Theorem alloc_mutual fuel :
(forall X U s sc req (Q : Z * astate -> Prop),
Inv X None U s -> 0 <= sc < 48 -> 0 <= req -> req + IB <= class_size sc -> (need sc <= fuel)%nat ->
(forall r, slot_post X U s sc req r -> Q r) -> itok (alloc_slot fuel sc req s) Q) /\
(forall X U s sc req (Q : option sptr * astate -> Prop),
Inv X None U s -> 0 <= sc < 48 -> 0 <= req -> req + IB <= class_size sc -> (need sc <= S fuel)%nat ->
active_hd s sc = None ->
(forall r, group_post X U s sc req r -> Q r) -> itok (alloc_group fuel sc req s) Q).
Proof.
induction fuel as [|f [IHs IHg]].
{ split; intros X U s sc req Q HI Hsc Hreq Hfit Hf; pose proof (need_ge2 sc); lia. }
split.
-
intros X U s sc req Q HI Hsc Hreq Hfit Hf HQ.
cbn fix beta iota delta [alloc_slot]. mbinds.
eapply try_avail_spec; [exact HI | exact Hsc | |].
+ intros s1 HI1 Hhd1 EH1 UB1. msimp. cbn [Z.eqb negb]. mbinds.
eapply IHg; [exact HI1 | exact Hsc | exact Hreq | exact Hfit | exact Hf | exact Hhd1 |].
intros [og s2] [HB [UB2 Hpost]]. msimp. cbn [fst snd] in HB, UB2, Hpost.
assert (HB' : heads_below s s2 sc) by (intros c Hc; rewrite (HB c Hc); apply EH1; lia).
assert (UB' : ub_same s s2) by (eapply ub_same_trans; [exact UB1 | exact UB2]).
destruct og as [g|].
* apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [exact HB'|]. split; [exact UB'|]. right. cbn [fst snd]. split; [lia|].
destruct Hpost as (am & H1 & H2 & H3 & H4 & H5 & H6). exists g, am. repeat (split; [assumption|]). exact H6.
* apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [exact HB'|]. split; [exact UB'|]. left. split; [reflexivity | exact Hpost].
+ intros first s1 (Hnz & g & am & HI1 & Hhd1 & U1 & Sc1 & Str1 & Hidx & EH1 & UB1). msimp.
destruct (first =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|]. cbn [negb].
apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [intros c Hc; apply EH1; lia|]. split; [exact UB1|]. right. cbn [fst snd].
split; [lia|]. exists g, am. repeat (split; [assumption|]). split; [lia | lia].
-
intros X U s sc req Q HI Hsc Hreq Hfit Hf Hhd HQ.
pose proof (class_size_bounds sc Hsc) as [S16 Smax].
cbn fix beta iota delta [alloc_group]. mbinds.
eapply alloc_meta_spec; [exact HI | |].
{ intros s1 HI1 Fr1 EU1 UB1. msimp. apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [|split; [exact UB1 | exact HI1]].
intros c Hc. destruct Fr1 as (EA & _). unfold active_hd. rewrite EA. reflexivity. }
intros m s1 HI1 NX Km Mm Fr1 EU1 UB1. msimp. mbinds. apply itok_get. msimp. cbn zeta.
pose proof Fr1 as (EA1 & EUs1 & _ & Len1 & Emc1).
assert (Hhd1 : active_hd s1 sc = None) by (unfold active_hd; rewrite EA1; exact Hhd).
pose proof (initial_cnt_facts sc (usage_of s1 sc) Hsc) as (Hc0 & Hc0s & Hc026).
set (cnt0 := initial_cnt sc (usage_of s1 sc)) in *.
assert (FRESH : forall q a, usedX (m :: X) s1 q a -> (prid (am_mem a) < length (st_regions s1))%nat).
{ intros q a Hu. apply EU1 in Hu. pose proof (used_group_prid_lt _ _ _ _ q a HI Hu). lia. }
destruct (PGSZ / 2 <? class_size sc * cnt0 + UNIT) eqn:Ebr.
+
set (plan := mmap_plan s1 sc req cnt0 (usage_of s1 sc)).
destruct plan as [cnt needed] eqn:Ep. subst plan. cbn [fst snd].
pose proof (mmap_plan_facts s1 sc req cnt0 (usage_of s1 sc) cnt needed Hsc Hc0 Hc0s Hreq Hfit Hc026 Ep)
as (Hcnt & Hcs & Hc26 & Nmod & N4096 & Nmax & Nfit & Nreq & Npr).
mbinds. eapply account_bounce_spec; [exact HI1|]. intros s2 HI2 (Em2 & Ea2 & Er2 & Eu2 & Ec2 & _). msimp.
mbinds. eapply step_seq_spec; [exact HI2|]. intros s3 HI3 (Em3 & Ea3 & Er3 & Eu3 & Ec3 & _). msimp.
mbinds. apply itok_ask; [cbn; unfold PGSZ in N4096; clear - N4096 Nmax; lia|]. intros z _. msimp.
assert (EU3 : forall q a, usedX (m :: X) s3 q a <-> usedX (m :: X) s1 q a).
{ intros q a. unfold usedX, MTX, MT. rewrite Em3, Em2. tauto. }
destruct (z =? 0); cbn [negb].
*
mbinds. eapply free_meta_spec; [exact HI3 | left; reflexivity |]. intros s4 HI4 Sb4 Ea4 EU4 UB4. msimp.
apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [|split].
-- intros c Hc. unfold active_hd. rewrite Ea4, Ea3, Ea2, EA1. reflexivity.
-- eapply ub_same_trans; [exact UB1|]. eapply ub_same_trans; [|exact UB4].
apply ub_same_metas. rewrite Em3, Em2. reflexivity.
-- cbn [fst snd]. rewrite (remove_head_notin m X NX) in HI4. exact HI4.
*
rewrite (page_round_fixed needed Nmod).
mbinds. eapply new_region_spec; [exact HI3 | | reflexivity | unfold PGSZ in N4096; lia]. intros s4 HI4 Es4. msimp.
mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp.
set (r := length (st_regions s3)).
set (s5 := set_mmap_counter (Z.land (st_mmap_counter s4 + 1) (2 ^ 32 - 1)) s4).
pose proof (inv_ctx HI4) as (_&_&_&_&_&_&_&_&C9&_).
assert (HI5 : Inv (m :: X) None U s5) by (apply Inv_set_mmap_counter; [exact HI4 | apply land32_range; lia]).
assert (EU5 : forall q a, usedX (m :: X) s5 q a <-> usedX (m :: X) s1 q a).
{ intros q a. rewrite <- EU3. unfold usedX, MTX, MT. subst s5 s4. cbn. tauto. }
assert (Hr5 : region_of s5 r = Some (mkRegion RkMap needed [] true)).
{ subst s5 s4 r. unfold region_of. cbn [st_regions set_mmap_counter set_regions]. apply region_of_app_new. }
set (aidx := if (if cnt - 1 <? (4096 - UNIT) / class_size sc - 1 then cnt - 1 else (4096 - UNIT) / class_size sc - 1) <? 0 then 0
else if cnt - 1 <? (4096 - UNIT) / class_size sc - 1 then cnt - 1 else (4096 - UNIT) / class_size sc - 1).
assert (Haidx : 0 <= aidx <= cnt - 1).
{ subst aidx. destruct (cnt - 1 <? (4096 - UNIT) / class_size sc - 1) eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1];
(destruct (_ <? 0) eqn:E2; [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]); lia. }
assert (Hml : 1 <= needed / 4096).
{ apply Z.div_le_lower_bound; unfold PGSZ in *; lia. }
assert (Hml' : needed / 4096 * 4096 = needed).
{ pose proof (Z_div_mod_eq_full needed 4096). unfold PGSZ in Nmod. lia. }
mbinds. eapply (install_group_spec X U s5 m sc cnt aidx (needed / 4096) (SP r 0) slot_zero).
-- exact HI5.
-- exact NX.
-- exact Hsc.
-- exact Hcnt.
-- exact Haidx.
-- lia.
-- unfold active_hd. subst s5 s4. cbn [st_active set_mmap_counter set_regions]. rewrite Ea3, Ea2. exact Hhd1.
-- left. split; [reflexivity | lia].
--
right. cbn [am_sc am_last am_maplen new_am]. rewrite new_am_stride.
split; [exact Hsc|]. split; [|split].
++ intros Hlt. destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)) eqn:E.
** apply andb_prop in E as [E _]. apply Z.eqb_eq in E. split; [exact E|]. rewrite new_am_allocated by lia. reflexivity.
** lia.
++ intros H26. right. specialize (Hc26 H26). lia.
++ destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)) eqn:E.
** apply andb_prop in E as [E _]. apply Z.eqb_eq in E. rewrite E. unfold UNIT. lia.
** replace (cnt - 1 + 1) with cnt by lia. exact Hcs.
--
intros _. exists r, (mkRegion RkMap needed [] true). cbn [am_mem am_maplen am_last new_am rg_kind rg_live rg_len].
split; [reflexivity|]. split; [exact Hr5|]. split; [reflexivity|]. split; [reflexivity|].
rewrite new_am_stride. unfold PGSZ. split; [lia|]. split.
{ destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)) eqn:E.
++ apply andb_prop in E as [E _]. apply Z.eqb_eq in E. rewrite E. unfold UNIT. lia.
++ destruct (Z.eq_dec cnt 1) as [->|Hne1].
{ exfalso. cbn [Z.sub Z.eqb] in E. destruct (needed / 4096 =? 0) eqn:E2; [apply Z.eqb_eq in E2; lia | discriminate]. }
replace (cnt - 1 + 1) with cnt by lia. specialize (Nfit ltac:(lia)). lia. }
cbn [am_sc new_am]. intros Hl0 _. specialize (Npr ltac:(lia)). unfold PGSZ in Npr |- *. lia.
-- intros H0. lia.
-- intros q a Hu Hp. exfalso. apply EU5 in Hu. pose proof (FRESH q a Hu). cbn [prid] in Hp. rewrite <- Er2, <- Er3 in H. subst r. lia.
-- intros _ q a Hu _ Hp. apply EU5 in Hu. pose proof (FRESH q a Hu). cbn [prid] in Hp. rewrite <- Er2, <- Er3 in H. subst r. lia.
-- intros s6 HI6 Hhd6 U6 EH6 Er6 Ec6 UB6. msimp. apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [|split].
++ intros c Hc. rewrite (EH6 c ltac:(lia) ltac:(lia)). unfold active_hd. subst s5 s4. cbn [st_active set_mmap_counter set_regions].
rewrite Ea3, Ea2, EA1. reflexivity.
++ eapply ub_same_trans; [exact UB1|]. eapply ub_same_trans; [|exact UB6].
apply ub_same_metas. subst s5 s4. cbn. rewrite Em3, Em2. reflexivity.
++ cbn [fst snd]. eexists. split; [exact HI6|]. split; [exact Hhd6|]. split; [exact U6|].
pose proof (links_fields (Some m) (Some m) (new_am (SP r 0) sc cnt aidx (needed / 4096) slot_zero)) as (_ & Ll & Ls & _).
rewrite Ls, Ll. cbn [am_sc am_last new_am]. split; [reflexivity|]. split; [|lia].
rewrite (strip_stride _ (new_am (SP r 0) sc cnt aidx (needed / 4096) slot_zero)) by (unfold strip; reflexivity).
rewrite new_am_stride. destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)); unfold UNIT, IB in *; lia.
+
apply Z.ltb_ge in Ebr.
pose proof (nested_facts sc cnt0 Hsc ltac:(lia) Hc026 Ebr) as NF. cbv zeta in NF.
destruct NF as (H23 & Hc2 & Htot & Hj & Hj48 & Hjfit & Hjlt).
set (total := UNIT + cnt0 * class_size sc - IB) in *. set (j := size_to_class total) in *.
mbinds.
eapply (IHs (m :: X) U s1 j total); [exact HI1 | exact Hj48 | lia | exact Hjfit | |].
{ pose proof (need_nested sc j H23 ltac:(lia)). lia. }
intros [idx s2] [HB2 [UB2 Hpost]]. msimp. cbn [fst snd] in HB2, UB2, Hpost.
destruct (idx <? 0) eqn:Eneg.
*
apply Z.ltb_lt in Eneg. destruct Hpost as [[_ HI2] | [Hge _]]; [|cbn [fst] in Hge; lia]. cbn [snd] in HI2.
mbinds. eapply free_meta_spec; [exact HI2 | left; reflexivity |]. intros s3 HI3 Sb3 Ea3 EU3 UB3. msimp.
apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [|split].
-- intros c Hc. pose proof (HB2 c ltac:(lia)) as E. unfold active_hd in E |- *. rewrite Ea3, E, EA1. reflexivity.
-- eapply ub_same_trans; [exact UB1|]. eapply ub_same_trans; [exact UB2 | exact UB3].
-- cbn [fst snd]. rewrite (remove_head_notin m X NX) in HI3. exact HI3.
* apply Z.ltb_ge in Eneg. destruct Hpost as [[Hm1 _] | [_ (g & am & HI2 & Hhd2 & U2 & Sc2 & Str2 & Hidx2)]]; [cbn [fst] in Hm1; lia|].
cbn [fst snd] in HI2, Hhd2, U2, Hidx2, HB2.
mbinds. apply itok_get_head. msimp. change (nth (Z.to_nat j) (st_active s2) None) with (active_hd s2 j). rewrite Hhd2. msimp.
pose proof (inv_groups HI2 g am U2) as G2. pose proof G2 as ((_ & _ & Glen & _) & Gml & _ & Gcl & _).
assert (Hstr : stride_of am = class_size j).
{ destruct Gcl as [(C63 & _) | (_ & _ & C26 & _)]; [lia|]. specialize (C26 ltac:(lia)).
unfold stride_of. rewrite Sc2. destruct C26 as [C|C]; [rewrite C|].
- destruct (am_last am =? 0); reflexivity.
- destruct (am_last am =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
mbinds. eapply itok_getm; [exact (proj1 (usedX_MT _ _ _ _ U2))|]. msimp.
mbinds. apply itok_mcheck; [rewrite Hstr; apply Z.eqb_refl|]. msimp.
mbinds. apply itok_get. msimp.
pose proof (inv_ctx HI2) as (_&_&_&_&_&_&_&_&C9&_).
mbinds. eapply (enframe_spec (m :: X) U s2 g idx (class_size j - IB) (st_mmap_counter s2) FGroup am);
[exact HI2 | exact U2 | pose proof (class_size_bounds j Hj48); unfold IB; lia | rewrite Hstr; lia | lia | intros _; rewrite Hstr; reflexivity | intros H63; exfalso; lia
| intros _ _; rewrite Sc2; exact Hhd2 |].
intros off s3 hdr Hoff Hofit Hoff0 Es3 HI3. msimp. specialize (Hoff0 eq_refl). subst off. rewrite Z.mul_0_r, padd_0.
set (am' := upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame 0 (class_size j - IB) FGroup)))) in Es3.
pose proof (upd_slot_fields am idx (mkSlot (Some hdr) (Some (mkFrame 0 (class_size j - IB) FGroup)))) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold am' in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
assert (U3 : usedX (m :: X) s3 g am').
{ rewrite Es3. apply usedX_upd. left. pose proof (usedX_MT _ _ _ _ U2) as [_ NXg]. auto. }
assert (Hext1 : group_extent (new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk) = total).
{ unfold group_extent. rewrite new_am_stride. cbn [am_last new_am Z.eqb andb negb].
destruct (cnt0 - 1 =? 0); cbn [andb]; subst total; (replace (cnt0 - 1 + 1) with cnt0 by lia); lia. }
mbinds. eapply (install_group_spec X U s3 m sc cnt0 (cnt0 - 1) 0 (slot_start am idx) slot_junk).
-- exact HI3.
-- exact NX.
-- exact Hsc.
-- lia.
-- lia.
-- lia.
-- rewrite Es3. unfold active_hd. cbn. pose proof (HB2 sc ltac:(lia)) as E. unfold active_hd in E. rewrite E, EA1. exact Hhd.
-- right. split; reflexivity.
-- right. cbn [am_sc am_last am_maplen new_am]. rewrite new_am_stride. cbn [Z.eqb andb negb].
replace ((cnt0 - 1 =? 0) && false) with false by (destruct (cnt0 - 1 =? 0); reflexivity).
split; [exact Hsc|]. split; [lia|]. split; [auto|]. replace (cnt0 - 1 + 1) with cnt0 by lia. exact Hc0s.
-- intros H0. cbn in H0. lia.
-- intros _. exists g, am', idx, (mkFrame 0 (class_size j - IB) FGroup). rewrite Fl, Fsc, Fss. cbn [fr_kind fr_n].
split; [exact U3|]. split; [lia|]. split.
{ unfold am'. rewrite nth_slot_upd_slot by (try lia; rewrite Glen; lia). rewrite Z.eqb_refl. reflexivity. }
split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. subst total. unfold UNIT, IB in *. nia.
-- intros q a Hu Hp. rewrite prid_slot_start in Hp. rewrite Es3 in Hu.
assert (Htot2 : 0 < total <= class_size j - IB).
{ pose proof Hjfit as HJ. subst total. unfold UNIT, IB in *. split; [nia | lia]. }
destruct (nested_lam (m :: X) U s2 g idx am hdr (class_size j - IB) q a sc cnt0 HI2 U2 ltac:(rewrite Hstr; reflexivity)
ltac:(rewrite Hext1; exact Htot2) Hu Hp) as [D | [I | P]].
++ left. exact D.
++ right; left. rewrite Es3. exact I.
++ right; right. split; [reflexivity|]. exact P.
-- intros H0. lia.
-- intros s4 HI4 Hhd4 U4 EH4 Er4 Ec4 UB4. msimp. apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [|split].
++ intros c Hc. rewrite (EH4 c ltac:(lia) ltac:(lia)). rewrite Es3. unfold active_hd. cbn [st_active upd_meta set_metas].
pose proof (HB2 c ltac:(lia)) as E. unfold active_hd in E. rewrite E, EA1. reflexivity.
++ eapply ub_same_trans; [exact UB1|]. eapply ub_same_trans; [exact UB2|]. eapply ub_same_trans; [|exact UB4].
rewrite Es3. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ U2))|].
rewrite (proj1 (usedX_MT _ _ _ _ U2)). cbn. apply blocks_of_upd_slot_same; [lia | exact Glen |].
unfold slotst_block, slot_block. cbn. destruct (inv_reserved HI2 g idx eq_refl) as (am_ & U_ & _ & Hfr_ & _).
pose proof (usedX_fun _ _ _ _ _ U_ U2) as E_. rewrite E_ in Hfr_. rewrite Hfr_. reflexivity.
++ cbn [fst snd]. eexists. split; [exact HI4|]. split; [exact Hhd4|]. split; [exact U4|].
pose proof (links_fields (Some m) (Some m) (new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk)) as (_ & Ll & Ls & _).
rewrite Ls, Ll. cbn [am_sc am_last new_am]. split; [reflexivity|]. split; [|lia].
rewrite (strip_stride _ (new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk)) by (unfold strip; reflexivity).
rewrite new_am_stride. cbn [Z.eqb andb negb]. replace ((cnt0 - 1 =? 0) && false) with false by (destruct (cnt0 - 1 =? 0); reflexivity). lia.
Qed.

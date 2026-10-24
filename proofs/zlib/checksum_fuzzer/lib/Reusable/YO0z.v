(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s
YO11 YO15 YO12.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Lemma region_of_app_old s l k : (k < length (st_regions s))%nat ->
region_of (set_regions (st_regions s ++ l) s) k = region_of s k.
Proof. intros Hk. unfold region_of. cbn. rewrite nth_error_app1 by exact Hk. reflexivity. Qed.
Lemma region_of_app_new s x : region_of (set_regions (st_regions s ++ [x]) s) (length (st_regions s)) = Some x.
Proof. unfold region_of. cbn. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.
Lemma nth_error_Some_lt {A} (l : list A) k x : nth_error l k = Some x -> (k < length l)%nat.
Proof.
revert k. induction l as [|h t IH]; intros [|k] H; cbn in H; try discriminate; cbn; [lia|].
apply IH in H. lia.
Qed.
Lemma region_of_lt s k rg : region_of s k = Some rg -> (k < length (st_regions s))%nat.
Proof. unfold region_of. apply nth_error_Some_lt. Qed.
Lemma region_of_app s l k rg : region_of s k = Some rg -> region_of (set_regions (st_regions s ++ l) s) k = Some rg.
Proof. intros H. rewrite region_of_app_old; [exact H | eapply region_of_lt; exact H]. Qed.
Lemma region_of_upd s r f k :
region_of (set_regions (lupd (st_regions s) r f) s) k =
if (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool then Some f else region_of s k.
Proof. unfold region_of. cbn. apply nth_error_lupd. Qed.
Lemma InvMeta_regions X R U s rs :
(forall k rg, region_of s k = Some rg -> rg_kind rg = RkMap -> region_of (set_regions rs s) k = Some rg) ->
InvMeta X R U s -> InvMeta X R U (set_regions rs s).
Proof.
intros Hreg (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
assert (EU : forall g am, usedX X (set_regions rs s) g am <-> usedX X s g am) by (intros; unfold usedX, MTX, MT; cbn; tauto).
split; [exact M1|]. split.
{ intros g am Hg. pose proof (M2 g am Hg) as (G1 & G2 & G3 & G4 & G5 & G6).
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [|exact G6].
intros Hm. destruct (G5 Hm) as (r & rg & H1 & H2 & H3 & H4 & H5 & H6). exists r, rg.
split; [exact H1|]. split; [apply Hreg; assumption|]. auto. }
split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|]. split; [exact M7 | exact M8].
Qed.
Lemma area_slots_disjoint s a1 a2 k1 k2 :
areas_ok s -> In a1 (st_areas s) -> In a2 (st_areas s) -> a1 <> a2 ->
0 <= k1 < METAS_PER_AREA -> 0 <= k2 < METAS_PER_AREA ->
padd a1 (AREA_HDR + META_SIZE * k1) <> padd a2 (AREA_HDR + META_SIZE * k2).
Proof.
intros A H1 H2 Hne Hk1 Hk2 E.
destruct A as (_ & Aok & _).
destruct (Aok a1 H1) as (r1 & o1 & rg1 & -> & Ho1 & _).
destruct (Aok a2 H2) as (r2 & o2 & rg2 & -> & Ho2 & _).
pose proof (f_equal prid E) as Er. pose proof (f_equal poff E) as Eo. cbn [prid poff padd] in Er, Eo. subst r2.
assert (o1 <> o2) by (intros ->; apply Hne; reflexivity).
pose proof (eq_refl : AREA_HDR = 24) as C1. pose proof (eq_refl : META_SIZE = 40) as C2.
pose proof (eq_refl : METAS_PER_AREA = 101) as C3. pose proof (eq_refl : PGSZ = 4096) as C4.
rewrite C4 in Ho1, Ho2.
pose proof (Z_div_mod_eq_full o1 4096) as D1. pose proof (Z_div_mod_eq_full o2 4096) as D2.
rewrite Ho1 in D1. rewrite Ho2 in D2.
remember (o1 / 4096) as q1 eqn:Q1. remember (o2 / 4096) as q2 eqn:Q2. clear Q1 Q2. lia.
Qed.
Lemma area_slot_inj a k1 k2 :
padd a (AREA_HDR + META_SIZE * k1) = padd a (AREA_HDR + META_SIZE * k2) -> k1 = k2.
Proof. destruct a. intros E. pose proof (f_equal poff E) as Eo. cbn [poff padd] in Eo. pose proof (eq_refl : META_SIZE = 40). lia. Qed.
Lemma take_slot_Inv X R U s :
Inv X R U s -> 0 < st_avail_meta_count s ->
let m := st_avail_meta s in
let s' := upd_meta m MRaw (set_avail_meta (padd m META_SIZE) (set_avail_meta_count (st_avail_meta_count s - 1) s)) in
~ In m (keys s) /\ memb m X = false /\ Inv (m :: X) R U s' /\
(forall g am, usedX (m :: X) s' g am <-> usedX X s g am).
Proof.
intros HI Hc m s'.
pose proof (inv_keys HI) as (Knd & Kpl & Kemp & Kav & Krange).
assert (Hne : st_areas s <> []) by (intros E; pose proof (Kemp E); lia).
set (la := last (st_areas s) (SP 0%nat 0)) in *.
assert (Hla : In la (st_areas s)) by (subst la; apply In_last; exact Hne).
pose proof (Kav Hne) as Em. fold m in Em.
assert (Hfresh : ~ In m (keys s)).
{ intros Hin. destruct (Kpl m Hin) as (a & k & Ha & Hk & Ep).
unfold handed in Hk. fold la in Hk.
destruct (sptr_eq_dec a la) as [->|Hna].
- rewrite sptr_eqb_refl in Hk. rewrite Em in Ep. apply area_slot_inj in Ep. lia.
- replace (sptr_eqb a la) with false in Hk by (symmetry; apply sptr_eqb_neq; exact Hna).
rewrite Em in Ep.
refine (area_slots_disjoint s la a (METAS_PER_AREA - st_avail_meta_count s) k (inv_areas HI) Hla Ha _ _ _ Ep).
+ intros E. apply Hna. symmetry. exact E.
+ pose proof (eq_refl : METAS_PER_AREA = 101). unfold METAS_PER_AREA in *. lia.
+ pose proof (eq_refl : METAS_PER_AREA = 101). unfold METAS_PER_AREA in *. lia. }
assert (NXm : memb m X = false).
{ apply memb_false_notIn. intros Hx. apply Hfresh. exact (proj1 (inv_X HI m Hx)). }
set (s1 := set_avail_meta (padd m META_SIZE) (set_avail_meta_count (st_avail_meta_count s - 1) s)).
assert (K1 : keys s' = keys s ++ [m]).
{ subst s'. rewrite keys_upd_notIn; [reflexivity|]. exact Hfresh. }
assert (EMT : forall q, q <> m -> MT s' q = MT s q).
{ intros q Hq. subst s'. rewrite MT_upd_other by exact Hq. reflexivity. }
assert (Mm : MT s' m = Some MRaw) by (subst s'; apply MT_upd_same).
assert (Mm0 : MT s m = None) by (unfold MT; apply mlookup_None_iff; exact Hfresh).
assert (EU : forall g am, usedX (m :: X) s' g am <-> usedX X s g am).
{ intros g am. unfold usedX, MTX. rewrite memb_cons. destruct (sptr_eqb g m) eqn:E; cbn [orb].
- apply sptr_eqb_eq in E. subst g. rewrite NXm, Mm0. split; discriminate.
- rewrite EMT by (apply sptr_eqb_neq; exact E). tauto. }
split; [exact Hfresh|]. split; [exact NXm|]. split; [|exact EU].
assert (EMTX : forall q, MTX (m :: X) s' q = match MTX X s q with Some x => Some x | None => None end).
{ intros q. unfold MTX. rewrite memb_cons. destruct (sptr_eqb q m) eqn:E; cbn [orb].
- apply sptr_eqb_eq in E. subst q. rewrite NXm, Mm0. reflexivity.
- rewrite EMT by (apply sptr_eqb_neq; exact E). destruct (memb q X); [reflexivity|]. destruct (MT s q); reflexivity. }
assert (EMTX' : forall q, MTX (m :: X) s' q = MTX X s q).
{ intros q. rewrite EMTX. destruct (MTX X s q); reflexivity. }
eapply (Inv_surgery X (m :: X) R R U U s s' HI).
- intros k rg Hk _. exact Hk.
- intros p am' Hp. exists am'. split; [apply EU; exact Hp | reflexivity].
- intros p am Hp. left. exists am. split; [apply EU; exact Hp | reflexivity].
- intros g i HR. destruct (inv_reserved HI g i HR) as (am & Hu & Hrest). exists am. split; [apply EU; exact Hu | exact Hrest].
- intros p i am' _. left. tauto.
-
pose proof (inv_ctx HI) as C. unfold ctx_ok in *. subst s' s1. unfold upd_meta. cbn -[Z.pow Z.lt Z.le].
destruct C as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12).
refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj C11 _))))))))))).
intros Hi. exfalso. destruct (C12 Hi) as (_ & Ha & _). exact (Hne Ha).
-
unfold keys_ok. rewrite K1.
assert (Ea : st_areas s' = st_areas s) by reflexivity. rewrite Ea.
assert (Ev : st_avail_meta s' = padd m META_SIZE) by reflexivity.
assert (Ec : st_avail_meta_count s' = st_avail_meta_count s - 1) by reflexivity.
assert (Eh : forall a, handed s' a = if sptr_eqb a la then METAS_PER_AREA - (st_avail_meta_count s - 1) else METAS_PER_AREA).
{ intros a. unfold handed. rewrite Ea, Ec. fold la. reflexivity. }
split.
{ apply NoDup_app_single; assumption. }
split.
{ intros p Hp. apply in_app_iff in Hp as [Hp | [<- | []]].
- destruct (Kpl p Hp) as (a & k & Ha & Hk & Ep). exists a, k. split; [exact Ha|]. split; [|exact Ep].
rewrite Eh. unfold handed in Hk. fold la in Hk. destruct (sptr_eqb a la); lia.
- exists la, (METAS_PER_AREA - st_avail_meta_count s). split; [exact Hla|]. split; [|exact Em].
rewrite Eh, sptr_eqb_refl. lia. }
split; [intros E; exfalso; exact (Hne E)|].
split; [|rewrite Ec; lia].
intros _. rewrite Ev, Ec, Em. fold la. destruct la; cbn [padd]. f_equal. pose proof (eq_refl : META_SIZE = 40). lia.
- exact (inv_areas HI).
-
intros x [<-|Hx].
+ rewrite K1, Mm. split; [apply in_app_iff; right; left; reflexivity | exact I].
+ destruct (inv_X HI x Hx) as [Kx Mx]. rewrite K1. split; [apply in_app_iff; left; exact Kx|].
rewrite EMT; [exact Mx|]. intros ->. exact (Hfresh Kx).
-
destruct (inv_rings HI) as (F & A & D). split; [|split].
+ destruct F as (ms & FR & Fall). exists ms. split.
* eapply ring_ok_ext; [|exact FR]. intros q _. unfold flinks. rewrite EMTX'. reflexivity.
* intros q pr nx Hq. rewrite EMTX' in Hq. eapply Fall. exact Hq.
+ intros sc Hsc. destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
change (active_hd s' sc) with (active_hd s sc).
split; [eapply ring_ok_ext; [|exact Rg]; intros q _; unfold alinks; rewrite EMTX'; reflexivity|].
split; [intros q am Hq; apply EU in Hq; apply Mem; exact Hq|].
split; [intros q am Hq; apply EU in Hq; apply Full; exact Hq|].
split; [intros q am Hq; apply EU in Hq; apply Q1; exact Hq|].
intros q am Hq; apply EU in Hq; apply Q2; exact Hq.
+ intros q am Hq. apply EU in Hq. apply (D q am Hq).
-
intros sc Hsc. change (usage_of s' sc) with (usage_of s sc). rewrite (inv_usage HI sc Hsc). f_equal.
unfold class_sum. rewrite K1, fold_right_app. cbn [fold_right].
replace (contrib (m :: X) s' sc m) with 0.
2:{ unfold contrib, MTX. rewrite memb_cons, sptr_eqb_refl. reflexivity. }
rewrite Z.add_0_l || idtac.
assert (E : forall l acc, fold_right (fun q a => contrib (m :: X) s' sc q + a) acc l =
fold_right (fun q a => contrib X s sc q + a) acc l).
{ induction l as [|k t IH]; intros acc; [reflexivity|]. cbn [fold_right]. rewrite IH. unfold contrib. rewrite EMTX'. reflexivity. }
rewrite E. cbn. lia.
Qed.
Lemma Inv_nonmeta X R U s s' :
Inv X R U s ->
st_metas s' = st_metas s -> st_active s' = st_active s ->
st_free_meta_head s' = st_free_meta_head s -> st_usage s' = st_usage s ->
(forall k rg, region_of s k = Some rg -> rg_kind rg = RkMap -> region_of s' k = Some rg) ->
ctx_ok s' -> keys_ok s' -> areas_ok s' -> Inv X R U s'.
Proof.
intros HI Em Ea Ef Eu Hreg C K A.
assert (EMT : forall q, MT s' q = MT s q) by (intros; unfold MT; rewrite Em; reflexivity).
assert (EU : forall g am, usedX X s' g am <-> usedX X s g am) by (intros; unfold usedX, MTX; rewrite EMT; tauto).
eapply (Inv_surgery X X R R U U s s' HI).
- exact Hreg.
- intros p am' Hp. exists am'. split; [apply EU; exact Hp | reflexivity].
- intros p am Hp. left. exists am. split; [apply EU; exact Hp | reflexivity].
- intros g i HR. destruct (inv_reserved HI g i HR) as (am & Hu & Hrest). exists am. split; [apply EU; exact Hu | exact Hrest].
- intros p i am' _. left. tauto.
- exact C. - exact K. - exact A.
- intros x Hx. destruct (inv_X HI x Hx) as [Kx Mx]. unfold keys. rewrite Em, EMT. split; [exact Kx | exact Mx].
- destruct (inv_rings HI) as (F & AR & D). split; [|split].
+ destruct F as (ms & FR & Fall). exists ms. rewrite Ef. split.
* eapply ring_ok_ext; [|exact FR]. intros q _. unfold flinks, MTX. rewrite EMT. reflexivity.
* intros q pr nx Hq. unfold MTX in *. rewrite EMT in Hq. eapply Fall. exact Hq.
+ intros sc Hsc. destruct (AR sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
replace (active_hd s' sc) with (active_hd s sc) by (unfold active_hd; rewrite Ea; reflexivity).
split; [eapply ring_ok_ext; [|exact Rg]; intros q _; unfold alinks, MTX; rewrite EMT; reflexivity|].
split; [intros q am Hq; apply EU in Hq; apply Mem; exact Hq|].
split; [intros q am Hq; apply EU in Hq; apply Full; exact Hq|].
split; [intros q am Hq; apply EU in Hq; apply Q1; exact Hq|].
intros q am Hq; apply EU in Hq; apply Q2; exact Hq.
+ intros q am Hq. apply EU in Hq. apply (D q am Hq).
- intros sc Hsc. unfold usage_of. rewrite Eu. pose proof (inv_usage HI sc Hsc) as E. unfold usage_of in E. rewrite E.
f_equal. unfold class_sum, keys. rewrite Em.
assert (EE : forall l, fold_right (fun q a => contrib X s' sc q + a) 0 l = fold_right (fun q a => contrib X s sc q + a) 0 l).
{ induction l as [|k t IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. unfold contrib, MTX. rewrite EMT. reflexivity. }
symmetry. apply EE.
Qed.
Lemma Inv_brk_dead X R U s :
Inv X R U s -> st_brk s <> BrkDead -> st_init_done s = true -> Inv X R U (set_brk BrkDead s).
Proof.
intros HI Hb Hinit. eapply Inv_nonmeta; try exact HI; try reflexivity.
- intros k rg Hk _. exact Hk.
- pose proof (inv_ctx HI) as C. unfold ctx_ok in *.
destruct C as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12).
refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj C11 _))))))))))).
cbn [st_init_done set_brk]. intros Hi. rewrite Hinit in Hi. discriminate.
- exact (inv_keys HI).
- pose proof (inv_areas HI) as A. unfold areas_ok in *.
destruct A as (A1&A2&A3&A4&A5&A6&A7&A8).
refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj _ A8))))))).
cbn [st_brk set_brk]. change (brk_regions (set_brk BrkDead s)) with (brk_regions s).
change (region_of (set_brk BrkDead s)) with (region_of s).
destruct (st_brk s) as [| |r p] eqn:Eb.
+ intros r Hr. rewrite A7 in Hr. destruct Hr.
+ exfalso. apply Hb. reflexivity.
+ intros r' Hr'. destruct A7 as (Hbr & rg & Hrg & Hl & Hlen & Hp). rewrite Hbr in Hr' |- *.
destruct Hr' as [<-|[]]. split; [reflexivity|]. exists rg. split; [exact Hrg|]. split; [exact Hl|].
rewrite Hlen. pose proof (eq_refl : PGSZ = 4096). split; [|nia].
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma brk_regions_app s x :
brk_regions (set_regions (st_regions s ++ [x]) s) =
brk_regions s ++ match rg_kind x with RkBrk => [length (st_regions s)] | _ => [] end.
Proof.
unfold brk_regions. cbn [st_regions set_regions]. rewrite length_app. cbn [length].
rewrite Nat.add_1_r, seq_S, flat_map_app. cbn [flat_map]. rewrite region_of_app_new, app_nil_r. f_equal.
apply flat_map_ext_In. intros k Hk. apply in_seq in Hk. rewrite region_of_app_old by lia. reflexivity.
Qed.
Lemma brk_regions_upd s r x rg :
region_of s r = Some rg -> rg_kind x = rg_kind rg ->
brk_regions (set_regions (lupd (st_regions s) r x) s) = brk_regions s.
Proof.
intros Hr Hk. unfold brk_regions. cbn [st_regions set_regions]. rewrite length_lupd.
apply flat_map_ext_In. intros k Hk'. rewrite region_of_upd.
destruct (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool eqn:E; [|reflexivity].
apply andb_prop in E as [E1 _]. apply Nat.eqb_eq in E1. subst k. rewrite Hr, Hk. reflexivity.
Qed.
Lemma resv_total_app s x :
resv_total (set_regions (st_regions s ++ [x]) s) =
resv_total s + match rg_kind x with RkMetaRes => rg_len x | _ => 0 end.
Proof.
unfold resv_total. cbn [st_regions set_regions]. rewrite fold_right_app. cbn [fold_right].
assert (G : forall l acc, fold_right (fun rg a => match rg_kind rg with RkMetaRes => rg_len rg + a | _ => a end) acc l =
fold_right (fun rg a => match rg_kind rg with RkMetaRes => rg_len rg + a | _ => a end) 0 l + acc).
{ induction l as [|h t IH]; intros acc; cbn; [lia|]. rewrite IH. destruct (rg_kind h); lia. }
rewrite G. destruct (rg_kind x); lia.
Qed.
Lemma resv_total_upd s r x rg :
region_of s r = Some rg ->
match rg_kind rg with RkMetaRes => rg_kind x = RkMetaRes /\ rg_len x = rg_len rg | _ => rg_kind x <> RkMetaRes end ->
resv_total (set_regions (lupd (st_regions s) r x) s) = resv_total s.
Proof.
unfold resv_total, region_of. cbn [st_regions set_regions].
revert r. induction (st_regions s) as [|h t IH]; intros [|r] Hr Hk; cbn in Hr |- *; try discriminate.
- injection Hr as ->. destruct (rg_kind rg) eqn:E.
+ destruct (rg_kind x); [reflexivity| congruence | reflexivity].
+ destruct Hk as [-> ->]. reflexivity.
+ destruct (rg_kind x); [reflexivity | congruence | reflexivity].
- rewrite (IH r Hr Hk). reflexivity.
Qed.
Lemma Inv_new_resv X R U s :
Inv X R U s -> st_avail_meta_area_count s = 0 -> st_init_done s = true ->
let n := Z.shiftl 2 (st_meta_alloc_shift s) in
let r := length (st_regions s) in
Inv X R U (set_meta_alloc_shift (st_meta_alloc_shift s + 1)
(set_avail_meta_area_count (n - 1)
(set_avail_meta_areas (SP r PGSZ)
(set_regions (st_regions s ++ [mkRegion RkMetaRes (n * PGSZ) [] true]) s)))).
Proof.
intros HI Hc0 Hinit n r.
pose proof (inv_ctx HI) as C. pose proof C as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12).
assert (Hn : n = 2 * 2 ^ st_meta_alloc_shift s) by (subst n; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
assert (Hpow : 1 <= 2 ^ st_meta_alloc_shift s).
{ pose proof (Z.pow_pos_nonneg 2 (st_meta_alloc_shift s)). lia. }
assert (Hn2 : 2 <= n) by lia.
pose proof (eq_refl : PGSZ = 4096) as HP.
set (x := mkRegion RkMetaRes (n * PGSZ) [] true).
set (s' := set_meta_alloc_shift _ _).
assert (ERG : forall k, region_of s' k = region_of (set_regions (st_regions s ++ [x]) s) k) by reflexivity.
eapply Inv_nonmeta; try exact HI; try reflexivity.
- intros k rg Hk _. rewrite ERG. apply region_of_app. exact Hk.
- unfold ctx_ok. subst s'. simp_st.
refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj _ (conj _ _))))))))))); [lia | lia |].
intros Hi. rewrite Hinit in Hi. discriminate.
- exact (inv_keys HI).
- pose proof (inv_areas HI) as (A1&A2&A3&A4&A5&A6&A7&A8&A9). unfold areas_ok.
refine (conj A1 (conj _ (conj A3 (conj A4 (conj _ (conj _ (conj _ (conj _ _)))))))).
+ intros a Ha. destruct (A2 a Ha) as (ra & oa & rga & Ea & Ho & Hlo & Hrg & Hl & Hhi & Hk).
exists ra, oa, rga. repeat (split; [assumption|]). split; [| split; [exact Hl | split; [exact Hhi | exact Hk]]].
rewrite ERG. apply region_of_app. exact Hrg.
+ intros k rg Hk Hkind. rewrite ERG in Hk.
unfold region_of in Hk. cbn [st_regions set_regions] in Hk. rewrite nth_error_app in Hk.
destruct (Nat.ltb k (length (st_regions s))) eqn:El.
* eapply A5; [exact Hk | exact Hkind].
* destruct (k - length (st_regions s))%nat as [|k'] eqn:Ek; cbn in Hk; [|destruct k'; discriminate].
injection Hk as <-. unfold x. cbn [rg_live rg_len]. split; [reflexivity|]. split; [|nia]. rewrite HP. apply Z_mod_mult.
+ change (resv_total (set_regions (st_regions s ++ [x]) s) = 2 * PGSZ * (2 ^ (st_meta_alloc_shift s + 1) - 1)).
rewrite resv_total_app. unfold x. cbn [rg_kind rg_len]. rewrite A6, Z.pow_add_r, Hn by lia. change (2 ^ 1) with 2. lia.
+ change (st_brk s') with (st_brk s).
assert (EB : brk_regions s' = brk_regions s).
{ change (brk_regions (set_regions (st_regions s ++ [x]) s) = brk_regions s).
rewrite brk_regions_app. unfold x. cbn [rg_kind]. apply app_nil_r. }
rewrite EB.
destruct (st_brk s) as [| |rb pb].
* exact A7.
* intros rr Hrr. destruct (A7 rr Hrr) as (Hbr & rg & Hrg & Hrest). split; [exact Hbr|]. exists rg.
split; [rewrite ERG; apply region_of_app; exact Hrg | exact Hrest].
* destruct A7 as (Hbr & rg & Hrg & Hrest). split; [exact Hbr|]. exists rg.
split; [rewrite ERG; apply region_of_app; exact Hrg | exact Hrest].
+ change (st_avail_meta_area_count s') with (n - 1). change (st_avail_meta_areas s') with (SP r PGSZ).
intros _. exists r, PGSZ, x.
split; [reflexivity|]. split.
{ rewrite ERG. subst r. apply region_of_app_new. }
unfold x. cbn [rg_kind rg_live rg_len rg_rw]. split; [reflexivity|]. split; [reflexivity|].
split; [rewrite HP; reflexivity|]. split; [lia|]. split; [nia|]. intros y [].
+ intros k rg Hk. rewrite ERG in Hk. unfold region_of in Hk. cbn [st_regions set_regions] in Hk. rewrite nth_error_app in Hk.
destruct (Nat.ltb k (length (st_regions s))); [eapply A9; exact Hk|].
destruct (k - length (st_regions s))%nat as [|k']; cbn in Hk; [injection Hk as <-; cbn; nia | destruct k'; discriminate].
Qed.
Definition open_st (p : sptr) (s : astate) : astate :=
set_avail_meta (padd p AREA_HDR)
(set_avail_meta_count METAS_PER_AREA
(set_areas (st_areas s ++ [p])
(set_area_head (match st_area_head s with None => Some p | h => h end)
(set_area_tail (Some p)
(set_avail_meta_areas (padd p 4096)
(set_avail_meta_area_count (st_avail_meta_area_count s - 1) s)))))).
Lemma st_areas_open p s : st_areas (open_st p s) = st_areas s ++ [p]. Proof. reflexivity. Qed.
Lemma st_area_head_open p s : st_area_head (open_st p s) = match st_area_head s with None => Some p | h => h end. Proof. reflexivity. Qed.
Lemma st_area_tail_open p s : st_area_tail (open_st p s) = Some p. Proof. reflexivity. Qed.
Lemma st_regions_open p s : st_regions (open_st p s) = st_regions s. Proof. reflexivity. Qed.
Lemma st_brk_open p s : st_brk (open_st p s) = st_brk s. Proof. reflexivity. Qed.
Lemma st_shift_open p s : st_meta_alloc_shift (open_st p s) = st_meta_alloc_shift s. Proof. reflexivity. Qed.
Lemma st_area_count_open p s : st_avail_meta_area_count (open_st p s) = st_avail_meta_area_count s - 1. Proof. reflexivity. Qed.
Lemma st_areas_ptr_open p s : st_avail_meta_areas (open_st p s) = padd p 4096. Proof. reflexivity. Qed.
Lemma region_of_open p s k : region_of (open_st p s) k = region_of s k. Proof. reflexivity. Qed.
Lemma brk_regions_open p s : brk_regions (open_st p s) = brk_regions s. Proof. reflexivity. Qed.
Lemma resv_total_open p s : resv_total (open_st p s) = resv_total s. Proof. reflexivity. Qed.
Lemma st_metas_open p s : st_metas (open_st p s) = st_metas s. Proof. reflexivity. Qed.
Lemma keys_ok_open s p :
keys_ok s -> st_avail_meta_count s = 0 -> ~ In p (st_areas s) ->
keys_ok (open_st p s).
Proof.
intros (Knd & Kpl & Kemp & Kav & Krange) Hc0 Hfresh.
unfold keys_ok, key_placed, handed. unfold open_st. simp_st.
change (keys (set_avail_meta _ _)) with (keys s).
rewrite last_app_single.
split; [exact Knd|]. split.
{ intros q Hq. destruct (Kpl q Hq) as (a & k & Ha & Hk & E). exists a, k.
split; [apply in_app_iff; left; exact Ha|]. split; [|exact E].
unfold handed in Hk. replace (sptr_eqb a p) with false by (symmetry; apply sptr_eqb_neq; intros ->; exact (Hfresh Ha)).
destruct (sptr_eqb a (last (st_areas s) (SP 0%nat 0))); lia. }
split; [intros E; destruct (st_areas s); discriminate|].
split; [| pose proof (eq_refl : METAS_PER_AREA = 101); lia].
intros _. rewrite Z.sub_diag, Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
Lemma ctx_ok_open s p :
ctx_ok s -> st_init_done s = true -> 1 <= st_avail_meta_area_count s -> ctx_ok (open_st p s).
Proof.
intros C Hi Hc. unfold ctx_ok in *. unfold open_st. simp_st.
destruct C as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12).
refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj _ _))))))))))); [lia|].
intros H. rewrite Hi in H. discriminate.
Qed.
Lemma brk_regions_In s r : In r (brk_regions s) -> exists rg, region_of s r = Some rg /\ rg_kind rg = RkBrk.
Proof.
unfold brk_regions. intros H. apply in_flat_map in H as (k & Hk & Hin).
destruct (region_of s k) as [rg|] eqn:E; [|destruct Hin].
destruct (rg_kind rg) eqn:Ek; try (destruct Hin; fail); destruct Hin as [<-|[]].
exists rg. auto.
Qed.
Lemma Inv_open_resv X R U s r o rg :
Inv X R U s -> 0 < st_avail_meta_area_count s -> st_avail_meta_count s = 0 -> st_init_done s = true ->
st_avail_meta_areas s = SP r o -> region_of s r = Some rg ->
Inv X R U (open_st (SP r o) (set_regions (lupd (st_regions s) r (mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [o]) (rg_live rg))) s)).
Proof.
intros HI Hc Hm0 Hinit Ep Hrg.
pose proof (inv_areas HI) as (A1&A2&A3&A4&A5&A6&A7&A8&A9).
destruct (A8 Hc) as (r' & o' & rg' & Ep' & Hrg' & Hk & Hl & Ho & Hlo & Hlen & Hrw).
rewrite Ep in Ep'. injection Ep' as <- <-. rewrite Hrg in Hrg'. injection Hrg' as <-.
set (x := mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [o]) (rg_live rg)).
set (s1 := set_regions (lupd (st_regions s) r x) s).
pose proof (region_of_lt _ _ _ Hrg) as Hrlt.
assert (ERG : forall k, region_of (open_st (SP r o) s1) k = region_of s1 k) by reflexivity.
assert (R1 : region_of s1 r = Some x).
{ subst s1. rewrite region_of_upd, Nat.eqb_refl. replace (Nat.ltb r (length (st_regions s))) with true; [reflexivity|].
symmetry. apply Nat.ltb_lt. exact Hrlt. }
assert (R2 : forall k, k <> r -> region_of s1 k = region_of s k).
{ intros k Hk'. subst s1. rewrite region_of_upd. replace (Nat.eqb k r) with false; [reflexivity|].
symmetry. apply Nat.eqb_neq. exact Hk'. }
assert (Hfresh : ~ In (SP r o) (st_areas s)).
{ intros Hin. destruct (A2 _ Hin) as (r2 & o2 & rg2 & E2 & _ & _ & Hrg2 & _ & _ & Hkind2).
injection E2 as <- <-. rewrite Hrg in Hrg2. injection Hrg2 as <-. rewrite Hk in Hkind2.
pose proof (Hrw o Hkind2). lia. }
pose proof (eq_refl : PGSZ = 4096) as HP.
eapply Inv_nonmeta; try exact HI; try reflexivity.
- intros k rgk Hk' Hkind. rewrite ERG. destruct (Nat.eq_dec k r) as [->|Hne].
+ rewrite Hrg in Hk'. injection Hk' as ->. rewrite Hk in Hkind. discriminate.
+ rewrite R2 by exact Hne. exact Hk'.
- apply ctx_ok_open; [exact (inv_ctx HI) | exact Hinit | change (st_avail_meta_area_count s1) with (st_avail_meta_area_count s); lia].
- apply keys_ok_open; [exact (inv_keys HI) | exact Hm0 | exact Hfresh].
- unfold areas_ok.
rewrite !st_areas_open, st_area_head_open, st_area_tail_open, st_brk_open, st_shift_open,
st_area_count_open, st_areas_ptr_open, brk_regions_open, resv_total_open.
change (st_areas s1) with (st_areas s). change (st_area_head s1) with (st_area_head s).
change (st_meta_alloc_shift s1) with (st_meta_alloc_shift s). change (st_brk s1) with (st_brk s).
change (st_avail_meta_area_count s1) with (st_avail_meta_area_count s).
split.
{ apply NoDup_app_single; [exact A1 | exact Hfresh]. }
split.
{ intros a Ha. apply in_app_iff in Ha as [Ha | [<- | []]].
- destruct (A2 a Ha) as (ra & oa & rga & Ea & Hoa & Hloa & Hrga & Hla & Hhia & Hka).
exists ra, oa. destruct (Nat.eq_dec ra r) as [->|Hne].
+ exists x. rewrite Hrg in Hrga. injection Hrga as ->. split; [exact Ea|]. split; [exact Hoa|]. split; [exact Hloa|].
split; [rewrite ERG; exact R1|]. unfold x. cbn [rg_live rg_len rg_kind rg_rw].
split; [exact Hla|]. split; [exact Hhia|]. rewrite Hk in Hka |- *. apply in_app_iff. left. exact Hka.
+ exists rga. split; [exact Ea|]. split; [exact Hoa|]. split; [exact Hloa|].
split; [rewrite ERG, R2 by exact Hne; exact Hrga|]. split; [exact Hla|]. split; [exact Hhia | exact Hka].
- exists r, o, x. split; [reflexivity|]. split; [exact Ho|]. split; [exact Hlo|]. split; [rewrite ERG; exact R1|].
unfold x. cbn [rg_live rg_len rg_kind rg_rw]. split; [exact Hl|]. split; [nia|].
rewrite Hk. apply in_app_iff. right. left. reflexivity. }
split.
{ rewrite A3. destruct (st_areas s); reflexivity. }
split.
{ destruct (st_areas s ++ [SP r o]) as [|a0 l0] eqn:E.
- exfalso. destruct (st_areas s); discriminate.
- rewrite <- E, last_app_single. reflexivity. }
split.
{ intros k rgk Hk'. rewrite ERG in Hk'. destruct (Nat.eq_dec k r) as [->|Hne].
- rewrite R1 in Hk'. injection Hk' as <-. unfold x. cbn [rg_kind rg_live rg_len]. intros _. eapply A5; eauto.
- rewrite R2 in Hk' by exact Hne. eapply A5; eauto. }
split.
{ subst s1. rewrite (resv_total_upd s r x rg Hrg); [exact A6|].
unfold x. cbn [rg_kind rg_len]. rewrite Hk. split; reflexivity. }
split.
{ assert (EB : brk_regions s1 = brk_regions s).
{ subst s1. eapply brk_regions_upd; [exact Hrg | reflexivity]. }
rewrite EB. destruct (st_brk s) as [| |rb pb].
- exact A7.
- intros rr Hrr. destruct (A7 rr Hrr) as (Hbr & rgb & Hrgb & Hrest). split; [exact Hbr|]. exists rgb. split; [|exact Hrest].
rewrite ERG, R2; [exact Hrgb|]. intros ->.
destruct (brk_regions_In s r Hrr) as (rg2 & Hrg2 & Hk2). rewrite Hrg in Hrg2. injection Hrg2 as <-. rewrite Hk in Hk2. discriminate.
- destruct A7 as (Hbr & rgb & Hrgb & Hrest). split; [exact Hbr|]. exists rgb. split; [|exact Hrest].
rewrite ERG, R2; [exact Hrgb|]. intros ->.
destruct (brk_regions_In s r ltac:(rewrite Hbr; left; reflexivity)) as (rg2 & Hrg2 & Hk2).
rewrite Hrg in Hrg2. injection Hrg2 as <-. rewrite Hk in Hk2. discriminate. }
split.
{ intros Hc'. exists r, (o + 4096), x. split; [reflexivity|]. split; [rewrite ERG; exact R1|].
unfold x. cbn [rg_kind rg_live rg_len rg_rw]. split; [exact Hk|]. split; [exact Hl|].
split; [rewrite HP in Ho |- *; replace (o + 4096) with (o + 1 * 4096) by lia; rewrite Z_mod_plus_full; exact Ho|].
split; [lia|]. split; [nia|].
intros y Hy. apply in_app_iff in Hy as [Hy | [<- | []]]; [pose proof (Hrw y Hy); lia | lia]. }
{ intros k rgk Hk'. rewrite ERG in Hk'. destruct (Nat.eq_dec k r) as [->|Hne].
- rewrite R1 in Hk'. injection Hk' as <-. unfold x. cbn [rg_len]. eapply A9. exact Hrg.
- rewrite R2 in Hk' by exact Hne. eapply A9. exact Hk'. }
Qed.
Lemma Inv_open_brk_first X R U s :
Inv X R U s -> st_brk s = BrkNever -> st_avail_meta_area_count s = 0 -> st_avail_meta_count s = 0 ->
st_init_done s = true ->
let r := length (st_regions s) in
let s1 := set_brk (BrkCur r 2) (set_avail_meta_areas (SP r PGSZ) (set_avail_meta_area_count 1
(set_regions (st_regions s ++ [mkRegion RkBrk (2 * PGSZ) [] true]) s))) in
Inv X R U (open_st (SP r PGSZ) s1).
Proof.
intros HI Hb Hc0 Hm0 Hinit r s1.
pose proof (inv_areas HI) as (A1&A2&A3&A4&A5&A6&A7&A8&A9).
set (x := mkRegion RkBrk (2 * PGSZ) [] true) in *.
assert (ERG : forall k, region_of (open_st (SP r PGSZ) s1) k = region_of (set_regions (st_regions s ++ [x]) s) k) by reflexivity.
assert (R1 : region_of (set_regions (st_regions s ++ [x]) s) r = Some x) by (subst r; apply region_of_app_new).
pose proof (eq_refl : PGSZ = 4096) as HP.
rewrite Hb in A7.
assert (Hfresh : ~ In (SP r PGSZ) (st_areas s)).
{ intros Hin. destruct (A2 _ Hin) as (r2 & o2 & rg2 & E2 & _ & _ & Hrg2 & _). injection E2 as <- <-.
pose proof (region_of_lt _ _ _ Hrg2). lia. }
eapply Inv_nonmeta; try exact HI; try reflexivity.
- intros k rgk Hk' _. rewrite ERG. apply region_of_app. exact Hk'.
- apply ctx_ok_open; [| exact Hinit | change (st_avail_meta_area_count s1) with 1; lia].
pose proof (inv_ctx HI) as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12). unfold ctx_ok. subst s1. simp_st.
refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj _ _))))))))))); [lia|].
intros Hi. rewrite Hinit in Hi. discriminate.
- apply keys_ok_open; [| exact Hm0 | exact Hfresh].
pose proof (inv_keys HI) as K. unfold keys_ok, key_placed, handed in *. subst s1. simp_st. exact K.
- unfold areas_ok.
rewrite !st_areas_open, st_area_head_open, st_area_tail_open, st_brk_open, st_shift_open,
st_area_count_open, st_areas_ptr_open, brk_regions_open, resv_total_open.
change (st_areas s1) with (st_areas s). change (st_area_head s1) with (st_area_head s).
change (st_meta_alloc_shift s1) with (st_meta_alloc_shift s). change (st_brk s1) with (BrkCur r 2).
change (st_avail_meta_area_count s1) with 1.
split.
{ apply NoDup_app_single; [exact A1 | exact Hfresh]. }
split.
{ intros a Ha. apply in_app_iff in Ha as [Ha | [<- | []]].
- destruct (A2 a Ha) as (ra & oa & rga & Ea & Hoa & Hloa & Hrga & Hla & Hhia & Hka).
exists ra, oa, rga. split; [exact Ea|]. split; [exact Hoa|]. split; [exact Hloa|].
split; [rewrite ERG; apply region_of_app; exact Hrga|]. split; [exact Hla|]. split; [exact Hhia | exact Hka].
- exists r, PGSZ, x. split; [reflexivity|]. split; [rewrite HP; reflexivity|]. split; [lia|]. split; [rewrite ERG; exact R1|].
unfold x. cbn [rg_live rg_len rg_kind rg_rw]. split; [reflexivity|]. split; [lia | exact I]. }
split.
{ rewrite A3. destruct (st_areas s); reflexivity. }
split.
{ destruct (st_areas s ++ [SP r PGSZ]) as [|a0 l0] eqn:E.
- exfalso. destruct (st_areas s); discriminate.
- rewrite <- E, last_app_single. reflexivity. }
split.
{ intros k rgk Hk'. rewrite ERG in Hk'. unfold region_of in Hk'. cbn [st_regions set_regions] in Hk'.
rewrite nth_error_app in Hk'. destruct (Nat.ltb k (length (st_regions s))) eqn:El.
- eapply A5. exact Hk'.
- destruct (k - length (st_regions s))%nat as [|k']; cbn in Hk'; [|destruct k'; discriminate].
injection Hk' as <-. unfold x. cbn [rg_kind]. discriminate. }
split.
{ change (resv_total s1) with (resv_total (set_regions (st_regions s ++ [x]) s)).
rewrite resv_total_app. unfold x. cbn [rg_kind]. rewrite Z.add_0_r. exact A6. }
split.
{ change (brk_regions s1) with (brk_regions (set_regions (st_regions s ++ [x]) s)).
rewrite brk_regions_app, A7. unfold x. cbn [rg_kind app]. split; [reflexivity|].
exists x. split; [rewrite ERG; exact R1|]. unfold x. cbn [rg_live rg_len]. split; [reflexivity|]. split; [lia | lia]. }
split.
{ intros Hc'. lia. }
{ intros k rgk Hk'. rewrite ERG in Hk'. unfold region_of in Hk'. cbn [st_regions set_regions] in Hk'. rewrite nth_error_app in Hk'.
destruct (Nat.ltb k (length (st_regions s))); [eapply A9; exact Hk'|].
destruct (k - length (st_regions s))%nat as [|k']; cbn in Hk'; [injection Hk' as <-; cbn; lia | destruct k'; discriminate]. }
Qed.
Lemma Inv_open_brk_grow X R U s r p rg :
Inv X R U s -> st_brk s = BrkCur r p -> st_avail_meta_area_count s = 0 -> st_avail_meta_count s = 0 ->
st_init_done s = true -> region_of s r = Some rg ->
let x := mkRegion RkBrk (rg_len rg + PGSZ) [] true in
let s1 := set_brk (BrkCur r (p + 1)) (set_avail_meta_areas (SP r (PGSZ * p)) (set_avail_meta_area_count 1
(set_regions (lupd (st_regions s) r x) s))) in
Inv X R U (open_st (SP r (PGSZ * p)) s1).
Proof.
intros HI Hb Hc0 Hm0 Hinit Hrg x s1.
pose proof (inv_areas HI) as (A1&A2&A3&A4&A5&A6&A7&A8&A9).
rewrite Hb in A7. destruct A7 as (Hbr & rg0 & Hrg0 & Hl0 & Hlen0 & Hp2).
rewrite Hrg in Hrg0. injection Hrg0 as <-.
pose proof (region_of_lt _ _ _ Hrg) as Hrlt.
assert (ERG : forall k, region_of (open_st (SP r (PGSZ * p)) s1) k = region_of (set_regions (lupd (st_regions s) r x) s) k) by reflexivity.
assert (R1 : region_of (set_regions (lupd (st_regions s) r x) s) r = Some x).
{ rewrite region_of_upd, Nat.eqb_refl. replace (Nat.ltb r (length (st_regions s))) with true; [reflexivity|].
symmetry. apply Nat.ltb_lt. exact Hrlt. }
assert (R2 : forall k, k <> r -> region_of (set_regions (lupd (st_regions s) r x) s) k = region_of s k).
{ intros k Hk'. rewrite region_of_upd. replace (Nat.eqb k r) with false; [reflexivity|]. symmetry. apply Nat.eqb_neq. exact Hk'. }
pose proof (eq_refl : PGSZ = 4096) as HP.
assert (Hkind : rg_kind rg = RkBrk).
{ destruct (brk_regions_In s r ltac:(rewrite Hbr; left; reflexivity)) as (rg2 & Hrg2 & Hk2). rewrite Hrg in Hrg2. injection Hrg2 as <-. exact Hk2. }
assert (Hfresh : ~ In (SP r (PGSZ * p)) (st_areas s)).
{ intros Hin. destruct (A2 _ Hin) as (r2 & o2 & rg2 & E2 & _ & _ & Hrg2 & _ & Hhi2 & _).
pose proof (f_equal prid E2) as Er2. pose proof (f_equal poff E2) as Eo2. cbn [prid poff] in Er2, Eo2. subst r2 o2.
rewrite Hrg in Hrg2. injection Hrg2 as <-. rewrite Hlen0 in Hhi2. nia. }
eapply Inv_nonmeta; try exact HI; try reflexivity.
- intros k rgk Hk' Hkk. rewrite ERG. destruct (Nat.eq_dec k r) as [->|Hne].
+ rewrite Hrg in Hk'. injection Hk' as ->. rewrite Hkind in Hkk. discriminate.
+ rewrite R2 by exact Hne. exact Hk'.
- apply ctx_ok_open; [| exact Hinit | change (st_avail_meta_area_count s1) with 1; lia].
pose proof (inv_ctx HI) as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12). unfold ctx_ok. subst s1. simp_st.
refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj _ _))))))))))); [lia|].
intros Hi. rewrite Hinit in Hi. discriminate.
- apply keys_ok_open; [| exact Hm0 | exact Hfresh].
pose proof (inv_keys HI) as K. unfold keys_ok, key_placed, handed in *. subst s1. simp_st. exact K.
- unfold areas_ok.
rewrite !st_areas_open, st_area_head_open, st_area_tail_open, st_brk_open, st_shift_open,
st_area_count_open, st_areas_ptr_open, brk_regions_open, resv_total_open.
change (st_areas s1) with (st_areas s). change (st_area_head s1) with (st_area_head s).
change (st_meta_alloc_shift s1) with (st_meta_alloc_shift s). change (st_brk s1) with (BrkCur r (p + 1)).
change (st_avail_meta_area_count s1) with 1.
split.
{ apply NoDup_app_single; [exact A1 | exact Hfresh]. }
split.
{ intros a Ha. apply in_app_iff in Ha as [Ha | [<- | []]].
- destruct (A2 a Ha) as (ra & oa & rga & Ea & Hoa & Hloa & Hrga & Hla & Hhia & Hka).
exists ra, oa. destruct (Nat.eq_dec ra r) as [->|Hne].
+ exists x. rewrite Hrg in Hrga. injection Hrga as ->. split; [exact Ea|]. split; [exact Hoa|]. split; [exact Hloa|].
split; [rewrite ERG; exact R1|]. unfold x. cbn [rg_live rg_len rg_kind rg_rw].
split; [reflexivity|]. split; [lia | exact I].
+ exists rga. split; [exact Ea|]. split; [exact Hoa|]. split; [exact Hloa|].
split; [rewrite ERG, R2 by exact Hne; exact Hrga|]. split; [exact Hla|]. split; [exact Hhia | exact Hka].
- exists r, (PGSZ * p), x. split; [reflexivity|]. split; [rewrite HP, Z.mul_comm; apply Z_mod_mult|]. split; [nia|].
split; [rewrite ERG; exact R1|].
unfold x. cbn [rg_live rg_len rg_kind rg_rw]. split; [reflexivity|]. split; [lia | exact I]. }
split.
{ rewrite A3. destruct (st_areas s); reflexivity. }
split.
{ destruct (st_areas s ++ [SP r (PGSZ * p)]) as [|a0 l0] eqn:E.
- exfalso. destruct (st_areas s); discriminate.
- rewrite <- E, last_app_single. reflexivity. }
split.
{ intros k rgk Hk'. rewrite ERG in Hk'. destruct (Nat.eq_dec k r) as [->|Hne].
- rewrite R1 in Hk'. injection Hk' as <-. unfold x. cbn [rg_kind]. discriminate.
- rewrite R2 in Hk' by exact Hne. eapply A5. exact Hk'. }
split.
{ change (resv_total s1) with (resv_total (set_regions (lupd (st_regions s) r x) s)).
rewrite (resv_total_upd s r x rg Hrg); [exact A6|]. rewrite Hkind. unfold x. cbn [rg_kind]. discriminate. }
split.
{ change (brk_regions s1) with (brk_regions (set_regions (lupd (st_regions s) r x) s)).
rewrite (brk_regions_upd s r x rg Hrg) by (rewrite Hkind; reflexivity). split; [exact Hbr|].
exists x. split; [rewrite ERG; exact R1|]. unfold x. cbn [rg_live rg_len]. split; [reflexivity|]. split; [lia | lia]. }
split.
{ intros Hc'. lia. }
{ intros k rgk Hk'. rewrite ERG in Hk'. destruct (Nat.eq_dec k r) as [->|Hne].
- rewrite R1 in Hk'. injection Hk' as <-. unfold x. cbn [rg_len]. pose proof (A9 _ _ Hrg). lia.
- rewrite R2 in Hk' by exact Hne. eapply A9. exact Hk'. }
Qed.
Definition am_frame (s s' : astate) : Prop :=
st_active s' = st_active s /\ st_usage s' = st_usage s /\
(forall k rg, region_of s k = Some rg -> rg_kind rg = RkMap -> region_of s' k = Some rg) /\
(length (st_regions s) <= length (st_regions s'))%nat /\
st_mmap_counter s' = st_mmap_counter s.
Lemma am_frame_refl s : am_frame s s.
Proof. repeat split; auto. Qed.
Lemma am_frame_trans s1 s2 s3 : am_frame s1 s2 -> am_frame s2 s3 -> am_frame s1 s3.
Proof.
intros (A1&A2&A5&A6&A7) (B1&B2&B5&B6&B7). repeat split; try congruence.
- intros k rg Hk Hkd. apply B5; [apply A5; assumption | exact Hkd].
- lia.
Qed.
Lemma region_of_set_brk b s k : region_of (set_brk b s) k = region_of s k. Proof. reflexivity. Qed.
Lemma region_of_set_ama p s k : region_of (set_avail_meta_areas p s) k = region_of s k. Proof. reflexivity. Qed.
Lemma region_of_set_amac c s k : region_of (set_avail_meta_area_count c s) k = region_of s k. Proof. reflexivity. Qed.
Lemma open_area_resv_spec X R U s (Q : bool * astate -> Prop) :
Inv X R U s -> 0 < st_avail_meta_area_count s -> st_avail_meta_count s = 0 -> st_init_done s = true ->
(forall (ok : bool) s', Inv X R U s' -> am_frame s s' -> st_metas s' = st_metas s -> st_init_done s' = true ->
(ok = true -> 0 < st_avail_meta_count s') -> Q (ok, s')) ->
itok (open_area true s) Q.
Proof.
intros HI Hc Hm0 Hinit HQ.
pose proof (inv_areas HI) as (E1&E2&E3&E4&E5&E6&E7&E8&E9).
destruct (E8 Hc) as (r & o & rg & Ep & Hrg & Hk & Hl & Ho & Hlo & Hlen & Hrw).
pose proof (eq_refl : PGSZ = 4096) as HP.
unfold open_area. mbinds. apply itok_get. msimp. mbinds. apply itok_ask.
{ cbn. split; [exact Hc|]. split; [reflexivity|]. exists rg. rewrite Ep. cbn.
repeat (split; [assumption|]). split; [lia|]. intros Hin. pose proof (Hrw o Hin). lia. }
intros z _. msimp. destruct (z =? 0) eqn:Ez; cbn [negb].
- apply itok_ret. apply HQ; auto; [apply am_frame_refl | intros; discriminate].
- mbinds. unfold upd_region. apply itok_modify. msimp. mbinds. apply itok_modify. msimp. apply itok_ret.
rewrite Ep. cbn [prid poff]. unfold region_of in Hrg. rewrite !(nth_error_nth _ _ _ Hrg).
match goal with |- Q (true, ?st) =>
change st with (open_st (SP r o) (set_regions (lupd (st_regions s) r (mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [o]) (rg_live rg))) s)) end.
apply HQ.
+ apply Inv_open_resv; auto.
+ repeat split; try reflexivity; try tauto.
* intros k rgk Hk' Hkk. rewrite region_of_open, region_of_upd.
destruct (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool eqn:E; [|exact Hk'].
apply andb_prop in E as [E _]. apply Nat.eqb_eq in E. subst k. unfold region_of in Hk'. rewrite Hrg in Hk'. injection Hk' as ->.
rewrite Hk in Hkk. discriminate.
* rewrite st_regions_open. cbn. rewrite length_lupd. lia.
+ reflexivity.
+ exact Hinit.
+ intros _. cbn. reflexivity.
Qed.
Lemma resv_then_open_spec X R U s (Q : bool * astate -> Prop) :
Inv X R U s -> st_avail_meta_count s = 0 -> st_init_done s = true ->
(forall (ok : bool) s', Inv X R U s' -> am_frame s s' -> st_metas s' = st_metas s -> st_init_done s' = true ->
(ok = true -> 0 < st_avail_meta_count s') -> Q (ok, s')) ->
itok ((rs <- area_from_mmap ;; if rs then open_area true else ret false) s) Q.
Proof.
intros HI Hm0 Hinit HQ.
pose proof (inv_ctx HI) as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12).
unfold area_from_mmap. mbinds. apply itok_get. msimp.
destruct (st_avail_meta_area_count s =? 0) eqn:Ec.
- apply Z.eqb_eq in Ec. mbinds. apply itok_ask.
{ cbn. pose proof (inv_areas HI) as (_&_&_&_&_&A6&_). split; [reflexivity|]. split; [exact Ec|]. split; [exact C10 | exact A6]. }
intros z _. msimp. destruct (z =? 0) eqn:Ez; cbn [negb].
+ mbinds. apply itok_ret. msimp. apply itok_ret. apply HQ; auto; [apply am_frame_refl | intros; discriminate].
+ unfold new_region. mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp. mbinds. apply itok_ret. msimp.
mbinds. apply itok_modify. msimp. mbinds. apply itok_ret. msimp.
match goal with |- itok (open_area true ?st) _ => set (s2 := st) end.
assert (HI2 : Inv X R U s2) by exact (Inv_new_resv X R U s HI Ec Hinit).
assert (Fr2 : am_frame s s2).
{ subst s2. repeat split; try reflexivity; try tauto.
- intros k rg Hk _. cbn [set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas]. apply region_of_app. exact Hk.
- cbn. rewrite length_app. cbn. lia. }
assert (Hc2 : 0 < st_avail_meta_area_count s2).
{ subst s2. cbn -[Z.lt Z.sub Z.shiftl]. rewrite Z.shiftl_mul_pow2 by lia.
pose proof (Z.pow_pos_nonneg 2 (st_meta_alloc_shift s)). lia. }
eapply open_area_resv_spec; [exact HI2 | exact Hc2 | subst s2; exact Hm0 | subst s2; exact Hinit |].
intros ok s' HI' Fr' Em' Hi' Hok.
apply HQ; [exact HI' | eapply am_frame_trans; [exact Fr2 | exact Fr'] | rewrite Em'; subst s2; reflexivity | exact Hi' | exact Hok].
- apply Z.eqb_neq in Ec. mbinds. apply itok_ret. msimp.
eapply open_area_resv_spec; [exact HI | lia | exact Hm0 | exact Hinit | exact HQ].
Qed.
Lemma new_area_spec X R U s (Q : bool * astate -> Prop) :
Inv X R U s -> st_avail_meta_count s = 0 -> st_init_done s = true ->
(forall (ok : bool) s', Inv X R U s' -> am_frame s s' -> st_metas s' = st_metas s -> st_init_done s' = true ->
(ok = true -> 0 < st_avail_meta_count s') -> Q (ok, s')) ->
itok ((nu <- area_from_brk ;; rs <- area_from_mmap ;; if rs then open_area nu else ret false) s) Q.
Proof.
intros HI Hm0 Hinit HQ.
pose proof (inv_areas HI) as (A1&A2&A3&A4&A5&A6&A7&A8&A9).
pose proof (inv_ctx HI) as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12).
pose proof (eq_refl : PGSZ = 4096) as HP.
unfold area_from_brk. mbinds. apply itok_get. msimp.
destruct ((st_avail_meta_area_count s =? 0) && match st_brk s with BrkDead => false | _ => true end) eqn:Econd.
2:{
mbinds. apply itok_ret. msimp. eapply resv_then_open_spec; eauto. }
apply andb_prop in Econd as [Ec Eb]. apply Z.eqb_eq in Ec.
destruct (st_brk s) as [| |rb pb] eqn:Ebrk; [ | discriminate | ].
-
mbinds. apply itok_ask. { cbn. rewrite Ebrk. auto. }
intros z1 _. msimp. mbinds. apply itok_ask.
{ cbn. left. rewrite Ebrk. auto. }
intros z2 _. msimp. destruct (z2 =? 0) eqn:Ez2; cbn [negb].
+
mbinds. apply itok_modify. msimp. mbinds. apply itok_ret. msimp.
assert (HI1 : Inv X R U (set_brk BrkDead s)) by (apply Inv_brk_dead; [exact HI | rewrite Ebrk; discriminate | exact Hinit]).
eapply resv_then_open_spec; [exact HI1 | exact Hm0 | exact Hinit |].
intros ok s' HI' Fr' Em' Hi' Hok.
apply HQ; [exact HI' | | rewrite Em'; reflexivity | exact Hi' | exact Hok].
eapply am_frame_trans; [| exact Fr']. repeat split; try reflexivity; try tauto; try (intros k rg Hk _; exact Hk).
+
unfold new_region. mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp. mbinds. apply itok_ret. msimp.
mbinds. apply itok_modify. msimp. mbinds. apply itok_ask.
{ cbn. eexists (length (st_regions s)), _. split; [reflexivity|]. split; [rewrite length_app; cbn; lia|].
split; [apply region_of_app_new|]. cbn. split; [reflexivity|]. split; [reflexivity|].
apply Forall_forall. intros a Ha. destruct (A2 a Ha) as (r0 & o0 & rg0 & -> & _ & _ & Hrg0 & _). cbn.
pose proof (region_of_lt _ _ _ Hrg0). lia. }
intros z3 _. msimp. mbinds. apply itok_ret. msimp.
unfold area_from_mmap. mbinds. apply itok_get. msimp. cbn [Z.eqb st_avail_meta_area_count set_brk set_avail_meta_areas set_avail_meta_area_count set_regions].
mbinds. apply itok_ret. msimp.
unfold open_area. mbinds. apply itok_get. msimp. mbinds. apply itok_ret. msimp. cbn [negb].
mbinds. apply itok_ret. msimp. mbinds. apply itok_modify. msimp. apply itok_ret.
match goal with |- Q (true, ?st) =>
change st with (open_st (SP (length (st_regions s)) PGSZ)
(set_brk (BrkCur (length (st_regions s)) 2) (set_avail_meta_areas (SP (length (st_regions s)) PGSZ)
(set_avail_meta_area_count 1 (set_regions (st_regions s ++ [mkRegion RkBrk (2 * PGSZ) [] true]) s))))) end.
apply HQ.
* apply Inv_open_brk_first; auto.
* repeat split; try reflexivity; try tauto.
-- intros k rg Hk _. rewrite region_of_open, region_of_set_brk, region_of_set_ama, region_of_set_amac.
apply region_of_app. exact Hk.
-- rewrite st_regions_open. cbn. rewrite length_app. cbn. lia.
* reflexivity.
* exact Hinit.
* intros _. cbn. reflexivity.
-
destruct A7 as (Hbr & rg & Hrg & Hl & Hlen & Hp2).
mbinds. apply itok_ask.
{ cbn. right. split; [reflexivity|]. exists rb, pb, rg. rewrite Ebrk.
destruct (brk_regions_In s rb ltac:(rewrite Hbr; left; reflexivity)) as (rg2 & Hrg2 & Hk2).
rewrite Hrg in Hrg2. injection Hrg2 as <-. auto 6. }
intros z2 _. msimp. destruct (z2 =? 0) eqn:Ez2; cbn [negb].
+ mbinds. apply itok_modify. msimp. mbinds. apply itok_ret. msimp.
assert (HI1 : Inv X R U (set_brk BrkDead s)) by (apply Inv_brk_dead; [exact HI | rewrite Ebrk; discriminate | exact Hinit]).
eapply resv_then_open_spec; [exact HI1 | exact Hm0 | exact Hinit |].
intros ok s' HI' Fr' Em' Hi' Hok.
apply HQ; [exact HI' | | rewrite Em'; reflexivity | exact Hi' | exact Hok].
eapply am_frame_trans; [| exact Fr']. repeat split; try reflexivity; try tauto; try (intros k rg' Hk _; exact Hk).
+ unfold upd_region. mbinds. apply itok_modify. msimp. mbinds. apply itok_modify. msimp. mbinds. apply itok_ret. msimp.
unfold region_of in Hrg. rewrite !(nth_error_nth _ _ _ Hrg).
unfold area_from_mmap. mbinds. apply itok_get. msimp. cbn [Z.eqb st_avail_meta_area_count set_brk set_avail_meta_areas set_avail_meta_area_count set_regions].
mbinds. apply itok_ret. msimp.
unfold open_area. mbinds. apply itok_get. msimp. mbinds. apply itok_ret. msimp. cbn [negb].
mbinds. apply itok_ret. msimp. mbinds. apply itok_modify. msimp. apply itok_ret.
match goal with |- Q (true, ?st) =>
change st with (open_st (SP rb (PGSZ * pb))
(set_brk (BrkCur rb (pb + 1)) (set_avail_meta_areas (SP rb (PGSZ * pb))
(set_avail_meta_area_count 1 (set_regions (lupd (st_regions s) rb (mkRegion RkBrk (rg_len rg + PGSZ) [] true)) s))))) end.
apply HQ.
* apply (Inv_open_brk_grow X R U s rb pb rg); auto.
* repeat split; try reflexivity; try tauto.
-- intros k rgk Hk Hkk. rewrite region_of_open, region_of_set_brk, region_of_set_ama, region_of_set_amac.
rewrite region_of_upd. destruct (Nat.eqb k rb && Nat.ltb rb (length (st_regions s)))%bool eqn:E; [|exact Hk].
apply andb_prop in E as [E _]. apply Nat.eqb_eq in E. subst k.
exfalso. destruct (brk_regions_In s rb ltac:(rewrite Hbr; left; reflexivity)) as (rg2 & Hrg2 & Hk2).
rewrite Hk in Hrg2. injection Hrg2 as ->. rewrite Hk2 in Hkk. discriminate.
-- rewrite st_regions_open. cbn. rewrite length_lupd. lia.
* reflexivity.
* exact Hinit.
* intros _. cbn. reflexivity.
Qed.
Lemma alloc_meta_spec X R U s (Q : option sptr * astate -> Prop) :
Inv X R U s ->
(forall s', Inv X R U s' -> am_frame s s' ->
(forall g am, usedX X s' g am <-> usedX X s g am) -> ub_same s s' -> Q (None, s')) ->
(forall m s', Inv (m :: X) R U s' -> memb m X = false -> In m (keys s') ->
(MT s' m = Some MRaw \/ MT s' m = Some (MFree None None)) ->
am_frame s s' ->
(forall g am, usedX (m :: X) s' g am <-> usedX X s g am) -> ub_same s s' -> Q (Some m, s')) ->
itok (alloc_meta s) Q.
Proof.
intros HI HQn HQs.
unfold alloc_meta. mbinds. apply itok_modify. msimp.
set (s0 := set_init_done true s).
assert (HI0 : Inv X R U s0) by (apply Inv_set_init_done; exact HI).
assert (Fr0 : am_frame s s0) by (repeat split; try reflexivity; intros k rg Hk _; exact Hk).
assert (Hinit0 : st_init_done s0 = true) by reflexivity.
mbinds. eapply dequeue_head_free_spec; [exact HI0 | |].
-
intros Hfh Hnofree. msimp. mbinds. apply itok_get. msimp.
assert (TAKE : forall s1, Inv X R U s1 -> am_frame s s1 -> st_metas s1 = st_metas s -> 0 < st_avail_meta_count s1 ->
itok ((s2 <- get ;;
put (set_avail_meta (padd (st_avail_meta s2) META_SIZE) (set_avail_meta_count (st_avail_meta_count s2 - 1) s2)) ;;
setslot (st_avail_meta s2) MRaw ;; ret (Some (st_avail_meta s2))) s1) Q).
{ intros s1 HI1 Fr1 Em1 Hc1.
mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp. mbinds. apply itok_setslot'. msimp. apply itok_ret.
destruct (take_slot_Inv X R U s1 HI1 Hc1) as (Hfresh & NX & HI2 & EU2).
apply HQs.
+ exact HI2.
+ exact NX.
+ rewrite keys_upd_notIn by exact Hfresh. apply in_app_iff. right. left. reflexivity.
+ left. apply MT_upd_same.
+ eapply am_frame_trans; [exact Fr1|]. repeat split; try reflexivity. intros k rg Hk _. exact Hk.
+ intros g am. rewrite EU2. unfold usedX, MTX, MT. rewrite Em1. reflexivity.
+ eapply ub_same_trans; [| apply ub_same_upd_notIn; [exact Hfresh | reflexivity]]. apply ub_same_metas. exact Em1. }
destruct (0 <? st_avail_meta_count s0) eqn:Ec.
+ apply Z.ltb_lt in Ec. mbinds. apply itok_ret. msimp. cbn [negb].
apply TAKE; [exact HI0 | exact Fr0 | reflexivity | exact Ec].
+ apply Z.ltb_ge in Ec. pose proof (inv_keys HI0) as (_ & _ & _ & _ & Krange).
assert (Hm0 : st_avail_meta_count s0 = 0) by lia.
apply itok_bind.
eapply new_area_spec; [exact HI0 | exact Hm0 | exact Hinit0 |].
intros ok s1 HI1 Fr1 Em1 Hi1 Hok. msimp. destruct ok; cbn [negb].
* apply TAKE; [exact HI1 | eapply am_frame_trans; [exact Fr0 | exact Fr1] | rewrite Em1; reflexivity | apply Hok; reflexivity].
* apply itok_ret. apply HQn; [exact HI1 | eapply am_frame_trans; [exact Fr0 | exact Fr1] | |].
-- intros g am. unfold usedX, MTX, MT. rewrite Em1. reflexivity.
-- apply ub_same_metas. rewrite Em1. reflexivity.
-
intros m s' HI' NX Mm Sb Ea EU UB. msimp. apply itok_ret. apply HQs.
+ exact HI'.
+ exact NX.
+ eapply MT_Some_In_keys. exact Mm.
+ right. exact Mm.
+ eapply am_frame_trans; [exact Fr0|].
destruct Sb as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11&E12&E13&E14&E15&E16&E17).
repeat split; try assumption.
* intros k rg Hk _. unfold region_of in *. rewrite E15. exact Hk.
* rewrite E15. lia.
+ intros g am. rewrite EU. reflexivity.
+ eapply ub_same_trans; [apply ub_same_metas; reflexivity | exact UB].
Qed.

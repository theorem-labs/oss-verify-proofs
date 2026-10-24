(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO0u YO15
YO10 YO11 YO12 YO0z YO14 YO0q YO0v YO0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN25 YN26 YN28 YN2q YN2t YN2r.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section m.
Variables (X : list sptr) (U : Z -> Z) (A : astate) (g : sptr) (i : Z) (am : ameta) (f : nat).
Hypothesis HI : Inv X (Some (g, i)) U A.
Hypothesis Hu : usedX X A g am.
Hypothesis HU : forall c, 0 <= U c.
Hypothesis HC1 : nt_C1 A g i am = true.
Hypothesis Hf : (fneed (am_sc am) <= S f)%nat.
Definition U1 : Z -> Z := fun c => U c + contrib X A c g.
Definition fromA (Y : list sptr) (s : astate) : Prop :=
forall q a, usedX Y s q a -> exists a0, usedX X A q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0.
Lemma Mg : MT A g = Some (MUsed am). Proof. exact (proj1 (usedX_MT _ _ _ _ Hu)). Qed.
Lemma NXg : memb g X = false. Proof. exact (proj2 (usedX_MT _ _ _ _ Hu)). Qed.
Lemma C1_facts : nt_mask am + bit i = ones (am_last am) /\ okay_to_free A g am = true /\
(am_sc am = 63 \/ 0 <= am_sc am < 48) /\ (forall j, ss_fr (nth_slot am j) = None).
Proof.
pose proof HC1 as H. unfold nt_C1 in H. apply andb_prop in H as [Hmask Hok]. apply Z.eqb_eq in Hmask.
pose proof (inv_groups HI g am Hu) as (_ & _ & _ & Gcl & _).
split; [exact Hmask|]. split; [exact Hok|]. split; [destruct Gcl as [(C & _) | (C & _)]; [left | right]; exact C|].
apply (frameless_of_mask X U A g i am HI Hu). unfold nt_mask in Hmask. exact Hmask.
Qed.
Definition P1 (s1 : astate) : Prop :=
Inv (g :: X) None U1 s1 /\ MT s1 g = Some (MUsed (am_set_links None None am)) /\
st_usage s1 = st_usage A /\ st_regions s1 = st_regions A /\ corr X A s1 /\ fromA (g :: X) s1 /\
(forall q, (forall a, usedX X A q a -> am_sc a <> am_sc am) -> q <> g -> MT s1 q = MT A q) /\ ub_same A s1.
Lemma step1 : itok (nt_deq g am A) (fun r => P1 (snd r)).
Proof.
pose proof C1_facts as (Hmask & Hok & Hscr & Hnofr). pose proof Mg as Mg. pose proof NXg as NXg.
set (sc := am_sc am) in *. unfold nt_deq. fold sc.
destruct (am_next am) as [nx|] eqn:Enx.
- assert (Hsc : 0 <= sc < 48).
{ destruct Hscr as [H63|H]; [|exact H]. exfalso. destruct (inv_rings HI) as (_ & _ & D). destruct (D g am Hu H63) as [_ E]. rewrite Enx in E. discriminate. }
mbinds. apply itok_massert; [apply Z.ltb_lt; lia|]. msimp. mbinds. apply itok_get_head. msimp.
change (nth (Z.to_nat sc) (st_active A) None) with (active_hd A sc).
mbinds. eapply (dequeue_exempt_spec X (Some (g, i)) U A sc g am); [exact HI | exact Hsc | exact Hu | reflexivity | rewrite Enx; intros E; discriminate | exact Hnofr | intros p j E; injection E; auto |].
intros s1 HI1 Sb1 Mg1 EH1 Mo1 Bwd1 Hk1 Hnew1 UB1. msimp. mbinds. apply itok_get_head. msimp.
change (nth (Z.to_nat sc) (st_active s1) None) with (active_hd s1 sc).
pose proof Sb1 as (_&_&_&_&_&_&_&_&_&Eus1&_&_&_&_&Erg1&_&EK1).
assert (C1 : fromA (g :: X) s1).
{ intros q a Hq. destruct (Bwd1 q a Hq) as (_ & a0 & H0 & E). pose proof (strip_fields _ _ E) as (Em&_&_&_&_&Eml&_).
exists a0. auto. }
assert (Cr1 : corr X A s1).
{ intros q a Hq. destruct (sptr_eq_dec q g) as [->|Hne].
- pose proof (usedX_MT _ _ _ _ Hq) as [M _]. rewrite Mg1 in M. injection M as <-. exists am.
split; [exact Hu|]. destruct am; split; reflexivity.
- apply C1. apply usedX_cons; assumption. }
assert (POST1 : forall s1', Inv (g :: X) None U1 s1' ->
(exists h x, s1' = upd_meta h x s1 /\ h <> g /\
(exists ah ah', x = MUsed ah' /\ usedX (g :: X) s1 h ah /\ am_sc ah = sc /\ am_mem ah' = am_mem ah /\ am_maplen ah' = am_maplen ah /\
blocks_of h ah' = blocks_of h ah)) \/ s1' = s1 ->
P1 s1').
{ intros s1' HI1' Hcase. unfold P1. fold sc. destruct Hcase as [(h & x & -> & Hhg & ah & ah' & -> & Uh & Sh & Emh & Emlh & Ebl) | ->].
- split; [exact HI1'|]. split; [rewrite MT_upd_other by (intros E; exact (Hhg (eq_sym E))); exact Mg1|].
split; [exact Eus1|]. split; [exact Erg1|].
assert (C2 : fromA (g :: X) (upd_meta h (MUsed ah') s1)).
{ intros q a Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
- injection E as <-. destruct (C1 h ah Uh) as (a0 & H0 & E0 & F0). exists a0. split; [exact H0|]. split; congruence.
- apply C1. exact Hq. }
split.
{ intros q a Hq. destruct (sptr_eq_dec q g) as [->|Hne].
- pose proof (usedX_MT _ _ _ _ Hq) as [M _]. rewrite MT_upd_other in M by (intros E; exact (Hhg (eq_sym E))).
rewrite Mg1 in M. injection M as <-. exists am. split; [exact Hu|]. destruct am; split; reflexivity.
- apply C2. apply usedX_cons; assumption. }
split; [exact C2|]. split.
{ intros q Hq Hqg. destruct (sptr_eq_dec q h) as [->|Hqh].
+ exfalso. destruct (Bwd1 h ah Uh) as (_ & a0 & H0 & E0). pose proof (strip_fields _ _ E0) as (_&_&_&_&Es&_).
apply (Hq a0 H0). congruence.
+ rewrite MT_upd_other by exact Hqh. apply Mo1; assumption. }
eapply ub_same_trans; [exact UB1|]. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ Uh))|].
rewrite (proj1 (usedX_MT _ _ _ _ Uh)). cbn. exact Ebl.
- split; [exact HI1'|]. split; [exact Mg1|]. split; [exact Eus1|]. split; [exact Erg1|]. split; [exact Cr1|]. split; [exact C1|]. split; [exact Mo1 | exact UB1]. }
destruct (osptr_eqb (active_hd A sc) (Some g)) eqn:Ehd.
+ apply osptr_eqb_eq in Ehd. destruct (Hnew1 Ehd) as [Hnone | (h & ah & Hh & Hhg & Uh & Sh & Avh)].
* rewrite Hnone. apply itok_ret. cbn [snd]. apply (POST1 s1 HI1). right. reflexivity.
* rewrite Hh. mbinds. eapply activate_group_spec; [exact HI1 | exact Hsc | exact Uh | exact Sh | exact Hh | exact Avh |].
intros mk s2 HI2 Es2. msimp. apply itok_ret. cbn [snd]. apply (POST1 s2 HI2). left.
eexists h, _. split; [exact Es2|]. split; [exact Hhg|]. eexists ah, _. split; [reflexivity|]. split; [exact Uh|]. split; [exact Sh|].
split; [destruct ah; reflexivity|]. split; [destruct ah; reflexivity|]. apply blocks_of_ext; destruct ah; reflexivity.
+ apply itok_ret. cbn [snd]. apply (POST1 s1 HI1). right. reflexivity.
- apply itok_ret. cbn [snd].
assert (Hp : am_prev am = None).
{ destruct Hscr as [H63|Hsc]; [destruct (inv_rings HI) as (_ & _ & D); exact (proj1 (D g am Hu H63))|].
eapply unlinked_of_next_None; eauto. }
unfold P1. split; [apply (Inv_exempt X (Some (g, i)) U A g am HI Hu Hnofr Hp Enx); intros p j E; injection E; auto|].
split; [rewrite Mg; destruct am; cbn in Hp, Enx |- *; subst; reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [apply corr_refl|]. split.
+ intros q a Hq. apply usedX_cons_inv in Hq as [_ Hq]. exists a. auto.
+ split; [intros; reflexivity | apply ub_same_refl].
Qed.
Definition P2 (s1 s2 : astate) : Prop :=
Inv (g :: X) None U s2 /\ st_metas s2 = st_metas s1 /\ st_regions s2 = st_regions A /\ st_active s2 = st_active s1 /\
fromA (g :: X) s2 /\ (forall Y q a, usedX Y s2 q a <-> usedX Y s1 q a).
Lemma usage_ge : 0 <= am_sc am < 48 -> am_last am + 1 <= usage_of A (am_sc am).
Proof.
intros Hsc. pose proof (MT_Some_In_keys _ _ _ Mg) as Kg.
rewrite (inv_usage HI (am_sc am) ltac:(lia)). pose proof (class_sum_ge_contrib X _ U A (am_sc am) g HI Kg) as Hge.
rewrite (contrib_used X A (am_sc am) g am Hu) in Hge. rewrite Z.eqb_refl in Hge. pose proof (HU (am_sc am)). lia.
Qed.
Lemma step2 s1 : P1 s1 ->
itok ((if am_sc am <? 48 then set_usage_of (am_sc am) (usage_of A (am_sc am) - (am_last am + 1)) else ret tt) s1) (fun r => P2 s1 (snd r)).
Proof.
intros (HI1 & Mg1 & Eus1 & Erg1 & Cr1 & C1 & Mo1 & UBs1). set (sc := am_sc am) in *.
assert (HU1 : forall c, 0 <= c < 48 -> U1 c = U c + (if sc =? c then am_last am + 1 else 0)).
{ intros c Hc. unfold U1. rewrite (contrib_used X A c g am Hu). reflexivity. }
assert (K : forall s2, Inv (g :: X) None U s2 -> st_metas s2 = st_metas s1 -> st_regions s2 = st_regions A -> st_active s2 = st_active s1 -> P2 s1 s2).
{ intros s2 HI2 Em2 Erg2 Ea2.
assert (MT2 : forall q, MT s2 q = MT s1 q) by (intros; unfold MT; rewrite Em2; reflexivity).
assert (EU2 : forall Y q a, usedX Y s2 q a <-> usedX Y s1 q a) by (intros; unfold usedX, MTX; rewrite MT2; tauto).
split; [exact HI2|]. split; [exact Em2|]. split; [exact Erg2|]. split; [exact Ea2|]. split; [| exact EU2].
intros q a Hq. apply EU2 in Hq. apply C1. exact Hq. }
destruct (sc <? 48) eqn:E48.
- apply Z.ltb_lt in E48. pose proof C1_facts as (_ & _ & Hscr & _). fold sc in Hscr. assert (Hsc : 0 <= sc < 48) by (destruct Hscr; lia).
apply itok_set_usage_of. pose proof (usage_ge Hsc) as Hv. fold sc in Hv.
pose proof (Inv_set_usage (g :: X) None U1 s1 sc (usage_of A sc - (am_last am + 1)) HI1 ltac:(lia) ltac:(lia)) as HI2.
apply K; [| reflexivity | exact Erg1 | reflexivity].
eapply Inv_U_ext; [|exact HI2]. intros c Hc. unfold Uadd. rewrite (HU1 c Hc).
replace (usage_of s1 sc) with (usage_of A sc) by (unfold usage_of; rewrite Eus1; reflexivity).
destruct (c =? sc) eqn:E1; destruct (sc =? c) eqn:E2; try lia;
try (apply Z.eqb_eq in E1; apply Z.eqb_neq in E2; lia); try (apply Z.eqb_neq in E1; apply Z.eqb_eq in E2; lia).
- apply Z.ltb_ge in E48. apply itok_ret. apply K; [| reflexivity | exact Erg1 | reflexivity].
eapply Inv_U_ext; [|exact HI1]. intros c Hc. rewrite (HU1 c Hc).
destruct (sc =? c) eqn:E2; [apply Z.eqb_eq in E2; lia | lia].
Qed.
Definition P4 (s4 : astate) (mi : option (nat * Z)) : Prop :=
Inv (g :: X) None U s4 /\ ub_same A s4 /\ fromA (g :: X) s4 /\ st_regions s4 = st_regions A /\
match mi with
| None => True
| Some (k, len) => exists rg, region_of s4 k = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
rg_len rg = page_round len /\ 0 <= len /\ (forall q a, usedX (g :: X) s4 q a -> 0 < am_maplen a -> prid (am_mem a) <> k)
end.
Lemma step3m s1 s2 : P1 s1 -> P2 s1 s2 -> 0 < am_maplen am ->
itok ((step_seq ;; record_seq (am_sc am) ;; ret (Some (prid (am_mem am), am_maplen am * 4096))) s2) (fun r => P4 (snd r) (fst r) /\ st_metas (snd r) = st_metas s2).
Proof.
intros (HI1 & Mg1 & Eus1 & Erg1 & Cr1 & C1 & Mo1 & UBs1) (HI2 & Em2 & Erg2 & Ea2 & C2 & EU2) Hml.
pose proof (inv_groups HI g am Hu) as (_ & _ & _ & _ & Gmp & _).
mbinds. eapply step_seq_spec; [exact HI2|]. intros s3 HI3 (Em3 & _ & Er3 & _). msimp.
mbinds. eapply record_seq_spec; [exact HI3|]. intros s4 HI4 (Em4 & _ & Er4 & _). msimp.
apply itok_ret. cbn [fst snd].
assert (EU4 : forall q a, usedX (g :: X) s4 q a <-> usedX (g :: X) s2 q a) by (intros; unfold usedX, MTX, MT; rewrite Em4, Em3; tauto).
split; [| rewrite Em4, Em3; reflexivity].
split; [exact HI4|]. split.
{ eapply ub_same_trans; [exact UBs1|]. apply ub_same_metas. rewrite Em4, Em3, Em2. reflexivity. }
split; [intros q a Hq; apply C2; apply EU4; exact Hq|].
split; [rewrite Er4, Er3; exact Erg2|].
destruct (Gmp Hml) as (r & rg & Emem & Hr & Hk & Hl & Hlen & _). exists rg. rewrite Emem. cbn [prid].
split; [unfold region_of in *; rewrite Er4, Er3, Erg2; exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split.
{ rewrite Hlen. unfold PGSZ. rewrite page_round_fixed; [reflexivity|]. unfold PGSZ. apply Z_mod_mult. }
split; [lia|].
intros q a Hq Hqm. apply EU4 in Hq. pose proof (usedX_cons_inv _ _ _ _ _ Hq) as [Hqg _].
destruct (C2 q a Hq) as (a0 & H0 & E0 & F0). rewrite E0. rewrite F0 in Hqm. intros Ep. apply Hqg.
eapply (inv_maps HI q a0 g am H0 Hu Hqm Hml). rewrite Emem. cbn. exact Ep.
Qed.
Lemma inv_seq s1 s2 : P1 s1 -> P2 s1 s2 -> Inv (g :: X) None U (A_seq s2) /\ ctx_frame s2 (A_seq s2).
Proof.
intros _ (HI2 & _). pose proof (step_seq_spec (g :: X) None U s2 (fun r => Inv (g :: X) None U (snd r) /\ ctx_frame s2 (snd r)) HI2 ltac:(intros s' H1 H2; split; assumption)) as K.
rewrite step_seq_eval in K. exact K.
Qed.
Lemma P4_mapped s1 s2 : P1 s1 -> P2 s1 s2 -> 0 < am_maplen am ->
P4 (A_rec (am_sc am) (A_seq s2)) (Some (prid (am_mem am), am_maplen am * 4096)) /\ st_metas (A_rec (am_sc am) (A_seq s2)) = st_metas s2.
Proof.
intros H1 H2 Hml. pose proof (step3m s1 s2 H1 H2 Hml) as K.
erewrite (bind_eval _ _ s2) in K by apply step_seq_eval. erewrite (bind_eval _ _ _) in K by apply record_seq_eval.
cbn [itok ret fst snd] in K. exact K.
Qed.
Definition am_forget (am' : ameta) (i' : Z) : ameta := upd_slot am' i' (mkSlot (ss_hdr (nth_slot am' i')) None).
Lemma step3n s1 s2 : P1 s1 -> P2 s1 s2 -> am_maplen am = 0 ->
exists g' am' i' fr',
am_sc am <> 63 /\ 0 <= am_sc am < 48 /\ usedX X A g' am' /\ usedX (g :: X) s2 g' am' /\ 0 <= i' <= am_last am' /\
ss_fr (nth_slot am' i') = Some fr' /\ fr_kind fr' = FGroup /\ fr_off fr' = 0 /\ am_mem am = frame_ptr am' i' fr' /\
0 <= am_sc am' < 48 /\ g' <> g /\ MT s2 g' = MT A g' /\
find_frame_in (st_metas s2) (am_mem am) = Some (g', i') /\
(forall c ac, usedX (g :: X) s2 c ac -> am_maplen ac = 0 -> am_mem ac <> slot_start am' i') /\
let s3 := upd_meta g' (MUsed (am_forget am' i')) s2 in
Inv (g :: X) (Some (g', i')) U s3 /\ usedX (g :: X) s3 g' (am_forget am' i') /\
((am_prev (am_forget am' i'), am_next (am_forget am' i')) <> (None, None) -> active_hd s3 (am_sc (am_forget am' i')) <> Some g' -> am_freed (am_forget am' i') <> 0) /\
(fneed (am_sc (am_forget am' i')) <= f)%nat /\
(forall mi s4, nf_post (g :: X) U s3 (mi, s4) -> nt_keep s3 s4 -> P4 s4 mi).
Proof.
intros (HI1 & Mg1 & Eus1 & Erg1 & Cr1 & C1 & Mo1 & UBs1) (HI2 & Em2 & Erg2 & Ea2 & C2 & EU2) Hml.
pose proof C1_facts as (Hmask & Hok & Hscr & Hnofr). set (sc := am_sc am) in *.
pose proof (inv_groups HI g am Hu) as (_ & _ & _ & _ & _ & Gns).
destruct (Gns Hml) as (N63 & g' & am' & i' & fr' & U' & Hi' & F' & K' & Emem & Hsc' & N63' & Fit).
assert (Hsc : 0 <= sc < 48) by (destruct Hscr as [H|H]; [exfalso; exact (N63 H) | exact H]).
pose proof (inv_groups HI g' am' U') as G'. pose proof G' as (_ & _ & Gsl' & Gcl' & _).
pose proof (Gsl' i' Hi') as (_ & _ & S3'). rewrite F' in S3'. destruct S3' as (Hal' & _ & (_ & _ & _ & _ & FG') & _).
destruct (FG' K') as [Hoff' _].
assert (Hsc'48 : 0 <= am_sc am' < 48) by (destruct Gcl' as [(C & _) | (C & _)]; [exfalso; exact (N63' C) | exact C]).
assert (Hg'g : g' <> g) by (intros ->; pose proof (usedX_fun _ _ _ _ _ U' Hu) as E; rewrite E in Hsc'; lia).
pose proof (usedX_MT _ _ _ _ U') as [Mg' NXg'].
assert (MT2 : forall q, MT s2 q = MT s1 q) by (intros; unfold MT; rewrite Em2; reflexivity).
assert (E2g' : MT s2 g' = MT A g').
{ rewrite MT2. apply (Mo1 g'); [| exact Hg'g]. intros a Ha. pose proof (usedX_fun _ _ _ _ _ Ha U') as ->. lia. }
assert (U'2 : usedX (g :: X) s2 g' am').
{ apply usedX_intro.
- rewrite memb_cons, NXg'. replace (sptr_eqb g' g) with false by (symmetry; apply sptr_eqb_neq; exact Hg'g). reflexivity.
- rewrite E2g'. exact Mg'. }
assert (Eptr : am_mem am = frame_ptr am' i' fr').
{ unfold frame_ptr. rewrite Hoff', Z.mul_0_r, padd_0. exact Emem. }
assert (NOSL : forall c ac, usedX (g :: X) s2 c ac -> am_maplen ac = 0 -> am_mem ac <> slot_start am' i').
{ intros c ac Hc Hmlc Emc. pose proof (usedX_cons_inv _ _ _ _ _ Hc) as [Hcg _].
destruct (C2 c ac Hc) as (ac0 & H0 & E0 & _).
eapply (same_mem_contra X _ U A c ac0 g am HI H0 Hu Hcg). rewrite <- E0, Emc. symmetry. exact Emem. }
exists g', am', i', fr'.
split; [exact N63|]. split; [exact Hsc|]. split; [exact U'|]. split; [exact U'2|]. split; [exact Hi'|]. split; [exact F'|]. split; [exact K'|].
split; [exact Hoff'|]. split; [exact Eptr|]. split; [exact Hsc'48|]. split; [exact Hg'g|]. split; [exact E2g'|].
split; [rewrite Eptr; exact (find_frame_in_spec (g :: X) None U s2 HI2 g' am' i' fr' U'2 Hi' F')|].
split; [exact NOSL|].
pose proof (forget_frame_spec (g :: X) U s2 g' i' am' fr' (fun r => snd r = upd_meta g' (MUsed (am_forget am' i')) s2 /\ Inv (g :: X) (Some (g', i')) U (snd r))
HI2 U'2 Hi' F' NOSL ltac:(intros s' Es' HI'; split; [exact Es' | exact HI'])) as FF.
unfold forget_frame in FF. erewrite (bind_eval (getm g') _ s2) in FF by (apply getm_eval; exact (proj1 (usedX_MT _ _ _ _ U'2))).
rewrite (setm_eval s2 g') in FF. cbn [itok snd] in FF. destruct FF as [_ HI3]. fold (am_forget am' i') in HI3.
cbn zeta.
assert (U'3 : usedX (g :: X) (upd_meta g' (MUsed (am_forget am' i')) s2) g' (am_forget am' i')).
{ apply usedX_upd. left. split; [reflexivity|]. split; [|reflexivity].
rewrite memb_cons, NXg'. replace (sptr_eqb g' g) with false by (symmetry; apply sptr_eqb_neq; exact Hg'g). reflexivity. }
pose proof (upd_slot_fields am' i' (mkSlot (ss_hdr (nth_slot am' i')) None)) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold (am_forget am' i') in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
split; [exact HI3|]. split; [exact U'3|]. split.
{ intros Hl Hnh. replace (am_freed (am_forget am' i')) with (am_freed am') by (unfold am_forget; destruct am'; reflexivity).
replace (am_prev (am_forget am' i'), am_next (am_forget am' i')) with (am_prev am', am_next am') in Hl by (unfold am_forget; destruct am'; reflexivity).
rewrite Fsc in Hnh. rewrite active_hd_upd_meta in Hnh.
apply (proj2 (proj2 (ring_facts _ _ _ _ _ _ HI2 U'2 ltac:(lia) ltac:(lia)))); [exact Hl | exact Hnh | intros; discriminate]. }
split.
{ rewrite Fsc. unfold fneed in Hf |- *. fold sc in Hf.
replace (sc <? 48) with true in Hf by (symmetry; apply Z.ltb_lt; lia).
replace (am_sc am' <? 48) with true by (symmetry; apply Z.ltb_lt; lia). lia. }
intros mi s4 (HI4 & Cr4 & UB34 & Hmi) (Erg4 & _). cbn [fst snd] in *. unfold P4.
assert (C4 : fromA (g :: X) s4).
{ intros q a Hq. destruct (Cr4 q a Hq) as (a3 & H3 & E3 & F3).
apply usedX_upd in H3. destruct H3 as [(-> & _ & E) | (Hne & H2')].
- injection E as <-. destruct (C2 g' am' U'2) as (a0 & H0 & E0 & F0). exists a0. split; [exact H0|]. split; congruence.
- destruct (C2 q a3 H2') as (a0 & H0 & E0 & F0). exists a0. split; [exact H0|]. split; congruence. }
split; [exact HI4|]. split.
{ eapply ub_same_trans; [exact UBs1|]. eapply ub_same_trans; [apply ub_same_metas; exact Em2|]. eapply ub_same_trans; [|exact UB34].
apply ub_same_upd_In; [eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ U'2))|].
rewrite (proj1 (usedX_MT _ _ _ _ U'2)). cbn. pose proof (inv_groups HI2 g' am' U'2) as ((_ & _ & Glen' & _) & _).
apply blocks_of_upd_slot_same; [exact Hi' | exact Glen' |]. unfold slotst_block, slot_block. cbn. rewrite F', K'. reflexivity. }
split; [exact C4|]. split.
{ rewrite Erg4. exact Erg2. }
exact Hmi.
Qed.
Definition P5 (s4 : astate) (mi : option (nat * Z)) (s5 : astate) : Prop :=
nf_post X U A (mi, s5) /\ same_but_metas_heads s4 s5 /\ st_active s5 = st_active s4 /\
(forall q a, usedX X s5 q a <-> usedX (g :: X) s4 q a).
Lemma step4 s4 mi : P4 s4 mi -> itok (free_meta g s4) (fun r => P5 s4 mi (snd r)).
Proof.
intros (HI4 & UB4 & C4 & Erg4 & Hmi). pose proof NXg as NXg.
eapply free_meta_spec; [exact HI4 | left; reflexivity |]. intros s5 HI5 Sb5 Ea5 EU5 UB5.
rewrite (remove_head_notin g X NXg) in HI5, EU5.
unfold P5, nf_post. cbn [fst snd]. split; [| split; [exact Sb5 | split; [exact Ea5 | exact EU5]]].
split; [exact HI5|]. split.
{ intros q a Hq. apply EU5 in Hq. apply C4. exact Hq. }
split; [eapply ub_same_trans; [exact UB4 | exact UB5]|].
destruct mi as [[k len]|]; [|exact I].
destruct Hmi as (rg & Hr & Hk & Hl & Hlen & Hlen0 & Hno). exists rg.
pose proof Sb5 as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&Erg5&_).
split; [unfold region_of in *; rewrite Erg5; exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [exact Hlen|]. split; [exact Hlen0|].
intros q a Hq. apply EU5 in Hq. exact (Hno q a Hq).
Qed.
End m.
Lemma bounded_upd_meta q x s : bounded (upd_meta q x s) <-> bounded s.
Proof. unfold bounded, usage_of. cbn. tauto. Qed.
Lemma bounded_set_active l s : bounded (set_active l s) <-> bounded s.
Proof. unfold bounded, usage_of. cbn. tauto. Qed.
Lemma bounded_seq s : bounded (A_seq s) <-> bounded s.
Proof. unfold bounded, usage_of, A_seq. destruct (st_seq s =? 255); cbn; tauto. Qed.
Lemma bounded_rec sc s : bounded (A_rec sc s) <-> bounded s.
Proof. unfold bounded, usage_of, A_rec. destruct (bounce_idx sc); cbn; tauto. Qed.
Lemma bounded_set_free_meta_head v s : bounded (set_free_meta_head v s) <-> bounded s.
Proof. unfold bounded, usage_of. cbn. tauto. Qed.
Lemma bounded_usg A0 sc am1 s :
bounded s -> (sc < 48 -> 0 <= usage_of A0 sc - (am_last am1 + 1) <= usage_of s sc) -> bounded (A_usg A0 sc am1 s).
Proof.
intros (B1 & B2 & B3) Hv. unfold A_usg. destruct (sc <? 48) eqn:E; [apply Z.ltb_lt in E | exact (conj B1 (conj B2 B3))].
specialize (Hv E). split; [| cbn; exact (conj B2 B3)].
intros c. unfold usage_of in *. cbn [st_usage set_usage]. unfold znth, zset in *. rewrite nth_zupd.
destruct (Nat.eqb (Z.to_nat c) (Z.to_nat sc) && Nat.ltb (Z.to_nat sc) (length (st_usage s)))%bool; [| apply B1].
pose proof (B1 sc). lia.
Qed.
Lemma chain_last lk prev l first d :
chain lk prev l first -> l <> [] -> exists pp, lk (last l d) = Some (Some pp, Some first).
Proof.
revert prev d. induction l as [|x rest IH]; intros prev d Hc Hne; [exfalso; exact (Hne eq_refl)|].
cbn [chain] in Hc. destruct Hc as [Hx Hr]. destruct rest as [|y rest'].
- cbn. exists prev. exact Hx.
- rewrite last_cons. apply (IH x x Hr). discriminate.
Qed.
Lemma ring_head_prev lk h ms :
ring_ok lk (Some h) ms ->
exists rest hp, ms = h :: rest /\ hp = last rest h /\ In hp ms /\
lk h = Some (Some hp, Some (hd h rest)) /\ (exists pp, lk hp = Some (Some pp, Some h)) /\ (hp = h <-> rest = []).
Proof.
intros Hr. destruct (ring_head_In _ _ _ Hr) as [_ [rest ->]]. destruct Hr as [[Hnd Hch] _].
exists rest, (last rest h). split; [reflexivity|]. split; [reflexivity|].
split; [destruct rest as [|r0 rest']; [left; reflexivity | right; apply In_last; discriminate]|].
cbn [chain] in Hch. rewrite last_cons in Hch. destruct Hch as [Lh Hc]. split; [exact Lh|]. split.
- destruct rest as [|y rest'].
+ cbn. exists h. exact Lh.
+ rewrite (last_indep (y :: rest') h y ltac:(discriminate)). change (last (y :: rest') y) with (last (y :: rest') y).
destruct (chain_last lk h (y :: rest') h y Hc ltac:(discriminate)) as [pp Hpp]. exists pp. exact Hpp.
- split; [| intros ->; reflexivity]. intros E. destruct rest as [|y rest']; [reflexivity|]. exfalso.
apply NoDup_cons_iff in Hnd as [Hni _]. apply Hni. rewrite <- E at 1. apply In_last. discriminate.
Qed.
Section n.
Variables (Y : list sptr) (U : Z -> Z) (s : astate) (g : sptr).
Hypothesis HI : Inv Y None U s.
Hypothesis Hg : In g Y.
Inductive fcase := FC0 | FC1a (h : sptr) (hnx : option sptr) | FC1b (h hp : sptr) (hnx hpp : option sptr).
Definition fcase_facts (c : fcase) : Prop :=
match c with
| FC0 => st_free_meta_head s = None
| FC1a h hnx => st_free_meta_head s = Some h /\ MT s h = Some (MFree (Some h) hnx) /\ memb h Y = false /\ h <> g
| FC1b h hp hnx hpp => st_free_meta_head s = Some h /\ MT s h = Some (MFree (Some hp) hnx) /\ memb h Y = false /\ h <> g /\
hp <> h /\ hp <> g /\ MT s hp = Some (MFree hpp (Some h)) /\ memb hp Y = false
end.
Lemma free_ring_cases : exists c, fcase_facts c.
Proof.
destruct (inv_rings HI) as ((ms & FR & Fall) & _ & _).
assert (NG : forall q, memb q Y = false -> q <> g) by (intros q Hq ->; rewrite (proj2 (memb_In g Y) Hg) in Hq; discriminate).
destruct (st_free_meta_head s) as [h|] eqn:Eh; [| exists FC0; exact Eh].
destruct (ring_head_prev _ _ _ FR) as (rest & hp & Ems & Ehp & Hpin & Lh & [pp Lhp] & Hiff).
destruct (flinks_free _ _ _ _ Lh) as (pr' & nx' & Mh & Eh' & Lk).
destruct (flinks_free _ _ _ _ Lhp) as (pr'' & nx'' & Mhp & Ehp' & Lk').
injection Lk as E1 E2. injection Lk' as E3 E4. subst pr' nx' pr'' nx''.
destruct (sptr_eq_dec hp h) as [E|Hne].
- exists (FC1a h (Some (hd h rest))). cbn. split; [exact Eh|]. split; [rewrite Eh', E; reflexivity|]. split; [exact Mh | apply NG; exact Mh].
- exists (FC1b h hp (Some (hd h rest)) (Some pp)). cbn.
split; [exact Eh|]. split; [exact Eh'|]. split; [exact Mh|]. split; [apply NG; exact Mh|].
split; [exact Hne|]. split; [apply NG; exact Mhp|]. split; [exact Ehp' | exact Mhp].
Qed.
End n.
Lemma used_metas_upd_notused s q x :
MT s q <> None -> (forall a, x <> MUsed a) ->
incl (used_metas (upd_meta q x s)) (used_metas s).
Proof.
unfold MT, used_metas, upd_meta. cbn. induction (st_metas s) as [|[p y] t IH]; cbn; intros Hq Hx; [congruence|].
destruct (sptr_eqb q p) eqn:E.
- apply sptr_eqb_eq in E. subst p. cbn. intros e He. apply in_app_iff in He as [He|He].
+ destruct x; try (destruct He; fail). exfalso. exact (Hx _ eq_refl).
+ apply in_app_iff. right. exact He.
- cbn. intros e He. apply in_app_iff in He as [He|He]; apply in_app_iff; [left; exact He | right; exact (IH Hq Hx e He)].
Qed.
Lemma used_metasX_upd_notused X s q x :
MT s q <> None -> (forall a, x <> MUsed a) ->
incl (used_metasX X (upd_meta q x s)) (used_metasX X s).
Proof.
intros Hq Hx e He. unfold used_metasX in *. apply filter_In in He as [He Hf]. apply filter_In. split; [exact (used_metas_upd_notused s q x Hq Hx e He) | exact Hf].
Qed.
Lemma imageX_upd_notused X s q x c :
MT s q <> None -> (forall a, x <> MUsed a) ->
In c (imageX X (upd_meta q x s)) -> In c (meta_slot_cells q (Some x)) \/ In c (imageX X s).
Proof.
intros Hq Hx Hc. unfold imageX in *. rewrite ctx_cells_upd_meta in Hc.
change (st_areas (upd_meta q x s)) with (st_areas s) in Hc.
apply in_app_iff in Hc as [Hc|Hc]; [right; apply in_app_iff; left; exact Hc|].
apply in_app_iff in Hc as [Hc|Hc].
- destruct (areas_cells_upd s q x (st_areas s) c Hc) as [H|H]; [right | left; exact H].
apply in_app_iff. right. apply in_app_iff. left. exact H.
- right. apply in_app_iff. right. apply in_app_iff. right.
apply in_flat_map in Hc as (gm & Hgm & Hc). apply in_flat_map. exists gm. split; [exact (used_metasX_upd_notused X s q x Hq Hx gm Hgm) | exact Hc].
Qed.
Lemma tail_cellsX_upd_notused X s q x c :
MT s q <> None -> (forall a, x <> MUsed a) ->
In c (tail_cellsX X (upd_meta q x s)) -> In c (tail_cellsX X s).
Proof.
intros Hq Hx Hc. unfold tail_cellsX in *.
apply in_flat_map in Hc as (gm & Hgm & Hc). apply in_flat_map. exists gm. split; [exact (used_metasX_upd_notused X s q x Hq Hx gm Hgm) | exact Hc].
Qed.
Lemma used_metasX_uncons X g s :
(forall a, MT s g <> Some (MUsed a)) -> NoDup (keys s) -> used_metasX (g :: X) s = used_metasX X s.
Proof.
intros Hg ND. unfold used_metasX. apply filter_ext_in. intros [q a] Hin. cbn [fst]. rewrite memb_cons.
destruct (sptr_eqb q g) eqn:E; [|reflexivity]. apply sptr_eqb_eq in E. subst q. exfalso.
apply (Hg a). apply (used_metas_iff s g a ND). exact Hin.
Qed.
Lemma imageX_uncons X g s : (forall a, MT s g <> Some (MUsed a)) -> NoDup (keys s) -> imageX (g :: X) s = imageX X s.
Proof. intros Hg ND. unfold imageX. rewrite (used_metasX_uncons X g s Hg ND). reflexivity. Qed.
Lemma tail_cellsX_uncons X g s : (forall a, MT s g <> Some (MUsed a)) -> NoDup (keys s) -> tail_cellsX (g :: X) s = tail_cellsX X s.
Proof. intros Hg ND. unfold tail_cellsX. rewrite (used_metasX_uncons X g s Hg ND). reflexivity. Qed.
End b.

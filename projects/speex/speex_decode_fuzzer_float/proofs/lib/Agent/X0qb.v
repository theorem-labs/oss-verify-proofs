(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1og X1r3 X1q8 X1po X1pv X1pf X1pm X1px X1pj X1q4
X1q0 X1pn X1qf X1qg X1ql X1q6 X1qh X1qn X1qd X1qe X1qj X1q5 X1pi X1qm X1ph X1qc.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qm X0qn X0px X0qc X0q7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation live_at0 := X0qc.live_at0 (only parsing).
Notation RGA := X0qc.RGA (only parsing).
Notation RBIG := X0qc.RBIG (only parsing).

Lemma rga_init ceil resv : RGA (minit 0 ceil resv) ∅ [].
Proof.
split; [| split].
- intros c q H. rewrite lookup_empty in H. discriminate H.
- intros b Hb. destruct Hb.
- intros c g i H. cbn in H. rewrite lookup_empty in H. discriminate H.
Qed.

Lemma live_at0_perm LB LB' c : Permutation LB LB' -> live_at0 LB c -> live_at0 LB' c.
Proof. intros P sfH_; first [ sf_destruct 4%nat sfH_ as b Hb E1 E2 | sf_fb; destruct sfH_ as (b & Hb & E1 & E2) ]. exists b. split; [eapply Permutation_in; [exact P| exact Hb]| auto]. Qed.

Lemma rga_perm st hdr LB LB' : Permutation LB LB' -> RGA st hdr LB -> RGA st hdr LB'.
Proof.
intros P (K & E & B). split; [exact K| split].
- intros b Hb. apply E. eapply Permutation_in; [apply Permutation_sym; exact P| exact Hb].
- intros c g i Hs Hm NL. apply (B c g i Hs Hm). intros L0. apply NL. eapply live_at0_perm; [exact P| exact L0].
Qed.

Lemma slot_top_strip st c : slot_top (strip st) c = slot_top st c.
Proof. reflexivity. Qed.

Section FACTS.
Context {RCEIL : RunCeiling}.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="X L BL LS INV IM IS"] Lemma slot_hosts c g i : s_slots st !! c = Some (g, i) ->
exists bg, hosts st bg g /\ 0 <= i <= m_last_idx (MR st g) /\ c = (fst bg, sstart (MR st g) i).
Proof.
intros Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hg] & Hi & Ec). exists bg.
rewrite (slot_start'_eq _ _ _ IM _ _ _ Hg) in Ec. auto.
Qed.

#[using="X L BL LS INV IM IG IS"] Lemma top_iff_base0 bg g : hosts st bg g -> (m_maplen (MR st g) <> 0 <-> snd bg = 0).
Proof.
intros Hg. destruct (hosts_ok _ _ _ IG _ _ Hg) as (ai & Hb & GO). split.
- intros Hml. exact (proj1 (g_top _ _ _ _ _ _ GO Hml)).
- intros B0 Hml. first [ pose proof (g_nest _ _ _ _ _ _ GO Hml) as sfP_; sf_destruct 4%nat sfP_ as p ip Hs _ | sf_fb; destruct (g_nest _ _ _ _ _ _ GO Hml) as (p & ip & Hs & _) ].
first [ pose proof (slot_hosts bg p ip Hs) as sfP_; sf_destruct 4%nat sfP_ as bp Hp Hip Ebg | sf_fb; destruct (slot_hosts bg p ip Hs) as (bp & Hp & Hip & Ebg) ].
pose proof (sstart0 _ _ _ IM _ _ Hp) as S0. pose proof (sstart_mono _ _ _ IG _ _ 0 ip Hp ltac:(lia)) as SM.
destruct (hosts_ok _ _ _ IG _ _ Hp) as (aip & _ & GOp). pose proof (g_align _ _ _ _ _ _ GOp) as [A0 _].
rewrite Ebg in B0. cbn in B0. unfold UNIT in *. lia.
Qed.

#[using="X L BL LS INV IM IG IS"] Lemma slot_mod16 c g i : s_slots st !! c = Some (g, i) -> snd c mod 16 = 0.
Proof.
intros Hs. first [ pose proof (slot_hosts c g i Hs) as sfP_; sf_destruct 4%nat sfP_ as bg Hg Hi -> | sf_fb; destruct (slot_hosts c g i Hs) as (bg & Hg & Hi & ->) ]. cbn [snd].
pose proof (stride_ge _ _ _ IG _ _ Hg) as [SG SM]. destruct (hosts_ok _ _ _ IG _ _ Hg) as (a & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
unfold sstart, UNIT in *. rewrite (hosts_gbase _ _ _ IM _ _ Hg).
pose proof (Z.div_mod (snd bg) 16 ltac:(lia)) as D1. rewrite A16 in D1. pose proof (Z.div_mod (get_stride (MR st g)) 16 ltac:(lia)) as D2. rewrite SM in D2.
replace (snd bg + 16 + get_stride (MR st g) * i) with ((snd bg / 16 + 1 + get_stride (MR st g) / 16 * i) * 16) by nia.
apply Z_mod_mult.
Qed.

#[using="X L LS INV IM IG IS"] Lemma nested_block_small c g i off n : s_slots st !! c = Some (g, i) -> m_maplen (MR st g) = 0 ->
In ((c, off), n) BL -> n < RBIG.
Proof.
intros Hs Hml Hk. destruct (slot_hosts c g i Hs) as (bg & Hg & _). destruct (hosts_ok _ _ _ IG _ _ Hg) as (ai & Hb & GO).
pose proof (g_nsc _ _ _ _ _ _ GO Hml) as NSC. destruct (g_sc _ _ _ _ _ _ GO) as [[SC _]|(_ & _ & ML & _)]; [| exfalso; exact (ML Hml)].
destruct (g_stride _ _ _ _ _ _ GO ltac:(lia)) as (GS & _ & _).
first [ pose proof (is_blocks _ _ _ IS _ Hk) as sfP_; sf_destruct 6%nat sfP_ as m i' Hs' Hoff Hn Hfit | sf_fb; destruct (is_blocks _ _ _ IS _ Hk) as (m & i' & Hs' & Hoff & Hn & Hfit) ]. cbn [bslot boff bsize fst snd] in Hs', Hoff, Hn, Hfit.
rewrite Hs in Hs'. inversion Hs'. subst m i'.
assert (SCL : size_class (m_sizeclass (MR st g)) <= size_class 19) by (apply size_class_le; lia).
change (size_class 19) with 63 in SCL. fold (MR st g) in Hfit. unfold RBIG, UNIT, IB in *. destruct GS as [GS|GS]; [nia| lia].
Qed.

#[using="X L BL LS INV IM IG IS"] Lemma hdr_not_inT (c : cptr) m i bm (c1 : cptr) g1 i1 k :
hosts st bm m -> 0 <= i <= m_last_idx (MR st m) -> c = (fst bm, sstart (MR st m) i) -> s_groups st !! c = None ->
s_slots st !! c1 = Some (g1, i1) -> c1 <> c -> 1 <= k <= 3 ->
~ inT (fst c) (sstart (MR st m) i - 3) (sstart (MR st m) (i + 1) - 4) (fst c1, snd c1 - k).
Proof.
intros Hm Hi Ec NH Hs1 NE Hk [Ef HT]. cbn [fst snd] in Ef, HT.
first [ pose proof (slot_hosts c1 g1 i1 Hs1) as sfP_; sf_destruct 4%nat sfP_ as b1 Hg1 Hi1 Ec1 | sf_fb; destruct (slot_hosts c1 g1 i1 Hs1) as (b1 & Hg1 & Hi1 & Ec1) ].
assert (Ef1 : fst b1 = fst bm) by (rewrite Ec1 in Ef; rewrite Ec in Ef; exact Ef).
assert (NEQ : g1 <> m \/ i1 <> i).
{ destruct (aptr_eq_dec g1 m) as [->|]; [right| left; congruence]. intros ->. apply NE. rewrite Ec1, Ec.
rewrite (hosts_inj _ _ _ IM _ _ _ Hg1 Hm). reflexivity. }
rewrite Ec in NH. cbn in NH.
pose proof (@sep_h3 _ _ _ _ IM IG IS m bm i Hm Hi NH g1 b1 i1 Hg1 Ef1 Hi1 NEQ) as D.
rewrite Ec1 in HT. cbn [snd] in HT. rewrite sstart_succ in D, HT. clear - D HT Hk. lia.
Qed.
End FACTS.

Lemma corr_slot_unique st LB BL b1 b2 :
CORR st LB BL -> NoDup (map bslot BL) -> In b1 LB -> In b2 LB -> blk_slot b1 = blk_slot b2 -> b1 = b2.
Proof.
intros CR. induction CR as [|x k LB0 BL0 Cx CR IH]; intros ND H1 H2 Es; [destruct H1|].
cbn [map] in ND. apply NoDup_cons in ND as [NI ND].
destruct H1 as [<-|H1]; destruct H2 as [<-|H2].
- reflexivity.
- exfalso. apply NI. apply list_elem_of_In. destruct (Forall2_In_l _ _ _ _ CR H2) as (k2 & Hk2 & (D1 & _)).
rewrite <- (proj1 Cx), Es, D1. apply in_map. exact Hk2.
- exfalso. apply NI. apply list_elem_of_In. destruct (Forall2_In_l _ _ _ _ CR H1) as (k1 & Hk1 & (D1 & _)).
rewrite <- (proj1 Cx), <- Es, D1. apply in_map. exact Hk1.
- exact (IH ND H1 H2 Es).
Qed.

Lemma rga_free {RCEIL : RunCeiling} resv st LB (b : block) (pf : aptr) (o o' : mem) ans st' hdr :
AREACH_from resv st LB -> In b LB ->
fst pf = fst (blk_slot b) -> conc st pf = blk_addr b ->
follow (mrun o (free st (Some pf))) ans = Some (o', st') ->
RGA st hdr LB ->
RGA st' hdr (filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot b))) LB).
Proof.
intros AR Hb Hfst Hconc FF (K & E & B).
first [ pose proof (areach_inv resv st LB AR) as sfP_; sf_destruct 8%nat sfP_ as L LS BL INV LIVE RESV SEC CR | sf_fb; destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR) ].
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as IR IA IM IL IG IS ISH | sf_fb; destruct sfP_ as (IR & IA & IM & IL & IG & IS & ISH) ].
destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
destruct k as [[c bo] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3.
destruct (blk_region _ _ _ _ _ ((c, bo), n) INV Hk) as (r & Hr & Kr). cbn [bslot fst snd] in Hr.
assert (Epf : pf = aadd c (UNIT * bo)).
{ unfold conc, get_region in Hconc, C3. rewrite Hfst, C1 in Hconc. rewrite Hr in Hconc, C3. rewrite C3 in Hconc.
apply injective_projections; unfold aadd; cbn [fst snd]; [rewrite Hfst, C1; reflexivity| lia]. }
subst pf.
first [ pose proof (free_leaf_frame pans_mem pupd_mem pans_mem_range st L BL LS c bo n o ans o' st' INV Hk FF) as sfP_; sf_destruct 4%nat sfP_ as F1 F2 F3 F4 | sf_fb; destruct (free_leaf_frame pans_mem pupd_mem pans_mem_range st L BL LS c bo n o ans o' st' INV Hk FF) as (F1 & F2 & F3 & F4) ].
destruct (free_leaf_facts pans_mem pupd_mem st L BL LS c bo n o ans o' st' INV Hk FF) as [SUB _].
first [ pose proof (free_sim pans_mem pupd_mem pans_mem_range st L BL LS c bo n o ans o' st' INV Hk FF) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ LS' INV' | sf_fb; destruct (free_sim pans_mem pupd_mem pans_mem_range st L BL LS c bo n o ans o' st' INV Hk FF) as (_ & _ & _ & LS' & INV') ].
pose proof INV' as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ IM' _ IG' IS' _ | sf_fb; destruct sfP_ as (_ & _ & IM' & _ & IG' & IS' & _) ].
first [ pose proof (is_blocks _ _ _ IS _ Hk) as sfP_; sf_destruct 6%nat sfP_ as g i Hsc Hoffr _ Hfit | sf_fb; destruct (is_blocks _ _ _ IS _ Hk) as (g & i & Hsc & Hoffr & _ & Hfit) ]. cbn [bslot boff bsize fst snd] in Hsc, Hoffr, Hfit.

assert (TOPK : forall (c1 : cptr) g1 i1, s_slots st' !! c1 = Some (g1, i1) ->
s_slots st !! c1 = Some (g1, i1) /\ slot_top st' c1 = slot_top st c1 /\ conc st' c1 = conc st c1
/\ (m_maplen (MR st' g1) <> 0 <-> m_maplen (MR st g1) <> 0)).
{ intros c1 g1 i1 Hs1. pose proof (F1 _ _ Hs1) as Hs0. split; [exact Hs0|].
first [ pose proof (slot_hosts _ _ _ _ _ INV' c1 g1 i1 Hs1) as sfP_; sf_destruct 4%nat sfP_ as bg' Hg' _ Ec1' | sf_fb; destruct (slot_hosts _ _ _ _ _ INV' c1 g1 i1 Hs1) as (bg' & Hg' & _ & Ec1') ].
first [ pose proof (slot_hosts _ _ _ _ _ INV c1 g1 i1 Hs0) as sfP_; sf_destruct 4%nat sfP_ as bg Hg _ Ec1 | sf_fb; destruct (slot_hosts _ _ _ _ _ INV c1 g1 i1 Hs0) as (bg & Hg & _ & Ec1) ].
assert (Ebg : bg' = bg).
{ destruct Hg' as [ai' Hg'']. destruct (F2 _ _ _ Hg'') as [ai0 Hg0]. exact (hosts_inj _ _ _ IM _ _ _ (ex_intro _ ai0 Hg0) Hg). }
subst bg'.
pose proof (top_iff_base0 _ _ _ _ _ INV' bg g1 Hg') as T1. pose proof (top_iff_base0 _ _ _ _ _ INV bg g1 Hg) as T0.
assert (TI : m_maplen (MR st' g1) <> 0 <-> m_maplen (MR st g1) <> 0) by tauto.
split; [| split; [| exact TI]].
- unfold slot_top. rewrite Hs1, Hs0. fold (MR st' g1). fold (MR st g1).
destruct (Z.eqb_spec (m_maplen (MR st' g1)) 0), (Z.eqb_spec (m_maplen (MR st g1)) 0); cbn; try reflexivity; exfalso; tauto.
- destruct Hg' as [ai' Hg'']. destruct (ig_region _ _ _ IG' _ _ Hg'') as (r1 & Hr1 & _).
apply conc_same. exists r1. rewrite Ec1'. cbn [fst]. split; [exact (SUB _ _ Hr1)| exact Hr1]. }
split; [exact K| split].
-   intros b' Hb'. apply In_filter_bool in Hb' as [Hb' NEb]. rewrite C1 in NEb. pose proof (E b' Hb') as Eb.
destruct (Forall2_In_l _ _ _ _ CR Hb') as (k' & Hk' & (D1 & D2 & D3)).
assert (Hk'' : In k' (bl_remove c BL)).
{ rewrite (bl_remove_filter c BL (is_nodup _ _ _ IS)). apply In_filter_bool. split; [exact Hk'|].
rewrite <- D1. exact NEb. }
first [ pose proof (is_blocks _ _ _ IS' _ Hk'') as sfP_; sf_destruct 4%nat sfP_ as g1 i1 Hs1 _ | sf_fb; destruct (is_blocks _ _ _ IS' _ Hk'') as (g1 & i1 & Hs1 & _) ]. rewrite <- D1 in Hs1.
first [ pose proof (TOPK _ _ _ Hs1) as sfP_; sf_destruct 4%nat sfP_ as Hs0 ET EC _ | sf_fb; destruct (TOPK _ _ _ Hs1) as (Hs0 & ET & EC & _) ]. rewrite ET, EC. exact Eb.
-   intros c1 g1 i1 Hs1 Hml NL. first [ pose proof (TOPK _ _ _ Hs1) as sfP_; sf_destruct 4%nat sfP_ as Hs0 _ _ TI | sf_fb; destruct (TOPK _ _ _ Hs1) as (Hs0 & _ & _ & TI) ].
assert (Hml0 : m_maplen (MR st g1) <> 0) by (apply TI; exact Hml).
destruct (aptr_eq_dec c1 c) as [->|NE].
+
pose proof (E b Hb) as Eb. rewrite C1 in Eb. unfold slot_top in Eb. rewrite Hs0 in Eb. fold (MR st g1) in Eb.
replace (negb (m_maplen (MR st g1) =? 0)) with true in Eb by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Hml0).
destruct Eb as (Htag & Haddr & Hh).
assert (Etag : snd (blk_id b) = bo) by (rewrite C3 in Haddr; unfold UNIT in Haddr; lia).
destruct (Z.eq_dec bo 0) as [B0|B0].
*
rewrite Hh, Etag, B0. destruct (F4 (g1, i1) B0 Hs1) as (R3 & R2 & R1).
split; [exists 255; rewrite R3; repeat split; try reflexivity; lia|].
rewrite R2, R1. unfold byte_of. cbn. repeat split; try reflexivity; try lia.
*
assert (NL0 : ~ live_at0 LB c).
{ intros sfH_; first [ sf_destruct 4%nat sfH_ as b2 Hb2 Es2 Ez2 | sf_fb; destruct sfH_ as (b2 & Hb2 & Es2 & Ez2) ]. pose proof (E b2 Hb2) as Eb2. unfold slot_top in Eb2. rewrite Es2, Hs0 in Eb2. fold (MR st g1) in Eb2.
replace (negb (m_maplen (MR st g1) =? 0)) with true in Eb2 by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Hml0).
destruct Eb2 as (_ & Haddr2 & _).

destruct (Forall2_In_l _ _ _ _ CR Hb2) as (k2 & Hk2 & (G1 & G2 & G3)).
assert (Ek : k2 = ((c, bo), n)).
{ pose proof (is_nodup _ _ _ IS) as ND.
first [ pose proof (is_blocks _ _ _ IS _ Hk2) as sfP_; sf_destruct 6%nat sfP_ as g2 i2 Hs2 Ho2 _ Hf2 | sf_fb; destruct (is_blocks _ _ _ IS _ Hk2) as (g2 & i2 & Hs2 & Ho2 & _ & Hf2) ]. rewrite <- G1, Es2, Hs0 in Hs2. inversion Hs2. subst g2 i2.
destruct k2 as [[c2 o2] n2]. cbn [bslot boff bsize fst snd] in G1, G2, G3, Ho2, Hf2. rewrite Es2 in G1. subst c2.
rewrite Ez2 in Haddr2. rewrite Haddr2 in G3.
assert (o2 = 0) by (unfold UNIT in G3; lia). subst o2.

exfalso. apply B0.
clear - ND Hk Hk2 C3 G3 Haddr Etag Ez2.
induction BL as [|x BL' IH]; [destruct Hk|].
cbn [map] in ND. apply NoDup_cons in ND as [NI ND'].
destruct Hk as [->|Hk]; destruct Hk2 as [E2|Hk2].
- inversion E2. reflexivity.
- exfalso. apply NI. apply list_elem_of_In. change (bslot (c, bo, n)) with (bslot ((c, 0), n2)). apply in_map. exact Hk2.
- exfalso. apply NI. rewrite E2. apply list_elem_of_In. change (bslot (c, 0, n2)) with (bslot ((c, bo), n)). apply in_map. exact Hk.
- exact (IH Hk Hk2 ND'). }
exfalso. apply B0. subst k2. cbn [bslot boff fst snd] in G3. rewrite Ez2 in Haddr2. rewrite Haddr2 in G3. unfold UNIT in G3. lia. }
pose proof (B c g1 i1 Hs0 Hml0 NL0) as Bc.
assert (E3 : forall k0, 1 <= k0 <= 3 -> cell_read (get_shadow st' (fst c)) (snd c - k0) = cell_read (get_shadow st (fst c)) (snd c - k0)).
{ intros k0 Hk0. apply (F3 c (g1, i1) k0 Hs1 Hk0). right. exact B0. }
destruct (hdr !! c) as [q|].
-- eapply HB_cells; [| exact Bc]. intros k0 Hk0. exact (E3 k0 Hk0).
-- rewrite (E3 3) by lia. exact Bc.
+
assert (NL0 : ~ live_at0 LB c1).
{ intros sfH_; first [ sf_destruct 4%nat sfH_ as b2 Hb2 Es2 Ez2 | sf_fb; destruct sfH_ as (b2 & Hb2 & Es2 & Ez2) ]. apply NL. exists b2. split; [| auto]. apply In_filter_bool. split; [exact Hb2|].
rewrite Es2, C1. destruct (aptr_eqb_spec c1 c) as [E0|_]; [exfalso; exact (NE E0)| reflexivity]. }
pose proof (B c1 g1 i1 Hs0 Hml0 NL0) as Bc.
assert (E3 : forall k0, 1 <= k0 <= 3 -> cell_read (get_shadow st' (fst c1)) (snd c1 - k0) = cell_read (get_shadow st (fst c1)) (snd c1 - k0)).
{ intros k0 Hk0. apply (F3 c1 (g1, i1) k0 Hs1 Hk0). left. exact NE. }
destruct (hdr !! c1) as [q|].
* eapply HB_cells; [| exact Bc]. intros k0 Hk0. exact (E3 k0 Hk0).
* rewrite (E3 3) by lia. exact Bc.
Qed.

Lemma rga_resize {RCEIL : RunCeiling} resv st LB (b : block) (off n' : Z) hdr :
AREACH_from resv st LB -> In b LB ->
0 <= off -> blk_addr b = conc st (blk_slot b) + UNIT * off -> 0 <= n' ->
(forall g idx, (s_slots st) !! (blk_slot b) = Some (g, idx) ->
UNIT * off + n' <= get_stride (get_meta_rec st g) - IB
/\ get_stride (get_meta_rec st g) - IB - UNIT * off - n' < 2^32) ->
RGA st hdr LB ->
RGA (resize_state st (blk_slot b) off n') hdr (lb_resize b n' LB).
Proof.
intros AR Hb Hoff Haddr Hn' FIT (K & E & B).
first [ pose proof (areach_inv resv st LB AR) as sfP_; sf_destruct 8%nat sfP_ as L LS BL INV LIVE RESV SEC CR | sf_fb; destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR) ].
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as IR IA IM IL IG IS ISH | sf_fb; destruct sfP_ as (IR & IA & IM & IL & IG & IS & ISH) ].
destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
destruct k as [[c bo] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3.
first [ pose proof (is_blocks _ _ _ IS _ Hk) as sfP_; sf_destruct 6%nat sfP_ as m i Hs _ _ _ | sf_fb; destruct (is_blocks _ _ _ IS _ Hk) as (m & i & Hs & _ & _ & _) ]. cbn [bslot fst snd] in Hs.
first [ pose proof (slot_hosts _ _ _ _ _ INV c m i Hs) as sfP_; sf_destruct 4%nat sfP_ as bm Hm Hi Ec | sf_fb; destruct (slot_hosts _ _ _ _ _ INV c m i Hs) as (bm & Hm & Hi & Ec) ].
assert (Eoff : bo = off) by (rewrite C1, C3 in Haddr; unfold UNIT in Haddr; lia). subst bo.
rewrite C1 in FIT |- *. destruct (FIT m i Hs) as [Hfit Hres].
assert (EST : resize_state st c off n' = X1qm.stf st c off n' m i).
{ unfold resize_state. rewrite Hs. unfold X1qm.stf. rewrite <- (resize_body_eq st c off n' m i). reflexivity. }
rewrite EST. set (st' := X1qm.stf st c off n' m i).
pose proof (resize_ctrl st c off n' m i) as [CE _]. fold st' in CE.
assert (SLE : s_slots st' = s_slots st) by exact (ce_slots _ _ CE).
assert (MRE : forall x, get_meta_rec st' x = get_meta_rec st x) by (intros x; apply get_meta_rec_ext; exact (ce_metas _ _ CE)).
assert (TOPE : forall c1, slot_top st' c1 = slot_top st c1).
{ intros c1. unfold slot_top. rewrite SLE. destruct (s_slots st !! c1) as [[g1 i1]|]; [rewrite MRE|]; reflexivity. }
assert (CONC : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite (ce_regions _ _ CE); reflexivity).
assert (NH : s_groups st !! c = None) by exact (rs_NH st L BL LS c off n INV Hk).

assert (LA : forall c1, live_at0 LB c1 -> live_at0 (lb_resize b n' LB) c1).
{ intros c1 sfH_; first [ sf_destruct 4%nat sfH_ as b2 Hb2 Es2 Ez2 | sf_fb; destruct sfH_ as (b2 & Hb2 & Es2 & Ez2) ]. destruct (aptr_eq_dec (blk_slot b2) c) as [E2|NE2].
- assert (b2 = b) by (apply (corr_slot_unique st LB BL b2 b CR (is_nodup _ _ _ IS) Hb2 Hb); rewrite E2, C1; reflexivity). subst b2.
exists (blk_id b, blk_addr b, n'). split; [left; reflexivity|]. cbn [blk_slot blk_id fst snd]. split; [| exact Ez2].
unfold blk_slot in Es2. exact Es2.
- exists b2. split; [| auto]. right. apply In_filter_bool. split; [exact Hb2|]. rewrite C1.
destruct (aptr_eqb_spec (blk_slot b2) c); [contradiction| reflexivity]. }
split; [exact K| split].
-   intros b' Hb'. rewrite TOPE, CONC.
assert (Hb0 : exists b0, In b0 LB /\ blk_slot b' = blk_slot b0 /\ blk_id b' = blk_id b0 /\ blk_addr b' = blk_addr b0).
{ destruct Hb' as [<-|Hb']; [exists b; cbn [blk_slot blk_id blk_addr fst snd]; auto|].
apply In_filter_bool in Hb' as [Hb' _]. exists b'. auto. }
first [ rename Hb0 into sfR_; sf_destruct 5%nat sfR_ as b0 Hb0 -> -> -> | sf_fb; destruct Hb0 as (b0 & Hb0 & -> & -> & ->) ]. exact (E b0 Hb0).
-   intros c1 g1 i1 Hs1 Hml NL. rewrite SLE in Hs1. rewrite MRE in Hml.
assert (NL0 : ~ live_at0 LB c1) by (intros L0; exact (NL (LA _ L0))).
pose proof (B c1 g1 i1 Hs1 Hml NL0) as Bc.
assert (E3 : forall k0, 1 <= k0 <= 3 -> cell_read (get_shadow st' (fst c1)) (snd c1 - k0) = cell_read (get_shadow st (fst c1)) (snd c1 - k0)).
{ intros k0 Hk0. destruct (aptr_eq_dec c1 c) as [->|NE].
-
assert (Ho : 0 < off).
{ pose proof (E b Hb) as Eb. rewrite C1 in Eb. unfold slot_top in Eb. rewrite Hs in Eb.
rewrite Hs in Hs1. inversion Hs1. subst g1 i1.
replace (negb (m_maplen (get_meta_rec st m) =? 0)) with true in Eb by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Hml).
destruct Eb as (T1 & T2 & _). rewrite C3 in T2.
destruct (Z.eq_dec off 0) as [O0|]; [| lia]. exfalso. apply NL0. exists b. split; [exact Hb|]. split; [exact C1|]. unfold UNIT in T2. lia. }
exact (stf_read_chdr st L BL LS c off n' m bm i INV Hs Hm Hn' Hfit k0 Ho Hk0).
- rewrite (stf_read_T st L BL LS c off n n' m bm i INV Hk Hs Hm Hn' Hfit (fst c1, snd c1 - k0)); [reflexivity|].
rewrite Ec at 1. cbn [fst]. replace (fst bm) with (fst c) by (rewrite Ec; reflexivity).
exact (hdr_not_inT x0 st L BL LS INV c m i bm c1 g1 i1 k0 Hm Hi Ec NH Hs1 NE Hk0). }
destruct (hdr !! c1) as [q|].
+ eapply HB_cells; [| exact Bc]. exact E3.
+ rewrite (E3 3) by lia. exact Bc.
Qed.

Lemma mark_conts_lookup_in l hdr (c : cptr) : In c l -> (mark_conts l hdr) !! c = Some (cont_q c).
Proof.
induction l as [|x l IH]; intros H; [destruct H|]. cbn [mark_conts fold_right].
destruct (aptr_eq_dec c x) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|].
change (fold_right (fun c0 h => <[c0 := cont_q c0]> h) hdr l) with (mark_conts l hdr).
rewrite lookup_insert_ne by congruence. apply IH. destruct H as [->|H]; [congruence| exact H].
Qed.
Lemma mark_conts_lookup_notin l hdr (c : cptr) : ~ In c l -> (mark_conts l hdr) !! c = hdr !! c.
Proof.
induction l as [|x l IH]; intros H; [reflexivity|]. cbn [mark_conts fold_right].
change (fold_right (fun c0 h => <[c0 := cont_q c0]> h) hdr l) with (mark_conts l hdr).
rewrite lookup_insert_ne by (intros ->; apply H; left; reflexivity). apply IH. intros H'. apply H. right. exact H'.
Qed.
Lemma mark_conts_lookup_inv l hdr (c : cptr) q : (mark_conts l hdr) !! c = Some q -> (In c l /\ q = cont_q c) \/ (~ In c l /\ hdr !! c = Some q).
Proof.
intros H. destruct (in_dec aptr_eq_dec c l) as [I|NI].
- left. rewrite (mark_conts_lookup_in l hdr c I) in H. inversion H. auto.
- right. rewrite (mark_conts_lookup_notin l hdr c NI) in H. auto.
Qed.

Lemma prune_lookup cs cs' hdr (c : cptr) :
(prune_new cs cs' hdr) !! c = if new_top_slot cs cs' c then None else hdr !! c.
Proof.
unfold prune_new. rewrite map_lookup_filter. destruct (hdr !! c) as [q|]; cbn; [| destruct (new_top_slot cs cs' c); reflexivity].
destruct (new_top_slot cs cs' c); cbn; [| reflexivity].
rewrite option_guard_False by (intros H; exact H). reflexivity.
Qed.

Lemma new_containers_in cs cs' (c : cptr) :
In c (new_containers cs cs') <-> slot_top cs' c = true /\ (s_groups cs) !! c = None /\ (s_groups cs') !! c <> None.
Proof.
unfold new_containers. rewrite In_filter_bool. rewrite andb_true_iff. rewrite <- list_elem_of_In.
split.
- intros (Hin & T & G). split; [exact T|]. split; [destruct (s_groups cs !! c); [discriminate| reflexivity]|].
apply list_elem_of_fmap in Hin as ([c' h] & -> & Hin). cbn. apply elem_of_map_to_list in Hin. rewrite Hin. discriminate.
- intros (T & G0 & G1). split; [| split; [exact T| rewrite G0; reflexivity]].
destruct (s_groups cs' !! c) as [h|] eqn:E; [| congruence]. apply list_elem_of_fmap. exists (c, h). split; [reflexivity|]. apply elem_of_map_to_list. exact E.
Qed.

Section MALLOC.
Context {RCEIL : RunCeiling}.
Variables (resv : list (Z * Z)) (st : mstate) (LB : list block) (hdr : gmap cptr Z) (n : Z).
Variables (o o1 : mem) (ans : list Z) (st2 : mstate) (g bg : aptr) (idx off : Z).
Let t : N := N.succ (s_tick st).
Hypothesis AR : AREACH_from resv st LB.
Hypothesis GA : RGA st hdr LB.
Hypothesis Hn : 0 <= n.
Hypothesis F1 : follow (mrun o (malloc_core full_lay (set_tick t st) n)) ans = Some (o1, (st2, Some (g, idx))).
Hypothesis Hmem : m_mem (get_meta_rec st2 g) = Some bg.
Let c : cptr := (fst bg, sstart (MR st2 g) idx).
Let stride : Z := get_stride (MR st2 g).
Let p : aptr := aadd c (UNIT * off).
Let slack : Z := (stride - IB - n) / UNIT.
Let ctr : Z := c_mmap_counter (ctx st2).
Hypothesis Hoff : 0 <= off <= 255.
Hypothesis Hfit : UNIT * off + n <= stride - IB.

Hypothesis HR0 : cell_read (get_shadow st2 (fst c)) (snd c - 3) = Known 0 -> off = fold_off (Z.land ctr 255) slack.
Hypothesis HR1 : forall v3 lo hi, cell_read (get_shadow st2 (fst c)) (snd c - 3) = Known v3 -> v3 <> 0 ->
cell_read (get_shadow st2 (fst c)) (snd c - 2) = Known lo -> cell_read (get_shadow st2 (fst c)) (snd c - 1) = Known hi ->
off = fold_off (Z.land (lo + 256 * hi + 1) 255) slack.

Hypothesis REGK : forall rid r, s_regions st !! rid = Some r -> exists r', s_regions st2 !! rid = Some r' /\ r_kind r' = r_kind r.
Let st' : mstate := havoc p n (fst (enframe_at st2 g idx n off)).
Let TOP : bool := negb (m_maplen (MR st2 g) =? 0).
Let tag : Z := if TOP then off else -1.
Let hdr1 : gmap cptr Z := hdr_after (strip st) (strip st2) hdr.
Let hdr2 : gmap cptr Z := if TOP then <[c := off]> hdr1 else hdr1.
Hypothesis AR' : AREACH_from resv st' (((c, tag), conc st' p, n) :: LB).

#[using="st n st2 g off t stride slack ctr TOP tag"] Lemma bytes2_eq q : 0 <= q < 2 ^ 16 -> byte_of q 0 + 256 * byte_of q 1 = q.
Proof.
intros Hq. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 8) with 256. rewrite (Z.mod_small (q / 256) 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
pose proof (Z.div_mod q 256 ltac:(lia)). lia.
Qed.

#[using="RCEIL resv o o1 ans t AR GA Hn F1 Hmem stride slack ctr Hoff Hfit HR0 HR1 REGK AR'"] Theorem rga_malloc :
slot_top (strip st2) c = TOP
/\ (TOP = true -> real_off hdr1 (strip st2) c n = off)
/\ (RBIG <= n -> TOP = true)
/\ RGA st' hdr2 (((c, tag), conc st' p, n) :: LB).
Proof.
first [ pose proof (areach_inv resv st LB AR) as sfP_; sf_destruct 8%nat sfP_ as L LS BL INV LIVE RESV SEC CR | sf_fb; destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR) ].
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as IR IA IM IL IG IS ISH | sf_fb; destruct sfP_ as (IR & IA & IM & IL & IG & IS & ISH) ].
pose proof (INVL_set_tick x0 st L BL LS t ltac:(unfold t; cbn; lia) INV) as INV0.
pose proof (TF0_tick_new st t (TKS_of _ _ _ _ _ INV) ltac:(unfold t; cbn; lia)) as TF0'.
first [ pose proof (malloc_core_leaf (set_tick t st) L BL LS n INV0 TF0' Hn pans_mem pupd_mem pans_mem_range o ans o1 st2 g idx F1) as sfP_; sf_destruct 10%nat sfP_ as L1 LS1 bg' Hg2 Hidx INV2 FIT TF2' RES32 [GP2 HK2] | sf_fb; destruct (malloc_core_leaf (set_tick t st) L BL LS n INV0 TF0' Hn pans_mem pupd_mem pans_mem_range o ans o1 st2 g idx F1) as (L1 & LS1 & bg' & Hg2 & Hidx & INV2 & FIT & TF2' & RES32 & [GP2 HK2]) ].
pose proof INV2 as sfP_; first [ sf_destruct 7%nat sfP_ as IR2 IA2 IM2 IL2 IG2 IS2 ISH2 | sf_fb; destruct sfP_ as (IR2 & IA2 & IM2 & IL2 & IG2 & IS2 & ISH2) ].
assert (Ebg : bg' = bg).
{ pose proof (hosts_mem _ _ _ IM2 _ _ Hg2) as M. fold (MR st2 g) in Hmem. unfold MR in M. rewrite M in Hmem. inversion Hmem. reflexivity. }
subst bg'.
destruct HK2 as [G0 S0 GE0 C0 N0].
pose proof (ef_slots (xpend x0 (Some c)) st2 L1 BL LS1 g bg idx INV2 Hg2 Hidx) as SL2. fold c in SL2.
pose proof (ef_NH (xpend x0 (Some c)) st2 L1 BL LS1 g bg idx INV2 Hg2 Hidx eq_refl) as NH2. fold c in NH2.
pose proof (ef_c16 (xpend x0 (Some c)) st2 L1 BL LS1 g bg idx n INV2 Hg2) as C16. fold c in C16.
assert (Est : st' = X1qe.stf st2 g bg idx n off).
{ unfold st', p. rewrite <- (ef_stf_eq (xpend x0 (Some c)) st2 L1 BL LS1 g bg idx n INV2 Hg2 off). reflexivity. }
destruct (X1qe.stf_ctrl st2 g bg idx n off) as [CE' _]. rewrite <- Est in CE'.
assert (SLE : s_slots st' = s_slots st2) by exact (ce_slots _ _ CE').
assert (MRE : forall x, MR st' x = MR st2 x) by (intros x; apply MR_ext; exact (ce_metas _ _ CE')).
assert (RGE : s_regions st' = s_regions st2) by exact (ce_regions _ _ CE').
assert (GRE : s_groups st' = s_groups st2) by exact (ce_groups _ _ CE').
first [ pose proof (areach_inv resv st' _ AR') as sfP_; sf_destruct 8%nat sfP_ as L' LS' BL' INV' _ _ _ CR' | sf_fb; destruct (areach_inv resv st' _ AR') as (L' & LS' & BL' & INV' & _ & _ & _ & CR') ].

assert (TOPc : slot_top (strip st2) c = TOP).
{ unfold slot_top. change (s_slots (strip st2)) with (s_slots st2). rewrite SL2. reflexivity. }

assert (TOPT : forall (c1 : cptr) g1 i1, s_slots st !! c1 = Some (g1, i1) -> (m_maplen (MR st2 g1) <> 0 <-> m_maplen (MR st g1) <> 0)).
{ intros c1 g1 i1 Hs1. first [ pose proof (slot_hosts _ _ _ _ _ INV c1 g1 i1 Hs1) as sfP_; sf_destruct 4%nat sfP_ as b1 [ai1 Hb1] _ _ | sf_fb; destruct (slot_hosts _ _ _ _ _ INV c1 g1 i1 Hs1) as (b1 & [ai1 Hb1] & _ & _) ].
destruct (G0 b1 (Some g1) ai1 Hb1) as [ai1' Hb1'].
pose proof (top_iff_base0 _ _ _ _ _ INV b1 g1 (ex_intro _ ai1 Hb1)) as T1.
pose proof (top_iff_base0 _ _ _ _ _ INV2 b1 g1 (ex_intro _ ai1' Hb1')) as T2. tauto. }

assert (NEWREG : forall (c1 : cptr) g1 i1, s_slots st2 !! c1 = Some (g1, i1) -> m_maplen (MR st2 g1) <> 0 -> s_slots st !! c1 = None ->
s_shadow st !! (fst c1) = None).
{ intros c1 g1 i1 Hs1 Hml1 Hn1.
first [ pose proof (slot_hosts _ _ _ _ _ INV2 c1 g1 i1 Hs1) as sfP_; sf_destruct 4%nat sfP_ as b1 Hb1 Hi1 Ec1 | sf_fb; destruct (slot_hosts _ _ _ _ _ INV2 c1 g1 i1 Hs1) as (b1 & Hb1 & Hi1 & Ec1) ].
pose proof (proj1 (top_iff_base0 _ _ _ _ _ INV2 b1 g1 Hb1) Hml1) as B10.
destruct (s_shadow st !! fst c1) as [sh|] eqn:ESH; [| reflexivity]. exfalso.
destruct (ish_dom _ _ ISH _ _ ESH) as (r & Hr & Kr).
destruct (REGK _ _ Hr) as (r' & Hr' & Kr').
destruct (ig_top _ _ _ IG (fst c1) r Hr Kr ltac:(discriminate)) as (T & HT & MT).
destruct HT as [aiT HT]. destruct (G0 _ _ _ HT) as [aiT' HT'].
assert (Eb1 : b1 = (fst c1, 0)) by (rewrite Ec1; cbn [fst]; destruct b1; cbn in B10 |- *; subst; reflexivity).
assert (ET : T = g1) by (apply (hosts_fun st2 (fst c1, 0)); [exists aiT'; exact HT'| rewrite <- Eb1; exact Hb1]). subst T.
pose proof (GE0 _ _ _ HT) as GEO. unfold geo_of in GEO. injection GEO. intros Esc Eml Eli Emm.
assert (ESS : slot_start' (MR st g1) i1 = slot_start' (MR st2 g1) i1).
{ unfold slot_start', get_stride. rewrite Emm, Eli, Eml, Esc. reflexivity. }
pose proof (is_total _ _ _ IS _ _ _ (ex_intro _ aiT HT) ltac:(rewrite <- Eli; exact Hi1)) as TOT.
rewrite ESS, (slot_start'_eq _ _ _ IM2 _ _ _ Hb1), <- Ec1 in TOT. rewrite TOT in Hn1. discriminate Hn1. }

set (conts := new_containers (strip st) (strip st2)) in *.
assert (CONTS : forall c1 : cptr, In c1 conts -> HB st2 c1 (cont_q c1) /\ 0 <= cont_q c1 < 2 ^ 16).
{ intros c1 Hin. apply new_containers_in in Hin as (T1 & Gn & Gs).
change (s_groups (strip st) !! c1) with (s_groups st !! c1) in Gn. change (s_groups (strip st2) !! c1) with (s_groups st2 !! c1) in Gs.
destruct (s_groups st2 !! c1) as [[[g1|] ai1]|] eqn:Eg1; [| exfalso; exact (ig_nometa _ _ _ IG2 _ _ Eg1)| congruence].
unfold slot_top in T1. change (s_slots (strip st2) !! c1) with (s_slots st2 !! c1) in T1.
destruct (s_slots st2 !! c1) as [[p0 i0]|] eqn:Es1; [| discriminate T1]. change (get_meta_rec (strip st2) p0) with (MR st2 p0) in T1.
first [ pose proof (slot_hosts _ _ _ _ _ INV2 c1 p0 i0 Es1) as sfP_; sf_destruct 4%nat sfP_ as bp Hbp Hi0 Ec1 | sf_fb; destruct (slot_hosts _ _ _ _ _ INV2 c1 p0 i0 Es1) as (bp & Hbp & Hi0 & Ec1) ].
assert (NZ : snd c1 <> 0).
{ rewrite Ec1. cbn [snd]. pose proof (sstart0 _ _ _ IM2 _ _ Hbp). pose proof (sstart_mono _ _ _ IG2 _ _ 0 i0 Hbp ltac:(lia)).
destruct (hosts_ok _ _ _ IG2 _ _ Hbp) as (a0 & _ & GO0). pose proof (g_align _ _ _ _ _ _ GO0). unfold UNIT in *. lia. }
first [ pose proof (N0 c1 g1 ai1 Gn Eg1 NZ) as sfP_; sf_destruct 9%nat sfP_ as p0' i0' bp' aip' Es1' Hbp' Hf' _ HBc | sf_fb; destruct (N0 c1 g1 ai1 Gn Eg1 NZ) as (p0' & i0' & bp' & aip' & Es1' & Hbp' & Hf' & _ & HBc) ].
rewrite Es1 in Es1'. inversion Es1'. subst p0' i0'.
pose proof (hosts_inj _ _ _ IM2 _ _ _ (ex_intro _ aip' Hbp') Hbp) as ->.
assert (B0 : snd bp = 0).
{ apply (proj1 (top_iff_base0 _ _ _ _ _ INV2 bp p0 Hbp)). apply Bool.negb_true_iff in T1. apply Z.eqb_neq in T1. exact T1. }
rewrite B0, Z.sub_0_r in HBc. fold (cont_q c1) in HBc. split; [exact HBc|]. exact (proj2 (proj2 (proj2 HBc))). }
assert (NCONT : forall (c1 : cptr) g1 i1, ~ In c1 conts -> s_slots st2 !! c1 = Some (g1, i1) -> m_maplen (MR st2 g1) <> 0 ->
s_groups st !! c1 <> None \/ s_groups st2 !! c1 = None).
{ intros c1 g1 i1 NI Hs1 Hml1. destruct (s_groups st2 !! c1) as [h|] eqn:Eg; [left| right; reflexivity]. intros Gn. apply NI.
apply new_containers_in. split; [| split; [exact Gn| change (s_groups (strip st2) !! c1) with (s_groups st2 !! c1); rewrite Eg; discriminate]].
unfold slot_top. change (s_slots (strip st2) !! c1) with (s_slots st2 !! c1). rewrite Hs1. change (get_meta_rec (strip st2) g1) with (MR st2 g1).
apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hml1. }

assert (E3 : forall (c1 : cptr) g1 i1 k, s_slots st2 !! c1 = Some (g1, i1) -> c1 <> c -> 1 <= k <= 3 ->
cell_read (get_shadow st' (fst c1)) (snd c1 - k) = cell_read (get_shadow st2 (fst c1)) (snd c1 - k)).
{ intros c1 g1 i1 k Hs1 NE Hk. rewrite Est.
apply (ef_read_T (xpend x0 (Some c)) st2 L1 BL LS1 g bg idx n INV2 Hg2 Hn FIT off (fst c1, snd c1 - k) ltac:(lia) Hfit).
change (fst bg) with (fst c). fold stride. unfold c at 2 3. cbn [snd]. rewrite <- sstart_succ. fold c.
exact (hdr_not_inT _ _ _ _ _ INV2 c g idx bg c1 g1 i1 k Hg2 Hidx eq_refl NH2 Hs1 NE Hk). }

assert (NIc : ~ In c conts).
{ intros Hin. apply new_containers_in in Hin as (_ & _ & Gs). apply Gs. exact NH2. }
assert (H1c : hdr1 !! c = if new_top_slot (strip st) (strip st2) c then None else hdr !! c).
{ unfold hdr1, hdr_after. fold conts. rewrite (mark_conts_lookup_notin _ _ _ NIc). apply prune_lookup. }

assert (NLc : ~ live_at0 LB c).
{ intros sfH_; first [ sf_destruct 4%nat sfH_ as b0 Hb0 Es0 _ | sf_fb; destruct sfH_ as (b0 & Hb0 & Es0 & _) ]. destruct (Forall2_In_l _ _ _ _ CR Hb0) as (k0 & Hk0 & (D1 & _)).
apply (ef_NB (xpend x0 (Some c)) st2 L1 BL LS1 g bg idx INV2 Hg2 Hidx eq_refl k0 Hk0). rewrite <- D1. exact Es0. }
split; [exact TOPc|]. split; [| split].
-
intros HT. unfold real_off. change (s_slots (strip st2) !! c) with (s_slots st2 !! c). rewrite SL2.
change (get_meta_rec (strip st2) g) with (MR st2 g). fold stride. fold slack.
unfold enf_raw. change (c_mmap_counter (s_ctx (strip st2))) with ctr. rewrite H1c.
unfold TOP in HT. apply Bool.negb_true_iff in HT. apply Z.eqb_neq in HT.
destruct (s_slots st !! c) as [[g0 i0]|] eqn:Es0.
+
replace (new_top_slot (strip st) (strip st2) c) with false.
2:{ unfold new_top_slot. change (s_slots (strip st) !! c) with (s_slots st !! c). rewrite Es0. rewrite andb_false_r. reflexivity. }
pose proof (S0 c (g0, i0) Es0) as Es2. pose proof (eq_trans (eq_sym SL2) Es2) as X. inversion X. subst g0 i0. clear X.
pose proof (proj2 (proj2 GA) c g idx Es0 (proj1 (TOPT c g idx Es0) HT) NLc) as Bc.
assert (CC : forall k, 1 <= k <= 3 -> cell_read (get_shadow st2 (fst c)) (snd c - k) = cell_read (get_shadow st (fst c)) (snd c - k)).
{ intros k Hk. apply (C0 c k C16 Hk). right. exact NH2. }
destruct (hdr !! c) as [q|].
* first [ sf_destruct 4%nat Bc as (v3 & K3 & NZ3 & R3) K2 K1 Rq | sf_fb; destruct Bc as ((v3 & K3 & NZ3 & R3) & K2 & K1 & Rq) ].
rewrite (HR1 v3 (byte_of q 0) (byte_of q 1)); [| rewrite CC by lia; exact K3| exact NZ3| rewrite CC by lia; exact K2| rewrite CC by lia; exact K1].
rewrite bytes2_eq by exact Rq. reflexivity.
* symmetry. apply HR0. rewrite CC by lia. exact Bc.
+
replace (new_top_slot (strip st) (strip st2) c) with true.
2:{ unfold new_top_slot. rewrite TOPc. change (s_slots (strip st) !! c) with (s_slots st !! c). rewrite Es0. unfold TOP. symmetry.
rewrite andb_true_r. apply Bool.negb_true_iff. apply Z.eqb_neq. exact HT. }
symmetry. apply HR0. rewrite (C0 c 3 C16 ltac:(lia) ltac:(right; exact NH2)).
pose proof (NEWREG c g idx SL2 HT Es0) as NS.
pose proof (known_noshadow st (fst c) (snd c - 3) NS) as K. unfold known, SHd in K. exact K.
-
intros HB0. unfold TOP. apply Bool.negb_true_iff. apply Z.eqb_neq. intros ML.
pose proof INV' as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ _ _ _ IS' _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & IS' & _) ].
inversion CR' as [|b0 k0 LB0 BL0 C0' CR0 E1 E2]. subst.
destruct C0' as (D1 & D2 & D3). cbn [blk_slot blk_size blk_id fst snd] in D1, D2.
destruct k0 as [[c0 o0] n0]. cbn [bslot bsize fst snd] in D1, D2. subst c0 n0.
pose proof (nested_block_small _ _ _ _ _ INV' c g idx o0 n ltac:(rewrite SLE; exact SL2) ltac:(rewrite MRE; exact ML) ltac:(left; reflexivity)).
lia.
-
assert (TOPE : forall c1, slot_top st' c1 = slot_top st2 c1).
{ intros c1. unfold slot_top. rewrite SLE. destruct (s_slots st2 !! c1) as [[g1 i1]|]; [| reflexivity]. fold (MR st' g1). rewrite MRE. reflexivity. }
assert (H2c : TOP = true -> hdr2 !! c = Some off).
{ intros HT. unfold hdr2. rewrite HT. apply lookup_insert_eq. }
assert (H2o : forall c1 : cptr, c1 <> c -> hdr2 !! c1 = hdr1 !! c1).
{ intros c1 NE. unfold hdr2. destruct TOP; [apply lookup_insert_ne; congruence| reflexivity]. }
assert (H1o : forall c1 : cptr, hdr1 !! c1 = if (existsb (aptr_eqb c1) conts) then Some (cont_q c1)
else if new_top_slot (strip st) (strip st2) c1 then None else hdr !! c1).
{ intros c1. unfold hdr1, hdr_after. fold conts. destruct (in_dec aptr_eq_dec c1 conts) as [I|NI].
- rewrite (mark_conts_lookup_in _ _ _ I). replace (existsb (aptr_eqb c1) conts) with true; [reflexivity|].
symmetry. apply existsb_exists. exists c1. split; [exact I| apply aptr_eqb_refl].
- rewrite (mark_conts_lookup_notin _ _ _ NI). replace (existsb (aptr_eqb c1) conts) with false; [apply prune_lookup|].
symmetry. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (x & Hx & Ex). apply aptr_eqb_eq in Ex. subst x. exact (NI Hx). }
split; [| split].
+   intros c1 q Hq. destruct (aptr_eq_dec c1 c) as [->|NE].
* destruct TOP eqn:ET.
-- rewrite (H2c eq_refl) in Hq. inversion Hq. subst q. lia.
-- unfold hdr2 in Hq. rewrite H1c in Hq. destruct (new_top_slot (strip st) (strip st2) c); [discriminate Hq|]. exact (proj1 GA _ _ Hq).
* rewrite (H2o _ NE), H1o in Hq. destruct (existsb (aptr_eqb c1) conts) eqn:EX.
-- inversion Hq. subst q. apply existsb_exists in EX as (x & Hx & Ex). apply aptr_eqb_eq in Ex. subst x. exact (proj2 (CONTS _ Hx)).
-- destruct (new_top_slot (strip st) (strip st2) c1); [discriminate Hq|]. exact (proj1 GA _ _ Hq).
+   intros b0 [<-|Hb0].
* cbn [blk_slot blk_id blk_addr fst snd]. rewrite TOPE. change (slot_top st2 c) with (slot_top (strip st2) c). rewrite TOPc.
unfold tag. destruct TOP eqn:ET; [| reflexivity].
split; [lia|]. split; [| exact (H2c eq_refl)].
unfold p. apply conc_aadd. pose proof INV' as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ IM' _ IG' IS' _ | sf_fb; destruct sfP_ as (_ & _ & IM' & _ & IG' & IS' & _) ].
first [ pose proof (slot_hosts _ _ _ _ _ INV' c g idx ltac:(rewrite SLE; exact SL2)) as sfP_; sf_destruct 4%nat sfP_ as b1 [a1 Hb1] _ Ec1 | sf_fb; destruct (slot_hosts _ _ _ _ _ INV' c g idx ltac:(rewrite SLE; exact SL2)) as (b1 & [a1 Hb1] & _ & Ec1) ].
destruct (ig_region _ _ _ IG' _ _ Hb1) as (r1 & Hr1 & _). exists r1. apply (f_equal fst) in Ec1. unfold c in Ec1. cbn [fst] in Ec1. unfold c. cbn [fst]. rewrite Ec1. exact Hr1.
* destruct (Forall2_In_l _ _ _ _ CR Hb0) as (k0 & Hk0 & (D1 & D2 & D3)).
first [ pose proof (is_blocks _ _ _ IS _ Hk0) as sfP_; sf_destruct 4%nat sfP_ as g0 i0 Hs0 _ | sf_fb; destruct (is_blocks _ _ _ IS _ Hk0) as (g0 & i0 & Hs0 & _) ]. rewrite <- D1 in Hs0.
pose proof (S0 _ _ Hs0) as Hs2.
assert (NE0 : blk_slot b0 <> c) by (rewrite D1; exact (ef_NB (xpend x0 (Some c)) st2 L1 BL LS1 g bg idx INV2 Hg2 Hidx eq_refl k0 Hk0)).
assert (TE : slot_top st' (blk_slot b0) = slot_top st (blk_slot b0)).
{ rewrite TOPE. unfold slot_top. rewrite Hs2, Hs0. fold (MR st2 g0). fold (MR st g0).
pose proof (TOPT _ _ _ Hs0) as TI.
destruct (Z.eqb_spec (m_maplen (MR st2 g0)) 0), (Z.eqb_spec (m_maplen (MR st g0)) 0); cbn; try reflexivity; exfalso; tauto. }
rewrite TE. pose proof (proj1 (proj2 GA) b0 Hb0) as Eb. destruct (slot_top st (blk_slot b0)); [| exact Eb].
destruct Eb as (E1 & E2 & E3'). split; [exact E1|]. split.
-- rewrite E2. f_equal. symmetry. apply conc_same.
destruct (blk_region _ _ _ _ _ k0 INV Hk0) as (r0 & Hr0 & Kr0). rewrite <- D1 in Hr0. exists r0. split; [exact Hr0|].
rewrite RGE. exact (proj1 GP2 _ _ Hr0 Kr0).
-- rewrite (H2o _ NE0), H1o. replace (existsb (aptr_eqb (blk_slot b0)) conts) with false.
2:{ symmetry. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (x & Hx & Ex). apply aptr_eqb_eq in Ex. subst x.
apply new_containers_in in Hx as (_ & _ & Gs). apply Gs. change (s_groups (strip st2) !! blk_slot b0) with (s_groups st2 !! blk_slot b0).
rewrite D1. first [ pose proof (block_facts (xpend x0 (Some c)) st2 L1 BL LS1 INV2 (bslot k0) (boff k0) (bsize k0) ltac:(destruct k0 as [[? ?] ?]; exact Hk0)) as sfP_; sf_destruct 8%nat sfP_ as m0 bm0 j0 aj0 a0 ar0 ka0 BF0 | sf_fb; destruct (block_facts (xpend x0 (Some c)) st2 L1 BL LS1 INV2 (bslot k0) (boff k0) (bsize k0) ltac:(destruct k0 as [[? ?] ?]; exact Hk0)) as (m0 & bm0 & j0 & aj0 & a0 & ar0 & ka0 & BF0) ]. exact (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF0). }
replace (new_top_slot (strip st) (strip st2) (blk_slot b0)) with false; [exact E3'|].
unfold new_top_slot. change (s_slots (strip st) !! blk_slot b0) with (s_slots st !! blk_slot b0). rewrite Hs0. rewrite andb_false_r. reflexivity.
+   intros c1 g1 i1 Hs1 Hml1 NL1. rewrite SLE in Hs1. change (get_meta_rec st' g1) with (MR st' g1) in Hml1. rewrite MRE in Hml1.
destruct (aptr_eq_dec c1 c) as [->|NE].
*
pose proof (eq_trans (eq_sym SL2) Hs1) as X. inversion X. subst g1 i1. clear X.
assert (HT : TOP = true) by (unfold TOP; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Hml1).
rewrite (H2c HT).
assert (NZ : off <> 0).
{ intros O0. apply NL1. exists ((c, tag), conc st' p, n). split; [left; reflexivity|]. cbn [blk_slot blk_id fst snd]. split; [reflexivity|].
unfold tag. rewrite HT. exact O0. }
destruct (ef_hdr_c (xpend x0 (Some c)) st2 L1 BL LS1 g bg idx n INV2 Hg2 Hidx Hn off ltac:(lia) Hfit) as (R3 & R2 & R1).
rewrite <- Est in R3, R2, R1. fold c in R3, R2, R1.
split; [exists 224; rewrite R3; repeat split; try reflexivity; lia|].
unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r. split; [exact R2|]. split; [exact R1|]. lia.
* pose proof (E3 c1 g1 i1) as E3c.
rewrite (H2o _ NE), H1o.
destruct (existsb (aptr_eqb c1) conts) eqn:EX.
--
apply existsb_exists in EX as (x & Hx & Ex). apply aptr_eqb_eq in Ex. subst x.
eapply HB_cells; [| exact (proj1 (CONTS _ Hx))]. intros k Hk. exact (E3c k Hs1 NE Hk).
-- assert (NI : ~ In c1 conts).
{ intros I. assert (X : existsb (aptr_eqb c1) conts = true) by (apply existsb_exists; exists c1; split; [exact I| apply aptr_eqb_refl]). rewrite EX in X. discriminate X. }
pose proof (NCONT c1 g1 i1 NI Hs1 Hml1) as GC.
pose proof (slot_mod16 _ _ _ _ _ INV2 c1 g1 i1 Hs1) as AL1.
assert (CC : forall k, 1 <= k <= 3 -> cell_read (get_shadow st' (fst c1)) (snd c1 - k) = cell_read (get_shadow st (fst c1)) (snd c1 - k)).
{ intros k Hk. rewrite (E3c k Hs1 NE Hk). exact (C0 c1 k AL1 Hk GC). }
destruct (s_slots st !! c1) as [[g0 i0]|] eqn:Es0.
++
replace (new_top_slot (strip st) (strip st2) c1) with false.
2:{ unfold new_top_slot. change (s_slots (strip st) !! c1) with (s_slots st !! c1). rewrite Es0. rewrite andb_false_r. reflexivity. }
pose proof (S0 c1 (g0, i0) Es0) as Es2. pose proof (eq_trans (eq_sym Hs1) Es2) as X. inversion X. subst g0 i0. clear X.
assert (NL0 : ~ live_at0 LB c1).
{ intros sfH_; first [ sf_destruct 4%nat sfH_ as b2 Hb2 E2 Z2 | sf_fb; destruct sfH_ as (b2 & Hb2 & E2 & Z2) ]. apply NL1. exists b2. split; [right; exact Hb2| auto]. }
pose proof (proj2 (proj2 GA) c1 g1 i1 Es0 (proj1 (TOPT c1 g1 i1 Es0) Hml1) NL0) as Bc.
destruct (hdr !! c1) as [q|].
** eapply HB_cells; [| exact Bc]. exact CC.
** rewrite (CC 3) by lia. exact Bc.
++
replace (new_top_slot (strip st) (strip st2) c1) with true.
2:{ unfold new_top_slot, slot_top. change (s_slots (strip st2) !! c1) with (s_slots st2 !! c1). change (s_slots (strip st) !! c1) with (s_slots st !! c1).
rewrite Hs1, Es0. change (get_meta_rec (strip st2) g1) with (MR st2 g1). symmetry. rewrite andb_true_r. apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hml1. }
rewrite (CC 3) by lia.
pose proof (known_noshadow st (fst c1) (snd c1 - 3) (NEWREG c1 g1 i1 Hs1 Hml1 Es0)) as K. unfold known, SHd in K. exact K.
Qed.
End MALLOC.

Section MALLOC_NONE.
Context {RCEIL : RunCeiling}.
Variables (resv : list (Z * Z)) (st : mstate) (LB : list block) (hdr : gmap cptr Z) (n : Z).
Variables (o o1 : mem) (ans : list Z) (st2 : mstate).
Let t : N := N.succ (s_tick st).
Hypothesis AR : AREACH_from resv st LB.
Hypothesis GA : RGA st hdr LB.
Hypothesis Hn : 0 <= n.
Hypothesis F1 : follow (mrun o (malloc_core full_lay (set_tick t st) n)) ans = Some (o1, (st2, None)).
Hypothesis REGK : forall rid r, s_regions st !! rid = Some r -> exists r', s_regions st2 !! rid = Some r' /\ r_kind r' = r_kind r.
Let hdr1 : gmap cptr Z := hdr_after (strip st) (strip st2) hdr.

#[using="RCEIL resv n o o1 ans t AR GA Hn F1 REGK"] Theorem rga_malloc_none : RGA st2 hdr1 LB.
Proof.
first [ pose proof (areach_inv resv st LB AR) as sfP_; sf_destruct 8%nat sfP_ as L LS BL INV LIVE RESV SEC CR | sf_fb; destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR) ].
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as IR IA IM IL IG IS ISH | sf_fb; destruct sfP_ as (IR & IA & IM & IL & IG & IS & ISH) ].
pose proof (INVL_set_tick x0 st L BL LS t ltac:(unfold t; cbn; lia) INV) as INV0.
pose proof (TF0_tick_new st t (TKS_of _ _ _ _ _ INV) ltac:(unfold t; cbn; lia)) as TF0'.
first [ pose proof (malloc_core_leaf_none (set_tick t st) L BL LS n INV0 TF0' Hn pans_mem pupd_mem pans_mem_range o ans o1 st2 F1) as sfP_; sf_destruct 4%nat sfP_ as L1 LS1 INV2 [GP2 HK2] | sf_fb; destruct (malloc_core_leaf_none (set_tick t st) L BL LS n INV0 TF0' Hn pans_mem pupd_mem pans_mem_range o ans o1 st2 F1) as (L1 & LS1 & INV2 & [GP2 HK2]) ].
pose proof INV2 as sfP_; first [ sf_destruct 7%nat sfP_ as IR2 IA2 IM2 IL2 IG2 IS2 ISH2 | sf_fb; destruct sfP_ as (IR2 & IA2 & IM2 & IL2 & IG2 & IS2 & ISH2) ].
destruct HK2 as [G0 S0 GE0 C0 N0].
assert (TOPT : forall (c1 : cptr) g1 i1, s_slots st !! c1 = Some (g1, i1) -> (m_maplen (MR st2 g1) <> 0 <-> m_maplen (MR st g1) <> 0)).
{ intros c1 g1 i1 Hs1. first [ pose proof (slot_hosts _ _ _ _ _ INV c1 g1 i1 Hs1) as sfP_; sf_destruct 4%nat sfP_ as b1 [ai1 Hb1] _ _ | sf_fb; destruct (slot_hosts _ _ _ _ _ INV c1 g1 i1 Hs1) as (b1 & [ai1 Hb1] & _ & _) ].
destruct (G0 b1 (Some g1) ai1 Hb1) as [ai1' Hb1'].
pose proof (top_iff_base0 _ _ _ _ _ INV b1 g1 (ex_intro _ ai1 Hb1)) as T1.
pose proof (top_iff_base0 _ _ _ _ _ INV2 b1 g1 (ex_intro _ ai1' Hb1')) as T2. tauto. }
assert (NEWREG : forall (c1 : cptr) g1 i1, s_slots st2 !! c1 = Some (g1, i1) -> m_maplen (MR st2 g1) <> 0 -> s_slots st !! c1 = None ->
s_shadow st !! (fst c1) = None).
{ intros c1 g1 i1 Hs1 Hml1 Hn1.
first [ pose proof (slot_hosts _ _ _ _ _ INV2 c1 g1 i1 Hs1) as sfP_; sf_destruct 4%nat sfP_ as b1 Hb1 Hi1 Ec1 | sf_fb; destruct (slot_hosts _ _ _ _ _ INV2 c1 g1 i1 Hs1) as (b1 & Hb1 & Hi1 & Ec1) ].
pose proof (proj1 (top_iff_base0 _ _ _ _ _ INV2 b1 g1 Hb1) Hml1) as B10.
destruct (s_shadow st !! fst c1) as [sh|] eqn:ESH; [| reflexivity]. exfalso.
destruct (ish_dom _ _ ISH _ _ ESH) as (r & Hr & Kr).
destruct (REGK _ _ Hr) as (r' & Hr' & Kr').
destruct (ig_top _ _ _ IG (fst c1) r Hr Kr ltac:(discriminate)) as (T & HT & MT).
destruct HT as [aiT HT]. destruct (G0 _ _ _ HT) as [aiT' HT'].
assert (Eb1 : b1 = (fst c1, 0)) by (rewrite Ec1; cbn [fst]; destruct b1; cbn in B10 |- *; subst; reflexivity).
assert (ET : T = g1) by (apply (hosts_fun st2 (fst c1, 0)); [exists aiT'; exact HT'| rewrite <- Eb1; exact Hb1]). subst T.
pose proof (GE0 _ _ _ HT) as GEO. unfold geo_of in GEO. injection GEO. intros Esc Eml Eli Emm.
assert (ESS : slot_start' (MR st g1) i1 = slot_start' (MR st2 g1) i1).
{ unfold slot_start', get_stride. rewrite Emm, Eli, Eml, Esc. reflexivity. }
pose proof (is_total _ _ _ IS _ _ _ (ex_intro _ aiT HT) ltac:(rewrite <- Eli; exact Hi1)) as TOT.
rewrite ESS, (slot_start'_eq _ _ _ IM2 _ _ _ Hb1), <- Ec1 in TOT. rewrite TOT in Hn1. discriminate Hn1. }
set (conts := new_containers (strip st) (strip st2)) in *.
assert (CONTS : forall c1 : cptr, In c1 conts -> HB st2 c1 (cont_q c1) /\ 0 <= cont_q c1 < 2 ^ 16).
{ intros c1 Hin. apply new_containers_in in Hin as (T1 & Gn & Gs).
change (s_groups (strip st) !! c1) with (s_groups st !! c1) in Gn. change (s_groups (strip st2) !! c1) with (s_groups st2 !! c1) in Gs.
destruct (s_groups st2 !! c1) as [[[g1|] ai1]|] eqn:Eg1; [| exfalso; exact (ig_nometa _ _ _ IG2 _ _ Eg1)| congruence].
unfold slot_top in T1. change (s_slots (strip st2) !! c1) with (s_slots st2 !! c1) in T1.
destruct (s_slots st2 !! c1) as [[p0 i0]|] eqn:Es1; [| discriminate T1]. change (get_meta_rec (strip st2) p0) with (MR st2 p0) in T1.
first [ pose proof (slot_hosts _ _ _ _ _ INV2 c1 p0 i0 Es1) as sfP_; sf_destruct 4%nat sfP_ as bp Hbp Hi0 Ec1 | sf_fb; destruct (slot_hosts _ _ _ _ _ INV2 c1 p0 i0 Es1) as (bp & Hbp & Hi0 & Ec1) ].
assert (NZ : snd c1 <> 0).
{ rewrite Ec1. cbn [snd]. pose proof (sstart0 _ _ _ IM2 _ _ Hbp). pose proof (sstart_mono _ _ _ IG2 _ _ 0 i0 Hbp ltac:(lia)).
destruct (hosts_ok _ _ _ IG2 _ _ Hbp) as (a0 & _ & GO0). pose proof (g_align _ _ _ _ _ _ GO0). unfold UNIT in *. lia. }
first [ pose proof (N0 c1 g1 ai1 Gn Eg1 NZ) as sfP_; sf_destruct 9%nat sfP_ as p0' i0' bp' aip' Es1' Hbp' Hf' _ HBc | sf_fb; destruct (N0 c1 g1 ai1 Gn Eg1 NZ) as (p0' & i0' & bp' & aip' & Es1' & Hbp' & Hf' & _ & HBc) ].
rewrite Es1 in Es1'. inversion Es1'. subst p0' i0'.
pose proof (hosts_inj _ _ _ IM2 _ _ _ (ex_intro _ aip' Hbp') Hbp) as ->.
assert (B0 : snd bp = 0).
{ apply (proj1 (top_iff_base0 _ _ _ _ _ INV2 bp p0 Hbp)). apply Bool.negb_true_iff in T1. apply Z.eqb_neq in T1. exact T1. }
rewrite B0, Z.sub_0_r in HBc. fold (cont_q c1) in HBc. split; [exact HBc|]. exact (proj2 (proj2 (proj2 HBc))). }
assert (NCONT : forall (c1 : cptr) g1 i1, ~ In c1 conts -> s_slots st2 !! c1 = Some (g1, i1) -> m_maplen (MR st2 g1) <> 0 ->
s_groups st !! c1 <> None \/ s_groups st2 !! c1 = None).
{ intros c1 g1 i1 NI Hs1 Hml1. destruct (s_groups st2 !! c1) as [h|] eqn:Eg; [left| right; reflexivity]. intros Gn. apply NI.
apply new_containers_in. split; [| split; [exact Gn| change (s_groups (strip st2) !! c1) with (s_groups st2 !! c1); rewrite Eg; discriminate]].
unfold slot_top. change (s_slots (strip st2) !! c1) with (s_slots st2 !! c1). rewrite Hs1. change (get_meta_rec (strip st2) g1) with (MR st2 g1).
apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hml1. }
assert (H1o : forall c1 : cptr, hdr1 !! c1 = if (existsb (aptr_eqb c1) conts) then Some (cont_q c1)
else if new_top_slot (strip st) (strip st2) c1 then None else hdr !! c1).
{ intros c1. unfold hdr1, hdr_after. fold conts. destruct (in_dec aptr_eq_dec c1 conts) as [I|NI].
- rewrite (mark_conts_lookup_in _ _ _ I). replace (existsb (aptr_eqb c1) conts) with true; [reflexivity|].
symmetry. apply existsb_exists. exists c1. split; [exact I| apply aptr_eqb_refl].
- rewrite (mark_conts_lookup_notin _ _ _ NI). replace (existsb (aptr_eqb c1) conts) with false; [apply prune_lookup|].
symmetry. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (x & Hx & Ex). apply aptr_eqb_eq in Ex. subst x. exact (NI Hx). }
split; [| split].
-   intros c1 q Hq. rewrite H1o in Hq. destruct (existsb (aptr_eqb c1) conts) eqn:EX.
+ inversion Hq. subst q. apply existsb_exists in EX as (x & Hx & Ex). apply aptr_eqb_eq in Ex. subst x. exact (proj2 (CONTS _ Hx)).
+ destruct (new_top_slot (strip st) (strip st2) c1); [discriminate Hq|]. exact (proj1 GA _ _ Hq).
-   intros b0 Hb0.
destruct (Forall2_In_l _ _ _ _ CR Hb0) as (k0 & Hk0 & (D1 & D2 & D3)).
first [ pose proof (is_blocks _ _ _ IS _ Hk0) as sfP_; sf_destruct 4%nat sfP_ as g0 i0 Hs0 _ | sf_fb; destruct (is_blocks _ _ _ IS _ Hk0) as (g0 & i0 & Hs0 & _) ]. rewrite <- D1 in Hs0.
pose proof (S0 _ _ Hs0) as Hs2.
assert (TE : slot_top st2 (blk_slot b0) = slot_top st (blk_slot b0)).
{ unfold slot_top. rewrite Hs2, Hs0. fold (MR st2 g0). fold (MR st g0).
pose proof (TOPT _ _ _ Hs0) as TI.
destruct (Z.eqb_spec (m_maplen (MR st2 g0)) 0), (Z.eqb_spec (m_maplen (MR st g0)) 0); cbn; try reflexivity; exfalso; tauto. }
rewrite TE. pose proof (proj1 (proj2 GA) b0 Hb0) as Eb. destruct (slot_top st (blk_slot b0)); [| exact Eb].
destruct Eb as (E1 & E2 & E3'). split; [exact E1|]. split.
+ rewrite E2. f_equal. symmetry. apply conc_same.
destruct (blk_region _ _ _ _ _ k0 INV Hk0) as (r0 & Hr0 & Kr0). rewrite <- D1 in Hr0. exists r0. split; [exact Hr0|].
exact (proj1 GP2 _ _ Hr0 Kr0).
+ rewrite H1o. replace (existsb (aptr_eqb (blk_slot b0)) conts) with false.
2:{ symmetry. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (x & Hx & Ex). apply aptr_eqb_eq in Ex. subst x.
apply new_containers_in in Hx as (_ & _ & Gs). apply Gs. change (s_groups (strip st2) !! blk_slot b0) with (s_groups st2 !! blk_slot b0).
rewrite D1. first [ pose proof (block_facts x0 st2 L1 BL LS1 INV2 (bslot k0) (boff k0) (bsize k0) ltac:(destruct k0 as [[? ?] ?]; exact Hk0)) as sfP_; sf_destruct 8%nat sfP_ as m0 bm0 j0 aj0 a0 ar0 ka0 BF0 | sf_fb; destruct (block_facts x0 st2 L1 BL LS1 INV2 (bslot k0) (boff k0) (bsize k0) ltac:(destruct k0 as [[? ?] ?]; exact Hk0)) as (m0 & bm0 & j0 & aj0 & a0 & ar0 & ka0 & BF0) ]. exact (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF0). }
replace (new_top_slot (strip st) (strip st2) (blk_slot b0)) with false; [exact E3'|].
unfold new_top_slot. change (s_slots (strip st) !! blk_slot b0) with (s_slots st !! blk_slot b0). rewrite Hs0. rewrite andb_false_r. reflexivity.
-   intros c1 g1 i1 Hs1 Hml1 NL1. change (get_meta_rec st2 g1) with (MR st2 g1) in Hml1.
rewrite H1o.
destruct (existsb (aptr_eqb c1) conts) eqn:EX.
+ apply existsb_exists in EX as (x & Hx & Ex). apply aptr_eqb_eq in Ex. subst x. exact (proj1 (CONTS _ Hx)).
+ assert (NI : ~ In c1 conts).
{ intros I. assert (X : existsb (aptr_eqb c1) conts = true) by (apply existsb_exists; exists c1; split; [exact I| apply aptr_eqb_refl]). rewrite EX in X. discriminate X. }
pose proof (NCONT c1 g1 i1 NI Hs1 Hml1) as GC.
pose proof (slot_mod16 _ _ _ _ _ INV2 c1 g1 i1 Hs1) as AL1.
assert (CC : forall k, 1 <= k <= 3 -> cell_read (get_shadow st2 (fst c1)) (snd c1 - k) = cell_read (get_shadow st (fst c1)) (snd c1 - k)).
{ intros k Hk. exact (C0 c1 k AL1 Hk GC). }
destruct (s_slots st !! c1) as [[g0 i0]|] eqn:Es0.
* replace (new_top_slot (strip st) (strip st2) c1) with false.
2:{ unfold new_top_slot. change (s_slots (strip st) !! c1) with (s_slots st !! c1). rewrite Es0. rewrite andb_false_r. reflexivity. }
pose proof (S0 c1 (g0, i0) Es0) as Es2. pose proof (eq_trans (eq_sym Hs1) Es2) as X. inversion X. subst g0 i0. clear X.
pose proof (proj2 (proj2 GA) c1 g1 i1 Es0 (proj1 (TOPT c1 g1 i1 Es0) Hml1) NL1) as Bc.
destruct (hdr !! c1) as [q|].
-- eapply HB_cells; [| exact Bc]. exact CC.
-- rewrite (CC 3) by lia. exact Bc.
* replace (new_top_slot (strip st) (strip st2) c1) with true.
2:{ unfold new_top_slot, slot_top. change (s_slots (strip st2) !! c1) with (s_slots st2 !! c1). change (s_slots (strip st) !! c1) with (s_slots st !! c1).
rewrite Hs1, Es0. change (get_meta_rec (strip st2) g1) with (MR st2 g1). symmetry. rewrite andb_true_r. apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hml1. }
rewrite (CC 3) by lia.
pose proof (known_noshadow st (fst c1) (snd c1 - 3) (NEWREG c1 g1 i1 Hs1 Hml1 Es0)) as K. unfold known, SHd in K. exact K.
Qed.
End MALLOC_NONE.

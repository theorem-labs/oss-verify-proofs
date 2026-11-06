(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1og X1of
X1q8 X1po X1pv X1pf X1px X1pm X1pj X1pk X1q4 X1pz X1q0 X1q1 X1q2 X1q3
X1qf X1qg X1ql X1pw X1q9 X1qa X1qq X1qr X1qh X1qb X1ph X1q6 X1qc
X1qn X1qo X1qp X1qd X1qe X1qj X1q5 X1pi X1py X1pp X1pq X1pr X1ps X1pt.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section FREE2.
Variables (BLG BLC : list blk).

Definition PostF (J' : jled) (x y : mstate) : Prop := exists rho', JR J' rho' x y.

#[using="Type"] Lemma free_tail_rel BG BC J rho st1G st1C LSG LSC c m bm i :
INVL (xpend x0 (Some c)) st1G (projG J) BG LSG -> INVL (xpend x0 (Some c)) st1C (projC J) BC LSC -> JR J rho st1G st1C ->
hosts st1G bm m -> 0 <= i <= m_last_idx (MR st1G m) -> c = (fst bm, sstart (MR st1G m) i) ->
tbit (m_avail (MR st1G m)) i = false -> tbit (m_freed (MR st1G m)) i = false ->
(0 <= m_sizeclass (MR st1G m) < 48 \/ m_sizeclass (MR st1G m) = 63) ->
jsim J (free_tail dec_slots st1G m i) (free_tail dec_slots st1C m i) PostF.
Proof.
intros INVG INVC R Hm Hi Ec NA NF SC. pose proof (jr_rc _ _ _ _ R) as HRC.
assert (HmC : hosts st1C bm m) by (destruct Hm as [ai H]; exists ai; rewrite (RC_groups _ _ _ _ HRC); exact H).
assert (MRC : forall x, MR st1C x = MR st1G x) by (intros x; unfold MR; apply (RC_MRc _ _ _ _ x HRC)).
unfold free_tail. rewrite !(RC_MRc _ _ _ _ m HRC). fold (MR st1G m).
rewrite !(guard_true 60) by (unfold testbit; rewrite Z.lor_spec; unfold tbit in NA, NF; rewrite NA, NF; reflexivity).
destruct (negb ((m_freed (MR st1G m) =? 0) || (Z.lor (m_freed (MR st1G m)) (m_avail (MR st1G m)) + bit i =? mask_upto (m_last_idx (MR st1G m))))).
{ apply jsim_ret. exists rho. apply JR_upd_meta. exact R. }
match goal with |- jsim _ (nontrivial_free dec_slots FUEL st1G m i ?kg ?bg) (nontrivial_free dec_slots FUEL st1C m i ?kc ?bc) _ =>
apply (jsim_steq J (sbind (nontrivial_free dec_slots FUEL st1G m i kS bS) (KF kg bg)) _ (sbind (nontrivial_free dec_slots FUEL st1C m i kS bS) (KF kc bc)) _);
[apply steq_sym; apply nontrivial_free_nat| apply steq_sym; apply nontrivial_free_nat|]
end.
destruct (ntf_spec2 _ FUEL dec_slots dec_slots (dec_slots_ok _) (dec_slots_ok _) (xpend x0 (Some c)) st1G (projG J) BG LSG m bm i kS bS
INVG Hm Hi ltac:(cbn; rewrite Ec; reflexivity) eq_refl eq_refl ltac:(unfold FUEL; lia) ltac:(unfold FUEL; lia)) as (sG2 & mi & LSG2 & EG & _ & [[RGG SEG] NFG] & RESG).
destruct (ntf_spec2 _ FUEL dec_slots dec_slots (dec_slots_ok _) (dec_slots_ok _) (xpend x0 (Some c)) st1C (projC J) BC LSC m bm i kS bS
INVC HmC ltac:(rewrite MRC; exact Hi) ltac:(cbn; rewrite MRC, Ec; reflexivity) eq_refl eq_refl ltac:(unfold FUEL; lia) ltac:(rewrite MRC; unfold FUEL; lia)) as (sC2 & miC & LSC2 & EC & _ & [[RGC SEC] NFC] & RESC).
pose proof (nontrivial_free_RC rho (j_resvC J) FUEL st1G st1C m i sG2 sC2 mi miC HRC EG EC) as [EMI HRC2]. subst miC.
rewrite EG, EC. cbn [sbind KF kS].
assert (R2 : JR J rho sG2 sC2).
{ assert (IR2 : exists X2 LS2, INVL X2 sG2 (projG J) BG LS2) by (destruct mi as [[base len]|]; [destruct RESG as (r & _ & _ & _ & _ & _ & INV2)|]; eexists _, _; eassumption).
destruct IR2 as (X2 & LS2 & INV2). exact (JR_reinv J rho st1G st1C sG2 sC2 _ X2 R (proj1 INVG) (proj1 INV2) RGG HRC2). }
destruct mi as [[base len]|].
2:{ apply jsim_ret. exists rho. exact R2. }
destruct RESG as (r & B0 & Hr & K & Elen & LEN & INVG2). destruct RESC as (rC & _ & HrC & _ & _ & _ & INVC2).
replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
destruct base as [rid o0]. cbn [fst snd] in *. subst o0.
assert (CG : conc sG2 (rid, 0) = r_base r) by (unfold conc, get_region; cbn [fst snd]; rewrite Hr; lia).
assert (CC : conc sC2 (rid, 0) = rho rid) by (rewrite (RC_conc _ _ _ _ (rid, 0) HRC2); cbn [fst snd]; rewrite Hr; lia).
rewrite CG, CC.
assert (JREL : jev_rel J (EMunmap (r_base r) len) (EMunmap (rho rid) len)).
{ cbn. split; [reflexivity|]. split; [exact (brk_quiet_of _ _ _ (proj1 INVG2))|].
exists (r_len r). split; [exact (jr_group_in _ _ _ _ _ _ R2 Hr K)| right; exact Elen]. }
assert (JCOH : jcoh J (EMunmap (r_base r) len) (EMunmap (rho rid) len)).
{ cbn. exact (coh_munmap _ BG LSG2 J rho sG2 sC2 INVG2 (proj1 INVC2) R2 rid r Hr K). }
apply jsim_vis; [exact JREL| exact JCOH|].
intros uG uC Hu. pose proof (jans_ok_G _ _ _ _ _ Hu) as UG. pose proof (jans_ok_C _ _ _ _ _ Hu) as UC.
cbn [answer_ok] in UG, UC. rewrite UG, UC.
apply jsim_ret. exists rho. cbn [jevent_post].
exact (JR_drop_group J rho sG2 sC2 rid r _ (projG J) _ (projC J) R2 (proj1 INVG2) (proj1 INVC2) Hr K).
Qed.

#[using="Type"] Theorem cfree_rel J rho sG sC LSG LSC c offG nG offC nC :
INVL x0 sG (projG J) BLG LSG -> INVL x0 sC (projC J) BLC LSC -> JR J rho sG sC ->
In ((c, offG), nG) BLG -> In ((c, offC), nC) BLC ->
jsim J (cfree (strip sG) (Some c)) (cfree (strip sC) (Some c)) PostF.
Proof.
intros INVG INVC R HkG HkC. pose proof (jr_rc _ _ _ _ R) as HRC.
destruct (free_prefix sG (projG J) BLG LSG c offG nG INVG HkG) as (m & bm & i & FHG & CEG & STRG & HsG & INVG1 & HmG & HiG & EcG & NAG & NFG & SCG & _).
destruct (free_prefix sC (projC J) BLC LSC c offC nC INVC HkC) as (mC & bmC & iC & FHC & CEC & STRC & HsC & INVC1 & _).
cbn zeta in *.
rewrite (RC_slots _ _ _ _ HRC), HsG in HsC. assert (mC = m /\ iC = i) as [-> ->] by (inversion HsC; auto). clear HsC.
set (st1G := wr16 _ 0 (wr8 _ 255 sG)) in *. set (st1C := wr16 _ 0 (wr8 _ 255 sC)) in *.
assert (R1 : JR J rho st1G st1C) by (apply (JR_layout J rho sG sC); [exact R| exact STRG| exact STRC]).
pose proof (free_tail_rel _ _ J rho st1G st1C LSG LSC c m bm i INVG1 INVC1 R1 HmG HiG EcG NAG NFG SCG) as FT.
pose proof (jsim_prun pz pu pz pu _ _ _ _ tt tt FT) as PR.
pose proof (jsim_strel2 _ _ _ _ _ _ _ _ PR (free_tail_slots_control pz pu st1G m i tt) (free_tail_slots_control pz pu st1C m i tt)) as J2.
rewrite STRG, STRC in J2.
unfold cfree. rewrite !s_slots_strip, HsG, (RC_slots _ _ _ _ HRC), HsG.
eapply jsim_bind; [exact J2|].
intros J' x' y' ([oG xG] & [oC yC] & [rho' R'] & EG & EC). cbn in R', EG, EC. apply jsim_ret. exists rho'.
apply (JR_layout J' rho' xG yC); [exact R'| rewrite strip_strip; symmetry; exact EG| rewrite strip_strip; symmetry; exact EC].
Qed.
End FREE2.

Lemma erase_rebase rho resv {ceil} cs : erase (rebase rho resv ceil cs) = erase cs.
Proof.
unfold erase, rebase. cbn. f_equal. apply map_eq. intros i. rewrite !lookup_fmap, lookup_rebase_regions.
destruct (s_regions cs !! i); reflexivity.
Qed.

Lemma RC_erase rho resv {ceil} sG sC : RC rho resv ceil sG sC -> erase (strip sC) = erase (strip sG).
Proof. intros H. unfold RC in H. rewrite H. apply erase_rebase. Qed.

Lemma JR_init ceilG ceilC resvG resvC : JR (jled_init ceilG ceilC resvG resvC) (fun _ => 0) (minit 0 ceilG resvG) (minit 0 ceilC resvC).
Proof.
constructor; cbn.
- unfold RC, rebase. cbn. unfold strip. cbn. f_equal. all: apply map_eq; intros i; rewrite lookup_rebase_regions, !lookup_empty; reflexivity.
- rewrite map_to_list_empty. cbn. apply Permutation_refl.
- rewrite map_to_list_empty. cbn. apply Permutation_refl.
- intros bG bC l. split; [discriminate|]. intros (rid & r & H & _). rewrite lookup_empty in H. discriminate.
- reflexivity.
Qed.

Definition JSIM (csG csC : mstate) (J : jled) : Prop :=
exists stG stC BLG BLC LSG LSC rho,
strip stG = csG /\ strip stC = csC
/\ INVL x0 stG (projG J) BLG LSG /\ INVL x0 stC (projC J) BLC LSC
/\ map bslot BLG = j_live J /\ map bslot BLC = j_live J
/\ JR J rho stG stC.

Lemma projG_set_live v J : projG (jset_live v J) = set_live v (projG J). Proof. reflexivity. Qed.
Lemma projC_set_live v J : projC (jset_live v J) = set_live v (projC J). Proof. reflexivity. Qed.

Lemma malloc_side st L BL LS n L' x :
INVL x0 st L BL LS -> 0 <= n -> cpath L (cmalloc (strip st) n) L' x ->
exists st', strip st' = fst x /\ ld_live L' = ld_live L /\
match snd x with
| Some c => exists off LS', INVL x0 st' L' (((c, off), n) :: BL) LS' /\ ~ In c (map bslot BL)
| None => exists LS', INVL x0 st' L' BL LS'
end.
Proof.
intros INV Hn CP. destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & RES).
rewrite Hf in Hf2. inversion Hf2. subst x. rewrite HL in RES, LIVE'. exists st'. split; [reflexivity|]. split; [exact LIVE'|]. cbn [fst snd].
destruct rf as [pf|]; destruct rc as [c|]; try (exfalso; exact RES).
- destruct RES as (off & LS' & _ & _ & INV' & NI). exists off, LS'. auto.
- exact RES.
Qed.

Lemma free_side st L BL LS c off n L' x :
INVL x0 st L BL LS -> In ((c, off), n) BL -> cpath L (cfree (strip st) (Some c)) L' x ->
exists st' LS', strip st' = x /\ ld_live L' = ld_live L /\ INVL x0 st' L' (bl_remove c BL) LS'.
Proof.
intros INV Hk CP. destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
rewrite Hf in SF.
destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o' st']|] eqn:FF; [| destruct SF].
destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o' st' INV Hk FF) as (Hf2 & _ & LIVE' & LS' & INV').
rewrite Hf in Hf2. inversion Hf2. subst x. rewrite HL in INV', LIVE'. exists st', LS'. auto.
Qed.

Lemma jsim_malloc_step csG csC J n J' xG xC :
JSIM csG csC J -> 0 <= n -> jcpath J (cmalloc csG n) (cmalloc csC n) J' xG xC ->
JSIM (fst xG) (fst xC) (match snd xG with Some c => jset_live (c :: j_live J') J' | None => J' end)
/\ malloc_post2 J' xG xC.
Proof.
intros (stG & stC & BLG & BLC & LSG & LSC & rho & <- & <- & INVG & INVC & LBG & LBC & R) Hn CP.
pose proof (cmalloc_rel BLG BLC J rho stG stC LSG LSC n ltac:(split; [exact INVG| split; [exact INVC| exact R]]) Hn) as REL.
pose proof (jsim_jcpath _ _ _ _ _ _ _ REL CP) as [ER [rho' R']].
pose proof (jcpath_live _ _ _ _ _ _ CP) as LIVE'.
destruct (malloc_side stG (projG J) BLG LSG n (projG J') xG INVG Hn (jcpath_cpath_G _ _ _ _ _ _ _ REL CP)) as (stG' & EG & _ & RESG).
destruct (malloc_side stC (projC J) BLC LSC n (projC J') xC INVC Hn (jcpath_cpath_C _ _ _ _ _ _ _ REL CP)) as (stC' & EC & _ & RESC).
assert (R'' : JR J' rho' stG' stC') by (apply (proj2 (JR_strip _ _ _ _)); rewrite EG, EC; exact R').
rewrite ER in RESC. destruct xG as [csG' rG]; destruct xC as [csC' rC]. cbn [fst snd] in *. subst rC csG' csC'.
split.
- destruct rG as [c|].
+ destruct RESG as (offG & LSG' & INVG' & NIG). destruct RESC as (offC & LSC' & INVC' & NIC).
exists stG', stC', (((c, offG), n) :: BLG), (((c, offC), n) :: BLC), LSG', LSC', rho'.
split; [reflexivity|]. split; [reflexivity|].
split; [rewrite projG_set_live; apply INVL_set_live; exact INVG'|]. split; [rewrite projC_set_live; apply INVL_set_live; exact INVC'|].
cbn. rewrite LIVE', LBG, LBC. split; [reflexivity|]. split; [reflexivity|].
apply (JR_Jframe J'); [exact R''| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity].
+ destruct RESG as (LSG' & INVG'). destruct RESC as (LSC' & INVC').
exists stG', stC', BLG, BLC, LSG', LSC', rho'. rewrite LIVE'. split; [reflexivity|]. split; [reflexivity|]. repeat (split; [assumption|]). exact R''.
- unfold malloc_post2. cbn [fst snd]. split; [reflexivity|]. split.
+ symmetry. exact (RC_erase _ _ _ _ (jr_rc _ _ _ _ R')).
+ destruct rG as [c|]; [| exact I]. destruct RESG as (offG & LSG' & INVG' & NIG). rewrite LIVE', <- LBG. exact NIG.
Qed.

Lemma jsim_free_step csG csC J c J' csG' csC' :
JSIM csG csC J -> In c (j_live J) -> jcpath J (cfree csG (Some c)) (cfree csC (Some c)) J' csG' csC' ->
JSIM csG' csC' (jset_live (ap_remove c (j_live J')) J') /\ free_post2 J' csG' csC'.
Proof.
intros (stG & stC & BLG & BLC & LSG & LSC & rho & <- & <- & INVG & INVC & LBG & LBC & R) Hc CP.
pose proof Hc as HcC. rewrite <- LBG in Hc. rewrite <- LBC in HcC.
destruct (In_bslot _ _ Hc) as (offG & nG & HkG). destruct (In_bslot _ _ HcC) as (offC & nC & HkC).
pose proof (cfree_rel BLG BLC J rho stG stC LSG LSC c offG nG offC nC INVG INVC R HkG HkC) as REL.
pose proof (jsim_jcpath _ _ _ _ _ _ _ REL CP) as [rho' R'].
pose proof (jcpath_live _ _ _ _ _ _ CP) as LIVE'.
destruct (free_side stG (projG J) BLG LSG c offG nG (projG J') csG' INVG HkG (jcpath_cpath_G _ _ _ _ _ _ _ REL CP)) as (stG' & LSG' & EG & _ & INVG').
destruct (free_side stC (projC J) BLC LSC c offC nC (projC J') csC' INVC HkC (jcpath_cpath_C _ _ _ _ _ _ _ REL CP)) as (stC' & LSC' & EC & _ & INVC').
assert (R'' : JR J' rho' stG' stC') by (apply (proj2 (JR_strip _ _ _ _)); rewrite EG, EC; exact R').
split.
- exists stG', stC', (bl_remove c BLG), (bl_remove c BLC), LSG', LSC', rho'.
split; [exact EG|]. split; [exact EC|].
split; [rewrite projG_set_live; apply INVL_set_live; exact INVG'|]. split; [rewrite projC_set_live; apply INVL_set_live; exact INVC'|].
cbn. rewrite LIVE', !bl_remove_map, LBG, LBC. split; [reflexivity|]. split; [reflexivity|].
apply (JR_Jframe J'); [exact R''| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity].
- unfold free_post2. rewrite <- EG, <- EC. symmetry. exact (RC_erase _ _ _ _ (jr_rc _ _ _ _ R'')).
Qed.

Theorem jcreach_sim csG csC J : jcreach csG csC J -> JSIM csG csC J.
Proof.
induction 1 as [ceilG ceilC resvG resvC HcG HcC|csG csC J n J' xG xC CR IH Hn CP|csG csC J c J' csG' csC' CR IH Hc CP].
- exists (minit 0 ceilG resvG), (minit 0 ceilC resvC), [], [], (fun _ => []), (fun _ => []), (fun _ => 0).
split; [reflexivity|]. split; [reflexivity|]. split; [apply INVL_init; [lia| exact HcG]|]. split; [apply INVL_init; [lia| exact HcC]|].
split; [reflexivity|]. split; [reflexivity|]. apply JR_init.
- exact (proj1 (jsim_malloc_step csG csC J n J' xG xC IH Hn CP)).
- exact (proj1 (jsim_free_step csG csC J c J' csG' csC' IH Hc CP)).
Qed.

Theorem cmalloc_contract2_proof : forall csG csC J n,
jcreach csG csC J -> 0 <= n -> jtree_ok J (cmalloc csG n) (cmalloc csC n) malloc_post2.
Proof.
intros csG csC J n CR Hn. pose proof (jcreach_sim csG csC J CR) as JS.
pose proof JS as (stG & stC & BLG & BLC & LSG & LSC & rho & EG & EC & INVG & INVC & LBG & LBC & R).
apply (jtree_ok_paths _ _ J (fun _ _ _ => True) malloc_post2).
- rewrite <- EG, <- EC. eapply (jsim_jtree_ok _ _ J _ (fun _ _ => True)).
+ exact (cmalloc_rel BLG BLC J rho stG stC LSG LSC n ltac:(split; [exact INVG| split; [exact INVC| exact R]]) Hn).
+ eapply (ptree_strel (malloc_control pans0 pupd0 pans0_range stG n tt)); [intros; exact I|].
eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range (malloc stG n) (projG J) _ tt (malloc_INVL stG (projG J) BLG LSG n INVG Hn)).
+ intros; exact I.
- intros J' x y CP. exact (proj2 (jsim_malloc_step csG csC J n J' x y JS Hn CP)).
Qed.

Theorem cfree_contract2_proof : forall csG csC J c,
jcreach csG csC J -> In c (j_live J) -> jtree_ok J (cfree csG (Some c)) (cfree csC (Some c)) free_post2.
Proof.
intros csG csC J c CR Hc. pose proof (jcreach_sim csG csC J CR) as JS.
pose proof JS as (stG & stC & BLG & BLC & LSG & LSC & rho & EG & EC & INVG & INVC & LBG & LBC & R).
pose proof Hc as HcG. pose proof Hc as HcC. rewrite <- LBG in HcG. rewrite <- LBC in HcC.
destruct (In_bslot _ _ HcG) as (offG & nG & HkG). destruct (In_bslot _ _ HcC) as (offC & nC & HkC).
apply (jtree_ok_paths _ _ J (fun _ _ _ => True) free_post2).
- rewrite <- EG, <- EC. eapply (jsim_jtree_ok _ _ J _ (fun _ _ => True)).
+ exact (cfree_rel BLG BLC J rho stG stC LSG LSC c offG nG offC nC INVG INVC R HkG HkC).
+ eapply (ptree_strel (free_control pans0 pupd0 stG (aadd c (UNIT * offG)) c tt (INVL_hdr_ok pans0 pupd0 stG (projG J) BLG LSG c offG nG INVG HkG))); [intros; exact I|].
eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range _ (projG J) _ tt (free_INVL_closed stG (projG J) BLG LSG c offG nG INVG HkG)).
+ intros; exact I.
- intros J' x y CP. exact (proj2 (jsim_free_step csG csC J c J' x y JS Hc CP)).
Qed.

Check (cmalloc_contract2_proof : forall csG csC J n,
jcreach csG csC J -> 0 <= n -> jtree_ok J (cmalloc csG n) (cmalloc csC n) malloc_post2).
Check (cfree_contract2_proof : forall csG csC J c,
jcreach csG csC J -> In c (j_live J) -> jtree_ok J (cfree csG (Some c)) (cfree csC (Some c)) free_post2).

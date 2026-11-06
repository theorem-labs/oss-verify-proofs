(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import KInvS8 MI_InvS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import MI_Kit MI_Arith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import MI_ListS8 MI_ExtS8 MI_Ext2S8 MI_GeomS8 MI_Pres4S8 MI_WFree2S8 MI_WNtf2S8 KStepS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import DecodeS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Heap Require Import HeTreeS8 HeAbsS8 HeEmptyS8 HeWNtfS8 HeMetaS8.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HMWFREE.
Context {RUNp : RunP}.

Record FREL (cs : mstate) (LS : lhead -> list aptr) (cs' : mstate) (u : Z) (nu : nat) : Prop := mkFREL {
  fr_einv : EINV cs';
  fr_hosts : forall b m, hosts cs' b m -> hosts cs b m /\ GEOM (MR cs' m) = GEOM (MR cs m);
  fr_slots : forall s v, s_slots cs' !! s = Some v -> s_slots cs !! s = Some v;
  fr_regions : (s_regions cs' = s_regions cs /\ u = 0 /\ nu = 0%nat)
      \/ (exists rid r, s_regions cs !! rid = Some r /\ r_kind r = RKGroup /\ s_regions cs' = delete rid (s_regions cs)
                        /\ u = mmap_len (r_len r) /\ nu = 1%nat);
  fr_nmeta : nmeta cs' = nmeta cs;
  fr_free : exists LS', lists_ok cs' LS' /\ Z.of_nat (length (LS' LFree)) + ngrp cs' = Z.of_nat (length (LS LFree)) + ngrp cs
      /\ (forall m, In m (LS LFree) -> In m (LS' LFree)) /\ (forall b m, hosts cs b m -> hosts cs' b m \/ In m (LS' LFree));
  fr_keys : forall m, s_metas cs' !! m <> None <-> s_metas cs !! m <> None;
  fr_ctx : CTXM cs cs'
}.

Lemma FREL_strip cs LS s u nu : FREL cs LS s u nu -> FREL cs LS (strip s) u nu.
Proof.
  intros [E H S R N F K C]. constructor.
  - destruct E as [E1 E2]. constructor; [exact E1| exact E2].
  - exact H.
  - exact S.
  - exact R.
  - exact N.
  - destruct F as (LS' & LO & CNT & FL & BK). exists LS'. split; [| split; [exact CNT| split; [exact FL| exact BK]]].
    apply (lists_ok_links s (strip s) LS' LO); [intros h; destruct h; reflexivity| intros x; split; reflexivity].
  - exact K.
  - destruct C; constructor; assumption.
Qed.

Lemma CASC_init cs L BL LS sc : INVC x0 cs L BL LS -> CASC cs LS cs LS [] sc.
Proof.
  intros INV. pose proof INV as (IR & IA & IM & IL & IG & IS).
  assert (LO : lists_ok cs LS) by (destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; auto).
  constructor.
  - exact LO.
  - reflexivity.
  - constructor; auto.
  - intros b m Hb. split; [exact Hb|]. split; reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn. lia.
  - intros z [].
  - constructor.
  - apply ctxm_refl.
  - intros s0 p j H. exact H.
  - intros sc' m Hm. exact (proj2 (il_active _ _ IL sc' m Hm)).
  - intros m Hm [b [ai Hb]]. pose proof (il_free _ _ IL m Hm) as F. destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Hm' & Hmem & _).
    cbn in Hm'. injection Hm' as <-. rewrite F in Hmem. discriminate.
  - intros m. tauto.
  - intros b m Hb. left. exact Hb.
Qed.

Lemma EINV_drop rid s : EINV s -> EINV (drop_region rid s).
Proof. intros [E1 E2]. constructor; [exact E1| exact E2]. Qed.

Theorem cfree_walk cs L BL LS c off n :
  INVC x0 cs L BL LS -> EINV cs -> In ((c, off), n) BL ->
  apw unmap_len (cfree cs (Some c)) 0 0 (fun u nu cs' => FREL cs LS cs' u nu).
Proof.
  intros INV E0 Hk. pose proof INV as (IR & IA & IM & IL & IG & IS).
  assert (LO : lists_ok cs LS) by (destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; auto).
  destruct (is_blocks _ _ _ IS _ Hk) as (g & idx & Hsl & _). cbn [bslot fst] in Hsl.
  destruct (is_valid _ _ _ IS _ _ _ Hsl) as (LV & Hidx & Ec). destruct LV as [bg Hg].
  destruct (g0_facts cs L BL LS INV bg g Hg) as (ai & Hg' & GO).
  pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_sc _ _ _ _ _ _ GO) as SC.
  pose proof (g_masks _ _ _ _ _ _ GO) as (Mav & Mfr & _).
  unfold cfree. rewrite Hsl. eapply apw_bind; [| intros u nu st1 H1; apply apw_ret; apply FREL_strip; exact H1].
  unfold free_tail. fold (MR cs g).
  apply apw_guard. intros G60. apply Bool.negb_true_iff in G60.
  set (mask := Z.lor (m_freed (MR cs g)) (m_avail (MR cs g))) in *.
  assert (MF : mask = fmask (MR cs g)) by (unfold mask, fmask; apply Z.lor_comm).
  assert (MN : 0 <= mask) by (unfold mask; apply Z.lor_nonneg; auto).
  assert (Hbit : Z.testbit (fmask (MR cs g)) idx = false) by (rewrite <- MF; exact G60).
  assert (MADD : mask + bit idx = Z.lor mask (bit idx)) by (rewrite bit_eq; apply add_bit_lor; [exact MN| lia| exact G60]).
  destruct (negb ((m_freed (MR cs g) =? 0) || (mask + bit idx =? mask_upto (m_last_idx (MR cs g))))) eqn:FAST.
  -
    apply apw_ret. apply Bool.negb_true_iff, Bool.orb_false_iff in FAST as [FR0 NALL].
    apply Z.eqb_neq in FR0. apply Z.eqb_neq in NALL.
    set (cs' := upd_meta g _ cs).
    assert (Rg : MR cs' g = m_set_freed (m_freed (MR cs g) + bit idx) (MR cs g)) by (unfold cs', MR; rewrite get_meta_rec_upd_same; reflexivity).
    assert (Ro : forall x, x <> g -> MR cs' x = MR cs x) by (intros x NE; unfold cs', MR; rewrite get_meta_rec_upd_other by exact NE; reflexivity).
    assert (HO : forall b m, hosts cs' b m <-> hosts cs b m) by (intros; apply hosts_ext; reflexivity).
    assert (FG : fmask (MR cs' g) = Z.lor (fmask (MR cs g)) (bit idx)).
    { rewrite Rg. unfold fmask, m_set_freed. cbn.
      assert (Fb : Z.testbit (m_freed (MR cs g)) idx = false).
      { pose proof G60 as G6. unfold mask, testbit in G6. rewrite Z.lor_spec in G6. apply Bool.orb_false_iff in G6. tauto. }
      rewrite (add_bit_lor (m_freed (MR cs g)) idx Mfr ltac:(lia) Fb), <- bit_eq. rewrite Z.lor_assoc. reflexivity. }
    assert (Pg : s_metas cs !! g <> None) by exact (g_present _ _ _ _ _ _ GO).
    constructor.
    + apply (EINV_after cs cs' L BL LS (fun _ => False) INV E0); [| intros m1 m2 []].
      intros b m Hb He. apply HO in Hb. split; [split; [exact Hb|]|].
      * destruct (aptr_eqb_spec m g) as [->|NE]; [rewrite Rg; reflexivity| rewrite (Ro m NE); reflexivity].
      * left. destruct (aptr_eqb_spec m g) as [->|NE].
        -- exfalso. unfold gempty in He. rewrite FG in He. rewrite Rg in He. cbn [m_last_idx m_set_freed] in He.
           rewrite <- MF, <- MADD in He. exact (NALL He).
        -- unfold gempty in He |- *. rewrite (Ro m NE) in He. exact He.
    + intros b m Hb. apply HO in Hb. split; [exact Hb|].
      destruct (aptr_eqb_spec m g) as [->|NE]; [rewrite Rg; reflexivity| rewrite (Ro m NE); reflexivity].
    + intros s0 v H. exact H.
    + left. split; [reflexivity| split; reflexivity].
    + unfold cs'. apply nmeta_upd_present. exact Pg.
    + exists LS. split; [| split; [reflexivity| split; [intros m Hm; exact Hm| intros b m Hb; left; apply HO; exact Hb]]].
      apply (lists_ok_links cs cs' LS LO); [intros h; unfold cs'; apply get_head_upd_meta|].
      intros x. destruct (aptr_eqb_spec x g) as [->|NE]; [rewrite Rg; split; reflexivity| rewrite (Ro x NE); split; reflexivity].
    + intros m. unfold cs'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec m g) as [->|NE]; [| tauto].
      split; [intros _; exact Pg| intros _; discriminate].
    + constructor; reflexivity.
  -
    apply (ntf_walk cs L BL LS INV _ unmap_len FUEL cs LS [] g bg idx _ (ret cs) 0 0%nat _ (CASC_init cs L BL LS _ INV) Hg eq_refl Hg Hidx Hbit).
    + unfold FUEL. lia.
    + pose proof SC as [[Hs _]|(Hs & _)]; unfold FUEL; lia.
    + intros st2 mi NP. destruct NP as [(LS2 & LO2 & CNT2 & _ & FL2 & BK2) KY2 _ _ NH (so & NE) NR NMI NM NC NS].
      assert (BK2' : forall b m, hosts cs b m -> hosts st2 b m \/ In m (LS2 LFree)) by (intros b m Hb; destruct (BK2 b m Hb) as [H|[H|[]]]; auto).
      assert (EI2 : EINV st2).
      { apply (EINV_after cs st2 L BL LS (fun m => so = Some m) INV E0); [| intros m1 m2 -> E; injection E; auto].
        intros b m Hb He. destruct (NH b m Hb) as [Hb0 Gm]. split; [split; assumption|].
        destruct (NE b m Hb He) as [C|(C1 & C2 & C3 & C4)]; [left; exact C| right; auto]. }
      assert (FR2 : forall u nu, (s_regions st2 = s_regions cs /\ u = 0 /\ nu = 0%nat) -> FREL cs LS st2 u nu).
      { intros u nu RR. constructor.
        - exact EI2.
        - exact NH.
        - intros s0 [p0 j0] H. exact (NS s0 p0 j0 H).
        - left. exact RR.
        - exact NM.
        - exists LS2. split; [exact LO2|]. cbn [length] in CNT2. split; [lia| split; [exact FL2| exact BK2']].
        - exact KY2.
        - exact NC. }
      destruct mi as [[base len]|].
      * destruct NMI as (B0 & r & Hr & Hkd & Hlen & Hpos).
        destruct (negb (len =? 0)) eqn:LZ; [| apply Bool.negb_false_iff, Z.eqb_eq in LZ; lia].
        apply apw_vis. intros ru. destruct (munmap_answer_ok ru); [| apply apw_bad].
        apply apw_ret. cbn [unmap_len]. constructor.
        -- apply EINV_drop. exact EI2.
        -- intros b m Hb. exact (NH b m Hb).
        -- intros s0 [p0 j0] H. exact (NS s0 p0 j0 H).
        -- right. exists (fst base), r. split; [exact Hr|]. split; [exact Hkd|]. split.
           ++ unfold drop_region. cbn. rewrite NR. reflexivity.
           ++ split; [lia| reflexivity].
        -- exact NM.
        -- exists LS2. split; [apply (lists_ok_links st2 _ LS2 LO2); [intros h; destruct h; reflexivity| intros x; split; reflexivity]|].
           cbn [length] in CNT2. unfold ngrp in *. cbn. split; [lia| split; [exact FL2| exact BK2']].
        -- exact KY2.
        -- destruct NC; constructor; assumption.
      * apply apw_ret. apply FR2. split; [exact NR| split; reflexivity].
Qed.

Lemma MARITH_frel cs LS cs' u nu : CURI cs -> MARITH cs -> FREL cs LS cs' u nu ->
  MARITH cs' /\ Phi cs' = Phi cs - u /\ Psi cs' = Psi cs - Z.of_nat nu.
Proof.
  intros CU [M1 M2 M3 M4 M5 M6] [_ _ _ R N _ _ [C1 C2 C3 C4 C5]].
  assert (NA : nareas cs' = nareas cs) by (unfold nareas; rewrite C5; reflexivity).
  assert (RS : forall f, (forall r, r_kind r = RKGroup -> f r = 0) -> regsum f cs' = regsum f cs).
  { intros f Hf. destruct R as [(E & _)|(rid & r & Hr & Hk & E & _)]; [exact (regsum_ext f cs cs' E)|].
    rewrite (regsum_delete f cs cs' rid r Hr E), (Hf r Hk). lia. }
  split; [| split].
  - constructor.
    + rewrite C3. exact M1.
    + rewrite C3, C2, NA. exact M2.
    + rewrite C3, NA. exact M3.
    + rewrite C3, (RS metalen); [exact M4|]. intros r Hk. unfold metalen. rewrite Hk. reflexivity.
    + intros rid r Hr Hk. rewrite NA. apply (M5 rid r); [| exact Hk].
      destruct R as [(E & _)|(rid' & r' & _ & _ & E & _)]; rewrite E in Hr; [exact Hr|].
      destruct (decide (rid = rid')) as [->|NE]; [rewrite lookup_delete_eq in Hr; discriminate| rewrite lookup_delete_ne in Hr by congruence; exact Hr].
    + rewrite NA, C1, N. exact M6.
  - rewrite !Phi_regsum. unfold brk_dead_w. rewrite C4.
    destruct R as [(E & -> & _)|(rid & r & Hr & Hk & E & -> & _)]; [rewrite (regsum_ext wreg cs cs' E); lia|].
    rewrite (regsum_delete wreg cs cs' rid r Hr E). unfold wreg at 2. rewrite Hk. lia.
  - unfold Psi. rewrite NA, !ngreg_regsum.
    destruct R as [(E & _ & ->)|(rid & r & Hr & Hk & E & _ & ->)]; [rewrite (regsum_ext isgreg cs cs' E); lia|].
    rewrite (regsum_delete isgreg cs cs' rid r Hr E). unfold isgreg at 2. rewrite Hk. lia.
Qed.

Theorem free_end cs L BL LS cs' u nu L' BL' LS' SZ :
  INVC x0 cs L BL LS -> NLK cs -> L63 cs SZ -> MARITH cs ->
  FREL cs LS cs' u nu -> INVC x0 cs' L' BL' LS' ->
  EINV cs' /\ NLK cs' /\ (forall SZ', (forall e, In e SZ' -> In e SZ) -> L63 cs' SZ') /\ MARITH cs'
  /\ Phi cs' = Phi cs - u /\ Psi cs' = Psi cs - Z.of_nat nu /\ nmeta cs' = nmeta cs
  /\ (forall b m, hosts cs' b m -> hosts cs b m /\ GEOM (MR cs' m) = GEOM (MR cs m)).
Proof.
  intros INV NL0 L630 MA FR INV'. pose proof FR as [E H S R N (LS2 & LO2 & _ & FL2 & BK2) KY C].
  pose proof INV as (IR & IA & IM & IL & IG & IS). pose proof INV' as (IR' & IA' & IM' & IL' & IG' & IS').
  destruct (MARITH_frel cs LS cs' u nu (CURI_of _ _ _ _ _ INV) MA FR) as (MA' & PH & PS).
  split; [exact E|]. split.
  { intros m Pm'. apply KY in Pm'.
    assert (HOSTED : forall b, hosts cs b m -> m_mem (MR cs' m) <> None \/ m_next (MR cs' m) <> None).
    { intros b Hb. destruct (BK2 b m Hb) as [Hb'|Hf].
      - left. rewrite (hosts_mem x0 cs' LS' IM' b m Hb'). discriminate.
      - right. apply (proj1 (proj1 (lo_link _ _ LO2 m))). exists LFree. exact Hf. }
    destruct (NL0 m Pm') as [Mm|Nx].
    - destruct (m_mem (MR cs m)) as [b|] eqn:Em; [| exfalso; exact (Mm eq_refl)].
      destruct (im_group _ _ _ IM m b Em) as [Hb|[]]. exact (HOSTED b Hb).
    - destruct (proj2 (proj1 (il_link _ _ IL m)) Nx) as [h Hh]. destruct h as [sc|].
      + destruct (il_active _ _ IL sc m Hh) as (_ & [b Hb] & _). exact (HOSTED b Hb).
      + right. apply (proj1 (proj1 (lo_link _ _ LO2 m))). exists LFree. exact (FL2 m Hh). }
  split.
  { intros SZ' SUB q k m i Hin Hsl Hsc. pose proof (S q (m, i) Hsl) as Hsl0.
    destruct (is_valid _ _ _ IS' q m i Hsl) as ([b Hb'] & _ & Eq). destruct (H b m Hb') as [Hb G].
    apply GEOM_eq in G as (_ & _ & _ & Gs & _). rewrite Gs in Hsc.
    destruct (L630 q k m i (SUB _ Hin) Hsl0 Hsc) as (r & Hr & Hk & Hl). exists r. split; [| split; [exact Hk| exact Hl]].
    destruct R as [(ER & _)|(rid & r' & Hr' & Hk' & ER & _)]; rewrite ER; [exact Hr|].
    destruct (decide (fst q = rid)) as [Ef|NE]; [| rewrite lookup_delete_ne by congruence; exact Hr].
    exfalso. pose proof Hb' as [ai Hgb]. destruct (ig_region _ _ _ IG' b _ Hgb) as (r2 & Hr2 & _).
    rewrite (slot_start'_eq x0 cs' LS' IM' m b i Hb') in Eq. assert (Efb : fst q = fst b) by (rewrite Eq; reflexivity).
    rewrite <- Efb, ER, Ef, lookup_delete_eq in Hr2. discriminate. }
  split; [exact MA'|]. split; [exact PH|]. split; [exact PS|]. split; [exact N| exact H].
Qed.

End HMWFREE.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRingOps OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfFree.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AXG_ntfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Lemma deq_model : forall X U s g i am, Inv X (Some (g, i)) U s -> usedX X s g am ->
  Z.lor (am_freed am) (am_avail am) + bit i = ones (am_last am) ->
  itok (deq_part g (am_sc am) am s) (fun r => let s1 := snd r in
        Inv (g :: X) None (fun c => U c + contrib X s c g) s1 /\ MT s1 g = Some (MUsed (am_set_links None None am)) /\
        st_usage s1 = st_usage s /\ st_regions s1 = st_regions s /\ corr X s s1 /\
        (forall q a, usedX (g :: X) s1 q a -> exists a0, usedX X s q a0 /\ ceq a a0) /\
        (forall q, (forall a, usedX X s q a -> am_sc a <> am_sc am) -> q <> g -> MT s1 q = MT s q) /\ ub_same s s1).
Proof.
  intros X U s g i am HI Hu Hmask.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. pose proof (MT_Some_In_keys _ _ _ Mg) as Kg.
  destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & Hfr & Hal). pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
  pose proof (inv_groups HI g am Hu) as G. pose proof G as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
  assert (Hscr : am_sc am = 63 \/ 0 <= am_sc am < 48) by (destruct Gcl as [(C & _) | (C & _)]; [left | right]; exact C).
  pose proof (frameless_of_mask X U s g i am HI Hu Hmask) as Hnofr.
  set (U1 := fun c => U c + contrib X s c g).
  set (sc := am_sc am) in *.
  unfold deq_part.
    destruct (am_next am) as [nx|] eqn:Enx.
      - assert (Hsc : 0 <= sc < 48).
        { destruct Hscr as [H63|H]; [|exact H]. exfalso. destruct (inv_rings HI) as (_ & _ & D). destruct (D g am Hu H63) as [_ E]. rewrite Enx in E. discriminate. }
        mbinds. apply itok_massert; [apply Z.ltb_lt; lia|]. msimp. mbinds. apply itok_get_head. msimp.
        change (nth (Z.to_nat sc) (st_active s) None) with (active_hd s sc).
        mbinds. eapply (dequeue_exempt_spec X (Some (g, i)) U s sc g am); [exact HI | exact Hsc | exact Hu | reflexivity | rewrite Enx; intros E; discriminate | exact Hnofr | intros p j E; injection E; auto |].
        intros s1 HI1 Sb1 Mg1 EH1 Mo1 Bwd1 Hk1 Hnew1 UB1. msimp. mbinds. apply itok_get_head. msimp.
        change (nth (Z.to_nat sc) (st_active s1) None) with (active_hd s1 sc).
        pose proof Sb1 as (_&_&_&_&_&_&_&_&_&Eus1&_&_&_&_&Erg1&_&EK1).
        assert (C1 : forall q a, usedX (g :: X) s1 q a -> exists a0, usedX X s q a0 /\ ceq a a0).
        { intros q a Hq. destruct (Bwd1 q a Hq) as (_ & a0 & H0 & E). exists a0. split; [exact H0 | exact (ceq_strip _ _ E)]. }
        assert (Cr1 : corr X s s1).
        { intros q a Hq. destruct (sptr_eq_dec q g) as [->|Hne].
          - pose proof (usedX_MT _ _ _ _ Hq) as [M _]. rewrite Mg1 in M. injection M as <-. exists am.
            split; [exact Hu|]. destruct am; unfold ceq; cbn; auto.
          - apply C1. apply usedX_cons; assumption. }
        assert (POST1 : forall s1', Inv (g :: X) None U1 s1' ->
                  (exists h x, s1' = upd_meta h x s1 /\ h <> g /\
                     (exists ah ah', x = MUsed ah' /\ usedX (g :: X) s1 h ah /\ am_sc ah = sc /\ ceq ah' ah /\
                        blocks_of h ah' = blocks_of h ah)) \/ s1' = s1 ->
                  let s1 := s1' in
                  Inv (g :: X) None U1 s1 /\ MT s1 g = Some (MUsed (am_set_links None None am)) /\
                  st_usage s1 = st_usage s /\ st_regions s1 = st_regions s /\ corr X s s1 /\
                  (forall q a, usedX (g :: X) s1 q a -> exists a0, usedX X s q a0 /\ ceq a a0) /\
                  (forall q, (forall a, usedX X s q a -> am_sc a <> sc) -> q <> g -> MT s1 q = MT s q) /\ ub_same s s1).
        { intros s1' HI1' Hcase. cbn zeta. destruct Hcase as [(h & x & -> & Hhg & ah & ah' & -> & Uh & Sh & Ceh & Ebl) | ->].
          - split; [exact HI1'|]. split; [rewrite MT_upd_other by (intros E; exact (Hhg (eq_sym E))); exact Mg1|].
            split; [exact Eus1|]. split; [exact Erg1|].
            assert (C2 : forall q a, usedX (g :: X) (upd_meta h (MUsed ah') s1) q a ->
                         exists a0, usedX X s q a0 /\ ceq a a0).
            { intros q a Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
              - injection E as <-. destruct (C1 h ah Uh) as (a0 & H0 & C0). exists a0. split; [exact H0 | exact (ceq_trans _ _ _ Ceh C0)].
              - apply C1. exact Hq. }
            split.
            { intros q a Hq. destruct (sptr_eq_dec q g) as [->|Hne].
              - pose proof (usedX_MT _ _ _ _ Hq) as [M _]. rewrite MT_upd_other in M by (intros E; exact (Hhg (eq_sym E))).
                rewrite Mg1 in M. injection M as <-. exists am. split; [exact Hu|]. destruct am; unfold ceq; cbn; auto.
              - apply C2. apply usedX_cons; assumption. }
            split; [exact C2|]. split.
            { intros q Hq Hqg. destruct (sptr_eq_dec q h) as [->|Hqh].
              + exfalso. destruct (Bwd1 h ah Uh) as (_ & a0 & H0 & E0). pose proof (strip_fields _ _ E0) as (_&_&_&_&Es&_).
                apply (Hq a0 H0). congruence.
              + rewrite MT_upd_other by exact Hqh. apply Mo1; assumption. }
            eapply ub_same_trans; [exact UB1|]. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ Uh))|].
            rewrite (proj1 (usedX_MT _ _ _ _ Uh)). cbn. exact Ebl.
          - split; [exact HI1'|]. split; [exact Mg1|]. split; [exact Eus1|]. split; [exact Erg1|]. split; [exact Cr1|]. split; [exact C1|]. split; [exact Mo1 | exact UB1]. }
        destruct (osptr_eqb (active_hd s sc) (Some g)) eqn:Ehd.
        + apply osptr_eqb_eq in Ehd. destruct (Hnew1 Ehd) as [Hnone | (h & ah & Hh & Hhg & Uh & Sh & Avh)].
          * rewrite Hnone. apply itok_ret. cbn [snd]. apply (POST1 s1 HI1). right. reflexivity.
          * rewrite Hh. mbinds. eapply activate_group_spec; [exact HI1 | exact Hsc | exact Uh | exact Sh | exact Hh | exact Avh |].
            intros mk s2 HI2 Es2. msimp. apply itok_ret. cbn [snd]. apply (POST1 s2 HI2). left.
            eexists h, _. split; [exact Es2|]. split; [exact Hhg|]. eexists ah, _. split; [reflexivity|]. split; [exact Uh|]. split; [exact Sh|].
            split; [destruct ah; unfold ceq; cbn; auto|]. apply blocks_of_ext; destruct ah; reflexivity.
        + apply itok_ret. cbn [snd]. apply (POST1 s1 HI1). right. reflexivity.
      - apply itok_ret. cbn [snd].
        assert (Hp : am_prev am = None).
        { destruct Hscr as [H63|Hsc]; [destruct (inv_rings HI) as (_ & _ & D); exact (proj1 (D g am Hu H63))|].
          eapply unlinked_of_next_None; eauto. }
        split; [apply (Inv_exempt X (Some (g, i)) U s g am HI Hu Hnofr Hp Enx); intros p j E; injection E; auto|].
        split; [rewrite Mg; destruct am; cbn in Hp, Enx |- *; subst; reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [apply corr_refl|]. split.
        + intros q a Hq. apply usedX_cons_inv in Hq as [_ Hq]. exists a. split; [exact Hq | apply ceq_refl].
        + split; [intros; reflexivity | apply ub_same_refl].
Qed.

(* [comment removed for export] *)
Definition DQP (X : list sptr) (U : Z -> Z) (s : astate) (g : sptr) (am : ameta) (s1 : astate) : Prop :=
  Inv (g :: X) None (fun c => U c + contrib X s c g) s1 /\ MT s1 g = Some (MUsed (am_set_links None None am)) /\
  st_usage s1 = st_usage s /\ st_regions s1 = st_regions s /\ corr X s s1 /\
  (forall q a, usedX (g :: X) s1 q a -> exists a0, usedX X s q a0 /\ ceq a a0) /\
  (forall q, (forall a, usedX X s q a -> am_sc a <> am_sc am) -> q <> g -> MT s1 q = MT s q) /\ ub_same s s1.

Lemma deq_model' : forall X U s g i am s1, Inv X (Some (g, i)) U s -> usedX X s g am ->
  Z.lor (am_freed am) (am_avail am) + bit i = ones (am_last am) -> deq_part g (am_sc am) am s = IRet (tt, s1) -> DQP X U s g am s1.
Proof. intros X U s g i am s1 HI Hu Hm E. pose proof (deq_model X U s g i am HI Hu Hm) as D. rewrite E in D. exact D. Qed.

Lemma alinks_used : forall X s sc q l, alinks X s sc q = Some l -> exists a, usedX X s q a /\ am_sc a = sc /\ l = (am_prev a, am_next a).
Proof.
  intros X s sc q l H. unfold alinks in H. destruct (MTX X s q) as [[pr nx| |a]|] eqn:E; try discriminate.
  destruct (am_sc a =? sc) eqn:Es; [|discriminate]. injection H as <-. exists a. split; [exact E|]. split; [apply Z.eqb_eq; exact Es | reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma usg_Inv : forall X U s g i am sA, Inv X (Some (g, i)) U s -> usedX X s g am -> (forall c, 0 <= U c) ->
  Inv (g :: X) None (fun c => U c + contrib X s c g) sA -> st_usage sA = st_usage s ->
  Inv (g :: X) None U (s_usg s sA (am_sc am) (am_last am)).
Proof.
  intros X U s g i am sA HI Hu HU HI1 Eus1.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. pose proof (MT_Some_In_keys _ _ _ Mg) as Kg.
  pose proof (inv_groups HI g am Hu) as (_ & _ & _ & Gcl & _).
  assert (Hsc0 : 0 <= am_sc am) by (destruct Gcl as [(C & _) | (C & _)]; lia).
  set (sc := am_sc am) in *.
  assert (HU1 : forall c, 0 <= c < 48 -> U c + contrib X s c g = U c + (if sc =? c then am_last am + 1 else 0)).
  { intros c Hc. rewrite (contrib_used X s c g am Hu). reflexivity. }
  unfold s_usg. destruct (sc <? 48) eqn:E48.
  - apply Z.ltb_lt in E48.
    assert (Hv : am_last am + 1 <= usage_of s sc).
    { rewrite (inv_usage HI sc ltac:(lia)). pose proof (class_sum_ge_contrib X _ U s sc g HI Kg) as Hge.
      rewrite (contrib_used X s sc g am Hu) in Hge. fold sc in Hge. rewrite Z.eqb_refl in Hge. pose proof (HU sc). lia. }
    pose proof (Inv_set_usage (g :: X) None _ sA sc (usage_of s sc - (am_last am + 1)) HI1 ltac:(lia) ltac:(lia)) as HI2.
    eapply Inv_U_ext; [|exact HI2]. intros c Hc. unfold Uadd. cbv beta. rewrite (HU1 c Hc).
    replace (usage_of sA sc) with (usage_of s sc) by (unfold usage_of; rewrite Eus1; reflexivity).
    destruct (c =? sc) eqn:E1; destruct (sc =? c) eqn:E2; try lia;
      try (apply Z.eqb_eq in E1; apply Z.eqb_neq in E2; lia); try (apply Z.eqb_neq in E1; apply Z.eqb_eq in E2; lia).
  - apply Z.ltb_ge in E48. eapply Inv_U_ext; [|exact HI1]. intros c Hc. cbv beta. rewrite (HU1 c Hc).
    destruct (sc =? c) eqn:E2; [apply Z.eqb_eq in E2; lia | lia].
Qed.

Lemma seq_rec_Inv : forall X R U s2 sc, Inv X R U s2 -> Inv X R U (s_rec sc (s_seq s2)).
Proof.
  intros X R U s2 sc HI.
  pose proof (step_seq_spec X R U s2 (fun r => Inv X R U (snd r)) HI (fun s' H' _ => H')) as A1.
  change (Inv X R U (s_seq s2)) in A1.
  pose proof (record_seq_spec X R U (s_seq s2) sc (fun r => Inv X R U (snd r)) A1 (fun s' H' _ => H')) as A2.
  unfold record_seq in A2. unfold s_rec. destruct (bounce_idx sc) as [k|]; exact A2.
Qed.

Lemma forget_itree : forall s pg amp idx, MT s pg = Some (MUsed amp) -> forget_frame pg idx s = IRet (tt, s_ff s pg amp idx).
Proof.
  intros s pg amp idx Mp. unfold MT in Mp. unfold forget_frame, getm, setm, modify, get, bind, ret. cbn [ibind fst snd]. rewrite Mp. reflexivity.
Qed.

Lemma forget_Inv : forall X U s2 pg amp idx fr, Inv X None U s2 -> usedX X s2 pg amp -> 0 <= idx <= am_last amp ->
  ss_fr (nth_slot amp idx) = Some fr ->
  (forall c ac, usedX X s2 c ac -> am_maplen ac = 0 -> am_mem ac <> slot_start amp idx) ->
  Inv X (Some (pg, idx)) U (s_ff s2 pg amp idx).
Proof.
  intros X U s2 pg amp idx fr HI Hu Hi Hfr Hno.
  pose proof (forget_frame_spec X U s2 pg idx amp fr (fun r => Inv X (Some (pg, idx)) U (snd r)) HI Hu Hi Hfr Hno (fun s' _ H' => H')) as A.
  rewrite (forget_itree s2 pg amp idx (proj1 (usedX_MT _ _ _ _ Hu))) in A. exact A.
Qed.

Lemma step_seq_itree : forall s, step_seq s = IRet (tt, s_seq s).
Proof. intros s. reflexivity. Qed.

Lemma record_seq_itree : forall sc s, record_seq sc s = IRet (tt, s_rec sc s).
Proof. intros sc s. unfold record_seq, s_rec. destruct (bounce_idx sc); reflexivity. Qed.

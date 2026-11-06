(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "astate"; "with_links"; "headloc"; "st_active"; "links_of"; "st_free_meta_head"; "sptr_eqb"; "HActive"; "HFreeMeta"; "st_area_head"; "st_area_tail"; "st_areas"; "st_avail_meta"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_avail_meta_count"; "st_bounces"; "st_brk"; "st_init_done"; "st_meta_alloc_shift"; "st_metas"; "st_mmap_counter"; "st_regions"; "st_seq"; "st_unmap_seq"; "st_usage"; "MUsed"; "brkst"; "dequeue"; "get_head"; "lupd"; "osptr_eqb"; "queue"; "region"; "set_active"; "set_free_meta_head"; "set_head"; "set_links"; "set_next"; "set_prev"; "setm"; "setslot"; "@Corelib.Init.Datatypes"; "option"; "Some"; "unit"; "prod"; "pair"; "bool"; "tt"; "list"; "None"; "length"; "nat"; "fst"; "snd"; "cons"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "MT"; "keys"; "active_hd"; "cycle_ok"; "ring_ok"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRingOps"; "set_head_st"; "head_of"; "heads_same_except"; "head_idx_ok"; "same_but_metas_heads"; "LK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase"; "itok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@Stdlib.Lists.List"; "In"; "hd"; "last"; "@Corelib.Lists.ListDef"; "nth"; "@Stdlib.ZArith.BinInt.Z"; "to_nat"; "@Corelib.Init.Peano"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Ltac mbinds := repeat lazymatch goal with |- itok (bind _ _ _) _ => apply itok_bind end.

Definition LK (s : astate) (q : sptr) : option (option sptr * option sptr) := ltac2:(tb__ "0|2|
S30S5A1S30S33S30S4A1M0G0A2M1A1Lx;S3eVs;Vq;A2S5S31G1SaR1A1A2Lx;S38G1A1X30x2").

Lemma links_with_links x pr nx : ltac2:(tb__ "0|1|
S0S33S30S4A1M0G0A2SaS7Vx;Vpr;Vnx;A3A1S34G0G0Vpr;Vnx;A4A3").
Proof. destruct x; reflexivity. Qed.

Lemma with_links_with_links x a b c d : ltac2:(tb__ "0|0|
S0S5S7S7Vx;Va;Vb;A3Vc;Vd;A3S7Vx;Vc;Vd;A3A3").
Proof. destruct x; reflexivity. Qed.

Definition set_head_st (h : headloc) (v : option sptr) (s : astate) : astate := ltac2:(tb__ "0|0|
S8S6Lh;Vh;S43S28S24S30S4A1S9Vs;A1S50R1A1Vv;A4Vs;A2Lsc;S29Vv;Vs;A2X8x2").

Lemma itok_set_head' h v s (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;S34S32S6S36S44Vh;Vv;Vs;A3A4A1S4aS33S32S6A2S2aVh;Vv;Vs;A3VQ;A3F_;").
Proof. intros H. apply itok_set_head. destruct h; exact H. Qed.

Definition head_of (h : headloc) (s : astate) : option sptr := ltac2:(tb__ "0|0|
S8S30S4A1Lh;Vh;S43S40Vs;R1A2Lsc;SbVs;A1X8x2").

Lemma itok_get_head' h s (Q : option sptr * astate -> Prop) : ltac2:(tb__ "0|1|
VQ;S34S30S4A1M0S6S45Vh;Vs;A2Vs;A4A1S4aS33G0S6A2S23Vh;Vs;A2VQ;A3F_;").
Proof. intros H. apply itok_get_head. destruct h; exact H. Qed.

Definition head_idx_ok (h : headloc) (s : astate) : Prop := ltac2:(tb__ "0|0|
S8OLh;Vh;S43S51S50R1A1S39S30S4A1S9Vs;A1A2A2Lsc;S3X8x2").

Lemma st_metas_set_head h v s : ltac2:(tb__ "0|0|
S0S37S33S4S5A2A1S1aS44Vh;Vv;Vs;A3A1S1aVs;A1A3").
Proof. destruct h; reflexivity. Qed.

Lemma MT_set_head h v s q : ltac2:(tb__ "0|0|
S0S30S5A1S3eS44Vh;Vv;Vs;A3Vq;A2S3eVs;Vq;A2A3").
Proof. unfold MT. rewrite st_metas_set_head. reflexivity. Qed.

Lemma head_of_set_head h v s : ltac2:(tb__ "0|0|
S47Vh;Vs;A2S0S30S4A1S45Vh;S44Vh;Vv;Vs;A3A2Vv;A3F_;").
Proof.
  destruct h as [sc|]; cbn; [|reflexivity]. intros Hi. unfold active_hd. cbn [st_active set_active].
  rewrite nth_lupd, Nat.eqb_refl. replace (Nat.ltb (Z.to_nat sc) (length (st_active s))) with true; [reflexivity|].
  symmetry. apply Nat.ltb_lt. exact Hi.
Qed.

Lemma nth_active_set_head h v s k : ltac2:(tb__ "0|2|
S43S0S8Vh;SdR1A1A3S2S0S3aVk;S50R2A1A3A1F_;Fsc;S0S30S4A1M0S4fG0Vk;S9S44Vh;Vv;Vs;A3A1S38S4A1M1A4S4fG0Vk;S9Vs;A1G1A4A3F_;").
Proof.
  intros Hk. destruct h as [sc|]; cbn [st_active set_head_st set_active set_free_meta_head]; [|reflexivity].
  rewrite nth_lupd. replace (Nat.eqb k (Z.to_nat sc)) with false; [reflexivity|].
  symmetry. apply Nat.eqb_neq. apply Hk. reflexivity.
Qed.

Lemma fmh_set_head h v s : ltac2:(tb__ "0|0|
S2S0S8Vh;SeA3A1S0S30S4A1SbS44Vh;Vv;Vs;A3A1SbVs;A1A3F_;").
Proof. destruct h; [reflexivity | intros H; exfalso; apply H; reflexivity]. Qed.

Lemma length_active_set_head h v s : ltac2:(tb__ "0|1|
S0S3aS39S30S4A1M0S9S44Vh;Vv;Vs;A3A1A2S39G0S9Vs;A1A2A3").
Proof. destruct h; cbn; [apply length_lupd | reflexivity]. Qed.

Lemma head_idx_ok_set_head h h' v s : ltac2:(tb__ "0|0|
S47Vh;Vs;A2S47Vh;S44Vh';Vv;Vs;A3A2F_;").
Proof. unfold head_idx_ok. rewrite length_active_set_head. auto. Qed.

Lemma head_idx_ok_upd_meta h g x s : ltac2:(tb__ "0|0|
S47Vh;Vs;A2S47Vh;S4bVg;Vx;Vs;A3A2F_;").
Proof. unfold head_idx_ok, upd_meta. cbn. auto. Qed.

Lemma head_of_upd_meta h g x s : ltac2:(tb__ "0|0|
S0S30S4A1S45Vh;S4bVg;Vx;Vs;A3A2S45Vh;Vs;A2A3").
Proof. destruct h; reflexivity. Qed.

Lemma itok_set_links' p pr nx s x (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
S0S30S5A1S3eVs;Vp;A2S31S5Vx;A2A3VQ;S34S32S6S36S4bVp;S7Vx;Vpr;Vnx;A3Vs;A3A4A1S4aS33S32S6A2S2bVp;Vpr;Vnx;Vs;A4VQ;A3F_;F_;").
Proof. intros. eapply itok_set_links; eauto. Qed.

Lemma itok_setm' p am s (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;S34S32S6S36S4bVp;S20Vam;A1Vs;A3A4A1S4aS33S32S6A2S2eVp;Vam;Vs;A3VQ;A3F_;").
Proof. intros. apply itok_setm. assumption. Qed.

Lemma itok_setslot' p x s (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;S34S32S6S36S4bVp;Vx;Vs;A3A4A1S4aS33S32S6A2S2fVp;Vx;Vs;A3VQ;A3F_;").
Proof. intros. apply itok_setslot. assumption. Qed.

Lemma itok_set_next p nx s x (Q : unit * astate -> Prop) : ltac2:(tb__ "0|1|
S0S30S5A1S3eVs;Vp;A2S31S5Vx;A2A3VQ;S34S32S6S36S4bVp;S7Vx;S3bS30S4A1M0G0SaVx;A1A3Vnx;A3Vs;A3A4A1S4aS33S32S6A2S2cVp;Vnx;Vs;A3VQ;A3F_;F_;").
Proof.
  intros Hm H. unfold set_next. apply itok_bind. eapply itok_get_links; [exact Hm|]. msimp.
  eapply itok_set_links; [exact Hm|]. exact H.
Qed.

Lemma itok_set_prev p pr s x (Q : unit * astate -> Prop) : ltac2:(tb__ "0|1|
S0S30S5A1S3eVs;Vp;A2S31S5Vx;A2A3VQ;S34S32S6S36S4bVp;S7Vx;Vpr;S3cS30S4A1M0G0SaVx;A1A3A3Vs;A3A4A1S4aS33S32S6A2S2dVp;Vpr;Vs;A3VQ;A3F_;F_;").
Proof.
  intros Hm H. unfold set_prev. apply itok_bind. eapply itok_get_links; [exact Hm|]. msimp.
  eapply itok_set_links; [exact Hm|]. exact H.
Qed.

Definition same_but_metas_heads (s s' : astate) : Prop := ltac2:(tb__ "0|3|
S1S0S35S18Vs';A1S18Vs;A1A3S1S0S43S1bVs';A1S1bVs;A1A3S1S0S4S12Vs';A1S12Vs;A1A3S1S0S43S15Vs';A1S15Vs;A1A3S1S0S43S13Vs';A1S13Vs;A1A3S1S0S43S19Vs';A1S19Vs;A1A3S1S0S30S4A1M0SfVs';A1SfVs;A1A3S1S0G0S10Vs';A1S10Vs;A1A3S1S0S4S14Vs';A1S14Vs;A1A3S1S0S37S43A1M1S1fVs';A1S1fVs;A1A3S1S0G1S1eVs';A1S1eVs;A1A3S1S0G1S16Vs';A1S16Vs;A1A3S1S0S43S1dVs';A1S1dVs;A1A3S1S0S21S17Vs';A1S17Vs;A1A3S1S0S37S27A1S1cVs';A1S1cVs;A1A3S1S0S37S4A1M2S11Vs';A1S11Vs;A1A3S0G2S3fVs';A1S3fVs;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").

Definition heads_same_except (h : headloc) (s s' : astate) : Prop := ltac2:(tb__ "0|4|
S1S3aS43S0S8Vh;SdR1A1A3S2S0S3aR3S50R2A1A3A1F_;Fsc;S0S30S4A1M0S4fG0R2S9Vs';A1M1S38S4A1M2A4S4fG0R2S9Vs;A1M3G2A4A3F_;Fk;S1S2S0S8Vh;SeA3A1S0G0SbVs';A1SbVs;A1A3F_;S0S3aS39G0G1A2S39G0G3A2A3A2A2").

Lemma sbmh_refl s : same_but_metas_heads s s.
Proof. repeat split; reflexivity. Qed.

Lemma sbmh_trans s1 s2 s3 : ltac2:(tb__ "0|0|
S48Vs1;Vs2;A2S48Vs2;Vs3;A2S48Vs1;Vs3;A2F_;F_;").
Proof. unfold same_but_metas_heads. intros A B. decompose [and] A. decompose [and] B. repeat split; congruence. Qed.

Lemma sbmh_upd_meta g x s : ltac2:(tb__ "0|0|
S4cS4Vg;S3fVs;A1A3S48Vs;S4bVg;Vx;Vs;A3A2F_;").
Proof. intros Hg. repeat split; try reflexivity. apply keys_upd_In. exact Hg. Qed.

Lemma sbmh_set_head h v s : ltac2:(tb__ "0|0|
S48Vs;S44Vh;Vv;Vs;A3A2").
Proof. destruct h; repeat split; reflexivity. Qed.

Lemma hse_refl h s : ltac2:(tb__ "0|0|
S46Vh;Vs;Vs;A3").
Proof. repeat split; reflexivity. Qed.

Lemma hse_trans h s1 s2 s3 : ltac2:(tb__ "0|0|
S46Vh;Vs1;Vs2;A3S46Vh;Vs2;Vs3;A3S46Vh;Vs1;Vs3;A3F_;F_;").
Proof.
  intros (A1 & A2 & A3) (B1 & B2 & B3). split; [|split]; [intros k Hk; rewrite B1, A1; auto | intros H; rewrite B2, A2; auto | congruence].
Qed.

Lemma hse_upd_meta h g x s : ltac2:(tb__ "0|0|
S46Vh;Vs;S4bVg;Vx;Vs;A3A3").
Proof. repeat split; reflexivity. Qed.

Lemma hse_set_head h v s : ltac2:(tb__ "0|0|
S46Vh;Vs;S44Vh;Vv;Vs;A3A3").
Proof.
  split; [|split].
  - intros k Hk. apply nth_active_set_head. exact Hk.
  - apply fmh_set_head.
  - apply length_active_set_head.
Qed.

Lemma In_keys_of_MT s q x : ltac2:(tb__ "0|0|
S0S30S5A1S3eVs;Vq;A2S31S5Vx;A2A3S4cS4Vq;S3fVs;A1A3F_;").
Proof. apply MT_Some_In_keys. Qed.

Lemma dequeue_op h m s x rest (lk : sptr -> option (option sptr * option sptr)) (Q : unit * astate -> Prop) : ltac2:(tb__ "0|c|
S0S30S5A1M0S3eVs;Vm;A2S31S5Vx;A2A3S41Vlk;S3dS4Vm;Vrest;A3M1A2S4S33S30S4A1M2G2A2M3S4cS4R2G1A3S0S30G3A1M4Vlk;R3A1S31G3R2A2A3S0G4S49Vs;R4A2S31G3R3A2A3F_;F_;Fl;Fq;S47Vh;Vs;A2S6S48Vs;R1A2S46Vh;Vs;R2A3S0G2S45Vh;R3A2S37S4A1M5G2Lrest;Vrest;S38S4A1M6S4G5S35G2L_;M7S25S45Vh;Vs;A2M8S31S4Vm;A2A2S31S4R2A2G8X35x2Ll;Ly;X37x2A3S0G0S3eR4Vm;A2S31S5S7Vx;G6G6A3A2A3S4S2S4cS4R1G1A3A1S0G0S3eR7R2A2S3eVs;R2A2A3F_;Fq;S4S5S4cS4R2Vrest;A3S0G0S3eVs;R3A2S31S5R2A2A3S0G0S3eRaR4A2S31S5S7R3G7ScR4S4dS4Vm;Vrest;A3M9A2S31S4S4eS4Vrest;Vm;A3MaA2S3bG2G2SaR3A1MbA3X35x2G7ScR4GaA2S31S4G9A2S3cG2G2GbA3X35x2A3A2A3F_;F_;Fxy;Fy;VQ;S34S32S6S36R7A4A1F_;F_;F_;F_;F_;F_;Fs';S4aS33S32S6A2S22Vh;Vm;Vs;A3VQ;A3F_;F_;F_;F_;F_;").
Proof.
  intros Hm Hcyc Hlk Hh HQ.
  destruct Hcyc as [Hnd Hch].
  assert (Lm : lk m = Some (Some (last rest m), Some (hd m rest))).
  { cbn [chain] in Hch. rewrite last_cons in Hch. destruct Hch as [Hx _]. exact Hx. }
  pose proof (Hlk m _ (or_introl eq_refl) Lm) as LKm. unfold LK in LKm. rewrite Hm in LKm.
  injection LKm as Lx.
  pose proof (In_keys_of_MT _ _ _ Hm) as Km.
  unfold dequeue. mbinds. eapply itok_get_links; [exact Hm|]. msimp. rewrite Lx. cbn [fst snd].
  inversion Hnd as [|m' rest0 Hmn Hndr]; subst.
  destruct rest as [|y rest'].
  -
    cbn [hd]. replace (osptr_eqb (Some m) (Some m)) with true by (cbn; rewrite sptr_eqb_refl; reflexivity).
    mbinds. apply itok_set_head'. msimp.
    eapply itok_set_links; [rewrite MT_set_head; exact Hm|].
    change (Q (tt, upd_meta m (with_links x None None) (set_head_st h None s))).
    apply HQ.
    + eapply sbmh_trans; [apply sbmh_set_head | apply sbmh_upd_meta]. unfold keys. rewrite st_metas_set_head. exact Km.
    + eapply hse_trans; [apply hse_set_head | apply hse_upd_meta].
    + rewrite head_of_upd_meta. apply head_of_set_head. exact Hh.
    + rewrite MT_upd_same. reflexivity.
    + intros q Hq. rewrite MT_upd_other, MT_set_head; [reflexivity|]. intros ->. apply Hq. left. reflexivity.
    + intros z xz Hz. destruct Hz.
  -
    cbn [hd].
    assert (Hym : y <> m) by (intros ->; apply Hmn; left; reflexivity).
    replace (osptr_eqb (Some y) (Some m)) with false
      by (symmetry; apply Bool.not_true_iff_false; rewrite osptr_eqb_eq; congruence).
    remember (last (y :: rest') m) as t eqn:Et.

    assert (Htin : In t (y :: rest')) by (rewrite Et; apply In_last; discriminate).
    assert (Htm : t <> m) by (intros E; apply Hmn; rewrite <- E; exact Htin).
    destruct Hch as [_ Hch].
    destruct (chain_links _ _ _ _ t Hch Htin) as (tpr & tnx & Lt).
    pose proof (Hlk t _ (or_intror Htin) Lt) as LKt. unfold LK in LKt.
    destruct (MT s t) as [xt|] eqn:Mt; [|discriminate]. injection LKt as Lxt.
    destruct (chain_links _ _ _ _ y Hch (or_introl eq_refl)) as (ypr & ynx & Ly).
    pose proof (Hlk y _ (or_intror (or_introl eq_refl)) Ly) as LKy. unfold LK in LKy.
    destruct (MT s y) as [xy|] eqn:My; [|discriminate]. injection LKy as Lxy.

    mbinds. eapply itok_set_next; [exact Mt|]. msimp. rewrite Lxt. cbn [fst].

    mbinds.
    apply (itok_set_prev _ _ _ (if sptr_eqb y t then with_links xt (Some tpr) (Some y) else xy)).
    { rewrite MT_upd. destruct (sptr_eqb y t); [reflexivity | exact My]. }
    msimp.

    mbinds. apply itok_get_head'. msimp. rewrite !head_of_upd_meta.
    match goal with |- itok ((if ?c then _ else _) ?st) _ => set (s2 := st) end.
    assert (K2 : same_but_metas_heads s s2 /\ heads_same_except h s s2 /\ head_of h s2 = head_of h s /\
                 head_idx_ok h s2 /\
                 MT s2 m = Some x /\
                 (forall q, ~ In q (m :: y :: rest') -> MT s2 q = MT s q) /\
                 (forall z xz, In z (y :: rest') -> MT s z = Some xz ->
                    MT s2 z = Some (with_links xz
                          (if sptr_eqb z y then Some t else fst (links_of xz))
                          (if sptr_eqb z t then Some y else snd (links_of xz))))).
    { subst s2. split.
      { eapply sbmh_trans; [apply sbmh_upd_meta; eapply In_keys_of_MT; exact Mt|].
        apply sbmh_upd_meta. rewrite keys_upd_In by (eapply In_keys_of_MT; exact Mt). eapply In_keys_of_MT; exact My. }
      split; [eapply hse_trans; apply hse_upd_meta|].
      split; [rewrite !head_of_upd_meta; reflexivity|].
      split; [apply head_idx_ok_upd_meta, head_idx_ok_upd_meta; exact Hh|].
      split.
      { rewrite MT_upd_other by (intros ->; exact (Hym eq_refl)).
        rewrite MT_upd_other by (intros ->; exact (Htm eq_refl)). exact Hm. }
      split.
      { intros q Hq. rewrite MT_upd_other by (intros ->; apply Hq; right; left; reflexivity).
        rewrite MT_upd_other by (intros ->; apply Hq; right; exact Htin). reflexivity. }
      intros z xz Hz Mz. rewrite MT_upd. destruct (sptr_eqb z y) eqn:Ezy.
      - apply sptr_eqb_eq in Ezy. subst z. rewrite My in Mz. injection Mz as <-.
        destruct (sptr_eqb y t) eqn:Eyt.
        + apply sptr_eqb_eq in Eyt. rewrite <- Eyt in *. rewrite Mt in My. injection My as <-.
          rewrite with_links_with_links, links_with_links. cbn [snd]. reflexivity.
        + rewrite Lxy. cbn [snd]. reflexivity.
      - rewrite MT_upd. destruct (sptr_eqb z t) eqn:Ezt.
        + apply sptr_eqb_eq in Ezt. subst z. rewrite Mt in Mz. injection Mz as <-. rewrite Lxt. reflexivity.
        + rewrite Mz. f_equal.
          destruct (chain_links _ _ _ _ z Hch Hz) as (zp & zn & Lz).
          pose proof (Hlk z _ (or_intror Hz) Lz) as LKz. unfold LK in LKz. rewrite Mz in LKz.
          injection LKz as Lxz.
          destruct xz as [p1 n1| |am]; cbn in Lxz |- *; [injection Lxz as -> ->; reflexivity | discriminate |].
          destruct am; cbn in Lxz |- *. injection Lxz as -> ->. reflexivity. }
    clearbody s2. destruct K2 as (S1 & S2 & S3 & S4 & S5 & S6 & S7).

    assert (FIN : forall s3, same_but_metas_heads s s3 -> heads_same_except h s s3 ->
              head_of h s3 = (if osptr_eqb (head_of h s) (Some m) then Some y else head_of h s) ->
              (forall q, MT s3 q = MT s2 q) -> head_idx_ok h s3 ->
              itok (set_links m None None s3) Q).
    { intros s3 T1 T2 T3 T4 T5. eapply itok_set_links; [rewrite T4; exact S5|].
      change (Q (tt, upd_meta m (with_links x None None) s3)).
      apply HQ.
      - eapply sbmh_trans; [exact T1 | apply sbmh_upd_meta]. destruct T1 as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& ->). exact Km.
      - eapply hse_trans; [exact T2 | apply hse_upd_meta].
      - rewrite head_of_upd_meta. exact T3.
      - apply MT_upd_same.
      - intros q Hq. rewrite MT_upd_other by (intros ->; apply Hq; left; reflexivity). rewrite T4. apply S6. exact Hq.
      - intros z xz Hz Mz. rewrite MT_upd_other by (intros ->; apply Hmn; exact Hz). rewrite T4.
        cbn [hd]. apply S7; assumption. }
    destruct (osptr_eqb (head_of h s) (Some m)) eqn:Ehd.
    + mbinds. apply itok_set_head'. msimp. apply FIN.
      * eapply sbmh_trans; [exact S1 | apply sbmh_set_head].
      * eapply hse_trans; [exact S2 | apply hse_set_head].
      * apply head_of_set_head. exact S4.
      * intros q. apply MT_set_head.
      * apply head_idx_ok_set_head. exact S4.
    + mbinds. apply itok_ret. msimp. apply FIN; auto.
Qed.

Lemma queue_op h m s x ms (lk : sptr -> option (option sptr * option sptr)) (Q : unit * astate -> Prop) : ltac2:(tb__ "0|c|
S0S30S5A1M0S3eVs;Vm;A2S31S5Vx;A2A3S0S33S30S4A1M1G1A2M2SaVx;A1S34G1G1S38S4A1M3G3A4A3S42Vlk;S45Vh;Vs;A2Vms;A3S2S4cS4Vm;Vms;A3A1S4G2S4cS4R2Vms;A3M4S0S30G2A1M5Vlk;R3A1S31G2R2A2A3S0G5S49Vs;R4A2S31G2R3A2A3F_;F_;Fl;Fq;S47Vh;Vs;A2S6S48Vs;R1A2S46Vh;Vs;R2A3S0G1S45Vh;R3A2S31S4S4dS4Vm;Vms;A3M6A2M7A3S0G0S3eR4Vm;A2S31S5S7Vx;S31S4S4eS4Vms;Vm;A3M8A2G7A3A2A3S4S2S4cS4R1S3dS4Vm;Vms;A3A3A1S0G0S3eR7R2A2S3eVs;R2A2A3F_;Fq;S4S5G4S0G0S3eVs;R3A2S31S5R2A2A3S0G0S3eRaR4A2S31S5S7R3S35G1L_;M9ScR4G6A2S31S4Vm;A2MaS3bG1G1SaR3A1MbA3X35x2G9ScR4G8A2GaS3cG1G1GbA3X35x2A3A2A3F_;F_;Fxy;Fy;VQ;S34S32S6S36R7A4A1F_;F_;F_;F_;F_;F_;Fs';S4aS33S32S6A2S26Vh;Vm;Vs;A3VQ;A3F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros Hm Lx Hring Hnin Hlk Hh HQ.
  pose proof (In_keys_of_MT _ _ _ Hm) as Km.
  unfold queue. mbinds. eapply itok_get_links; [exact Hm|]. msimp. rewrite Lx. cbn [fst snd].
  mbinds. apply itok_massert; [reflexivity|]. msimp.
  mbinds. apply itok_get_head'. msimp.
  destruct Hring as [[Hnd Hch] Hhd].
  destruct ms as [|h0 rest].
  -
    cbn in Hhd. rewrite Hhd.
    mbinds. eapply itok_set_links'; [exact Hm|]. msimp.
    apply itok_set_head'.
    apply HQ.
    + eapply sbmh_trans; [apply sbmh_upd_meta; exact Km | apply sbmh_set_head].
    + eapply hse_trans; [apply hse_upd_meta | apply hse_set_head].
    + cbn [hd]. apply head_of_set_head. apply head_idx_ok_upd_meta. exact Hh.
    + rewrite MT_set_head, MT_upd_same. reflexivity.
    + intros q Hq. rewrite MT_set_head, MT_upd_other; [reflexivity|]. intros ->. apply Hq. left. reflexivity.
    + intros y xy Hy. destruct Hy.
  - cbn in Hhd. rewrite Hhd.
    assert (Hh0m : h0 <> m) by (intros ->; apply Hnin; left; reflexivity).
    remember (last (h0 :: rest) m) as t eqn:Et.
    assert (Et' : last (h0 :: rest) h0 = t) by (rewrite Et; apply last_indep; discriminate).
    rewrite Et' in Hch.
    assert (Htin : In t (h0 :: rest)) by (rewrite Et; apply In_last; discriminate).
    assert (Htm : t <> m) by (intros E; apply Hnin; rewrite <- E; exact Htin).

    pose proof Hch as Hch0. cbn [chain] in Hch0. destruct Hch0 as [Lh0 _].
    pose proof (Hlk h0 _ (or_introl eq_refl) Lh0) as LKh0. unfold LK in LKh0.
    destruct (MT s h0) as [xh|] eqn:Mh; [|discriminate]. injection LKh0 as Lxh.
    destruct (chain_links _ _ _ _ t Hch Htin) as (tpr & tnx & Lt).
    pose proof (Hlk t _ Htin Lt) as LKt. unfold LK in LKt.
    destruct (MT s t) as [xt|] eqn:Mt; [|discriminate]. injection LKt as Lxt.
    mbinds. eapply itok_get_links; [exact Mh|]. msimp. rewrite Lxh. cbn [fst].

    mbinds. eapply itok_set_links'; [exact Hm|]. msimp.

    mbinds. eapply (itok_set_next _ _ _ xt).
    { rewrite MT_upd_other by exact Htm. exact Mt. }
    msimp. rewrite Lxt. cbn [fst].

    apply (itok_set_prev _ _ _ (if sptr_eqb h0 t then with_links xt (Some tpr) (Some m) else xh)).
    { rewrite MT_upd. destruct (sptr_eqb h0 t); [reflexivity|]. rewrite MT_upd_other by exact Hh0m. exact Mh. }
    match goal with |- Q (tt, ?st) => set (s' := st) end.
    apply HQ; subst s'.
    + eapply sbmh_trans; [apply sbmh_upd_meta; exact Km|].
      eapply sbmh_trans; [apply sbmh_upd_meta | apply sbmh_upd_meta].
      * rewrite keys_upd_In by exact Km. eapply In_keys_of_MT; exact Mt.
      * rewrite keys_upd_In; [| rewrite keys_upd_In by exact Km; eapply In_keys_of_MT; exact Mt].
        rewrite keys_upd_In by exact Km. eapply In_keys_of_MT; exact Mh.
    + eapply hse_trans; [apply hse_upd_meta|]. eapply hse_trans; apply hse_upd_meta.
    + rewrite !head_of_upd_meta. cbn [hd]. exact Hhd.
    + cbn [hd]. rewrite MT_upd_other by (intros E; exact (Hh0m (eq_sym E))).
      rewrite MT_upd_other by (intros E; exact (Htm (eq_sym E))).
      rewrite MT_upd_same. reflexivity.
    + intros q Hq. rewrite MT_upd_other by (intros ->; apply Hq; right; left; reflexivity).
      rewrite MT_upd_other by (intros ->; apply Hq; right; exact Htin).
      rewrite MT_upd_other by (intros ->; apply Hq; left; reflexivity). reflexivity.
    + intros y xy Hy My. cbn [hd]. rewrite MT_upd. destruct (sptr_eqb y h0) eqn:Eyh.
      * apply sptr_eqb_eq in Eyh. subst y. rewrite Mh in My. injection My as <-.
        destruct (sptr_eqb h0 t) eqn:Eht.
        -- apply sptr_eqb_eq in Eht. rewrite <- Eht in Mt. rewrite Mh in Mt. injection Mt as <-.
           rewrite with_links_with_links, links_with_links. cbn [snd]. reflexivity.
        -- rewrite Lxh. cbn [snd]. reflexivity.
      * rewrite MT_upd. destruct (sptr_eqb y t) eqn:Eyt.
        -- apply sptr_eqb_eq in Eyt. subst y. rewrite Mt in My. injection My as <-. rewrite Lxt. reflexivity.
        -- rewrite MT_upd_other by (intros ->; apply Hnin; exact Hy). rewrite My. f_equal.
           destruct (chain_links _ _ _ _ y Hch Hy) as (yp & yn & Ly).
           pose proof (Hlk y _ Hy Ly) as LKy. unfold LK in LKy. rewrite My in LKy. injection LKy as Lxy.
           destruct xy as [p1 n1| |am]; cbn in Lxy |- *; [injection Lxy as -> ->; reflexivity | discriminate |].
           destruct am; cbn in Lxy |- *. injection Lxy as -> ->. reflexivity.
Qed.

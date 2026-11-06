(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "sptr_eqb"; "@Corelib.Init.Logic"; "eq"; "not"; "ex"; "and"; "iff"; "@Corelib.Init.Datatypes"; "Some"; "option"; "bool"; "pair"; "prod"; "nil"; "app"; "list"; "cons"; "None"; "@Stdlib.Lists.List"; "In"; "last"; "hd"; "NoDup"; "hd_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "chain"; "cycle_ok"; "ring_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing"; "links"; "lk_set"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition links : ltac2:(tb__ "0|0|
E") := ltac2:(tb__ "0|1|
S8SbS8S0A1M0G0A2A1").
Definition lkmap := sptr -> links.

Definition lk_set (lk : lkmap) (p : sptr) (v : option sptr * option sptr) : lkmap := ltac2:(tb__ "0|1|
S0S9S19L_;S1R1Vp;A2S7SbS8S0A1M0G0A2Vv;A2Vlk;R1A1X9x2Lq;").

Lemma lk_set_same lk p v : ltac2:(tb__ "0|1|
S2S19S1aVlk;Vp;Vv;Vp;A4S7SbS8S0A1M0G0A2Vv;A2A3").
Proof. unfold lk_set. rewrite sptr_eqb_refl. reflexivity. Qed.

Lemma lk_set_other lk p v q : ltac2:(tb__ "0|0|
S3S2S0Vq;Vp;A3A1S2S19S1aVlk;Vp;Vv;Vq;A4Vlk;Vq;A1A3F_;").
Proof. intros H. unfold lk_set. destruct (sptr_eqb q p) eqn:E; [apply sptr_eqb_eq in E; congruence | reflexivity]. Qed.

Lemma chain_ext lk lk' prev l first : ltac2:(tb__ "0|1|
S0S11S0R1Vl;A3S2S8SbS8S0A1M0G0A2A1Vlk';R2A1Vlk;R2A1A3F_;Fx;S16Vlk;Vprev;Vl;Vfirst;A4S16Vlk';Vprev;Vl;Vfirst;A4F_;F_;").
Proof.
  revert prev. induction l as [|x rest IH]; intros prev Hext H; cbn in *; [exact I|].
  destruct H as [Hx Hr]. split.
  - rewrite Hext by (left; reflexivity). exact Hx.
  - apply IH; [intros y Hy; apply Hext; right; exact Hy | exact Hr].
Qed.

Lemma cycle_ok_ext lk lk' ms : ltac2:(tb__ "0|1|
S0S11S0R1Vms;A3S2S8SbS8S0A1M0G0A2A1Vlk';R2A1Vlk;R2A1A3F_;Fx;S17Vlk;Vms;A2S17Vlk';Vms;A2F_;F_;").
Proof.
  intros Hext [Hnd H]. split; [exact Hnd|]. destruct ms as [|m0 rest]; [exact H|].
  apply chain_ext with lk; assumption.
Qed.

Lemma ring_ok_ext lk lk' hd ms : ltac2:(tb__ "0|1|
S0S11S0R1Vms;A3S2S8SbS8S0A1M0G0A2A1Vlk';R2A1Vlk;R2A1A3F_;Fx;S18Vlk;Vhd;Vms;A3S18Vlk';Vhd;Vms;A3F_;F_;").
Proof. intros Hext [Hc Hh]. split; [eapply cycle_ok_ext; eauto | exact Hh]. Qed.

Lemma chain_links lk prev l first x : ltac2:(tb__ "0|2|
S16Vlk;Vprev;Vl;Vfirst;A4S11S0Vx;Vl;A3S4S0S0S4S0S0S2S8SbS8S0A1M0G0A2M1A1Vlk;Vx;A1S7G1SaG0G0S7S0R2A2S7S0R1A2A4A2A3Lnx;A2Lpr;A2F_;F_;").
Proof.
  revert prev. induction l as [|y rest IH]; intros prev H Hin; [destruct Hin|].
  cbn in H. destruct H as [Hy Hr]. destruct Hin as [<-|Hin].
  - eexists _, _. exact Hy.
  - eapply IH; eauto.
Qed.

Lemma cycle_links lk ms x : ltac2:(tb__ "0|2|
S17Vlk;Vms;A2S11S0Vx;Vms;A3S4S0S0S4S0S0S2S8SbS8S0A1M0G0A2M1A1Vlk;Vx;A1S7G1SaG0G0S7S0R2A2S7S0R1A2A4A2A3Lnx;A2Lpr;A2F_;F_;").
Proof.
  intros [_ H] Hin. destruct ms as [|m0 rest]; [destruct Hin|]. eapply chain_links; eauto.
Qed.

Lemma ring_links lk hd ms x : ltac2:(tb__ "0|2|
S18Vlk;Vhd;Vms;A3S11S0Vx;Vms;A3S4S0S0S4S0S0S2S8SbS8S0A1M0G0A2M1A1Vlk;Vx;A1S7G1SaG0G0S7S0R2A2S7S0R1A2A4A2A3Lnx;A2Lpr;A2F_;F_;").
Proof. intros [Hc _] Hin. eapply cycle_links; eauto. Qed.

Lemma ring_head lk hd ms : ltac2:(tb__ "0|0|
S18Vlk;Vhd;Vms;A3S2S8S0A1Vhd;S15S0Vms;A2A3F_;").
Proof. intros [_ H]. exact H. Qed.

Lemma ring_head_In lk h ms : ltac2:(tb__ "0|1|
S18Vlk;S7S0Vh;A2Vms;A3S5S11S0Vh;Vms;A3S4SeS0A1M0G0S2G0Vms;SfS0Vh;R1A3A3Lrest;A2A2F_;").
Proof.
  intros [_ Hh]. destruct ms as [|m0 rest]; [discriminate|]. cbn in Hh.
  injection Hh as ->. split; [left; reflexivity | exists rest; reflexivity].
Qed.

Lemma ring_None lk ms : ltac2:(tb__ "0|0|
S18Vlk;S10S0A1Vms;A3S2SeS0A1Vms;ScS0A1A3F_;").
Proof. intros [_ Hh]. destruct ms; [reflexivity | discriminate]. Qed.

Lemma ring_nil lk hd : ltac2:(tb__ "0|0|
S18Vlk;Vhd;ScS0A1A3S2S8S0A1Vhd;S10S0A1A3F_;").
Proof. intros [_ Hh]. exact Hh. Qed.

Lemma ring_ok_nil lk : ring_ok lk None [].
Proof. split; [split; [constructor | exact I] | reflexivity]. Qed.

Lemma last_indep {T} (l : list T) d d' : ltac2:(tb__ "0|0|
S3S2SeVT;A1Vl;ScVT;A1A3A1S2VT;S12VT;Vl;Vd;A3S12VT;Vl;Vd';A3A3F_;").
Proof.
  induction l as [|x [|y t] IH]; intros H; [congruence | reflexivity |].
  cbn [last]. apply IH. discriminate.
Qed.

Lemma last_cons {T} (x : T) l d : ltac2:(tb__ "0|0|
S2VT;S12VT;SfVT;Vx;Vl;A3Vd;A3S12VT;Vl;Vx;A3A3").
Proof.
  destruct l as [|y t]; [reflexivity|].
  change (last (y :: t) d = last (y :: t) x). apply last_indep. discriminate.
Qed.

Lemma last_app_single {T} (l : list T) (a d : T) : ltac2:(tb__ "0|0|
S2VT;S12VT;SdVT;Vl;SfVT;Va;ScVT;A1A3A3Vd;A3Va;A3").
Proof. induction l as [|x [|y t] IH]; cbn in *; auto. Qed.

Lemma In_last {T} (l : list T) d : ltac2:(tb__ "0|0|
S3S2SeVT;A1Vl;ScVT;A1A3A1S11VT;S12VT;Vl;Vd;A3Vl;A3F_;").
Proof.
  induction l as [|x [|y t] IH]; intros H; [congruence | left; reflexivity |].
  right. apply IH. discriminate.
Qed.

Lemma hd_app_indep {T} (l : list T) d d' r : ltac2:(tb__ "0|0|
S3S2SeVT;A1Vl;ScVT;A1A3A1S2VT;S13VT;Vd;SdVT;Vl;Vr;A3A3S13VT;Vd';Vl;A3A3F_;").
Proof. destruct l; [congruence | reflexivity]. Qed.

Lemma hd_app {T} (d : T) l r : ltac2:(tb__ "0|0|
S2VT;S13VT;Vd;SdVT;Vl;Vr;A3A3S13VT;S13VT;Vd;Vr;A3Vl;A3A3").
Proof. destruct l; reflexivity. Qed.

Lemma chain_app lk prev l1 l2 first : ltac2:(tb__ "0|0|
S6S16Vlk;Vprev;SdS0Vl1;Vl2;A3Vfirst;A4S5S16Vlk;Vprev;Vl1;S13S0Vfirst;Vl2;A3A4S16Vlk;S12S0Vl1;Vprev;A3Vl2;Vfirst;A4A2A2").
Proof.
  revert prev. induction l1 as [|x rest IH]; intros prev.
  - cbn. tauto.
  - cbn [app chain]. rewrite last_cons, hd_app, (IH x). tauto.
Qed.

Lemma chain_next lk prev l first x pr nx : ltac2:(tb__ "0|3|
S16Vlk;Vprev;Vl;Vfirst;A4S11S0Vx;Vl;A3S2S8SbS8S0A1M0G0A2M1A1Vlk;Vx;A1S7G1SaG0G0Vpr;Vnx;A4A2A3S4SeS0A1M2G2S4G2G2S5S2G2Vl;SdS0R2SfS0Vx;R1A3A3A3S5S2G0Vnx;S7S0S13S0Vfirst;R1A3A2A3S2G0Vpr;S7S0S12S0R2Vprev;A3A2A3A2A2Ll2;A2Ll1;A2F_;F_;F_;").
Proof.
  revert prev. induction l as [|y rest IH]; intros prev Hc Hin Hx; [destruct Hin|].
  cbn in Hc. destruct Hc as [Hy Hr]. destruct (sptr_eq_dec x y) as [<-|Hne].
  - exists [], rest. rewrite Hx in Hy. injection Hy as -> ->. repeat split; reflexivity.
  - destruct Hin as [->|Hin]; [congruence|].
    destruct (IH y Hr Hin Hx) as (l1 & l2 & -> & Hn & Hp).
    exists (y :: l1), l2. repeat split; try assumption.
    rewrite Hp. f_equal. symmetry. apply last_cons.
Qed.

Lemma cycle_rotate lk x l : ltac2:(tb__ "0|0|
S17Vlk;SfS0Vx;Vl;A3A2S17Vlk;SdS0Vl;SfS0Vx;ScS0A1A3A3A2F_;").
Proof.
  intros [Hnd Hc]. split. apply NoDup_app_single; inversion Hnd; subst; assumption.
  destruct l as [|y l'].
  - cbn in *. exact Hc.
  - cbn [app]. rewrite last_cons, last_app_single.
    cbn [chain] in Hc. rewrite last_cons in Hc. destruct Hc as [Hx Hrest].
    change (chain lk x ((y :: l') ++ [x]) y). apply chain_app. split.
    + cbn [hd]. exact Hrest.
    + cbn [chain hd] in Hx |- *. split; [|exact I]. exact Hx.
Qed.

Lemma cycle_rotate_n lk l1 l2 : ltac2:(tb__ "0|0|
S17Vlk;SdS0Vl1;Vl2;A3A2S17Vlk;SdS0Vl2;Vl1;A3A2F_;").
Proof.
  revert l2. induction l1 as [|x rest IH]; intros l2 H.
  - rewrite app_nil_r. exact H.
  - cbn in H. apply cycle_rotate in H. rewrite <- app_assoc in H. apply IH in H.
    rewrite <- app_assoc in H. exact H.
Qed.

Lemma chain_snoc lk lk' p p' l f f' m : ltac2:(tb__ "0|6|
S16Vlk;Vp;Vl;Vf;A4S14S0Vl;A2S3S2SeS0A1Vl;ScS0A1M0A3A1S3S11S0Vm;Vl;A3A1S0S8S0A1M1G1S11S0R3Vl;A3S2S8SbG1G1A2M2A1M3Vlk;R4A1S7G2SaG1G1R3R2A4A2A3S2G3Vlk';R5A1S7G2SaG1G1S9G1L_;M4S1R5S13S0Vm;Vl;A3A2S7S0Vp';A2R4X9x2G4S1R5S12S0Vl;Vm;A3M5A2S7S0Vm;A2R3X9x2A4A2A3F_;F_;Fnx;Fpr;Fx;S2G3Vlk';Vm;A1S7G2SaG1G1S7S0G5A2S7S0Vf';A2A4A2A3S16Vlk';Vp';SdS0Vl;SfS0Vm;G0A3A3Vf';A4F_;F_;F_;F_;F_;F_;").
Proof.
  revert p p'. induction l as [|x rest IH]; intros p p' Hc Hnd Hne Hm Hupd Hlm; [congruence|].
  cbn [chain] in Hc. destruct Hc as [Hx Hrest].
  inversion Hnd as [|x' rest' Hxn Hndr]; subst.
  cbn [app chain]. split.
  - rewrite (Hupd x _ _ (or_introl eq_refl) Hx). cbn [hd]. rewrite sptr_eqb_refl.
    destruct rest as [|y rest'].
    + cbn. rewrite sptr_eqb_refl. reflexivity.
    + rewrite last_cons.
      assert (E : sptr_eqb x (last (y :: rest') x) = false).
      { apply sptr_eqb_neq. intros Heq. apply Hxn. rewrite Heq at 1. apply In_last. discriminate. }
      rewrite E. reflexivity.
  - destruct rest as [|y rest'].
    + cbn. split; [|exact I]. rewrite Hlm. reflexivity.
    + apply (IH x x).
      * exact Hrest.
      * exact Hndr.
      * discriminate.
      * intros Hin. apply Hm. right. exact Hin.
      * intros z pr nx Hz Hlz. rewrite (Hupd z pr nx (or_intror Hz) Hlz).
        cbn [hd]. rewrite last_cons, (last_indep (y :: rest') x m) by discriminate.
        assert (E : sptr_eqb z x = false) by (apply sptr_eqb_neq; intros ->; exact (Hxn Hz)).
        rewrite E. destruct (sptr_eqb z y) eqn:Ezy; [|reflexivity].
        apply sptr_eqb_eq in Ezy. subst z. cbn [chain] in Hrest. destruct Hrest as [Hy _].
        rewrite Hy in Hlz. injection Hlz as <- <-. reflexivity.
      * rewrite Hlm. rewrite last_cons, (last_indep (y :: rest') x m) by discriminate. reflexivity.
Qed.

Lemma cycle_snoc lk lk' ms m : ltac2:(tb__ "0|8|
S17Vlk;Vms;A2S3S2SeS0A1Vms;ScS0A1M0A3A1S3S11S0Vm;Vms;A3A1S0S8S0A1M1G1S11S0R3Vms;A3S2S8SbG1G1A2M2A1M3Vlk;R4A1S7G2SaG1G1R3R2A4A2A3S2G3Vlk';R5A1S7G2SaG1G1S9G1L_;M4S1R5S13S0Vm;Vms;A3M5A2S7S0Vm;A2M6R4X9x2G4S1R5S12S0Vms;Vm;A3M7A2G6R3X9x2A4A2A3F_;F_;Fnx;Fpr;Fx;S2G3Vlk';Vm;A1S7G2SaG1G1S7S0G7A2S7S0G5A2A4A2A3S17Vlk';SdS0Vms;SfS0Vm;G0A3A3A2F_;F_;F_;F_;F_;").
Proof.
  intros [Hnd Hc] Hne Hm Hupd Hlm. split; [apply NoDup_app_single; assumption|].
  destruct ms as [|m0 rest]; [congruence|]. cbn [app]. rewrite last_cons, last_app_single.
  change (chain lk' m ((m0 :: rest) ++ [m]) m0).
  rewrite (last_indep (m0 :: rest) m0 m) in Hc by discriminate.
  eapply chain_snoc; eauto.
Qed.

Lemma chain_retarget lk lk' p l x y : ltac2:(tb__ "0|5|
S16Vlk;Vp;Vl;Vx;A4S14S0Vl;A2S3S2SeS0A1Vl;ScS0A1A3A1S0S11S0R1Vl;A3S3S2S0R2Vy;A3A1F_;Fz;S0S8S0A1M0G0S11S0R3Vl;A3S2S8SbG0G0A2M1A1M2Vlk;R4A1S7G1SaG0G0R3R2A4A2A3S2G2Vlk';R5A1S7G1SaG0G0S9G0L_;M3S1R5Vy;A2S7S0S12S0Vl;Vy;A3M4A2R4X9x2G3S1R5G4A2S7S0Vy;A2R3X9x2A4A2A3F_;F_;Fnx;Fpr;Fz;S16Vlk';Vp;Vl;Vy;A4F_;F_;F_;F_;F_;").
Proof.
  revert p. induction l as [|z l IH]; intros p Hc Hnd Hne Hny Hupd; [congruence|].
  cbn [chain] in Hc |- *. destruct Hc as [Hz Hl]. inversion Hnd as [|z' l' Hzn Hndl]; subst.
  assert (Ezy : sptr_eqb z y = false) by (apply sptr_eqb_neq; apply Hny; left; reflexivity).
  split.
  - rewrite (Hupd z _ _ (or_introl eq_refl) Hz), Ezy. destruct l as [|w l''].
    + cbn. rewrite sptr_eqb_refl. reflexivity.
    + rewrite last_cons.
      assert (E : sptr_eqb z (last (w :: l'') z) = false).
      { apply sptr_eqb_neq. intros Heq. apply Hzn. rewrite Heq at 1. apply In_last. discriminate. }
      rewrite E. reflexivity.
  - destruct l as [|w l'']; [exact I|].
    apply IH; auto.
    + discriminate.
    + intros u Hu. apply Hny. right. exact Hu.
    + intros u pr nx Hu Hlu. rewrite last_cons, (last_indep (w :: l'') z y) in Hupd by discriminate.
      apply Hupd; [right; exact Hu | exact Hlu].
Qed.

Lemma cycle_remove_first lk lk' x ms : ltac2:(tb__ "0|6|
S17Vlk;SfS0Vx;Vms;A3A2S3S2SeS0A1Vms;ScS0A1A3A1S0S8S0A1M0G0S11S0R3Vms;A3S2S8SbG0G0A2M1A1M2Vlk;R4A1S7G1SaG0G0R3R2A4A2A3S2G2Vlk';R5A1S7G1SaG0G0S9G0L_;M3S1R5S13S0Vx;Vms;A3M4A2S7S0S12S0Vms;Vx;A3M5A2R4X9x2G3S1R5G5A2S7S0G4A2R3X9x2A4A2A3F_;F_;Fnx;Fpr;Fy;S17Vlk';Vms;A2F_;F_;F_;").
Proof.
  intros [Hnd Hc] Hne Hupd. inversion Hnd as [|x' ms' Hxn Hndm]; subst.
  split; [exact Hndm|]. destruct ms as [|y rest]; [congruence|].
  cbn [chain] in Hc. rewrite last_cons in Hc. destruct Hc as [Hx [Hy Hrest]].
  cbn [hd] in Hupd.
  rewrite (last_indep (y :: rest) x y) in Hupd by discriminate.
  inversion Hndm as [|y' rest' Hyn Hndr]; subst.
  cbn [chain]. split.
  - rewrite (Hupd y _ _ (or_introl eq_refl) Hy), sptr_eqb_refl.
    destruct rest as [|w rest''].
    + cbn. rewrite sptr_eqb_refl. reflexivity.
    + rewrite last_cons.
      assert (E : sptr_eqb y (last (w :: rest'') y) = false).
      { apply sptr_eqb_neq. intros Heq. apply Hyn. rewrite Heq at 1. apply In_last. discriminate. }
      rewrite E. reflexivity.
  - destruct rest as [|w rest'']; [exact I|].
    eapply chain_retarget.
    + exact Hrest.
    + exact Hndr.
    + discriminate.
    + intros z Hz ->. exact (Hyn Hz).
    + intros z pr nx Hz Hlz. rewrite (Hupd z _ _ (or_intror Hz) Hlz).
      rewrite last_cons. reflexivity.
Qed.


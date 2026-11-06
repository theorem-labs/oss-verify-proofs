(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "iff"; "False"; "True"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "ameta"; "mslot"; "astate"; "st_active"; "am_sc"; "MFree"; "set_active"; "am_avail"; "am_freed"; "am_next"; "am_prev"; "lupd"; "MRaw"; "usage_of"; "with_links"; "HActive"; "HFreeMeta"; "MUsed"; "am_set_links"; "dequeue"; "dequeue_head"; "free_meta"; "sptr_eqb"; "st_free_meta_head"; "st_init_done"; "st_metas"; "@Corelib.Init.Datatypes"; "option"; "Some"; "prod"; "bool"; "list"; "pair"; "false"; "cons"; "length"; "unit"; "None"; "nat"; "nil"; "tt"; "orb"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "usedX"; "Inv"; "MT"; "alinks"; "memb"; "flinks"; "active_hd"; "keys"; "ring_ok"; "Xok"; "areas_ok"; "contrib"; "ctx_ok"; "keys_ok"; "usage_ok"; "MTX"; "rings_ok"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.Lists.List"; "In"; "hd"; "last"; "remove"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRingOps"; "same_but_metas_heads"; "LK"; "heads_same_except"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery"; "strip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "ucontrib"; "upd_meta"; "@Stdlib.ZArith.BinInt.Z"; "le"; "to_nat"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase"; "itok"; "sptr_eq_dec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings"; "relinked"; "@Corelib.Init.Peano"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame MallocWfRingOps MallocWfSurgery.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma Inv_set_active X R U s l : ltac2:(tb__ "0|1|
S34VX;VR;VU;Vs;A4S0S2eS2bS23S8A1Vl;A2U30A3S43VX;VR;SfVl;Vs;A2M0A3S34VX;VR;VU;G0A4F_;F_;F_;").
Proof.
  intros HI Hl RG.
  split.
  { pose proof (inv_ctx HI) as C. unfold ctx_ok in *. cbn -[Z.pow Z.le Z.lt]. cbn in C.
    destruct C as (C1 & Crest). split; [exact Hl | exact Crest]. }
  split; [exact (inv_keys HI)|]. split; [exact (inv_areas HI)|].
  pose proof (inv_meta HI) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
  split; [exact RG|]. split; [exact M6|]. split; [exact M7 | exact M8].
Qed.

Lemma active_hd_set_active_other s sc sc' v : ltac2:(tb__ "0|2|
S50Z0M0Vsc;A2S50G0Vsc';A2S3S0S44Vsc';Vsc;A3A1S0S23S8A1M1S39SfS14G1ScVs;A1S51Vsc;A1Vv;A4Vs;A2Vsc';A2S39Vs;Vsc';A2A3F_;F_;F_;").
Proof.
  intros H1 H2 H3. unfold active_hd. cbn [st_active set_active]. rewrite nth_lupd.
  replace (Nat.eqb (Z.to_nat sc') (Z.to_nat sc)) with false; [reflexivity|].
  symmetry. apply Nat.eqb_neq. lia.
Qed.

Lemma active_hd_set_active_same s sc v : ltac2:(tb__ "0|3|
S56S51Vsc;A1M0S2bS23S8A1M1ScVs;A1M2A2A2S0G1S39SfS14G1G2G0Vv;A4Vs;A2Vsc;A2Vv;A3F_;").
Proof.
  intros H. unfold active_hd. cbn [st_active set_active]. rewrite nth_lupd, Nat.eqb_refl.
  replace (Nat.ltb (Z.to_nat sc) (length (st_active s))) with true; [reflexivity|].
  symmetry. apply Nat.ltb_lt. exact H.
Qed.

Lemma ring_head_links X s sc m0 am0 ms : ltac2:(tb__ "0|2|
S3bS36VX;Vs;Vsc;A3S24S8Vm0;A2Vms;A3S33VX;Vs;Vm0;Vam0;A4S2S27S8A1M0G0S1S0G0Vms;S2aS8Vm0;R1A3A3S1S0S23S8A1M1S13Vam0;A1S24S8S47S8R1Vm0;A3A2A3S0G1S12Vam0;A1S24S8S46S8Vm0;R1A3A2A3A2A2Lrest;A2F_;F_;").
Proof.
  intros Hr Hu. destruct (ring_head_In _ _ _ Hr) as [_ [rest ->]]. exists rest. split; [reflexivity|].
  destruct Hr as [[Hnd Hch] _]. cbn [chain] in Hch. rewrite last_cons in Hch. destruct Hch as [L _].
  unfold alinks in L. pose proof Hu as Hu'. unfold usedX in Hu'. rewrite Hu' in L.
  destruct (am_sc am0 =? sc); [|discriminate]. injection L as -> ->. auto.
Qed.

Lemma Inv_rotate_head X R U s sc m0 am0 m1 : ltac2:(tb__ "0|3|
S34VX;VR;VU;Vs;A4S1S50Z0M0Vsc;A2S52Vsc;Z30A2A2S33VX;Vs;Vm0;Vam0;A4S0S44SdVam0;A1Vsc;A3S0S23S8A1M1S39Vs;Vsc;A2S24S8Vm0;A2A3S0S44S10Vam0;A1G0A3S3S0S44S11Vam0;A1G0A3A1S0G1S12Vam0;A1S24S8Vm1;A2M2A3S34VX;VR;VU;SfS14G1ScVs;A1S51Vsc;A1G2A4Vs;A2A4F_;F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hsc Hu Hsca Hhd Hav Hfr Hnx.
  pose proof (inv_ctx HI) as C. destruct C as (Clen & _).
  apply Inv_set_active; [exact HI | rewrite length_lupd; exact Clen |].
  destruct (inv_rings HI) as (F & A & D).
  split; [exact F|]. split; [|exact D].
  intros sc' Hsc'. destruct (Z.eq_dec sc' sc) as [->|Hne].
  - destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2).
    rewrite Hhd in Rg. destruct (ring_head_links _ _ _ _ _ _ Rg Hu) as (rest & -> & Hpr & Hnx').
    rewrite Hnx in Hnx'. injection Hnx' as Em1.
    exists (rest ++ [m0]).
    rewrite active_hd_set_active_same by (rewrite Clen; lia).
    split.
    { split; [apply cycle_rotate; exact (proj1 Rg)|].
      rewrite Em1. destruct rest; reflexivity. }
    split.
    { intros g am Hg Hs. rewrite <- (Mem g am Hg Hs), in_app_iff. cbn. tauto. }
    split.
    { intros g am Hg Hs Hnin. apply (Full g am Hg Hs). cbn. rewrite in_app_iff in Hnin. cbn in Hnin. tauto. }
    split.
    { intros g am Hg Hs Hav'. exfalso.
      pose proof (Q1 g am Hg Hs Hav') as E. rewrite Hhd in E. injection E as ->.
      pose proof (usedX_fun _ _ _ _ _ Hg Hu) as ->. exact (Hav' Hav). }
    { intros g am Hg Hs Hin Hnh HnR. destruct (sptr_eq_dec g m0) as [->|Hne].
      - pose proof (usedX_fun _ _ _ _ _ Hg Hu) as ->. exact Hfr.
      - apply (Q2 g am Hg Hs).
        + cbn. rewrite in_app_iff in Hin. cbn in Hin. tauto.
        + rewrite Hhd. congruence.
        + exact HnR. }
  - destruct (A sc' Hsc') as (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
    rewrite active_hd_set_active_other by lia.
    exact (conj Rg (conj Mem (conj Full (conj Q1 Q2)))).
Qed.

Lemma sbmh_ctx s s' : ltac2:(tb__ "0|2|
S49Vs;Vs';A2S0S2eS2bS23S8A1M0ScVs';A1A2S2bG0ScVs;A1A2A3S0S26S21Vs;A1S29A3S0S27S25S8SaA2M1A1S22Vs';A1S2fG1A1A3F_;S3fVs;A1S3fVs';A1F_;F_;F_;F_;").
Proof.
  intros Sb Hl Hinit C. unfold same_but_metas_heads in Sb. unfold ctx_ok in *.
  destruct Sb as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11&E12&E13&E14&E15&E16&E17).
  rewrite Hl, E1, E2, E5, E6, E10, E11, E12, E13, E14, E16.
  destruct C as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12&C13).
  repeat (split; [assumption|]). split; [|exact C13]. intros Hi. destruct (C12 Hi) as (D1&D2&D3&D4). auto.
Qed.

Lemma sbmh_keys s s' : ltac2:(tb__ "0|0|
S49Vs;Vs';A2S40Vs;A1S40Vs';A1F_;F_;").
Proof.
  intros Sb K. unfold same_but_metas_heads in Sb.
  destruct Sb as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11&E12&E13&E14&E15&E16&E17).
  unfold keys_ok, key_placed, handed in *. rewrite E17, E16, E3, E4. exact K.
Qed.

Lemma sbmh_areas s s' : ltac2:(tb__ "0|0|
S49Vs;Vs';A2S3dVs;A1S3dVs';A1F_;F_;").
Proof.
  intros Sb A. unfold same_but_metas_heads in Sb.
  destruct Sb as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11&E12&E13&E14&E15&E16&E17).
  unfold areas_ok, area_ok, resv_total, brk_regions, region_of in *.
  rewrite E16, E15, E7, E8, E6, E14, E5, E9. exact A.
Qed.

Lemma sbmh_usage_of s s' sc : ltac2:(tb__ "0|0|
S49Vs;Vs';A2S0S44S16Vs';Vsc;A2S16Vs;Vsc;A2A3F_;").
Proof.
  intros Sb. unfold same_but_metas_heads in Sb.
  destruct Sb as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11&E12&E13&E14&E15&E16&E17).
  unfold usage_of. rewrite E10. reflexivity.
Qed.

Definition relinked (s s' : astate) (S : list sptr) : Prop := ltac2:(tb__ "0|3|
S1S8S3S45S8R1VS;A3M0A1S0S23SaA1M1S35Vs';R2A2S35Vs;R2A2A3F_;Fq;S8G0S2SaSaS2S23S8A1M2G2S2G2G2S1S0G1S35Vs;R5A2S24SaR3A2A3S1S0G1S35Vs';R5A2S24SaS17R3R2R1A3A2A3S3S0SaR3S15A3A1A2A2Lnx;A2Lpr;A2Lx;A2F_;Fq;A2").

Section Relinked.
  Variables (X : list sptr) (s s' : astate) (S : list sptr).
  Hypothesis RL : ltac2:(tb__ "0|0|
S55Vs;Vs';VS;A3").
  Hypothesis SX : ltac2:(tb__ "0|0|
S8S45S8R1VS;A3S0S26S37R2VX;A2S29A3F_;Fq;").

  Lemma rl_MT_cases q : ltac2:(tb__ "0|4|
S7S0S23SaA1M0S35Vs';Vq;A2M1S35Vs;Vq;A2M2A3S2SaSaS2S23S8A1M3G3S2G3G3S1S0G0G2S24SaR3A2A3S1S0G0G1S24SaS17R3R2R1A3A2A3S1S3S0SaR3S15A3A1S45S8Vq;VS;A3A2A2A2Lnx;A2Lpr;A2Lx;A2A2").
  Proof using RL.
    destruct RL as [R1 R2]. destruct (in_dec sptr_eq_dec q S) as [Hi|Hn].
    - right. destruct (R2 q Hi) as (x & pr & nx & A & B & C). exists x, pr, nx. auto.
    - left. apply R1. exact Hn.
  Qed.

  Lemma rl_used_bwd q am' : ltac2:(tb__ "0|0|
S33VX;Vs';Vq;Vam';A4S2S9S9S1S33VX;Vs;Vq;R1A4S0S9S4cVam';A1S4cR1A1A3A2Lam;A2F_;").
  Proof using RL.
    intros Hu. pose proof (usedX_MT _ _ _ _ Hu) as [M NX].
    destruct (rl_MT_cases q) as [E | (x & pr & nx & A & B & C & D)].
    - exists am'. split; [apply usedX_intro; [exact NX | rewrite <- E; exact M] | reflexivity].
    - rewrite B in M. destruct x as [| |am]; cbn in M; try discriminate.
      injection M as <-. exists am. split; [apply usedX_intro; assumption | reflexivity].
  Qed.

  Lemma rl_used_fwd q am : ltac2:(tb__ "0|0|
S33VX;Vs;Vq;Vam;A4S2S9S9S1S33VX;Vs';Vq;R1A4S0S9S4cR1A1S4cVam;A1A3A2Lam';A2F_;").
  Proof using RL.
    intros Hu. pose proof (usedX_MT _ _ _ _ Hu) as [M NX].
    destruct (rl_MT_cases q) as [E | (x & pr & nx & A & B & C & D)].
    - exists am. split; [apply usedX_intro; [exact NX | rewrite E; exact M] | reflexivity].
    - rewrite A in M. injection M as ->. exists (am_set_links pr nx am).
      split; [apply usedX_intro; [exact NX | exact B] | reflexivity].
  Qed.

  Lemma rl_used_same q am : ltac2:(tb__ "0|0|
S3S45S8Vq;VS;A3A1S4S33VX;Vs';Vq;Vam;A4S33VX;Vs;Vq;Vam;A4A2F_;").
  Proof using RL.
    intros Hn. destruct RL as [R1 _]. unfold usedX, MTX. rewrite (R1 q Hn). tauto.
  Qed.

  Lemma rl_Xok : ltac2:(tb__ "0|0|
S0S27S8A1S3aVs';A1S3aVs;A1A3S3cVX;Vs;A2S3cVX;Vs';A2F_;F_;").
  Proof using RL SX.
    intros K XO x Hx. destruct (XO x Hx) as [Kx Mx]. split; [rewrite K; exact Kx|].
    destruct RL as [R1 _]. rewrite R1; [exact Mx|]. intros Hin. pose proof (SX x Hin) as E.
    unfold memb in E. assert (existsb (sptr_eqb x) X = true); [|congruence].
    apply existsb_exists. exists x. split; [exact Hx | apply sptr_eqb_refl].
  Qed.

  Lemma rl_contrib sc q : ltac2:(tb__ "0|0|
S0S44S3eVX;Vs';Vsc;Vq;A4S3eVX;Vs;Vsc;Vq;A4A3").
  Proof using RL.
    unfold contrib, MTX. destruct (memb q X); [reflexivity|].
    destruct (rl_MT_cases q) as [E | (x & pr & nx & A & B & C & D)]; [rewrite E; reflexivity|].
    rewrite A, B. destruct x; cbn; reflexivity.
  Qed.

  Lemma rl_usage U : ltac2:(tb__ "0|0|
S49Vs;Vs';A2S41VX;VU;Vs;A3S41VX;VU;Vs';A3F_;F_;").
  Proof using RL.
    intros Sb Hu sc Hsc. rewrite (sbmh_usage_of _ _ sc Sb), (Hu sc Hsc). f_equal.
    unfold class_sum. destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). rewrite K.
    assert (E : forall l, fold_right (fun g acc => contrib X s' sc g + acc) 0 l =
                          fold_right (fun g acc => contrib X s sc g + acc) 0 l).
    { induction l as [|k t IH]; [reflexivity|]. cbn [fold_right]. rewrite IH, rl_contrib. reflexivity. }
    symmetry. apply E.
  Qed.

  Lemma rl_flinks_same q : ltac2:(tb__ "0|1|
S3S45S8Vq;VS;A3A1S0S23S25S23S8A1M0G0A2A1S38VX;Vs';Vq;A3S38VX;Vs;Vq;A3A3F_;").
  Proof using RL. intros Hn. destruct RL as [R1 _]. unfold flinks, MTX. rewrite (R1 q Hn). reflexivity. Qed.

  Lemma rl_alinks_same sc q : ltac2:(tb__ "0|1|
S3S45S8Vq;VS;A3A1S0S23S25S23S8A1M0G0A2A1S36VX;Vs';Vsc;Vq;A4S36VX;Vs;Vsc;Vq;A4A3F_;").
  Proof using RL. intros Hn. destruct RL as [R1 _]. unfold alinks, MTX. rewrite (R1 q Hn). reflexivity. Qed.

  Lemma rl_alinks_other sc sc' q : ltac2:(tb__ "0|1|
S8S45S8R1VS;A3S2S9S9S1S33VX;Vs;R3R1A4S0S44SdR1A1Vsc;A3A2Lam;A2F_;Fp;S3S0S44Vsc';Vsc;A3A1S0S23S25S23S8A1M0G0A2A1S36VX;Vs';Vsc';Vq;A4S36VX;Vs;Vsc';Vq;A4A3F_;F_;").
  Proof using RL.
    intros HS Hne. destruct (in_dec sptr_eq_dec q S) as [Hi|Hn]; [|apply rl_alinks_same; exact Hn].
    destruct (HS q Hi) as (am & Hu & Hsc). destruct (rl_used_fwd _ _ Hu) as (am' & Hu' & E).
    unfold alinks. pose proof Hu as M. pose proof Hu' as M'. unfold usedX in M, M'. rewrite M, M'.
    apply strip_fields in E as (_&_&_&_&Es&_). rewrite Es, Hsc.
    replace (sc =? sc') with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  Qed.

  Lemma rl_flinks_used sc q : ltac2:(tb__ "0|1|
S8S45S8R1VS;A3S2S9S9S1S33VX;Vs;R3R1A4S0S44SdR1A1Vsc;A3A2Lam;A2F_;Fp;S0S23S25S23S8A1M0G0A2A1S38VX;Vs';Vq;A3S38VX;Vs;Vq;A3A3F_;").
  Proof using RL.
    intros HS. destruct (in_dec sptr_eq_dec q S) as [Hi|Hn]; [|apply rl_flinks_same; exact Hn].
    destruct (HS q Hi) as (am & Hu & Hsc). destruct (rl_used_fwd _ _ Hu) as (am' & Hu' & E).
    unfold flinks. pose proof Hu as M. pose proof Hu' as M'. unfold usedX in M, M'. rewrite M, M'. reflexivity.
  Qed.
End Relinked.

Lemma ub_same_relinked s s' S : ltac2:(tb__ "0|0|
S55Vs;Vs';VS;A3S0S27S8A1S3aVs';A1S3aVs;A1A3S4dVs;Vs';A2F_;F_;").
Proof.
  intros [R1 R2] K. exists []. rewrite app_nil_r. split; [exact K|]. split; [intros m []|].
  intros g Hg. destruct (in_dec sptr_eq_dec g S) as [Hi|Hn].
  - destruct (R2 g Hi) as (x & pr & nx & A & B & C). rewrite A, B. apply ucontrib_with_links.
  - rewrite (R1 g Hn). reflexivity.
Qed.

Lemma alinks_used X s sc q l : ltac2:(tb__ "0|2|
S0S23S25S23S8A1M0G0A2M1A1S36VX;Vs;Vsc;Vq;A4S24G1Vl;A2A3S2S9S9S1S33VX;Vs;Vq;R1A4S1S0S44SdR1A1Vsc;A3S0G1Vl;S28G0G0S13R1A1S12R1A1A4A3A2A2Lam;A2F_;").
Proof.
  unfold alinks. destruct (MTX X s q) as [[| |am]|] eqn:E; try discriminate.
  destruct (am_sc am =? sc) eqn:Es; [|discriminate]. intros H. injection H as <-.
  exists am. split; [exact E|]. split; [apply Z.eqb_eq; exact Es | reflexivity].
Qed.

Lemma ring_members_used X s sc hd ms q : ltac2:(tb__ "0|0|
S3bS36VX;Vs;Vsc;A3Vhd;Vms;A3S45S8Vq;Vms;A3S2S9S9S1S33VX;Vs;Vq;R1A4S0S44SdR1A1Vsc;A3A2Lam;A2F_;F_;").
Proof.
  intros Hr Hin. destruct (ring_links _ _ _ _ Hr Hin) as (pr & nx & L).
  destruct (alinks_used _ _ _ _ _ L) as (am & Hu & Hs & _). exists am. auto.
Qed.

Lemma LK_of_alinks X s sc q l : ltac2:(tb__ "0|4|
S0S23S25S23S8A1M0G0A2M1A1M2S36VX;Vs;Vsc;Vq;A4S24G1Vl;A2M3A3S0G2S4aVs;Vq;A2G3A3F_;").
Proof.
  intros H. destruct (alinks_used _ _ _ _ _ H) as (am & Hu & _ & ->).
  unfold LK. pose proof (usedX_MT _ _ _ _ Hu) as [M _]. rewrite M. reflexivity.
Qed.

Lemma LK_of_flinks X s q l : ltac2:(tb__ "0|4|
S0S23S25S23S8A1M0G0A2M1A1M2S38VX;Vs;Vq;A3S24G1Vl;A2M3A3S0G2S4aVs;Vq;A2G3A3F_;").
Proof.
  unfold flinks, LK, MTX. destruct (memb q X); [discriminate|].
  destruct (MT s q) as [[pr nx| |am]|]; try discriminate. intros H. injection H as <-. reflexivity.
Qed.

Lemma Inv_dequeue_full_head X R U s sc m0 am0 (Q : unit * astate -> Prop) : ltac2:(tb__ "0|8|
S34VX;VR;VU;Vs;A4S1S50Z0M0Vsc;A2S52Vsc;Z30A2A2S33VX;Vs;Vm0;Vam0;A4S0S44SdVam0;A1Vsc;A3S0S23S8A1M1S39Vs;Vsc;A2S24S8Vm0;A2A3S0S44S10Vam0;A1G0A3S0S44S11Vam0;A1G0A3S8S9S33VX;Vs;R2R1A4M2S0S44SdR2A1Vsc;A3S0S44S10R3A1G0A3F_;F_;Fam;Fg;S8S44S3S0S23S25S8S44A2M3A1VR;S24G3S28S8S44R2R1A4A2A3A1Fi;Fq;SbS34VX;VR;VU;R1A4S49Vs;R2A2S4bS18Vsc;A1M4Vs;R3A3S8S9S33VX;R6R2R1A4S2S9S9S1S33VX;Vs;R4R1A4S0S9S4cR3A1M5S4cR1A1M6A3A2Lam;A2F_;Fam';Fg;S8S9G2S2S9S9S1S33VX;R9R4R1A4S0S9G6G5A3A2Lam';A2F_;Fam;Fg;S0S23SaA1S35R6Vm0;A2S24SaS1aS1bS2dS8A1M7G7Vam0;A3A1A2A3G1OLx;S39R7Vsc;A2S8S1S3S0S8R1Vm0;A3A1S2S9S9S1S33VX;R9R2R1A4S1S0S44SdR1A1Vsc;A3S1S3S0S44S11R1A1G0A3A1S3S0G1S13R1A1G7A3A1A2A2A2Lam1;A2A2Lm1;S6X23x2S4dVs;R8A2VQ;S28S2cSbS30R9A4A1F_;F_;F_;F_;F_;F_;F_;F_;Fs';S53S25S2cSbA2S1cG4Vm0;Vs;A3VQ;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hsc Hu Hsca Hhd Hav Hfr Hall HR0 HQ.
  destruct (inv_rings HI) as (F & A & D).
  destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2).
  rewrite Hhd in Rg. destruct (ring_head_In _ _ _ Rg) as [_ [rest Ems]]. subst ms.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mm0 NX0].
  pose proof (inv_ctx HI) as C. destruct C as (Clen & Crest).
  eapply (dequeue_op (HActive sc) m0 s (MUsed am0) rest (alinks X s sc)).
  - exact Mm0.
  - exact (proj1 Rg).
  - intros q l _ Hl. eapply LK_of_alinks. exact Hl.
  - cbn. rewrite Clen. lia.
  - intros s' Sb Hse Hhd' Mm0' Mother Mrest.

    assert (RL : relinked s s' (m0 :: rest)).
    { split.
      - exact Mother.
      - intros q Hq. destruct Hq as [<- | Hq].
        + exists (MUsed am0), None, None. split; [exact Mm0|]. split; [exact Mm0'|]. discriminate.
        + destruct (ring_members_used _ _ _ _ _ q Rg (or_intror Hq)) as (am & Hqu & _).
          pose proof (usedX_MT _ _ _ _ Hqu) as [Mq _].
          eexists (MUsed am), _, _. split; [exact Mq|]. split; [apply (Mrest q (MUsed am) Hq Mq) | discriminate]. }
    assert (SX : forall q, In q (m0 :: rest) -> memb q X = false).
    { intros q Hq. destruct (ring_members_used _ _ _ _ _ q Rg Hq) as (am & Hqu & _). exact (proj2 (usedX_MT _ _ _ _ Hqu)). }
    assert (SC : forall q, In q (m0 :: rest) -> exists am, usedX X s q am /\ am_sc am = sc).
    { intros q Hq. eapply ring_members_used; eauto. }
    pose proof (rl_used_bwd X s s' _ RL) as Bwd. pose proof (rl_used_fwd X s s' _ RL) as Fwd.

    assert (Hhd_new : active_hd s' sc = match rest with [] => None | y :: _ => Some y end).
    { cbn [head_of] in Hhd'. rewrite Hhd' , Hhd. destruct rest; [reflexivity|]. cbn. rewrite sptr_eqb_refl. reflexivity. }
    assert (Rg' : ring_ok (alinks X s' sc) (active_hd s' sc) rest).
    { rewrite Hhd_new. split; [| destruct rest; reflexivity].
      destruct rest as [|y rest']; [split; [constructor | exact I] |].
      eapply (cycle_remove_first (alinks X s sc) (alinks X s' sc) m0 (y :: rest')).
      - exact (proj1 Rg).
      - discriminate.
      - intros z pr nx Hz Lz. destruct (alinks_used _ _ _ _ _ Lz) as (am & Hzu & Hzs & El).
        pose proof (usedX_MT _ _ _ _ Hzu) as [Mz NXz].
        pose proof (Mrest z (MUsed am) Hz Mz) as Mz'. cbn [with_links] in Mz'.
        unfold alinks, usedX, MTX in *. rewrite NXz in *. rewrite Mz'. cbn [am_sc am_prev am_next am_set_links].
        rewrite Hzs, Z.eqb_refl. injection El as -> ->. cbn [fst snd links_of]. reflexivity. }
    apply HQ; auto.
    all: try (eapply ub_same_relinked; [exact RL|]; destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K); exact K).
    + eapply (Inv_surgery X X R R U U s s' HI).
      * destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_& ER &_). intros k rg Hk _. unfold region_of in *. rewrite ER. exact Hk.
      * exact Bwd.
      * intros p am Hp. left. apply Fwd. exact Hp.
      * intros g i HR. destruct (inv_reserved HI g i HR) as (am & Hgu & Hi & Hf & Ha).
        destruct (Fwd _ _ Hgu) as (am' & Hgu' & E). exists am'.
        pose proof (strip_fields _ _ E) as (_&_&_&El&_). rewrite (strip_nth_slot _ _ i E), (strip_allocated _ _ i E), El. auto.
      * intros p i am' _. left. tauto.
      * apply (sbmh_ctx s s' Sb).
        -- destruct Hse as (_&_&Hl). exact Hl.
        -- intros Hi. exfalso. destruct Crest as (_&_&_&_&_&_&_&_&_&_&Ci&_). destruct (Ci Hi) as (Hm & _).
           pose proof (MT_Some_In_keys _ _ _ Mm0) as K. unfold keys in K. rewrite Hm in K. exact K.
        -- exact (inv_ctx HI).
      * apply (sbmh_keys s s' Sb). exact (inv_keys HI).
      * apply (sbmh_areas s s' Sb). exact (inv_areas HI).
      * eapply rl_Xok; eauto. { destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). exact K. } exact (inv_X HI).
      *
        split.
        { destruct F as (fms & FR & Fall). exists fms. split.
          - destruct Hse as (_ & Hfm & _). rewrite (Hfm ltac:(discriminate)).
            eapply ring_ok_ext; [|exact FR]. intros q _. eapply rl_flinks_used; eauto.
          - intros g pr nx Hg. apply (Fall g pr nx). unfold MTX in *.
            destruct (memb g X); [discriminate|].
            destruct (rl_MT_cases s s' _ RL g) as [E | (x & p' & n' & A1 & B1 & C1 & D1)]; [rewrite <- E; exact Hg|].
            exfalso. destruct (SC g D1) as (am & Hgu & _). pose proof (usedX_MT _ _ _ _ Hgu) as [Mg _].
            rewrite Mg in A1. injection A1 as <-. rewrite B1 in Hg. cbn in Hg. discriminate. }
        split.
        { intros sc' Hsc'. destruct (Z.eq_dec sc' sc) as [->|Hne].
          - exists rest. split; [exact Rg'|].
            split.
            { intros g am' Hg Hs'. destruct (Bwd _ _ Hg) as (am & Hgu & E).
              pose proof (strip_fields _ _ E) as (_&_&_&_&Es&_).
              destruct (sptr_eq_dec g m0) as [->|Hne].
              - pose proof (usedX_MT _ _ _ _ Hg) as [Mg _]. rewrite Mm0' in Mg. injection Mg as <-. cbn.
                split; [intros Hin | intros H; exfalso; apply H; reflexivity].
                exfalso. destruct Rg as [[Hnd _] _]. inversion Hnd; subst. contradiction.
              - destruct (in_dec sptr_eq_dec g rest) as [Hin|Hnin].
                + split; [intros _ | intros _; exact Hin].
                  destruct (ring_links _ _ _ _ Rg' Hin) as (pr & nx & L).
                  unfold alinks in L. pose proof Hg as Hg2. unfold usedX in Hg2. rewrite Hg2 in L.
                  rewrite Hs', Z.eqb_refl in L. injection L as -> ->. discriminate.
                + rewrite (rl_used_same X s s' _ RL g am') in Hg by (intros [->|Hc]; [exact (Hne eq_refl)|exact (Hnin Hc)]).
                  rewrite <- (Mem g am' Hg ltac:(congruence)). cbn. split; [intros Hi; right; exact Hi|].
                  intros [->|Hi]; [exfalso; exact (Hne eq_refl)|exact Hi]. }
            split.
            { intros g am' Hg Hs' Hnin. destruct (Bwd _ _ Hg) as (am & Hgu & E).
              pose proof (strip_fields _ _ E) as (_&Eav&Efr&_&Es&_). rewrite Eav, Efr.
              destruct (sptr_eq_dec g m0) as [->|Hne].
              - pose proof (usedX_fun _ _ _ _ _ Hgu Hu) as ->. auto.
              - apply (Full g am Hgu ltac:(congruence)). cbn. intros [->|Hi]; [exact (Hne eq_refl)|exact (Hnin Hi)]. }
            split.
            { intros g am' Hg Hs' Hav'. exfalso. destruct (Bwd _ _ Hg) as (am & Hgu & E).
              pose proof (strip_fields _ _ E) as (_&Eav&_&_&Es&_). apply Hav'. rewrite Eav. apply (Hall g am Hgu). congruence. }
            { intros g am' Hg Hs' Hin Hnh HnR. destruct (Bwd _ _ Hg) as (am & Hgu & E).
              pose proof (strip_fields _ _ E) as (_&_&Efr&_&Es&_). rewrite Efr.
              apply (Q2 g am Hgu ltac:(congruence)); [right; exact Hin| |exact HnR].
              rewrite Hhd. intros E2. injection E2 as ->.
              destruct Rg as [[Hnd _] _]. inversion Hnd; subst. contradiction. }
          - destruct (A sc' Hsc') as (ms' & Rg2 & Mem2 & Full2 & Q12 & Q22). exists ms'.
            destruct Hse as (Hoth & _ & _).
            assert (EH : active_hd s' sc' = active_hd s sc').
            { unfold active_hd. apply Hoth. intros sc0 E0. injection E0 as <-. lia. }
            rewrite EH. split.
            { eapply ring_ok_ext; [|exact Rg2]. intros q _. eapply rl_alinks_other; eauto. }
            split; [|split; [|split]]; intros g am' Hg Hs'; destruct (Bwd _ _ Hg) as (am & Hgu & E);
              pose proof (strip_fields _ _ E) as (_&Eav&Efr&_&Es&_);
              assert (Hgn : ~ In g (m0 :: rest)) by (intros Hi; destruct (SC g Hi) as (a2 & Hu2 & Hs2); pose proof (usedX_fun _ _ _ _ _ Hu2 Hgu) as ->; congruence);
              rewrite (rl_used_same X s s' _ RL g am' Hgn) in Hg.
            + apply Mem2; [exact Hg | exact Hs'].
            + apply Full2; [exact Hg | exact Hs'].
            + apply Q12; [exact Hg | exact Hs'].
            + apply Q22; [exact Hg | exact Hs']. }
        { intros g am' Hg H63. destruct (Bwd _ _ Hg) as (am & Hgu & E).
          pose proof (strip_fields _ _ E) as (_&_&_&_&Es&_).
          assert (Hgn : ~ In g (m0 :: rest)).
          { intros Hi. destruct (SC g Hi) as (a2 & Hu2 & Hs2). pose proof (usedX_fun _ _ _ _ _ Hu2 Hgu) as ->. lia. }
          rewrite (rl_used_same X s s' _ RL g am' Hgn) in Hg. apply (D g am' Hg H63). }
      * eapply rl_usage; eauto. exact (inv_usage HI).
    + rewrite Hhd_new. destruct rest as [|y rest']; [exact I|].
      split.
      { intros ->. destruct Rg as [[Hnd _] _]. inversion Hnd; subst. apply H1. left. reflexivity. }
      destruct (ring_members_used _ _ _ _ _ y Rg (or_intror (or_introl eq_refl))) as (am & Hyu & Hys).
      destruct (Fwd _ _ Hyu) as (am' & Hyu' & E). exists am'.
      pose proof (strip_fields _ _ E) as (_&_&Efr&_&Es&_).
      split; [exact Hyu'|]. split; [congruence|]. split.
      { rewrite Efr. apply (Q2 y am Hyu Hys); [right; left; reflexivity| |intros i; apply HR0].
        rewrite Hhd. intros E2. injection E2 as ->. destruct Rg as [[Hnd _] _]. inversion Hnd; subst. apply H1. left. reflexivity. }
      destruct (ring_links _ _ _ _ Rg' (or_introl eq_refl)) as (pr & nx & L).
      unfold alinks in L. pose proof Hyu' as M. unfold usedX in M. rewrite M in L.
      rewrite Es, Hys, Z.eqb_refl in L. injection L as -> _. discriminate.
Qed.

Local Open Scope mm_scope.

Lemma memb_cons q m X : ltac2:(tb__ "0|0|
S0S26S37Vq;S2aS8Vm;VX;A3A2S31S1fVq;Vm;A2S37Vq;VX;A2A2A3").
Proof. reflexivity. Qed.

Lemma memb_In q X : ltac2:(tb__ "0|0|
S4S0S26S37Vq;VX;A2S32A3S45S8Vq;VX;A3A2").
Proof.
  unfold memb. rewrite existsb_exists. split.
  - intros (x & Hx & E). apply sptr_eqb_eq in E. subst. exact Hx.
  - intros H. exists q. split; [exact H | apply sptr_eqb_refl].
Qed.

Lemma memb_false_notIn q X : ltac2:(tb__ "0|0|
S4S0S26S37Vq;VX;A2S29A3S3S45S8Vq;VX;A3A1A2").
Proof.
  rewrite <- memb_In. destruct (memb q X); split; intros H; try discriminate; auto. exfalso. apply H. reflexivity.
Qed.

Lemma flinks_free X s q l : ltac2:(tb__ "0|2|
S0S23S25S23S8A1M0G0A2M1A1S38VX;Vs;Vq;A3S24G1Vl;A2A3S2G0G0S2G0G0S1S0S26S37Vq;VX;A2S29A3S1S0S23SaA1S35Vs;Vq;A2S24SaSeR2R1A2A2A3S0G1Vl;S28G0G0R2R1A4A3A2A2Lnx;A2Lpr;A2F_;").
Proof.
  unfold flinks, MTX. destruct (memb q X) eqn:M; [discriminate|].
  destruct (MT s q) as [[pr nx| |am]|] eqn:E; try discriminate. intros H. injection H as <-.
  exists pr, nx. auto.
Qed.

Lemma fring_members_free X s hd ms q : ltac2:(tb__ "0|1|
S3bS38VX;Vs;A2Vhd;Vms;A3S45S8Vq;Vms;A3S2S23S8A1M0G0S2G0G0S1S0S26S37Vq;VX;A2S29A3S0S23SaA1S35Vs;Vq;A2S24SaSeR2R1A2A2A3A2Lnx;A2Lpr;A2F_;F_;").
Proof.
  intros Hr Hin. destruct (ring_links _ _ _ _ Hr Hin) as (pr & nx & L).
  destruct (flinks_free _ _ _ _ L) as (pr' & nx' & M & E & _). exists pr', nx'. auto.
Qed.

Lemma dequeue_head_free_spec X R U s (Q : option sptr * astate -> Prop) : ltac2:(tb__ "0|3|
S34VX;VR;VU;Vs;A4S0S23S8A1M0S20Vs;A1S2dS8A1M1A3S8G0G0S0S23SaA1M2S42VX;Vs;R3A3S24SaSeR2R1A2A2A3S5F_;Fnx;Fpr;Fg;VQ;S28G0SbG1Vs;A4A1F_;F_;S8SbS34S2aS8R2VX;A3VR;VU;R1A4S0S26S37R3VX;A2S29A3S0G2S35R3R4A2S24SaSeG1G1A2A2A3S49Vs;R4A2S0S27G0A1ScR5A1ScVs;A1A3S8S9S4S33S2aS8R9VX;A3R8R2R1A4S33VX;Vs;R2R1A4A2Fam;Fg;S4dVs;R7A2VQ;S28G0SbS24S8R9A2R8A4A1F_;F_;F_;F_;F_;F_;F_;Fs';Fm;S53S25G0SbA2S1dS19Vs;A2VQ;A3F_;F_;F_;").
Proof.
  intros HI HQnone HQsome.
  destruct (inv_rings HI) as (F & A & D). destruct F as (ms & FR & Fall).
  unfold dequeue_head. mbinds. apply itok_get_head'. msimp. cbn [head_of].
  destruct (st_free_meta_head s) as [m|] eqn:Efh.
  2:{ mbinds. apply itok_ret. apply HQnone; [reflexivity|].
      intros g pr nx Hg. pose proof (Fall g pr nx Hg) as Hin. apply ring_None in FR. subst ms. destruct Hin. }
  destruct (ring_head_In _ _ _ FR) as [_ [rest Ems]]. subst ms.
  destruct (fring_members_free _ _ _ _ m FR (or_introl eq_refl)) as (pr0 & nx0 & NXm & Mm).
  pose proof (inv_ctx HI) as (Clen & Crest).
  mbinds.
  eapply (dequeue_op HFreeMeta m s (MFree pr0 nx0) rest (flinks X s)).
  - exact Mm.
  - exact (proj1 FR).
  - intros q l _ Hl. eapply LK_of_flinks. exact Hl.
  - exact I.
  - intros s' Sb Hse Hhd' Mm' Mother Mrest. msimp. apply itok_ret.
    assert (RL : relinked s s' (m :: rest)).
    { split; [exact Mother|]. intros q [<-|Hq].
      - exists (MFree pr0 nx0), None, None. repeat split; auto. discriminate.
      - destruct (fring_members_free _ _ _ _ q FR (or_intror Hq)) as (pr & nx & _ & Mq).
        eexists (MFree pr nx), _, _. split; [exact Mq|]. split; [apply (Mrest q _ Hq Mq) | discriminate]. }
    assert (SX : forall q, In q (m :: rest) -> memb q X = false).
    { intros q Hq. destruct (fring_members_free _ _ _ _ q FR Hq) as (pr & nx & M & _). exact M. }

    assert (EU : forall g am, usedX (m :: X) s' g am <-> usedX X s g am).
    { intros g am. unfold usedX, MTX. rewrite memb_cons.
      destruct (sptr_eqb g m) eqn:Egm; cbn [orb].
      - apply sptr_eqb_eq in Egm. subst g. rewrite NXm, Mm. split; discriminate.
      - destruct (memb g X); [tauto|].
        destruct (rl_MT_cases s s' _ RL g) as [E | (x & p' & n' & A1 & B1 & C1 & D1)]; [rewrite E; tauto|].
        rewrite A1, B1. destruct (fring_members_free _ _ _ _ g FR D1) as (pr & nx & _ & Mg).
        rewrite Mg in A1. injection A1 as <-. cbn. split; discriminate. }
    destruct Hse as (Hact & _ & Hlen).
    assert (EA : st_active s' = st_active s).
    { apply nth_ext with (d := None) (d' := None); [exact Hlen|]. intros n _. apply Hact. intros sc E. discriminate. }
    apply HQsome; auto.
    2:{ eapply ub_same_relinked; [exact RL|]. destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). exact K. }
    eapply (Inv_surgery X (m :: X) R R U U s s' HI).
    + destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_& ER &_). intros k rg Hk _. unfold region_of in *. rewrite ER. exact Hk.
    + intros p am' Hp. exists am'. split; [apply EU; exact Hp | reflexivity].
    + intros p am Hp. left. exists am. split; [apply EU; exact Hp | reflexivity].
    + intros g i HR. destruct (inv_reserved HI g i HR) as (am & Hgu & Hrest). exists am. split; [apply EU; exact Hgu | exact Hrest].
    + intros p i am' _. left. tauto.
    + apply (sbmh_ctx s s' Sb); [exact Hlen | | exact (inv_ctx HI)].
      intros Hi. exfalso. destruct Crest as (_&_&_&_&_&_&_&_&_&_&Ci&_). destruct (Ci Hi) as (Hm & _).
      pose proof (MT_Some_In_keys _ _ _ Mm) as K. unfold keys in K. rewrite Hm in K. exact K.
    + apply (sbmh_keys s s' Sb). exact (inv_keys HI).
    + apply (sbmh_areas s s' Sb). exact (inv_areas HI).
    +
      intros x Hx. destruct Hx as [<-|Hx].
      * split; [| rewrite Mm'; exact I].
        destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). rewrite K. eapply MT_Some_In_keys. exact Mm.
      * destruct (inv_X HI x Hx) as [Kx Mx].
        destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). rewrite K. split; [exact Kx|].
        destruct RL as [R1 _]. rewrite R1; [exact Mx|].
        intros Hin. pose proof (SX x Hin) as E. apply memb_false_notIn in E. exact (E Hx).
    +
      split.
      { exists rest.
        assert (Hfh : st_free_meta_head s' = match rest with [] => None | y :: _ => Some y end).
        { cbn [head_of] in Hhd'. rewrite Hhd', Efh. destruct rest; [reflexivity|]. cbn. rewrite sptr_eqb_refl. reflexivity. }
        split.
        - rewrite Hfh. split; [|destruct rest; reflexivity].
          destruct rest as [|y rest']; [split; [constructor | exact I]|].
          eapply (cycle_remove_first (flinks X s) (flinks (m :: X) s') m (y :: rest')).
          + exact (proj1 FR).
          + discriminate.
          + intros z pr nx Hz Lz. destruct (flinks_free _ _ _ _ Lz) as (pr' & nx' & NXz & Mz & El).
            injection El as <- <-.
            pose proof (Mrest z _ Hz Mz) as Mz'. cbn [with_links] in Mz'.
            unfold flinks, MTX. rewrite memb_cons, NXz.
            replace (sptr_eqb z m) with false.
            2:{ symmetry. apply sptr_eqb_neq. intros ->. destruct FR as [[Hnd _] _]. inversion Hnd; subst. contradiction. }
            cbn [orb]. rewrite Mz'. cbn [fst snd links_of]. reflexivity.
        - intros g pr nx Hg. unfold MTX in Hg. rewrite memb_cons in Hg.
          destruct (sptr_eqb g m) eqn:Egm; [discriminate|]. cbn [orb] in Hg.
          destruct (memb g X) eqn:NXg; [discriminate|].
          destruct (rl_MT_cases s s' _ RL g) as [E | (x & p' & n' & A1 & B1 & C1 & D1)].
          + rewrite E in Hg. assert (Hin : In g (m :: rest)) by (apply (Fall g pr nx); unfold MTX; rewrite NXg; exact Hg).
            destruct Hin as [->|Hin]; [rewrite sptr_eqb_refl in Egm; discriminate | exact Hin].
          + destruct D1 as [->|D1]; [rewrite sptr_eqb_refl in Egm; discriminate | exact D1]. }
      split.
      { intros sc Hsc. destruct (A sc Hsc) as (ms' & Rg2 & Mem2 & Full2 & Q12 & Q22). exists ms'.
        assert (EH : active_hd s' sc = active_hd s sc) by (unfold active_hd; rewrite EA; reflexivity).
        rewrite EH.
        assert (EL : forall q, alinks (m :: X) s' sc q = alinks X s sc q).
        { intros q. unfold alinks.
          destruct (MTX (m :: X) s' q) as [[| |am]|] eqn:E1.
          - destruct (MTX X s q) as [[| |am']|] eqn:E2; try reflexivity.
            assert (Hu : usedX X s q am') by exact E2. apply EU in Hu. unfold usedX in Hu. rewrite Hu in E1. discriminate.
          - destruct (MTX X s q) as [[| |am']|] eqn:E2; try reflexivity.
            assert (Hu : usedX X s q am') by exact E2. apply EU in Hu. unfold usedX in Hu. rewrite Hu in E1. discriminate.
          - assert (Hu : usedX (m :: X) s' q am) by exact E1. apply EU in Hu. unfold usedX in Hu. rewrite Hu. reflexivity.
          - destruct (MTX X s q) as [[| |am']|] eqn:E2; try reflexivity.
            assert (Hu : usedX X s q am') by exact E2. apply EU in Hu. unfold usedX in Hu. rewrite Hu in E1. discriminate. }
        split; [eapply ring_ok_ext; [intros q _; apply EL | exact Rg2]|].
        split; [intros g am Hg; apply EU in Hg; apply Mem2; exact Hg|].
        split; [intros g am Hg; apply EU in Hg; apply Full2; exact Hg|].
        split; [intros g am Hg; apply EU in Hg; apply Q12; exact Hg|].
        intros g am Hg; apply EU in Hg; apply Q22; exact Hg. }
      { intros g am Hg. apply EU in Hg. apply (D g am Hg). }
    +
      intros sc Hsc. rewrite (sbmh_usage_of _ _ sc Sb), (inv_usage HI sc Hsc). f_equal.
      unfold class_sum. destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). rewrite K.
      assert (E : forall l, fold_right (fun g acc => contrib (m :: X) s' sc g + acc) 0 l =
                            fold_right (fun g acc => contrib X s sc g + acc) 0 l).
      { induction l as [|k t IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. f_equal.
        unfold contrib.
        destruct (MTX (m :: X) s' k) as [[| |am]|] eqn:E1; destruct (MTX X s k) as [[| |am']|] eqn:E2; try reflexivity.
        all: try (assert (Hu : usedX X s k am') by exact E2; apply EU in Hu; unfold usedX in Hu; rewrite Hu in E1; discriminate).
        all: try (assert (Hu : usedX (m :: X) s' k am) by exact E1; apply EU in Hu; unfold usedX in Hu; rewrite Hu in E2; try discriminate).
        injection E2 as ->. reflexivity. }
      symmetry. apply E.
Qed.

Lemma Inv_upd_exempt X R U s g x :
  Inv X R U s -> In g X ->
  match x with MRaw => True | MFree None None => True
             | MUsed am => am_prev am = None /\ am_next am = None /\ (forall i, ss_fr (nth_slot am i) = None)
             | _ => False end ->
  Inv X R U (upd_meta g x s).
Proof.
  intros HI Hg Hx.
  pose proof (proj1 (inv_X HI g Hg)) as Kg.
  assert (Mg : memb g X = true) by (apply memb_In; exact Hg).
  assert (EMTX : forall q, MTX X (upd_meta g x s) q = MTX X s q).
  { intros q. unfold MTX. rewrite MT_upd. destruct (sptr_eqb q g) eqn:E; [|reflexivity].
    apply sptr_eqb_eq in E. subst q. rewrite Mg. reflexivity. }
  assert (EU : forall q am, usedX X (upd_meta g x s) q am <-> usedX X s q am).
  { intros q am. unfold usedX. rewrite EMTX. tauto. }
  assert (Sb : same_but_metas_heads s (upd_meta g x s)) by (apply sbmh_upd_meta; exact Kg).
  eapply (Inv_surgery X X R R U U s _ HI).
  - intros k rg Hk _. exact Hk.
  - intros p am' Hp. exists am'. split; [apply EU; exact Hp | reflexivity].
  - intros p am Hp. left. exists am. split; [apply EU; exact Hp | reflexivity].
  - intros q i HR. destruct (inv_reserved HI q i HR) as (am & Hu & Hrest). exists am. split; [apply EU; exact Hu | exact Hrest].
  - intros p i am' _. left. tauto.
  - apply (sbmh_ctx s _ Sb); [reflexivity | | exact (inv_ctx HI)].
    intros Hi. exfalso. pose proof (inv_ctx HI) as (_&_&_&_&_&_&_&_&_&_&_&Ci&_). destruct (Ci Hi) as (Hm & _).
    unfold keys in Kg. rewrite Hm in Kg. exact Kg.
  - apply (sbmh_keys s _ Sb). exact (inv_keys HI).
  - apply (sbmh_areas s _ Sb). exact (inv_areas HI).
  - intros y Hy. destruct (inv_X HI y Hy) as [Ky My]. split; [rewrite (keys_upd_In _ _ _ Kg); exact Ky|].
    rewrite MT_upd. destruct (sptr_eqb y g); [|exact My]. destruct x as [[p|] [n|]| |am]; try exact Hx; destruct Hx.
  - destruct (inv_rings HI) as (F & A & D). split; [|split].
    + destruct F as (ms & FR & Fall). exists ms. split.
      * eapply ring_ok_ext; [|exact FR]. intros q _. unfold flinks. rewrite EMTX. reflexivity.
      * intros q pr nx Hq. rewrite EMTX in Hq. eapply Fall. exact Hq.
    + intros sc Hsc. destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
      change (active_hd (upd_meta g x s) sc) with (active_hd s sc).
      split; [eapply ring_ok_ext; [|exact Rg]; intros q _; unfold alinks; rewrite EMTX; reflexivity|].
      split; [intros q am Hq; apply EU in Hq; apply Mem; exact Hq|].
      split; [intros q am Hq; apply EU in Hq; apply Full; exact Hq|].
      split; [intros q am Hq; apply EU in Hq; apply Q1; exact Hq|].
      intros q am Hq; apply EU in Hq; apply Q2; exact Hq.
    + intros q am Hq. apply EU in Hq. apply (D q am Hq).
  - intros sc Hsc. rewrite (sbmh_usage_of _ _ sc Sb), (inv_usage HI sc Hsc). f_equal.
    unfold class_sum. rewrite (keys_upd_In _ _ _ Kg).
    assert (E : forall l, fold_right (fun q acc => contrib X (upd_meta g x s) sc q + acc) 0 l =
                          fold_right (fun q acc => contrib X s sc q + acc) 0 l).
    { induction l as [|k t IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. unfold contrib. rewrite EMTX. reflexivity. }
    symmetry. apply E.
Qed.

Lemma usedX_upd_exempt X s g x q am : ltac2:(tb__ "0|0|
S45S8Vg;VX;A3S4S33VX;S4fVg;Vx;Vs;A3Vq;Vam;A4S33VX;Vs;Vq;Vam;A4A2F_;").
Proof.
  intros Hg. unfold usedX, MTX. rewrite MT_upd. destruct (sptr_eqb q g) eqn:E; [|tauto].
  apply sptr_eqb_eq in E. subst q. rewrite (proj2 (memb_In g X) Hg). tauto.
Qed.

Lemma ucontrib_exempt_nil X R U s g k : ltac2:(tb__ "0|2|
S34VX;VR;VU;Vs;A4S45S8Vg;VX;A3S0S27S25S25S8S44A2M0G0A2M1A1S4eVk;S35Vs;Vg;A2A2S2fG1A1A3F_;F_;").
Proof.
  intros HI Hg. destruct (inv_X HI g Hg) as [_ Mx]. unfold ucontrib.
  destruct (MT s g) as [[pr nx| |am]|]; try reflexivity. destruct Mx as (A & B & H). apply blocks_of_frameless. exact H.
Qed.

Lemma free_meta_spec X R U s g (Q : unit * astate -> Prop) : ltac2:(tb__ "0|1|
S34VX;VR;VU;Vs;A4S45S8Vg;VX;A3SbS34S48S8S54Vg;VX;A4M0VR;VU;R1A4S49Vs;R2A2S0S27S23S8A1A1ScR3A1ScVs;A1A3S8S9S4S33G0R6R2R1A4S33VX;Vs;R2R1A4A2Fam;Fq;S4dVs;R5A2VQ;S28S2cSbS30R6A4A1F_;F_;F_;F_;F_;Fs';S53S25S2cSbA2S1eVg;Vs;A2VQ;A3F_;F_;F_;").
Proof.
  intros HI Hg HQ.
  unfold free_meta. mbinds. apply itok_setslot'. msimp.
  set (s1 := upd_meta g (MFree None None) s).
  assert (HI1 : Inv X R U s1) by (apply Inv_upd_exempt; [exact HI | exact Hg | exact I]).
  pose proof (proj1 (inv_X HI g Hg)) as Kg.
  assert (Sb1 : same_but_metas_heads s s1) by (apply sbmh_upd_meta; exact Kg).
  assert (Mg1 : MT s1 g = Some (MFree None None)) by (subst s1; apply MT_upd_same).
  destruct (inv_rings HI1) as (F & A & D). destruct F as (ms & FR & Fall).
  pose proof (inv_ctx HI1) as (Clen & Crest).
  assert (Hgn : ~ In g ms).
  { intros Hin. destruct (fring_members_free _ _ _ _ g FR Hin) as (pr & nx & M & _).
    apply memb_false_notIn in M. exact (M Hg). }
  eapply (queue_op HFreeMeta g s1 (MFree None None) ms (flinks X s1)).
  - exact Mg1.
  - reflexivity.
  - exact FR.
  - exact Hgn.
  - intros q l _ Hl. eapply LK_of_flinks. exact Hl.
  - exact I.
  - intros s' Sb Hse Hhd' Mg' Mother Mms.
    set (X' := remove sptr_eq_dec g X) in *.
    assert (RL : relinked s1 s' (g :: ms)).
    { split; [exact Mother|]. intros q [<-|Hq].
      - eexists (MFree None None), _, _. split; [exact Mg1|]. split; [exact Mg'|]. discriminate.
      - destruct (fring_members_free _ _ _ _ q FR Hq) as (pr & nx & _ & Mq).
        eexists (MFree pr nx), _, _. split; [exact Mq|]. split; [apply (Mms q _ Hq Mq) | discriminate]. }
    assert (MX' : forall q, memb q X' = memb q X && negb (sptr_eqb q g)).
    { intros q. subst X'. destruct (memb q X) eqn:E1; destruct (sptr_eqb q g) eqn:E2; cbn.
      - apply memb_false_notIn. apply sptr_eqb_eq in E2. subst. apply remove_In.
      - apply memb_In. apply memb_In in E1. apply in_in_remove; [|exact E1]. apply sptr_eqb_neq in E2. exact E2.
      - apply memb_false_notIn. intros H. apply in_remove in H as [H _]. apply memb_false_notIn in E1. exact (E1 H).
      - apply memb_false_notIn. intros H. apply in_remove in H as [H _]. apply memb_false_notIn in E1. exact (E1 H). }
    assert (EU : forall q am, usedX X' s' q am <-> usedX X s1 q am).
    { intros q am. unfold usedX, MTX. rewrite MX'.
      destruct (sptr_eqb q g) eqn:Eqg; cbn [negb andb].
      - apply sptr_eqb_eq in Eqg. subst q. rewrite (proj2 (memb_In g X) Hg), Mg'. cbn. split; discriminate.
      - rewrite andb_true_r. destruct (memb q X); [tauto|].
        destruct (rl_MT_cases s1 s' _ RL q) as [E | (x & p' & n' & A1 & B1 & C1 & D1)]; [rewrite E; tauto|].
        rewrite A1, B1. destruct D1 as [->|D1]; [rewrite sptr_eqb_refl in Eqg; discriminate|].
        destruct (fring_members_free _ _ _ _ q FR D1) as (pr & nx & _ & Mq).
        rewrite Mq in A1. injection A1 as <-. cbn. split; discriminate. }
    destruct Hse as (Hact & _ & Hlen).
    assert (EA : st_active s' = st_active s1).
    { apply nth_ext with (d := None) (d' := None); [exact Hlen|]. intros n _. apply Hact. intros sc E. discriminate. }
    apply HQ.
    2:{ eapply sbmh_trans; [exact Sb1 | exact Sb]. }
    2:{ rewrite EA. reflexivity. }
    2:{ intros q am. rewrite EU. subst s1. apply usedX_upd_exempt. exact Hg. }
    2:{ eapply ub_same_trans.
        - subst s1. apply (ub_same_upd_In s g (MFree None None) Kg). rewrite (ucontrib_exempt_nil X R U s g g HI Hg). reflexivity.
        - eapply ub_same_relinked; [exact RL|]. destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). exact K. }
    eapply (Inv_surgery X X' R R U U s1 s' HI1).
    + destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_& ER &_). intros k rg Hk _. unfold region_of in *. rewrite ER. exact Hk.
    + intros p am' Hp. exists am'. split; [apply EU; exact Hp | reflexivity].
    + intros p am Hp. left. exists am. split; [apply EU; exact Hp | reflexivity].
    + intros q i HR. destruct (inv_reserved HI1 q i HR) as (am & Hu & Hrest). exists am. split; [apply EU; exact Hu | exact Hrest].
    + intros p i am' _. left. tauto.
    + apply (sbmh_ctx s1 s' Sb); [exact Hlen | | exact (inv_ctx HI1)].
      intros Hi. exfalso. destruct Crest as (_&_&_&_&_&_&_&_&_&_&Ci&_). destruct (Ci Hi) as (Hm & _).
      pose proof (MT_Some_In_keys _ _ _ Mg1) as K. unfold keys in K. rewrite Hm in K. exact K.
    + apply (sbmh_keys s1 s' Sb). exact (inv_keys HI1).
    + apply (sbmh_areas s1 s' Sb). exact (inv_areas HI1).
    +
      intros y Hy. subst X'. apply in_remove in Hy as [Hy Hyg].
      destruct (inv_X HI1 y Hy) as [Ky My].
      destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). rewrite K. split; [exact Ky|].
      destruct RL as [R1 _]. rewrite R1; [exact My|].
      intros [->|Hin]; [exact (Hyg eq_refl)|].
      destruct (fring_members_free _ _ _ _ y FR Hin) as (pr & nx & M & _). apply memb_false_notIn in M. exact (M Hy).
    +
      split.
      { exists (ms ++ [g]). cbn [head_of] in Hhd'. split.
        - split; [| rewrite Hhd'; destruct ms; reflexivity].
          destruct ms as [|h0 rest].
          { cbn. split; [constructor; [intros [] | constructor]|]. split; [|exact I].
            unfold flinks, MTX. rewrite MX', (proj2 (memb_In g X) Hg), sptr_eqb_refl. cbn [andb negb].
            rewrite Mg'. reflexivity. }
          eapply (cycle_snoc (flinks X s1) (flinks X' s') (h0 :: rest) g (proj1 FR)).
            * discriminate.
            * exact Hgn.
            * intros z pr nx Hz Lz. destruct (flinks_free _ _ _ _ Lz) as (pr' & nx' & NXz & Mz & El).
              injection El as <- <-.
              pose proof (Mms z _ Hz Mz) as Mz'. cbn [with_links] in Mz'.
              unfold flinks, MTX. rewrite MX', NXz.
              replace (sptr_eqb z g) with false by (symmetry; apply sptr_eqb_neq; intros ->; exact (Hgn Hz)).
              cbn [andb negb]. rewrite Mz'. cbn [fst snd links_of]. reflexivity.
            * unfold flinks, MTX. rewrite MX', (proj2 (memb_In g X) Hg), sptr_eqb_refl. cbn [andb negb].
              rewrite Mg'. reflexivity.
        - intros q pr nx Hq. unfold MTX in Hq. rewrite MX' in Hq.
          destruct (sptr_eqb q g) eqn:Eqg; [apply sptr_eqb_eq in Eqg; subst; apply in_app_iff; right; left; reflexivity|].
          rewrite andb_true_r in Hq. apply in_app_iff. left.
          destruct (memb q X) eqn:NXq; [discriminate|].
          destruct (rl_MT_cases s1 s' _ RL q) as [E | (x & p' & n' & A1 & B1 & C1 & D1)].
          + rewrite E in Hq. apply (Fall q pr nx). unfold MTX. rewrite NXq. exact Hq.
          + destruct D1 as [->|D1]; [rewrite sptr_eqb_refl in Eqg; discriminate | exact D1]. }
      split.
      { intros sc Hsc. destruct (A sc Hsc) as (ms' & Rg2 & Mem2 & Full2 & Q12 & Q22). exists ms'.
        assert (EH : active_hd s' sc = active_hd s1 sc) by (unfold active_hd; rewrite EA; reflexivity).
        rewrite EH.
        assert (EL : forall q, alinks X' s' sc q = alinks X s1 sc q).
        { intros q. unfold alinks.
          destruct (MTX X' s' q) as [[| |am]|] eqn:E1.
          - destruct (MTX X s1 q) as [[| |am']|] eqn:E2; try reflexivity.
            assert (Hu : usedX X s1 q am') by exact E2. apply EU in Hu. unfold usedX in Hu. rewrite Hu in E1. discriminate.
          - destruct (MTX X s1 q) as [[| |am']|] eqn:E2; try reflexivity.
            assert (Hu : usedX X s1 q am') by exact E2. apply EU in Hu. unfold usedX in Hu. rewrite Hu in E1. discriminate.
          - assert (Hu : usedX X' s' q am) by exact E1. apply EU in Hu. unfold usedX in Hu. rewrite Hu. reflexivity.
          - destruct (MTX X s1 q) as [[| |am']|] eqn:E2; try reflexivity.
            assert (Hu : usedX X s1 q am') by exact E2. apply EU in Hu. unfold usedX in Hu. rewrite Hu in E1. discriminate. }
        split; [eapply ring_ok_ext; [intros q _; apply EL | exact Rg2]|].
        split; [intros q am Hq; apply EU in Hq; apply Mem2; exact Hq|].
        split; [intros q am Hq; apply EU in Hq; apply Full2; exact Hq|].
        split; [intros q am Hq; apply EU in Hq; apply Q12; exact Hq|].
        intros q am Hq; apply EU in Hq; apply Q22; exact Hq. }
      { intros q am Hq. apply EU in Hq. apply (D q am Hq). }
    +
      intros sc Hsc. rewrite (sbmh_usage_of _ _ sc Sb), (inv_usage HI1 sc Hsc). f_equal.
      unfold class_sum. destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). rewrite K.
      assert (E : forall l, fold_right (fun q acc => contrib X' s' sc q + acc) 0 l =
                            fold_right (fun q acc => contrib X s1 sc q + acc) 0 l).
      { induction l as [|k t IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. f_equal.
        unfold contrib.
        destruct (MTX X' s' k) as [[| |am]|] eqn:E1; destruct (MTX X s1 k) as [[| |am']|] eqn:E2; try reflexivity.
        all: try (assert (Hu : usedX X s1 k am') by exact E2; apply EU in Hu; unfold usedX in Hu; rewrite Hu in E1; discriminate).
        all: try (assert (Hu : usedX X' s' k am) by exact E1; apply EU in Hu; unfold usedX in Hu; rewrite Hu in E2; try discriminate).
        injection E2 as ->. reflexivity. }
      symmetry. apply E.
Qed.

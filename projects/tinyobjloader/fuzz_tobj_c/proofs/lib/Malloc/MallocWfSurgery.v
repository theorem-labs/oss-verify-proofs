(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery"; "strip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "ameta"; "sptr"; "frame"; "region"; "nth_slot"; "am_mem"; "ss_fr"; "am_maplen"; "stride_of"; "RkMap"; "am_aidx"; "am_avail"; "am_freed"; "am_last"; "am_sc"; "am_slots"; "poff"; "prid"; "rg_kind"; "rkind"; "slot_start"; "slotst"; "am_set_links"; "class_size"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "usedX"; "group_extent"; "group_ok"; "allocated"; "region_of"; "Inv"; "memb"; "hdr_byte3"; "hdr_off16"; "inside"; "mapped_ok"; "nested_ok"; "reserved_ok"; "Xok"; "areas_ok"; "ctx_ok"; "keys_ok"; "rings_ok"; "usage_ok"; "@Corelib.Init.Datatypes"; "option"; "Some"; "bool"; "None"; "nat"; "true"; "false"; "pair"; "prod"; "list"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame MallocWfRingOps.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition strip (am : ameta) : ameta := am_set_links None None am.

Lemma strip_fields a b : ltac2:(tb__ "0|0|
S0S7S6Va;A1S6Vb;A1A3S1S0S8ScVa;A1ScVb;A1A3S1S0S1fS12Va;A1S12Vb;A1A3S1S0S1fS13Va;A1S13Vb;A1A3S1S0S1fS14Va;A1S14Vb;A1A3S1S0S1fS15Va;A1S15Vb;A1A3S1S0S1fSeVa;A1SeVb;A1A3S1S0S1fS11Va;A1S11Vb;A1A3S0S3cS1cA1S16Va;A1S16Vb;A1A3A2A2A2A2A2A2A2F_;").
Proof. unfold strip, am_set_links. intros H. injection H. auto 10. Qed.

Lemma strip_stride a b : ltac2:(tb__ "0|0|
S0S7S6Va;A1S6Vb;A1A3S0S1fSfVa;A1SfVb;A1A3F_;").
Proof. intros H. apply strip_fields in H. unfold stride_of. destruct H as (_&_&_&->&->&->&_). reflexivity. Qed.

Lemma strip_extent a b : ltac2:(tb__ "0|0|
S0S7S6Va;A1S6Vb;A1A3S0S1fS21Va;A1S21Vb;A1A3F_;").
Proof. intros H. unfold group_extent. rewrite (strip_stride _ _ H). apply strip_fields in H. destruct H as (_&_&_&->&_). reflexivity. Qed.

Lemma strip_slot_start a b i : ltac2:(tb__ "0|0|
S0S7S6Va;A1S6Vb;A1A3S0S8S1bVa;Vi;A2S1bVb;Vi;A2A3F_;").
Proof. intros H. unfold slot_start. rewrite (strip_stride _ _ H). apply strip_fields in H. destruct H as (->&_). reflexivity. Qed.

Lemma strip_nth_slot a b i : ltac2:(tb__ "0|0|
S0S7S6Va;A1S6Vb;A1A3S0S1cSbVa;Vi;A2SbVb;Vi;A2A3F_;").
Proof. intros H. unfold nth_slot. apply strip_fields in H. destruct H as (_&_&_&_&_&_&_&->). reflexivity. Qed.

Lemma strip_allocated a b i : ltac2:(tb__ "0|0|
S0S7S6Va;A1S6Vb;A1A3S0S35S23Va;Vi;A2S23Vb;Vi;A2A3F_;").
Proof. intros H. unfold allocated. apply strip_fields in H. destruct H as (_&->&->&_). reflexivity. Qed.

Lemma strip_hdr_byte3 a b i fr : ltac2:(tb__ "0|0|
S0S7S6Va;A1S6Vb;A1A3S0S1fS27Va;Vi;Vfr;A3S27Vb;Vi;Vfr;A3A3F_;").
Proof. intros H. unfold hdr_byte3, rsv_code. rewrite (strip_stride _ _ H). reflexivity. Qed.

Lemma strip_hdr_off16 a b i fr : ltac2:(tb__ "0|0|
S0S7S6Va;A1S6Vb;A1A3S0S1fS28Va;Vi;Vfr;A3S28Vb;Vi;Vfr;A3A3F_;").
Proof. intros H. unfold hdr_off16. rewrite (strip_stride _ _ H). reflexivity. Qed.

Lemma strip_set_links pr nx am : ltac2:(tb__ "0|0|
S0S7S6S1dVpr;Vnx;Vam;A3A1S6Vam;A1A3").
Proof. reflexivity. Qed.

Lemma strip_refl am : ltac2:(tb__ "0|1|
S0S7S6Vam;A1M0G0A3").
Proof. reflexivity. Qed.

Lemma class_size_ge16 sc : ltac2:(tb__ "0|0|
S1S3dZ0Vsc;A2S3fVsc;Z30A2A2S3dZ10S1eVsc;A1A2F_;").
Proof.
  intros H. unfold class_size, znth.
  assert (G : forall n, (n < 48)%nat -> 16 <= UNIT * nth n size_classes 0).
  { intros n Hn. do 48 (destruct n as [|n]; [cbn; lia|]). lia. }
  apply G. lia.
Qed.

Lemma stride_pos X R s g am : ltac2:(tb__ "0|0|
S22VX;VR;Vs;Vg;Vam;A5S3dZ10SfVam;A1A2F_;").
Proof.
  intros (Gm & Gml & _ & Gc & _). unfold stride_of. destruct Gm as (Hl & _).
  destruct ((am_last am =? 0) && negb (am_maplen am =? 0)) eqn:E.
  - apply andb_prop in E as [_ E2]. destruct (am_maplen am =? 0) eqn:E3; [discriminate|].
    apply Z.eqb_neq in E3. unfold UNIT. lia.
  - destruct Gc as [(H63 & Hl0 & Hmp & _) | (Hsc & _)].
    + rewrite Hl0 in E. cbn [Z.eqb andb] in E. destruct (am_maplen am =? 0) eqn:E3; [|discriminate].
      apply Z.eqb_eq in E3. lia.
    + apply class_size_ge16. exact Hsc.
Qed.

Lemma extent_pos X R s g am : ltac2:(tb__ "0|0|
S22VX;VR;Vs;Vg;Vam;A5S3fZ0S21Vam;A1A2F_;").
Proof.
  intros G. pose proof (stride_pos _ _ _ _ _ G) as Hs. destruct G as ((Hl & _) & _).
  unfold group_extent, UNIT, IB. nia.
Qed.

Section Surgery.
  Variables (X X' : list sptr) (R R' : option (sptr * Z)) (U U' : Z -> Z) (s s' : astate).
  Hypothesis HI : ltac2:(tb__ "0|0|
S25VX;VR;VU;Vs;A4").
  Hypothesis ER : ltac2:(tb__ "0|1|
S37SaS0S33SaA1M0S24Vs;R2A2S34SaR1A2A3S0S1aS19R2A1S10A3S0G0S24Vs';R4A2S34SaR3A2A3F_;F_;Frg;Fk;").

  Hypothesis Cb : ltac2:(tb__ "0|0|
S8S7S20VX';Vs';R2R1A4S3S7S7S1S20VX;Vs;R4R1A4S0S7S6R3A1S6R1A1A3A2Lam;A2F_;Fam';Fp;").

  Hypothesis Cf : ltac2:(tb__ "0|0|
S8S7S20VX;Vs;R2R1A4S2S3S7S7S1S20VX';Vs';R4R1A4S0S7S6R1A1S6R3A1A3A2Lam';A2S1S0S35S26R3VX';A2S38A3S1fS0S33S9A1SdSbR3R1A2A1S36S9A1A3Fj;A2A2F_;Fam;Fp;").

  Hypothesis HR' : ltac2:(tb__ "0|0|
S2cVX';VR';Vs';A3").

  Hypothesis RR : ltac2:(tb__ "0|6|
S8S1fS7S20VX';Vs';R3R1A4S2S5S0S33S3bS8S1fA2M0A1M1VR;S34G0S3aS8S1fR4R3A4A2M2A3M3S0G1VR';G2A3M4A2S2S1G4S1S4G3A1S0S33S9A1SdSbR2R3A2A1S36S9A1A3M5A2A2S1G3S1S4G4A1G5S0S35S23R3R4A2S39A3F_;A2A2A2A2F_;Fam';Fi;Fp;").

  Lemma su_nested a a' : ltac2:(tb__ "0|0|
S0S7S6Va';A1S6Va;A1A3S2bVX;Vs;Va;A3S2bVX';Vs';Va';A3F_;F_;").
  Proof using Cf.
    intros E N Hm. apply strip_fields in E as (Em & _ & _ & El & Es & Eml & _ & _).
    rewrite Eml in Hm. destruct (N Hm) as [N63 (g' & b & i' & fr' & Hu & Hi & Hf & Hk & Hmem & Hsc & Hsc' & Hfit)].
    split; [congruence|].
    destruct (Cf _ _ Hu) as [(b' & Hu' & Eb) | [_ Hgone]].
    - exists g', b', i', fr'. pose proof (strip_fields _ _ Eb) as (Bm&_&_&Bl&Bs&_&_&Bsl).
      split; [exact Hu'|]. split; [rewrite Bl; exact Hi|].
      split; [unfold nth_slot in *; rewrite Bsl; exact Hf|]. split; [exact Hk|].
      split; [rewrite Em, (strip_slot_start _ _ _ Eb); exact Hmem|].
      split; [rewrite Es, Bs; exact Hsc|]. split; [rewrite Bs; exact Hsc'|].
      rewrite Es, El. exact Hfit.
    - exfalso. rewrite (Hgone i') in Hf. discriminate.
  Qed.

  Lemma su_mapped a a' : ltac2:(tb__ "0|0|
S0S7S6Va';A1S6Va;A1A3S2aVs;Va;A2S2aVs';Va';A2F_;F_;").
  Proof using ER.
    intros E M Hm. pose proof (strip_stride _ _ E) as Est. apply strip_fields in E as (Em & _ & _ & El & Es & Eml & _).
    rewrite Eml in Hm. destruct (M Hm) as (r & rg & H1 & H2 & H3 & H4 & H5 & H6). exists r, rg.
    rewrite Em, Eml, El, Est, Es. split; [exact H1|]. split; [apply ER; assumption|]. auto.
  Qed.

  Lemma su_group p am am' : ltac2:(tb__ "0|0|
S22VX;VR;Vs;Vp;Vam;A5S20VX';Vs';Vp;Vam';A4S0S7S6Vam';A1S6Vam;A1A3S22VX';VR';Vs';Vp;Vam';A5F_;F_;F_;").
  Proof using Cf ER RR.
    intros G Hu E. pose proof G as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
    pose proof (strip_fields _ _ E) as (Em & Eav & Efr & El & Es & Eml & Eai & Esl).
    pose proof (strip_stride _ _ E) as Est.
    split.
    { unfold masks_ok in *. rewrite El, Eai, Esl, Eav, Efr. exact Gm. }
    split; [rewrite Eml; exact Gml|].
    split.
    { intros i Hi. rewrite El in Hi. pose proof (Gsl i Hi) as (S1 & S2 & S3).
      unfold slot_ok. rewrite (strip_nth_slot _ _ i E), Eml.
      split; [exact S1|]. split; [exact S2|].
      pose proof (RR p i am' Hu) as RRi. rewrite (strip_nth_slot _ _ i E), (strip_allocated _ _ i E) in RRi.
      destruct (ss_fr (nth_slot am i)) as [fr|].
      - destruct S3 as (A1 & A2 & A3 & A4). rewrite (strip_allocated _ _ i E).
        split; [exact A1|]. split.
        { destruct RRi as [RRi | [(_ & _ & RRi) | (RRi & RRi' & _)]]; [ | discriminate | exact RRi'].
          intros H. apply A2. apply RRi. exact H. }
        split.
        { unfold frame_ok in *. rewrite Est, (strip_hdr_off16 _ _ i fr E). exact A3. }
        rewrite (strip_hdr_byte3 _ _ i fr E), (strip_hdr_off16 _ _ i fr E). exact A4.
      - rewrite (strip_allocated _ _ i E).
        destruct RRi as [RRi | [(RRi & _) | (_ & _ & RRi)]].
        + destruct S3 as [S3|S3]; [left; exact S3 | right; apply RRi; exact S3].
        + right. exact RRi.
        + left. apply RRi. reflexivity. }
    split.
    { unfold class_ok in *. rewrite Es, El, Eml, Eav, Efr, Est, (strip_allocated _ _ 0 E), (strip_nth_slot _ _ 0 E).
      destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & C6) | C]; [left | right; exact C].
      repeat split; auto.
      destruct C6 as [C6 | C6]; [| right; exact C6].
      pose proof (RR p 0 am' Hu) as [RRi | [(RRi & _) | (_ & RRn & RRi)]].
      - left. apply RRi. exact C6.
      - left. exact RRi.
      -
        rewrite (strip_nth_slot _ _ 0 E), (strip_allocated _ _ 0 E) in RRi.
        destruct (ss_fr (nth_slot am 0)) as [fr|] eqn:Ef.
        + right. pose proof (Gsl 0 ltac:(lia)) as (_ & _ & S3). rewrite Ef in S3.
          exists fr. split; [reflexivity|].
          destruct S3 as (_ & HR2 & _). exfalso. exact (HR2 C6).
        + exfalso. specialize (RRi eq_refl). unfold allocated in RRi. rewrite C4, C5 in RRi. cbn in RRi.
          rewrite Z.lor_0_l, Z.bits_0 in RRi || (cbn in RRi). discriminate. }
    split; [eapply su_mapped; eauto | eapply su_nested; eauto].
  Qed.
End Surgery.

Section Surgery2.
  Variables (X X' : list sptr) (R R' : option (sptr * Z)) (U U' : Z -> Z) (s s' : astate).
  Hypothesis HI : ltac2:(tb__ "0|0|
S25VX;VR;VU;Vs;A4").
  Hypothesis ER : ltac2:(tb__ "0|1|
S37SaS0S33SaA1M0S24Vs;R2A2S34SaR1A2A3S0S1aS19R2A1S10A3S0G0S24Vs';R4A2S34SaR3A2A3F_;F_;Frg;Fk;").
  Hypothesis Cb : ltac2:(tb__ "0|0|
S8S7S20VX';Vs';R2R1A4S3S7S7S1S20VX;Vs;R4R1A4S0S7S6R3A1S6R1A1A3A2Lam;A2F_;Fam';Fp;").
  Hypothesis Cf : ltac2:(tb__ "0|0|
S8S7S20VX;Vs;R2R1A4S2S3S7S7S1S20VX';Vs';R4R1A4S0S7S6R1A1S6R3A1A3A2Lam';A2S1S0S35S26R3VX';A2S38A3S1fS0S33S9A1SdSbR3R1A2A1S36S9A1A3Fj;A2A2F_;Fam;Fp;").
  Hypothesis HR' : ltac2:(tb__ "0|0|
S2cVX';VR';Vs';A3").
  Hypothesis RR : ltac2:(tb__ "0|6|
S8S1fS7S20VX';Vs';R3R1A4S2S5S0S33S3bS8S1fA2M0A1M1VR;S34G0S3aS8S1fR4R3A4A2M2A3M3S0G1VR';G2A3M4A2S2S1G4S1S4G3A1S0S33S9A1SdSbR2R3A2A1S36S9A1A3M5A2A2S1G3S1S4G4A1G5S0S35S23R3R4A2S39A3F_;A2A2A2A2F_;Fam';Fi;Fp;").

  Lemma su_groups : ltac2:(tb__ "0|0|
S8S7S20VX';Vs';R2R1A4S22VX';VR';Vs';R3R2A5F_;Fam';Fp;").
  Proof using Cb Cf ER HI RR.
    intros p am' Hu. destruct (Cb _ _ Hu) as (am & Hu0 & E).
    eapply su_group; eauto. apply (inv_groups HI). exact Hu0.
  Qed.

  Lemma su_inside a a' b b' : ltac2:(tb__ "0|3|
S0S7S6Va';A1S6Va;A1A3S0S7S6Vb';A1S6Vb;A1A3S29VX;Vs;Va;Vb;A4S2S29VX';Vs';Va';Vb';A4S3S8S8S3S7S7S1S20VX;Vs;R2R1A4S1S0S35S26R2VX';A2S38A3S1S1fS0S33S9A1SdSbR2R1A2A1S36S9A1A3Fj;S1S3dS17ScR1A1M0A1M1S17ScVa;A1A1M2A2S1S3dS3eG2S21Va;A1A2S3eG1S21R1A1A2A2S1S0S1fSeR1A1Z0A3S0S37S18G0A1S18ScVb;A1A1A3A2A2A2A2A2A2Lac;A2Lc;A2A2F_;F_;F_;").
  Proof using Cf.
    intros Ea Eb (j & fr & c & ac & Hj & Hfr & Hk & Hc & Hml & Hmem & Hlo & Hhi & Hfit).
    destruct (Cf _ _ Hc) as [(ac' & Hc' & Ec) | [Hg Hnone]].
    - left. pose proof (strip_fields _ _ Ec) as (Cm&_&_&_&_&Cml&_&_).
      pose proof (strip_fields _ _ Eb) as (Bm&_&_&Bl&_&_&_&Bsl).
      pose proof (strip_fields _ _ Ea) as (Am&_).
      exists j, fr, c, ac'. split; [rewrite Bl; exact Hj|]. split; [unfold nth_slot in *; rewrite Bsl; exact Hfr|].
      split; [exact Hk|]. split; [exact Hc'|]. split; [rewrite Cml; exact Hml|].
      split; [rewrite Cm, (strip_slot_start _ _ _ Eb); exact Hmem|].
      split; [rewrite Cm, Am; exact Hlo|].
      split; [rewrite Am, Cm, (strip_extent _ _ Ea), (strip_extent _ _ Ec); exact Hhi|].
      rewrite (strip_extent _ _ Ec). exact Hfit.
    - right. exists c, ac. repeat split; auto.
      rewrite Hmem. unfold slot_start. destruct (am_mem b); reflexivity.
  Qed.

  Lemma su_laminar : laminar X' s'.
  Proof using Cb Cf HI.
    intros p1 a1' p2 a2' H1 H2 Hne Hr.
    destruct (Cb _ _ H1) as (a1 & U1 & E1). destruct (Cb _ _ H2) as (a2 & U2 & E2).
    pose proof (strip_fields _ _ E1) as (M1&_). pose proof (strip_fields _ _ E2) as (M2&_).
    assert (Hgone : forall a a' pa c ac, usedX X s pa a -> usedX X' s' pa a' -> strip a' = strip a ->
              usedX X s c ac -> memb c X' = true -> (forall j, ss_fr (nth_slot ac j) = None) ->
              poff (am_mem ac) <= poff (am_mem a) ->
              poff (am_mem a) + group_extent a <= poff (am_mem ac) + group_extent ac ->
              am_maplen ac = 0 -> prid (am_mem a) = prid (am_mem ac) -> False).
    { intros a a' pa c ac Ua Ua' Ea Uc Xc Fc Lo Hi Mc Pr.
      assert (Hpc : pa <> c).
      { intros ->. pose proof (usedX_MT _ _ _ _ Ua') as [_ M]. rewrite M in Xc. discriminate. }
      pose proof (extent_pos _ _ _ _ _ (inv_groups HI pa a Ua)) as Pa.
      destruct (inv_laminar HI pa a c ac Ua Uc Hpc Pr) as [D | [I | I]].
      - unfold spans_disjoint in D. lia.
      - destruct I as (j & fr & _ & _ & _ & Hfr & _). rewrite (Fc j) in Hfr. discriminate.
      - destruct I as (j & fr & c2 & ac2 & Hj & Hfr & Hk & Uc2 & Ml2 & Mem2 & Lo2 & Hi2 & _).

        pose proof (stride_pos _ _ _ _ _ (inv_groups HI pa a Ua)) as Sp.
        unfold slot_start in Mem2. rewrite Mem2 in Lo2. destruct (am_mem a) as [ra oa]. cbn [poff padd] in Lo2, Lo, Hi.
        assert (0 <= stride_of a * j) by (apply Z.mul_nonneg_nonneg; lia).
        unfold UNIT in Lo2. lia. }
    destruct (inv_laminar HI p1 a1 p2 a2 U1 U2 Hne ltac:(rewrite <- M1, <- M2; exact Hr)) as [D | [I | I]].
    - left. unfold spans_disjoint in *. rewrite M1, M2, (strip_extent _ _ E1), (strip_extent _ _ E2). exact D.
    - destruct (su_inside _ _ _ _ E1 E2 I) as [I' | (c & ac & Uc & Xc & Fc & Lo & Hi & Mc)]; [right; left; exact I'|].
      exfalso. destruct Mc as [Mc Pc]. eapply (Hgone a1 a1' p1 c ac); eauto.
      rewrite Pc, <- M1, <- M2. exact Hr.
    - destruct (su_inside _ _ _ _ E2 E1 I) as [I' | (c & ac & Uc & Xc & Fc & Lo & Hi & Mc)]; [right; right; exact I'|].
      exfalso. destruct Mc as [Mc Pc]. eapply (Hgone a2 a2' p2 c ac); eauto.
      rewrite Pc, <- M1, <- M2. symmetry. exact Hr.
  Qed.

  Lemma su_maps : maps_unique X' s'.
  Proof using Cb HI.
    intros p1 a1' p2 a2' H1 H2 Hm1 Hm2 Hr.
    destruct (Cb _ _ H1) as (a1 & U1 & E1). destruct (Cb _ _ H2) as (a2 & U2 & E2).
    pose proof (strip_fields _ _ E1) as (M1&_&_&_&_&L1&_). pose proof (strip_fields _ _ E2) as (M2&_&_&_&_&L2&_).
    eapply (inv_maps HI p1 a1 p2 a2); eauto; try lia. congruence.
  Qed.

  Lemma su_partial : partial_unique X' s'.
  Proof using Cb HI.
    intros p1 a1' p2 a2' H1 H2 Hsc Hp1 Hp2.
    destruct (Cb _ _ H1) as (a1 & U1 & E1). destruct (Cb _ _ H2) as (a2 & U2 & E2).
    pose proof (strip_fields _ _ E1) as (_&_&_&L1&S1&_&A1&_). pose proof (strip_fields _ _ E2) as (_&_&_&L2&S2&_&A2&_).
    eapply (inv_partial HI p1 a1 p2 a2); eauto; try lia; congruence.
  Qed.

  Theorem Inv_surgery : ltac2:(tb__ "0|0|
S2fVs';A1S30Vs';A1S2eVs';A1S2dVX';Vs';A2S31VX';VR';Vs';A3S32VX';VU';Vs';A3S25VX';VR';VU';Vs';A4F_;F_;F_;F_;F_;F_;").
  Proof using Cb Cf ER HI HR' RR.
    intros C K A XO RG US.
    split; [exact C|]. split; [exact K|]. split; [exact A|].
    split; [exact XO|]. split; [apply su_groups|]. split; [apply su_laminar|]. split; [apply su_maps|].
    split; [exact RG|]. split; [exact US|]. split; [exact HR' | apply su_partial].
  Qed.
End Surgery2.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "ameta"; "frame"; "am_sc"; "am_mem"; "ss_fr"; "MUsed"; "am_last"; "am_maplen"; "nth_slot"; "am_next"; "am_prev"; "am_freed"; "am_avail"; "mslot"; "region"; "bit"; "fkind"; "fr_kind"; "ones"; "ss_hdr"; "upd_slot"; "FUser"; "HActive"; "am_set_freed"; "am_set_links"; "class_size"; "slot_start"; "stride_of"; "FGroup"; "NEST_FUEL"; "RkMap"; "activate_group"; "am_aidx"; "am_set_avail"; "dequeue"; "forget_frame"; "fr_n"; "free"; "mkSlot"; "nontrivial_free"; "okay_to_free"; "page_round"; "prid"; "queue"; "release_slot"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "slotst"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "False"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "usedX"; "Inv"; "active_hd"; "contrib"; "MT"; "class_sum"; "frame_ptr"; "keys"; "region_of"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "lor"; "eqb"; "land"; "ldiff"; "ltb"; "sub"; "testbit"; "to_nat"; "@Corelib.Init.Datatypes"; "prod"; "Some"; "pair"; "option"; "None"; "unit"; "bool"; "cons"; "nat"; "tt"; "app"; "list"; "false"; "andb"; "fst"; "nil"; "snd"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase"; "itok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "ub_same"; "ublist"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree"; "corr"; "fneed"; "nf_post"; "@Stdlib.Lists.List"; "In"; "NoDup"; "fold_right"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery"; "strip"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRingOps"; "same_but_metas_heads"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame
  MallocWfRingOps MallocWfSurgery MallocWfRings MallocWfMeta MallocWfSlot MallocWfGeom MallocWfArith MallocWfGroup.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Lemma Inv_U_ext X R U U' s : ltac2:(tb__ "0|0|
S3bS35S45Z0R1A2S46R1Z30A2A2S34S3bVU';R2A1VU;R2A1A3F_;Fc;S3dVX;VR;VU;Vs;A4S3dVX;VR;VU';Vs;A4F_;F_;").
Proof.
  intros HU HI. split; [exact (inv_ctx HI)|]. split; [exact (inv_keys HI)|]. split; [exact (inv_areas HI)|].
  pose proof (inv_meta HI) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|]. split; [exact M5|].
  split; [|exact (conj M7 M8)]. intros c Hc. rewrite (HU c Hc). apply M6. exact Hc.
Qed.

Lemma contrib_nonneg X R U s c q : ltac2:(tb__ "0|0|
S3dVX;VR;VU;Vs;A4S45Z0S3fVX;Vs;Vc;Vq;A4A2F_;").
Proof.
  intros HI. unfold contrib. destruct (MTX X s q) as [[| |am]|] eqn:E; try lia.
  destruct (am_sc am =? c); [|lia]. pose proof (inv_groups HI q am E) as ((M1 & _) & _). lia.
Qed.

Lemma fold_sum_nonneg (f : sptr -> Z) l : ltac2:(tb__ "0|2|
S0S69S0R1Vl;A3S45Z0M0Vf;R2A1M1A2F_;Fq;S45G0S6bS3bS0S0S3bS47G1R1A2Lacc;Lq;G0Vl;A5A2F_;").
Proof. induction l as [|x t IH]; intros H; cbn; [lia|]. pose proof (H x (or_introl eq_refl)). assert (0 <= fold_right (fun q acc => f q + acc) 0 t) by (apply IH; intros; apply H; right; assumption). lia. Qed.

Lemma class_sum_ge_contrib X R U s c g : ltac2:(tb__ "0|0|
S3dVX;VR;VU;Vs;A4S69S0Vg;S43Vs;A1A3S45S3fVX;Vs;Vc;Vg;A4S41VX;Vs;Vc;A3A2F_;F_;").
Proof.
  intros HI Hg. unfold class_sum.
  rewrite (fold_sum_delta (fun q => if sptr_eqb q g then 0 else contrib X s c q) (contrib X s c) g (keys s) (proj1 (inv_keys HI)) Hg).
  2:{ intros q Hq. destruct (sptr_eqb q g) eqn:E; [apply sptr_eqb_eq in E; contradiction | reflexivity]. }
  rewrite sptr_eqb_refl.
  assert (0 <= fold_right (fun q acc => (if sptr_eqb q g then 0 else contrib X s c q) + acc) 0 (keys s)).
  { apply fold_sum_nonneg. intros q _. destruct (sptr_eqb q g); [lia|]. eapply contrib_nonneg. exact HI. }
  lia.
Qed.

Lemma contrib_used X s c g am : ltac2:(tb__ "0|0|
S3cVX;Vs;Vg;Vam;A4S34S3bS3fVX;Vs;Vc;Vg;A4S56S3bL_;S49S4Vam;A1Vc;A2S47S8Vam;A1Z1A2Z0X56x2A3F_;").
Proof. intros Hu. unfold contrib. unfold usedX in Hu. rewrite Hu. reflexivity. Qed.

Lemma Inv_exempt X R U s g am : ltac2:(tb__ "0|3|
S3dVX;VR;VU;Vs;A4S3cVX;Vs;Vg;Vam;A4S3bS34S53S3A1S6SaVam;R1A2A1S54S3A1A3Fj;S34S53S0A1M0ScVam;A1S54S0A1M1A3S34G0SbVam;A1G1A3S0S3bS34S53S50S0S3bA2M2A1VR;S51G2S52S0S3bR2R1A4A2A3S34S0R3Vg;A3F_;Fi;Fp;S3dS57S0Vg;VX;A3S54G2A1S3bS47VU;R1A1S3fVX;Vs;R1Vg;A4A2Lc;Vs;A4F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hu Hfr Hp Hn HRg.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. pose proof (MT_Some_In_keys _ _ _ Mg) as Kg.
  assert (EMTX : forall q, q <> g -> MTX (g :: X) s q = MTX X s q).
  { intros q Hq. unfold MTX. rewrite memb_cons. destruct (sptr_eqb q g) eqn:E; [apply sptr_eqb_eq in E; contradiction | reflexivity]. }
  assert (EMg : MTX (g :: X) s g = None) by (unfold MTX; rewrite memb_cons, sptr_eqb_refl; reflexivity).
  assert (Bwd : forall p a, usedX (g :: X) s p a -> p <> g /\ usedX X s p a).
  { intros p a Ha. destruct (sptr_eq_dec p g) as [->|Hne]; [unfold usedX in Ha; rewrite EMg in Ha; discriminate|].
    split; [exact Hne|]. unfold usedX in *. rewrite <- (EMTX p Hne). exact Ha. }
  assert (Fwd : forall p a, usedX X s p a -> p <> g -> usedX (g :: X) s p a).
  { intros p a Ha Hne. unfold usedX in *. rewrite (EMTX p Hne). exact Ha. }
  destruct (inv_rings HI) as (F & A & D).
  eapply (Inv_surgery X (g :: X) R None U _ s s HI).
  - intros k rg Hk _. exact Hk.
  - intros p a' Ha'. destruct (Bwd p a' Ha') as [Hne Ha]. exists a'. split; [exact Ha | reflexivity].
  - intros p a Ha. destruct (sptr_eq_dec p g) as [->|Hne].
    + right. pose proof (usedX_fun _ _ _ _ _ Ha Hu) as ->. split; [|exact Hfr]. rewrite memb_cons, sptr_eqb_refl. reflexivity.
    + left. exists a. split; [apply Fwd; assumption | reflexivity].
  - intros p i E. discriminate.
  - intros p i a' Ha'. left. destruct (Bwd p a' Ha') as [Hne _]. split; [intros E; exfalso; exact (Hne (HRg p i E)) | discriminate].
  - exact (inv_ctx HI).
  - exact (inv_keys HI).
  - exact (inv_areas HI).
  - intros x [<-|Hx].
    + split; [exact Kg|]. rewrite Mg. auto.
    + exact (inv_X HI x Hx).
  - split; [|split].
    + destruct F as (ms & Rg & Hall). exists ms. split.
      * eapply ring_ok_ext; [|exact Rg]. intros q _. unfold flinks. destruct (sptr_eq_dec q g) as [->|Hne].
        -- rewrite EMg. unfold MTX. rewrite NXg, Mg. reflexivity.
        -- rewrite (EMTX q Hne). reflexivity.
      * intros q pr nx Hq. destruct (sptr_eq_dec q g) as [->|Hne]; [rewrite EMg in Hq; discriminate|].
        rewrite (EMTX q Hne) in Hq. eapply Hall. exact Hq.
    + intros c Hc. destruct (A c Hc) as (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
      assert (Hgn : am_sc am = c -> ~ In g ms).
      { intros Hs Hin. apply (Mem g am Hu Hs) in Hin. apply Hin. rewrite Hp, Hn. reflexivity. }
      split.
      { eapply ring_ok_ext; [|exact Rg]. intros q Hq. unfold alinks. destruct (sptr_eq_dec q g) as [->|Hne].
        - rewrite EMg. unfold MTX. rewrite NXg, Mg. destruct (am_sc am =? c) eqn:E; [|reflexivity].
          exfalso. apply Z.eqb_eq in E. exact (Hgn E Hq).
        - rewrite (EMTX q Hne). reflexivity. }
      split; [intros q a Hq; destruct (Bwd q a Hq) as [_ Ha]; apply Mem; exact Ha|].
      split; [intros q a Hq; destruct (Bwd q a Hq) as [_ Ha]; apply Full; exact Ha|].
      split; [intros q a Hq; destruct (Bwd q a Hq) as [_ Ha]; apply Q1; exact Ha|].
      intros q a Hq Hs Hin Hnh _. destruct (Bwd q a Hq) as [Hne Ha]. apply (Q2 q a Ha Hs Hin Hnh).
      intros i E. exact (Hne (HRg q i E)).
    + intros q a Hq. destruct (Bwd q a Hq) as [_ Ha]. exact (D q a Ha).
  - intros c Hc. rewrite (inv_usage HI c Hc). unfold class_sum.
    rewrite (fold_sum_delta (contrib X s c) (contrib (g :: X) s c) g (keys s) (proj1 (inv_keys HI)) Kg).
    2:{ intros q Hq. unfold contrib. rewrite (EMTX q Hq). reflexivity. }
    replace (contrib (g :: X) s c g) with 0 by (unfold contrib; rewrite EMg; reflexivity). lia.
Qed.

Lemma usedX_cons_inv X g s q a : ltac2:(tb__ "0|0|
S3cS57S0Vg;VX;A3Vs;Vq;Va;A4S35S36S34S0Vq;Vg;A3A1S3cVX;Vs;Vq;Va;A4A2F_;").
Proof.
  intros Hu. pose proof (usedX_MT _ _ _ _ Hu) as [M N]. rewrite memb_cons in N. apply orb_false_elim in N as [E N].
  apply sptr_eqb_neq in E. split; [exact E|]. apply usedX_intro; assumption.
Qed.

Lemma usedX_cons X g s q a : ltac2:(tb__ "0|0|
S3cVX;Vs;Vq;Va;A4S36S34S0Vq;Vg;A3A1S3cS57S0Vg;VX;A3Vs;Vq;Va;A4F_;F_;").
Proof.
  intros Hu Hne. pose proof (usedX_MT _ _ _ _ Hu) as [M N]. apply usedX_intro; [|exact M].
  rewrite memb_cons, N. destruct (sptr_eqb q g) eqn:E; [apply sptr_eqb_eq in E; contradiction | reflexivity].
Qed.

Lemma in_split_sptr (g : sptr) ms : ltac2:(tb__ "0|1|
S69S0Vg;Vms;A3S6aS0Vms;A2S37S5bS0A1M0G0S37G0G0S35S34G0Vms;S5aS0R2S57S0Vg;R1A3A3A3S35S36S69S0Vg;R2A3A1S36S69S0Vg;R1A3A1A2A2Ll2;A2Ll1;A2F_;F_;").
Proof.
  intros Hin Hnd. destruct (in_split _ _ Hin) as (l1 & l2 & ->). exists l1, l2. split; [reflexivity|].
  apply NoDup_remove_2 in Hnd. rewrite in_app_iff in Hnd. tauto.
Qed.

Lemma dequeue_exempt_spec X R U s sc g am (Q : unit * astate -> Prop) : ltac2:(tb__ "0|a|
S3dVX;VR;VU;Vs;A4S35S45Z0M0Vsc;A2S46Vsc;Z30A2A2S3cVX;Vs;Vg;Vam;A4S34S3bS4Vam;A1Vsc;A3S36S34S50S53S0A1M1G1A2S52G1G1ScVam;A1SbVam;A1A4S52G1G1S54S0A1M2G2A4A3A1S3bS34S53S3A1S6SaVam;R1A2A1S54S3A1A3Fj;S0S3bS34S53S50S0S3bA2M3A1VR;S51G3S52S0S3bR2R1A4A2A3S34S0R3Vg;A3M4F_;Fi;Fp;S1S3dS57S0Vg;VX;A3M5S54G3A1S3bS47VU;R1A1S3fVX;Vs;R1Vg;A4A2Lc;R1A4S6eVs;R2A2S34S53SfA1M6S40R3Vg;A2S51SfS7S1aG2G2Vam;A3A1A2A3S3bS45G0R1A2S36S34S3bR2Vsc;A3A1S34G1S3eR7R3A2S3eVs;R3A2A3F_;F_;Fc;S0S2S3cVX;Vs;R2R1A4S36S34S3bS4R2A1Vsc;A3A1F_;Fa;S36S34S0R2Vg;A3A1M7S34G6S40R8R3A2S40Vs;R3A2A3F_;F_;Fq;S0S2S3cG5R8R2R1A4S35S36G4A1S37S2S2S35S3cVX;Vs;R4R1A4S34S2S6cR3A1S6cR1A1A3A2La;A2A2F_;Fa';Fq;S36S34G1S3eVs;Vsc;A2M8S51S0Vg;A2A3M9A1S34G1S3eR8Vsc;A2G8A3F_;G9S38S34G1S3eR9Vsc;A2G2A3S37S0S0S37S2S2S35S34G1S3eRbVsc;A2S51S0R2A2A3S35G7S35S3cG5RbR2R1A4S35S34S3bS4R1A1Vsc;A3S34S3bSeR1A1G0A3A2A2A2A2Lah;A2Lh;A2A2F_;S64Vs;R9A2VQ;S52S55S1S59RaA4A1F_;F_;F_;F_;F_;F_;F_;F_;F_;Fs';S62S50S55S1A2S24S18Vsc;A1Vg;Vs;A3VQ;A3F_;F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hsc Hu Hsca Hlinked Hfr HRg HQ.
  destruct (inv_rings HI) as (F & A & D).
  destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. pose proof (MT_Some_In_keys _ _ _ Mg) as Kg.
  pose proof (inv_ctx HI) as C. destruct C as (Clen & Crest).
  assert (Hin : In g ms) by (apply (Mem g am Hu Hsca); exact Hlinked).
  destruct (in_split_sptr g ms Hin (proj1 (proj1 Rg))) as (l1 & l2 & Ems & Hn1 & Hn2).
  assert (Cyc : cycle_ok (alinks X s sc) (g :: l2 ++ l1)).
  { change (g :: l2 ++ l1) with ((g :: l2) ++ l1). apply cycle_rotate_n. rewrite <- Ems. exact (proj1 Rg). }
  set (rest := l2 ++ l1) in Cyc.
  assert (Hms : forall q, In q ms <-> q = g \/ In q rest).
  { intros q. rewrite Ems. subst rest. rewrite !in_app_iff. cbn [In]. split; intros H; decompose [or] H; subst; auto 6. }
  assert (SC : forall q, In q (g :: rest) -> exists a, usedX X s q a /\ am_sc a = sc).
  { intros q Hq. eapply ring_members_used; [exact Rg|]. apply Hms. destruct Hq as [<-|Hq]; auto. }
  assert (SX : forall q, In q (g :: rest) -> memb q X = false).
  { intros q Hq. destruct (SC q Hq) as (a & Hqu & _). exact (proj2 (usedX_MT _ _ _ _ Hqu)). }
  eapply (dequeue_op (HActive sc) g s (MUsed am) rest (alinks X s sc)).
  - exact Mg.
  - exact Cyc.
  - intros q l _ Hl. eapply LK_of_alinks. exact Hl.
  - cbn. rewrite Clen. lia.
  - intros s' Sb Hse Hhd' Mg' Mother Mrest.
    assert (RL : relinked s s' (g :: rest)).
    { split.
      - exact Mother.
      - intros q Hq. destruct Hq as [<- | Hq].
        + exists (MUsed am), None, None. split; [exact Mg|]. split; [exact Mg'|]. discriminate.
        + destruct (SC q (or_intror Hq)) as (a & Hqu & _). pose proof (usedX_MT _ _ _ _ Hqu) as [Mq _].
          eexists (MUsed a), _, _. split; [exact Mq|]. split; [apply (Mrest q (MUsed a) Hq Mq) | discriminate]. }
    pose proof (rl_used_bwd X s s' _ RL) as Bwd. pose proof (rl_used_fwd X s s' _ RL) as Fwd.
    pose proof Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&Erg&_&EK).
    destruct Hse as (Hoth & Hfmh & Hlen).
    assert (EH : forall c, 0 <= c -> c <> sc -> active_hd s' c = active_hd s c).
    { intros c Hc Hne. unfold active_hd. apply Hoth. intros sc0 E0. injection E0 as <-. lia. }

    assert (Bwd' : forall q a', usedX (g :: X) s' q a' -> q <> g /\ exists a, usedX X s q a /\ strip a' = strip a).
    { intros q a' Hq. destruct (usedX_cons_inv _ _ _ _ _ Hq) as [Hne Hq']. split; [exact Hne|]. apply Bwd. exact Hq'. }
    assert (Same : forall q a', usedX (g :: X) s' q a' -> ~ In q (g :: rest) -> usedX X s q a').
    { intros q a' Hq Hnin. destruct (usedX_cons_inv _ _ _ _ _ Hq) as [Hne Hq']. apply (rl_used_same X s s' _ RL q a' Hnin). exact Hq'. }
    assert (NotS : forall q a', usedX (g :: X) s' q a' -> am_sc a' <> sc -> ~ In q (g :: rest)).
    { intros q a' Hq Hs Hi. destruct (SC q Hi) as (a & Hqu & Hqs). destruct (Bwd' q a' Hq) as (_ & a0 & Hq0 & E).
      pose proof (usedX_fun _ _ _ _ _ Hq0 Hqu) as ->. apply strip_fields in E as (_&_&_&_&Es&_). congruence. }

    assert (Hhd_old : active_hd s sc = hd_error ms) by exact (proj2 Rg).
    assert (Hhd_new : active_hd s' sc = hd_error (l1 ++ l2)).
    { cbn [head_of] in Hhd'. rewrite Hhd'. rewrite Hhd_old, Ems. subst rest.
      destruct l1 as [|h1 l1']; cbn.
      - destruct l2 as [|y l2']; cbn; [reflexivity|]. rewrite sptr_eqb_refl. reflexivity.
      - destruct (l2 ++ h1 :: l1') as [|y t] eqn:E; [destruct l2; discriminate|].
        destruct (sptr_eqb h1 g) eqn:E2; [|reflexivity]. apply sptr_eqb_eq in E2. subst h1. exfalso. apply Hn1. left. reflexivity. }
    assert (Rg' : ring_ok (alinks (g :: X) s' sc) (active_hd s' sc) (l1 ++ l2)).
    { rewrite Hhd_new. split; [|reflexivity].
      apply cycle_rotate_n. fold rest.
      assert (Cyc' : rest = [] \/ cycle_ok (alinks (g :: X) s' sc) rest).
      { destruct rest as [|y rest'] eqn:Er; [left; reflexivity | right].
        eapply (cycle_remove_first (alinks X s sc) (alinks (g :: X) s' sc) g (y :: rest')).
        - exact Cyc.
        - discriminate.
        - intros z pr nx Hz Lz. destruct (alinks_used _ _ _ _ _ Lz) as (a & Hzu & Hzs & El).
          pose proof (usedX_MT _ _ _ _ Hzu) as [Mz NXz].
          pose proof (Mrest z (MUsed a) Hz Mz) as Mz'. cbn [with_links] in Mz'.
          assert (Hzg : z <> g).
          { intros ->. destruct Cyc as [Hnd _]. inversion Hnd; subst. contradiction. }
          unfold alinks, MTX. rewrite memb_cons, NXz. replace (sptr_eqb z g) with false by (symmetry; apply sptr_eqb_neq; exact Hzg).
          cbn [orb]. rewrite Mz'. cbn [am_sc am_prev am_next am_set_links].
          rewrite Hzs, Z.eqb_refl. injection El as -> ->. cbn [fst snd links_of]. reflexivity. }
      destruct Cyc' as [-> | Cyc']; [split; [constructor | exact I] | exact Cyc']. }
    apply HQ.
    + eapply (Inv_surgery X (g :: X) R None U _ s s' HI).
      * intros k rg Hk _. unfold region_of in *. rewrite Erg. exact Hk.
      * intros p a' Hp. destruct (Bwd' p a' Hp) as [_ H]. exact H.
      * intros p a Hp. destruct (sptr_eq_dec p g) as [->|Hne].
        -- right. pose proof (usedX_fun _ _ _ _ _ Hp Hu) as ->. split; [rewrite memb_cons, sptr_eqb_refl; reflexivity | exact Hfr].
        -- left. destruct (Fwd _ _ Hp) as (a' & Hp' & E). exists a'. split; [apply usedX_cons; assumption | exact E].
      * intros p i E. discriminate.
      * intros p i a' Hp. left. destruct (Bwd' p a' Hp) as [Hne _]. split; [intros E; exfalso; exact (Hne (HRg p i E)) | discriminate].
      * apply (sbmh_ctx s s' Sb); [exact Hlen | | exact (inv_ctx HI)].
        intros Hi. exfalso. destruct Crest as (_&_&_&_&_&_&_&_&_&_&Ci&_). destruct (Ci Hi) as (Hm & _).
        unfold keys in Kg. rewrite Hm in Kg. exact Kg.
      * apply (sbmh_keys s s' Sb). exact (inv_keys HI).
      * apply (sbmh_areas s s' Sb). exact (inv_areas HI).
      * intros x [<-|Hx].
        -- split; [rewrite EK; exact Kg|]. rewrite Mg'. cbn. split; [reflexivity|]. split; [reflexivity|].
           intros i. unfold nth_slot in *. cbn. apply Hfr.
        -- destruct (inv_X HI x Hx) as [Kx Mx]. split; [rewrite EK; exact Kx|].
           rewrite Mother; [exact Mx|]. intros Hi. pose proof (SX x Hi) as E. apply memb_false_notIn in E. exact (E Hx).
      *
        split.
        { destruct F as (fms & FR & Fall). exists fms. split.
          - rewrite (Hfmh ltac:(discriminate)).
            eapply ring_ok_ext; [|exact FR]. intros q _.
            unfold flinks. destruct (sptr_eq_dec q g) as [->|Hne].
            + unfold MTX. rewrite memb_cons, sptr_eqb_refl, NXg, Mg. reflexivity.
            + replace (MTX (g :: X) s' q) with (MTX X s' q) by (unfold MTX; rewrite memb_cons; replace (sptr_eqb q g) with false by (symmetry; apply sptr_eqb_neq; exact Hne); reflexivity).
              fold (flinks X s' q). fold (flinks X s q). eapply rl_flinks_used; eauto.
          - intros q pr nx Hq. apply (Fall q pr nx). unfold MTX in *. rewrite memb_cons in Hq.
            destruct (sptr_eqb q g) eqn:Eqg; [discriminate|]. cbn [orb] in Hq. destruct (memb q X); [discriminate|].
            destruct (rl_MT_cases s s' _ RL q) as [E | (x & p' & n' & A1 & B1 & C1 & D1)]; [rewrite <- E; exact Hq|].
            exfalso. destruct (SC q D1) as (a & Hqu & _). pose proof (usedX_MT _ _ _ _ Hqu) as [Mq _].
            rewrite Mq in A1. injection A1 as <-. rewrite B1 in Hq. cbn in Hq. discriminate. }
        split.
        { intros c Hc. destruct (Z.eq_dec c sc) as [->|Hne].
          - exists (l1 ++ l2). split; [exact Rg'|].
            assert (InNew : forall q, In q (l1 ++ l2) <-> In q rest) by (intros q; subst rest; rewrite !in_app_iff; tauto).
            split.
            { intros q a' Hq Hs'. destruct (Bwd' q a' Hq) as (Hne & a & Hqu & E).
              destruct (in_dec sptr_eq_dec q rest) as [Hi|Hni].
              + split; [intros _ | intros _; apply InNew; exact Hi].
                destruct (ring_links _ _ _ _ Rg' (proj2 (InNew q) Hi)) as (pr & nx & L).
                unfold alinks in L. pose proof Hq as Hq2. unfold usedX in Hq2. rewrite Hq2, Hs', Z.eqb_refl in L.
                injection L as -> ->. discriminate.
              + assert (Hq0 : usedX X s q a') by (apply Same; [exact Hq | intros [E0|E0]; [exact (Hne (eq_sym E0)) | exact (Hni E0)]]).
                rewrite <- (Mem q a' Hq0 Hs'). rewrite InNew, Hms. split; [intros H; right; exact H | intros [E0|E0]; [exfalso; exact (Hne E0) | exact E0]]. }
            split.
            { intros q a' Hq Hs' Hnin. destruct (Bwd' q a' Hq) as (Hne & _).
              assert (Hni : ~ In q rest) by (intros Hi; apply Hnin; apply InNew; exact Hi).
              assert (Hq0 : usedX X s q a') by (apply Same; [exact Hq | intros [E0|E0]; [exact (Hne (eq_sym E0)) | exact (Hni E0)]]).
              apply (Full q a' Hq0 Hs'). rewrite Hms. intros [E0|E0]; [exact (Hne E0) | exact (Hni E0)]. }
            split.
            { intros q a' Hq Hs' Hav'. destruct (Bwd' q a' Hq) as (Hne & a & Hqu & E).
              pose proof (strip_fields _ _ E) as (_&Eav&_&_&Es&_). rewrite Eav in Hav'.
              pose proof (Q1 q a Hqu ltac:(congruence) Hav') as Hh.
              rewrite Hhd_new. rewrite Hhd_old, Ems in Hh. destruct l1 as [|h1 l1']; cbn in Hh |- *.
              - injection Hh as ->. exfalso. exact (Hne eq_refl).
              - exact Hh. }
            { intros q a' Hq Hs' Hiq Hnh _. destruct (Bwd' q a' Hq) as (Hne & a & Hqu & E).
              pose proof (strip_fields _ _ E) as (_&_&Efr&_&Es&_). rewrite Efr.
              apply (Q2 q a Hqu ltac:(congruence)).
              - apply Hms. right. apply InNew. exact Hiq.
              - rewrite Hhd_old, Ems. rewrite Hhd_new in Hnh. destruct l1 as [|h1 l1']; cbn in Hnh |- *.
                + intros E0. injection E0 as ->. exact (Hne eq_refl).
                + exact Hnh.
              - intros i E0. exact (Hne (HRg q i E0)). }
          - destruct (A c Hc) as (ms' & Rg2 & Mem2 & Full2 & Q12 & Q22). exists ms'.
            rewrite (EH c ltac:(lia) Hne). split.
            { eapply ring_ok_ext; [|exact Rg2]. intros q Hq.
              destruct (sptr_eq_dec q g) as [->|Hqg].
              - exfalso. destruct (ring_members_used _ _ _ _ _ g Rg2 Hq) as (a2 & Hu2 & Hs2). pose proof (usedX_fun _ _ _ _ _ Hu2 Hu) as ->. lia.
              - unfold alinks. replace (MTX (g :: X) s' q) with (MTX X s' q) by (unfold MTX; rewrite memb_cons; replace (sptr_eqb q g) with false by (symmetry; apply sptr_eqb_neq; exact Hqg); reflexivity).
                fold (alinks X s' c q). fold (alinks X s c q). eapply rl_alinks_other; eauto. }
            split; [|split; [|split]]; intros q a' Hq Hs';
              pose proof (NotS q a' Hq ltac:(lia)) as Hni; pose proof (Same q a' Hq Hni) as Hq0.
            + apply Mem2; [exact Hq0 | exact Hs'].
            + apply Full2; [exact Hq0 | exact Hs'].
            + apply Q12; [exact Hq0 | exact Hs'].
            + intros Hiq Hnh _. apply (Q22 q a' Hq0 Hs' Hiq Hnh). intros i E0. apply (HRg q i) in E0. subst q. apply Hni. left. reflexivity. }
        { intros q a' Hq H63. pose proof (NotS q a' Hq ltac:(lia)) as Hni. pose proof (Same q a' Hq Hni) as Hq0. exact (D q a' Hq0 H63). }
      *
        intros c Hc. rewrite (sbmh_usage_of _ _ c Sb), (inv_usage HI c Hc). unfold class_sum. rewrite EK.
        rewrite (fold_sum_delta (contrib X s c) (contrib (g :: X) s' c) g (keys s) (proj1 (inv_keys HI)) Kg).
        2:{ intros q Hq. rewrite <- (rl_contrib X s s' _ RL c q). unfold contrib, MTX. rewrite memb_cons.
            replace (sptr_eqb q g) with false by (symmetry; apply sptr_eqb_neq; exact Hq). reflexivity. }
        replace (contrib (g :: X) s' c g) with 0 by (unfold contrib, MTX; rewrite memb_cons, sptr_eqb_refl; reflexivity). lia.
    + exact Sb.
    + exact Mg'.
    + exact EH.
    + intros q Hq Hqg. apply Mother. intros Hi. destruct (SC q Hi) as (a & Hqu & Hqs). exact (Hq a Hqu Hqs).
    + exact Bwd'.
    + intros Hnh. rewrite Hhd_new. rewrite Hhd_old, Ems in Hnh |- *. destruct l1 as [|h1 l1']; cbn in Hnh |- *; [exfalso; apply Hnh; reflexivity | reflexivity].
    + intros Hh. rewrite Hhd_old, Ems in Hh. destruct l1 as [|h1 l1']; cbn in Hh.
      2:{ injection Hh as ->. exfalso. apply Hn1. left. reflexivity. }
      rewrite Hhd_new. cbn. destruct l2 as [|y l2']; [left; reflexivity | right].
      cbn. assert (Hy : In y ms) by (rewrite Ems; cbn; right; left; reflexivity).
      destruct (ring_members_used _ _ _ _ _ y Rg Hy) as (ay & Hyu & Hys).
      assert (Hyg : y <> g) by (intros ->; apply Hn2; left; reflexivity).
      destruct (Fwd _ _ Hyu) as (ay' & Hyu' & E). exists y, ay'.
      pose proof (strip_fields _ _ E) as (_&Eav&_&_&Es&_).
      split; [reflexivity|]. split; [exact Hyg|]. split; [apply usedX_cons; assumption|]. split; [congruence|].
      rewrite Eav. destruct (Z.eq_dec (am_avail ay) 0) as [E0|E0]; [exact E0|]. exfalso.
      pose proof (Q1 y ay Hyu Hys E0) as Hh'. rewrite Hhd_old, Ems in Hh'. cbn in Hh'. injection Hh' as ->. exact (Hyg eq_refl).
    + eapply ub_same_relinked; [exact RL | exact EK].
Qed.

Lemma drop_frame_Inv X U s g am i fr x : ltac2:(tb__ "0|7|
S3dVX;S54S50S0S3bA2M0A1VU;Vs;A4S3cVX;Vs;Vg;Vam;A4S35S45Z0M1Vi;A2S45Vi;S8Vam;A1A2A2S34S53S3A1M2S6SaVam;Vi;A2M3A1S51S3Vfr;A2A3S34S12S13Vfr;A1S1eA3S0S2S3cVX;Vs;R2R1A4S34S3bS9R2A1G1A3S36S34S0S5R3A1S1cVam;Vi;A2A3A1F_;F_;Fac;Fc;F_;S34G2S6Vx;A1S54S3A1A3S38S34S53S50S3bS3bA2M4A1M5S15Vx;A1M6S15G3A1A3S34G5G6S51G4S52S3bS3bZffG1A4A2A3A2S3dVX;S51G0S52S0S3bVg;Vi;A4A2VU;S63Vg;S7S16Vam;Vi;Vx;A3A1Vs;A3A4F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hu Hi Hfr Hchild Hxfr Hxhdr.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg].
  pose proof (inv_groups HI g am Hu) as G. pose proof G as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  pose proof Gm as (Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra).
  set (am1 := upd_slot am i x).
  assert (Hlen : (Z.to_nat i < length (am_slots am))%nat) by (rewrite Glen; lia).
  assert (NS : forall j, 0 <= j -> nth_slot am1 j = if j =? i then x else nth_slot am j).
  { intros j Hj. subst am1. apply nth_slot_upd_slot; [lia | exact Hj | exact Hlen]. }
  pose proof (Gsl i Hi) as (Si1 & Si2 & Si3). rewrite Hfr in Si3. destruct Si3 as (Hal & _ & Fok & Hhdr0).
  assert (GS : geom_same_upto X s am am1).
  { split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros j frj Hj0 Hj Hkj. rewrite NS by exact Hj0. destruct (j =? i) eqn:E; [|left; exact Hj].
    apply Z.eqb_eq in E. subst j. right. rewrite Hfr in Hj. injection Hj as <-. exact (Hchild Hkj). }
  assert (Hscr : am_sc am = 63 \/ (0 <= am_sc am < 48)).
  { destruct Gcl as [(C1 & _) | (C1 & _)]; [left; exact C1 | right; exact C1]. }
  eapply (Inv_used_update X None (Some (g, i)) U s g am am1 HI Hu GS).
  - split; reflexivity.
  - unfold masks_ok. subst am1. unfold upd_slot. cbn -[Z.le Z.lt Z.add Z.testbit]. rewrite length_lupd.
    repeat (split; [assumption|]). exact Gfra.
  - intros j Hj. cbn [am_last am1 upd_slot am_set_slots] in Hj.
    pose proof (Gsl j Hj) as (S1 & S2 & S3). unfold slot_ok. rewrite NS by lia.
    replace (am_maplen am1) with (am_maplen am) by reflexivity.
    replace (allocated am1 j) with (allocated am j) by reflexivity.
    destruct (j =? i) eqn:Ej.
    + apply Z.eqb_eq in Ej. subst j. rewrite Hxfr. split; [|split; [|right; reflexivity]].
      * intros Hn. destruct Hxhdr as [E|E]; [rewrite E in Hn; apply Si1; exact Hn | rewrite E in Hn; discriminate].
      * intros h3 h16 Eh. destruct Hxhdr as [E|E]; rewrite E in Eh; [apply Si2; exact Eh | injection Eh as <- <-; lia].
    + apply Z.eqb_neq in Ej. split; [exact S1|]. split; [exact S2|].
      destruct (ss_fr (nth_slot am j)) as [frj|].
      * destruct S3 as (A1 & A2 & A3 & A4). split; [exact A1|]. split; [intros E; injection E; lia|].
        split; [| exact A4]. unfold frame_ok, hdr_off16 in *. exact A3.
      * destruct S3 as [S3|S3]; [left; exact S3 | discriminate].
  - destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & C6) | (C1 & C2 & C3 & C4)].
    +
      left. repeat (split; [assumption|]). left. replace i with 0 by lia. reflexivity.
    + right. repeat (split; [assumption|]). exact C4.
  - intros p j Hp. split; intros HH; [injection HH; intros; subst; exfalso; exact (Hp eq_refl) | discriminate].
  - intros j HH. injection HH as <-. cbn [am_last am1 upd_slot am_set_slots]. split; [exact Hi|]. rewrite NS by lia. rewrite Z.eqb_refl.
    split; [exact Hxfr|]. exact Hal.
  - intros Hsc HL. apply (proj1 (ring_facts _ _ _ _ _ _ HI Hu Hsc ltac:(lia))). exact HL.
  - intros Hsc Hav. apply (proj1 (proj2 (ring_facts _ _ _ _ _ _ HI Hu Hsc ltac:(lia)))). exact Hav.
  - intros Hsc HL Hnh HnR. exfalso. exact (HnR i eq_refl).
  - intros Hpa p a Hp Hpg Hsca Hpa'. apply Hpg. symmetry.
    eapply (inv_partial HI g am p a Hu Hp); [symmetry; exact Hsca | exact Hpa | exact Hpa'].
Qed.

Lemma requeue_spec X U s sc g i am (Q : unit * astate -> Prop) : ltac2:(tb__ "0|4|
S3dVX;S51S50S0S3bA2S52S0S3bVg;Vi;A4A2M0VU;Vs;A4S35S45Z0M1Vsc;A2S46Vsc;Z30A2A2S3cVX;Vs;Vg;Vam;A4S34S3bS4Vam;A1Vsc;A3S34S53S0A1M2ScVam;A1S54S0A1M3A3S34G2SbVam;A1G3A3S36S34G2S3eVs;Vsc;A2S51S0Vg;A2A3A1S1S0S0S3dVX;G0VU;R3A4S6eVs;R4A2S34S53SfA1S40R5Vg;A2S51SfS7S1aS51S0R4A2S51S0R3A2Vam;A3A1A2A3S3bS45G1R1A2S36S34S3bR2Vsc;A3A1S34G2S3eR9R3A2S3eVs;R3A2A3F_;F_;Fc;S0S2S3cVX;R9R2R1A4S37S2S2S35S3cVX;Vs;R4R1A4S34S2S6cR3A1S6cR1A1A3A2La;A2F_;Fa';Fq;S64Vs;R8A2VQ;S52S55S1S59R9A4A1F_;F_;F_;F_;F_;F_;Fnx;Fpr;Fs';S62S50S55S1A2S2dS18Vsc;A1Vg;Vs;A3VQ;A3F_;F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hsc Hu Hsca Hp Hn Hnh HQ.
  destruct (inv_rings HI) as (F & A & D).
  destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. pose proof (MT_Some_In_keys _ _ _ Mg) as Kg.
  pose proof (inv_ctx HI) as C. destruct C as (Clen & Crest).
  assert (Hgn : ~ In g ms).
  { intros Hin. apply (Mem g am Hu Hsca) in Hin. apply Hin. rewrite Hp, Hn. reflexivity. }
  destruct (Full g am Hu Hsca Hgn) as [Hav Hfr].
  assert (SC : forall q, In q ms -> exists a, usedX X s q a /\ am_sc a = sc).
  { intros q Hq. eapply ring_members_used; [exact Rg | exact Hq]. }
  assert (SX : forall q, In q (g :: ms) -> memb q X = false).
  { intros q [<-|Hq]; [exact NXg|]. destruct (SC q Hq) as (a & Hqu & _). exact (proj2 (usedX_MT _ _ _ _ Hqu)). }
  eapply (queue_op (HActive sc) g s (MUsed am) ms (alinks X s sc)).
  - exact Mg.
  - cbn. rewrite Hp, Hn. reflexivity.
  - exact Rg.
  - exact Hgn.
  - intros q l _ Hl. eapply LK_of_alinks. exact Hl.
  - cbn. rewrite Clen. lia.
  - intros s' Sb Hse Hhd' Mg' Mother Mms.
    assert (RL : relinked s s' (g :: ms)).
    { split; [exact Mother|]. intros q [<-|Hq].
      - eexists (MUsed am), _, _. split; [exact Mg|]. split; [exact Mg'|]. discriminate.
      - destruct (SC q Hq) as (a & Hqu & _). pose proof (usedX_MT _ _ _ _ Hqu) as [Mq _].
        eexists (MUsed a), _, _. split; [exact Mq|]. split; [apply (Mms q _ Hq Mq) | discriminate]. }
    pose proof (rl_used_bwd X s s' _ RL) as Bwd. pose proof (rl_used_fwd X s s' _ RL) as Fwd.
    pose proof Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&Erg&_&EK).
    destruct Hse as (Hoth & Hfmh & Hlen).
    assert (EH : forall c, 0 <= c -> c <> sc -> active_hd s' c = active_hd s c).
    { intros c Hc Hne. unfold active_hd. apply Hoth. intros sc0 E0. injection E0 as <-. lia. }
    assert (Hhd_old : active_hd s sc = hd_error ms) by exact (proj2 Rg).
    assert (Hhd_new : active_hd s' sc = hd_error (ms ++ [g])).
    { cbn [head_of] in Hhd'. rewrite Hhd'. destruct ms; reflexivity. }
    assert (Rg' : ring_ok (alinks X s' sc) (active_hd s' sc) (ms ++ [g])).
    { rewrite Hhd_new. split; [|reflexivity].
      destruct ms as [|h0 rest] eqn:Ems.
      - cbn. split; [constructor; [intros [] | constructor]|]. split; [|exact I].
        unfold alinks. pose proof (usedX_intro X s' g _ NXg Mg') as U'. unfold usedX in U'. rewrite U'.
        cbn [am_sc am_prev am_next am_set_links]. rewrite Hsca, Z.eqb_refl. reflexivity.
      - eapply (cycle_snoc (alinks X s sc) (alinks X s' sc) (h0 :: rest) g (proj1 Rg)).
        + discriminate.
        + exact Hgn.
        + intros z pr nx Hz Lz. destruct (alinks_used _ _ _ _ _ Lz) as (a & Hzu & Hzs & El).
          pose proof (usedX_MT _ _ _ _ Hzu) as [Mz NXz].
          pose proof (Mms z (MUsed a) Hz Mz) as Mz'. cbn [with_links] in Mz'.
          unfold alinks, MTX. rewrite NXz, Mz'. cbn [am_sc am_prev am_next am_set_links].
          rewrite Hzs, Z.eqb_refl. injection El as -> ->. cbn [fst snd links_of]. reflexivity.
        + unfold alinks. pose proof (usedX_intro X s' g _ NXg Mg') as U'. unfold usedX in U'. rewrite U'.
          cbn [am_sc am_prev am_next am_set_links]. rewrite Hsca, Z.eqb_refl. reflexivity. }
    apply (HQ s' (last ms g) (hd g ms)).
    + eapply (Inv_surgery X X (Some (g, i)) (Some (g, i)) U U s s' HI).
      * intros k rg Hk _. unfold region_of in *. rewrite Erg. exact Hk.
      * exact Bwd.
      * intros p a Hpu. left. apply Fwd. exact Hpu.
      * intros q j HR. injection HR as <- <-. destruct (inv_reserved HI g i eq_refl) as (a & Hgu & Hj & Hf & Ha).
        destruct (Fwd _ _ Hgu) as (a' & Hgu' & E). exists a'.
        pose proof (strip_fields _ _ E) as (_&_&_&El&_). rewrite (strip_nth_slot _ _ i E), (strip_allocated _ _ i E), El. auto.
      * intros p j a' _. left. tauto.
      * apply (sbmh_ctx s s' Sb); [exact Hlen | | exact (inv_ctx HI)].
        intros Hi. exfalso. destruct Crest as (_&_&_&_&_&_&_&_&_&_&Ci&_). destruct (Ci Hi) as (Hm & _).
        unfold keys in Kg. rewrite Hm in Kg. exact Kg.
      * apply (sbmh_keys s s' Sb). exact (inv_keys HI).
      * apply (sbmh_areas s s' Sb). exact (inv_areas HI).
      * eapply rl_Xok; eauto. exact (inv_X HI).
      * split.
        { destruct F as (fms & FR & Fall). exists fms. split.
          - rewrite (Hfmh ltac:(discriminate)). eapply ring_ok_ext; [|exact FR]. intros q _.
            apply (rl_flinks_used X s s' _ RL sc). intros p [<-|Hpin]; [exists am; split; [exact Hu | exact Hsca] | apply SC; exact Hpin].
          - intros q pr nx Hq. apply (Fall q pr nx). unfold MTX in *. destruct (memb q X); [discriminate|].
            destruct (rl_MT_cases s s' _ RL q) as [E | (x & p' & n' & A1 & B1 & C1 & D1)]; [rewrite <- E; exact Hq|].
            exfalso. assert (exists a, MT s q = Some (MUsed a)) as (a & Ma).
            { destruct D1 as [<-|D1]; [exists am; exact Mg|]. destruct (SC q D1) as (a & Hqu & _). exists a. exact (proj1 (usedX_MT _ _ _ _ Hqu)). }
            rewrite Ma in A1. injection A1 as <-. rewrite B1 in Hq. cbn in Hq. discriminate. }
        split.
        { intros c Hc. destruct (Z.eq_dec c sc) as [->|Hne].
          - exists (ms ++ [g]). split; [exact Rg'|].
            split.
            { intros q a' Hq Hs'. destruct (Bwd _ _ Hq) as (a & Hqu & E). rewrite in_app_iff. cbn.
              destruct (sptr_eq_dec q g) as [->|Hqg].
              - pose proof (usedX_MT _ _ _ _ Hq) as [M _]. rewrite Mg' in M. injection M as <-. cbn. split; [intros _; discriminate | intros _; right; left; reflexivity].
              - destruct (in_dec sptr_eq_dec q ms) as [Hi|Hni].
                + split; [intros _; discriminate || idtac | intros _; left; exact Hi].
                  destruct (ring_links _ _ _ _ Rg' ltac:(apply in_app_iff; left; exact Hi)) as (pr & nx & L).
                  unfold alinks in L. pose proof Hq as Hq2. unfold usedX in Hq2. rewrite Hq2, Hs', Z.eqb_refl in L.
                  intros HL. rewrite HL in L. discriminate.
                + rewrite (rl_used_same X s s' _ RL q a') in Hq by (intros [E0|E0]; [exact (Hqg (eq_sym E0)) | exact (Hni E0)]).
                  rewrite <- (Mem q a' Hq Hs'). split; [intros [H|[H|[]]]; [exact H | exfalso; exact (Hqg (eq_sym H))] | intros H; left; exact H]. }
            split.
            { intros q a' Hq Hs' Hnin. rewrite in_app_iff in Hnin. cbn in Hnin.
              assert (Hqg : q <> g) by (intros ->; apply Hnin; right; left; reflexivity).
              assert (Hni : ~ In q ms) by (intros Hi; apply Hnin; left; exact Hi).
              rewrite (rl_used_same X s s' _ RL q a') in Hq by (intros [E0|E0]; [exact (Hqg (eq_sym E0)) | exact (Hni E0)]).
              exact (Full q a' Hq Hs' Hni). }
            split.
            { intros q a' Hq Hs' Hav'. destruct (Bwd _ _ Hq) as (a & Hqu & E).
              pose proof (strip_fields _ _ E) as (_&Eav&_&_&Es&_). rewrite Eav in Hav'.
              destruct (sptr_eq_dec q g) as [->|Hqg]; [pose proof (usedX_fun _ _ _ _ _ Hqu Hu) as ->; exfalso; exact (Hav' Hav)|].
              pose proof (Q1 q a Hqu ltac:(congruence) Hav') as Hh. rewrite Hhd_new. rewrite Hhd_old in Hh.
              destruct ms; cbn in Hh |- *; [discriminate | exact Hh]. }
            { intros q a' Hq Hs' Hiq Hnh' HnR. destruct (Bwd _ _ Hq) as (a & Hqu & E).
              pose proof (strip_fields _ _ E) as (_&_&Efr&_&Es&_). rewrite Efr.
              destruct (sptr_eq_dec q g) as [->|Hqg]; [exfalso; exact (HnR i eq_refl)|].
              apply (Q2 q a Hqu ltac:(congruence)).
              - rewrite in_app_iff in Hiq. destruct Hiq as [H|[H|[]]]; [exact H | exfalso; exact (Hqg (eq_sym H))].
              - rewrite Hhd_old. rewrite Hhd_new in Hnh'. destruct ms; cbn in Hnh' |- *; [discriminate | exact Hnh'].
              - exact HnR. }
          - destruct (A c Hc) as (ms' & Rg2 & Mem2 & Full2 & Q12 & Q22). exists ms'.
            rewrite (EH c ltac:(lia) Hne). split.
            { eapply ring_ok_ext; [|exact Rg2]. intros q _. apply (rl_alinks_other X s s' _ RL sc c q); [|lia].
              intros p [<-|Hpin]; [exists am; split; [exact Hu | exact Hsca] | apply SC; exact Hpin]. }
            assert (Hsame : forall q a', usedX X s' q a' -> am_sc a' = c -> usedX X s q a').
            { intros q a' Hq Hs'. apply (rl_used_same X s s' _ RL q a'); [|exact Hq].
              intros Hi. destruct (Bwd _ _ Hq) as (a & Hqu & E). pose proof (strip_fields _ _ E) as (_&_&_&_&Es&_).
              assert (am_sc a = sc); [|congruence].
              destruct Hi as [<-|Hi]; [pose proof (usedX_fun _ _ _ _ _ Hqu Hu) as ->; exact Hsca|].
              destruct (SC q Hi) as (a2 & Hu2 & Hs2). pose proof (usedX_fun _ _ _ _ _ Hu2 Hqu) as ->. exact Hs2. }
            split; [|split; [|split]]; intros q a' Hq Hs'; pose proof (Hsame q a' Hq Hs') as Hq0.
            + apply Mem2; [exact Hq0 | exact Hs'].
            + apply Full2; [exact Hq0 | exact Hs'].
            + apply Q12; [exact Hq0 | exact Hs'].
            + apply Q22; [exact Hq0 | exact Hs']. }
        { intros q a' Hq H63.
          assert (Hq0 : usedX X s q a').
          { apply (rl_used_same X s s' _ RL q a'); [|exact Hq]. intros Hi. destruct (Bwd _ _ Hq) as (a & Hqu & E).
            pose proof (strip_fields _ _ E) as (_&_&_&_&Es&_).
            destruct Hi as [<-|Hi]; [pose proof (usedX_fun _ _ _ _ _ Hqu Hu) as ->; lia|].
            destruct (SC q Hi) as (a2 & Hu2 & Hs2). pose proof (usedX_fun _ _ _ _ _ Hu2 Hqu) as ->. lia. }
          exact (D q a' Hq0 H63). }
      * eapply rl_usage; eauto. exact (inv_usage HI).
    + exact Sb.
    + exact Mg'.
    + exact EH.
    + exact Bwd.
    + eapply ub_same_relinked; [exact RL | exact EK].
Qed.

Lemma frameless_of_mask X U s g i am : ltac2:(tb__ "0|0|
S3dVX;S51S50S0S3bA2S52S0S3bVg;Vi;A4A2VU;Vs;A4S3cVX;Vs;Vg;Vam;A4S34S3bS47S48SdVam;A1SeVam;A1A2S11Vi;A1A2S14S8Vam;A1A1A3S3bS34S53S3A1S6SaVam;R1A2A1S54S3A1A3Fj;F_;F_;F_;").
Proof.
  intros HI Hu Hmask.
  destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & Hfr & Hal). pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
  pose proof (inv_groups HI g am Hu) as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & _) & _ & Gsl & _).
  assert (Hbit : Z.testbit (Z.lor (am_freed am) (am_avail am)) i = false).
  { unfold allocated in Hal. rewrite Z.lor_comm. destruct (Z.testbit _ i); [discriminate | reflexivity]. }
  pose proof (add_bit_lor _ i ltac:(lia) Hbit) as E. rewrite E in Hmask.
  assert (Hall : forall j, 0 <= j <= am_last am -> j <> i -> Z.testbit (Z.lor (am_freed am) (am_avail am)) j = true).
  { intros j Hj Hne. pose proof (f_equal (fun m => Z.testbit m j) Hmask) as T. cbn beta in T.
    rewrite Z.lor_spec, testbit_bit, testbit_ones in T by lia.
    replace (i =? j) with false in T by (symmetry; apply Z.eqb_neq; lia).
    replace (0 <=? j) with true in T by (symmetry; apply Z.leb_le; lia).
    replace (j <=? am_last am) with true in T by (symmetry; apply Z.leb_le; lia).
    destruct (Z.testbit (Z.lor (am_freed am) (am_avail am)) j); [reflexivity | cbn in T; discriminate]. }
  assert (Hslots : forall j, 0 <= j <= am_last am -> ss_fr (nth_slot am j) = None).
  { intros j Hj. destruct (Z.eq_dec j i) as [->|Hne]; [exact Hfr|].
    pose proof (Gsl j Hj) as (_ & _ & S3). destruct (ss_fr (nth_slot am j)) as [fr|]; [|reflexivity].
    destruct S3 as (A1 & _). exfalso. unfold allocated in A1. rewrite Z.lor_comm, (Hall j Hj Hne) in A1. discriminate. }
  intros j. destruct (Z_lt_dec j 0) as [Hj|Hj].
  { unfold nth_slot. replace (Z.to_nat j) with (Z.to_nat 0) by lia. apply (Hslots 0). lia. }
  destruct (Z_lt_dec (am_last am) j) as [Hj2|Hj2].
  { unfold nth_slot. rewrite nth_overflow; [reflexivity|]. rewrite Glen. lia. }
  apply Hslots. lia.
Qed.

Lemma same_mem_contra X R U s p a q b : ltac2:(tb__ "0|0|
S3dVX;VR;VU;Vs;A4S3cVX;Vs;Vp;Va;A4S3cVX;Vs;Vq;Vb;A4S36S34S0Vp;Vq;A3A1S34S0S5Va;A1S5Vb;A1A3S39F_;F_;F_;F_;F_;").
Proof.
  intros HI Ha Hb Hne Em.
  pose proof (extent_pos _ _ _ _ _ (inv_groups HI p a Ha)) as Pa. pose proof (extent_pos _ _ _ _ _ (inv_groups HI q b Hb)) as Pb.
  pose proof (stride_pos _ _ _ _ _ (inv_groups HI p a Ha)) as Sa. pose proof (stride_pos _ _ _ _ _ (inv_groups HI q b Hb)) as Sb.
  assert (K : forall a b, am_mem a = am_mem b -> 0 < group_extent a -> 16 <= stride_of b -> inside X s a b -> False).
  { intros a0 b0 E0 P0 S0 (j & fr & c & ac & Hj & _ & _ & _ & _ & Memc & Lo & _ & _).
    rewrite Memc, poff_slot_start, E0 in Lo. unfold UNIT in Lo. nia. }
  destruct (inv_laminar HI p a q b Ha Hb Hne ltac:(rewrite Em; reflexivity)) as [D | [I | I]].
  - unfold spans_disjoint in D. rewrite Em in D. lia.
  - exact (K a b Em Pa Sb I).
  - exact (K b a (eq_sym Em) Pb Sa I).
Qed.

Lemma release_slot_spec X U s g i am fr (Q : unit * astate -> Prop) : ltac2:(tb__ "0|2|
S3dVX;S54S50S0S3bA2M0A1VU;Vs;A4S3cVX;Vs;Vg;Vam;A4S35S45Z0Vi;A2S45Vi;S8Vam;A1A2A2S34S53S3A1M1S6SaVam;Vi;A2A1S51S3Vfr;A2A3S34S12S13Vfr;A1S17A3S1S33S34S1R2S63Vg;S7S16Vam;Vi;R1A3A1Vs;A3A3S34G1S6R2A1S54S3A1A3S3dVX;S51G0S52S0S3bVg;Vi;A4A2VU;R4A4VQ;S52S55S1S59R5A4A1F_;F_;F_;Fx;Fs';S62S50S55S1A2S2eVg;Vi;Vs;A3VQ;A3F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hu Hi Hfr Hk HQ. pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
  unfold release_slot. mbinds. eapply itok_getm; [exact Mg|]. msimp. rewrite Hfr.
  apply itok_setm'.
  set (x := if fr_off fr =? 0 then mkSlot (Some (255, 0)) None else mkSlot (ss_hdr (nth_slot am i)) None).
  assert (Hx : ss_fr x = None /\ (ss_hdr x = ss_hdr (nth_slot am i) \/ ss_hdr x = Some (255, 0))).
  { subst x. destruct (fr_off fr =? 0); cbn; auto. }
  destruct Hx as [Hx1 Hx2].
  apply (HQ _ x eq_refl Hx1). eapply drop_frame_Inv; eauto. intros HG. rewrite Hk in HG. discriminate.
Qed.

Lemma forget_frame_spec X U s g i am fr (Q : unit * astate -> Prop) : ltac2:(tb__ "0|3|
S3dVX;S54S50S0S3bA2M0A1VU;Vs;A4S3cVX;Vs;Vg;Vam;A4S35S45Z0M1Vi;A2S45Vi;S8Vam;A1A2A2S34S53S3A1S6SaVam;Vi;A2M2A1S51S3Vfr;A2A3S0S2S3cVX;Vs;R2R1A4S34S3bS9R2A1G1A3S36S34S0S5R3A1S1cVam;Vi;A2A3A1F_;F_;Fac;Fc;S1S34S1R1S63Vg;S7S16Vam;Vi;S28S15G2A1S54S3A1A2A3A1Vs;A3A3S3dVX;S51G0S52S0S3bVg;Vi;A4A2VU;R2A4VQ;S52S55S1S59R3A4A1F_;F_;Fs';S62S50S55S1A2S25Vg;Vi;Vs;A3VQ;A3F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hu Hi Hfr Hno HQ. pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
  unfold forget_frame. mbinds. eapply itok_getm; [exact Mg|]. msimp. apply itok_setm'.
  apply (HQ _ eq_refl). eapply drop_frame_Inv; eauto; cbn; auto.
Qed.

Lemma activate_group_spec X U s sc h ah (Q : Z * astate -> Prop) : ltac2:(tb__ "0|4|
S3dVX;S54S50S0S3bA2A1M0VU;Vs;A4S35S45Z0M1Vsc;A2S46Vsc;Z30A2A2S3cVX;Vs;Vh;Vah;A4S34S3bS4Vah;A1Vsc;A3S34S53S0A1S3eVs;Vsc;A2S51S0Vh;A2A3S34S3bSeVah;A1G1A3S3bS1S3dVX;G0VU;R1A4S34S1R2S63Vh;S7S23S4aSdVah;A1M2S14S22Vah;A1A1M3A2S19S4bG2G3A2Vah;A2A2A1Vs;A3A3VQ;S52S3bS1R4R3A4A1F_;F_;Fs';Fmask;S62S50S3bS1A2S21Vh;Vs;A2VQ;A3F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hsc Hu Hs Hhd Hav HQ. pose proof (usedX_MT _ _ _ _ Hu) as [Mh _].
  unfold activate_group. mbinds. eapply itok_getm; [exact Mh|]. msimp.
  mbinds. apply itok_massert; [apply Z.eqb_eq; exact Hav|]. msimp. mbinds. apply itok_setm'. msimp. apply itok_ret.
  apply HQ; [|reflexivity]. rewrite <- Hs in Hsc, Hhd. exact (activate_Inv X U s h ah HI Hu Hsc Hhd Hav).
Qed.

Lemma set_freed_Inv X U s g i am : ltac2:(tb__ "0|4|
S3dVX;S51S50S0S3bA2M0S52S0S3bVg;Vi;A4A2VU;Vs;A4S3cVX;Vs;Vg;Vam;A4S35S45Z0S4Vam;A1M1A2S46G1Z30A2A2S36S34S50S53S0A1M2G2A2S52G2G2ScVam;A1SbVam;A1A4S52G2G2S54S0A1M3G3A4A3A1S45S1bG1A1S1dVam;A1A2S3dVX;S54G0A1VU;S63Vg;S7S19S48SdVam;A1S11Vi;A1A2Vam;A2A1Vs;A3A4F_;F_;F_;F_;F_;").
Proof.
  intros HI Hu Hsc Hlinked Hstr.
  destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & Hfr & Hal). pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
  pose proof (inv_groups HI g am Hu) as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & _).
  assert (Hbit : Z.testbit (am_freed am) i = false /\ Z.testbit (am_avail am) i = false).
  { unfold allocated in Hal. rewrite Z.lor_spec in Hal. destruct (Z.testbit (am_avail am) i), (Z.testbit (am_freed am) i); cbn in Hal; try discriminate. auto. }
  destruct Hbit as [Hfb Hab].
  assert (Tnew : forall j, Z.testbit (Z.lor (am_freed am) (bit i)) j = Z.testbit (am_freed am) j || (i =? j)).
  { intros j. destruct (Z_lt_dec j 0) as [Hj|Hj]; [rewrite !testbit_neg_idx by lia; cbn; symmetry; apply Z.eqb_neq; lia|].
    rewrite Z.lor_spec, testbit_bit by lia. reflexivity. }
  change (am_set_freed (Z.lor (am_freed am) (bit i)) am) with
    (am_set_aidx (am_aidx am) (am_set_freed (Z.lor (am_freed am) (bit i)) (am_set_avail (am_avail am) am))).
  eapply (Inv_masks X (Some (g, i)) None U s g am); try exact HI; try exact Hu; try exact Hsc.
  - unfold masks_ok. cbn -[Z.le Z.lt Z.add Z.testbit Z.lor Z.to_nat Z.leb andb].
    split; [exact Glast|]. split; [exact Gaidx|]. split; [exact Glen|]. split; [exact Gav|].
    split; [apply Z.lor_nonneg; split; [exact Gfrn | unfold bit; apply Z.pow_nonneg; lia]|].
    split; [intros j Hj Ha; rewrite Tnew, (Gdisj j Hj Ha); cbn; apply Z.eqb_neq; intros ->; rewrite Ha in Hab; discriminate|].
    split; [intros j Hj; destruct (Gabove j Hj) as [A B]; rewrite Tnew, A, B; cbn; split; [reflexivity | apply Z.eqb_neq; lia]|].
    split; [exact Gavp|].
    intros j Hj. rewrite Tnew, (Gfra j Hj). reflexivity.
  - intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
    + right; right. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hal|].
      unfold allocated. cbn [am_avail am_freed am_set_aidx am_set_freed am_set_avail]. rewrite Z.lor_spec, Tnew, Z.eqb_refl, orb_true_r, orb_true_r. reflexivity.
    + left. unfold allocated. cbn [am_avail am_freed am_set_aidx am_set_freed am_set_avail]. rewrite !Z.lor_spec, testbit_bit by lia.
      replace (i =? j) with false by (symmetry; apply Z.eqb_neq; lia). rewrite orb_false_r. reflexivity.
  - intros p j Hp1 Hp2. split; intros E; [|discriminate]. exfalso. injection E as -> ->. apply Hp2. reflexivity.
  - intros j E. discriminate.
  - intros j E. injection E as <-. right. unfold allocated. cbn [am_avail am_freed am_set_aidx am_set_freed am_set_avail].
    rewrite Z.lor_spec, Tnew, Z.eqb_refl, !orb_true_r. reflexivity.
  - intros HL. exfalso. exact (Hlinked HL).
  - intros Hav. apply (proj1 (proj2 (ring_facts _ _ _ _ _ _ HI Hu ltac:(lia) ltac:(lia)))). exact Hav.
  - intros _ _ _ E. pose proof (f_equal (fun m => Z.testbit m i) E) as T. cbn beta in T. rewrite Tnew, Z.eqb_refl, orb_true_r, Z.bits_0 in T. discriminate.
  - intros Hpa p a Hp Hpg Hsca Hpa'. apply Hpg. symmetry.
    eapply (inv_partial HI g am p a Hu Hp); [symmetry; exact Hsca | exact Hpa | exact Hpa'].
  - intros Hlt. exfalso. lia.
Qed.

Lemma mask_zero_of_bits m : ltac2:(tb__ "0|1|
S45Z0M0Vm;A2S3bS45G0R1A2S34S56S4eVm;R2A2S5cA3F_;Fj;S34S3bVm;G0A3F_;F_;").
Proof. intros Hm Hb. apply bits_inj_nonneg. intros j Hj. rewrite Hb, Z.bits_0 by exact Hj. reflexivity. Qed.

Lemma unlinked_of_next_None X R U s g am : ltac2:(tb__ "0|3|
S3dVX;VR;VU;Vs;A4S3cVX;Vs;Vg;Vam;A4S35S45Z0S4Vam;A1M0A2S46G0Z30A2A2S34S53S0A1M1SbVam;A1S54S0A1M2A3S34G1ScVam;A1G2A3F_;F_;F_;F_;").
Proof.
  intros HI Hu Hsc Hn. destruct (inv_rings HI) as (_ & A & _). destruct (A (am_sc am) Hsc) as (ms & Rg & Mem & _).
  destruct (am_prev am) as [p|] eqn:Ep; [|reflexivity]. exfalso.
  assert (Hin : In g ms) by (apply (Mem g am Hu eq_refl); rewrite Ep, Hn; discriminate).
  destruct (ring_links _ _ _ _ Rg Hin) as (pr & nx & L). unfold alinks in L. unfold usedX in Hu. rewrite Hu, Z.eqb_refl in L.
  rewrite Hn in L. injection L as _ E. discriminate.
Qed.

Definition fneed (sc : Z) : nat := ltac2:(tb__ "0|1|
S56S58L_;S4cVsc;Z30M0A2S4fS4dG0Vsc;A2A1U1X56x2").

Lemma fneed_le sc : ltac2:(tb__ "0|0|
S45Z0Vsc;A2S6dS67Vsc;A1S1fA2F_;").
Proof. intros H. unfold fneed, NEST_FUEL. destruct (sc <? 48) eqn:E; [apply Z.ltb_lt in E|]; lia. Qed.

Definition corr (X : list sptr) (s s' : astate) : Prop := ltac2:(tb__ "0|0|
S0S2S3cVX;Vs';R2R1A4S37S2S2S35S3cVX;Vs;R4R1A4S35S34S0S5R3A1S5R1A1A3S34S3bS9R3A1S9R1A1A3A2A2La0;A2F_;Fa;Fq;").

Lemma corr_refl X s : ltac2:(tb__ "0|0|
S66VX;Vs;Vs;A3").
Proof. intros q a Hq. exists a. auto. Qed.

Lemma corr_trans X s1 s2 s3 : ltac2:(tb__ "0|0|
S66VX;Vs1;Vs2;A3S66VX;Vs2;Vs3;A3S66VX;Vs1;Vs3;A3F_;F_;").
Proof.
  intros A B q a Hq. destruct (B q a Hq) as (a1 & H1 & E1 & F1). destruct (A q a1 H1) as (a0 & H0 & E0 & F0).
  exists a0. split; [exact H0|]. split; congruence.
Qed.

Definition nf_post (X : list sptr) (U : Z -> Z) (s : astate) (r : option (nat * Z) * astate) : Prop := ltac2:(tb__ "0|4|
S35S3dVX;S54S50S0S3bA2A1VU;S60S53S50S58S3bA2M0A1M1S1Vr;A3M2A4S35S66VX;Vs;G2A3S35S64Vs;G2A2G1OLx;S5eG1S1Vr;A3G0G0OLp;R1S58S3bS37S10S10S35S34S53S10A1S44G2R3A2S51S10R1A2A3S35S34S32S2fR1A1S20A3S35S34S56S31R1A1S61A3S35S34S3bS30R1A1S2bR2A1A3S35S45Z0M3R2A2S0S2S3cVX;G2R2R1A4S46G3S9R2A1A2S36S34S58S2cS5R3A1A1R7A3A1F_;F_;Fa;Fq;A2A2A2A2A2Lrg;A2Llen;Lk;X50x1Lp;S3aX53x2A2A2A2").

Lemma else_branch_facts X U s g i am : ltac2:(tb__ "0|1|
S3dVX;S51S50S0S3bA2S52S0S3bVg;Vi;A4A2VU;Vs;A4S3cVX;Vs;Vg;Vam;A4S34S56S5dS49S47S48SdVam;A1SeVam;A1A2S11Vi;A1A2S14S8Vam;A1A1A2S2aVs;Vg;Vam;A3A2S5cA3S35S35S45Z0S4Vam;A1M0A2S46G0Z30A2A2S45S1bG0A1S1dVam;A1A2A2F_;F_;F_;").
Proof.
  intros HI Hu Hcond.
  destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & Hfr & Hal). pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
  pose proof (inv_groups HI g am Hu) as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & _).
  assert (Hm0 : am_last am = 0 -> Z.lor (am_freed am) (am_avail am) + bit i = ones (am_last am)).
  { intros Hl0. assert (i = 0) as -> by lia. rewrite Hl0.
    assert (E : Z.lor (am_freed am) (am_avail am) = 0).
    { apply mask_zero_of_bits; [apply Z.lor_nonneg; lia|]. intros j Hj. rewrite Z.lor_spec.
      destruct (Z.eq_dec j 0) as [->|Hne].
      - unfold allocated in Hal. rewrite Z.lor_spec in Hal. destruct (Z.testbit (am_avail am) 0), (Z.testbit (am_freed am) 0); cbn in Hal |- *; congruence.
      - destruct (Gabove j ltac:(lia)) as [A B]. rewrite A, B. reflexivity. }
    rewrite E. reflexivity. }
  destruct Gcl as [(C63 & Cl & _) | (Csc & CN1 & _ & _)].
  - exfalso. rewrite (Hm0 Cl), Z.eqb_refl in Hcond. unfold okay_to_free in Hcond. rewrite C63 in Hcond. cbn in Hcond. discriminate.
  - split; [exact Csc|]. destruct (Z_lt_dec (stride_of am) (class_size (am_sc am))) as [Hlt|]; [|lia]. exfalso.
    destruct (CN1 Hlt) as [Hl0 _]. rewrite (Hm0 Hl0), Z.eqb_refl in Hcond. unfold okay_to_free in Hcond.
    replace (stride_of am <? class_size (am_sc am)) with true in Hcond by (symmetry; apply Z.ltb_lt; exact Hlt).
    rewrite orb_true_r in Hcond. discriminate.
Qed.

Theorem nontrivial_free_spec fuel : ltac2:(tb__ "0|5|
S5bS0A1S3bS3bF_;S1S0S3bS2S50S53S50S58S3bA2A1S1A2M0OF_;S3dR7S51S50S0S3bA2S52S0S3bR4R3A4A2R6R5A4S3cR8R6R5R3A4S3bS45Z0M1R9R1A1A2Fc;S36S34S50S53S0A1M2G2A2S52G2G2ScR5A1SbR5A1A4S52G2G2S54S0A1M3G3A4A3A1S36S34G2S3eR9S4R6A1M4A2S51S0R8A2A3A1S36S34S3bSdR7A1G1A3A1F_;F_;S6dS67G4A1Vfuel;A2G0S68RdRcRbR1A4R8R2A1F_;Fr;S62G0S29Vfuel;RaR9RbA4R7A3F_;F_;F_;F_;F_;F_;FQ;Fam;Fi;Fg;Fs;FU;FX;").
Proof.
  induction fuel as [|f IH]; intros X U s g i am Q HI Hu HU HR2g Hf HQ.
  { exfalso. unfold fneed in Hf. destruct (am_sc am <? 48) eqn:E; [apply Z.ltb_lt in E|]; lia. }
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. pose proof (MT_Some_In_keys _ _ _ Mg) as Kg.
  destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & Hfr & Hal). pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
  pose proof (inv_groups HI g am Hu) as G. pose proof G as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
  assert (Hscr : am_sc am = 63 \/ 0 <= am_sc am < 48) by (destruct Gcl as [(C & _) | (C & _)]; [left | right]; exact C).
  cbn fix beta iota delta [nontrivial_free].
  mbinds. eapply itok_getm; [exact Mg|]. msimp. mbinds. apply itok_get. msimp. cbn zeta.
  set (sc := am_sc am) in *. set (mask := Z.lor (am_freed am) (am_avail am)).
  destruct ((mask + bit i =? ones (am_last am)) && okay_to_free s g am) eqn:Hcond.
  -
    apply andb_prop in Hcond as [Hmask Hok]. apply Z.eqb_eq in Hmask.
    pose proof (frameless_of_mask X U s g i am HI Hu Hmask) as Hnofr.
    set (U1 := fun c => U c + contrib X s c g).

    mbinds.
    match goal with |- itok (?mm s) _ =>
      assert (STEP1 : itok (mm s) (fun r => let s1 := snd r in
        Inv (g :: X) None U1 s1 /\ MT s1 g = Some (MUsed (am_set_links None None am)) /\
        st_usage s1 = st_usage s /\ st_regions s1 = st_regions s /\ corr X s s1 /\
        (forall q a, usedX (g :: X) s1 q a -> exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0) /\
        (forall q, (forall a, usedX X s q a -> am_sc a <> sc) -> q <> g -> MT s1 q = MT s q) /\ ub_same s s1)) end.
    { destruct (am_next am) as [nx|] eqn:Enx.
      - assert (Hsc : 0 <= sc < 48).
        { destruct Hscr as [H63|H]; [|exact H]. exfalso. destruct (inv_rings HI) as (_ & _ & D). destruct (D g am Hu H63) as [_ E]. rewrite Enx in E. discriminate. }
        mbinds. apply itok_massert; [apply Z.ltb_lt; lia|]. msimp. mbinds. apply itok_get_head. msimp.
        change (nth (Z.to_nat sc) (st_active s) None) with (active_hd s sc).
        mbinds. eapply (dequeue_exempt_spec X (Some (g, i)) U s sc g am); [exact HI | exact Hsc | exact Hu | reflexivity | rewrite Enx; intros E; discriminate | exact Hnofr | intros p j E; injection E; auto |].
        intros s1 HI1 Sb1 Mg1 EH1 Mo1 Bwd1 Hk1 Hnew1 UB1. msimp. mbinds. apply itok_get_head. msimp.
        change (nth (Z.to_nat sc) (st_active s1) None) with (active_hd s1 sc).
        pose proof Sb1 as (_&_&_&_&_&_&_&_&_&Eus1&_&_&_&_&Erg1&_&EK1).
        assert (C1 : forall q a, usedX (g :: X) s1 q a -> exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0).
        { intros q a Hq. destruct (Bwd1 q a Hq) as (_ & a0 & H0 & E). pose proof (strip_fields _ _ E) as (Em&_&_&_&_&Eml&_).
          exists a0. auto. }
        assert (Cr1 : corr X s s1).
        { intros q a Hq. destruct (sptr_eq_dec q g) as [->|Hne].
          - pose proof (usedX_MT _ _ _ _ Hq) as [M _]. rewrite Mg1 in M. injection M as <-. exists am.
            split; [exact Hu|]. destruct am; split; reflexivity.
          - apply C1. apply usedX_cons; assumption. }
        assert (POST1 : forall s1', Inv (g :: X) None U1 s1' ->
                  (exists h x, s1' = upd_meta h x s1 /\ h <> g /\
                     (exists ah ah', x = MUsed ah' /\ usedX (g :: X) s1 h ah /\ am_sc ah = sc /\ am_mem ah' = am_mem ah /\ am_maplen ah' = am_maplen ah /\
                        blocks_of h ah' = blocks_of h ah)) \/ s1' = s1 ->
                  let s1 := s1' in
                  Inv (g :: X) None U1 s1 /\ MT s1 g = Some (MUsed (am_set_links None None am)) /\
                  st_usage s1 = st_usage s /\ st_regions s1 = st_regions s /\ corr X s s1 /\
                  (forall q a, usedX (g :: X) s1 q a -> exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0) /\
                  (forall q, (forall a, usedX X s q a -> am_sc a <> sc) -> q <> g -> MT s1 q = MT s q) /\ ub_same s s1).
        { intros s1' HI1' Hcase. cbn zeta. destruct Hcase as [(h & x & -> & Hhg & ah & ah' & -> & Uh & Sh & Emh & Emlh & Ebl) | ->].
          - split; [exact HI1'|]. split; [rewrite MT_upd_other by (intros E; exact (Hhg (eq_sym E))); exact Mg1|].
            split; [exact Eus1|]. split; [exact Erg1|].
            assert (C2 : forall q a, usedX (g :: X) (upd_meta h (MUsed ah') s1) q a ->
                         exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0).
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
        destruct (osptr_eqb (active_hd s sc) (Some g)) eqn:Ehd.
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
        split; [apply (Inv_exempt X (Some (g, i)) U s g am HI Hu Hnofr Hp Enx); intros p j E; injection E; auto|].
        split; [rewrite Mg; destruct am; cbn in Hp, Enx |- *; subst; reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [apply corr_refl|]. split.
        + intros q a Hq. apply usedX_cons_inv in Hq as [_ Hq]. exists a. auto.
        + split; [intros; reflexivity | apply ub_same_refl]. }
    revert STEP1. apply itok_mono. intros [u1 s1] (HI1 & Mg1 & Eus1 & Erg1 & Cr1 & C1 & Mo1 & UBs1). cbn [fst snd] in *. msimp.
    mbinds. eapply itok_getm; [exact Mg1|]. msimp.
    replace (am_last (am_set_links None None am)) with (am_last am) by (destruct am; reflexivity).
    replace (am_maplen (am_set_links None None am)) with (am_maplen am) by (destruct am; reflexivity).
    replace (am_mem (am_set_links None None am)) with (am_mem am) by (destruct am; reflexivity).
    assert (HU1 : forall c, 0 <= c < 48 -> U1 c = U c + (if sc =? c then am_last am + 1 else 0)).
    { intros c Hc. unfold U1. rewrite (contrib_used X s c g am Hu). reflexivity. }

    mbinds.
    match goal with |- itok (?mm s1) _ =>
      assert (STEP2 : itok (mm s1) (fun r => let s2 := snd r in
        Inv (g :: X) None U s2 /\ st_metas s2 = st_metas s1 /\ st_regions s2 = st_regions s /\ st_active s2 = st_active s1)) end.
    { destruct (sc <? 48) eqn:E48.
      - apply Z.ltb_lt in E48. apply itok_set_usage_of. cbn zeta.
        assert (Hv : am_last am + 1 <= usage_of s sc).
        { rewrite (inv_usage HI sc ltac:(lia)). pose proof (class_sum_ge_contrib X _ U s sc g HI Kg) as Hge.
          rewrite (contrib_used X s sc g am Hu) in Hge. fold sc in Hge. rewrite Z.eqb_refl in Hge. pose proof (HU sc). lia. }
        pose proof (Inv_set_usage (g :: X) None U1 s1 sc (usage_of s sc - (am_last am + 1)) HI1 ltac:(lia) ltac:(lia)) as HI2.
        split; [|split; [reflexivity|split; [exact Erg1|reflexivity]]].
        eapply Inv_U_ext; [|exact HI2]. intros c Hc. unfold Uadd. rewrite (HU1 c Hc).
        replace (usage_of s1 sc) with (usage_of s sc) by (unfold usage_of; rewrite Eus1; reflexivity).
        destruct (c =? sc) eqn:E1; destruct (sc =? c) eqn:E2; try lia;
          try (apply Z.eqb_eq in E1; apply Z.eqb_neq in E2; lia); try (apply Z.eqb_neq in E1; apply Z.eqb_eq in E2; lia).
      - apply Z.ltb_ge in E48. apply itok_ret. cbn zeta. split; [|split; [reflexivity|split; [exact Erg1|reflexivity]]].
        eapply Inv_U_ext; [|exact HI1]. intros c Hc. rewrite (HU1 c Hc).
        destruct (sc =? c) eqn:E2; [apply Z.eqb_eq in E2; lia | lia]. }
    revert STEP2. apply itok_mono. intros [u2 s2] (HI2 & Em2 & Erg2 & Ea2). cbn [fst snd] in *. msimp.
    assert (MT2 : forall q, MT s2 q = MT s1 q) by (intros; unfold MT; rewrite Em2; reflexivity).
    assert (EU2 : forall Y q a, usedX Y s2 q a <-> usedX Y s1 q a) by (intros; unfold usedX, MTX; rewrite MT2; tauto).
    assert (C2 : forall q a, usedX (g :: X) s2 q a -> exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0).
    { intros q a Hq. apply EU2 in Hq. apply C1. exact Hq. }

    mbinds.
    match goal with |- itok (?mm s2) _ =>
      assert (STEP3 : itok (mm s2) (fun r => let s4 := snd r in
        Inv (g :: X) None U s4 /\ ub_same s s4 /\
        (forall q a, usedX (g :: X) s4 q a -> exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0) /\
        match fst r with
        | None => True
        | Some (k, len) => exists rg, region_of s4 k = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
            rg_len rg = page_round len /\ 0 <= len /\ (forall q a, usedX (g :: X) s4 q a -> 0 < am_maplen a -> prid (am_mem a) <> k)
        end)) end.
    { destruct (negb (am_maplen am =? 0)) eqn:Eml.
      -
        assert (Hml : 0 < am_maplen am) by (destruct (am_maplen am =? 0) eqn:E; [discriminate | apply Z.eqb_neq in E; lia]).
        mbinds. eapply step_seq_spec; [exact HI2|]. intros s3 HI3 (Em3 & _ & Er3 & _). msimp.
        mbinds. eapply record_seq_spec; [exact HI3|]. intros s4 HI4 (Em4 & _ & Er4 & _). msimp.
        apply itok_ret. cbn zeta. cbn [fst snd].
        assert (EU4 : forall q a, usedX (g :: X) s4 q a <-> usedX (g :: X) s2 q a) by (intros; unfold usedX, MTX, MT; rewrite Em4, Em3; tauto).
        split; [exact HI4|]. split.
        { eapply ub_same_trans; [exact UBs1|]. apply ub_same_metas. rewrite Em4, Em3, Em2. reflexivity. }
        split; [intros q a Hq; apply C2; apply EU4; exact Hq|].
        destruct (Gmp Hml) as (r & rg & Emem & Hr & Hk & Hl & Hlen & _). exists rg. rewrite Emem. cbn [prid].
        split; [unfold region_of in *; rewrite Er4, Er3, Erg2; exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split.
        { rewrite Hlen. unfold PGSZ. rewrite page_round_fixed; [reflexivity|]. unfold PGSZ. apply Z_mod_mult. }
        split; [lia|].
        intros q a Hq Hqm. apply EU4 in Hq. pose proof (usedX_cons_inv _ _ _ _ _ Hq) as [Hqg _].
        destruct (C2 q a Hq) as (a0 & H0 & E0 & F0). rewrite E0. rewrite F0 in Hqm. intros Ep. apply Hqg.
        eapply (inv_maps HI q a0 g am H0 Hu Hqm Hml). rewrite Emem. cbn. exact Ep.
      -
        assert (Hml : am_maplen am = 0) by (destruct (am_maplen am =? 0) eqn:E; [apply Z.eqb_eq in E; exact E | discriminate]).
        destruct (Gns Hml) as (N63 & g' & am' & i' & fr' & U' & Hi' & F' & K' & Emem & Hsc' & N63' & Fit).
        assert (Hsc : 0 <= sc < 48) by (destruct Hscr as [H|H]; [exfalso; exact (N63 H) | exact H]).
        pose proof (inv_groups HI g' am' U') as G'. pose proof G' as (_ & _ & Gsl' & Gcl' & _).
        pose proof (Gsl' i' Hi') as (_ & _ & S3'). rewrite F' in S3'. destruct S3' as (Hal' & _ & (_ & _ & _ & _ & FG') & _).
        destruct (FG' K') as [Hoff' _].
        assert (Hsc'48 : 0 <= am_sc am' < 48) by (destruct Gcl' as [(C & _) | (C & _)]; [exfalso; exact (N63' C) | exact C]).
        assert (Hg'g : g' <> g) by (intros ->; pose proof (usedX_fun _ _ _ _ _ U' Hu) as E; rewrite E in Hsc'; lia).
        pose proof (usedX_MT _ _ _ _ U') as [Mg' NXg'].
        assert (U'2 : usedX (g :: X) s2 g' am').
        { apply EU2. apply usedX_intro.
          - rewrite memb_cons, NXg'. replace (sptr_eqb g' g) with false by (symmetry; apply sptr_eqb_neq; exact Hg'g). reflexivity.
          - rewrite (Mo1 g'); [exact Mg' | | exact Hg'g]. intros a Ha. pose proof (usedX_fun _ _ _ _ _ Ha U') as ->. lia. }
        assert (Eptr : am_mem am = frame_ptr am' i' fr').
        { unfold frame_ptr. rewrite Hoff', Z.mul_0_r, padd_0. exact Emem. }
        mbinds. unfold find_frame. mbinds. apply itok_get. msimp.
        rewrite Eptr, (find_frame_in_spec (g :: X) None U s2 HI2 g' am' i' fr' U'2 Hi' F'). msimp. apply itok_ret. cbn [fst snd].
        mbinds. eapply itok_getm; [exact (proj1 (usedX_MT _ _ _ _ U'2))|]. msimp.
        mbinds. apply itok_mcheck; [unfold slot_is_group; rewrite F', K'; reflexivity|]. msimp.
        mbinds. eapply (forget_frame_spec (g :: X) U s2 g' i' am' fr'); [exact HI2 | exact U'2 | exact Hi' | exact F' | |].
        { intros c ac Hc Hmlc Emc. pose proof (usedX_cons_inv _ _ _ _ _ Hc) as [Hcg _].
          destruct (C2 c ac Hc) as (ac0 & H0 & E0 & _).
          eapply (same_mem_contra X _ U s c ac0 g am HI H0 Hu Hcg). rewrite <- E0, Emc. symmetry. exact Emem. }
        intros s3 Es3 HI3. msimp.
        set (am'' := upd_slot am' i' (mkSlot (ss_hdr (nth_slot am' i')) None)) in Es3.
        assert (U'3 : usedX (g :: X) s3 g' am'').
        { rewrite Es3. apply usedX_upd. left. split; [reflexivity|]. split; [|reflexivity].
          rewrite memb_cons, NXg'. replace (sptr_eqb g' g) with false by (symmetry; apply sptr_eqb_neq; exact Hg'g). reflexivity. }
        pose proof (upd_slot_fields am' i' (mkSlot (ss_hdr (nth_slot am' i')) None)) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold am'' in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
        eapply (IH (g :: X) U s3 g' i' am''); [exact HI3 | exact U'3 | exact HU | | |].
        +
          intros Hl Hnh. replace (am_freed am'') with (am_freed am') by (subst am''; destruct am'; reflexivity).
          replace (am_prev am'', am_next am'') with (am_prev am', am_next am') in Hl by (subst am''; destruct am'; reflexivity).
          rewrite Fsc in Hnh. replace (active_hd s3 (am_sc am')) with (active_hd s2 (am_sc am')) in Hnh by (rewrite Es3; reflexivity).
          apply (proj2 (proj2 (ring_facts _ _ _ _ _ _ HI2 U'2 ltac:(lia) ltac:(lia)))); [exact Hl | exact Hnh | intros; discriminate].
        + rewrite Fsc. unfold fneed in Hf |- *. fold sc in Hf.
          replace (sc <? 48) with true in Hf by (symmetry; apply Z.ltb_lt; lia).
          replace (am_sc am' <? 48) with true by (symmetry; apply Z.ltb_lt; lia). lia.
        + intros [mi s4] (HI4 & Cr4 & UB34 & Hmi). cbn [fst snd] in *. cbn zeta.
          assert (C4 : forall q a, usedX (g :: X) s4 q a -> exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0).
          { intros q a Hq. destruct (Cr4 q a Hq) as (a3 & H3 & E3 & F3).
            rewrite Es3 in H3. apply usedX_upd in H3. destruct H3 as [(-> & _ & E) | (Hne & H2')].
            - injection E as <-. destruct (C2 g' am' U'2) as (a0 & H0 & E0 & F0). exists a0. split; [exact H0|]. split; congruence.
            - destruct (C2 q a3 H2') as (a0 & H0 & E0 & F0). exists a0. split; [exact H0|]. split; congruence. }
          split; [exact HI4|]. split; [|split; [exact C4 | exact Hmi]].
          eapply ub_same_trans; [exact UBs1|]. eapply ub_same_trans; [apply ub_same_metas; exact Em2|]. eapply ub_same_trans; [|exact UB34].
          rewrite Es3. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ U'2))|].
          rewrite (proj1 (usedX_MT _ _ _ _ U'2)). cbn. pose proof (inv_groups HI2 g' am' U'2) as ((_ & _ & Glen' & _) & _).
          apply blocks_of_upd_slot_same; [exact Hi' | exact Glen' |]. unfold slotst_block, slot_block. cbn. rewrite F', K'. reflexivity. }
    revert STEP3. apply itok_mono. intros [mi s4] (HI4 & UB4 & C4 & Hmi). cbn [fst snd] in *. msimp.

    mbinds. eapply free_meta_spec; [exact HI4 | left; reflexivity |]. intros s5 HI5 Sb5 Ea5 EU5 UB5. msimp.
    rewrite (remove_head_notin g X NXg) in HI5, EU5.
    apply itok_ret. apply HQ. unfold nf_post. cbn [fst snd].
    split; [exact HI5|]. split.
    { intros q a Hq. apply EU5 in Hq. apply C4. exact Hq. }
    split; [eapply ub_same_trans; [exact UB4 | exact UB5]|].
    destruct mi as [[k len]|]; [|exact I].
    destruct Hmi as (rg & Hr & Hk & Hl & Hlen & Hlen0 & Hno). exists rg.
    pose proof Sb5 as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&Erg5&_).
    split; [unfold region_of in *; rewrite Erg5; exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [exact Hlen|]. split; [exact Hlen0|].
    intros q a Hq. apply EU5 in Hq. exact (Hno q a Hq).
  -
    destruct (else_branch_facts X U s g i am HI Hu Hcond) as [Hsc Hstr]. fold sc in Hsc, Hstr.
    pose proof (ring_facts X (Some (g, i)) U s g am HI Hu ltac:(lia) ltac:(lia)) as (RF1 & RF2 & RF3). fold sc in RF1, RF2, RF3.
    mbinds.
    match goal with |- itok (?mm s) _ =>
      assert (STEPE : itok (mm s) (fun r => let s1 := snd r in
        Inv X (Some (g, i)) U s1 /\
        exists am2, MT s1 g = Some (MUsed am2) /\ (am_prev am2, am_next am2) <> (None, None) /\ strip am2 = strip am /\
          (forall q a', usedX X s1 q a' -> exists a, usedX X s q a /\ strip a' = strip a) /\ ub_same s s1)) end.
    { destruct (mask =? 0) eqn:Em0.
      - apply Z.eqb_eq in Em0.
        assert (Hfr0 : am_freed am = 0).
        { subst mask. apply Z.lor_eq_0_iff in Em0. exact (proj1 Em0). }
        mbinds. apply itok_massert; [apply Z.ltb_lt; lia|]. msimp. mbinds. apply itok_get_head. msimp.
        change (nth (Z.to_nat sc) (st_active s) None) with (active_hd s sc).
        destruct (osptr_eqb (active_hd s sc) (Some g)) eqn:Ehd.
        + apply osptr_eqb_eq in Ehd. apply itok_ret. cbn zeta. cbn [snd]. split; [exact HI|]. exists am.
          split; [exact Mg|]. split; [|split; [reflexivity | split; [intros q a' Hq; exists a'; auto | apply ub_same_refl]]].

          destruct (inv_rings HI) as (_ & A & _). destruct (A sc Hsc) as (ms & Rg & Mem & _).
          apply (Mem g am Hu eq_refl). rewrite Ehd in Rg. exact (proj1 (ring_head_In _ _ _ Rg)).
        + assert (Hnh : active_hd s sc <> Some g) by (intros E; rewrite E in Ehd; cbn in Ehd; rewrite sptr_eqb_refl in Ehd; discriminate).
          assert (Hunl : am_prev am = None /\ am_next am = None).
          { destruct (am_prev am) eqn:Ep; destruct (am_next am) eqn:En; try (exfalso; apply (HR2g ltac:(discriminate) Hnh); exact Hfr0). auto. }
          destruct Hunl as [Hp Hn].
          eapply (requeue_spec X U s sc g i am); [exact HI | exact Hsc | exact Hu | reflexivity | exact Hp | exact Hn | exact Hnh |].
          intros s1 pr nx HI1 Sb1 Mg1 EH1 Bwd1 UB1. cbn zeta. cbn [snd]. split; [exact HI1|]. exists (am_set_links (Some pr) (Some nx) am).
          split; [exact Mg1|]. split; [destruct am; cbn; discriminate|]. split; [destruct am; reflexivity | split; [exact Bwd1 | exact UB1]].
      - apply itok_ret. cbn zeta. cbn [snd]. split; [exact HI|]. exists am.
        split; [exact Mg|]. split; [|split; [reflexivity | split; [intros q a' Hq; exists a'; auto | apply ub_same_refl]]].
        intros HL. destruct (RF1 HL) as [Hav0 Hfr0]. apply Z.eqb_neq in Em0. apply Em0. subst mask. rewrite Hav0, Hfr0. reflexivity. }
    revert STEPE. apply itok_mono. intros [u1 s1] (HI1 & am2 & Mg2 & Hl2 & Hst2 & Bwd1 & UB1). cbn [fst snd] in *. msimp.
    pose proof (strip_fields _ _ Hst2) as (Emem2 & _ & _ & _ & Esc2 & Eml2 & _).
    assert (U2 : usedX X s1 g am2) by (apply usedX_intro; [exact NXg | exact Mg2]).
    mbinds. eapply itok_getm; [exact Mg2|]. msimp. mbinds. apply itok_setm'. msimp. apply itok_ret.
    apply HQ. unfold nf_post. cbn [fst snd]. split; [|split; [|split; [|exact I]]].
    + apply (set_freed_Inv X U s1 g i am2 HI1 U2); [rewrite Esc2; exact Hsc | exact Hl2 |].
      rewrite Esc2, (strip_stride _ _ Hst2). exact Hstr.
    + intros q a Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
      * injection E as <-. exists am. split; [exact Hu|]. destruct am2, am; cbn in Emem2, Eml2 |- *; subst; auto.
      * destruct (Bwd1 q a Hq) as (a0 & H0 & E0). pose proof (strip_fields _ _ E0) as (Em&_&_&_&_&Eml&_). exists a0. auto.
    + eapply ub_same_trans; [exact UB1|]. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact Mg2|]. rewrite Mg2. cbn. apply blocks_of_freed.
Qed.

Theorem free_spec U s g am idx fr (Q : unit * astate -> Prop) : ltac2:(tb__ "0|7|
S3dS5fS0A1M0S54S50S0S3bA2M1A1M2VU;Vs;A4S3bS45Z0M3VU;R1A1A2Fc;S3cG0Vs;Vg;Vam;A4S35S45G3Vidx;A2S45Vidx;S8Vam;A1A2A2S34S53S3A1S6SaVam;Vidx;A2A1S51S3Vfr;A2A3S34S12S13Vfr;A1S17A3S1S3dG0G2VU;R1A4S0S2S3cG0R4R2R1A4S37S2S2S35S3cG0Vs;R4R1A4S35S34S0S5R3A1S5R1A1A3S34S3bS9R3A1S9R1A1A3A2A2La0;A2F_;Fa;Fq;S37S5bS50G1G1A2M4A1M5G5S37G5G5S35S34G5S65Vs;A1S5aG4R2S57G4S52G1G1S52S0S3bS42Vam;Vidx;Vfr;A3M6S26Vfr;A1A4S52S0S3bVg;Vidx;A4A4R1A3A3A3S34G5S65R5A1S5aG4R2R1A3A3A2Ll2;A2Ll1;A2VQ;S52S55S1S59R4A4A1F_;F_;F_;Fs';S62S50S55S1A2S27S51S0G6A2Vs;A2VQ;A3F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI HU Hu Hidx Hfr Hk HQ.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg].
  pose proof (inv_groups HI g am Hu) as G. pose proof G as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
  pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (Hal & _ & _ & _).
  assert (Hscr : am_sc am = 63 \/ 0 <= am_sc am < 48) by (destruct Gcl as [(C & _) | (C & _)]; [left | right]; exact C).
  unfold free. mbinds. unfold find_frame. mbinds. apply itok_get. msimp.
  rewrite (find_frame_in_spec [] None U s HI g am idx fr Hu Hidx Hfr). apply itok_ret. msimp.
  mbinds. eapply itok_getm; [exact Mg|]. msimp. cbn zeta.
  mbinds. eapply release_slot_spec; [exact HI | exact Hu | exact Hidx | exact Hfr | exact Hk |].
  intros s1 x Es1 Hx HI1. msimp.
  assert (DEL : forall s', ub_same s1 s' -> exists l1 l2, ublist s = l1 ++ ((frame_ptr am idx fr, fr_n fr), (g, idx)) :: l2 /\ ublist s' = l1 ++ l2).
  { intros s' UB'. pose proof (inv_groups HI g am Hu) as ((_ & _ & Glen0 & _) & _).
    destruct (ublist_upd_slot s g am idx x (proj1 (inv_keys HI)) (proj1 (usedX_MT _ _ _ _ Hu)) Hidx Glen0) as (l1 & l2 & E1 & E2).
    exists l1, l2. rewrite (ub_same_ublist _ _ UB'), Es1, E2, E1. unfold slot_block, slotst_block. rewrite Hfr, Hk, Hx. split; reflexivity. }
  set (am1 := upd_slot am idx x) in Es1.
  assert (U1 : usedX [] s1 g am1) by (rewrite Es1; apply usedX_upd; left; auto).
  pose proof (upd_slot_fields am idx x) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold am1 in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
  assert (Flk : (am_prev am1, am_next am1) = (am_prev am, am_next am) /\ am_freed am1 = am_freed am /\ am_avail am1 = am_avail am).
  { subst am1. destruct am; repeat split; reflexivity. }
  destruct Flk as (Flk & Ffr & Fav).
  assert (Hbits : Z.testbit (am_freed am) idx = false /\ Z.testbit (am_avail am) idx = false).
  { unfold allocated in Hal. rewrite Z.lor_spec in Hal. destruct (Z.testbit (am_avail am) idx), (Z.testbit (am_freed am) idx); cbn in Hal; try discriminate; auto. }
  destruct Hbits as [Hfb Hab].
  mbinds. apply itok_massert.
  { apply Z.eqb_eq. apply bits_inj_nonneg. intros j Hj. rewrite Z.land_spec, Z.lor_spec, testbit_bit, Z.bits_0 by lia.
    destruct (Z.eq_dec idx j) as [<-|Hne]; [rewrite Hfb, Hab, Z.eqb_refl; reflexivity|].
    replace (idx =? j) with false by (symmetry; apply Z.eqb_neq; exact Hne). apply andb_false_r. }
  msimp.
  pose proof (ring_facts [] None U s g am HI Hu) as RF.
  destruct (negb (am_freed am =? 0) && negb (Z.lor (am_freed am) (am_avail am) + bit idx =? ones (am_last am))) eqn:Ebr.
  -
    apply andb_prop in Ebr as [Efr0 _]. assert (Hfr0 : am_freed am <> 0) by (destruct (am_freed am =? 0) eqn:E; [discriminate | apply Z.eqb_neq in E; exact E]).
    assert (Hsc : 0 <= am_sc am < 48).
    { destruct Hscr as [H63|H]; [|exact H]. exfalso. destruct Gcl as [(_ & _ & _ & _ & C5 & _) | (C & _)]; [exact (Hfr0 C5) | lia]. }
    destruct (RF ltac:(lia) ltac:(lia)) as (RF1 & RF2 & RF3).
    assert (Hlinked : (am_prev am, am_next am) <> (None, None)) by (intros HL; destruct (RF1 HL) as [_ E]; exact (Hfr0 E)).
    assert (Hstr : class_size (am_sc am) <= stride_of am).
    { destruct Gcl as [(C & _) | (_ & CN1 & _)]; [lia|]. destruct (Z_lt_dec (stride_of am) (class_size (am_sc am))) as [Hlt|]; [|lia].
      exfalso. destruct (CN1 Hlt) as [Hl0 _]. apply Hfr0. apply mask_zero_of_bits; [exact Gfrn|]. intros j Hj.
      destruct (Z.eq_dec j idx) as [->|Hne]; [exact Hfb|]. destruct (Gabove j ltac:(lia)) as [_ B]. exact B. }
    mbinds. eapply itok_getm; [rewrite Es1; apply MT_upd_same|]. msimp. apply itok_setm'.
    rewrite (add_bit_lor (am_freed am) idx ltac:(lia) Hfb). rewrite <- Ffr.
    apply HQ.
    + apply (set_freed_Inv [] U s1 g idx am1 HI1 U1); [rewrite Fsc; exact Hsc | rewrite Flk; exact Hlinked | rewrite Fsc, Fst; exact Hstr].
    + intros q a Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
      * injection E as <-. exists am. split; [exact Hu|]. rewrite <- Fm, <- Fml. destruct am1; split; reflexivity.
      * rewrite Es1 in Hq. apply usedX_upd in Hq. destruct Hq as [(E & _) | (_ & Hq)]; [exfalso; exact (Hne E)|]. exists a. auto.
    + apply DEL. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ U1))|].
      rewrite (proj1 (usedX_MT _ _ _ _ U1)). cbn. apply blocks_of_freed.
  -
    mbinds. eapply (nontrivial_free_spec NEST_FUEL [] U s1 g idx am1); [exact HI1 | exact U1 | exact HU | | |].
    + rewrite Flk, Ffr, Fsc. replace (active_hd s1 (am_sc am)) with (active_hd s (am_sc am)) by (rewrite Es1; reflexivity).
      intros HL Hnh. destruct Hscr as [H63|Hsc].
      { exfalso. destruct (inv_rings HI) as (_ & _ & D). destruct (D g am Hu H63) as [P N]. apply HL. rewrite P, N. reflexivity. }
      destruct (RF ltac:(lia) ltac:(lia)) as (_ & _ & RF3). apply RF3; [exact HL | exact Hnh | intros; discriminate].
    + rewrite Fsc. apply fneed_le. destruct Hscr as [H|H]; lia.
    + intros [mi s2] (HI2 & Cr2 & UB2 & Hmi). cbn [fst snd] in *. msimp.
      assert (C2 : forall q a, usedX [] s2 q a -> exists a0, usedX [] s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0).
      { intros q a Hq. destruct (Cr2 q a Hq) as (a1 & H1 & E1 & F1). rewrite Es1 in H1. apply usedX_upd in H1.
        destruct H1 as [(-> & _ & E) | (Hne & H0)].
        - injection E as <-. exists am. split; [exact Hu|]. split; congruence.
        - exists a1. auto. }
      destruct mi as [[r len]|].
      * destruct Hmi as (rg & Hr & Hkd & Hl & Hlen & Hlen0 & Hno).
        mbinds. apply itok_ask.
        { cbn [req_ok]. exists rg. split; [exact Hr|]. split; [exact Hkd|]. split; [exact Hl|]. split; [exact Hlen|]. split; [exact Hlen0|].
          apply Forall_forall. intros [q a] Hin Hml. cbn [snd] in *.
          apply (used_metas_iff s2 q a (proj1 (inv_keys HI2))) in Hin.
          exact (Hno q a (usedX_intro [] s2 q a eq_refl Hin) Hml). }
        intros z _. msimp. eapply upd_region_kill_spec; [exact HI2 | exact Hr | exact Hkd | exact Hno |].
        intros s3 HI3 Em3 _. apply HQ; [exact HI3| |].
        -- intros q a Hq. apply C2. unfold usedX, MTX, MT in *. rewrite Em3 in Hq. exact Hq.
        -- apply DEL. eapply ub_same_trans; [exact UB2 | apply ub_same_metas; exact Em3].
      * apply itok_ret. apply HQ; [exact HI2 | exact C2 | apply DEL; exact UB2].
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "iff"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "region"; "sptr"; "astate"; "st_regions"; "set_regions"; "rkind"; "st_avail_meta_count"; "rg_kind"; "st_init_done"; "st_metas"; "st_avail_meta_area_count"; "mslot"; "padd"; "PGSZ"; "st_brk"; "brkst"; "st_areas"; "AREA_HDR"; "META_SIZE"; "SP"; "lupd"; "rg_len"; "set_avail_meta_area_count"; "set_avail_meta_areas"; "set_brk"; "BrkDead"; "mkRegion"; "st_active"; "st_usage"; "BrkCur"; "METAS_PER_AREA"; "RkBrk"; "RkMap"; "ameta"; "bind"; "open_area"; "set_init_done"; "st_area_head"; "st_free_meta_head"; "st_meta_alloc_shift"; "BrkNever"; "M"; "MRaw"; "RkMetaRes"; "area_from_mmap"; "ret"; "set_avail_meta"; "set_avail_meta_count"; "st_avail_meta_areas"; "st_mmap_counter"; "MFree"; "alloc_meta"; "area_from_brk"; "rg_live"; "rg_rw"; "set_area_head"; "set_area_tail"; "set_areas"; "set_meta_alloc_shift"; "st_area_tail"; "st_avail_meta"; "@Corelib.Init.Datatypes"; "bool"; "option"; "Some"; "true"; "list"; "nil"; "cons"; "nat"; "app"; "length"; "prod"; "false"; "pair"; "None"; "andb"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "region_of"; "Inv"; "brk_regions"; "resv_total"; "usedX"; "ctx_ok"; "keys_ok"; "InvMeta"; "areas_ok"; "keys"; "memb"; "MT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta"; "open_st"; "am_frame"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "sub"; "le"; "shiftl"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase"; "itok"; "@Corelib.Init.Peano"; "lt"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "upd_meta"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame
  MallocWfRingOps MallocWfSurgery MallocWfRings.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Lemma region_of_app_old s l k : ltac2:(tb__ "0|1|
S6aVk;S4cS6S9Vs;A1M0A2A2S0S44S6A1S53SaS4bS6G0Vl;A3Vs;A2Vk;A2S53Vs;Vk;A2A3F_;").
Proof. intros Hk. unfold region_of. cbn. rewrite nth_error_app1 by exact Hk. reflexivity. Qed.

Lemma region_of_app_new s x : ltac2:(tb__ "0|1|
S0S44S6A1S53SaS4bS6S9Vs;A1M0S49S6Vx;S48S6A1A3A3Vs;A2S4cS6G0A2A2S45S6Vx;A2A3").
Proof. unfold region_of. cbn. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma nth_error_Some_lt {A} (l : list A) k x : ltac2:(tb__ "0|0|
S0S44VA;A1S68VA;Vl;Vk;A3S45VA;Vx;A2A3S6aVk;S4cVA;Vl;A2A2F_;").
Proof.
  revert k. induction l as [|h t IH]; intros [|k] H; cbn in H; try discriminate; cbn; [lia|].
  apply IH in H. lia.
Qed.

Lemma region_of_lt s k rg : ltac2:(tb__ "0|0|
S0S44S6A1S53Vs;Vk;A2S45S6Vrg;A2A3S6aVk;S4cS6S9Vs;A1A2A2F_;").
Proof. unfold region_of. apply nth_error_Some_lt. Qed.

Lemma region_of_app s l k rg : ltac2:(tb__ "0|2|
S0S44S6A1M0S53Vs;Vk;A2S45S6Vrg;A2M1A3S0G0S53SaS4bS6S9Vs;A1Vl;A3Vs;A2Vk;A2G1A3F_;").
Proof. intros H. rewrite region_of_app_old; [exact H | eapply region_of_lt; exact H]. Qed.

Lemma region_of_upd s r f k : ltac2:(tb__ "0|2|
S0S44S6A1M0S53SaS1aS6S9Vs;A1M1Vr;Vf;A4Vs;A2Vk;A2S43G0L_;S51S6eVk;Vr;A2S6fVr;S4cS6G1A2A2A2S45S6Vf;A2S53Vs;Vk;A2X43x2A3").
Proof. unfold region_of. cbn. apply nth_error_lupd. Qed.

Lemma InvMeta_regions X R U s rs : ltac2:(tb__ "0|2|
S4aS6S0S44S6A1M0S53Vs;R2A2S45S6R1A2A3S0SbSdR2A1S26A3S0G0S53SaVrs;Vs;A2M1R4A2S45S6R3A2A3F_;F_;Frg;Fk;S5aVX;VR;VU;Vs;A4S5aVX;VR;VU;G1A4F_;F_;").
Proof.
  intros Hreg (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  assert (EU : forall g am, usedX X (set_regions rs s) g am <-> usedX X s g am) by (intros; unfold usedX, MTX, MT; cbn; tauto).
  split; [exact M1|]. split.
  { intros g am Hg. pose proof (M2 g am Hg) as (G1 & G2 & G3 & G4 & G5 & G6).
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [|exact G6].
    intros Hm. destruct (G5 Hm) as (r & rg & H1 & H2 & H3 & H4 & H5 & H6). exists r, rg.
    split; [exact H1|]. split; [apply Hreg; assumption|]. auto. }
  split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|]. split; [exact M7 | exact M8].
Qed.

Lemma area_slots_disjoint s a1 a2 k1 k2 : ltac2:(tb__ "0|2|
S5bVs;A1S67S7Va1;S16Vs;A1M0A3S67S7Va2;G0A3S2S0S7Va1;Va2;A3A1S1S65Z0M1Vk1;A2S62Vk1;S24A2A2S1S65G1Vk2;A2S62Vk2;S24A2A2S2S0S7S12Va1;S61S17S63S18Vk1;A2A2A2S12Va2;S61S17S63S18Vk2;A2A2A2A3A1F_;F_;F_;F_;F_;F_;").
Proof.
  intros A H1 H2 Hne Hk1 Hk2 E.
  destruct A as (_ & Aok & _).
  destruct (Aok a1 H1) as (r1 & o1 & rg1 & -> & Ho1 & _).
  destruct (Aok a2 H2) as (r2 & o2 & rg2 & -> & Ho2 & _).
  pose proof (f_equal prid E) as Er. pose proof (f_equal poff E) as Eo. cbn [prid poff padd] in Er, Eo. subst r2.
  assert (o1 <> o2) by (intros ->; apply Hne; reflexivity).
  pose proof (eq_refl : AREA_HDR = 24) as C1. pose proof (eq_refl : META_SIZE = 40) as C2.
  pose proof (eq_refl : METAS_PER_AREA = 101) as C3. pose proof (eq_refl : PGSZ = 4096) as C4.
  rewrite C4 in Ho1, Ho2.
  pose proof (Z_div_mod_eq_full o1 4096) as D1. pose proof (Z_div_mod_eq_full o2 4096) as D2.
  rewrite Ho1 in D1. rewrite Ho2 in D2.
  remember (o1 / 4096) as q1 eqn:Q1. remember (o2 / 4096) as q2 eqn:Q2. clear Q1 Q2. lia.
Qed.

Lemma area_slot_inj a k1 k2 : ltac2:(tb__ "0|0|
S0S7S12Va;S61S17S63S18Vk1;A2A2A2S12Va;S61S17S63S18Vk2;A2A2A2A3S0S52Vk1;Vk2;A3F_;").
Proof. destruct a. intros E. pose proof (f_equal poff E) as Eo. cbn [poff padd] in Eo. pose proof (eq_refl : META_SIZE = 40). lia. Qed.

Lemma take_slot_Inv X R U s : ltac2:(tb__ "0|1|
S54VX;VR;VU;Vs;A4S62Z0ScVs;A1M0A2S42Vs;A1S7S6dR1S30S34S12R1S18A2S35S64G0Z1A2Vs;A2A2A3S8S1S2S67S7R2S5cVs;A1A3A1S1S0S43S5dR2VX;A2S4eA3S1S54S49S7R2VX;A3VR;VU;R1A4S7S27S3S57S49S7R4VX;A3R3R2R1A4S57VX;Vs;R2R1A4A2Fam;Fg;A2A2A2Ts';Tm;F_;F_;").
Proof.
  intros HI Hc m s'.
  pose proof (inv_keys HI) as (Knd & Kpl & Kemp & Kav & Krange).
  assert (Hne : st_areas s <> []) by (intros E; pose proof (Kemp E); lia).
  set (la := last (st_areas s) (SP 0%nat 0)) in *.
  assert (Hla : In la (st_areas s)) by (subst la; apply In_last; exact Hne).
  pose proof (Kav Hne) as Em. fold m in Em.
  assert (Hfresh : ~ In m (keys s)).
  { intros Hin. destruct (Kpl m Hin) as (a & k & Ha & Hk & Ep).
    unfold handed in Hk. fold la in Hk.
    destruct (sptr_eq_dec a la) as [->|Hna].
    - rewrite sptr_eqb_refl in Hk. rewrite Em in Ep. apply area_slot_inj in Ep. lia.
    - replace (sptr_eqb a la) with false in Hk by (symmetry; apply sptr_eqb_neq; exact Hna).
      rewrite Em in Ep.
      refine (area_slots_disjoint s la a (METAS_PER_AREA - st_avail_meta_count s) k (inv_areas HI) Hla Ha _ _ _ Ep).
      + intros E. apply Hna. symmetry. exact E.
      + pose proof (eq_refl : METAS_PER_AREA = 101). unfold METAS_PER_AREA in *. lia.
      + pose proof (eq_refl : METAS_PER_AREA = 101). unfold METAS_PER_AREA in *. lia. }
  assert (NXm : memb m X = false).
  { apply memb_false_notIn. intros Hx. apply Hfresh. exact (proj1 (inv_X HI m Hx)). }
  set (s1 := set_avail_meta (padd m META_SIZE) (set_avail_meta_count (st_avail_meta_count s - 1) s)).
  assert (K1 : keys s' = keys s ++ [m]).
  { subst s'. rewrite keys_upd_notIn; [reflexivity|]. exact Hfresh. }
  assert (EMT : forall q, q <> m -> MT s' q = MT s q).
  { intros q Hq. subst s'. rewrite MT_upd_other by exact Hq. reflexivity. }
  assert (Mm : MT s' m = Some MRaw) by (subst s'; apply MT_upd_same).
  assert (Mm0 : MT s m = None) by (unfold MT; apply mlookup_None_iff; exact Hfresh).
  assert (EU : forall g am, usedX (m :: X) s' g am <-> usedX X s g am).
  { intros g am. unfold usedX, MTX. rewrite memb_cons. destruct (sptr_eqb g m) eqn:E; cbn [orb].
    - apply sptr_eqb_eq in E. subst g. rewrite NXm, Mm0. split; discriminate.
    - rewrite EMT by (apply sptr_eqb_neq; exact E). tauto. }
  split; [exact Hfresh|]. split; [exact NXm|]. split; [|exact EU].
  assert (EMTX : forall q, MTX (m :: X) s' q = match MTX X s q with Some x => Some x | None => None end).
  { intros q. unfold MTX. rewrite memb_cons. destruct (sptr_eqb q m) eqn:E; cbn [orb].
    - apply sptr_eqb_eq in E. subst q. rewrite NXm, Mm0. reflexivity.
    - rewrite EMT by (apply sptr_eqb_neq; exact E). destruct (memb q X); [reflexivity|]. destruct (MT s q); reflexivity. }
  assert (EMTX' : forall q, MTX (m :: X) s' q = MTX X s q).
  { intros q. rewrite EMTX. destruct (MTX X s q); reflexivity. }
  eapply (Inv_surgery X (m :: X) R R U U s s' HI).
  - intros k rg Hk _. exact Hk.
  - intros p am' Hp. exists am'. split; [apply EU; exact Hp | reflexivity].
  - intros p am Hp. left. exists am. split; [apply EU; exact Hp | reflexivity].
  - intros g i HR. destruct (inv_reserved HI g i HR) as (am & Hu & Hrest). exists am. split; [apply EU; exact Hu | exact Hrest].
  - intros p i am' _. left. tauto.
  -
    pose proof (inv_ctx HI) as C. unfold ctx_ok in *. subst s' s1. unfold upd_meta. cbn -[Z.pow Z.lt Z.le].
    destruct C as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12&C13).
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj C11 (conj _ C13)))))))))))).
    intros Hi. exfalso. destruct (C12 Hi) as (_ & Ha & _). exact (Hne Ha).
  -
    unfold keys_ok. rewrite K1.
    assert (Ea : st_areas s' = st_areas s) by reflexivity. rewrite Ea.
    assert (Ev : st_avail_meta s' = padd m META_SIZE) by reflexivity.
    assert (Ec : st_avail_meta_count s' = st_avail_meta_count s - 1) by reflexivity.
    assert (Eh : forall a, handed s' a = if sptr_eqb a la then METAS_PER_AREA - (st_avail_meta_count s - 1) else METAS_PER_AREA).
    { intros a. unfold handed. rewrite Ea, Ec. fold la. reflexivity. }
    split.
    { apply NoDup_app_single; assumption. }
    split.
    { intros p Hp. apply in_app_iff in Hp as [Hp | [<- | []]].
      - destruct (Kpl p Hp) as (a & k & Ha & Hk & Ep). exists a, k. split; [exact Ha|]. split; [|exact Ep].
        rewrite Eh. unfold handed in Hk. fold la in Hk. destruct (sptr_eqb a la); lia.
      - exists la, (METAS_PER_AREA - st_avail_meta_count s). split; [exact Hla|]. split; [|exact Em].
        rewrite Eh, sptr_eqb_refl. lia. }
    split; [intros E; exfalso; exact (Hne E)|].
    split; [|rewrite Ec; lia].
    intros _. rewrite Ev, Ec, Em. fold la. destruct la; cbn [padd]. f_equal. pose proof (eq_refl : META_SIZE = 40). lia.
  - exact (inv_areas HI).
  -
    intros x [<-|Hx].
    + rewrite K1, Mm. split; [apply in_app_iff; right; left; reflexivity | exact I].
    + destruct (inv_X HI x Hx) as [Kx Mx]. rewrite K1. split; [apply in_app_iff; left; exact Kx|].
      rewrite EMT; [exact Mx|]. intros ->. exact (Hfresh Kx).
  -
    destruct (inv_rings HI) as (F & A & D). split; [|split].
    + destruct F as (ms & FR & Fall). exists ms. split.
      * eapply ring_ok_ext; [|exact FR]. intros q _. unfold flinks. rewrite EMTX'. reflexivity.
      * intros q pr nx Hq. rewrite EMTX' in Hq. eapply Fall. exact Hq.
    + intros sc Hsc. destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
      change (active_hd s' sc) with (active_hd s sc).
      split; [eapply ring_ok_ext; [|exact Rg]; intros q _; unfold alinks; rewrite EMTX'; reflexivity|].
      split; [intros q am Hq; apply EU in Hq; apply Mem; exact Hq|].
      split; [intros q am Hq; apply EU in Hq; apply Full; exact Hq|].
      split; [intros q am Hq; apply EU in Hq; apply Q1; exact Hq|].
      intros q am Hq; apply EU in Hq; apply Q2; exact Hq.
    + intros q am Hq. apply EU in Hq. apply (D q am Hq).
  -
    intros sc Hsc. change (usage_of s' sc) with (usage_of s sc). rewrite (inv_usage HI sc Hsc). f_equal.
    unfold class_sum. rewrite K1, fold_right_app. cbn [fold_right].
    replace (contrib (m :: X) s' sc m) with 0.
    2:{ unfold contrib, MTX. rewrite memb_cons, sptr_eqb_refl. reflexivity. }
    rewrite Z.add_0_l || idtac.
    assert (E : forall l acc, fold_right (fun q a => contrib (m :: X) s' sc q + a) acc l =
                              fold_right (fun q a => contrib X s sc q + a) acc l).
    { induction l as [|k t IH]; intros acc; [reflexivity|]. cbn [fold_right]. rewrite IH. unfold contrib. rewrite EMTX'. reflexivity. }
    rewrite E. cbn. lia.
Qed.

Lemma Inv_nonmeta X R U s s' : ltac2:(tb__ "0|2|
S54VX;VR;VU;Vs;A4S0S47S4dS7S11A2A1SfVs';A1SfVs;A1A3S0S47S44S7A1M0A1S21Vs';A1S21Vs;A1A3S0G0S2cVs';A1S2cVs;A1A3S0S47S52A1S22Vs';A1S22Vs;A1A3S4aS6S0S44S6A1M1S53Vs;R2A2S45S6R1A2A3S0SbSdR2A1S26A3S0G1S53Vs';R4A2S45S6R3A2A3F_;F_;Frg;Fk;S58Vs';A1S59Vs';A1S5bVs';A1S54VX;VR;VU;Vs';A4F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Em Ea Ef Eu Hreg C K A.
  assert (EMT : forall q, MT s' q = MT s q) by (intros; unfold MT; rewrite Em; reflexivity).
  assert (EU : forall g am, usedX X s' g am <-> usedX X s g am) by (intros; unfold usedX, MTX; rewrite EMT; tauto).
  eapply (Inv_surgery X X R R U U s s' HI).
  - exact Hreg.
  - intros p am' Hp. exists am'. split; [apply EU; exact Hp | reflexivity].
  - intros p am Hp. left. exists am. split; [apply EU; exact Hp | reflexivity].
  - intros g i HR. destruct (inv_reserved HI g i HR) as (am & Hu & Hrest). exists am. split; [apply EU; exact Hu | exact Hrest].
  - intros p i am' _. left. tauto.
  - exact C. - exact K. - exact A.
  - intros x Hx. destruct (inv_X HI x Hx) as [Kx Mx]. unfold keys. rewrite Em, EMT. split; [exact Kx | exact Mx].
  - destruct (inv_rings HI) as (F & AR & D). split; [|split].
    + destruct F as (ms & FR & Fall). exists ms. rewrite Ef. split.
      * eapply ring_ok_ext; [|exact FR]. intros q _. unfold flinks, MTX. rewrite EMT. reflexivity.
      * intros q pr nx Hq. unfold MTX in *. rewrite EMT in Hq. eapply Fall. exact Hq.
    + intros sc Hsc. destruct (AR sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
      replace (active_hd s' sc) with (active_hd s sc) by (unfold active_hd; rewrite Ea; reflexivity).
      split; [eapply ring_ok_ext; [|exact Rg]; intros q _; unfold alinks, MTX; rewrite EMT; reflexivity|].
      split; [intros q am Hq; apply EU in Hq; apply Mem; exact Hq|].
      split; [intros q am Hq; apply EU in Hq; apply Full; exact Hq|].
      split; [intros q am Hq; apply EU in Hq; apply Q1; exact Hq|].
      intros q am Hq; apply EU in Hq; apply Q2; exact Hq.
    + intros q am Hq. apply EU in Hq. apply (D q am Hq).
  - intros sc Hsc. unfold usage_of. rewrite Eu. pose proof (inv_usage HI sc Hsc) as E. unfold usage_of in E. rewrite E.
    f_equal. unfold class_sum, keys. rewrite Em.
    assert (EE : forall l, fold_right (fun q a => contrib X s' sc q + a) 0 l = fold_right (fun q a => contrib X s sc q + a) 0 l).
    { induction l as [|k t IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. unfold contrib, MTX. rewrite EMT. reflexivity. }
    symmetry. apply EE.
Qed.

Lemma Inv_init_brk_dead X R U s : ltac2:(tb__ "0|0|
S54VX;VR;VU;Vs;A4S2S0S15S14Vs;A1S1fA3A1S54VX;VR;VU;S1eS1fS2aS46Vs;A2A2A4F_;F_;").
Proof.
  intros HI Hb. eapply Inv_nonmeta; try exact HI; try reflexivity.
  - intros k rg Hk _. exact Hk.
  - pose proof (inv_ctx HI) as C. unfold ctx_ok in *.
    destruct C as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12&C13).
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj C11 (conj _ _)))))))))))).
    + cbn [st_init_done set_brk set_init_done]. intros Hi. discriminate Hi.
    + cbn [st_init_done st_brk set_brk set_init_done]. intros _. discriminate.
  - exact (inv_keys HI).
  - pose proof (inv_areas HI) as A. unfold areas_ok in *.
    destruct A as (A1&A2&A3&A4&A5&A6&A7&A8).
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj _ A8))))))).
    cbn [st_brk set_brk set_init_done]. change (brk_regions (set_brk BrkDead (set_init_done true s))) with (brk_regions s).
    change (region_of (set_brk BrkDead (set_init_done true s))) with (region_of s).
    destruct (st_brk s) as [| |r p] eqn:Eb.
    + intros r Hr. rewrite A7 in Hr. destruct Hr.
    + exfalso. apply Hb. reflexivity.
    + intros r' Hr'. destruct A7 as (Hbr & rg & Hrg & Hl & Hlen & Hp). rewrite Hbr in Hr' |- *.
      destruct Hr' as [<-|[]]. split; [reflexivity|]. exists rg. split; [exact Hrg|]. split; [exact Hl|].
      rewrite Hlen. pose proof (eq_refl : PGSZ = 4096). split; [|nia].
      rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma Inv_brk_dead X R U s : ltac2:(tb__ "0|0|
S54VX;VR;VU;Vs;A4S2S0S15S14Vs;A1S1fA3A1S0S43SeVs;A1S46A3S54VX;VR;VU;S1eS1fVs;A2A4F_;F_;F_;").
Proof.
  intros HI Hb Hinit. rewrite <- (set_init_done_same s Hinit) at 1. exact (Inv_init_brk_dead X R U s HI Hb).
Qed.

Lemma brk_regions_app s x : ltac2:(tb__ "0|3|
S0S47S4aA1M0S55SaS4bS6S9Vs;A1M1S49S6Vx;S48S6A1A3A3Vs;A2A1S4bS4aS55Vs;A1SbG0Lx;SdVx;A1S49S4aS4cS6G1A2S48S4aA1M2A3G2G2Xbx3A3A3").
Proof.
  unfold brk_regions. cbn [st_regions set_regions]. rewrite length_app. cbn [length].
  rewrite Nat.add_1_r, seq_S, flat_map_app. cbn [flat_map]. rewrite region_of_app_new, app_nil_r. f_equal.
  apply flat_map_ext_In. intros k Hk. apply in_seq in Hk. rewrite region_of_app_old by lia. reflexivity.
Qed.

Lemma brk_regions_upd s r x rg : ltac2:(tb__ "0|0|
S0S44S6A1S53Vs;Vr;A2S45S6Vrg;A2A3S0SbSdVx;A1SdVrg;A1A3S0S47S4aA1S55SaS1aS6S9Vs;A1Vr;Vx;A4Vs;A2A1S55Vs;A1A3F_;F_;").
Proof.
  intros Hr Hk. unfold brk_regions. cbn [st_regions set_regions]. rewrite length_lupd.
  apply flat_map_ext_In. intros k Hk'. rewrite region_of_upd.
  destruct (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 _]. apply Nat.eqb_eq in E1. subst k. rewrite Hr, Hk. reflexivity.
Qed.

Lemma resv_total_app s x : ltac2:(tb__ "0|1|
S0S52S56SaS4bS6S9Vs;A1S49S6Vx;S48S6A1A3A3Vs;A2A1S61S56Vs;A1SbS52Lx;SdVx;A1Z0M0S1bVx;A1G0Xbx3A2A3").
Proof.
  unfold resv_total. cbn [st_regions set_regions]. rewrite fold_right_app. cbn [fold_right].
  assert (G : forall l acc, fold_right (fun rg a => match rg_kind rg with RkMetaRes => rg_len rg + a | _ => a end) acc l =
                           fold_right (fun rg a => match rg_kind rg with RkMetaRes => rg_len rg + a | _ => a end) 0 l + acc).
  { induction l as [|h t IH]; intros acc; cbn; [lia|]. rewrite IH. destruct (rg_kind h); lia. }
  rewrite G. destruct (rg_kind x); lia.
Qed.

Lemma resv_total_upd s r x rg : ltac2:(tb__ "0|2|
S0S44S6A1S53Vs;Vr;A2S45S6Vrg;A2A3SbOLx;SdVrg;A1S2S0SbSdVx;A1S31A3M0A1M1S1G0S0S52S1bVx;A1S1bVrg;A1A3A2G1Xbx3S0S52S56SaS1aS6S9Vs;A1Vr;Vx;A4Vs;A2A1S56Vs;A1A3F_;F_;").
Proof.
  unfold resv_total, region_of. cbn [st_regions set_regions].
  revert r. induction (st_regions s) as [|h t IH]; intros [|r] Hr Hk; cbn in Hr |- *; try discriminate.
  - injection Hr as ->. destruct (rg_kind rg) eqn:E.
    + destruct (rg_kind x); [reflexivity| congruence | reflexivity].
    + destruct Hk as [-> ->]. reflexivity.
    + destruct (rg_kind x); [reflexivity | congruence | reflexivity].
  - rewrite (IH r Hr Hk). reflexivity.
Qed.

Lemma Inv_new_resv X R U s : ltac2:(tb__ "0|3|
S54VX;VR;VU;Vs;A4S0S52S10Vs;A1Z0A3S0S43SeVs;A1S46A3S66Z2S2dVs;A1M0A2S52S4cS6S9Vs;A1M1A2S4aS54VX;VR;VU;S40S61G0Z1M2A2S1cS64R2G2A2S1dS19R1S13A2SaS4bS6G1S49S6S20S31S63R2S13A2S48S52A1S46A4S48S6A1A3A3Vs;A2A2A2A2A4Tr;Tn;F_;F_;F_;").
Proof.
  intros HI Hc0 Hinit n r.
  pose proof (inv_ctx HI) as C. pose proof C as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12).
  assert (Hn : n = 2 * 2 ^ st_meta_alloc_shift s) by (subst n; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  assert (Hpow : 1 <= 2 ^ st_meta_alloc_shift s).
  { pose proof (Z.pow_pos_nonneg 2 (st_meta_alloc_shift s)). lia. }
  assert (Hn2 : 2 <= n) by lia.
  pose proof (eq_refl : PGSZ = 4096) as HP.
  set (x := mkRegion RkMetaRes (n * PGSZ) [] true).
  set (s' := set_meta_alloc_shift _ _).
  assert (ERG : forall k, region_of s' k = region_of (set_regions (st_regions s ++ [x]) s) k) by reflexivity.
  eapply Inv_nonmeta; try exact HI; try reflexivity.
  - intros k rg Hk _. rewrite ERG. apply region_of_app. exact Hk.
  - unfold ctx_ok. subst s'. simp_st.
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj _ (conj _ (conj _ (proj2 C12))))))))))))); [lia | lia |].
    intros Hi. rewrite Hinit in Hi. discriminate.
  - exact (inv_keys HI).
  - pose proof (inv_areas HI) as (A1&A2&A3&A4&A5&A6&A7&A8&A9). unfold areas_ok.
    refine (conj A1 (conj _ (conj A3 (conj A4 (conj _ (conj _ (conj _ (conj _ _)))))))).
    + intros a Ha. destruct (A2 a Ha) as (ra & oa & rga & Ea & Ho & Hlo & Hrg & Hl & Hhi & Hk).
      exists ra, oa, rga. repeat (split; [assumption|]). split; [| split; [exact Hl | split; [exact Hhi | exact Hk]]].
      rewrite ERG. apply region_of_app. exact Hrg.
    + intros k rg Hk Hkind. rewrite ERG in Hk.
      unfold region_of in Hk. cbn [st_regions set_regions] in Hk. rewrite nth_error_app in Hk.
      destruct (Nat.ltb k (length (st_regions s))) eqn:El.
      * eapply A5; [exact Hk | exact Hkind].
      * destruct (k - length (st_regions s))%nat as [|k'] eqn:Ek; cbn in Hk; [|destruct k'; discriminate].
        injection Hk as <-. unfold x. cbn [rg_live rg_len]. split; [reflexivity|]. split; [|nia]. rewrite HP. apply Z_mod_mult.
    + change (resv_total (set_regions (st_regions s ++ [x]) s) = 2 * PGSZ * (2 ^ (st_meta_alloc_shift s + 1) - 1)).
      rewrite resv_total_app. unfold x. cbn [rg_kind rg_len]. rewrite A6, Z.pow_add_r, Hn by lia. change (2 ^ 1) with 2. lia.
    + change (st_brk s') with (st_brk s).
      assert (EB : brk_regions s' = brk_regions s).
      { change (brk_regions (set_regions (st_regions s ++ [x]) s) = brk_regions s).
        rewrite brk_regions_app. unfold x. cbn [rg_kind]. apply app_nil_r. }
      rewrite EB.
      destruct (st_brk s) as [| |rb pb].
      * exact A7.
      * intros rr Hrr. destruct (A7 rr Hrr) as (Hbr & rg & Hrg & Hrest). split; [exact Hbr|]. exists rg.
        split; [rewrite ERG; apply region_of_app; exact Hrg | exact Hrest].
      * destruct A7 as (Hbr & rg & Hrg & Hrest). split; [exact Hbr|]. exists rg.
        split; [rewrite ERG; apply region_of_app; exact Hrg | exact Hrest].
    + change (st_avail_meta_area_count s') with (n - 1). change (st_avail_meta_areas s') with (SP r PGSZ).
      intros _. exists r, PGSZ, x.
      split; [reflexivity|]. split.
      { rewrite ERG. subst r. apply region_of_app_new. }
      unfold x. cbn [rg_kind rg_live rg_len rg_rw]. split; [reflexivity|]. split; [reflexivity|].
      split; [rewrite HP; reflexivity|]. split; [lia|]. split; [nia|]. intros y [].
    + intros k rg Hk. rewrite ERG in Hk. unfold region_of in Hk. cbn [st_regions set_regions] in Hk. rewrite nth_error_app in Hk.
      destruct (Nat.ltb k (length (st_regions s))); [eapply A9; exact Hk|].
      destruct (k - length (st_regions s))%nat as [|k']; cbn in Hk; [injection Hk as <-; cbn; nia | destruct k'; discriminate].
Qed.

Definition open_st (p : sptr) (s : astate) : astate := ltac2:(tb__ "0|2|
S34S12Vp;S17A2S35S24S3fS4bS7S16Vs;A1S49S7Vp;S48S7A1A3A3S3dS44S7A1M0G0Lx;S2bVs;A1S7S45S7R1A2Ls0;S45S7Vp;A2M1X44x2S3eG1S1dS12Vp;Z1000A2S1cS64S10Vs;A1Z1A2Vs;A2A2A2A2A2A2A2").

Lemma st_areas_open p s : ltac2:(tb__ "0|0|
S0S47S7A1S16S5fVp;Vs;A2A1S4bS7S16Vs;A1S49S7Vp;S48S7A1A3A3A3"). Proof. reflexivity. Qed.
Lemma st_area_head_open p s : ltac2:(tb__ "0|1|
S0S44S7A1M0S2bS5fVp;Vs;A2A1G0G0Lx;S2bVs;A1S7S45S7R1A2Ls0;S45S7Vp;A2X44x2A3"). Proof. reflexivity. Qed.
Lemma st_area_tail_open p s : ltac2:(tb__ "0|0|
S0S44S7A1S41S5fVp;Vs;A2A1S45S7Vp;A2A3"). Proof. reflexivity. Qed.
Lemma st_regions_open p s : ltac2:(tb__ "0|0|
S0S47S6A1S9S5fVp;Vs;A2A1S9Vs;A1A3"). Proof. reflexivity. Qed.
Lemma st_brk_open p s : ltac2:(tb__ "0|0|
S0S15S14S5fVp;Vs;A2A1S14Vs;A1A3"). Proof. reflexivity. Qed.
Lemma st_shift_open p s : ltac2:(tb__ "0|0|
S0S52S2dS5fVp;Vs;A2A1S2dVs;A1A3"). Proof. reflexivity. Qed.
Lemma st_area_count_open p s : ltac2:(tb__ "0|0|
S0S52S10S5fVp;Vs;A2A1S64S10Vs;A1Z1A2A3"). Proof. reflexivity. Qed.
Lemma st_areas_ptr_open p s : ltac2:(tb__ "0|0|
S0S7S36S5fVp;Vs;A2A1S12Vp;Z1000A2A3"). Proof. reflexivity. Qed.
Lemma region_of_open p s k : ltac2:(tb__ "0|0|
S0S44S6A1S53S5fVp;Vs;A2Vk;A2S53Vs;Vk;A2A3"). Proof. reflexivity. Qed.
Lemma brk_regions_open p s : ltac2:(tb__ "0|0|
S0S47S4aA1S55S5fVp;Vs;A2A1S55Vs;A1A3"). Proof. reflexivity. Qed.
Lemma resv_total_open p s : ltac2:(tb__ "0|0|
S0S52S56S5fVp;Vs;A2A1S56Vs;A1A3"). Proof. reflexivity. Qed.
Lemma st_metas_open p s : ltac2:(tb__ "0|0|
S0S47S4dS7S11A2A1SfS5fVp;Vs;A2A1SfVs;A1A3"). Proof. reflexivity. Qed.

Lemma keys_ok_open s p : ltac2:(tb__ "0|0|
S59Vs;A1S0S52ScVs;A1Z0A3S2S67S7Vp;S16Vs;A1A3A1S59S5fVp;Vs;A2A1F_;F_;F_;").
Proof.
  intros (Knd & Kpl & Kemp & Kav & Krange) Hc0 Hfresh.
  unfold keys_ok, key_placed, handed. unfold open_st. simp_st.
  change (keys (set_avail_meta _ _)) with (keys s).
  rewrite last_app_single.
  split; [exact Knd|]. split.
  { intros q Hq. destruct (Kpl q Hq) as (a & k & Ha & Hk & E). exists a, k.
    split; [apply in_app_iff; left; exact Ha|]. split; [|exact E].
    unfold handed in Hk. replace (sptr_eqb a p) with false by (symmetry; apply sptr_eqb_neq; intros ->; exact (Hfresh Ha)).
    destruct (sptr_eqb a (last (st_areas s) (SP 0%nat 0))); lia. }
  split; [intros E; destruct (st_areas s); discriminate|].
  split; [| pose proof (eq_refl : METAS_PER_AREA = 101); lia].
  intros _. rewrite Z.sub_diag, Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.

Lemma ctx_ok_open s p : ltac2:(tb__ "0|0|
S58Vs;A1S0S43SeVs;A1S46A3S65Z1S10Vs;A1A2S58S5fVp;Vs;A2A1F_;F_;F_;").
Proof.
  intros C Hi Hc. unfold ctx_ok in *. unfold open_st. simp_st.
  destruct C as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12&C13).
  refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj _ (conj _ C13)))))))))))); [lia|].
  intros H. rewrite Hi in H. discriminate.
Qed.

Lemma brk_regions_In s r : ltac2:(tb__ "0|0|
S67S4aVr;S55Vs;A1A3S4S6S6S1S0S44S6A1S53Vs;Vr;A2S45S6R1A2A3S0SbSdR1A1S25A3A2Lrg;A2F_;").
Proof.
  unfold brk_regions. intros H. apply in_flat_map in H as (k & Hk & Hin).
  destruct (region_of s k) as [rg|] eqn:E; [|destruct Hin].
  destruct (rg_kind rg) eqn:Ek; try (destruct Hin; fail); destruct Hin as [<-|[]].
  exists rg. auto.
Qed.

Lemma Inv_open_resv X R U s r o rg : ltac2:(tb__ "0|2|
S54VX;VR;VU;Vs;A4S62Z0M0S10Vs;A1A2S0S52ScVs;A1G0A3S0S43SeVs;A1S46A3S0S7S36Vs;A1S19Vr;Vo;A2M1A3S0S44S6A1S53Vs;Vr;A2S45S6Vrg;A2A3S54VX;VR;VU;S5fG1SaS1aS6S9Vs;A1Vr;S20SdVrg;A1S1bVrg;A1S4bS52S3cVrg;A1S49S52Vo;S48S52A1A3A3S3bVrg;A1A4A4Vs;A2A2A4F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hc Hm0 Hinit Ep Hrg.
  pose proof (inv_areas HI) as (A1&A2&A3&A4&A5&A6&A7&A8&A9).
  destruct (A8 Hc) as (r' & o' & rg' & Ep' & Hrg' & Hk & Hl & Ho & Hlo & Hlen & Hrw).
  rewrite Ep in Ep'. injection Ep' as <- <-. rewrite Hrg in Hrg'. injection Hrg' as <-.
  set (x := mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [o]) (rg_live rg)).
  set (s1 := set_regions (lupd (st_regions s) r x) s).
  pose proof (region_of_lt _ _ _ Hrg) as Hrlt.
  assert (ERG : forall k, region_of (open_st (SP r o) s1) k = region_of s1 k) by reflexivity.
  assert (R1 : region_of s1 r = Some x).
  { subst s1. rewrite region_of_upd, Nat.eqb_refl. replace (Nat.ltb r (length (st_regions s))) with true; [reflexivity|].
    symmetry. apply Nat.ltb_lt. exact Hrlt. }
  assert (R2 : forall k, k <> r -> region_of s1 k = region_of s k).
  { intros k Hk'. subst s1. rewrite region_of_upd. replace (Nat.eqb k r) with false; [reflexivity|].
    symmetry. apply Nat.eqb_neq. exact Hk'. }
  assert (Hfresh : ~ In (SP r o) (st_areas s)).
  { intros Hin. destruct (A2 _ Hin) as (r2 & o2 & rg2 & E2 & _ & _ & Hrg2 & _ & _ & Hkind2).
    injection E2 as <- <-. rewrite Hrg in Hrg2. injection Hrg2 as <-. rewrite Hk in Hkind2.
    pose proof (Hrw o Hkind2). lia. }
  pose proof (eq_refl : PGSZ = 4096) as HP.
  eapply Inv_nonmeta; try exact HI; try reflexivity.
  - intros k rgk Hk' Hkind. rewrite ERG. destruct (Nat.eq_dec k r) as [->|Hne].
    + rewrite Hrg in Hk'. injection Hk' as ->. rewrite Hk in Hkind. discriminate.
    + rewrite R2 by exact Hne. exact Hk'.
  - apply ctx_ok_open; [exact (inv_ctx HI) | exact Hinit | change (st_avail_meta_area_count s1) with (st_avail_meta_area_count s); lia].
  - apply keys_ok_open; [exact (inv_keys HI) | exact Hm0 | exact Hfresh].
  - unfold areas_ok.
    rewrite !st_areas_open, st_area_head_open, st_area_tail_open, st_brk_open, st_shift_open,
            st_area_count_open, st_areas_ptr_open, brk_regions_open, resv_total_open.
    change (st_areas s1) with (st_areas s). change (st_area_head s1) with (st_area_head s).
    change (st_meta_alloc_shift s1) with (st_meta_alloc_shift s). change (st_brk s1) with (st_brk s).
    change (st_avail_meta_area_count s1) with (st_avail_meta_area_count s).
    split.
    { apply NoDup_app_single; [exact A1 | exact Hfresh]. }
    split.
    { intros a Ha. apply in_app_iff in Ha as [Ha | [<- | []]].
      - destruct (A2 a Ha) as (ra & oa & rga & Ea & Hoa & Hloa & Hrga & Hla & Hhia & Hka).
        exists ra, oa. destruct (Nat.eq_dec ra r) as [->|Hne].
        + exists x. rewrite Hrg in Hrga. injection Hrga as ->. split; [exact Ea|]. split; [exact Hoa|]. split; [exact Hloa|].
          split; [rewrite ERG; exact R1|]. unfold x. cbn [rg_live rg_len rg_kind rg_rw].
          split; [exact Hla|]. split; [exact Hhia|]. rewrite Hk in Hka |- *. apply in_app_iff. left. exact Hka.
        + exists rga. split; [exact Ea|]. split; [exact Hoa|]. split; [exact Hloa|].
          split; [rewrite ERG, R2 by exact Hne; exact Hrga|]. split; [exact Hla|]. split; [exact Hhia | exact Hka].
      - exists r, o, x. split; [reflexivity|]. split; [exact Ho|]. split; [exact Hlo|]. split; [rewrite ERG; exact R1|].
        unfold x. cbn [rg_live rg_len rg_kind rg_rw]. split; [exact Hl|]. split; [nia|].
        rewrite Hk. apply in_app_iff. right. left. reflexivity. }
    split.
    { rewrite A3. destruct (st_areas s); reflexivity. }
    split.
    { destruct (st_areas s ++ [SP r o]) as [|a0 l0] eqn:E.
      - exfalso. destruct (st_areas s); discriminate.
      - rewrite <- E, last_app_single. reflexivity. }
    split.
    { intros k rgk Hk'. rewrite ERG in Hk'. destruct (Nat.eq_dec k r) as [->|Hne].
      - rewrite R1 in Hk'. injection Hk' as <-. unfold x. cbn [rg_kind rg_live rg_len]. intros _. eapply A5; eauto.
      - rewrite R2 in Hk' by exact Hne. eapply A5; eauto. }
    split.
    { subst s1. rewrite (resv_total_upd s r x rg Hrg); [exact A6|].
      unfold x. cbn [rg_kind rg_len]. rewrite Hk. split; reflexivity. }
    split.
    { assert (EB : brk_regions s1 = brk_regions s).
      { subst s1. eapply brk_regions_upd; [exact Hrg | reflexivity]. }
      rewrite EB. destruct (st_brk s) as [| |rb pb].
      - exact A7.
      - intros rr Hrr. destruct (A7 rr Hrr) as (Hbr & rgb & Hrgb & Hrest). split; [exact Hbr|]. exists rgb. split; [|exact Hrest].
        rewrite ERG, R2; [exact Hrgb|]. intros ->.
        destruct (brk_regions_In s r Hrr) as (rg2 & Hrg2 & Hk2). rewrite Hrg in Hrg2. injection Hrg2 as <-. rewrite Hk in Hk2. discriminate.
      - destruct A7 as (Hbr & rgb & Hrgb & Hrest). split; [exact Hbr|]. exists rgb. split; [|exact Hrest].
        rewrite ERG, R2; [exact Hrgb|]. intros ->.
        destruct (brk_regions_In s r ltac:(rewrite Hbr; left; reflexivity)) as (rg2 & Hrg2 & Hk2).
        rewrite Hrg in Hrg2. injection Hrg2 as <-. rewrite Hk in Hk2. discriminate. }
    split.
    { intros Hc'. exists r, (o + 4096), x. split; [reflexivity|]. split; [rewrite ERG; exact R1|].
      unfold x. cbn [rg_kind rg_live rg_len rg_rw]. split; [exact Hk|]. split; [exact Hl|].
      split; [rewrite HP in Ho |- *; replace (o + 4096) with (o + 1 * 4096) by lia; rewrite Z_mod_plus_full; exact Ho|].
      split; [lia|]. split; [nia|].
      intros y Hy. apply in_app_iff in Hy as [Hy | [<- | []]]; [pose proof (Hrw y Hy); lia | lia]. }
    { intros k rgk Hk'. rewrite ERG in Hk'. destruct (Nat.eq_dec k r) as [->|Hne].
      - rewrite R1 in Hk'. injection Hk' as <-. unfold x. cbn [rg_len]. eapply A9. exact Hrg.
      - rewrite R2 in Hk' by exact Hne. eapply A9. exact Hk'. }
Qed.

Lemma Inv_open_brk_first X R U s : ltac2:(tb__ "0|3|
S54VX;VR;VU;Vs;A4S0S15S14Vs;A1S2eA3S0S52S10Vs;A1Z0M0A3S0S52ScVs;A1G0A3S4cS6S9Vs;A1M1A2S4aS1eS23R1Z2M2A2S1dS19R1S13A2S1cZ1SaS4bS6G1S49S6S20S25S63G2S13A2S48S52A1S46A4S48S6A1A3A3S2aS46Vs;A2A2A2A2A2S8S54VX;VR;VU;S5fS19R2S13A2R1A2A4Ts1;Tr;F_;F_;F_;F_;").
Proof.
  intros HI Hb Hc0 Hm0 r s1.
  pose proof (inv_areas HI) as (A1&A2&A3&A4&A5&A6&A7&A8&A9).
  set (x := mkRegion RkBrk (2 * PGSZ) [] true) in *.
  assert (ERG : forall k, region_of (open_st (SP r PGSZ) s1) k = region_of (set_regions (st_regions s ++ [x]) s) k) by reflexivity.
  assert (R1 : region_of (set_regions (st_regions s ++ [x]) s) r = Some x) by (subst r; apply region_of_app_new).
  pose proof (eq_refl : PGSZ = 4096) as HP.
  rewrite Hb in A7.
  assert (Hfresh : ~ In (SP r PGSZ) (st_areas s)).
  { intros Hin. destruct (A2 _ Hin) as (r2 & o2 & rg2 & E2 & _ & _ & Hrg2 & _). injection E2 as <- <-.
    pose proof (region_of_lt _ _ _ Hrg2). lia. }
  eapply Inv_nonmeta; try exact HI; try reflexivity.
  - intros k rgk Hk' _. rewrite ERG. apply region_of_app. exact Hk'.
  - apply ctx_ok_open; [| reflexivity | change (st_avail_meta_area_count s1) with 1; lia].
    pose proof (inv_ctx HI) as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12&C13). unfold ctx_ok. subst s1. simp_st.
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj _ (conj _ _)))))))))))); [lia| |].
    + intros Hi. discriminate Hi.
    + intros _. discriminate.
  - apply keys_ok_open; [| exact Hm0 | exact Hfresh].
    pose proof (inv_keys HI) as K. unfold keys_ok, key_placed, handed in *. subst s1. simp_st. exact K.
  - unfold areas_ok.
    rewrite !st_areas_open, st_area_head_open, st_area_tail_open, st_brk_open, st_shift_open,
            st_area_count_open, st_areas_ptr_open, brk_regions_open, resv_total_open.
    change (st_areas s1) with (st_areas s). change (st_area_head s1) with (st_area_head s).
    change (st_meta_alloc_shift s1) with (st_meta_alloc_shift s). change (st_brk s1) with (BrkCur r 2).
    change (st_avail_meta_area_count s1) with 1.
    split.
    { apply NoDup_app_single; [exact A1 | exact Hfresh]. }
    split.
    { intros a Ha. apply in_app_iff in Ha as [Ha | [<- | []]].
      - destruct (A2 a Ha) as (ra & oa & rga & Ea & Hoa & Hloa & Hrga & Hla & Hhia & Hka).
        exists ra, oa, rga. split; [exact Ea|]. split; [exact Hoa|]. split; [exact Hloa|].
        split; [rewrite ERG; apply region_of_app; exact Hrga|]. split; [exact Hla|]. split; [exact Hhia | exact Hka].
      - exists r, PGSZ, x. split; [reflexivity|]. split; [rewrite HP; reflexivity|]. split; [lia|]. split; [rewrite ERG; exact R1|].
        unfold x. cbn [rg_live rg_len rg_kind rg_rw]. split; [reflexivity|]. split; [lia | exact I]. }
    split.
    { rewrite A3. destruct (st_areas s); reflexivity. }
    split.
    { destruct (st_areas s ++ [SP r PGSZ]) as [|a0 l0] eqn:E.
      - exfalso. destruct (st_areas s); discriminate.
      - rewrite <- E, last_app_single. reflexivity. }
    split.
    { intros k rgk Hk'. rewrite ERG in Hk'. unfold region_of in Hk'. cbn [st_regions set_regions] in Hk'.
      rewrite nth_error_app in Hk'. destruct (Nat.ltb k (length (st_regions s))) eqn:El.
      - eapply A5. exact Hk'.
      - destruct (k - length (st_regions s))%nat as [|k']; cbn in Hk'; [|destruct k'; discriminate].
        injection Hk' as <-. unfold x. cbn [rg_kind]. discriminate. }
    split.
    { change (resv_total s1) with (resv_total (set_regions (st_regions s ++ [x]) s)).
      rewrite resv_total_app. unfold x. cbn [rg_kind]. rewrite Z.add_0_r. exact A6. }
    split.
    { change (brk_regions s1) with (brk_regions (set_regions (st_regions s ++ [x]) s)).
      rewrite brk_regions_app, A7. unfold x. cbn [rg_kind app]. split; [reflexivity|].
      exists x. split; [rewrite ERG; exact R1|]. unfold x. cbn [rg_live rg_len]. split; [reflexivity|]. split; [lia | lia]. }
    split.
    { intros Hc'. lia. }
    { intros k rgk Hk'. rewrite ERG in Hk'. unfold region_of in Hk'. cbn [st_regions set_regions] in Hk'. rewrite nth_error_app in Hk'.
      destruct (Nat.ltb k (length (st_regions s))); [eapply A9; exact Hk'|].
      destruct (k - length (st_regions s))%nat as [|k']; cbn in Hk'; [injection Hk' as <-; cbn; lia | destruct k'; discriminate]. }
Qed.

Lemma Inv_open_brk_grow X R U s r p rg : ltac2:(tb__ "0|3|
S54VX;VR;VU;Vs;A4S0S15S14Vs;A1S23Vr;Vp;A2A3S0S52S10Vs;A1Z0M0A3S0S52ScVs;A1G0A3S0S43SeVs;A1S46A3S0S44S6A1S53Vs;Vr;A2S45S6Vrg;A2A3S20S25S61S1bVrg;A1S13A2S48S52A1S46A4S6S1eS23Vr;S61Vp;Z1M1A2A2S1dS19Vr;S63S13Vp;A2A2M2S1cG1SaS1aS6S9Vs;A1Vr;R1A4Vs;A2A2A2A2S8S54VX;VR;VU;S5fG2R1A2A4Ts1;Tx;F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hb Hc0 Hm0 Hinit Hrg x s1.
  pose proof (inv_areas HI) as (A1&A2&A3&A4&A5&A6&A7&A8&A9).
  rewrite Hb in A7. destruct A7 as (Hbr & rg0 & Hrg0 & Hl0 & Hlen0 & Hp2).
  rewrite Hrg in Hrg0. injection Hrg0 as <-.
  pose proof (region_of_lt _ _ _ Hrg) as Hrlt.
  assert (ERG : forall k, region_of (open_st (SP r (PGSZ * p)) s1) k = region_of (set_regions (lupd (st_regions s) r x) s) k) by reflexivity.
  assert (R1 : region_of (set_regions (lupd (st_regions s) r x) s) r = Some x).
  { rewrite region_of_upd, Nat.eqb_refl. replace (Nat.ltb r (length (st_regions s))) with true; [reflexivity|].
    symmetry. apply Nat.ltb_lt. exact Hrlt. }
  assert (R2 : forall k, k <> r -> region_of (set_regions (lupd (st_regions s) r x) s) k = region_of s k).
  { intros k Hk'. rewrite region_of_upd. replace (Nat.eqb k r) with false; [reflexivity|]. symmetry. apply Nat.eqb_neq. exact Hk'. }
  pose proof (eq_refl : PGSZ = 4096) as HP.
  assert (Hkind : rg_kind rg = RkBrk).
  { destruct (brk_regions_In s r ltac:(rewrite Hbr; left; reflexivity)) as (rg2 & Hrg2 & Hk2). rewrite Hrg in Hrg2. injection Hrg2 as <-. exact Hk2. }
  assert (Hfresh : ~ In (SP r (PGSZ * p)) (st_areas s)).
  { intros Hin. destruct (A2 _ Hin) as (r2 & o2 & rg2 & E2 & _ & _ & Hrg2 & _ & Hhi2 & _).
    pose proof (f_equal prid E2) as Er2. pose proof (f_equal poff E2) as Eo2. cbn [prid poff] in Er2, Eo2. subst r2 o2.
    rewrite Hrg in Hrg2. injection Hrg2 as <-. rewrite Hlen0 in Hhi2. nia. }
  eapply Inv_nonmeta; try exact HI; try reflexivity.
  - intros k rgk Hk' Hkk. rewrite ERG. destruct (Nat.eq_dec k r) as [->|Hne].
    + rewrite Hrg in Hk'. injection Hk' as ->. rewrite Hkind in Hkk. discriminate.
    + rewrite R2 by exact Hne. exact Hk'.
  - apply ctx_ok_open; [| exact Hinit | change (st_avail_meta_area_count s1) with 1; lia].
    pose proof (inv_ctx HI) as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12&C13). unfold ctx_ok. subst s1. simp_st.
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj _ (conj _ _)))))))))))); [lia| |].
    + intros Hi. rewrite Hinit in Hi. discriminate.
    + intros _. discriminate.
  - apply keys_ok_open; [| exact Hm0 | exact Hfresh].
    pose proof (inv_keys HI) as K. unfold keys_ok, key_placed, handed in *. subst s1. simp_st. exact K.
  - unfold areas_ok.
    rewrite !st_areas_open, st_area_head_open, st_area_tail_open, st_brk_open, st_shift_open,
            st_area_count_open, st_areas_ptr_open, brk_regions_open, resv_total_open.
    change (st_areas s1) with (st_areas s). change (st_area_head s1) with (st_area_head s).
    change (st_meta_alloc_shift s1) with (st_meta_alloc_shift s). change (st_brk s1) with (BrkCur r (p + 1)).
    change (st_avail_meta_area_count s1) with 1.
    split.
    { apply NoDup_app_single; [exact A1 | exact Hfresh]. }
    split.
    { intros a Ha. apply in_app_iff in Ha as [Ha | [<- | []]].
      - destruct (A2 a Ha) as (ra & oa & rga & Ea & Hoa & Hloa & Hrga & Hla & Hhia & Hka).
        exists ra, oa. destruct (Nat.eq_dec ra r) as [->|Hne].
        + exists x. rewrite Hrg in Hrga. injection Hrga as ->. split; [exact Ea|]. split; [exact Hoa|]. split; [exact Hloa|].
          split; [rewrite ERG; exact R1|]. unfold x. cbn [rg_live rg_len rg_kind rg_rw].
          split; [reflexivity|]. split; [lia | exact I].
        + exists rga. split; [exact Ea|]. split; [exact Hoa|]. split; [exact Hloa|].
          split; [rewrite ERG, R2 by exact Hne; exact Hrga|]. split; [exact Hla|]. split; [exact Hhia | exact Hka].
      - exists r, (PGSZ * p), x. split; [reflexivity|]. split; [rewrite HP, Z.mul_comm; apply Z_mod_mult|]. split; [nia|].
        split; [rewrite ERG; exact R1|].
        unfold x. cbn [rg_live rg_len rg_kind rg_rw]. split; [reflexivity|]. split; [lia | exact I]. }
    split.
    { rewrite A3. destruct (st_areas s); reflexivity. }
    split.
    { destruct (st_areas s ++ [SP r (PGSZ * p)]) as [|a0 l0] eqn:E.
      - exfalso. destruct (st_areas s); discriminate.
      - rewrite <- E, last_app_single. reflexivity. }
    split.
    { intros k rgk Hk'. rewrite ERG in Hk'. destruct (Nat.eq_dec k r) as [->|Hne].
      - rewrite R1 in Hk'. injection Hk' as <-. unfold x. cbn [rg_kind]. discriminate.
      - rewrite R2 in Hk' by exact Hne. eapply A5. exact Hk'. }
    split.
    { change (resv_total s1) with (resv_total (set_regions (lupd (st_regions s) r x) s)).
      rewrite (resv_total_upd s r x rg Hrg); [exact A6|]. rewrite Hkind. unfold x. cbn [rg_kind]. discriminate. }
    split.
    { change (brk_regions s1) with (brk_regions (set_regions (lupd (st_regions s) r x) s)).
      rewrite (brk_regions_upd s r x rg Hrg) by (rewrite Hkind; reflexivity). split; [exact Hbr|].
      exists x. split; [rewrite ERG; exact R1|]. unfold x. cbn [rg_live rg_len]. split; [reflexivity|]. split; [lia | lia]. }
    split.
    { intros Hc'. lia. }
    { intros k rgk Hk'. rewrite ERG in Hk'. destruct (Nat.eq_dec k r) as [->|Hne].
      - rewrite R1 in Hk'. injection Hk' as <-. unfold x. cbn [rg_len]. pose proof (A9 _ _ Hrg). lia.
      - rewrite R2 in Hk' by exact Hne. eapply A9. exact Hk'. }
Qed.

Definition am_frame (s s' : astate) : Prop := ltac2:(tb__ "0|1|
S1S0S47S44S7A1A1S21Vs';A1S21Vs;A1A3S1S0S47S52A1S22Vs';A1S22Vs;A1A3S1S4aS6S0S44S6A1M0S53Vs;R2A2S45S6R1A2A3S0SbSdR2A1S26A3S0G0S53Vs';R4A2S45S6R3A2A3F_;F_;Frg;Fk;S1S6bS4cS6S9Vs;A1A2S4cS6S9Vs';A1A2A2S0S52S37Vs';A1S37Vs;A1A3A2A2A2A2").

Lemma am_frame_refl s : am_frame s s.
Proof. repeat split; auto. Qed.

Lemma am_frame_trans s1 s2 s3 : ltac2:(tb__ "0|0|
S60Vs1;Vs2;A2S60Vs2;Vs3;A2S60Vs1;Vs3;A2F_;F_;").
Proof.
  intros (A1&A2&A5&A6&A7) (B1&B2&B5&B6&B7). repeat split; try congruence.
  - intros k rg Hk Hkd. apply B5; [apply A5; assumption | exact Hkd].
  - lia.
Qed.

Lemma region_of_set_brk b s k : ltac2:(tb__ "0|0|
S0S44S6A1S53S1eVb;Vs;A2Vk;A2S53Vs;Vk;A2A3"). Proof. reflexivity. Qed.
Lemma region_of_set_ama p s k : ltac2:(tb__ "0|0|
S0S44S6A1S53S1dVp;Vs;A2Vk;A2S53Vs;Vk;A2A3"). Proof. reflexivity. Qed.
Lemma region_of_set_amac c s k : ltac2:(tb__ "0|0|
S0S44S6A1S53S1cVc;Vs;A2Vk;A2S53Vs;Vk;A2A3"). Proof. reflexivity. Qed.

Lemma open_area_resv_spec X R U s (Q : bool * astate -> Prop) : ltac2:(tb__ "0|1|
S54VX;VR;VU;Vs;A4S62Z0M0S10Vs;A1A2S0S52ScVs;A1G0A3S0S43SeVs;A1S46A3S43S8S54VX;VR;VU;R1A4S60Vs;R2A2S0S47S4dS7S11A2A1SfR3A1SfVs;A1A3S0S43SeR4A1S46A3S0S43R6S46A3S62G0ScR6A1A2F_;VQ;S4fS43S8R7R6A4A1F_;F_;F_;F_;F_;Fs';Fok;S69S4dS43S8A2S29S46Vs;A2VQ;A3F_;F_;F_;F_;F_;").
Proof.
  intros HI Hc Hm0 Hinit HQ.
  pose proof (inv_areas HI) as (E1&E2&E3&E4&E5&E6&E7&E8&E9).
  destruct (E8 Hc) as (r & o & rg & Ep & Hrg & Hk & Hl & Ho & Hlo & Hlen & Hrw).
  pose proof (eq_refl : PGSZ = 4096) as HP.
  unfold open_area. mbinds. apply itok_get. msimp. mbinds. apply itok_ask.
  { cbn. split; [exact Hc|]. split; [reflexivity|]. exists rg. rewrite Ep. cbn.
    repeat (split; [assumption|]). split; [lia|]. intros Hin. pose proof (Hrw o Hin). lia. }
  intros z _. msimp. destruct (z =? 0) eqn:Ez; cbn [negb].
  - apply itok_ret. apply HQ; auto; [apply am_frame_refl | intros; discriminate].
  - mbinds. unfold upd_region. apply itok_modify. msimp. mbinds. apply itok_modify. msimp. apply itok_ret.
    rewrite Ep. cbn [prid poff]. unfold region_of in Hrg. rewrite !(nth_error_nth _ _ _ Hrg).
    match goal with |- Q (true, ?st) =>
      change st with (open_st (SP r o) (set_regions (lupd (st_regions s) r (mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [o]) (rg_live rg))) s)) end.
    apply HQ.
    + apply Inv_open_resv; auto.
    + repeat split; try reflexivity; try tauto.
      * intros k rgk Hk' Hkk. rewrite region_of_open, region_of_upd.
        destruct (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool eqn:E; [|exact Hk'].
        apply andb_prop in E as [E _]. apply Nat.eqb_eq in E. subst k. unfold region_of in Hk'. rewrite Hrg in Hk'. injection Hk' as ->.
        rewrite Hk in Hkk. discriminate.
      * rewrite st_regions_open. cbn. rewrite length_lupd. lia.
    + reflexivity.
    + exact Hinit.
    + intros _. cbn. reflexivity.
Qed.

Lemma resv_then_open_spec X R U s (Q : bool * astate -> Prop) : ltac2:(tb__ "0|1|
S54VX;VR;VU;Vs;A4S0S52ScVs;A1Z0M0A3S0S43SeVs;A1S46A3S43S8S54VX;VR;VU;R1A4S60Vs;R2A2S0S47S4dS7S11A2A1SfR3A1SfVs;A1A3S0S43SeR4A1S46A3S0S43R6S46A3S62G0ScR6A1A2F_;VQ;S4fS43S8R7R6A4A1F_;F_;F_;F_;F_;Fs';Fok;S69S4dS43S8A2S28S43S43S32S43S43S2fS43A1Lrs;R1S29S46A1S33S43S4eA2X43x2Lrs;Vs;A5VQ;A3F_;F_;F_;F_;").
Proof.
  intros HI Hm0 Hinit HQ.
  pose proof (inv_ctx HI) as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12).
  unfold area_from_mmap. mbinds. apply itok_get. msimp.
  destruct (st_avail_meta_area_count s =? 0) eqn:Ec.
  - apply Z.eqb_eq in Ec. mbinds. apply itok_ask.
    { cbn. pose proof (inv_areas HI) as (_&_&_&_&_&A6&_). split; [reflexivity|]. split; [exact Ec|]. split; [exact C10 | exact A6]. }
    intros z _. msimp. destruct (z =? 0) eqn:Ez; cbn [negb].
    + mbinds. apply itok_ret. msimp. apply itok_ret. apply HQ; auto; [apply am_frame_refl | intros; discriminate].
    + unfold new_region. mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp. mbinds. apply itok_ret. msimp.
      mbinds. apply itok_modify. msimp. mbinds. apply itok_ret. msimp.
      match goal with |- itok (open_area true ?st) _ => set (s2 := st) end.
      assert (HI2 : Inv X R U s2) by exact (Inv_new_resv X R U s HI Ec Hinit).
      assert (Fr2 : am_frame s s2).
      { subst s2. repeat split; try reflexivity; try tauto.
        - intros k rg Hk _. cbn [set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas]. apply region_of_app. exact Hk.
        - cbn. rewrite length_app. cbn. lia. }
      assert (Hc2 : 0 < st_avail_meta_area_count s2).
      { subst s2. cbn -[Z.lt Z.sub Z.shiftl]. rewrite Z.shiftl_mul_pow2 by lia.
        pose proof (Z.pow_pos_nonneg 2 (st_meta_alloc_shift s)). lia. }
      eapply open_area_resv_spec; [exact HI2 | exact Hc2 | subst s2; exact Hm0 | subst s2; exact Hinit |].
      intros ok s' HI' Fr' Em' Hi' Hok.
      apply HQ; [exact HI' | eapply am_frame_trans; [exact Fr2 | exact Fr'] | rewrite Em'; subst s2; reflexivity | exact Hi' | exact Hok].
  - apply Z.eqb_neq in Ec. mbinds. apply itok_ret. msimp.
    eapply open_area_resv_spec; [exact HI | lia | exact Hm0 | exact Hinit | exact HQ].
Qed.

Lemma pre_init_facts X R U t : ltac2:(tb__ "0|2|
S54VX;VR;VU;Vt;A4S0S43SeVt;A1S4eA3S1S0S47S4dS7S11A2M0A1SfVt;A1S48G0A1A3S1S0S47S7A1S16Vt;A1S48S7A1A3S1S0S15S14Vt;A1S2eA3S1S0S52S10Vt;A1Z0M1A3S1S0S44S7A1S2cVt;A1S50S7A1A3S0S52ScVt;A1G1A3A2A2A2A2A2F_;F_;").
Proof.
  intros HI Hinit.
  pose proof (inv_ctx HI) as (_&_&_&_&_&_&_&_&_&_&_& CI & _). destruct (CI Hinit) as (M & A & B & AC).
  pose proof (inv_keys HI) as (_ & _ & K3 & _).
  repeat split; try assumption.
  - destruct (st_free_meta_head t) as [q|] eqn:E; [|reflexivity]. exfalso.
    destruct (inv_rings HI) as ((ms & Rg & Hall) & _). rewrite E in Rg. destruct (ring_head_In _ _ _ Rg) as [Hin _].
    destruct (ring_links _ _ _ q Rg Hin) as (pr & nx & Hl).
    destruct (flinks_free _ _ _ _ Hl) as (pr' & nx' & _ & Mq & _). pose proof (MT_Some_In_keys _ _ _ Mq) as K.
    unfold keys in K. rewrite M in K. exact K.
  - exact (K3 A).
Qed.

Lemma new_area_spec X R U t s (Q : bool * astate -> Prop) : ltac2:(tb__ "0|1|
S54VX;VR;VU;Vt;A4S0S8Vs;S2aS46Vt;A2A3S0S52ScVs;A1Z0M0A3S43S8S54VX;VR;VU;R1A4S60Vs;R2A2S0S47S4dS7S11A2A1SfR3A1SfVs;A1A3S0S43SeR4A1S46A3S0S43R6S46A3S62G0ScR6A1A2F_;VQ;S4fS43S8R7R6A4A1F_;F_;F_;F_;F_;Fs';Fok;S69S4dS43S8A2S28S43S43S3aS43S28S43S43S32S43S43S2fS43A1Lrs;R1S29R2A1S33S43S4eA2X43x2Lrs;A4Lnu;Vs;A5VQ;A3F_;F_;F_;F_;").
Proof.
  intros HIt Es Hm0 HQ.
  pose proof (eq_refl : PGSZ = 4096) as HP.
  destruct (st_init_done t) eqn:Hit.
  -
    subst s. rewrite !(set_init_done_same t Hit) in HQ, Hm0 |- *. rename t into s.
    pose proof HIt as HI. pose proof Hit as Hinit.
    pose proof (inv_areas HI) as (A1&A2&A3&A4&A5&A6&A7&A8&A9).
    pose proof (inv_ctx HI) as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12&C13).
    unfold area_from_brk. mbinds. apply itok_get. msimp.
    destruct ((st_avail_meta_area_count s =? 0) && match st_brk s with BrkDead => false | _ => true end) eqn:Econd.
    2:{
        mbinds. apply itok_ret. msimp. eapply resv_then_open_spec; eauto. }
    apply andb_prop in Econd as [Ec Eb]. apply Z.eqb_eq in Ec.
    destruct (st_brk s) as [| |rb pb] eqn:Ebrk; [ | discriminate | ].
    +
      exfalso. exact (C13 Hinit eq_refl).
    +
      destruct A7 as (Hbr & rg & Hrg & Hl & Hlen & Hp2).
      mbinds. apply itok_ask.
      { cbn. right. split; [reflexivity|]. exists rb, pb, rg. rewrite Ebrk.
        destruct (brk_regions_In s rb ltac:(rewrite Hbr; left; reflexivity)) as (rg2 & Hrg2 & Hk2).
        rewrite Hrg in Hrg2. injection Hrg2 as <-. auto 6. }
      intros z2 _. msimp. destruct (z2 =? 0) eqn:Ez2; cbn [negb].
      * mbinds. apply itok_modify. msimp. mbinds. apply itok_ret. msimp.
        assert (HI1 : Inv X R U (set_brk BrkDead s)) by (apply Inv_brk_dead; [exact HI | rewrite Ebrk; discriminate | exact Hinit]).
        eapply resv_then_open_spec; [exact HI1 | exact Hm0 | exact Hinit |].
        intros ok s' HI' Fr' Em' Hi' Hok.
        apply HQ; [exact HI' | | rewrite Em'; reflexivity | exact Hi' | exact Hok].
        eapply am_frame_trans; [| exact Fr']. repeat split; try reflexivity; try tauto; try (intros k rg' Hk _; exact Hk).
      * unfold upd_region. mbinds. apply itok_modify. msimp. mbinds. apply itok_modify. msimp. mbinds. apply itok_ret. msimp.
        unfold region_of in Hrg. rewrite !(nth_error_nth _ _ _ Hrg).
        unfold area_from_mmap. mbinds. apply itok_get. msimp. cbn [Z.eqb st_avail_meta_area_count set_brk set_avail_meta_areas set_avail_meta_area_count set_regions].
        mbinds. apply itok_ret. msimp.
        unfold open_area. mbinds. apply itok_get. msimp. mbinds. apply itok_ret. msimp. cbn [negb].
        mbinds. apply itok_ret. msimp. mbinds. apply itok_modify. msimp. apply itok_ret.
        match goal with |- Q (true, ?st) =>
          change st with (open_st (SP rb (PGSZ * pb))
            (set_brk (BrkCur rb (pb + 1)) (set_avail_meta_areas (SP rb (PGSZ * pb))
              (set_avail_meta_area_count 1 (set_regions (lupd (st_regions s) rb (mkRegion RkBrk (rg_len rg + PGSZ) [] true)) s))))) end.
        apply HQ.
        -- apply (Inv_open_brk_grow X R U s rb pb rg); auto.
        -- repeat split; try reflexivity; try tauto.
           ++ intros k rgk Hk Hkk. rewrite region_of_open, region_of_set_brk, region_of_set_ama, region_of_set_amac.
              rewrite region_of_upd. destruct (Nat.eqb k rb && Nat.ltb rb (length (st_regions s)))%bool eqn:E; [|exact Hk].
              apply andb_prop in E as [E _]. apply Nat.eqb_eq in E. subst k.
              exfalso. destruct (brk_regions_In s rb ltac:(rewrite Hbr; left; reflexivity)) as (rg2 & Hrg2 & Hk2).
              rewrite Hk in Hrg2. injection Hrg2 as ->. rewrite Hk2 in Hkk. discriminate.
           ++ rewrite st_regions_open. cbn. rewrite length_lupd. lia.
        -- reflexivity.
        -- exact Hinit.
        -- intros _. cbn. reflexivity.
  -
    destruct (pre_init_facts X R U t HIt Hit) as (PM & PA & PB & PAC & PFH & PMC).
    pose proof (inv_areas HIt) as (A1&A2&A3&A4&A5&A6&A7&A8&A9).
    subst s. unfold area_from_brk. mbinds. apply itok_get. msimp.
    cbn [st_avail_meta_area_count st_brk set_init_done]. rewrite PAC, PB. cbn [Z.eqb andb].
    pose proof A7 as B7. rewrite PB in B7.
    mbinds. apply itok_ask. { cbn. rewrite ?PB. split; [reflexivity | exact B7]. }
    intros z1 _. msimp. mbinds. apply itok_ask.
    { cbn. left. rewrite ?PB. split; [reflexivity|]. split; [reflexivity | exact B7]. }
    intros z2 _. msimp. destruct (z2 =? 0) eqn:Ez2; cbn [negb].
    +
      mbinds. apply itok_modify. msimp. mbinds. apply itok_ret. msimp.
      assert (HI1 : Inv X R U (set_brk BrkDead (set_init_done true t))) by (apply Inv_init_brk_dead; [exact HIt | rewrite PB; discriminate]).
      eapply resv_then_open_spec; [exact HI1 | exact Hm0 | reflexivity |].
      intros ok s' HI' Fr' Em' Hi' Hok.
      apply HQ; [exact HI' | | rewrite Em'; reflexivity | exact Hi' | exact Hok].
      eapply am_frame_trans; [| exact Fr']. repeat split; try reflexivity; try tauto; try (intros k rg Hk _; exact Hk).
    +
      unfold new_region. mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp. mbinds. apply itok_ret. msimp.
      mbinds. apply itok_modify. msimp. mbinds. apply itok_ask.
      { cbn. eexists (length (st_regions t)), _. split; [reflexivity|]. split; [rewrite length_app; cbn; lia|].
        split; [apply (region_of_app_new (set_init_done true t))|]. cbn. split; [reflexivity|]. split; [reflexivity|].
        rewrite PA. constructor. }
      intros z3 _. msimp. mbinds. apply itok_ret. msimp.

      unfold area_from_mmap. mbinds. apply itok_get. msimp. cbn [Z.eqb st_avail_meta_area_count set_brk set_avail_meta_areas set_avail_meta_area_count set_regions].
      mbinds. apply itok_ret. msimp.
      unfold open_area. mbinds. apply itok_get. msimp. mbinds. apply itok_ret. msimp. cbn [negb].
      mbinds. apply itok_ret. msimp. mbinds. apply itok_modify. msimp. apply itok_ret.
      match goal with |- Q (true, ?st) =>
        change st with (open_st (SP (length (st_regions t)) PGSZ)
          (set_brk (BrkCur (length (st_regions t)) 2) (set_avail_meta_areas (SP (length (st_regions t)) PGSZ)
            (set_avail_meta_area_count 1 (set_regions (st_regions t ++ [mkRegion RkBrk (2 * PGSZ) [] true]) (set_init_done true t)))))) end.
      apply HQ.
      * apply Inv_open_brk_first; auto.
      * repeat split; try reflexivity; try tauto.
        -- intros k rg Hk _. rewrite region_of_open, region_of_set_brk, region_of_set_ama, region_of_set_amac.
           apply (region_of_app (set_init_done true t)). exact Hk.
        -- rewrite st_regions_open. cbn. rewrite length_app. cbn. lia.
      * reflexivity.
      * reflexivity.
      * intros _. cbn. reflexivity.
Qed.

Lemma alloc_meta_spec X R U s (Q : option sptr * astate -> Prop) : ltac2:(tb__ "0|5|
S54VX;VR;VU;Vs;A4S8S54VX;VR;VU;R1A4S60Vs;R2A2S7S27S3S57VX;R5R2R1A4S57VX;Vs;R2R1A4M0A2Fam;Fg;S6cVs;R4A2VQ;S4fS44S7A1M1S8S50S7A1M2R5A4A1F_;F_;F_;F_;Fs';S7S8S54S49S7R2VX;A3VR;VU;R1A4S0S43S5dR3VX;A2S4eA3S67S7R4S5cR3A1A3S5S0S44S11A1M3S5eR4R5A2M4S45S11S30A2A3S0G3G4S45S11S38G2G2A2A2A3A2S60Vs;R5A2S7S27S3S57S49S7R9VX;A3R8R2R1A4G0A2Fam;Fg;S6cVs;R7A2VQ;S4fG1S8S45S7R9A2R8A4A1F_;F_;F_;F_;F_;F_;F_;Fs';Fm;S69S4dG1S8A2S39Vs;A1VQ;A3F_;F_;F_;").
Proof.
  intros HI HQn HQs.
  unfold alloc_meta. mbinds. apply itok_modify. msimp.
  set (s0 := set_init_done true s).
  assert (Fr0 : am_frame s s0) by (repeat split; try reflexivity; intros k rg Hk _; exact Hk).
  assert (Hinit0 : st_init_done s0 = true) by reflexivity.

  assert (TAKE : forall s1, Inv X R U s1 -> am_frame s s1 -> st_metas s1 = st_metas s -> 0 < st_avail_meta_count s1 ->
            itok ((s2 <- get ;;
                   put (set_avail_meta (padd (st_avail_meta s2) META_SIZE) (set_avail_meta_count (st_avail_meta_count s2 - 1) s2)) ;;
                   setslot (st_avail_meta s2) MRaw ;; ret (Some (st_avail_meta s2))) s1) Q).
  { intros s1 HI1 Fr1 Em1 Hc1.
    mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp. mbinds. apply itok_setslot'. msimp. apply itok_ret.
    destruct (take_slot_Inv X R U s1 HI1 Hc1) as (Hfresh & NX & HI2 & EU2).
    apply HQs.
    + exact HI2.
    + exact NX.
    + rewrite keys_upd_notIn by exact Hfresh. apply in_app_iff. right. left. reflexivity.
    + left. apply MT_upd_same.
    + eapply am_frame_trans; [exact Fr1|]. repeat split; try reflexivity. intros k rg Hk _. exact Hk.
    + intros g am. rewrite EU2. unfold usedX, MTX, MT. rewrite Em1. reflexivity.
    + eapply ub_same_trans; [| apply ub_same_upd_notIn; [exact Hfresh | reflexivity]]. apply ub_same_metas. exact Em1. }

  assert (NEW : st_avail_meta_count s0 = 0 ->
            itok ((ok <- (nu <- area_from_brk ;; rs <- area_from_mmap ;; if rs then open_area nu else ret false) ;;
                   if negb ok then ret None
                   else s2 <- get ;;
                        put (set_avail_meta (padd (st_avail_meta s2) META_SIZE) (set_avail_meta_count (st_avail_meta_count s2 - 1) s2)) ;;
                        setslot (st_avail_meta s2) MRaw ;; ret (Some (st_avail_meta s2))) s0) Q).
  { intros Hm0. apply itok_bind.
    eapply (new_area_spec X R U s s0); [exact HI | reflexivity | exact Hm0 |].
    intros ok s1 HI1 Fr1 Em1 Hi1 Hok. msimp. destruct ok; cbn [negb].
    * apply TAKE; [exact HI1 | eapply am_frame_trans; [exact Fr0 | exact Fr1] | rewrite Em1; reflexivity | apply Hok; reflexivity].
    * apply itok_ret. apply HQn; [exact HI1 | eapply am_frame_trans; [exact Fr0 | exact Fr1] | |].
      -- intros g am. unfold usedX, MTX, MT. rewrite Em1. reflexivity.
      -- apply ub_same_metas. rewrite Em1. reflexivity. }
  destruct (st_init_done s) eqn:Hit.
  2:{
      destruct (pre_init_facts X R U s HI Hit) as (PM & PA & PB & PAC & PFH & PMC).
      unfold dequeue_head. mbinds. mbinds. apply itok_get_head'. msimp. cbn [head_of]. unfold s0 at 1. cbn [st_free_meta_head set_init_done]. rewrite PFH.
      mbinds. apply itok_ret. msimp. mbinds. apply itok_get. msimp.
      replace (0 <? st_avail_meta_count s0) with false by (symmetry; apply Z.ltb_ge; unfold s0; cbn; lia).
      apply NEW. unfold s0. cbn. exact PMC. }

  assert (HI0 : Inv X R U s0).
  { apply Inv_set_init_done; [exact HI|]. pose proof (inv_ctx HI) as (_&_&_&_&_&_&_&_&_&_&_&_& C13). exact (C13 Hit). }
  mbinds. eapply dequeue_head_free_spec; [exact HI0 | |].
  -
    intros Hfh Hnofree. msimp. mbinds. apply itok_get. msimp.
    destruct (0 <? st_avail_meta_count s0) eqn:Ec.
    + apply Z.ltb_lt in Ec. mbinds. apply itok_ret. msimp. cbn [negb].
      apply TAKE; [exact HI0 | exact Fr0 | reflexivity | exact Ec].
    + apply Z.ltb_ge in Ec. pose proof (inv_keys HI0) as (_ & _ & _ & _ & Krange).
      assert (Hm0 : st_avail_meta_count s0 = 0) by lia.
      apply NEW. exact Hm0.
  -
    intros m s' HI' NX Mm Sb Ea EU UB. msimp. apply itok_ret. apply HQs.
    + exact HI'.
    + exact NX.
    + eapply MT_Some_In_keys. exact Mm.
    + right. exact Mm.
    + eapply am_frame_trans; [exact Fr0|].
      destruct Sb as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11&E12&E13&E14&E15&E16&E17).
      repeat split; try assumption.
      * intros k rg Hk _. unfold region_of in *. rewrite E15. exact Hk.
      * rewrite E15. lia.
    + intros g am. rewrite EU. reflexivity.
    + eapply ub_same_trans; [apply ub_same_metas; reflexivity | exact UB].
Qed.

(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (4 recorded proofs replaced by written proofs (inv_M_ext, inv_L_ext, group_ok_ext and 1 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_List MI_Ext.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Ext2 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic6eq_indI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext6MR_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext9hosts_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K59OSSVerify5KrLib4Spec6MI_Inv5inv_M01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decI47Corelib7Numbers7BinNums1Z00C45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3dllC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib4Spec6MI_Ext=dll_ext_metasC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC59OSSVerify5KrLib4Spec6MI_Ext>live_group_extC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_L01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes4unit01C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes?RelationClasses=iff_ReflexiveI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6MI_Inv4gendC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv8group_ok01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z3addI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_S01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.

Section EXT2.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).

Lemma inv_M_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> inv_M X st LS -> inv_M X st' LS.
Proof.
  intros HM HG I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [M1 M2 M3 M4 M5]; constructor.
  - intros m Hm. rewrite !ME in *. apply M1. exact Hm.
  - intros m b Hm. rewrite ME in Hm. destruct (M2 m b Hm) as [H|H]; [left; apply HE; exact H| right; exact H].
  - intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & H1 & H2 & H3). exists m. rewrite !ME. auto.
  - intros m Hm. rewrite HM. apply M4. exact Hm.
  - intros z Hz. destruct (M5 z Hz) as (H1 & H2 & H3 & b & H4 & H5). rewrite !ME, HG. repeat split; auto. exists b. auto.
Qed.

Lemma inv_L_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> (forall h, get_head st' h = get_head st h) ->
  inv_L st LS -> inv_L st' LS.
Proof.
  intros HM HG HE I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
  - intros h. rewrite HE. apply L1.
  - intros h. apply (dll_ext_metas st st' HM). apply L2.
  - exact L3.
  - exact L4.
  - intros m. rewrite !ME. apply L5.
  - intros m Hm. rewrite !ME. apply L6. exact Hm.
  - intros sc m Hm. destruct (L7 sc m Hm) as (H1 & H2 & H3). rewrite (live_group_ext st st' HG), ME. auto.
  - exact L9.
Qed.

Lemma group_ok_ext m b ai : s_metas st' = s_metas st -> s_slots st' = s_slots st ->
  (forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> fst b = rid -> s_regions st' !! rid = Some r) ->
  group_ok X st LS m b ai -> group_ok X st' LS m b ai.
Proof.
  intros HM HS HR I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14]; constructor; rewrite ?ME, ?HM, ?HS; try assumption.
  - intros Hml. destruct (G13 Hml) as (H0 & r & Hr & Hk & E1 & E2). split; [exact H0|]. exists r. split; [| auto]. apply HR; auto.
  - intros H. destruct (G14 H) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !ME. auto 10.
Qed.

Lemma inv_S_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> s_slots st' = s_slots st ->
  inv_S X st BL -> inv_S X st' BL.
Proof.
  intros HM HG HS I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [S1 S2 S3 S4 S5 S6]; constructor.
  - intros s m i H. rewrite HS in H. destruct (S1 s m i H) as (? & ? & ?). rewrite (live_group_ext st st' HG), !ME. auto.
  - intros b m i Hb Hi. rewrite HS, ME. apply (S2 b); [apply HE; exact Hb| rewrite <- ME; exact Hi].
  - intros b m ai i Hb Hi. rewrite HG in Hb. rewrite !ME, HG. apply (S3 b m ai i); [exact Hb| rewrite <- ME; exact Hi].
  - intros c Hc. rewrite HS. apply S4. exact Hc.
  - exact S5.
  - intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, ME. auto.
Qed.
End EXT2.

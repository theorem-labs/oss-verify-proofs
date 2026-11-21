(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (17 recorded proofs replaced by written proofs (blk_region, conc_aadd, conc_same and 14 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Geom MI_Ext MI_WFree2 MI_WNtf2 MI_TF2 MI_WSlot MI_WMalloc MI_Sim MI_Contracts.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep MallocTree MallocBlocks.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MallocFacts_inv () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec:MallocCtrl6followC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC35stdpp7tactics<f_equal_helpC45stdpp;list_basics4list;list_filterC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List8map_consC35stdpp4base6FilterI46Stdlib5Lists4List7Forall200C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C45stdpp>list_relations4list9NoDup_nilC35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C35stdpp4base?list_elem_of_InI35stdpp4base5NoDup00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9is_blocksC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6MI_Inv8is_validC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupK59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9ig_regionC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C47Corelib4Init9Datatypes3fstK47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leI47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableK47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init9Datatypes3sndI46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec4KInv:event_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_resvC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK59OSSVerify5KrLib4Spec4KInv9brk_phase02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9set_brkphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_brkregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:set_brkregC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib4Spec4KInv9set_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:set_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib4Spec4KInv9bump_metaC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9MAP_FIXEDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5TWO64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ENOSYSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc<undef_reason00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9cpath_indC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv5cpath00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9answer_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc?MallocFacts_inv?event_post_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc?MallocFacts_inv?event_post_atopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc?MallocFacts_inv:cpath_resvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc?MallocFacts_inv:cpath_atopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc?MallocFacts_inv:ld_staticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec6MI_Inv7ir_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec6Malloc7atop_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02C46Stdlib5Lists4List;Forall2_indI47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00K46Stdlib5Lists4List7Forall201K46Stdlib5Lists4List7Forall202C35stdpp4base6filterC46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decC47Corelib4Init5Logic3notC35stdpp4base6decideI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib4Spec6MI_Inv9bl_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC45stdpp>list_relations4list:NoDup_consC59OSSVerify5KrLib4Spec6MI_Kit=aptr_eqb_specC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes7reflect00C46Stdlib5Lists4List6in_mapC47Corelib4Init5Logic9False_indc59OSSVerify5KrLib6Malloc?MallocFacts_inv9filter_idC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC35stdpp4base7elem_ofC35stdpp9decidable9False_decK47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6MI_Sim6lafterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree4mrunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc?MallocFacts_inv<Forall2_In_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc?MallocFacts_inv?Forall2_impl_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc?MallocFacts_inv>Forall2_filterC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc<MallocBlocks;AREACH_from00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc?MallocFacts_inv4CORRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5minitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv8led_initC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec<MI_Contracts9INVL_initC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc?MallocFacts_inv5corr1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps9fresh_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7cmallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot2GPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv8set_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<MI_Contracts=INVL_set_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc?MallocFacts_inv:blk_regionC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc?MallocFacts_inv9conc_aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc?MallocFacts_inv9conc_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4freeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr05C47Corelib4Init9DatatypesEinjective_projectionsC59OSSVerify5KrLib4Spec6MI_Sim8free_simC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim?free_leaf_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9dec_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib4Spec6MI_Inv8is_nodupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc?MallocFacts_inv@bl_remove_filterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks?AREACH_from_indC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib4Spec6MI_Sim:malloc_simC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5cfreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2x0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pupd_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree>pans_mem_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc?MallocFacts_inv:areach_invC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib4Spec6MI_Sim;INVL_hdr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl6hdr_okC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition corr1 (st : mstate) (b : block) (k : blk) : Prop :=
  blk_slot b = bslot k /\ blk_size b = bsize k /\ blk_addr b = conc st (bslot k) + UNIT * boff k.
Definition CORR (st : mstate) (LB : list block) (BL : list blk) : Prop := Forall2 (corr1 st) LB BL.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma blk_region X st L BL LS k : INVL X st L BL LS -> In k BL ->
  exists r, s_regions st !! fst (bslot k) = Some r /\ r_kind r = RKGroup.
Proof.
  intros INV Hk. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & _).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ i Hb) in Es. rewrite Es. cbn [fst].
  destruct Hb as [ai Hb]. exact (ig_region _ _ _ IG _ _ Hb).
Qed.

Lemma conc_aadd st p d : (exists r, s_regions st !! fst p = Some r) -> conc st (aadd p d) = conc st p + d.
Proof. intros [r Hr]. unfold conc, get_region, aadd. cbn. rewrite Hr. lia. Qed.

Lemma conc_same st st' p : (exists r, s_regions st !! fst p = Some r /\ s_regions st' !! fst p = Some r) -> conc st' p = conc st p.
Proof. intros (r & H1 & H2). unfold conc, get_region. rewrite H1, H2. reflexivity. Qed.

Lemma event_post_resv L e z : ld_resv (event_post L e z) = ld_resv L.
Proof.
  destruct e as [rq|a len prot flags|a len|a len prot|p c h|w]; cbn; try reflexivity.
  - destruct (rq =? 0); [reflexivity|]. destruct (z =? rq); [| reflexivity]. destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[b l]|]; reflexivity.
  - destruct (Z.land flags MAP_FIXED =? 0); [| reflexivity]. destruct (is_err z); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
  - destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); reflexivity.
Qed.
Lemma cpath_resv {R} L (t : M R) L' r : cpath L t L' r -> ld_resv L' = ld_resv L.
Proof. induction 1; [reflexivity|]. rewrite IHcpath. apply event_post_resv. Qed.

(* [comment removed for export] *)
Definition ld_statics (L : mled) : list (Z * Z) * Z := (ld_resv L, ld_atop L).
Lemma event_post_atop L e z : ld_atop (event_post L e z) = ld_atop L.
Proof.
  destruct e as [rq|a len prot flags|a len|a len prot|p c h|w]; cbn; try reflexivity.
  - destruct (rq =? 0); [reflexivity|]. destruct (z =? rq); [| reflexivity]. destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[b l]|]; reflexivity.
  - destruct (Z.land flags MAP_FIXED =? 0); [| reflexivity]. destruct (is_err z); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
  - destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); reflexivity.
Qed.
Lemma cpath_atop {R} L (t : M R) L' r : cpath L t L' r -> ld_atop L' = ld_atop L.
Proof. induction 1; [reflexivity|]. rewrite IHcpath. apply event_post_atop. Qed.
Lemma cpath_statics {R} L (t : M R) L' r : cpath L t L' r -> ld_statics L' = ld_statics L.
Proof. intros H. unfold ld_statics. rewrite (cpath_resv _ _ _ _ H), (cpath_atop _ _ _ _ H). reflexivity. Qed.
Lemma INVL_statics X st L BL LS resv : INVL X st L BL LS -> ld_statics L = (resv, ATOP) ->
  s_reserved st = resv /\ s_atop st = ATOP /\ ld_resv L = resv.
Proof.
  intros INV E. destruct (ir_resv _ _ _ (proj1 INV)) as (R1 & R2 & _). unfold ld_statics in E. injection E as E1 E2.
  rewrite <- R1, <- R2. auto.
Qed.

Lemma Forall2_In_l {A B} (P : A -> B -> Prop) l1 l2 a : Forall2 P l1 l2 -> In a l1 -> exists b, In b l2 /\ P a b.
Proof.
  induction 1 as [|x y l1' l2' Hxy H IH]; intros Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists y; split; [left; reflexivity| exact Hxy]|].
  destruct (IH Hin) as (b & Hb & Pb). exists b. split; [right; exact Hb| exact Pb].
Qed.

Lemma Forall2_impl_in {A B} (P Q : A -> B -> Prop) l1 l2 :
  Forall2 P l1 l2 -> (forall a b, In a l1 -> In b l2 -> P a b -> Q a b) -> Forall2 Q l1 l2.
Proof.
  induction 1 as [|x y l1' l2' Hxy H IH]; intros HPQ; constructor.
  - apply HPQ; [left; reflexivity| left; reflexivity| exact Hxy].
  - apply IH. intros a b Ha Hb. apply HPQ; right; assumption.
Qed.

Lemma Forall2_filter {A B} (P : A -> B -> Prop) (p : A -> bool) (q : B -> bool) l1 l2 :
  Forall2 P l1 l2 -> (forall a b, P a b -> p a = q b) -> Forall2 P (filter p l1) (filter q l2).
Proof.
  induction 1 as [|x y l1' l2' Hxy H IH]; intros E; cbn; [constructor|].
  rewrite (E _ _ Hxy). destruct (q y); [constructor; [exact Hxy| apply IH; exact E]| apply IH; exact E].
Qed.

Lemma Forall2_map_eq {A B C} (P : A -> B -> Prop) (f : A -> C) (g : B -> C) l1 l2 :
  Forall2 P l1 l2 -> (forall a b, P a b -> f a = g b) -> map f l1 = map g l2.
Proof. induction 1; intros E; cbn; [reflexivity|]. rewrite (E _ _ H). f_equal. apply IHForall2. exact E. Qed.

Lemma filter_id {A} (p : A -> bool) l : (forall x, In x l -> p x = true) -> filter p l = l.
Proof.
  induction l as [|x l IH]; intros H; cbn; [reflexivity|].
  rewrite (H x ltac:(left; reflexivity)). f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma bl_remove_filter c BL : NoDup (map bslot BL) ->
  bl_remove c BL = filter (fun k => negb (aptr_eqb (bslot k) c)) BL.
Proof.
  induction BL as [|k BL IH]; intros ND; cbn; [reflexivity|].
  cbn in ND. apply NoDup_cons in ND as [NI ND].
  destruct (aptr_eqb_spec (bslot k) c) as [E|NE]; cbn.
  - symmetry. apply filter_id. intros y Hy. destruct (aptr_eqb_spec (bslot y) c) as [E'|NE']; [| reflexivity].
    exfalso. apply NI. apply list_elem_of_In. rewrite E, <- E'. apply in_map. exact Hy.
  - f_equal. apply IH. exact ND.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem areach_inv resv st LB : AREACH_from resv st LB ->
  exists L LS BL, INVL x0 st L BL LS /\ ld_live L = map bslot BL /\ ld_statics L = (resv, ATOP) /\ s_secret st = 0 /\ CORR st LB BL.
Proof.
  induction 1 as [|st LB n o o' ans st' pf cst c AR IH Hn FF FC|st LB n o o' ans st' AR IH Hn FF|st LB b pf o o' ans st' AR IH Hb Hfst Hconc FF].
  - exists (led_init resv ATOP), (fun _ => []), []. split; [apply INVL_init; [lia| pose proof atop_range; unfold atop_hi; lia]|]. repeat split; try reflexivity. constructor.
  - destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    destruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' (Some pf) INV Hn FF) as (rc0 & FT & CP & LIVE' & [GPR GPS] & RES).
    unfold mrun in FC |- *. rewrite FC in FT. inversion FT. subst cst rc0.
    destruct RES as (off & LS' & Epf & Hoff & INV' & NI).
    set (L' := lafter L (cmalloc (strip st) n) ans) in *.
    exists (set_live (map bslot (((c, off), n) :: BL)) L'), LS', (((c, off), n) :: BL).
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; unfold ld_statics in RESV |- *; cbn; rewrite (cpath_resv _ _ _ _ CP), (cpath_atop _ _ _ _ CP); exact RESV|].
    split; [rewrite GPS; exact SEC|].
    constructor.
    + split; [reflexivity|]. split; [reflexivity|]. cbn [blk_addr bslot boff fst snd]. rewrite Epf. apply conc_aadd.
      destruct (blk_region _ _ _ _ _ ((c, off), n) INV' ltac:(left; reflexivity)) as (r & Hr & _). exists r. exact Hr.
    + eapply Forall2_impl_in; [exact CR|]. intros b k Hb Hk (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|]. rewrite C3.
      rewrite (conc_same st st' (bslot k)); [reflexivity|].
      destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
  - destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    destruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' None INV Hn FF) as (rc0 & FT & CP & LIVE' & [GPR GPS] & RES).
    destruct rc0 as [c|]; [destruct RES|]. destruct RES as (LS' & INV').
    set (L' := lafter L (cmalloc (strip st) n) ans) in *.
    exists (set_live (map bslot BL) L'), LS', BL.
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; unfold ld_statics in RESV |- *; cbn; rewrite (cpath_resv _ _ _ _ CP), (cpath_atop _ _ _ _ CP); exact RESV|].
    split; [rewrite GPS; exact SEC|].
    eapply Forall2_impl_in; [exact CR|]. intros bb k Hb Hk (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|]. rewrite C3.
    rewrite (conc_same st st' (bslot k)); [reflexivity|].
    destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
  - destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
    destruct k as [[c off] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3.
    destruct (blk_region _ _ _ _ _ ((c, off), n) INV Hk) as (r & Hr & Kr). cbn [bslot fst snd] in Hr.
    assert (Epf : pf = aadd c (UNIT * off)).
    { unfold conc, get_region in Hconc, C3. rewrite Hfst, C1 in Hconc. rewrite Hr in Hconc, C3. rewrite C3 in Hconc.
      apply injective_projections; unfold aadd; cbn [fst snd]; [rewrite Hfst, C1; reflexivity| lia]. }
    subst pf.
    destruct (free_sim pans_mem pupd_mem pans_mem_range st L BL LS c off n o ans o' st' INV Hk FF) as (FT & CP & LIVE' & LS' & INV').
    destruct (free_leaf_facts pans_mem pupd_mem st L BL LS c off n o ans o' st' INV Hk FF) as [SUB SEC'].
    set (L' := lafter L (cfree (strip st) (Some c)) ans) in *.
    exists (set_live (map bslot (bl_remove c BL)) L'), LS', (bl_remove c BL).
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; unfold ld_statics in RESV |- *; cbn; rewrite (cpath_resv _ _ _ _ CP), (cpath_atop _ _ _ _ CP); exact RESV|].
    split; [rewrite SEC'; exact SEC|].
    rewrite (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))).
    rewrite C1.
    pose proof (Forall2_filter (corr1 st) (fun b' : block => negb (aptr_eqb (blk_slot b') c)) (fun k0 : blk => negb (aptr_eqb (bslot k0) c)) LB BL CR
                  ltac:(intros b' k' (D1 & _ & _); rewrite D1; reflexivity)) as CRF.
    eapply Forall2_impl_in; [exact CRF|]. intros b' k' Hb' Hk' (D1 & D2 & D3). split; [exact D1|]. split; [exact D2|]. rewrite D3.
    rewrite (conc_same st st' (bslot k')); [reflexivity|].
    rewrite <- (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))) in Hk'.
    destruct (blk_region _ _ _ _ _ k' INV' Hk') as (r' & Hr' & _). exists r'. split; [exact (SUB _ _ Hr')| exact Hr'].
Qed.


(* [comment removed for export] *)
Lemma areach_hdr_ok_proof : forall {resv} st LB (blk : block) (off : Z),
  AREACH_from resv st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  hdr_ok pans_mem pupd_mem st (aadd (blk_slot blk) (UNIT * off)) (blk_slot blk).
Proof.
  intros resv st LB blk off AR Hb Ho Ha.
  destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c bo] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3. rewrite C1 in Ha |- *.
  assert (off = bo) by (unfold UNIT in *; lia). subst off.
  exact (INVL_hdr_ok pans_mem pupd_mem st L BL LS c bo n INV Hk).
Qed.


End CANSEC1.

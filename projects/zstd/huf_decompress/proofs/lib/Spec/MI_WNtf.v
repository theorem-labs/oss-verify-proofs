(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (one5_iff, one5_E_to_B, aor_form and 4 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree MI_WFree2 MI_WKill.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WNtf () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init9Datatypes2IDC35stdpp4gmapBgmap_dep_ne_lookupC59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapI35stdpp4gmap8gmap_key00I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffI47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C47Corelib4Init5Logic3notK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic6or_indC59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7and_indI47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3bitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec9MI_WFree25xpendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_masksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6MI_Inv4g_liC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6MI_Inv4g_aiC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7is_partC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z3eqbK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib4Spec8MI_Arith;testbit_bitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lor_specC56Stdlib6ZArith6BinInt1Z8eqb_reflC46Stdlib4Bool4Bool:orb_true_rC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z:lor_nonnegK47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z:pow_nonnegC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsBsubrelation_properC46Stdlib4Bool4Bool<orb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00I47Corelib4Init9Datatypes4prod00c59OSSVerify5KrLib4Spec7MI_WNtf;one5_E_to_BC1?~~~~~~~~~~~~~~~I35stdpp4gmap8gmap_dep00C35stdpp9countable6encodeC47Corelib4Init9Datatypes2idK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z8lt_totalC59OSSVerify5KrLib4Spec7MI_Geom9sstart_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9stride_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula07c59OSSVerify5KrLib4Spec7MI_WNtf8one5_iffC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool;orb_false_rC59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib4Spec8MI_Pres1@INVL_mask_changeC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC46Stdlib5Lists4List2InK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03C47Corelib7Classes?RelationClasses;reflexivityI47Corelib4Init5Logic2ex00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205C47Corelib7Classes?RelationClasses=iff_ReflexiveK47Corelib7Numbers7BinNums8positive03C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C47Corelib7Classes>Morphisms_PropIiff_iff_iff_impl_morphismC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_WNtf8aor_formC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib4Spec7MI_Geom9hosts_memC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_WNtfAactivate_group_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>activate_groupC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec8MI_ArithAtestbit_mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9land_specC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z:ldiff_specC59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv6extras01C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC56Stdlib6ZArith6BinInt1Z;land_nonnegC56Stdlib6ZArith6BinInt1Z<ldiff_nonnegC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C59OSSVerify5KrLib4Spec6MI_Inv9il_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec6MI_Inv7g_underC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8land_0_lC56Stdlib6ZArith6BinInt1Z9ldiff_0_lI59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>impl_Reflexivec59OSSVerify5KrLib4Spec7MI_WNtf8a_listedC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma one5_iff (A B C D E A' B' C' D' E' : Prop) :
  (A <-> A') -> (B <-> B') -> (C <-> C') -> (D <-> D') -> (E <-> E') -> one5 A B C D E -> one5 A' B' C' D' E'.
Proof. unfold one5. tauto. Qed.
(* [comment removed for export] *)
Lemma one5_E_to_B (A B C D E B' E' : Prop) : E -> B' -> ~ E' -> one5 A B C D E -> one5 A B' C D E'.
Proof. unfold one5. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AOR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g bg : aptr) (ai i : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) ai).
Hypothesis Hi : 0 <= i <= m_last_idx (MR st g).
Hypothesis HP : x_pend X = Some (fst bg, sstart (MR st g) i).
Hypothesis C1 : x_fresh X <> Some g -> forall sc, In g (LS (LActive sc)) -> Some g <> head_of (LS (LActive sc)) -> m_avail (MR st g) = 0.
Hypothesis C2 : x_fresh X <> Some g -> m_sizeclass (MR st g) < 48 -> in_list LS g.
Hypothesis C3 : m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g).
Let st' := upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st.

Lemma aor_form : st' = upd_meta g (fun r => m_set_avail (m_avail (MR st g)) (m_set_freed (Z.lor (m_freed (MR st g)) (bit i)) r)) st.
Proof. unfold st', upd_meta, MR. destruct (get_meta_rec st g); reflexivity. Qed.

Theorem INVL_aor : INVL (xpend X None) st' L BL LS.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (ig_ok _ _ _ IG _ _ _ Hg) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  assert (Hgh : hosts st bg g) by (exists ai; exact Hg).
  pose proof (is_part _ _ _ IS _ _ _ i Hg Hi) as Pi. cbn zeta in Pi. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh) in Pi.
  assert (NA : tbit (m_avail (MR st g)) i = false).
  { destruct (tbit (m_avail (MR st g)) i) eqn:E; [| reflexivity]. exfalso. unfold one5 in Pi. tauto. }
  assert (TB : forall j, 0 <= j -> tbit (Z.lor (m_freed (MR st g)) (bit i)) j = tbit (m_freed (MR st g)) j || (i =? j)).
  { intros j Hj. unfold tbit. rewrite Z.lor_spec, testbit_bit by lia. reflexivity. }
  assert (NZ : Z.lor (m_freed (MR st g)) (bit i) <> 0).
  { intros E. pose proof (TB i ltac:(lia)) as T. rewrite E, Z.eqb_refl, Bool.orb_true_r in T. unfold tbit in T. rewrite Z.bits_0 in T. discriminate. }
  rewrite aor_form.
  apply (INVL_mask_change X st L BL LS g bg ai (m_avail (MR st g)) (Z.lor (m_freed (MR st g)) (bit i)) None INV Hg).
  - split; [exact M1|]. split; [apply Z.lor_nonneg; split; [exact M2| unfold bit; apply Z.pow_nonneg; lia]|]. split; [exact M3|].
    split; [| split].
    + intros j Hj. rewrite TB by exact Hj. rewrite Bool.orb_true_iff. intros [H|H]; [exact (M4 j Hj H)| apply Z.eqb_eq in H; lia].
    + intros j Hj Ha. rewrite TB by exact Hj. rewrite Bool.orb_true_iff. intros [H|H]; [exact (M5 j Hj Ha H)| apply Z.eqb_eq in H; subst j; rewrite NA in Ha; discriminate].
    + intros j Hj. rewrite TB by lia. rewrite (M6 j Hj). reflexivity.
  - intros j Hj. cbn zeta. rewrite TB by lia.
    pose proof (is_part _ _ _ IS _ _ _ j Hg Hj) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh) in P |- *.
    destruct (Z.eqb_spec i j) as [<-|NE].
    + rewrite Bool.orb_true_r. eapply one5_E_to_B; [exact HP| reflexivity| discriminate| exact P].
    + rewrite Bool.orb_false_r. eapply one5_iff; [reflexivity| reflexivity| reflexivity| reflexivity| | exact P].
      rewrite HP. split; [intros E; exfalso| discriminate]. inversion E.
      destruct (Z.lt_total i j) as [LT|[EQ|LT]]; [| lia|].
      * pose proof (sstart_lt _ _ _ IG _ _ i j Hgh LT). pose proof (stride_ge _ _ _ IG _ _ Hgh) as [SG _]. unfold UNIT in *. lia.
      * pose proof (sstart_lt _ _ _ IG _ _ j i Hgh LT). pose proof (stride_ge _ _ _ IG _ _ Hgh) as [SG _]. unfold UNIT in *. lia.
  - right. split.
    + intros s Hs. rewrite HP in Hs. inversion Hs. subst s. exists i. split; [exact Hi|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh). reflexivity.
    + intros s Hs. discriminate.
  - intros NF sc Hin Hnh. split; [exact (C1 NF sc Hin Hnh)| exact NZ].
  - intros NF Hsc NI. exfalso. exact (NI (C2 NF Hsc)).
  - intros _ Hsc Hlt. exfalso. pose proof (C3 Hsc). lia.
Qed.
End AOR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ACT.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (a ba : aptr) (aia : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Ha : s_groups st !! ba = Some (mkGhdr (Some a) aia).
Hypothesis AV0 : m_avail (MR st a) = 0.
Hypothesis HEAD : head_of (LS (LActive (m_sizeclass (MR st a)))) = Some a.
Let act := mask_upto aia.
Let A' := Z.land (m_freed (MR st a)) act.
Let F' := Z.ldiff (m_freed (MR st a)) act.
Let st' := upd_meta a (fun r => m_set_avail A' (m_set_freed F' r)) st.

Lemma act_eq : match m_mem (MR st a) with
               | Some _ => mask_upto (group_active_idx st (default (0%N, -1) (m_mem (MR st a))))
               | None => 0 end = act.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  rewrite (hosts_mem _ _ _ IM _ _ (ex_intro _ aia Ha)). cbn. unfold group_active_idx, get_group. rewrite Ha.
  pose proof (g_ai _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Ha)) as AI. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Ha)) as LI.
  unfold act. f_equal. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 5) with 32. lia.
Qed.

Lemma activate_group_eq {T} (k : mstate -> Z -> M T) bail : activate_group a st k bail = k st' A'.
Proof.
  unfold activate_group. fold (MR st a). rewrite AV0. cbn [guard Z.eqb]. rewrite act_eq. reflexivity.
Qed.

Lemma a_listed : In a (LS (LActive (m_sizeclass (MR st a)))).
Proof. destruct (LS (LActive (m_sizeclass (MR st a)))); cbn in HEAD; [discriminate|]. inversion HEAD. left. reflexivity. Qed.

Theorem INVL_activate : INVL X st' L BL LS.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (ig_ok _ _ _ IG _ _ _ Ha) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  assert (Hah : hosts st ba a) by (exists aia; exact Ha).
  assert (TA : forall j, 0 <= j -> tbit A' j = tbit (m_freed (MR st a)) j && (j <=? aia)).
  { intros j Hj. unfold A', act, tbit. rewrite Z.land_spec, testbit_mask_upto by lia. reflexivity. }
  assert (TF : forall j, 0 <= j -> tbit F' j = tbit (m_freed (MR st a)) j && negb (j <=? aia)).
  { intros j Hj. unfold F', act, tbit. rewrite Z.ldiff_spec, testbit_mask_upto by lia. reflexivity. }
  assert (X_eta : X = mkX (x_idle X) (x_zomb X) (x_pend X) (x_orph X) (x_fresh X)) by (destruct X; reflexivity).
  rewrite X_eta at 1.
  apply (INVL_mask_change X st L BL LS a ba aia A' F' (x_pend X) INV Ha).
  - split; [apply Z.land_nonneg; left; exact M2|]. split; [apply Z.ldiff_nonneg; left; exact M2|].
    split; [| split; [| split]].
    + intros j Hj. rewrite TA by exact Hj. rewrite Bool.andb_true_iff. intros [_ H]. apply Z.leb_le in H. exact H.
    + intros j Hj. rewrite TF by exact Hj. rewrite Bool.andb_true_iff. intros [H _]. exact (M4 j Hj H).
    + intros j Hj. rewrite TA, TF by exact Hj. rewrite !Bool.andb_true_iff. intros [_ H1] [_ H2]. rewrite H1 in H2. discriminate.
    + intros j Hj. rewrite TF by lia. rewrite (M6 j Hj). cbn. destruct (Z.leb_spec j aia); [lia| reflexivity].
  - intros j Hj. cbn zeta. rewrite TA, TF by lia.
    pose proof (is_part _ _ _ IS _ _ _ j Ha Hj) as P. cbn zeta in P.
    assert (NAj : tbit (m_avail (MR st a)) j = false) by (unfold tbit; rewrite AV0; apply Z.bits_0).
    rewrite NAj in P.
    destruct (tbit (m_freed (MR st a)) j); destruct (j <=? aia); cbn [andb negb]; revert P; unfold one5; clear; tauto.
  - left. reflexivity.
  - intros NF sc Hin Hnh. exfalso. destruct (il_active _ _ IL sc a Hin) as (_ & _ & E). subst sc. exact (Hnh (eq_sym HEAD)).
  - intros NF Hsc NI. exfalso. apply NI. exists (LActive (m_sizeclass (MR st a))). exact a_listed.
  - intros NF Hsc Hlt. destruct (g_under _ _ _ _ _ _ GO NF Hsc Hlt) as [_ F0]. unfold A', F'. rewrite F0. split; [apply Z.land_0_l| apply Z.ldiff_0_l].
Qed.
End ACT.

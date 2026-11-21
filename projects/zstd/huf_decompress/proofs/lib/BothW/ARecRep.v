(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (22 recorded proofs replaced by written proofs (firstn_skipn_perm_mid, perm_mid_to_front, length_skipn_Z and 19 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ARep ARepQ ARepFrame ARepKit AHeapP AFreeModel ARepQP AFreeRep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ARecRep () := "I46Stdlib7Sorting;Permutation;Permutation00C47Corelib7Classes?RelationClasses<transitivityC46Stdlib5Lists4List9app_assocC47Corelib5Lists7ListDef5skipnC47Corelib4Init5Logic8eq_ind_rC46Stdlib7Sorting;PermutationGPermutation_EquivalenceC46Stdlib7Sorting;PermutationDPermutation_app_headC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List<firstn_skipnC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List7existsbI47Corelib4Init9Datatypes4list00C47Corelib5Lists7ListDef6firstnK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib7Classes?RelationClassesFEquivalence_TransitiveC46Stdlib7Sorting;PermutationHPermutation_app_swap_appC46Stdlib7Sorting;PermutationBPermutation_middleI47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib5BothW7ARecRepEfirstn_skipn_perm_midC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List:firstn_nilC46Stdlib5Lists4List8nil_consC46Stdlib7Sorting;Permutation>Permutation_inC46Stdlib5Lists4List<length_skipnc59OSSVerify5KrLib5BothW7ARecRepAperm_mid_to_frontC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib5Lists4List=length_firstnc59OSSVerify5KrLib5BothW7ARecRep>length_skipn_ZC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minc59OSSVerify5KrLib5BothW7ARecRep?length_firstn_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z8mul_commC59OSSVerify5KrLib4Spec8AsanCtrl:max_cachedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00C59OSSVerify5KrLib5BothW8AFreeRep9any_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeRep9any_rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z3eqbK59OSSVerify5KrLib5BothW4ARep6xclass01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep5aconc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffI59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARecRep6rfree'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARecRep7rcache'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARecRep4xrecC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_appC46Stdlib5Lists4List6filterC59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:filter_appC59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4findI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5BothW8AFreeRep4banyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC46Stdlib5Lists4List9find_someC59OSSVerify5KrLib5BothW8AFreeRep;key_fresh_gC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib5BothW9ARepFrame=busy_of_x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeRep;busy_of_X_gC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z8eqb_reflc59OSSVerify5KrLib5BothW7ARecRep<busy_of_xrecC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupK59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltc59OSSVerify5KrLib5BothW7ARecRep@max_cached_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARecRep4rcutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARecRep4rcntC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARecRep5rhalfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARecRep9rec_classC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC47Corelib4Init3Nat3addK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc59OSSVerify5KrLib5BothW7ARecRep5rcnt'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARecRep7rcut_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARecRep4rnf'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeRepBbusy_slots_split_gC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARecRep?busy_slots_xrecC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation?Permutation_symC59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat3N2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK59OSSVerify5KrLib4Spec8AsanCtrl6aclass01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeRepBPermutation_NoDup'C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib5BothW7ARecRep7In_xrecC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_app_iffK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARecRep=length_rfree'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARecRep>length_rcache'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARecRep8rec_permC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ARecRep:xrec_keepsC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma firstn_skipn_perm_mid : forall {A} (f c : list A) (i : nat) (x : A) (b1 b2 : list A),
  Permutation ((f ++ skipn i c) ++ (firstn i c ++ [x]) ++ (b1 ++ b2)) (f ++ c ++ (b1 ++ [x] ++ b2)).
Proof.
  intros A f c i x b1 b2. rewrite <- !app_assoc. apply Permutation_app_head.
  transitivity (firstn i c ++ skipn i c ++ [x] ++ b1 ++ b2); [apply Permutation_app_swap_app|].
  rewrite (app_assoc (firstn i c) (skipn i c)), firstn_skipn. apply Permutation_app_head. cbn [app]. apply Permutation_middle.
Qed.

Lemma perm_mid_to_front : forall {A} (f c : list A) (x : A) (b1 b2 : list A),
  Permutation (f ++ (c ++ [x]) ++ (b1 ++ b2)) (f ++ c ++ (b1 ++ [x] ++ b2)).
Proof.
  intros A f c x b1 b2. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. cbn [app]. apply Permutation_middle.
Qed.

Lemma length_skipn_Z : forall {A} (l : list A) i, (i <= length l)%nat -> Z.of_nat (length (skipn i l)) = Z.of_nat (length l) - Z.of_nat i.
Proof. intros A l i Hi. rewrite length_skipn. lia. Qed.
Lemma length_firstn_Z : forall {A} (l : list A) i, (i <= length l)%nat -> Z.of_nat (length (firstn i l)) = Z.of_nat i.
Proof. intros A l i Hi. rewrite length_firstn. lia. Qed.

Lemma max_cached_range : forall c, 2 <= max_cached c <= 16 /\ 1 <= max_cached c / 2 <= 8 /\ max_cached c = 2 * (max_cached c / 2).
Proof.
  intros c. unfold max_cached.
  set (q := Z.max 1 (Z.min 8 (1024 / size_of_class c))). assert (1 <= q <= 8) by lia.
  rewrite (Z.mul_comm 2 q), Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Recyc.
Variables (L : alayout) (st : astate) (X : aconc) (s0 : bstate) (c k n b1 ctx : Z) (l1 l2 : list xbusy).
Variable drained : bool.
Hypothesis XB : x_busy X = l1 ++ bany s0 c k n b1 ctx :: l2.
Hypothesis WF : awf L st X.
Hypothesis NL : forall p, s0 <> BLive p.

Definition rcnt : Z := c_count (get_cls st c).
Definition rhalf : Z := max_cached c / 2.
Definition rcut : nat := Z.to_nat (rcnt - rhalf).
(* [comment removed for export] *)
Definition rcache' : list Z :=
  if drained then firstn rcut (xc_cache (x_cls X c)) ++ [k] else xc_cache (x_cls X c) ++ [k].
Definition rfree' : list Z :=
  if drained then xc_free (x_cls X c) ++ skipn rcut (xc_cache (x_cls X c)) else xc_free (x_cls X c).
Definition xrec : aconc :=
  mkAConc (fun c' => if c' =? c then mkXClass rfree' rcache' else x_cls X c') (l1 ++ l2).

Lemma rec_class : 1 <= c < K_NUM_CLASSES.
Proof. exact (any_class L st X s0 c k n b1 ctx l1 l2 XB WF). Qed.

Lemma rec_range : 1 <= c < K_NUM_CLASSES /\ 0 <= k < ndist st c.
Proof. exact (any_range L st X s0 c k n b1 ctx l1 l2 XB WF). Qed.

Lemma In_xrec : forall y, In y (x_busy xrec) <-> In y (l1 ++ l2).
Proof. intros y. unfold xrec. cbn [x_busy]. tauto. Qed.

Lemma busy_slots_xrec : forall c',
  busy_slots xrec c' = busy_slots (mkAConc (x_cls X) l1) c' ++ busy_slots (mkAConc (x_cls X) l2) c'.
Proof. intros c'. unfold busy_slots, xrec. cbn [x_busy]. rewrite List.filter_app, map_app. reflexivity. Qed.

Lemma busy_of_xrec : forall c' k',
  busy_of xrec c' k' = if (c =? c') && (k =? k') then None else busy_of X c' k'.
Proof.
  intros c' k'. rewrite (busy_of_X_g L st X s0 c k n b1 ctx l1 l2 XB WF).
  unfold xrec. rewrite (busy_of_x_cls _ (x_cls X) (l1 ++ l2)).
  destruct ((c =? c') && (k =? k')) eqn:E; [| reflexivity].
  apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst c' k'.
  unfold busy_of. cbn [x_busy]. destruct (List.find _ (l1 ++ l2)) as [y|] eqn:F; [| reflexivity]. exfalso.
  apply List.find_some in F. destruct F as [Hy T]. apply andb_true_iff in T. destruct T as [T1 T2].
  apply Z.eqb_eq in T1. apply Z.eqb_eq in T2. exact (key_fresh_g L st X s0 c k n b1 ctx l1 l2 XB WF y Hy T1 T2).
Qed.

Lemma busy_of_xrec_self : busy_of xrec c k = None.
Proof. rewrite busy_of_xrec, !Z.eqb_refl. reflexivity. Qed.
Lemma busy_of_xrec_other : forall c' k', (c <> c' \/ k <> k') -> busy_of xrec c' k' = busy_of X c' k'.
Proof.
  intros c' k' H. rewrite busy_of_xrec. destruct (Z.eqb_spec c c'); destruct (Z.eqb_spec k k'); cbn [andb]; try reflexivity. lia.
Qed.

(* [comment removed for export] *)
Definition rnf' : Z := c_num_freed (get_cls st c) + (if drained then rhalf else 0).
Definition rcnt' : Z := if drained then rcnt - rhalf + 1 else rcnt + 1.

Hypothesis DRC : if drained then rcnt = max_cached c else rcnt < max_cached c.

Lemma rcut_le : drained = true -> (rcut <= length (xc_cache (x_cls X c)))%nat /\ Z.of_nat rcut = rcnt - rhalf.
Proof.
  intros D. pose proof WF as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC c rec_class) as (_ & _ & _ & _ & _ & _ & _ & _ & LENC & CNT & _).
  pose proof (max_cached_range c) as MC. rewrite D in DRC. unfold rcut, rcnt, rhalf in *. split; lia.
Qed.

Lemma length_rcache' : Z.of_nat (length rcache') = rcnt'.
Proof.
  pose proof WF as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC c rec_class) as (_ & _ & _ & _ & _ & _ & _ & _ & LENC & CNT & _).
  pose proof rcut_le as RL. unfold rcache', rcnt'. destruct drained.
  - destruct (RL eq_refl) as [LE EQ]. rewrite length_app, length_firstn. cbn [length]. unfold rcnt in *. lia.
  - rewrite length_app. cbn [length]. unfold rcnt. lia.
Qed.

Lemma length_rfree' : Z.of_nat (length rfree') = rnf'.
Proof.
  pose proof WF as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC c rec_class) as (_ & _ & _ & _ & _ & _ & _ & LENF & LENC & CNT & _).
  pose proof rcut_le as RL. unfold rfree', rnf'. destruct drained.
  - destruct (RL eq_refl) as [LE EQ]. rewrite length_app, length_skipn. unfold rcnt in *. lia.
  - lia.
Qed.

(* [comment removed for export] *)
Lemma rec_perm : Permutation (rfree' ++ rcache' ++ busy_slots xrec c)
                             (xc_free (x_cls X c) ++ xc_cache (x_cls X c) ++ busy_slots X c).
Proof.
  rewrite busy_slots_xrec, (busy_slots_split_g X s0 c k n b1 ctx l1 l2 XB), Z.eqb_refl.
  unfold rfree', rcache'. destruct drained.
  - apply firstn_skipn_perm_mid.
  - apply perm_mid_to_front.
Qed.

(* [comment removed for export] *)
Lemma awf_xrec : forall s mfa',
  a_space_beg s = a_space_beg st -> a_ptr_array s = a_ptr_array st -> a_cinit s = true ->
  a_live s = a_live st -> a_next s = a_next st ->
  (forall c', c' <> c -> get_cls s c' = get_cls st c') ->
  get_cls s c = mkAClass (c_mapped_user (get_cls st c)) (c_allocated_user (get_cls st c)) rnf' mfa' rcnt' ->
  4 * rnf' <= mfa' <= K_FREEARR_MAX -> mfa' mod K_FREEARR_MAP = 0 ->
  awf L s xrec.
Proof.
  intros s mfa' E1 E2 E3 E5 E6 GC GCC MFA MFAM.
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  pose proof (max_cached_range c) as MCR.
  assert (MC : forall c', max_count s c' = max_cached c') by (intros c'; unfold max_count; rewrite E3; reflexivity).
  assert (MCle : forall c', max_count st c' <= max_cached c').
  { intros c'. unfold max_count. pose proof (max_cached_range c'). destruct (a_cinit st); lia. }
  assert (NDc : ndist s c = ndist st c) by (unfold ndist; rewrite GCC; reflexivity).
  assert (NDo : forall c', c' <> c -> ndist s c' = ndist st c') by (intros c' NE; unfold ndist; rewrite (GC c' NE); reflexivity).
  unfold awf. rewrite E1, E2, E5, E6.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split.
  { intros c' HC'. rewrite MC. unfold xrec. cbn [x_cls].
    destruct (Z.eqb_spec c' c) as [->|NE].
    - rewrite GCC, NDc. cbn [xc_free xc_cache c_allocated_user c_mapped_user c_num_freed c_mapped_free_array c_count].
      destruct (PERC c rec_class) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
      split; [unfold rnf', rhalf; destruct drained; lia|]. split; [exact MFA|]. split; [exact MFAM|].
      split; [exact length_rfree'|]. split; [exact length_rcache'|].
      split; [unfold rcnt', rcnt, rhalf in *; destruct drained; lia|].
      split.
      + eapply Permutation_NoDup'; [apply Permutation_sym; exact rec_perm| exact ND].
      + intros k0 Hk. apply RANGE. eapply Permutation_in; [exact rec_perm| exact Hk].
    - rewrite (GC c' NE), (NDo c' NE), busy_slots_xrec.
      destruct (PERC c' HC') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
      rewrite (busy_slots_split_g X s0 c k n b1 ctx l1 l2 XB) in ND, RANGE.
      destruct (Z.eqb_spec c c') as [E|_]; [congruence|]. cbn [app] in ND, RANGE.
      repeat (split; [assumption|]). split; [pose proof (MCle c'); lia|]. split; [exact ND| exact RANGE]. }
  split.
  { intros c' HC'. rewrite GC; [exact (OUTC c' HC')|]. intros ->. exact (HC' rec_class). }
  split.
  { intros y Hy. apply In_xrec in Hy. exact (BUSY y ltac:(rewrite XB; apply in_app_iff; apply in_app_iff in Hy; destruct Hy as [Hy|Hy]; [left; exact Hy| right; right; exact Hy])). }
  split.
  { intros p' c' n' H. destruct (LIVE p' c' n' H) as (y & Hy & Sy & R). exists y. split; [| split; [exact Sy| exact R]].
    apply In_xrec. rewrite XB in Hy. apply in_app_iff in Hy. apply in_app_iff. destruct Hy as [Hy|[E|Hy]]; [left; exact Hy| | right; exact Hy].
    exfalso. subst y. cbn in Sy. exact (NL p' Sy). }
  split; [exact FRESH|].
  intros y1 y2 H1 H2 EQ EX. apply In_xrec in H1. apply In_xrec in H2.
  apply UNIQ; [| | exact EQ| exact EX]; rewrite XB; apply in_app_iff; [apply in_app_iff in H1; destruct H1 as [H1|H1]| apply in_app_iff in H2; destruct H2 as [H2|H2]];
    [left; exact H1| right; right; exact H1| left; exact H2| right; right; exact H2].
Qed.

(* [comment removed for export] *)
Lemma xrec_keeps : forall y, In y (x_busy X) -> y <> bany s0 c k n b1 ctx -> In y (x_busy xrec).
Proof.
  intros y Hy NE. apply In_xrec. rewrite XB in Hy. apply in_app_iff in Hy. apply in_app_iff.
  destruct Hy as [Hy|[E|Hy]]; [left; exact Hy| congruence| right; exact Hy].
Qed.
Lemma xrec_sub : forall y, In y (x_busy xrec) -> In y (x_busy X).
Proof.
  intros y Hy. apply In_xrec in Hy. rewrite XB. apply in_app_iff in Hy. apply in_app_iff.
  destruct Hy as [Hy|Hy]; [left; exact Hy| right; right; exact Hy].
Qed.
Lemma xrec_live : forall y p, In y (x_busy X) -> xb_st y = BLive p -> In y (x_busy xrec).
Proof. intros y p Hy Sy. apply xrec_keeps; [exact Hy|]. intros ->. cbn in Sy. exact (NL p Sy). Qed.

Lemma xrec_cls_other : forall c', c' <> c -> x_cls xrec c' = x_cls X c'.
Proof. intros c' NE. unfold xrec. cbn [x_cls]. destruct (Z.eqb_spec c' c); [congruence| reflexivity]. Qed.
Lemma xrec_cls_self : x_cls xrec c = mkXClass rfree' rcache'.
Proof. unfold xrec. cbn [x_cls]. rewrite Z.eqb_refl. reflexivity. Qed.
End Recyc.
End CANSEC1.

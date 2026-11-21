(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (8 recorded proofs replaced by written proofs (In_classes, forallb_classes, tab_basic_ok and 5 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Malloc.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LB_Tables () := "C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismK47Corelib4Init9Datatypes3nat02C47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic3iffK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC46Stdlib5Lists4List:in_map_iffC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC46Stdlib5Lists4List6in_seqC56Stdlib6ZArith6BinInt1Z3maxI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init5Logic6eq_indC46Stdlib9micromega;ZifyClasses5mkappK47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqI46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C47Corelib7Classes?RelationClasses?iff_equivalenceK47Corelib7Numbers7BinNums8positive03C47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes?RelationClasses=iff_ReflexiveK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib4Spec9LB_Tables7classesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>forallb_forallc59OSSVerify5KrLib4Spec9LB_Tables:In_classesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbc59OSSVerify5KrLib4Spec9LB_Tables?forallb_classesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_Tables9tab_basicC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_Tables2S_C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebc59OSSVerify5KrLib4Spec9LB_Tables4cmaxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_Tables8std_spanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_Tables7std_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_Tables8tab_hostC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib4Spec9LB_Tables:std_nestedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9LB_Tables7bighostC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4negbC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init9Datatypes3orbK47Corelib4Init5Logic2or01C47Corelib4Init5Logic3notK47Corelib4Init5Logic2or02C47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z6leb_gtC46Stdlib4Bool4Bool8eqb_propC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib4Init5Logic7and_indC46Stdlib4Bool4Bool<orb_true_iffC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib4Init5Logic6or_indC46Stdlib4Bool4Bool=andb_true_iffC46Stdlib4Bool4Bool3eqbC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes?RelationClasses=iff_SymmetricC47Corelib7Classes?RelationClasses>iff_Transitivec59OSSVerify5KrLib4Spec9LB_Tables<tab_basic_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:fold_right".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition S_ (c : Z) : Z := UNIT * size_class c.
Definition cmax (c : Z) : Z :=
  if c <? 9 then small_cnt c 0 else halve_big 8 (med_cnt (Z.land c 3)) (S_ c).
Definition std_span (c : Z) : Z := cmax c * S_ c + UNIT.
Definition std_nested (c : Z) : bool := std_span c <=? PGSZ / 2.
Definition bighost (c : Z) : Z := if std_nested c then size_to_class (std_span c - IB) else -1.
Definition std_len (c : Z) : Z := round_up_pg (std_span c).

Definition classes : list Z := map Z.of_nat (seq 0 48).

Lemma In_classes c : 0 <= c < 48 <-> In c classes.
Proof.
  unfold classes. rewrite in_map_iff. split.
  - intros H. exists (Z.to_nat c). rewrite in_seq. split; lia.
  - intros (n & <- & Hn). rewrite in_seq in Hn. lia.
Qed.

Lemma forallb_classes (f : Z -> bool) : forallb f classes = true -> forall c, 0 <= c < 48 -> f c = true.
Proof. intros H c Hc. rewrite forallb_forall in H. apply H. apply In_classes. exact Hc. Qed.

Ltac by_table f :=
  let H := fresh in
  assert (H : forallb f classes = true) by (vm_compute; reflexivity);
  intros c Hc; pose proof (forallb_classes f H c Hc) as T; unfold f in T; cbn beta in T;
  repeat (apply andb_prop in T as [T ?]);
  repeat match goal with K : (_ =? _) = true |- _ => apply Z.eqb_eq in K | K : (_ <=? _) = true |- _ => apply Z.leb_le in K | K : (_ <? _) = true |- _ => apply Z.ltb_lt in K end.

(* [comment removed for export] *)
Definition tab_basic (c : Z) : bool :=
  (16 <=? S_ c) && (S_ c <=? 131056) && (8 <=? cmax c) && (cmax c <=? 32) && (std_span c <=? std_len c) && (std_len c <=? std_span c + 4095)
  && (std_len c <=? 1048576) && (Z.modulo (std_len c) PGSZ =? 0).
Lemma tab_basic_ok : forall c, 0 <= c < 48 ->
  16 <= S_ c <= 131056 /\ 8 <= cmax c <= 32 /\ std_span c <= std_len c <= std_span c + 4095 /\ std_len c <= 1048576 /\ std_len c mod PGSZ = 0.
Proof. by_table tab_basic. repeat split; assumption. Qed.

(* [comment removed for export] *)
Definition tab_host (c : Z) : bool :=
  if c <=? 6 then (std_nested c) && ((bighost c =? 15) || (bighost c =? 19) || (bighost c =? 23)) && (std_span c <=? S_ (bighost c)) && (c <? bighost c)
  else negb (std_nested c) && (bighost c =? -1).
Lemma tab_host_small : forall c, 0 <= c <= 6 ->
  std_nested c = true /\ (bighost c = 15 \/ bighost c = 19 \/ bighost c = 23) /\ std_span c <= S_ (bighost c) /\ c < bighost c.
Proof.
  intros c Hc. assert (H : forallb tab_host classes = true) by (vm_compute; reflexivity).
  pose proof (forallb_classes tab_host H c ltac:(lia)) as T. unfold tab_host in T.
  replace (c <=? 6) with true in T by (symmetry; apply Z.leb_le; lia).
  apply andb_prop in T as [T T4]. apply andb_prop in T as [T T3]. apply andb_prop in T as [T1 T2].
  apply Z.leb_le in T3. apply Z.ltb_lt in T4.
  split; [exact T1|]. split; [| auto].
  destruct (Z.eqb_spec (bighost c) 15); [auto|]. destruct (Z.eqb_spec (bighost c) 19); [auto|]. destruct (Z.eqb_spec (bighost c) 23); [auto|]. cbn in T2. discriminate.
Qed.
Lemma tab_host_big : forall c, 7 <= c < 48 -> std_nested c = false /\ bighost c = -1.
Proof.
  intros c Hc. assert (H : forallb tab_host classes = true) by (vm_compute; reflexivity).
  pose proof (forallb_classes tab_host H c ltac:(lia)) as T. unfold tab_host in T.
  replace (c <=? 6) with false in T by (symmetry; apply Z.leb_gt; lia).
  apply andb_prop in T as [T1 T2]. apply Z.eqb_eq in T2. destruct (std_nested c); [discriminate| auto].
Qed.

(* [comment removed for export] *)
Lemma bighost_inv : forall c, 0 <= c < 48 ->
  (bighost c = 15 <-> c = 0) /\ (bighost c = 19 <-> c = 1 \/ c = 2) /\ (bighost c = 23 <-> 3 <= c <= 6).
Proof.
  intros c Hc.
  assert (H : forallb (fun c => Bool.eqb (bighost c =? 15) (c =? 0) && Bool.eqb (bighost c =? 19) ((c =? 1) || (c =? 2)) && Bool.eqb (bighost c =? 23) ((3 <=? c) && (c <=? 6))) classes = true) by (vm_compute; reflexivity).
  pose proof (forallb_classes _ H c Hc) as T. cbn beta in T.
  apply andb_prop in T as [T T3]. apply andb_prop in T as [T1 T2].
  apply Bool.eqb_prop in T1. apply Bool.eqb_prop in T2. apply Bool.eqb_prop in T3.
  split; [| split].
  - rewrite <- Z.eqb_eq, T1, Z.eqb_eq. tauto.
  - rewrite <- Z.eqb_eq, T2, Bool.orb_true_iff, !Z.eqb_eq. tauto.
  - rewrite <- Z.eqb_eq, T3, Bool.andb_true_iff, Z.leb_le, Z.leb_le. tauto.
Qed.

(* [comment removed for export] *)
Lemma size_class_pos : forall c, 0 <= c < 48 -> 0 < size_class c.
Proof. intros c Hc. pose proof (tab_basic_ok c Hc). unfold S_, UNIT in *. lia. Qed.

(* [comment removed for export] *)
Lemma sum_S : fold_right Z.add 0 (map S_ classes) = 795632.
Proof. vm_compute. reflexivity. Qed.

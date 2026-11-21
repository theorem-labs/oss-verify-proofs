(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (16 recorded proofs replaced by written proofs (forallb_range_spec, range_by_compute, range_bv_eq and 13 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List.
From stdpp Require Import bitvector.definitions.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import AModelFacts.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_APrimFacts () := "C47Corelib7Classes?RelationClasses9Reflexivec59OSSVerify5KrLib5BothW:APrimFacts=forallb_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums1Z02C45stdpp7numbers1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib5BothW:APrimFactsBforallb_range_specC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes3orbC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec8AsanCtrl6rz_logC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:APrimFacts<rz_log_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07K47Corelib7Numbers7BinNums1N02C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AModelFacts:rz_size_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05K47Corelib7Numbers7BinNums1N01c59OSSVerify5KrLib5BothW:APrimFacts=rz_size_casesC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z<eq_decidableK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AModelFacts?rounded_size_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:APrimFacts=rz_size_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;needed_sizeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:APrimFacts=rounded_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7needed0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6shiftlC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6NArith6BinNat1N3subC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr06C45stdpp9bitvector;definitions?bv_half_modulusC45stdpp9bitvector;definitions>bv_swrap_smallC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z9mod_smallI47Corelib7Numbers7BinNums1N00c59OSSVerify5KrLib5BothW:APrimFacts;sllw_rz_genC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:APrimFacts8class_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8class_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:APrimFacts@range_by_computeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes5implbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes9andb_propC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib4Bool4Bool>implb_true_iffK46Stdlib9micromega5Tauto8GFormula01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6shiftrC47Corelib4Init9Datatypes4andbK46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega5Tauto4kind02c59OSSVerify5KrLib5BothW:APrimFacts<class_ok_allC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:APrimFacts6cls_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:max_cachedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:APrimFacts:cls_ok_allC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:APrimFacts:prim_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:APrimFacts;class_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:APrimFacts9cls_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C59OSSVerify5KrLib5BothW;AModelFactsCsize_of_class_smallC1?~~~~~~~~~~~~~~~".
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Fixpoint forallb_range (f : Z -> bool) (lo : Z) (n : nat) : bool :=
  match n with O => true | S k => if f lo then forallb_range f (lo + 1) k else false end.

Lemma forallb_range_spec : forall f n lo, forallb_range f lo n = true -> forall z, lo <= z < lo + Z.of_nat n -> f z = true.
Proof.
  intros f n. induction n as [|k IH]; intros lo H z Hz; [lia|].
  cbn [forallb_range] in H. destruct (f lo) eqn:E; [| discriminate].
  destruct (Z.eq_dec z lo) as [->|NE]; [exact E|]. apply (IH (lo + 1) H). lia.
Qed.

(* [comment removed for export] *)
Lemma range_by_compute : forall (P : Z -> Prop) (f : Z -> bool) lo hi,
  (forall z, f z = true -> P z) -> forallb_range f lo (Z.to_nat (hi - lo + 1)) = true ->
  forall z, lo <= z <= hi -> P z.
Proof.
  intros P f lo hi Hf Hb z Hz. apply Hf. apply (forallb_range_spec f _ lo Hb). lia.
Qed.

(* [comment removed for export] *)
Lemma range_bv_eq : forall (e c : Z -> Z) lo hi,
  forallb_range (fun z => Z.eqb (e z mod 2^64) (c z mod 2^64)) lo (Z.to_nat (hi - lo + 1)) = true ->
  forall z, lo <= z <= hi -> Z_to_bv 64 (e z) = Z_to_bv 64 (c z).
Proof.
  intros e c lo hi Hb z Hz. pose proof (forallb_range_spec _ _ _ Hb z ltac:(lia)) as E. cbn beta in E.
  apply Z.eqb_eq in E. apply Z_to_bv_eqm. exact E.
Qed.

(* [comment removed for export] *)
Lemma range_bv_eq8 : forall (e c : Z -> Z) lo hi,
  forallb_range (fun z => negb (z mod 8 =? 0) || Z.eqb (e z mod 2^64) (c z mod 2^64)) lo (Z.to_nat (hi - lo + 1)) = true ->
  forall z, lo <= z <= hi -> z mod 8 = 0 -> Z_to_bv 64 (e z) = Z_to_bv 64 (c z).
Proof.
  intros e c lo hi Hb z Hz M8. pose proof (forallb_range_spec _ _ _ Hb z ltac:(lia)) as E. cbn beta in E.
  replace (z mod 8 =? 0) with true in E by (symmetry; apply Z.eqb_eq; exact M8). cbn in E.
  apply Z.eqb_eq in E. apply Z_to_bv_eqm. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.

Lemma rz_size_cases : forall n,
  rz_size n = 16 \/ rz_size n = 32 \/ rz_size n = 64 \/ rz_size n = 128 \/ rz_size n = 256 \/ rz_size n = 512 \/ rz_size n = 1024 \/ rz_size n = 2048.
Proof.
  intros n. rewrite rz_size_eq. pose proof (rz_log_range n) as R.
  assert (E : rz_log n = 0 \/ rz_log n = 1 \/ rz_log n = 2 \/ rz_log n = 3 \/ rz_log n = 4 \/ rz_log n = 5 \/ rz_log n = 6 \/ rz_log n = 7) by lia.
  destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; cbn; lia.
Qed.

Lemma rz_size_range : forall n, 16 <= rz_size n <= 2048 /\ rz_size n mod 16 = 0.
Proof. intros n. destruct (rz_size_cases n) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; (split; [lia| reflexivity]). Qed.

Lemma rounded_facts : forall n, Z.max n 8 <= rounded_size n <= Z.max n 8 + 7 /\ rounded_size n mod 8 = 0.
Proof. intros n. rewrite rounded_size_eq. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
Lemma prim_facts : forall n, 1 <= n -> is_primary n = true ->
  needed_size n = rounded_size n + rz_size n
  /\ 16 <= rz_size n <= 2048 /\ rz_size n = 16 * 2 ^ rz_log n /\ rz_size n mod 16 = 0 /\ 0 <= rz_log n <= 7
  /\ Z.max n 8 <= rounded_size n <= Z.max n 8 + 7 /\ rounded_size n mod 8 = 0
  /\ 24 <= needed_size n <= 65536.
Proof.
  intros n N PRIM. pose proof (rz_size_range n) as [R1 R2]. pose proof (rounded_facts n) as [Q1 Q2]. pose proof (rz_log_range n) as RL.
  unfold needed_size. rewrite PRIM. unfold is_primary, needed0, K_MAX_SIZE in PRIM. apply Z.leb_le in PRIM.
  unfold needed0. repeat split; try lia. apply rz_size_eq.
Qed.

(* [comment removed for export] *)
Lemma sllw_rz_gen : forall n, bv_swrap 32 (Z.shiftl 16 ((rz_log n mod 18446744073709551616) mod 32)) = rz_size n.
Proof.
  intros n. pose proof (rz_log_range n) as RLR. pose proof (rz_size_eq n) as RZE. pose proof (rz_size_range n) as [RR _].
  rewrite !(Z.mod_small (rz_log n)) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite RZE.
  apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N (32 - 1)) with 2147483648 by reflexivity. lia.
Qed.

Lemma sllw_rz_gen2 : forall n, bv_swrap 32 (Z.shiftl 16 (rz_log n mod 32)) = rz_size n.
Proof.
  intros n. pose proof (rz_log_range n) as RLR. rewrite <- (sllw_rz_gen n).
  rewrite !(Z.mod_small (rz_log n)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition class_ok (s : Z) : bool :=
  let c := class_id s in let S := size_of_class c in
  (1 <=? c) && (c <=? 30) && (s <=? S) && (S <=? 65536) && (S mod 16 =? 0) && (16 <=? S)
  && (implb (s <=? 512) (c =? Z.shiftr (s + 31) 5)) && (implb (512 <? s) (17 <=? c)).

Lemma class_ok_all : forallb_range class_ok 1 (Z.to_nat (65536 - 1 + 1)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma class_facts : forall s, 1 <= s <= 65536 ->
  let c := class_id s in let S := size_of_class c in
  1 <= c <= 30 /\ s <= S <= 65536 /\ S mod 16 = 0 /\ 16 <= S
  /\ (s <= 512 -> c = Z.shiftr (s + 31) 5) /\ (512 < s -> 17 <= c).
Proof.
  intros s Hs. cbv zeta.
  pose proof (range_by_compute (fun s => let c := class_id s in let S := size_of_class c in
              1 <= c <= 30 /\ s <= S <= 65536 /\ S mod 16 = 0 /\ 16 <= S /\ (s <= 512 -> c = Z.shiftr (s + 31) 5) /\ (512 < s -> 17 <= c))
              class_ok 1 65536) as R.
  apply R; [| exact class_ok_all | exact Hs].
  intros z Hz. unfold class_ok in Hz. cbv zeta.
  repeat (apply andb_prop in Hz; destruct Hz as [Hz ?H]).
  repeat match goal with H : implb _ _ = true |- _ => rewrite implb_true_iff in H end.
  repeat split; intros; lia.
Qed.

(* [comment removed for export] *)
Definition cls_ok (c : Z) : bool :=
  let S := size_of_class c in (16 <=? S) && (S <=? 65536) && (S mod 16 =? 0) && (2 <=? max_cached c) && (max_cached c <=? 16)
  && (implb (17 <=? c) (S mod 256 =? 0)) && (implb (17 <=? c) (768 <=? S)).
Lemma cls_ok_all : forallb_range cls_ok 1 (Z.to_nat (30 - 1 + 1)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cls_facts : forall c, 1 <= c <= 30 ->
  16 <= size_of_class c <= 65536 /\ size_of_class c mod 16 = 0 /\ 2 <= max_cached c <= 16
  /\ (17 <= c -> size_of_class c mod 256 = 0 /\ 768 <= size_of_class c).
Proof.
  intros c Hc.
  pose proof (range_by_compute (fun c => 16 <= size_of_class c <= 65536 /\ size_of_class c mod 16 = 0 /\ 2 <= max_cached c <= 16
              /\ (17 <= c -> size_of_class c mod 256 = 0 /\ 768 <= size_of_class c)) cls_ok 1 30) as R.
  apply R; [| exact cls_ok_all | exact Hc].
  intros z Hz. unfold cls_ok in Hz. cbv zeta in Hz.
  repeat (apply andb_prop in Hz; destruct Hz as [Hz ?H]).
  repeat match goal with H : implb _ _ = true |- _ => rewrite implb_true_iff in H end.
  repeat split; intros; lia.
Qed.

(* [comment removed for export] *)
Lemma prim_class_facts : forall n c, 1 <= n -> is_primary n = true -> class_id (needed_size n) = c ->
  1 <= c <= 30 /\ needed_size n <= size_of_class c <= 65536 /\ size_of_class c mod 16 = 0
  /\ (needed_size n <= 512 -> c = Z.shiftr (needed_size n + 31) 5 /\ size_of_class c = 32 * c)
  /\ 2 <= max_cached c <= 16.
Proof.
  intros n c N PRIM HC. pose proof (prim_facts n N PRIM) as (NS & RZR & _ & _ & _ & _ & _ & NR).
  pose proof (class_facts (needed_size n) ltac:(lia)) as CF. cbv zeta in CF. rewrite HC in CF.
  destruct CF as (C1 & C2 & C3 & C4 & C5 & C6).
  pose proof (cls_facts c C1) as (D1 & D2 & D3 & D4).
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [| exact D3].
  intros L. split; [exact (C5 L)|]. apply size_of_class_small. specialize (C5 L). rewrite C5.
  rewrite Z.shiftr_div_pow2 by lia. clear -L NR. Z.div_mod_to_equations. lia.
Qed.
End CANSEC1.

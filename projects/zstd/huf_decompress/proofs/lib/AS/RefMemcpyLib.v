(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (51 recorded proofs replaced by written proofs (firstn_add, firstn_sub_app, skipn_add and 48 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RefMemcpyLib () := "c59OSSVerify5KrLib2AS<RefMemcpyLib3subC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3appI47Corelib4Init9Datatypes4list00C47Corelib4Init3Nat3addC47Corelib5Lists7ListDef5skipnI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C47Corelib4Init5Logic6eq_indc59OSSVerify5KrLib2AS<RefMemcpyLib:firstn_addC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4flipC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List<length_skipnI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3minC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z8min_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List=length_firstnC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C35stdpp7tactics<f_equal_helpc59OSSVerify5KrLib2AS<RefMemcpyLib9skipn_addC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_allK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init5Peano2ltC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3nthK47Corelib7Numbers7BinNums1Z02C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedC59OSSVerify5KrLib2AS5Hoare3at_C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfI47Corelib7Numbers7BinNums1N00K47Corelib4Init5Logic4True01C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC59OSSVerify5KrLib2AS5Hoare4at_0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLib7at_succC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib2AS7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic8iff_reflC59OSSVerify5KrLib2AS5Hoare5at_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLib<word_succ_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC56Stdlib5Arith8PeanoNat3Nat;le_gt_casesc59OSSVerify5KrLib2AS<RefMemcpyLib:wbytes_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLib>firstn_sub_appC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c59OSSVerify5KrLib2AS<RefMemcpyLib=wbytes_extendC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib2AS8PropExec7seg_romC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2AS8PropExec3rdnC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init5Logic5False00c59OSSVerify5KrLib2AS<RefMemcpyLib9rdn_skipnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib2AS8PropExecDbytes_le_to_Z_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExecCbytes_le_to_Z_boundC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01c59OSSVerify5KrLib2AS<RefMemcpyLib=lez_bound_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLib:lez4_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z4of_NC35stdpp9decidable;bool_decideC35stdpp9decidableCbool_decide_reflectI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic3notC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9not_morphK46Stdlib9micromega5Tauto8GFormula07C45stdpp9bitvector;definitions=bv_swrap_specC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC45stdpp9bitvector;definitions@bv_wrap_spec_lowc59OSSVerify5KrLib2AS<RefMemcpyLib6u_lez4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLib3LWvC1?~~~~~~~~~~~~~~~C35stdpp4base:decide_relC45stdpp7numbers1Z6lt_decC46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z;lt_ge_casesc59OSSVerify5KrLib2AS<RefMemcpyLib=testbit_u_LWvC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowC59OSSVerify5KrLib2AS8PropExec>Z_testbit_highC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1ZBmod_pow2_bits_highC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3lorK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z6bits_0C47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib2AS8PropExec8u8_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z;shiftl_specC56Stdlib6ZArith6BinInt1Z8lor_specc59OSSVerify5KrLib2AS<RefMemcpyLib8lez_consC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z=testbit_neg_rC46Stdlib4Bool4Bool;orb_false_rc59OSSVerify5KrLib2AS<RefMemcpyLib@testbit_lez_highC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec<bytes_le_appC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z6shiftrc59OSSVerify5KrLib2AS<RefMemcpyLibAtestbit_lez_skipnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;shiftr_specC45stdpp9bitvector;definitionsAbv_wrap_spec_highc59OSSVerify5KrLib2AS<RefMemcpyLibAZ_to_le_bytes_lezC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExecBZ_to_le_bytes_wrapC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc59OSSVerify5KrLib2AS<RefMemcpyLibEword_to_le_bytes_4_eqC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions=bv_wrap_smallc59OSSVerify5KrLib2AS<RefMemcpyLib3LBvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_srliC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLib?testbit_nth_lezC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLib:sb_byte_eqC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula0:C59OSSVerify5KrLib2AS8PropExec7v_srliwC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto4kind02C59OSSVerify5KrLib2AS8PropExec6v_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4v_orC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appc59OSSVerify5KrLib2AS<RefMemcpyLibBtestbit_lez_firstnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLib?testbit_lez_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLibCtestbit_u_srliw_LWvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLibBtestbit_u_slli_LWvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLib=testbit_u_vorC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lor_commc59OSSVerify5KrLib2AS<RefMemcpyLib>sw_bytes_mergeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib2AS7StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLib4at_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StoreOk<store_ok_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List2InC59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec:getr_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLib:keeps_getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I59OSSVerify5KrLib2AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim<msteps_transC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c59OSSVerify5KrLib2AS<RefMemcpyLib8keeps_csC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_eq_decC35stdpp4base6decideI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib2AS8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_ind".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sub {A} (bs : list A) (j k : nat) : list A := firstn k (skipn j bs).

Lemma firstn_add : forall {A} (l : list A) a b,
  firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  intros A l a. revert l. induction a as [|a IH]; intros l b.
  - cbn. reflexivity.
  - destruct l as [|x l]; cbn.
    + destruct b; reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma firstn_sub_app : forall {A} (bs : list A) j k,
  firstn j bs ++ sub bs j k = firstn (j + k) bs.
Proof. intros. unfold sub. rewrite firstn_add. reflexivity. Qed.

Lemma skipn_add : forall {A} (l : list A) a b, skipn (a + b) l = skipn b (skipn a l).
Proof.
  intros A l a. revert l. induction a as [|a IH]; intros l b; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct b; reflexivity|]. apply IH.
Qed.

Lemma sub_length : forall {A} (bs : list A) j k,
  (j + k <= length bs)%nat -> length (sub bs j k) = k.
Proof.
  intros A bs j k H. unfold sub. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma sub_split : forall {A} (bs : list A) j a b,
  sub bs j (a + b) = sub bs j a ++ sub bs (j + a) b.
Proof.
  intros A bs j a b. unfold sub. rewrite firstn_add. f_equal.
  rewrite <- skipn_add. f_equal; lia.
Qed.

Lemma sub_0_all : forall {A} (bs : list A), sub bs 0 (length bs) = bs.
Proof. intros. unfold sub. cbn. apply firstn_all. Qed.

Lemma length_firstn_id : forall {A} (bs : list A) k, k = length bs -> firstn k bs = bs.
Proof. intros A bs k ->. apply firstn_all. Qed.

Lemma sub_nth : forall (bs : list byte) j,
  (j < length bs)%nat -> sub bs j 1 = [nth j bs (Z_to_bv 8 0)].
Proof.
  intros bs j. revert bs. induction j as [|j IH]; intros bs H.
  - destruct bs; cbn in *; [lia|reflexivity].
  - destruct bs; cbn in *; [lia|]. unfold sub in IH. apply IH. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma at_succ : forall (a : word) d, (at_ a d + 1)%bv = at_ a (d + 1).
Proof.
  intros a d. unfold at_. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_unsigned (1 : word)) with 1.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma word_succ_at : forall (a : word), (a + 1)%bv = at_ a 1.
Proof. intros a. rewrite <- (at_0 a) at 1. rewrite at_succ. reflexivity. Qed.

Lemma at_u : forall (a : word) d,
  0 <= bv_unsigned a + d -> bv_unsigned a + d < 2^64 ->
  bv_unsigned (at_ a d) = bv_unsigned a + d.
Proof. intros a d H1 H2. unfold at_. apply u_Z2bv; lia. Qed.

Lemma at_nat : forall (a : word) (j : nat), (a + nat_to_word j)%bv = at_ a (Z.of_nat j).
Proof.
  intros a j. unfold at_, nat_to_word. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbytes_app : forall bs1 bs2 m (a : word),
  wbytes m a (bs1 ++ bs2) = wbytes (wbytes m a bs1) (at_ a (Z.of_nat (length bs1))) bs2.
Proof.
  induction bs1 as [|b r IH]; intros bs2 m a.
  - cbn [app wbytes length Z.of_nat]. rewrite at_0. reflexivity.
  - cbn [app wbytes length]. rewrite IH. f_equal.
    rewrite word_succ_at, at_at. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_extend : forall m (dst : word) bs j k,
  wbytes (wbytes m dst (firstn j bs)) (at_ dst (Z.of_nat j)) (sub bs j k)
  = wbytes m dst (firstn (j + k) bs) \/ (length bs < j)%nat.
Proof.
  intros m dst bs j k.
  destruct (Nat.le_gt_cases j (length bs)) as [H|H]; [left|right; exact H].
  rewrite <- firstn_sub_app, wbytes_app. rewrite length_firstn. f_equal. f_equal. f_equal. lia.
Qed.

Lemma wbytes_extend' : forall m (dst : word) bs j k,
  (j <= length bs)%nat ->
  wbytes (wbytes m dst (firstn j bs)) (at_ dst (Z.of_nat j)) (sub bs j k)
  = wbytes m dst (firstn (j + k) bs).
Proof.
  intros m dst bs j k H. destruct (wbytes_extend m dst bs j k) as [E|E]; [exact E|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_skipn : forall segs mem n (a : word) bs j,
  rdn segs mem a n = Some bs -> (j <= n)%nat ->
  rdn segs mem (at_ a (Z.of_nat j)) (n - j) = Some (skipn j bs).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs j H Hj.
  - assert (j = 0)%nat by lia. subst j. cbn in H. injection H as <-.
    rewrite at_0. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1)%bv n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct j as [|j].
    + rewrite at_0. cbn [Nat.sub skipn rdn]. rewrite Eb, Er. reflexivity.
    + cbn [skipn]. replace (S n - S j)%nat with (n - j)%nat by lia.
      replace (at_ a (Z.of_nat (S j))) with (at_ (a + 1)%bv (Z.of_nat j))
        by (rewrite word_succ_at, at_at; f_equal; lia).
      apply IH; [exact Er|lia].
Qed.

Lemma rdn_sub : forall segs mem n (a : word) bs j k,
  rdn segs mem a n = Some bs -> (j + k <= n)%nat ->
  rdn segs mem (at_ a (Z.of_nat j)) k = Some (sub bs j k).
Proof.
  intros segs mem n a bs j k H Hjk. unfold sub.
  apply (rdn_firstn segs mem (n - j)); [|lia].
  apply rdn_skipn; [exact H|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Abbreviation lez := bytes_le_to_Z.

(* [comment removed for export] *)
Definition LWv (l : list byte) : word := v_lw (Z_to_bv 64 (lez l)).

Lemma lez_bound_len : forall bs k, length bs = k -> 0 <= lez bs < 2 ^ (8 * Z.of_nat k).
Proof. intros bs k <-. split; [apply bytes_le_to_Z_nonneg | apply bytes_le_to_Z_bound]. Qed.
Lemma lez4_range : forall l, length l = 4%nat -> 0 <= lez l < 2 ^ 32.
Proof. intros l H. pose proof (lez_bound_len l 4%nat H). change (8 * Z.of_nat 4) with 32 in H0. lia. Qed.
Lemma u_lez4 : forall l, length l = 4%nat -> bv_unsigned (Z_to_bv 64 (lez l)) = lez l.
Proof. intros l H. pose proof (lez4_range l H). apply u_Z2bv; lia. Qed.

Lemma testbit_u_LWv : forall l i, length l = 4%nat -> 0 <= i < 32 ->
  Z.testbit (bv_unsigned (LWv l)) i = Z.testbit (lez l) i.
Proof.
  intros l i H Hi. unfold LWv, v_lw. rewrite Z_to_bv_unsigned, u_lez4 by exact H.
  rewrite bv_wrap_spec_low by lia.
  rewrite bv_swrap_spec by lia.
  case_bool_decide; [reflexivity|].
  replace i with 31 by lia. reflexivity.
Qed.

Lemma u_vlw_mod32 : forall l, length l = 4%nat -> bv_unsigned (LWv l) mod 2 ^ 32 = lez l.
Proof.
  intros l H. pose proof (lez4_range l H) as R.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 32) as [Hl|Hh].
  - rewrite Z.mod_pow2_bits_low by lia. apply testbit_u_LWv; [exact H|lia].
  - rewrite Z.mod_pow2_bits_high by lia. symmetry. apply (Z_testbit_high 32); lia.
Qed.

Lemma lez_cons : forall b bs, lez (b :: bs) = Z.lor (bv_unsigned b) (Z.shiftl (lez bs) 8).
Proof. reflexivity. Qed.

Lemma testbit_lez_high : forall bs i, 8 * Z.of_nat (length bs) <= i -> Z.testbit (lez bs) i = false.
Proof.
  intros bs i Hi. apply (Z_testbit_high (8 * Z.of_nat (length bs))); try lia.
  apply lez_bound_len. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma testbit_lez_skipn : forall q bs i, 0 <= i ->
  Z.testbit (lez (skipn q bs)) i = Z.testbit (lez bs) (i + 8 * Z.of_nat q).
Proof.
  induction q as [|q IH]; intros bs i Hi.
  - cbn [skipn]. f_equal. lia.
  - destruct bs as [|b bs].
    + cbn [skipn lez]. rewrite !Z.bits_0. reflexivity.
    + cbn [skipn]. rewrite IH by lia. rewrite lez_cons.
      rewrite Z.lor_spec, Z.shiftl_spec by lia.
      pose proof (u8_range b).
      rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. cbn [orb]. f_equal. lia.
Qed.

Lemma testbit_lez_firstn : forall q bs i, 0 <= i ->
  Z.testbit (lez (firstn q bs)) i = if i <? 8 * Z.of_nat q then Z.testbit (lez bs) i else false.
Proof.
  induction q as [|q IH]; intros bs i Hi.
  - cbn [firstn lez]. rewrite Z.bits_0. destruct (Z.ltb_spec i (8 * Z.of_nat 0)); [lia|reflexivity].
  - destruct bs as [|b bs].
    + cbn [firstn lez]. rewrite !Z.bits_0. destruct (i <? _); reflexivity.
    + cbn [firstn]. rewrite !lez_cons, !Z.lor_spec, !Z.shiftl_spec by lia.
      destruct (Z.lt_ge_cases i 8) as [H8|H8].
      * rewrite !(Z.testbit_neg_r _ (i - 8)) by lia.
        destruct (Z.ltb_spec i (8 * Z.of_nat (S q))); [reflexivity|lia].
      * rewrite IH by lia.
        destruct (Z.ltb_spec (i - 8) (8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (S q))); try lia; try reflexivity.
        pose proof (u8_range b). rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. reflexivity.
Qed.

Lemma testbit_lez_app : forall xs ys i, 0 <= i ->
  Z.testbit (lez (xs ++ ys)) i =
  if i <? 8 * Z.of_nat (length xs) then Z.testbit (lez xs) i else Z.testbit (lez ys) (i - 8 * Z.of_nat (length xs)).
Proof.
  intros xs ys i Hi. rewrite bytes_le_app, Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i (8 * Z.of_nat (length xs))).
  - rewrite (Z.testbit_neg_r (lez ys)) by lia. apply orb_false_r.
  - rewrite testbit_lez_high by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_lez : forall bs, Z_to_le_bytes (length bs) (lez bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes].
  replace (Z.shiftr (lez (b :: bs)) 8) with (lez bs).
  2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.shiftr_spec by lia.
      pose proof (testbit_lez_skipn 1 (b :: bs) i Hi) as E. change (skipn 1 (b :: bs)) with bs in E.
      rewrite E. reflexivity. }
  rewrite IH. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
  destruct (Z.lt_ge_cases i 8).
  - rewrite bv_wrap_spec_low by lia. rewrite lez_cons, Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (i - 8)) by lia. apply orb_false_r.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.

Lemma word_to_le_bytes_4_eq : forall (v : word) (l : list byte),
  length l = 4%nat ->
  (forall i, 0 <= i < 32 -> Z.testbit (bv_unsigned v) i = Z.testbit (lez l) i) ->
  word_to_le_bytes 4 v = l.
Proof.
  intros v l Hl Hb. unfold word_to_le_bytes.
  rewrite <- (Z_to_le_bytes_wrap 4 32) by (cbn; lia).
  rewrite <- Hl at 1. rewrite <- (Z_to_le_bytes_lez l). rewrite Hl. f_equal.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 32).
  - rewrite bv_wrap_spec_low by lia. apply Hb. lia.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply testbit_lez_high. rewrite Hl. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_LWv : forall l, length l = 4%nat -> word_to_le_bytes 4 (LWv l) = l.
Proof.
  intros l H. apply word_to_le_bytes_4_eq; [exact H|]. intros i Hi. apply testbit_u_LWv; assumption.
Qed.

(* [comment removed for export] *)
Definition LBv (b : byte) : word := Z_to_bv 64 (bv_unsigned b).

Lemma sb_byte_LBv : forall b : byte, Z_to_bv 8 (bv_unsigned (LBv b)) = b.
Proof.
  intros b. unfold LBv. pose proof (u8_range b). rewrite u_Z2bv by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

(* [comment removed for export] *)
Lemma sb_byte_eq : forall (v : word) (b : byte),
  (forall i, 0 <= i < 8 -> Z.testbit (bv_unsigned v) i = Z.testbit (bv_unsigned b) i) ->
  Z_to_bv 8 (bv_unsigned v) = b.
Proof.
  intros v b Hb. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
  destruct (Z.lt_ge_cases i 8).
  - rewrite bv_wrap_spec_low by lia. apply Hb. lia.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.

Lemma testbit_nth_lez : forall l q i, 0 <= i < 8 -> (q < length l)%nat ->
  Z.testbit (bv_unsigned (nth q l (Z_to_bv 8 0))) i = Z.testbit (lez l) (i + 8 * Z.of_nat q).
Proof.
  intros l q i Hi Hq. rewrite <- testbit_lez_skipn by lia.
  revert l Hq. induction q as [|q IH]; intros l Hq.
  - destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. rewrite lez_cons.
    rewrite Z.lor_spec, Z.shiftl_spec, (Z.testbit_neg_r _ (i - 8)) by lia. symmetry. apply orb_false_r.
  - destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. apply IH. cbn in Hq. lia.
Qed.

(* [comment removed for export] *)
Lemma sb_byte_srli_LWv : forall l q, length l = 4%nat -> (q <= 3)%nat ->
  Z_to_bv 8 (bv_unsigned (v_srli (LWv l) (8 * Z.of_nat q))) = nth q l (Z_to_bv 8 0).
Proof.
  intros l q H Hq. apply sb_byte_eq. intros i Hi.
  unfold v_srli. rewrite Z_to_bv_unsigned, bv_wrap_spec_low, Z.shiftr_spec by lia.
  rewrite testbit_u_LWv by (try exact H; lia).
  rewrite testbit_nth_lez by (try rewrite H; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma testbit_u_srliw_LWv : forall l s i, length l = 4%nat -> 1 <= s -> 0 <= i ->
  Z.testbit (bv_unsigned (v_srliw (LWv l) s)) i = if i + s <? 32 then Z.testbit (lez l) (i + s) else false.
Proof.
  intros l s i H Hs Hi. unfold v_srliw. rewrite Z_to_bv_unsigned.
  assert (Sh : forall j, 0 <= j -> Z.testbit (Z.shiftr (bv_wrap 32 (bv_unsigned (LWv l))) s) j
                              = if j + s <? 32 then Z.testbit (lez l) (j + s) else false).
  { intros j Hj. rewrite Z.shiftr_spec by lia.
    destruct (Z.ltb_spec (j + s) 32).
    - rewrite bv_wrap_spec_low by lia. apply testbit_u_LWv; [exact H|lia].
    - apply bv_wrap_spec_high. lia. }
  destruct (Z.lt_ge_cases i 64).
  - rewrite bv_wrap_spec_low by lia. rewrite bv_swrap_spec by lia.
    case_bool_decide.
    + apply Sh. lia.
    + rewrite Sh by lia.
      destruct (Z.ltb_spec (Z.of_N 32 - 1 + s) 32), (Z.ltb_spec (i + s) 32); try lia; reflexivity.
  - rewrite bv_wrap_spec_high by lia. destruct (Z.ltb_spec (i + s) 32); [lia|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma testbit_u_slli_LWv : forall l s i, length l = 4%nat -> 0 <= s -> 0 <= i < 32 ->
  Z.testbit (bv_unsigned (v_slli (LWv l) s)) i = if i <? s then false else Z.testbit (lez l) (i - s).
Proof.
  intros l s i H Hs Hi. unfold v_slli. rewrite Z_to_bv_unsigned.
  rewrite bv_wrap_spec_low by lia. rewrite Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i s).
  - apply Z.testbit_neg_r. lia.
  - apply testbit_u_LWv; [exact H|lia].
Qed.

Lemma testbit_u_vor : forall (x y : word) i, 0 <= i ->
  Z.testbit (bv_unsigned (v_or x y)) i = Z.testbit (bv_unsigned x) i || Z.testbit (bv_unsigned y) i.
Proof.
  intros x y i Hi. unfold v_or. rewrite Z_to_bv_unsigned.
  destruct (Z.lt_ge_cases i 64).
  - rewrite bv_wrap_spec_low by lia. apply Z.lor_spec.
  - rewrite bv_wrap_spec_high by lia.
    pose proof (u64_range x). pose proof (u64_range y).
    rewrite (Z_testbit_high 64 (bv_unsigned x)) by lia. rewrite (Z_testbit_high 64 (bv_unsigned y)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_merge : forall l1 l2 (q : nat) (v : word),
  length l1 = 4%nat -> length l2 = 4%nat -> (1 <= q <= 3)%nat ->
  v = v_or (v_slli (LWv l2) (32 - 8 * Z.of_nat q)) (v_srliw (LWv l1) (8 * Z.of_nat q)) ->
  word_to_le_bytes 4 v = skipn q l1 ++ firstn q l2.
Proof.
  intros l1 l2 q v H1 H2 Hq ->.
  apply word_to_le_bytes_4_eq.
  { rewrite length_app, length_skipn, length_firstn, H1, H2. lia. }
  intros i Hi.
  rewrite testbit_u_vor by lia.
  rewrite testbit_u_slli_LWv by (try exact H2; lia).
  rewrite testbit_u_srliw_LWv by (try exact H1; lia).
  rewrite testbit_lez_app by lia. rewrite length_skipn, H1.
  rewrite testbit_lez_skipn by lia.
  destruct (Z.ltb_spec i (32 - 8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (4 - q))),
           (Z.ltb_spec (i + 8 * Z.of_nat q) 32); try lia.
  - reflexivity.
  - rewrite testbit_lez_firstn by lia.
    destruct (Z.ltb_spec (i - 8 * Z.of_nat (4 - q)) (8 * Z.of_nat q)); [|lia].
    rewrite orb_false_r. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_merge' : forall l1 l2 (q : nat) (v : word),
  length l1 = 4%nat -> length l2 = 4%nat -> (1 <= q <= 3)%nat ->
  v = v_or (v_srliw (LWv l1) (8 * Z.of_nat q)) (v_slli (LWv l2) (32 - 8 * Z.of_nat q)) ->
  word_to_le_bytes 4 v = skipn q l1 ++ firstn q l2.
Proof.
  intros l1 l2 q v H1 H2 Hq ->. apply (sw_bytes_merge l1 l2 q); try assumption.
  unfold v_or. f_equal. apply Z.lor_comm.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma store_ok_at : forall segs m (dst : word) (N : nat) bsw j k,
  bv_unsigned dst + Z.of_nat N <= 2 ^ 64 ->
  store_ok segs m dst N = true ->
  0 <= j -> j + Z.of_nat k <= Z.of_nat N ->
  store_ok segs (wbytes m dst bsw) (at_ dst j) k = true.
Proof.
  intros segs m dst N bsw j k Hnw Hok Hj Hk.
  destruct k as [|k]; [reflexivity|].
  pose proof (u64_range dst).
  apply (store_ok_mono segs (S k) m); [apply wbytes_grows|].
  apply (store_ok_sub segs m dst (at_ dst j) N (S k) Hnw Hok); rewrite at_u; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition callee_kept : list reg :=
  [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition keeps (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r callee_kept -> getr regs' r = getr regs r.

Lemma keeps_refl : forall regs, keeps regs regs.
Proof. intros regs r _. reflexivity. Qed.

Lemma keeps_trans : forall r1 r2 r3, keeps r1 r2 -> keeps r2 r3 -> keeps r1 r3.
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

(* [comment removed for export] *)
Lemma keeps_upd : forall regs regs' (rd : reg) v,
  keeps regs regs' -> ~ In rd callee_kept -> keeps regs (regupd regs' rd v).
Proof.
  intros regs regs' rd v K Hn r Hr.
  rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

(* [comment removed for export] *)
Lemma keeps_getr : forall regs regs' (r : reg), keeps regs regs' -> In r callee_kept -> getr regs' r = getr regs r.
Proof. intros regs regs' r K Hr. apply K, Hr. Qed.

Ltac kept_reg := cbv [callee_kept In]; intuition congruence.

Example keeps_sp_example : forall regs regs', keeps regs regs' -> getr regs' 2 = getr regs 2.
Proof. intros regs regs' K. apply (keeps_getr _ _ 2 K). kept_reg. Qed.

(* [comment removed for export] *)
Ltac not_kept := cbv; clear; intuition discriminate.   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac solve_keeps :=
  repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma runs_trans : forall segs (s0 : machine_state)
    (st1 : bvmap 5 word -> machine_state) (P1 : bvmap 5 word -> Prop)
    (st2 : bvmap 5 word -> machine_state) (P2 : bvmap 5 word -> Prop),
  (exists r1, msteps segs s0 (st1 r1) /\ P1 r1) ->
  (forall r1, P1 r1 -> exists r2, msteps segs (st1 r1) (st2 r2) /\ P2 r2) ->
  exists r2, msteps segs s0 (st2 r2) /\ P2 r2.
Proof.
  intros segs s0 st1 P1 st2 P2 (r1 & R1 & H1) K.
  destruct (K r1 H1) as (r2 & R2 & H2).
  exists r2. split; [eapply msteps_trans; eassumption | exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition callee_saved : list reg :=
  [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition keeps_cs (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r callee_saved -> getr regs' r = getr regs r.

Lemma keeps_cs_refl : forall regs, keeps_cs regs regs.
Proof. intros regs r _. reflexivity. Qed.

Lemma keeps_cs_trans : forall r1 r2 r3, keeps_cs r1 r2 -> keeps_cs r2 r3 -> keeps_cs r1 r3.
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

Lemma keeps_cs_upd : forall regs regs' (rd : reg) v,
  keeps_cs regs regs' -> ~ In rd callee_saved -> keeps_cs regs (regupd regs' rd v).
Proof.
  intros regs regs' rd v K Hn r Hr.
  rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

(* [comment removed for export] *)
Lemma keeps_cs_upd_same : forall regs regs' (rd : reg) v,
  keeps_cs regs regs' -> getr regs rd = v -> rd <> 0%bv -> keeps_cs regs (regupd regs' rd v).
Proof.
  intros regs regs' rd v K Hv Hnz r Hr.
  destruct (decide (r = rd)) as [->|Hne].
  - rewrite getr_same by exact Hnz. symmetry. exact Hv.
  - rewrite getr_other by exact Hne. apply K, Hr.
Qed.

Lemma keeps_keeps_cs : forall regs regs', keeps regs regs' -> keeps_cs regs regs'.
Proof.
  intros regs regs' K r Hr. apply K. unfold callee_saved, callee_kept in *. cbn [In] in *. intuition.
Qed.

Lemma keeps_cs_getr : forall regs regs' (r : reg), keeps_cs regs regs' -> In r callee_saved -> getr regs' r = getr regs r.
Proof. intros regs regs' r K Hr. apply K, Hr. Qed.

Ltac solve_keeps_cs :=
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (28 recorded proofs replaced by written proofs (le8_lit, le4_lit, shl52_land64 and 25 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_fmt_fp_lib () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List6nth_okC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z?mul_mod_distr_lC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib6Common7SFModel8land_W64C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib6Common;SFW1_lemmas<zb_land_pow2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib7ZBridge<zb_land_maskC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC59OSSVerify5KrLib6Common9SoftFloat4hi64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat4lo64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common<F_fmt_fp_lib:hi64_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z9lt_succ_rC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C59OSSVerify5KrLib6Common5FmtFp8signbitlC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3lorC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib6Common5FmtFp;fpclassifylC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing3Pol02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega:ZMicromega;ZArithProof04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib6Common;SFW1_lemmas:swrap32_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MStateAunsigned_lit_wrapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic4True00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK45stdpp9bitvector;definitions2bv01C56Stdlib6ZArith6BinInt1Z7eqb_neqC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib3Lib2FP>freg_get_otherC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib4Init5Logic4True01C46Stdlib5Lists4List:length_mapc59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init9Datatypes3nat00C46Stdlib5Lists4List7map_appC47Corelib4Init9Datatypes3appI47Corelib4Init9Datatypes4prod00I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib5Lists7ListDef:Forall_indC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4Spec5Stdio8to_bytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z=shiftl_nonnegC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith8Zbitwise1Z<add_lor_landC56Stdlib6ZArith6BinInt1Z;land_nonnegC47Corelib4Init5Logic3iffC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z9pow_add_rK46Stdlib9micromega5Tauto8GFormula09C47Corelib4Init9Datatypes8list_indC56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums1N01c59OSSVerify5KrLib6Common<F_fmt_fp_libCbytes_le_to_Z_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z?shiftl_spec_lowC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z>ones_spec_highC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z@land_lor_distr_lC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z:shiftl_0_rC56Stdlib6ZArith6BinInt1Z8sub_diagC56Stdlib6ZArith6BinInt1Z?shiftr_shiftl_lC56Stdlib6ZArith6BinInt1Z:shiftr_lorI47Corelib7Numbers7BinNums1N00c59OSSVerify5KrLib6Common<F_fmt_fp_libBZ_to_le_bytes_to_ZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib3Arr4u32sC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib5Lists4List<length_skipnC47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List<firstn_skipnC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List=length_firstnc59OSSVerify5KrLib6Common<F_fmt_fp_lib<le4_of_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib3Lib3Arr;u32s_lengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init5Peano2ltC46Stdlib5Lists4List>nth_error_nth'C46Stdlib5Lists4List9nth_errorc59OSSVerify5KrLib6Common<F_fmt_fp_lib4wnthC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib3Lib3ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=nth_error_nthC47Corelib5Lists7ListDef3nthc59OSSVerify5KrLib6Common<F_fmt_fp_lib4wvalC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat;lt_ge_casesI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses9not_morphC59OSSVerify5KrLib3Lib3ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_overflowC59OSSVerify5KrLib3Lib3Arr:upd_lengthC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith6BinInt1Z7div_divC47Corelib7Classes>Morphisms_Prop@not_iff_morphismC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc59OSSVerify5KrLib6Common<F_fmt_fp_lib9sx32_zeroC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib7Classes?RelationClasses>iff_TransitiveC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x2 := getreg 2%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "sp=" x2.

(* [comment removed for export] *)
Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Ltac fix_litstore :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | _ => idtac
  end.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac zstep0 := zs.

(* [comment removed for export] *)
Ltac name_cb n H := match type of H with context [CB n ?l] => let j := fresh "jk" in set (j := l) in H; clearbody j end.

(* [comment removed for export] *)
Lemma shl52_land64 : forall f, (0 <= f)%Z -> Z.land (Z.shiftl f 52) 18446744073709551615 = (4503599627370496 * (f mod 4096))%Z.
Proof.
  intros f Hf. rewrite land_W64, Z.shiftl_mul_pow2 by lia. change (2^64)%Z with (4503599627370496 * 4096)%Z.
  change (2^52)%Z with 4503599627370496%Z. rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. reflexivity.
Qed.
Lemma land_bit11 : forall f, Z.land f 2048 = (2048 * ((f / 2048) mod 2))%Z.
Proof. intros. change 2048%Z with (2^11)%Z. rewrite zb_land_pow2 by lia. reflexivity. Qed.
Lemma land_bit0 : forall f, Z.land f 1 = (f mod 2)%Z.
Proof. intros. change 1%Z with (2^1 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma hi64_range : forall x, (0 <= hi64 x < 2^64)%Z.
Proof. intros. unfold hi64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.
Lemma lo64_range : forall x, (0 <= lo64 x < 2^64)%Z.
Proof. intros. unfold lo64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.

Lemma signbitl_range : forall x, (0 <= signbitl x <= 1)%Z.
Proof.
  intros. unfold signbitl. pose proof (hi64_range x). rewrite Z.shiftr_div_pow2 by lia.
  split; [apply Z.div_pos; lia|]. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma fpclassifyl_range : forall x, (0 <= fpclassifyl x <= 4)%Z.
Proof. intros. unfold fpclassifyl. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. Qed.

(* [comment removed for export] *)
Lemma sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, swrap32_eq.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Ltac unwrapK K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K.
Ltac mlia := Z.div_mod_to_equations; lia.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].

Lemma fother : forall (F : bvmap 5 word) (v : word) (k : reg),
  bv_unsigned k <> 10%Z -> reg_get (bvmap_set 10 v F) k = reg_get F k.
Proof.
  intros F v k Hk. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq.
  change (bv_unsigned (10 : reg)) with 10%Z. lia.
Qed.

(* [comment removed for export] *)
Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.
Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
(* [comment removed for export] *)
Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
  Forall (fun iv => snd iv <= A \/ A + N <= fst iv)%Z W -> (A <= a)%Z -> (a + n <= A + N)%Z -> (0 <= n)%Z -> disjoint_from W a n.
Proof.
  intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.
(* [comment removed for export] *)
Lemma zb_to_bytes_eq : forall l, zb l = Stdio.to_bytes l.
Proof. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
  2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  pose proof (bytes_le_to_Z_range bs) as HR.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
    2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.ltb_spec0 i 8).
        - rewrite Z.shiftl_spec_low by lia. reflexivity.
        - rewrite Z.ones_spec_high by lia. apply andb_false_r. }
    rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
    rewrite Z.lor_0_l. exact IH.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma u32arr_of_u8arr : forall segs m A bs k,
  u8arr segs m A bs -> length bs = (4 * k)%nat ->
  exists ws, length ws = k /\ u32arr segs m A ws.
Proof.
  intros segs m A bs k [Hb Hw] HL.
  assert (G : forall k bs, length bs = (4 * k)%nat -> exists ws, length ws = k /\ u32s ws = bs).
  { clear. induction k as [|k IH]; intros bs HL.
    - exists []. destruct bs; [split; reflexivity| cbn in HL; lia].
    - destruct (IH (skipn 4 bs) ltac:(rewrite length_skipn; lia)) as (ws & Hlen & Hu).
      exists (le_bytes_to_word (firstn 4 bs) :: ws). split; [cbn; lia|].
      cbn [u32s]. rewrite Hu, le4_of_bytes by (rewrite length_firstn; lia). apply firstn_skipn. }
  destruct (G k bs HL) as (ws & Hlen & Hu). exists ws. split; [exact Hlen|]. split.
  - rewrite Hu. exact Hb.
  - rewrite Hlen. replace (4 * Z.of_nat k)%Z with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.

Lemma u8arr_of_u32arr : forall segs m A ws, u32arr segs m A ws -> u8arr segs m A (u32s ws).
Proof. intros segs m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws))%Z by lia. exact Hw. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wnth (ws : list word) (i : Z) : word := nth (Z.to_nat i) ws (Z_to_bv 64 0).
Definition wval (ws : list word) (i : Z) : Z := (bv_unsigned (wnth ws i) mod 4294967296)%Z.

Lemma nth_error_wnth : forall ws i, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat -> nth_error ws (Z.to_nat i) = Some (wnth ws i).
Proof. intros ws i Hi Hl. unfold wnth. apply nth_error_nth'. exact Hl. Qed.

Lemma wval_upd_same : forall ws i v, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat ->
  wval (upd ws (Z.to_nat i) v) i = (bv_unsigned v mod 4294967296)%Z.
Proof.
  intros ws i v Hi Hl. unfold wval, wnth.
  pose proof (nth_error_upd_same ws (Z.to_nat i) v Hl) as E.
  apply nth_error_nth with (d := Z_to_bv 64 0) in E. rewrite E. reflexivity.
Qed.
Lemma wval_upd_other : forall ws i j v, (0 <= i)%Z -> (0 <= j)%Z -> i <> j ->
  wval (upd ws (Z.to_nat i) v) j = wval ws j.
Proof.
  intros ws i j v Hi Hj Hij. unfold wval, wnth.
  destruct (Nat.lt_ge_cases (Z.to_nat j) (length ws)) as [Hl|Hl].
  - pose proof (nth_error_upd_other ws (Z.to_nat i) (Z.to_nat j) v ltac:(lia)) as E.
    rewrite (nth_error_nth' ws (Z_to_bv 64 0) Hl) in E.
    apply nth_error_nth with (d := Z_to_bv 64 0) in E. rewrite E. reflexivity.
  - rewrite !nth_overflow by (rewrite ?upd_length; lia). reflexivity.
Qed.
Lemma wval_range : forall ws i, (0 <= wval ws i < 4294967296)%Z.
Proof. intros. unfold wval. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma div1e9_magic : forall x, (0 <= x < 2^64)%Z ->
  Z.shiftr (Z.shiftr (Z.shiftr x 9 * 19342813113834067) 64) 11 = (x / 1000000000)%Z.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
  change (2^64 * 2^11)%Z with (2^75)%Z. change 1000000000%Z with (512 * 1953125)%Z. rewrite <- Z.div_div by lia.
  change (2^9)%Z with 512%Z.
  set (y := (x / 512)%Z). assert (Hy : (0 <= y < 2^55)%Z) by (subst y; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  clearbody y. clear x Hx.
  Z.div_mod_to_equations. nia.
Qed.

Lemma sx32_zero : forall w : word, bv_unsigned (sx32 w) = 0%Z <-> (bv_unsigned w mod 4294967296 = 0)%Z.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_modulus in R. change (2^64)%Z with 18446744073709551616%Z in *. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R.
  split; intros H; Z.div_mod_to_equations; lia.
Qed.
Lemma sx32_nonzero : forall w : word, bv_unsigned (sx32 w) <> 0%Z <-> (bv_unsigned w mod 4294967296 <> 0)%Z.
Proof. intros w. rewrite sx32_zero. tauto. Qed.

Lemma mulhu_M_range : forall x, (0 <= x < 2^62)%Z ->
  (0 <= Z.shiftr (Z.shiftr x 9 * 19342813113834067) 64 < 18446744073709551616)%Z.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia.
  split. { apply Z.div_pos; [|lia]. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]. }
  apply Z.div_lt_upper_bound; [lia|].
  assert (x / 2^9 < 2^53)%Z by (apply Z.div_lt_upper_bound; lia). 
  assert (0 <= x / 2^9)%Z by (apply Z.div_pos; lia). nia.
Qed.

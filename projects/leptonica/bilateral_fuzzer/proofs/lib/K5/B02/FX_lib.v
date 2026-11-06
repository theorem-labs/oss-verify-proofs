(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Export SFModel Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Export ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Export FX_Layout.
Ltac2 kr_t_FX_lib () := "C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z7testbitK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z4landC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic3notC46Stdlib4Bool4Bool<andb_false_rK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z=pow2_bits_eqbC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z<testbit_trueC47Corelib4Init5Logic5proj1C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z7mul_1_rC56Stdlib6ZArith6BinInt1Z=testbit_falsec69OSSVerify5KrLib2K53B026FX_libAzb_land_pow2_bit0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_0_rI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z03I47Corelib4Init5Logic3and00K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z9mod_smallK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions8bv_swrapc69OSSVerify5KrLib2K53B026FX_lib:swrap32_eqC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C69OSSVerify5KrLib2K53Lib7ZBridge<zb_land_maskC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026FX_lib?land_mask_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9land_onesI45stdpp9bitvector;definitions2bv00K47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem3le8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib2K53Lib3Mem3le4C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega:ZMicromega;ZArithProof04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr06C69OSSVerify5KrLib2K53Lib6MStateAunsigned_lit_wrapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem4sx32C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK45stdpp9bitvector;definitions2bv01C56Stdlib6ZArith6BinInt1Z7eqb_neqC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC69OSSVerify5KrLib2K53Lib2FP>freg_get_otherC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z=shiftl_nonnegC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith8Zbitwise1Z<add_lor_landC56Stdlib6ZArith6BinInt1Z;land_nonnegI47Corelib4Init5Logic2or00C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C46Stdlib9micromega;ZifyClasses5mkrelC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z9pow_add_rK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula09K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums1N01c69OSSVerify5KrLib2K53B026FX_libCbytes_le_to_Z_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z?shiftl_spec_lowC56Stdlib6ZArith6BinInt1Z>ones_spec_highC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z@land_lor_distr_lC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z:shiftl_0_rC56Stdlib6ZArith6BinInt1Z8sub_diagC56Stdlib6ZArith6BinInt1Z?shiftr_shiftl_lC56Stdlib6ZArith6BinInt1Z:shiftr_lorI47Corelib7Numbers7BinNums1N00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~". (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZLemmas.
Local Open Scope Z_scope.

Lemma zb_land_pow2_bit0 : forall x k, 0 <= k -> Z.testbit x k = false -> Z.land x (2^k) = 0.
Proof.
  intros x k Hk Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity| apply Bool.andb_false_r].
Qed.

(* [comment removed for export] *)
Lemma zb_land_pow2 : forall x k, 0 <= k -> Z.land x (2^k) = 2^k * ((x / 2^k) mod 2).
Proof.
  intros x k Hk. destruct (Z.testbit x k) eqn:Hb.
  - pose proof (proj1 (Z.testbit_true x k Hk) Hb) as Hm. rewrite Hm, Z.mul_1_r.
    apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity | apply Bool.andb_false_r].
  - pose proof (proj1 (Z.testbit_false x k Hk) Hb) as Hm. rewrite Hm, Z.mul_0_r.
    apply zb_land_pow2_bit0; assumption.
Qed.

Lemma bv_wrap32_eq : forall z, bv_wrap 32 z = z mod 4294967296.
Proof. reflexivity. Qed.

Lemma swrap32_eq : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. reflexivity. Qed.

Lemma swrap32_small : forall z, - 2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.

Lemma land_mask_small : forall x k, 0 <= k -> 0 <= x < 2^k -> Z.land x (2^k - 1) = x.
Proof. intros x k Hk Hx. rewrite zb_land_mask by lia. apply Z.mod_small. lia. Qed.

Lemma land_W64_small : forall x, 0 <= x < 18446744073709551616 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (2^64 - 1). apply land_mask_small; [lia|]. change (2^64) with 18446744073709551616. lia. Qed.

Lemma land_M32_small : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x Hx. change 4294967295 with (2^32 - 1). apply land_mask_small; [lia|]. change (2^32) with 4294967296. lia. Qed.

Lemma land_W64 : forall y, Z.land y 18446744073709551615 = (y mod 2^64)%Z.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). apply Z.land_ones. lia. Qed.
End ZLemmas.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

Lemma land_bit0 : forall f, Z.land f 1 = (f mod 2)%Z.
Proof. intros. change 1%Z with (2^1 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. Qed.

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

(* [comment removed for export] *)

Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_FMT_emit : Z := 0x15265.        (* [comment removed for export] *)
Definition A_FMT_usage : Z := 0x16729.       (* [comment removed for export] *)
Definition A_FMT_too_big : Z := 0x1b4c4.     (* [comment removed for export] *)
Definition A_FMT_cannot_open : Z := 0x201ea. (* [comment removed for export] *)
Definition A_FMT_read_error : Z := 0x201ff.  (* [comment removed for export] *)
Definition A_FMT_precond : Z := 0x228a9.     (* [comment removed for export] *)
Definition A_FMT_unreached : Z := 0x22c69.   (* [comment removed for export] *)
Definition A_FMT_msg : Z := 0x22f02.         (* [comment removed for export] *)
Definition A_NULLSTR : Z := 0x23ebf.         (* [comment removed for export] *)

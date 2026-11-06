(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Arr Walk Image.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import R_cache_defs R_depot_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
Ltac2 kr_t_R_depot_hash () := "C46Stdlib5Lists4List6nth_okC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List9fold_leftC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib2K53Lib3Mem3le8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K53Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Image>ro_cells_imageC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib2K53Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic4True01C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC69OSSVerify5KrLib2K53B23<R_depot_defs3w64C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9land_onesc69OSSVerify5KrLib2K53B23<R_depot_hash;Z_to_bv_w64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_depot_defs6mm_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorK46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith6BinInt1Z9mod_smallC69OSSVerify5KrLib2K53B23<R_depot_defs6mm_getC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03C47Corelib4Init9Datatypes:option_mapC46Stdlib5Lists4List=nth_error_mapC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C47Corelib5Lists7ListDef3mapC47Corelib5Lists7ListDef6firstnC47Corelib4Init9Datatypes3appC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify5KrLib2K53B23<R_depot_defs<mm_add_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53B23<R_depot_defs7mm_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init5Logic3notC47Corelib4Init5Peano2ltC46Stdlib5Lists4List>nth_error_SomeC46Stdlib5Lists4List>nth_error_app1C69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr;u64arr_readC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC69OSSVerify5KrLib2K53B23<R_depot_defs=mm_init_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23<R_depot_hash=fold_mm_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC69OSSVerify5KrLib2K56Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC69OSSVerify5KrLib2K53Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC69OSSVerify5KrLib2K53Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC69OSSVerify5KrLib2K56Common8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast<sf_load_goalC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv3Sem4core01K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C69OSSVerify5KrLib2K53Lib8StepFast7sf_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast?sf_install_loadC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C69OSSVerify5KrLib2K56Common8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C69OSSVerify5KrLib2K53Lib8StepFast8sf_congTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5v_mulC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5m_mulC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0BC69OSSVerify5KrLib2K56Common8PropExec6v_srliC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC69OSSVerify5KrLib2K56Common8PropExec8alu_srliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C69OSSVerify5KrLib2K56Common8PropExec5v_xorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge9zr_shiftrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_xorC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C69OSSVerify5KrLib2K53Lib7ZBridge7zr_lxorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=fold_left_appc69OSSVerify5KrLib2K53B23<R_depot_hash9hseg_stepC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib2K53Lib8StepFast<sf_branch_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_cong1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C47Corelib4Init5Logic5proj2K46Stdlib9micromega=RingMicromega5Psatz07C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symI47Corelib4Init5Peano2le00C46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List;firstn_all2C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqc69OSSVerify5KrLib2K53B23<R_depot_hash9mm_add_bvC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>nth_error_NoneC69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC4ELinuxProcessSemantics5Riscv3Sem7mul_divK46Stdlib9micromega=RingMicromega5Psatz05C69OSSVerify5KrLib2K53Lib8StepFast;sf_evt_stepC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5mulop01C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C69OSSVerify5KrLib2K53B23<R_depot_defs:depot_hashC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23<R_depot_hash;ro_c8_imageC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC69OSSVerify5KrLib2K56Common8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC69OSSVerify5KrLib2K56Common8PropExec7b_auipcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C69OSSVerify5KrLib2K53Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5v_andC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_andC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec6v_slliC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C69OSSVerify5KrLib2K56Common8PropExec5v_luiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5b_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C69OSSVerify5KrLib2K56Common8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C69OSSVerify5KrLib2K56Common8PropExec7w_addiwC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0;c69OSSVerify5KrLib2K53B23<R_depot_hash9mm_get_bvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23<R_depot_hash9hash_loopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C69OSSVerify5KrLib2K53Lib4Step@ro_cells_read_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_depot_defs4mm_mC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_depot_defs5mm_m8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_depot_defs7mm_seedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem2w0C69OSSVerify5KrLib2K53Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop03".   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma ro_c8_image : forall (m : mem) A v, mem_inv asegs m -> ro_bytes_b asegs A (le8 (Z_to_bv 64 v)) = true -> (0 <= A)%Z ->
  (A + 8 <= 2^64)%Z -> ro_cells asegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v MI Hb HA Hl. pose proof (ro_cells_image asegs m A _ MI Hb HA ltac:(rewrite length_le8; cbn; lia)) as R.
  rewrite length_le8 in R. destruct R as [_ R]. split; [exact (conj I I)| exact R].
Qed.

Lemma Z_to_bv_w64 : forall x, Z_to_bv 64 (w64 x) = Z_to_bv 64 x.
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, w64. change (bv_modulus 64) with (2^64)%Z.
  apply Z.mod_mod. lia.
Qed.

(* [comment removed for export] *)
Lemma mm_add_bv : forall h k,
  Z_to_bv 64 (Z.lxor (Z.land (Z.lxor (Z.shiftr (Z.land (k * 14313749767032793493) 18446744073709551615) 47)
                                    (Z.land (k * 14313749767032793493) 18446744073709551615) * 14313749767032793493)
                            18446744073709551615) h * 14313749767032793493)
  = Z_to_bv 64 (mm_add h k).
Proof.
  intros h k. unfold mm_add, mm_mix, mm_m. rewrite Z_to_bv_w64. change 18446744073709551615%Z with (Z.ones 64).
  rewrite !Z.land_ones by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mm_get_bv : forall H, (0 <= H < 2^64)%Z ->
  Z_to_bv 64
    (Z.lxor
       (Z.shiftr (Z.land (Z.lxor (Z.shiftr (Z.land (Z.lxor 0 (Z.land H 18446744073709551615) * 14313749767032793493)
                                                   18446744073709551615) 47)
                                 (Z.land (Z.lxor 0 (Z.land H 18446744073709551615) * 14313749767032793493)
                                    18446744073709551615) * 14313749767032793493) 18446744073709551615) 47)
       (Z.land (Z.lxor (Z.shiftr (Z.land (Z.lxor 0 (Z.land H 18446744073709551615) * 14313749767032793493)
                                    18446744073709551615) 47)
                       (Z.land (Z.lxor 0 (Z.land H 18446744073709551615) * 14313749767032793493)
                          18446744073709551615) * 14313749767032793493) 18446744073709551615))
  = Z_to_bv 64 (mm_get (mm_add H 0)).
Proof.
  intros H RH. unfold mm_get, mm_add, mm_mix, w64, mm_m. change 18446744073709551615%Z with (Z.ones 64).
  rewrite !Z.land_ones by lia. rewrite (Z.mod_small H (2^64)) by lia. reflexivity.
Qed.

Lemma hseg_step : forall (ws : list word) j w, nth_error ws (Z.to_nat j) = Some w -> (0 <= j)%Z ->
  firstn (Z.to_nat (j + 1)) (map bv_unsigned ws) = firstn (Z.to_nat j) (map bv_unsigned ws) ++ [bv_unsigned w].
Proof.
  intros ws j w Hw Hj. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  assert (Hw' : nth_error (map bv_unsigned ws) (Z.to_nat j) = Some (bv_unsigned w)) by (rewrite nth_error_map, Hw; reflexivity).
  clear Hw. revert ws Hw'. induction (Z.to_nat j) as [|n IH]; intros ws Hw'; destruct ws as [|x ws]; cbn in *; try discriminate.
  - injection Hw' as <-. reflexivity.
  - f_equal. apply IH. exact Hw'.
Qed.

Lemma fold_mm_range : forall l h, (0 <= h < 2^64)%Z -> (0 <= fold_left mm_add l h < 2^64)%Z.
Proof. induction l as [|x l IH]; intros h Hh; cbn [fold_left]; [exact Hh| apply IH, mm_add_range]. Qed.

Section HASH.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (TR sz : Z) (ws rest : list word) (Q : machine_state -> Prop).
Hypothesis Hsz : (1 <= sz <= 254)%Z.
Hypothesis Hl : Z.of_nat (length ws) = sz.
Hypothesis HTR : (0 <= TR /\ TR + 2040 <= 2^63)%Z.
Hypothesis TB : u64arr asegs m TR (ws ++ rest).

Section LOOP.
Variables (s3 s6 s7 : word).
Hypothesis K : forall a5 a6, evt asegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14313749767032793493) (Z_to_bv 64 (TR + 8 * sz))
             (Z_to_bv 64 (fold_left mm_add (map bv_unsigned ws) (mm_init sz))) (Z_to_bv 64 0) (Z_to_bv 64 (TR + 8 * sz))
             a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xebdb8) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Lemma hash_loop : forall k j hacc a5 a6, Z.to_nat (sz - j) = k -> (0 <= j < sz)%Z ->
  hacc = fold_left mm_add (firstn (Z.to_nat j) (map bv_unsigned ws)) (mm_init sz) ->
  evt asegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14313749767032793493) (Z_to_bv 64 (TR + 8 * j)) (Z_to_bv 64 hacc)
             (Z_to_bv 64 0) (Z_to_bv 64 (TR + 8 * sz)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xebd94) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j hacc a5 a6 Hk Hj Eh; [lia|].
  destruct (nth_error ws (Z.to_nat j)) as [w|] eqn:Hw; [| apply nth_error_None in Hw; lia].
  pose proof (u64arr_read asegs m TR (ws ++ rest) j w (Z_to_bv 64 (TR + 8 * j)) TB
                ltac:(rewrite nth_error_app1 by (apply nth_error_Some; rewrite Hw; discriminate); exact Hw)
                ltac:(lia) ltac:(reflexivity)) as RD.
  assert (Rh : (0 <= hacc < 2^64)%Z) by (rewrite Eh; apply fold_mm_range, mm_init_range).
  do 8 zstep. clear RD.
  rewrite mm_add_bv.
  assert (Eh' : mm_add hacc (bv_unsigned w) = fold_left mm_add (firstn (Z.to_nat (j + 1)) (map bv_unsigned ws)) (mm_init sz)).
  { rewrite (hseg_step ws j w Hw) by lia. rewrite fold_left_app. cbn [fold_left]. rewrite Eh. reflexivity. }
  rewrite Eh'. clear Eh'.
  zstep.
  destruct (Z.eq_dec (j + 1) sz) as [Ej|Nj].
  - ifF. replace (TR + 8 * j + 8)%Z with (TR + 8 * sz)%Z by lia. rewrite Ej. rewrite firstn_all2 by (rewrite map_length; lia). apply K.
  - ifT. replace (TR + 8 * j + 8)%Z with (TR + 8 * (j + 1))%Z by lia. apply (IH (j + 1)%Z); [lia| lia| reflexivity].
Qed.
End LOOP.

(* [comment removed for export] *)
Lemma hash_frag : forall a0 a3 a4 a5 a6 s3 s6 s7,
  mem_inv asegs m ->
  (forall a0' a1' a2' a4' a5' a6', evt asegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' (Z_to_bv 64 0x400000) a4' a5' a6' a7 s2
             (Z_to_bv 64 (depot_hash (map bv_unsigned ws))) s4 s5 (Z_to_bv 64 0xffff) (Z_to_bv 64 0x7fffffff) s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0xebdf8) fc None m (seg_rom asegs))) ->
  evt asegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 TR) (Z_to_bv 64 sz) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0xebd5c) fc None m (seg_rom asegs)).
Proof.
  intros a0 a3 a4 a5 a6 s3 s6 s7 MI K2.
  pose proof (ro_c8_image m 0x10320 mm_m MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as RM.
  pose proof (ro_c8_image m 0x10378 mm_m8 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as RM8.
  pose proof (ro_c8_image m 0x10668 mm_seed MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as RS.
  unfold mm_m, mm_m8, mm_seed in RM, RM8, RS.
  do 14 zstep.
  assert (E1 : Z.land sz 4294967295 = sz).
  { change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones, Z.mod_small by lia. reflexivity. }
  assert (E2 : Z.shiftr sz 32 = 0%Z).
  { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. }
  rewrite E1, E2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z. replace (sz * 8)%Z with (8 * sz)%Z by lia.
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  change (Z.lxor (sz * 3829533694005038248 mod 2 ^ 64) 10900877739976798860) with (mm_init sz).
  replace (Z_to_bv 64 TR) with (Z_to_bv 64 (TR + 8 * 0)) by (f_equal; lia).
  eapply (hash_loop s3 s6 s7) with (k := Z.to_nat sz) (j := 0%Z); [| lia| lia| reflexivity].
  intros a5' a6'.
  do 16 zstep.
  rewrite mm_get_bv by (apply fold_mm_range, mm_init_range).
  replace (mm_get (mm_add (fold_left mm_add (map bv_unsigned ws) (mm_init sz)) 0)) with (depot_hash (map bv_unsigned ws))
    by (unfold depot_hash; rewrite map_length, Hl; reflexivity).
  apply K2.
Qed.
End HASH.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Export StartupTac RefMemcpyLib.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_SumsLib () := "C47Corelib7Program6Basics4flipC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilC46Stdlib5Lists4List=repeat_lengthK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5Hoare3at_C13~~~K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StepTac6u_Z2bvC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_addC13~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C47Corelib4Init5Logic7f_equalK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<RefMemcpyLib4at_uC13~~~C47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthC47Corelib5Lists7ListDef6firstnC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExec6wbytesC13~~~C46Stdlib5Lists4List:firstn_allC56Stdlib6ZArith6BinInt1Z6to_natc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SumsLib4memkC13~~~I47Corelib4Init9Datatypes3nat00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9u64_rangeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~C47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<RefMemcpyLib3subC13~~~C47Corelib4Init5Peano2ltC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<RefMemcpyLib7sub_nthC13~~~C47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<RefMemcpyLib7rdn_subC13~~~C47Corelib4Init3Nat3minI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3minC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List=length_firstnC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExec>rdn_wbytes_outC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SumsLib2b_C13~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC46Stdlib9micromega8ZifyInst7Inj_Z_ZC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<RefMemcpyLib;store_ok_atC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<RefMemcpyLib>wbytes_extend'C13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr06K47Corelib4Init9Datatypes4prod01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SumsLib7rd_src1C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5Hoare7at_addiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8step_lbuC13~~~K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5instr07I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SumsLib6wr_dstC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim:step_sb_atC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SumsLib<memk_extend1C13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8u8_rangeC13~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib5Lists7ListDef6repeatc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SumsLib5msetkC13~~~C47Corelib4Init9Datatypes3appC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<RefMemcpyLib:wbytes_appC13~~~C46Stdlib5Lists4List:repeat_appc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SumsLib<msetk_extendC13~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1ZAmul_pow2_bits_lowC46Stdlib4Bool4Bool<andb_false_rC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec>Z_testbit_highC13~~~C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z4lxorc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SumsLibAland_shl_disjointC13~~~C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lxor_lorC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_slliC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SumsLib@lor_shl_disjointC13~~~K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr05C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4v_orC13~~~C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz07C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7mul_1_rC46Stdlib6ZArith4ZdivAZmult_mod_idemp_rC56Stdlib6ZArith6BinInt1Z7add_0_rK46Stdlib9micromega7EnvRing3Pol03C56Stdlib6ZArith6BinInt1Z9div_smallK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z9div_add_lC47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC47Corelib7Classes?RelationClasses;reflexivityC56Stdlib6ZArith6BinInt1Z6shiftrK46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02C56Stdlib6ZArith6BinInt1Z;le_preorderc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SumsLib2M8C13~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SumsLib8M8_digitC13~~~C47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC56Stdlib6ZArith6BinInt1Z=shiftr_shiftrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SumsLib;byte_eq_modC13~~~C56Stdlib6ZArith6BinInt1Z7mod_modK4ELinuxProcessSemantics5Riscv5Instr5instr0:K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6regupdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7step_orC13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K4ELinuxProcessSemantics5Riscv5Instr5aluop09K47Corelib4Init5Logic4True01".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint code_at (segs : list Segment) (base : word) (off : Z) (ws : list (bv 32)) : Prop :=
  match ws with
  | [] => True
  | w :: ws' => fetch_word segs (at_ base off) = Some w /\ code_at segs base (off + 4)%Z ws'
  end.
End FPX_1.


(* [comment removed for export] *)
Ltac code_at_vm :=
  cbn [code_at Z.add Pos.add Pos.succ];
  repeat split;
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Ltac zlit_at :=
  repeat match goal with
  | |- context [at_ ?b (?x + ?y)%Z] =>
      is_Z_lit x; is_Z_lit y;
      let z := eval cbv in (x + y)%Z in change (at_ b (x + y)%Z) with (at_ b z)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac fold_at_vars :=
  repeat match goal with
         | |- context [v_addi ?b ?e] => is_var b; change (v_addi b e) with (at_ b e)
         end.

(* [comment removed for export] *)
Ltac vn :=
  gres; rwH; imm_norm; unfold btgt;
  rewrite ?at_addi; rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l;
  fold_at_vars; rewrite ?at_addi; zlit_at; vals_lit.
Ltac pcn := vn.

(* [comment removed for export] *)
Ltac an F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vn
  | _ => stepi F D; vn
  end.

(* [comment removed for export] *)
Ltac av F D v tac := stepiv F D v ltac:(gres; rwH; imm_norm; tac); vn.

(* [comment removed for export] *)
Ltac ab_tk F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
    end;
    [ exact F | reflexivity | exact D | gres; rwH; imm_norm; tac ]
  | step_simpl; vn ].

Ltac ab_ft F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
    end;
    [ exact F | reflexivity | exact D | gres; rwH; imm_norm; tac ]
  | step_simpl; vn ].

(* [comment removed for export] *)
Ltac aret F D k :=
  stepjr F D k ltac:(gres; rwH; reflexivity);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      end.

(* [comment removed for export] *)
Ltac condz :=
  rwH; unfold at_, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; unorm; lia.

(* [comment removed for export] *)
Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia).
Section FPX_2. Context {fx : PropExec.FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma at_fold : forall (a : word) d, Z_to_bv 64 (bv_unsigned a + d) = at_ a d.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"] "h01ah11dp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210p1001:p4p710R1p8p1001Xp4p710P1p8p10027p4p710P1p8g002Yj10Tg003>j14Tg003\j12Tg004?j21Tg005Cj23Tg005]#0#0#0#0#0#0#4#2R1g006Bf1f0'1,31W1W0o"). Qed.

Lemma v_add_at : forall (a : word) z, (0 <= z < 2 ^ 64)%Z -> v_add a (Z_to_bv 64 z) = at_ a z.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"] "h04__p1h14__x1h22Hah37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with91zh:2Hzh;1ap;1p;2p;3p;4p;6p;7p;8g002Yj10Tg003>j1XTg003\j1FTg006`j1>Tg007>j2OTg007[j22Tg0087j26Tg008Rj25Tg009<j24Tg009Yj23Tg00:?j37Tg005Cj2=Tg00:Yj2WTg00;Aj3UTg00;ej1TTg00<Ej1NTg00<ej2LTg00=Cj1KTg00=aj1HTg00>Lj2;Tg00>oj2GTg00?Rj4:Tg00@=j6ETg00@aj1DTg00ACj2CTg00Aej2ITg00BQj3JTg00C0j4BTg00Cbj3ATg00DEj3MTg001:j6@Tg00ENj2PTg004?j2QTg00FWj2?Tg00G3j7RTg00GWj7STg00H;j8VTg00H_R0f0R1'?p=1f1R2g00I=R3g00I\R4P4g00J<R5P1g00J\FRp=8f2R6P3P4P4P5P2P1FSp=9f3R7P3P4P4P5P6P2P1GVp=<g005]R8#0R9#0#0#0#0#0R:#XR;#FR<g006BR=%11R>%>9R9%>:R:'OR?,21R@'6P=P215;7RA/41,3;14A6,3;57<X9=15;6/42,3;,=<13;2RA,5;1W9:RB1209%1:120?[[RC%19RDg00K<REAU9:2UW2R:%1?\E^2DRDp-0REg00KXRF#TRG%NFRF1L=2RH%K=RI%H=RJP=1;=0g00LD1G=8R8C:,8JRKPJP3P4P4P5P7EER359J%D4R4PKC<1CJ5R5P1P6g00LkRKg00MKRL'=1I16=7KLdAJ=02CBR0b4b7b8X1=W016>2%12[^1=^0EP1f4R>/2?P>P7O3b3b5b6PBPCP:PDPGPFPHPIPJP=P8g00Mk1;=9=A=;C:,8JR;99J3P4P;C<P5P0b4b7b8X1=X0E162@122?[^1=^0EP1%1>P>P7O3b3b5b65M2E@1P6A1Q6257<eW:W9W;o"). Qed.

Lemma at_eq_u : forall (a : word) d e,
  (0 <= bv_unsigned a + d < 2 ^ 64)%Z -> (0 <= bv_unsigned a + e < 2 ^ 64)%Z ->
  at_ a d = at_ a e -> d = e.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"] "h04__x1h14__x2h27__arithh36__sat0h46__sat1h51Hh64__p1h74__ffh88__varmaph95__with:2Hah;4__x3h<1zh=2Hdh>2Heh?1ah@1dhA1ep;1p;2p;3p;6p;4p;7p;8g002Yj16Tg003>j1eTg003\j1NTg008Rj20j1FTg009<j21Tg006`j1ATg007>j2MTg007[j23Tg0087j27Tg004?j25Tg00:?j3<Tg00NRj6dTg00:Yj2XTg00;Aj3WTg00;ej1UTg00<Ej1TTg00<ej2@Tg00Noj1OTg00OMj4BTg00=Cj1LTg00=aj1KTg00>Lj2>Tg00>oj2;Tg00Okj3:Tg00?Rj48Tg00@=j6JTg00@aj1ITg00ACj2HTg005Cj2GTg00Aej2PTg00BQj3QTg00C0j4RTg00Cbj3STg00PNj4CTg00QZj6ETg00R6j1cTg00RTj2bTg00S5j1]Tg00STj2DTg00T=j3\Tg00Tfj3YTg00UOj2ZTg00V;j3[Tg00V[j1VTg00FWj2^Tg00G3j7_Tg00GWj7`Tg00H;j8aTg00H_R0f0R1'^p=2g006BR2f1R3;<1p=4P3g00I=R4g00I\R5P5g00J<R6P1g00J\F_p=9f2R7P4P5P5P6P3P1F`p=?f3R8P4P5P5P6P7P3P1Gap==g005]R9#6R:#6#6#6#6#6R;#eR<#NR=10<7/13R>#2%A:R?%A;R;'MR@,3>'710<8/13R>#213>@'7f4R>/5815>75<=P=P2%F<f5R=/5>RA15=8RBP1Ed10<A10<B'4P2f6RB/5=,0<f7RA/5=,0<RC,41X<2P110<B/1=RDPBP=1X?;RE130?%2;130@[[RF%2?RGg00K<RHAW?;3UW:R;%2@\H^:GRGp-0RHg00KXRI#URJ%TIRKP21@27RLP3%O2CBRM%L2RN%K2ROP21>20g00LD1;29RP1;2:R:5:2RQC8,9ORRPOP4P5P5P6P>EJR45?O%I5R5PRC=1HO6R6P1P7g00LkRRg00MKRS'G1P17=<RSdAQ203CRR0b7b8b9X02X12W6RS1113RR#2/771137RT#2[^02^12^6HRUP1f9RV,0<RWf8RX'1RY/3@PXPWPBO4b2b3b4PEPFP;PGPJPKPMPNPOP2PQg00Mk1>2?=S2<C8,9OR?9?O4P5P?C=P6P0b7b8b9X02X12X6HR?13R@,7713T@[^02^12^6HRHP1%2YPXPWPBO4b2b3b4CCEE15B>,0<,4DP2PC10<X/1A/41X<2P110<ARC/1=RDPAP=PEPFP;PGPSPUP1f:RU,0<RS/1XR=/3@PXPSPBO4b2b3b4PEPFP;PGP?PHP1%2=PXPSPBO4b2b3b4CCEE11CB/4DPEPFP;PG%c9,b2g00W@RG#],D25\21D2G5Y2g00W_'Z=[IJPKP2PLP31@28CBPNPOP2%V9,;2R9=:2Pg00XKRNA:29:C8,9OP5P2PPPNP:C8,9OC=P6P0b7b8b9X02X12X;211711173'41437[^02^12^;2P1f;,0<PVPUP8O4b2b3b4b5b5b5W5W>W=XA2X@2W?o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record cpyH (segs : list Segment) (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := CPYH {
  cHn : (0 <= n)%Z;
  cHlen : length bs = Z.to_nat n;
  cHsrc : rdn segs mem0 src (length bs) = Some bs;
  cHdst : store_ok segs mem0 dst (length bs) = true;
  cHdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
  cHnws : (bv_unsigned src + n < 2 ^ 64)%Z;
  cHnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.

Section MEMK.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Hypothesis HOK : cpyH segs mem0 dst src n bs.

  Let Hn := cHn _ _ _ _ _ _ HOK.
  Let Hlen := cHlen _ _ _ _ _ _ HOK.
  Let Hsrc := cHsrc _ _ _ _ _ _ HOK.
  Let Hdst := cHdst _ _ _ _ _ _ HOK.
  Let Hdisj := cHdisj _ _ _ _ _ _ HOK.
  Let Hnws := cHnws _ _ _ _ _ _ HOK.
  Let Hnwd := cHnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Definition memk (k : Z) : word -> option byte := wbytes mem0 dst (firstn (Z.to_nat k) bs).
  (* [comment removed for export] *)
  Definition b_ (j : Z) : byte := nth (Z.to_nat j) bs (Z_to_bv 8 0).

  Lemma memk_0 : memk 0 = mem0.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"; "MEMK"] "p;1p;2g002Yj10Tg003>j12Tg003\j11Tg00Y2j13Tg005Cj24Tg005]#0#0#0R0#0#0#0#2#1%20#1#3[p,4mem0'4o"). Qed.

  Lemma memk_n : memk n = wbytes mem0 dst bs.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"; "MEMK"] "h01lh11np;1p;2p;3p;6g002Yj10Tg003>j15Tg003\j13Tg00YTj26Tg00Y2j1>Tg00Z4j34Tg00ZSj32Tg00:?j31Tg00<Ej1;Tg005Cj2:Tg00[\j27Tg001:j68Tg00\;j19Tg00QZj6=Tg00\[j1<Tg00]bR0g005]#0#0#0R1#5#3R2p,2bsR3'6R4%01#0#0#5#3%>2[R1p,4mem0R5p,3dstR6f0R7=42332A2563R831X10%;2R0P3A2567=118X001:18A42431723E8p,1nR3#9p,4HlenE=%<3=118eo"). Qed.

  Lemma rd_src1 : forall k j,
      (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
      rdn segs (memk k) (at_ src j) 1 = Some [b_ j].
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"; "MEMK"] "h04__x1h14__x2h24__x3h34__p1h44__x4h54__p2h62H2h75Hlen0h87__arithh94__ffh:8__varmaph;5__with<4cstrh=2z2h>1nh?6__sat4h@1xhA2H3hB6__sat5hC2z3hD4__p3hE4__x5hF4__x6hG4__x7hH6__sat3hI1yhJ2H4hK2HahL4__p4hM6__sat6hN4__x8hO1ohP1zhQ2z4hR1HhS2H0hT2H1hU2HjhV2HkhW1bhX1jhY1khZ1lh[1mp%0p&0p;2p;1p;4p;3p;<p;8p;6p;9p;7p;Bg00FWR0j20Tg0087j22Tg006`j1kTg009<R1j21Tg00^Ak109Tg002Yj1PTg003>k103Tg008Rj2cTg007>k20JTg007[R2j23Tg003\j1xTg00<Ek101Tg00Y2k10jTg004?j2^k10YTg00S5j1ATg00_Nj4]Tg00\;R3j1gTg009Yk20]Tg00`Uk406Tg00;ek105Tg00V;j3NTg00a1j2[Tg00:?j38j1}Tg00aSR4j1BTg005Cj2bTg00b3j1{Tg00bQl<\Tg00YTk200Tg00c6k20?Tg00cYk30>Tg00d6k40<Tg00d]k10;Tg00eBj2vTg00:Yk20aTg00;Ak30`Tg00R6k10_Tg00RTk20^Tg00T=j3rTg00STk208Tg00=Ck10\Tg00=ak10[Tg00>Lj2qTg00>ok204Tg00@ak10ZTg00V[j1dTg00ACk20XTg00Aek20WTg00BQk30QTg00C0k40PTg00edj4UTg00fOk80OTg00flk40NTg00h7R5j2~Tg00Nok10ITg00hOk30HTg001:j6STg00i^j2zTg00j5R6j2yTg00jOm90ETg00QZk60DTg00Z4k30CTg00ZSk30BTg00k^j2`Tg00l5j2;Tg00lOR7j2oTg00llk40ATg00mOk60KTg00n7k20LTg00Cbk30STg00PNk40TTg00nYk30UTg00o;m90iTg00\[k10hTg010Lk10gTg011Qk20fTg011nm<0:Tg00Tfj3hTg00UOj2tTg00<ek20eTg00OMk40dTg00?Rj4ZTg00G3j7_Tg00GWj7iTg00Okk30bTg00H;j8fTg012Sj7sTg00@=k60cTg0137lBuTg00H_R8f0R9'0p=5g006BR:f1R;;89p=M20f89p=I1b:9p=?P:g00]bR<P:P:P3f4R3P4f3R=g013]f2R>P;P9N<0:p=mP<P:P:P:P4P4f5R?P3P=P>P;P9N<0:p=l1389p=C1098p=LA8:98p=KA8:>;,2=/;9p==208:9p=@Ah:;9p=9Ah:;9g00W_R@'tp=G1t9@p>07g00KXRAANA;97N>p=J1t;@=NA9p=<20e:9p=QP:P>P;P9H0dp=6204:9p=EP:P;g00MkR@P9CZp=pP>g00I=RBg00I\RCPCg00J<RDP:P;g00XKREP9CZg00J\RFF_p=RP=PBPCPCPDP>PBPCPCPDP;PFF_P9Fip=OP:P;g00LDRGP9CZp=eB0b:;9p=:P>PBPCPCPDP:P;PGP9CZPFF_p=4f6RGPBPCPCPDP?P3P=PBPCPCPDP>P;P9GfGfp=7P?PBPCPCPDP3PBPCPCPDP=P>FsP;P9Gfp=HP<P:P5P4P2g014JP?P3P=P>P;P9M<\p>0MAh:;99h:>p=DANA;9p=nP>PBPCPCPDP:P;P@P9CZPFF_p=FP;PBPCPCPDP9J0cp=XP>PBPCPCPDP;P9Fip=YP3PBPCPCPDP=PBPCPCPDP>P;FiP9Fsp=|11>;/09p=>P<P3P=P>P;P9ESp=TP<P<P<P:P:P:g014lP4P4P4P1g015LP?P3P=P>P;P9MBup>0GP<P:P6P4P0g015oP?P3P=P>P;P9M<\p>0FP:P:P:P:P:P:P1P9P;P>P1P=P3P?PGf7R1f8R6f9R@MBup=wP:P:P0P1P0PGP?P3P=P>P;P9M<\p=aP<P<P<P:P:P:g016QP4P4P4P7g0171P?P3P=P>P;P9MBup>0@A8:;9,2>p=jP:P;PEP9CZp=VP=PBPCPCPDP>P;PBPCPCPDP9PFF_Fip=WP>PBPCPCPDP;P9Fsp>0=12;9,;>p>0212=>12;9';p>0RP=PBPCPCPDP>P;P9Gfp>0V%5;S00p,1nRB,0;'2Q00g005]RF#kRE,1>R7/0Bp,3srcR0$09%PFR2#PR5#PRH#P#P#PRI$03RJ/c0RK#5S01%k2RL%kIRI+0JRM,3KS02'2p,3dstRN$091cJNRO#5S0313OMS04'2&03HRP#xRQ$01RR$0jRSp,4segsRTp,4mem0RU1^0?RVg00W@RW#ARXC]PQ%gGRYp,2bsRZ20]P8RPH06&05QS055NQS06,[RS0798S9XOSP:%xJR[&0Y0R\P\%g?R]#BR^P?P[\:/b\1M^?%I?R\/M?P:P:%}:R_P9X@:R`P_1M;9#{XI:X@:P^P\P`P`%B9Ra#?X@<S08P]P\P`%I9X@:R\P?P?%??R]DmElP?P?P]M<\200QZR]%gBRb58<%B]Rc%IBRd'MReP<P:%}<P4P_%B;/MaA8<;920?;940>XI<X@<P]Pc%?cPbP\PBO1P`P\PBPB%?BDmR_M<\p,4HlenS09H0<R4Pe&0;]Rf%5cRc1v81%C1%I1RgP1%L1%Kg'2C=%I6P:1v8BRg%CBS0:PdPB%LBS0;%Kd'2C=RhPdP:20aLIRi%CL%5I%CM[[Rj%5LRkg00K<RlB0`LI;UWKRI%5M\l^KkRk%AXRl#ARm#ARn#@S0<&0_F-0^:Ro%@mRm5r:S0=208:WRW'9Rp'9Rq%@XRr/9WRs,GmS0>&07p&05ARp3J'<&01ARA%Q>Rt%Q=S0?76;&0\:Ru&0[:RvPvPvPv1q:8Rw%E2Rx'p204:FRy=RvxRzCOPvPv1exwARvywR{CO&0ZCRCPv1q:ER|,:xS0@%dFRF#ER}54vS0APCPvA4vwxS0BPCPzF7EH20XvDRDP9P>g00LkRzg00MKR~'b20W9>=8z~dB0Q:8;H0PR~b9b:b;X0:X1:X2:%C;P9P;%L;%K9Rz'2C=107=S0C%5=1M=3[[[^0:^1:^2:P9PBf>S0DP?PGf;R7f<S0EO6b8b?bBbCbAb=b6b<b7CUL0O1^0^=8[VP[%BY,^0S0FPTPUP9PXC]PQ%g1R^PZPPH06Q055NQ,[RRP58SXW[PSPQPZPYPXH0NR[,[RA8S9PXOSPRQ061[R9=8SPXZRQ07,bSP[Pb1~^9X><1~Yb%IGR[/3dPYP[P`P\PGPG%?GDmS07PbPdP_J0MP4PePfPcPgPhPdP:f:R\,v8S06%C\%I\R8P\%L\%K8'2C=S0G%I7S0HP:PiPjPIPkp-0R8%@lRl/9rRr,GmRP%AnS0I#@Rn/GqQ0=19lWRl5Dn1nPp'<3JS0=PA&0I:RP%Q3S0J76=96t;S0KPuPvPvPv%dF#ERt9FvwARvyt1XvGRq=Yv{D|S0LPCPvPvPvAFvw}S0MARvx}PvPv1e}w1Xv1COS0ND|S0OPCPv1:t|=4v}S0PPCPvA4vwtS0QPCAFvyxF7F7PDP~b9b:b;X0:X1:X2:X4:X38W5%C=RtP9P=123zC=S0RPtP>P=%L=/2GC=RtA>?E3Rz%5GR{133?[[[[^0:^1:^2:^4:^38^58P9%K?f?S0S#LQ0SPBP?P=P3PGQ0Ef=S0SO:S0Tb8b?bBbCbAb=b6b<b7CUP]Q09DT:0HZYESPTPUQ0FPXC]PTPUP]P0PZPYPXp,4HsrcPb1z^X/y9X><1zYXS0F/yb11[ES0U/0dQ0FQ0UPYP[Q07PXPE%?ES0UJ0GPbPdP_J0FP4PePfPcPgPhPdP:Q06Q0GQ0HP:PiPjPIPkQ0=PAQ0KPuPvQ0LPCPvQ0OPCPvQ0PPCPvQ0QPC1:y|=4vxF7F7PDP~b9b:b;X0:X1:X2:X4:X38X58Q0R113ES0Q/0?S0P\{\z\t[^0:^1:^2:^4:^38^58Q0Tb8b?bBbCbAb=b6b<b7CUP]Q09DTN90EES1^0GRtP9J0Db6PTB0CQYZS0T:0BUNPVPXC]PTQ0TPUPNPVPX1`Y]S0R1cJtRt%BXRN;>ORU11OaS0O/0t';X><Pb1`^9#B,1OS0L/0t,;UX><P:11K?RU119NS0K/0O1`^b#B=>O9';XP:11UNR^/0OS0=1`YbS0F#BS0V,1ORt/0US0W';S0X11UERa/0OS0Y1o[dRz,1OR{/0US0Z';Q0=Q0WQ0YQ0ZP`10;9#{XI:X@:S0ZP^PaP`P`P`P:P:g017T11;9H0A#?X[:X>:S0YPUPU%?US0WPNPEP`P`Q08PXPEQ0UElM:wS0UPOPO%?ORNGaP`Q0ZPtP{P`P`P`Q0YPOPOPNQ0VPzP`P`Q08Q0FPzPYP[Q07PbPdP_J0@ElM:wS07PUPUQ0WGaJ0KP4PePfPcPgPhPdP:Q06Q0GQ0HP:20L9>S0W139>1o9>R_P910>9?j_>C=S0F1o;=S08P:PiPjPIPkQ0I#AR_#AR[#@Rz19nsS0I'GS0VQ0V%A[S0Y#AS0=#@R[%@_R_Ar:on5Dz'GS0[Q0[Q0</GrRNADnmlS0<,9[S0\$07Q0Y#@RmQ0I'GS0IQ0IAr:o_=Dzn,G[Q0=#A#@Q0\'9Q0<9D[mADz_s1nNp'<'<9JNN'<5JN3J3J3J3JPA%Q1S0V?63P%QGS0[76>%Q6?6?P?6=P76;PuPvPvPv%d5#ERN%EHRH5FvS0IPv%E5R5/VNCWPvA4vHNS0<Pv1V5HCWPCPvPvPvPv%PF#ERF,pwARvNFCOPv1Xv\S0\Pv1VNwCWPCPvPvPvPv%d2#ER2,pwARvH2CO1Xv7S0=ARvHwS0Y5YvPCPvQ0@=4v2PCPvQ0BPCPvPv1:}2=4vy1:y2=4v}PC1:yxR2/:|Rs=4v}1:}5=4v260=vEHF7EHEHEHPDP~b9b:b;X0:X1:X2:X4:XE:XF:XG:XN:X38X58131GP=P110G1?j=GC=%CG?j6GR[%K6Ro802@B02[7oQ0Q/01%5?RoA>1@?A>?@1';11G1R[?>E6A>6@[';[[[[[[^0:^1:^2:^4:^E:^F:^G:^N:^38^58P9Q0;fAR[#LP?P1P[PBP=POf@S0QPKP3PGP6Q0SQ0Dp,5HdisjO@b8bBbMbQbJbCbAb=b6b<b7CUQ0Xe1cJVS0XP0P?P4PePfPcPgPhPdP:PiPjPIPk19nrQ0>/npRr'<PAQ0J?6>PQ0?76;RVPuPvPvQ0M=YvqQ0NPCPvPvPv1ew51Xv6COPCPvPvPv1ewy1Xv@S0NCOPCPvQ0APCPvQ0BPCA4vw2F7F7EHPDP~b9b:b;X0:X1:X2:X4:X38X58XD8XL8%C>P3%L>P?H0R%53/21%5>/2@Q0P11?G#5\o[[[[^0:^1:^2:^4:^38^58^D8^L8P9Q02Q04%K=1M=BPOPBQ0EPKP3P1P6P@P\O=b8bHb?b=b6b<b7%5UeP4PePfPcPgPhPdP:PiPjPIPkPrPAPVPuPv1q:L>0S:JRJ9FvyRL9YvqS04PCPvQ0APCPv1:5}=FvJR5PCPv1:y}=FvJRyPCAFv2JF7F7PDP~b9b:b;X0:X1:X2:X4:X38139M,23RqQ0C11?3/3MR\11=?/3MRo113?R[/3M[[[[^0:^1:^2:^4:^38P9Q01POPBQ0EPKP6P@p,4HnwdS0Ep,4HnwsS01O9S02b8bHb?b=b6b<b713UMeH0TS0PESP]Q09DTQ0T-00QS0TB0UQYZRZDTP:PUQ0K/0MXP:10^MRU10aMP`Q0ZP^PaQ0UPMPM%?MRaGaP4PePfPcPgPhPdP:PiPjPIPkPrPAPVPuPvQ04PCPvQ0APCPvP5PCPvPyPCA4vsJF7F7PDP~b9b:b;X0:X1:X2:X4:X38Q0CA>[EM\o\\[\q^0:^1:^2:^4:^38Q02b8bHb?b=b6b<b7CUPUeQ0XQ0PESQ0RQ0O/0MX><PbQ0L/0MX><10tM10{MP`Q0ZPtP{Q07PMPMPaGaP4PePfPcPgPhPdP:Q06Q0GQ0HP:Q0WQ0FQ08P:PiPjPIPk19nW9Dz_RnADz_lR_19m_19mn/<p'<'<'<PAQ0[?63P%Q?76>Q0V?61P?6=P76;PuPvPvPvQ0IPv1VxNCWPvQ0<Pv1VxHCWPCPvPvPvQ0NPv1VH}CWQ0\Q0Y5YvPCPvQ0==YvLPCPv1:F|=4v}PCPvA4vwFPCPvPyPCPvP5PCA4v2JH0VF7F7EHEHPDP~b9b:b;X0:X1:X2:X4:XE:XF:XG:X38X58XD813G?P;PG10?G?j;?C=P6PGP=%KG,2@C=13>M,27A>1E?%5611?1/3M11@6/3MA>16M[[[[[[[^0:^1:^2:^4:^E:^F:^G:^38^58^D8P9Q03Q0;Q0:P?P1Q0QPKPBP=POP3P6P7Q0SQ0DQ0EQ01OAb8bBbMbQbJbCbAb=b6b<b7CUP]Q09DTQ0TPZDTN90iESbSbRPT&0h31^0=PXC]&0g=Q055NQ,[R58SeWTWUWVXX:XY:o"). Qed.

  Lemma wr_dst : forall k j m,
      (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      store_ok segs (memk k) (at_ dst j) m = true.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"; "MEMK"] "h01xh14__p1h24__x1h34__x2h44__x3h54__x4h61nh72H1h82Hah95Hlen0h:7__arithh;4__ffh<6__sat2h=6__sat3h>8__varmaph?5__with@4cstrhA5cstr0hB1mhC1yhD2z1hE2HjhF2HmhG1jhH1kp&0p;1p;2p;3p;4p;<p;6p;;p;Bp;7p;8g00aSR0j14Tg009<R1j22Tg00FWR2j20Tg002Yj1;Tg003>j1TTg003\j1oTg00YTj2hTg00\;R3j1LTg00Z4j3_Tg008Rj2KTg006`j1JTg007>j2[Tg011Qj2YTg00b3k102Tg00llj4~Tg00:?j33j1OTg00c6j2eTg00cYj3dTg00bQl<MTg00d6j4aTg00d]j1ITg00eBj2^Tg007[j2:Tg0087j29Tg00l5j2ETg00:Yj2]Tg00;Aj3\Tg00S5j1ATg00STj2=Tg00UOj2BTg00;ej1ZTg00V;j3CTg00<Ek103Tg00<ej2XTg00Nok101Tg00OMj4VTg00=Ck100Tg00=aj1}Tg00>Lj2UTg00V[j1yTg00>oj2?Tg00@=j6wTg00@aj1pTg00Okj3FTg00Cbj3mTg00ACj2jTg005Cj2QTg00Aej2kTg00BQj3iTg00C0j4lTg00edj4STg001:j6NTg00R6j1gTg00RTj2fTg00T=j3rTg0188l;sTg00\[j1tTg004?j2uTg019Kj4vTg011nl<WTg0137lBcTg00Tfj3bTg00?Rj4GTg00G3j7zTg00GWj7{Tg012Sj7|Tg00H;j8`Tg00H_R4f0R5'0p=7g006BR6/Q5p=6P6g00]bR7P6P6P3f4R3P0f3R8g013]f2R9f1R:P5M<Wp=xP7P6P6P6P0P0f5R;P3P8P9P:P5M<Wp=qP6P6P6P6P6P6P1P5P:P9P1P8P3P;f6R1f7R<f8R=f9MBcp=nP6P6P2P<P2P1P;P3P8P9P:P5M<Mp=PA3654p=DAb6:5p=5P6P:g00MkP5CGp=HP:g00I=R2g00I\R<P<g00J<R>P5g00J\Fzp=1P6P:g00XKP5CGp=>P9P2P<P<P>P:P5F{p=@P9P2P<P<P>P:P5F|p=RP6P:g00LDP5CGp=<P8P2P<P<P>P9P:P5G`p=8%7:%4:R?,29p,1nR@'0p,4segsRAp,4mem0p,3dstRBg005]RC#;RD#;RE#;RF#T#oRGp,2bsRH'hRI%L3=_GHP8P9P7%L@RH%;F#;#;RF#TRG/KBRJ%45RK'2%JDRL%JFRF'[RM'0X67%4HRN,2JRO/0M1Y4@RP,2JRQ/0MP5X06RR10:5$02XC6X06RSPOPQPRPRPRP6P6g017T12:5C~#6XB6X66PJPJ%6JPNPPPRPR%6KX07PHPPPR1Y45X06RQP@P@%6@DxROEqRTM:nPMPM%6MGPA37IH%4IRU=36PRVP7P6%O7P0%O6A36?KA37:51e:53dXC7X07PIPU%6UPHPQP@O1POM<Mp,4HlenROCaRQPV%IIR?%7URU%I3R0%43#7RW1^4@RX1:4@RYA36P@'910@4RZ%DP'9'ER[PPP61]LFR\1:4L%7F1:4M[[R]%7LR^g00K<R_A\LF:UW8RF%7M\_^8^R^p-0R_g00KXR`g00W@Ra#ARb#ARc#ARd#A,=6Re1=6dRd1=6b1=6aRa'5Rb'5'5g00W_Rf'B15da,5e/Bf%Z`Re5C`3C&03`RaP6P61X63P9&016CVP:1X68CVRg&006Rh%}6Ri1U64Rj%yC,?6Rk'H,1i1?6DRD/>k,1i5@iPiP2P<P<P>P1EwR11>Dj,1i5@i5Ri%p<R<Pi1?6CR2=F6k1U6L=m6GRL'H,1iP<Pi1?6ERE=F6k/HL,1iP<Pi1<jk,1iP<AF62DR2/<L,1iC8C8C8C81ji>R>P5P9g00LkRLg00MKRD'Q1k59=3LDdAi64:ClRlb;b>b?X26X36X46X56W11:49A36:9'9%D:,93'E12:8/:M12;3/:M%7;123;/0M[[[[^26^36^46^56^1_P5PZp,3src,KGP@P8PJP3p,4Hnwdp,4Hnwsp,2HnO9b:b<b=bDb7bAb@b9CSPIPOENp,4HdstP:P7PH%48,23/0KX67%49,28RK/0N10KPPRPSPKPK%6KPNPPPTGPPQPVP?PUP0PWPXP[PPP6P\P]PFP^%gC,f61=6c5r6/5bRb,5d/Bf1Bbf=C`e5C`PaPgPhPi1>kE,1i9@i11<Ej,1i1>kj,1i5@i5RiP<Pi1<2E,1iP<1<2k,1iC8C8P>Plb;b>b?X26X36X46X56X1_A3698,931084%D9'9'E12:9/031298/03[[^26^36^46^56^1_P5PYP@P8f:#4f;P3P=O7b:b<b=bDb7bAb@b9CSPIPOENM;sPA%t31uB8P9Cv=3LDeWFWEXB7XG6XH6o"). Qed.

  Lemma memk_extend1 : forall k,
      (0 <= k)%Z -> (k + 1 <= n)%Z ->
      wbytes (memk k) (at_ dst k) [b_ k] = memk (k + 1).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"; "MEMK"] "h04__x1h14__x2h24__x3h34__p1h44__x4h51xh62H2h72H3h85Hlen0h97__arithh:4__ffh;4__p2h<6__sat5h=8__varmaph>5__with?4cstrh@2z2hA2z3hB6__sat4hC2HahD1nhE1yhF1HhG2H1hH2H4hI2HkhJ6__sat6hK1bhL1khM1lhN1ohO2z4p%0p&0p;1p;2p;<p;3p;4p;8p;6p;7p;Bg006`j1\Tg009<R0j2?Tg00FWR1j2<Tg002Yj1BTg003>j1mTg003\j1kTg004?k10?j2KTg00\;R2j1DTg00aSR3j1ETg005Cj2HTg00:?j1sj31Tg00b3k10PTg00bQl<OTg00YTk20JTg00c6k20FTg00cYk30>Tg00d6k40<Tg00d]k10:Tg00eBj2PTg00:Yj2{Tg007>j2zTg00;Aj3yTg00S5j1GTg00R6j1uTg00RTj2tTg00T=j3_Tg00STj2rTg00;ej1qTg00<Ej1pTg00<ej2^Tg00OMj4]Tg00=Ck10OTg00=ak10NTg00>Lj2nTg00>oj2QTg00@ak10KTg00Okj3ZTg00V[k10ITg00ACk20GTg00Aek20ETg00BQk30DTg00C0k40CTg00edj4RTg00fOj8VTg00Y2k10=Tg00Z4j3Jj2ck105Tg00ZSj38k207Tg009Yk20;Tg00`Uj4dTg00V;j3;Tg00flk409Tg00i^k208Tg00Nok103Tg00j5R4j2eTg001:j6XTg01:Kj6~Tg00h7R5j2fTg007[R6j2WTg00hOj3|Tg00QZj6`Tg00\[j1iTg010Lk10@Tg011Qk20ATg011nl<lTg0087j2oTg00l5k20BTg00Tfj3xTg00UOj2hTg00?Rj4TTg00G3j7YTg00GWj7jTg012Sj7wTg00H;j8[Tg0137lBvTg00@=k60MTg00H_R7f0R8'<p=@g006BR9f1R:;18p=920A78p=21H98p=CP9g00]bR;P9P9P2f4R2P3f3R<g013]f2R=P:P8M<lp=UP;P9P9P9P3P3f5R>P2P<P=P:P8M<lp>0LP;P9P8P3P:P=P<P2P>f6R?f7R@f8RAM<Op=g1W78p=4A19:8,o=p=51<87p=:A1987p=A1o:8-0B=p=31r98p=IAx9:8p=0g00KXRBg00W_RC,h:;;8p=7P9P:g00MkP8CTp=LP9P:g00XKP8CTp=FP:g00I=RDg00I\REPEg00J<RFP8g00J\RGFYp==P<PDPEPEPFP=PDPEPEPFP:PGFYP8Fjp=6P9P:g00LDRHP8CTp=SP=PDPEPEPFP:P8Fwp=MP=PDPEPEPFP9P:PHP8CTPGFYp=NP<PDPEPEPFP=P:P8G[p>0HP?PDPEPEPFP>P2P<PDPEPEPFP=P:P8G[G[p=>P;P;P;P9P9P9g014lP3P3P3P0g015LP>P2P<P=P:P8MBvp>04P:PDPEPEPFP8J0Mp=aP;P9P4P3P1g015oP>P2P<P=P:P8M<Op>021h8Cp=bA;B:8p>01A;B:89;B=p>00P=PDPEPEPFP:P8Fjp>06P;P9P5P3P6g014JP>P2P<P=P:P8M<Op=}%@8g005]R6#\R3,?:p,1nR5'<P9%B6RD#B#BRC#B#B#BR1#m#kR4p,3dstR0$0?RGPG%D=RH#ERIP=P4\9/HG19I=%2=RG/9=P9P9%s9RJP8X59RKPJ19:8$0PXE9X59PIPGPKPK%E8RL#CX5;PHPGPK%28X59RGP=P=%C=RHDUJ0LP=P=PHM<O%mCRC#kRHp,2bsRM+0JRN%D5RO51;%ENRP%25RQ'9RR%s;S00PJ%E:/9LA1;:820F:840>XE;X5;RLPNPP%CPPOPGP5O1PKPGP5P5%C5DURSM9gp,4HlenRTH0<RUPR&0:NRV%@PRP1P72%42%22RW;52%:2%AW33%2>P91P75RW%45?5Q5%:5%AQ33RXPQP9%\DRY%\1R1'{RZ%4Y%@11zY1R[#4[[R\%@YR]g00K<R^AyY1:UWCR1%@[\^^C]R]g00W@R^#GR[#GRY#GR_#GR`#I%u6,t9Ra%I_R_5_9Rb1r9^R^'0Rc'0Rd%I[Re/0^,0_%qBRf,7c'7'7%pBRBP91^9=P:1^9<RgC]&0O9Rh&0N9RiPiPi1n97Rj1Q9DRD'L1Q96Rk/FD,=iRlC6PiPi1SDj1Fkj,=iRmC65Mi&0KEREPi1n93Rn9Z9D&0I6R6,Q9Ro5NiPEPiANijDPEPlH0HF>20GiFRFP8P=g00LkRlg00MKRp'H20E8==1lpdB0D97:H0CRpb:b=b>X09X19X29%4:?58:%::%A8Rl331?=3Rq/<<%@<19<2[[[^09^19^29P8P5f;S01P>P?f9f:S02O6b9bBb<bAb7b@b6b?b8CRGV1K0I1K0=RI514P4%D<Rr#E,K0Rs&0=H\4Rtp,4mem0Ru%D2Rv=JHM780RwPHPvPM20;C7S03Cd%qHRC5;H7881?23Rx#D=JHM98u0Ry31XK4%pHR4PHPMPrP[H09Rz%Ev,K0=8w8=1tyXM4Pt208r[Rw=JHMR{98u0A1t8yXNtP4Pt207u0RyPyP{1?<3R{#DR|=JHMPt\4/HyP4P41cHw1cH|PMPMP;P4\4Ry&05HR}P}PwP|Py\;/H}A1;w|%2<R}/?3Ry%2{R~'9Q00PJPLPwPyPrP}PKPGP<P<%C<DURyP[P3%C3J04P|P~PKPGP{P{%C{DUM9gPUPRPVPP1?>3R{,P7%4{%2{RG;5{%:{%AG331??3#2P91P7@R7%4@%2@R3;5@%:@%A333R3%2ARGP9PWPXPQP9PZP\P1P]p-0RK%G`R`#IR~10ec'0%G`#IA_9a~10_^'0Ra'010~c/7f,7a'7'7PBP9P9&039P=1^92C]P:PgC]RgPhPiPiPi%B6,Q9R6,Lj1Fk6,=iC6R:PiPi1S6jPmC65MiPEPiPiPiAZ96nRa,Lj1FDa,=iC6PiPi1Saj1ai?RcC65MiPEPiANiaoRaPEPiANij6R6PEAZ9kn/FD,=iF>F>PFPpb:b=b>X09X19X29X49W3%4<Rn?58<R`%:<R|;3l%4x?5=x%:x;3>1<{2R{%@?Rw19x>[[[[^09^19^29^49^3KP8%A@f>P5P@P>P?PAf<RAf=O9b9b<bJbObHbAb7b@b6b?b8CRGV1H4MGVGVAJHrM98u0?8szPuP0PMPrP[P;PO1ev8XD;1erO1<}QPrP}PyPOPQPSJ02PUPRPVPPPWPXPQP9P7P3PGP9PZP\P1P]%IYRY/0e,0_#bR_10~d#b10Y^,0b,0~201_f'7400R_PBPgPhPiB06icm9Mi:R:PEPiPiPi1Ljo1FDo,=iC6PiPi1Soj1ai@C65MiR@PEPiPaPEPiP6PEANikDF>F>PFPpb:b=b>X09X19X29X49X3KX;KA3`2lR`A5n=<?3|?R|1<2>\w\{[[^09^19^29^49^3K^;KP8%A>%:APAP5P>P<P2P?Q02Q01O:R?b9bBb<bAb7b@b6b?b8CRPNPTEXE~EXPHPrPMQ03Cd=;HCP;PO1fv8XD;1frO1W}QPrP}PyPOPQPSE}PUPRPVPPPWPXPQP9P7P3PGP9PZP\P1P]P_PBPgPhPiP:PEPiP@PEPiPaPEPiP6PE1LkD,=iF>F>PFPpb:b=b>X09X19X29X49X3KX;K1W2>\w\{\|\`^09^19^29^49^3K^;KP?b9bBb<bAb7b@b6b?b8CRPNPTEX9|MrE`1K0<P8E`bF%i=&0@==;HC78I%iq51teWGWIXL9o"). Qed.

  (* [comment removed for export] *)
  Lemma mc_lbu : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
    RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned (b_ j)))) (v_addi pc 4) (memk k) rom).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"; "MEMK"] "h04__x1h14__x2h22H2h35Hlen0h47__arithh54__ffh66__sat3h76__sat4h88__varmaph95__with:4cstrh;1xh<2z2h=2Hah>1bh?2Hdh@2HehA2HfhB2HjhC3Hj0hD3Hj1hE2HkhF3HrshG3immhH1jhI2j0hJ1khK2pchL2rdhM4regshN3romhO2rshP1whQ1yhR1zp;1p;2p;3p;5p;4p;<p;7p;6p;?p;8g002Yj13Tg00V[j1PTg003>j16Tg003\j15Tg000Nj2xTg00Y2j18Tg01;aj2dTg00a1j2@Tg00:?j30j1ETg01<cj1[Tg01=cj2XTg01>Cj1VTg01?4j5QTg006`j1:Tg01?`j4rTg01@@j2MTg004?j29Tg01AHj2BTg009<j27Tg00FWj21Tg0087j24Tg00\[j1NTg010Lj1OTg00<Ej1ITg01B0j2HTg00S5j1\Tg00_Nj4<Tg00;ej1GTg00V;j3ZTg00YTj2YTg00\;R0j1WTg00aSR1j1;Tg011Qj2FTg00c6j2UTg00cYj3TTg005Cj2DTg00bQl<STg00d6j4wTg00d]j1vTg00eBj2uTg007[j2CTg00l5j2qTg00:Yj2pTg007>j2oTg00;Aj3nTg00<ej2JTg00Noj1jTg00OMj4iTg00=Cj1hTg00=aj1fTg00>Lj2LTg00>oj2KTg00GWj7eTg00@aj1cTg00ACj2gTg00Aej2bTg00BQj3kTg00C0j4lTg00Okj3aTg01C:j5mTg001:j6=Tg01DDj3`Tg01ELl?_Tg011nl<^Tg00?Rj4]Tg00G3j7sTg00H;j8tTg00H_R2f0R3'1p=2g006BR4g00]bR5P4P4P0f4R0P1f3R6g013]f2R7f1R8P3M<^p=RP4P8g00LDP3C]p=?P8g00I=R9g00I\R:P:g00J<R;P3g00J\Fsp=>P6P9P:P:P;P7P8P3Gtp=Ag005]R<#3R=#P#6R>%3=R?#3R@#3#3RA#3RB#6#5RC'x%6@#5R@#8\C%6A#5RA%5>R>%P<#3#3#6RD#5%8Ap,4segsREf8RF'df6RG,@A30g00LkRAf7RH#[g01FXRI30g01G8RJ/X4RK#8%VFPJP4g01GdPIPHPGf5RIDQ%:?Cr,@K30f<RK/MHp,3srcR?/9050C1BDH,7I=040%2Hp,1nRJ,1H'4%2G%:<RL,7H/1Jp,2fxPEfARMf@f:RN#Nf?ROf>f=PKf;RP%OFPHPGPIPCf9RI,9?RG%I@RQ#8RRPE%NPRS1BDK,H3g00W@#\RTC<%OI%G@5Z@,@QRQ30X>CPC1BDPRP,7IRD,9?PEPSP3PTC<=0RQX>CP4PFPEPS19?3PTC<=0RQXR4PNPFp,2bs,Y@R@%WJRN505%;@RQ1F2JRR504RTP5P4%E5P1%E4%;8%;3504A05831U833TXQ5X;5P@PQ1D4QPN1F23X;4RNPJO1P3X;4PNPJPJ1D4JDRM<Sp,4HlenCwRNPT%v@R@%2QRQ1u2JR51C2JA04RJ'411J2A04R2'4'qR1PRP4%:=RS%:BRB'pRE1C2S%2B1oSBRU,C2[[RV%2SRWg00K<RXAnSB8UW=RB%2U\X^=WRWg00KXRX#GRU%IXRXP41J47P8%j4CiRS%h4RY%f4RZPZP9P:P:P;1L421K4<R<'?,>ZR91K4=R=,?<,>ZFeR[%c:R:P[CA1gZ;R;P3P7g00MKR[,DA1b37=0A[dAk428ClR2b5b8b9X04X14%23R[1138'4%28RA1187'4[^04^14P3PJPMPIO3b4b6b7b<b2b:b3PNPTP@PQP5P1PRP4PEPVPBPWPUPX1J48PYPZP9P:P9CAP;P2b5b8b9X04PA\[^04P3POPFO2b4b6b7b<b2b:b3PNPTP@PQP5P1PRP4PEPVPBPWPUPXPSPYPZ1L4L9a4</?=,>ZRZP:PZCAP;P2b5b8b9X04X14173L/18178L/17[^04^14P3PJPOPHO3b4b6b7b<b2b:b3DmPDP6E=1HGPA`?IPE=1MMKP0E=M?_WDWCWEWBWFW?W@WAXH4XI4XJ4WGXO>WLWPWNXKCWMo"). Qed.

  (* [comment removed for export] *)
  Lemma mc_sb : forall regs pc rom w rs1 rs2 (imm : bv 12) k k0 (v : word),
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ dst k0 -> (k0 + bv_signed imm = k)%Z ->
    getr regs rs2 = v -> Z_to_bv 8 (bv_unsigned v) = b_ k ->
    (0 <= k)%Z -> (k + 1 <= n)%Z ->
    RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (memk (k + 1)) rom).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"; "MEMK"] "h01xh14__x1h22H3h32Hah45Hlen0h57__arithh64__ffh76__sat4h86__sat5h98__varmaph:5__with;4__x2h<1bh=4cstrh>1yh?2z3h@2HbhA2HdhB2HehC2HfhD2HkhE3Hk0hF3Hk1hG4Hrs1hH4Hrs2hI3immhJ1khK2k0hL1mhM1nhN1ohO2pchP4regshQ3romhR3rs1hS3rs2hT1vhU1whV1zp&0p;1p;2p;3p;4p;5p;6p;<p;Dp;7p;8p;Bg002Yj11Tg00V[j1RTg003>j17Tg003\j18Tg000Nk206Tg00Y2j1=Tg01;aj2lTg00a1j2KTg00:?j30j1PTg01<cj1]Tg01=cj2ZTg01>Cj1XTg01HPj4UTg006`j1:Tg01?`k404Tg01@@j2@Tg004?j26Tg01AHj2>Tg009<R0j22Tg008Rj2kTg009Yj2hTg010Lj1CTg00FWR1j23Tg00\[j1ATg00;ej1ETg00V;j3_Tg00ZSj3^Tg01I<j1\Tg01JDj5DTg01KLj2[Tg01B0j2<Tg01LHj2YTg005Cj2BTg001:j6;Tg01DDj3WTg00S5j1VTg00YTj2TTg00\;R2j1STg00aSR3j19Tg011Qj2QTg00c6k205Tg00cYk303Tg00bQl<NTg00d6j4yTg00d]j1xTg00eBj2sTg007[j2?Tg0087j2MTg00l5j2rTg00:Yj2qTg007>j2pTg00;Aj3oTg00<Ej1nTg00<ej2HTg00=Cj1jTg00=aj1iTg00>Lj2FTg00>oj2GTg00?Rj4ITg00@aj1gTg00ACj2mTg00Aej2fTg00BQj3eTg00C0j4dTg00b3j1cTg00llj4tTg00Noj1vTg00OMj4wTg00Okj3aTg00edj4`Tg01MPj5zTg01NYlD{Tg01Ofj3|Tg00QZj6}Tg011nl<OTg00G3j7~Tg00H;k800Tg0137mB01Tg00H_R4f0R5'3p=4g006BR6/B5p=5P6g00]bR7P6P6P2f4R2P3f3R8g013]f2R9f1R:P5M<Op>02P:g00I=R;g00I\R<P<g00J<R=P5g00J\F~p=LP8P;P<P<P=P9P:P5L00p=JP7P6P6P6P3P3f5R;P2P8P9P:P5M<Op=uP6P6P6P6P6P6P0P5P:P9P0P8P2P;f6R0f7R>f8R?f9R@NB01p=bg005]RA#1RB#R#7RC%1BRD#1RE#1#1RF#1RG#7RH#8RI+06%7ERE#8RJ#=\IRK%7F#8RF%8CRC%RA#1#1#7RL#8%=Fp,4segsRM/l?1KF030g00LkRF%]>g01FX30g01G8RN/Z6RO#=%X?PNP6g01GdP>P0P;CU%:DRDH04,KO30f<RO/@?p,3dstRN/6250I1>L>,2;=060f>RP/@@=0I;1kH0,hE%C?50J%4@f:RE%:ARH'2p,1nRQ'3PKf;RR#ARS16NRRT%CRRU%EJ5_J3^g01Q5RV#\p,2fxRWfCRXfBRY%AOfARZDD,[MPWPX1<YDP5PZDD,YV30XNKPWPMPYPZPSf@f?PPf=RSPOPTP@PUP?P>P0PI16NER01>LS,<516NORS50IX<IPI1>LORO,2ERL,6NA0I5SX<IP6PR16N5=0ISXV61BITPLP2E;1<0OAWNEOE;1@YPP;E;P8P9PRPRg00W@#VR8p,2bs,TJRJ%SQR;507%9JRP1Q4QRO506REP7P6%P7P3%P6%9:%95R3506A07:5205:5403X>7X07PJPP%5PP;1Q45X06R;PQO1P5X06RNP;PQPQ%5QR;I02M<Np,4HlenCyR0PE%xJRJ%4PRP1s4QR21?4QA06OQ'M13Q4A06O4'M'rRLPOP6%:BRT%:GRG'qRS1?4T%4G1pTGRU,?4[[R@%4TRZg00K<RMAoTG:UW3RG%4U\M^3ZRZg00KXRM#ERU%nMRM1H6:%j6RT%i6RWP61F64g00LDRK1G6ARACI,LWRV%g<R<PVCJ1mW=R=P5P9g00MKRV,BF1f59=0FVdAe64:CdR4b6b9b:X16%45%4:[^16P5PYP?O2b5b7b8b?b2b=b4R?%4Re%98RV,2RRF/3QRD12RHRX/3QP6P6P1PNP113:5#cX>6X06PFPXPNPNPNP6P6g017T12:5Ct#5XL6XM6PRPR%5RPVPHPNPN%53X07P8PH%5HEuM:bPQPQP;M<NP0PEPJPPP2PLPOP6PSP@PGPZPUPMP61H69P:%v6CwPTPWP61F6H9a6APK1G6BCI,LWRWP<PWCJP=P4b6b9b:X16X;6125H/3:12:H/39[^16^;6P5PQPYP>O3b5b7b8b?b2b=b4R>C`PDeDzMD{%AXA|R?>E}WFWEW@WHWDWGWAWBWCXTIXK6XJ6WIXSCWRWUWQXOIWPo"). Qed.

End MEMK.

Lemma sb_val_b : forall bs j, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned (b_ bs j)))) = b_ bs j.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"] "h04__p1h14__x1h22Hah37__arithh44__ffh58__varmaph65__with71Hh86__sat0h96__sat1h:2bsh;1jh<1zp;1p;2p;3p;4p;6p;7p;8g002Yj10Tg003>j1?Tg003\j1HTg00<Ej1:Tg010Lj24Tg01R<j1RTg008Rj23Tg006`j19Tg007[j22Tg0087j28Tg009Yj2=Tg00:?j3>Tg01SHj2XTg00;ej1VTg00<ej2UTg00=Cj1QTg00=aj1NTg00>Lj25Tg00>oj2LTg00?Rj47Tg00@=j6GTg00@aj1FTg00ACj2ETg005Cj2ITg00Aej2DTg00BQj3JTg00C0j4KTg00:Yj2CTg007>j2BTg00;Aj3MTg00Cbj3ATg00DEj3OTg001:j6PTg00FWj2@Tg00G3j7STg00GWj7TTg00H;j8WTg00H_R0f0R1'@p=1f1R2g00I=R3g00I\R4P4g00J<R5P1g00J\FSp=6f2R6P3P4P4P5P2P1FTp=<f3R7P3P4P4P5P6P2P1GWp=;g005]R8#0R9#0#0R:#?R;#HR<#:g006BR=1421R>#R13;>R>#1%0:#0#0R:#0#0#9R?,2>'8P=1462R>,3;R@1=;11476RA5><X<=1X;>%?:R>1=>@'3p-0R<g00KXRB#VRC%:BRB1U=2RD%Q=RE%N=RFP=15=0g00LD1L=8R8C7,6FRGPFP3P4P4P5P7EGR35<F%F4R4PGC;1EF5R5P1P6g00LkRGg00MKRH'I1D16=>GHdAJ=02CKRHb4b5b6X1=W0%11/82%12[^1=^0<P113;ARA/2?PAP2O3b3%99R9%9:R:'C1209%1:1B9:RA,20[[%19R0g00K<RGAM9:2UW2%1A\G^20PCPBPDPEPFP=P8g00MkRE15=?C7,6F9<F3P4P=P8PE15=9=A=>C7,6FC;P5PHb4b5b6X1=X0<121?,82122A[^1=^0<P1f5f4'4,3;R;#1P;P7O3b3b8b95O@EPb7W;W:o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MSETK.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variable s : word.
  Variable n : Z.
  Variable b : byte.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned s + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok segs mem0 s (Z.to_nat n) = true.

  Definition msetk (k : Z) : word -> option byte := wbytes mem0 s (repeat b (Z.to_nat k)).

  Lemma msetk_0 : msetk 0 = mem0.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"; "MSETK"] "p;1p;2g002Yj10Tg003>j12Tg003\j11Tg00Y2j13Tg005Cj24Tg005]#0#0#0R0#0#0#0#2#1%20#1#3[p,4mem0'4o"). Qed.

  Lemma wr_s : forall k j m,
      (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      store_ok segs (msetk k) (at_ s j) m = true.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"; "MSETK"] "h04__p1h14__x1h24__x2h34__x3h41xh52H1h62Hah77__arithh84__ffh94__p2h:6__sat2h;6__sat3h<8__varmaph=5__with>4__x4h?4cstrh@1mhA2z1hB2HjhC2HmhD1jhE1khF1nhG1yp;1p;2p;3p;4p;;p;<p;Bp;6p;7p;8g00aSR0j1:Tg009<R1j22Tg00FWR2j20Tg00\;R3j1STg002Yj15Tg003>j1MTg003\j1cTg01T:j3^Tg008Rj2[Tg006`j1JTg007>j2XTg011Qj2ITg00b3j1|Tg00llj4zTg00d]j1eTg00eBj2dTg007[j2?Tg00:?j36Tg0087j24Tg00l5j2FTg00:Yj2\Tg00;Aj3ZTg00S5j1ETg00STj2<Tg00UOj2=Tg00;ej1YTg00V;j3@Tg00<Ej1WTg00<ej2DTg00OMj4HTg00=Cj1VTg00=aj1UTg00>oj2BTg00V[j1{Tg00>Lj2RTg00@aj1yTg00Okj3QTg00Cbj3uTg00?Rj4GTg00ACj2qTg005Cj2NTg00Aej2oTg00BQj3nTg00C0j4gTg00edj4LTg00R6j1fTg00RTj2hTg00T=j3iTg00Noj1jTg0188l;kTg01TYj1lTg004?j2mTg019Kj4bTg011nl<OTg0137lBaTg00bQl<`Tg00Tfj3sTg00@=j6tTg00G3j7_Tg00GWj7wTg012Sj7xTg00H;j8]Tg00H_R4f0R5'0p=7g006BR6/N5p=8P6g00]bR7P6P6P3f4R3P0f3R8g013]f2R9f1R:P5M<Op=vP7P6P6P6P0P0f5R0P3P8P9P:P5M<Op=rP6P6P6P6P6P6P1P5P:P9P1P8P3P0f6R1f7R;f8R<f9R=MBap=pP6P6P2P;P2P1P0P3P8P9P:P5M<`p=PA6654p=CAs6:5p=3P:g00I=R2g00I\R;P;g00J<R>P5Etp=TP6P:g00XKP5CGp=AP:P2P;P;P>P5g00J\F_p=1P9P2P;P;P>P:P5Fwp=>P9P2P;P;P>P:P5Fxp=KP6P:g00LDP5CGp=9P8P2P;P;P>P9P:P5G]p=;%7:%::,29p,1nR2'0p,4segsR?p,4mem0p,1sR@%S2RAg005]RB#5RC#5RD#5RE#M#cp,1b%S33^P8P9%5E#5#5RE#MRF/[@RG%:ARH'2RI%JCRJ%JERE'XRK'01I42RL,2GRM/0KP5X46RN10:5#|XG6X46ROPIPMPNPNPNP6P6g017T12:5Cz#8X@6XF6PGPG%8GPHPLPNPN%:5#8X47PAPLPN1I45X46P2P2%82DvErRAM:pPKPK%8KGP%e9RM%:9RI#7RP1d42RQ1?42RRA66L2'41024RS%CL'4'FRTPLP61\JERU1?4J%7E1?4K[[RV%7JRWg00K<RXAZJE:UW6RE%7K\X^6WRWp-0RXg00KXRYg00W@RZ#ER[#ER\#E,<6R]1<6\R\1<6[1<6ZRZ'3R['3'3g00W_R^'=13\Z,3]/=^%YYRZ5@Y3@%WYR_P61D69P:1D68R`CH%V6Ra%U6Rb1Tb01B6CRC%{B,B6R0'A,1b5>b1Tb1Rc1R64Rd,AC,1b5>b5Kb%y;R;PbP61B6BRe=Q60g00Mk1R6J=u6FRFCG,1bP;Pb19d0,1bP;AQ6eCRe/9F,1bC;C;C;1qb>R>P5P9g00LkRFg00MKRC'N1o59=6FCdAn64:CgRJb8b<b=X16X26X36X0XW9A66:9,48%C:,43'F12:8/?K%731283/0K[[[^16^26^36^0X^9XP5PSPRP2P8PGP3p,3Hnwp,2HnO8b7b:b;bAb5b?CLp,3HokP:128IRI/0H10ILPNPOPIPI%8IPHPLPAGPPMPPPQPTPLP6PUPVPEPW%fB,h6=i6\/3[R[,3]/=^1=[^=@YZ5@YP_P6P61D63P9%j6CHP:P`CHPaPb1B6DRD,A0,1b9>bc19Dd,1b1A0d,1b5>b5KbP;Pb19eD,1bP;19e0,1bC;C;P>PJb8b<b=X16X26X36X>6X0XA6698,431084%C9'4'F12:9/031298/03[[^16^26^36^>6^0XP5PRP2P8%:<P=P3P1O7b7b:b;bAb5b?CLM;kP?%l31m@8P9Cb=6FCeWCWBX@7XD6XE6o"). Qed.

  Lemma msetk_extend : forall k m,
      (0 <= k)%Z ->
      wbytes (msetk k) (at_ s k) (repeat b m) = msetk (k + Z.of_nat m).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"; "MSETK"] "h01xh14__p1h24__x1h34__x2h42H1h52Hah67__arithh74__ffh86__sat3h98__varmaph:5__with;4__x3h<4__x4h=1nh>1yh?2z1h@1HhA2H2hB2HkhC6__sat2hD6__sat4hE4cstrhF1khG1lhH1mhI1ohJ2z2p&0p;1p;2p;3p;<p;4p;8p;6p;Bp;7g00\;R0j1ITg00i^j2[Tg00aSR1j1<Tg009<R2j2;Tg00:?j33j1bTg00c6j2kTg00cYj3gTg005Cj24Tg00bQl<dTg00d]k106Tg00eBj2QTg0087j22Tg00FWj2ATg00l5j2DTg002Yj1=Tg006`j1XTg00:Yj2pTg007>j2oTg00;Aj3mTg00R6j1lTg00RTj2jTg00S5j1CTg00T=j3JTg00STj2WTg00;ej1fTg00<Ej1VTg00Noj1eTg00<ej2STg00OMj4MTg00=Ck10<Tg00=ak10;Tg00>Lk20:Tg00V[k108Tg00>oj2KTg00?Rj4UTg00@ak105Tg00Okj3`Tg00ACk204Tg00Aek203Tg00BQk302Tg00C0j4zTg00edj4^Tg003>j1]Tg003\j1\Tg00Y2j1yTg01T:j38Tg00ZSj35j2Zj1rTg004?j2Bj1qTg01Uaj3xTg00YTj2sTg00b3j1tTg00fOj8PTg0027j3wTg001:j6OTg01V>j4nTg01WPj4{Tg00QZj6|Tg01TYj1YTg011Qj2}Tg011nl<_Tg0137lB~Tg007[k200Tg00Tfk301Tg00UOj2NTg00V;j3TTg00G3j7cTg00GWj7iTg012Sk707Tg00@=j6hTg00H;k809Tg00H_R3f0R4'Ap=>1}34p=6g006BR5f1R6;34p=1P5g00]bR7P5P5P0f4R0P1f3R8g013]f2R9P6P4M<_p=LP7P7P7P5P5P5g014lP1P1P1P2g015Lf5R2P0P8P9P6P4MB~p>0=20034p=9A3543p=F1W54p=@B01564p=0g00KXR:g00W_R;,N91N6;=T:43Tp=HP6g00I=R<g00I\R=P=g00J<R>P4g00J\R?Fcp=:P9P<P=P=P>P5P6g00XKP4CUP?Fcp=7P9P<P=P=P>P6P4Fip=GP5P6g00LDP4CUp=EP9P<P=P=P>P6P4K07p=RP6P<P=P=P>P4Ehp=aP8P<P=P=P>P9P6P4L09p=?P7P5P5P5P1P1P2P0P8P9P6P4M<_p=u1N6;=T:4p=v%>6R;%I9R</[6R?%<6R@,;9RA#IRB537RC%69RD/;@RE%6ARF'1P7P5%b7P1%b5R1%<4RG,1@A37641k643gX>7X07P?PEP<PDP4X05RD%64X05R<P9P91459DLP6P@145@J0=PBPFPDP<PAPA145ADLM<d&066%>@%<9,;8R@,Q3%9@%6@RF/1@'21A@3%FF'2'D%<8,;0#6P51Q32%92%62RF/12'21A23%FF'2'Df6RF#6P5g005]RB#=RE#XR?%=E#=RH#=#=#=RI#XRJ'pRK%9?%>J1o?JRL#9[[RM%>?RNg00K<ROAm?J6UW5RJ%>L\O^5NRNp-0RO%lB,j5RLg00W@R?#CRP#CRQ#CRR#CRS#CRT#@RU5J5%@RRR%@QRQ1W5?R?'0'0'0RV%@SRSAJ5LRRW%@P/0?RP'0'0RX,0UAJ5LS10R?'0RY,0U10W?,0SRS10US%CT#@/0V%f:RV3H5HY5HX3H%V:R:P5P5%e5RXP91S50CMP61S58CM&0<5RY&0;5RTP520:53RSg00Mk&08BRU#=,K5RWCU,:T1K5BRB=7TW5GT1EWS,:TA7TBS5GT5RT&05=R=PT1aTF1K5URU1K5ERE9`5WRZ57T5GT1EZS,:TA7TUS5GT5RTP=PT1ESE,:TP=PT1ESW,:TP=A`5BE=7TUC?C?C?C?204T>R>P4P9g00LkRUg00MKRW'420349=3UWdB02536CzRWb7b9b:X25X35X;5X<5W1%98RU1148'21A83RZ%F4'2'D1;09R[,18,221A[3%F8'2'D%>8%>F1;02/1F[[[[^25^35^;5^<5^1OP4f:R[f9#<R\';#9P[P2P\P8P0PFf7f8R\O9b6b8bDbJbAb?b4bEC^PCP7%I8RC/[9R2%]I#\RI%]H#\RH#y[R[p,4mem0R]p,1sR^p,1bR_%I058H35R`1B^0A8H_8Ra35RbA8H_495]^33X=7%VHRcA8H_CRdA8H_9Re5xHRfA5]^493[bXGcP[A5]^dRg1sHdRh#<,B^;5eA3[b4XI[P7PC1B^G=5`a93[bX=7PcP[1B^8Rb,Zg%<CRa,B^R`,ZgPePePIP[\cRi%rgRgPgPbP`Pi\I/4gP5PI%q^RgPgP8PaPI\5/4g118a%68Rg,18P5P5P1PDP11164R1#tX>5X05P8P81458RIPaPgPDPD145GX07PCPgPDP<P8P8PIDLEuM<d1Q3811g8,2U%Fg,2Z'D%60P5PKPMPJPNAJ5LQ/0?R?,0R10QP1v?V3HP:P51S59P6PXCMPYPT1aT0A7TEB5GT1EBS,:TA7TES5GT5RTP=PT1ESB,:TP=A7TBEC?C?P>PWb7b9b:X25X35X1O12911A43%F6'2'D1198\;[^25^35^1OP4%9\P8P\P0PFO5b6bCb8b?b4C^GPGP14ceGPPhAwH_CEOA5]^fPdPeP]P^CnEOA8H_2PHP_PCP9C{EO%I@P4E|b@%Y91B^9A8H_635%YA53[eWBXH7XF5o"). Qed.

  Lemma msetk_extend1 : forall k, (0 <= k)%Z -> wbytes (msetk k) (at_ s k) [b] = msetk (k + 1).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"; "MSETK"] "h02Hkh11kp;2p;1p;3g00FWj22Tg00S5j11Tg01Woj30Tg006Bg00H_f0R0'2f1g00W@#1;00W0W1o"). Qed.
End MSETK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.land (a * 2 ^ k) b = 0%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"] "h04__x1h14__x2h21bh37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with92Hah:2Hbh;2Hhh<2Hih=2Hkh>2Hlh?1ah@1ihA1khB1op;1p;2p;3p;4p;7p;6p;8g002Yj1]Tg006`j1KTg007>j21Tg007[j22Tg0087j2<Tg01Y>j25Tg01Y[j2?Tg01Z9j20Tg01ZZj26Tg00:?j37Tg01[8j2DTg00FWj24Tg00l5R0j2\Tg005Cj2ATg00:Yj2VTg00;Aj3UTg00;ej1TTg00<Ej1PTg00<ej2@Tg00Noj1OTg00OMj4JTg00=Cj1ITg00=aj1HTg00>oj2>Tg00?Rj4;Tg00@aj1GTg00ACj2LTg00Aej2FTg00BQj3ETg00C0j4MTg01[]j4NTg01\Hj1QTg00>Lj2CTg00GWj7RTg01\hj6STg01^:j1[Tg01^Zj3ZTg001:j6BTg01_=j3WTg00G3j7XTg00H;j8YTg00H_R1f0R2'4p=3g00LkR3g01FXR4772p==f1R5g00I=R6g00I\R7P7g00J<R8P2g00J\FXp=9f3R9P6P7P7P8f2R:P5P2GYp=8P3P4P9P:P5P2EBp=:g006BR;%3:%35R<%39g005]R=#]R>#KR?/1:,29'<f5R@11?9'5f4RA'?%32RBP3f7RC11?@'5RD/05f6RE/05'6101:9732X23f8RF11?E'5/0:10C:'6=732X231D5@125@14@5'\P012:E14E:f9R011?C'5/0910F9'6#=P2129Cf:RG/0@,62#=X231A3411?F,5G/0AR4PGPFPA1V?FRH121?%3011?G,21[[RG%3?RIg00K<RJf;RK=U?5UW9RL11?KRM#3\J^9IRIg00KXRJ#TRN%PJRJP;1@;:P5%O;CJRO%I;RP%H;RQP;1>;=R=g00Mk1>;>R>C;,9QRR%G7RSPRC81LQ8RTP2P:g00MKRU,A31F2:=73UdAE;15CMRUb4b7b8X0;X1;1225RV125:RW[^0;^1;P2PKPCP9O3b3b5b6CNC:W>P2O114C911?0,5K/0@/62#=X23%Q4100APFP0PAPHPGPLPIPNPJ1@;5PPPQP;1C;1g00LDRAP=C;,9QR4PSP4C8PTPUb4b7b8X0;P<\B^0;P2PKP0O2b3b5b6PHPGPLPIPNPJPOPPPQPQP6P7P7P8P4PRFRRRPSPRC8PTPUb4b7b8X0;X1;1<BV1<<W[^0;^1;P2PMf<PFO3b3b5b6PHPGPLPIPNPJPOPPPQP;P=PAP>C;,9QRQPSPQC8PTPUb4b7b8X0;X1;1425145:[^0;^1;P2PCPKP9O3b3b5b6ESC:W;P2O1n200100000021000011000bB1015%[5C:1?DE/05AZDE5EBW<X@;7W1W:W=W9XA;X2;W?o"). Qed.

Lemma lor_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"] "h04__x1h12Hah27__arithh36__sat0h46__sat1h54__ffh68__varmaph75__with84__x2h92Hbh:2Hkh;1ah<1bh=1kh>1zp;1p;2p;3p;4p;7p;6p;8g002Yj1WTg006`j1CTg007>j22Tg007[j21Tg0087j23Tg01Y>j2:Tg01_`j2BTg009<j25Tg00:?j39Tg00:Yj2?Tg00;Aj3=Tg00;ej1<Tg00<Ej1VTg00<ej2;Tg00=Cj1UTg00=aj1LTg00>Lj2KTg00>oj27Tg00?Rj48Tg00@aj1FTg00ACj2DTg005Cj2ETg00Aej2ATg00BQj3GTg00C0j4HTg00Noj1@Tg00OMj4ITg00GWj7JTg01`>j6>Tg01aRj3MTg01b<j4NTg01bXj2OTg01c5j3PTg00QZj6QTg00FWj2RTg00G3j7STg00H;j8TTg00H_R0f0R1'Rp=0f1R2g00I=R3g00I\R4P4g00J<R5P1g00J\FSp=4f3R6P3P4P4P5f2R7P2P1GTp=6g006BR8%07%02R9%06g005]R:#WR;#CR</27,16'3P8f5R=12<6':R>f4R?'BR@f6RA12<?':/5=9981X>8P815>?P@P=P?P61?<6R@110<%0?12<=,10[[RB%0<RCg00K<RDA=<A2UW1RE12<AR<#0\D^1CRCg00KXRD#<RF%VDRD1;82%U8RG%L8RHP81K80g00LD178:R:C8,4HRI%F4RJPIC61DH5RKP1P7g00LkRLg00MKRM'E1A17=9LMdAG802CHR0b5b6b7X08RM%01RLP9[^08RNP1f8P=O2b2b3b4P@PBPEPCPMPNP1PAP?O2b2b3b4P@PBPEPCPFPDP81;87P2%@8CIPGPHPHP3P4P4P5PIP8P:g00Mk178;C8,4HFJRHPJPHC6PKP0b5b6b7X08X881112,3L1127,39[^08^88P1P<f7P6O3b2b3b4E>R69M>?CN1O>?AP>?6EQW9W:W1X=8X<8W;o"). Qed.

Lemma v_slli_mul : forall (x : word) k, (0 <= k)%Z -> v_slli x k = Z_to_bv 64 (bv_unsigned x * 2 ^ k).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"] "h04__x1h12Hkh27__arithh34__ffh48__varmaph55__with61kh71xh81zp;1p;2p;3p;4p;7p;8p;6g002Yj10Tg003>j1MTg003\j1=Tg00FWj24Tg008Rj27Tg006`j1FTg007>j25Tg01Y>j26Tg009Yj22Tg00:?j31Tg005Cj23Tg01cWj28Tg00;ej19Tg00<Ej1LTg00<ej2KTg00=Cj1JTg00=aj1ETg00>Lj2BTg00>oj2?Tg00?Rj4>Tg00G3j7@Tg00@aj1ATg00H;j8<Tg00ACj2CTg00Aej2DTg00BQj3;Tg00C0j4GTg01d7j3HTg001:j6:Tg01d`j2ITg005]R0#0R1#0#0#0#0#0#MR2#=R3g006BR4g00H_R5f0R6'4R7P4f2R8,72R9%F1R1f1R:'5'6R;1226f3,721518'6,22513X84122;R;,33189:g00KXR2#9%L21K4:%J4%E4R2g00I=R1g00I\R<P<g00J<R=P2P1P<P<P=P41B45g00LD1?40C>g00J\F@R0%A<P0G<1C2=P6P8g00LkR=g00MKR2'31D68=1=2dA;45:CGb3b4b5X04145:\7^04P6P8P:O2b29H9:E:1I8:=13;eW1W6W7o"). Qed.

Lemma v_or_shl : forall (x : word) a k, (0 <= a)%Z -> (0 <= k)%Z -> (a * 2 ^ k < 2 ^ 64)%Z ->
  (bv_unsigned x < 2 ^ k)%Z ->
  v_or (Z_to_bv 64 (a * 2 ^ k)) x = Z_to_bv 64 (a * 2 ^ k + bv_unsigned x).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"] "h04__x1h12Hah27__arithh36__sat1h46__sat2h56__sat3h64__x2h74__ffh86__sat4h98__varmaph:5__with;4__p1h<4__x3h=1zh>1Hh?2H0h@3HakhA2HkhB2HxhC6__sat0hD1ahE1khF1xp;1p;2p;3p;4p;6p;5p;7p;8g002Yj18Tg003>j1hTg003\j1UTg006`j1MTg007>j24Tg01Y>j26Tg007[j21Tg008Rj25Tg00^Aj1QTg0087j2?Tg00:Yj2CTg00;Aj3;Tg00;ej1gTg00<Ej1fTg00Noj1aTg00=Cj1ZTg00=aj1XTg00>Lj2LTg00ACj2VTg005Cj2GTg00Aej2TTg00:?j3:Tg00BQj3STg00C0j4RTg01bXj2ETg009Yj27Tg009<j2ATg00<ej2DTg00>oj2@Tg00@aj1PTg00OMj4FTg00@=j6OTg01ejj6NTg001:j6KTg00S5j1<Tg00STj2>Tg01g=j3BTg00Tfj3JTg00UOj2eTg00V;j3dTg00V[j1`Tg01gfj5\Tg00Cbj3[Tg01hJj3YTg00DEj3]Tg01hmj2^Tg00FWj2_Tg00?Rj4ITg00G3j7bTg00H;j8WTg00GWj7cTg00H_R0f0R1'_p=0g006BR2f1R3g00LDP1CIp=9P3g00I=R4g00I\R5P5g00J<R6P1g00J\Fbp=3f3R7P4P5P5P6f2R8P3P1GWp=2P8P4P5P5P6P3P1Fcp=HP2P3g00MkP1CIp==g005]R9#8R:#8#8#8#8#8R;#hR<#UR=%03R>%M:R?/48,67%M;R;,4?R@'1f5RA,5<14?7'1f6RB#Q15<BRC#011C@'?1C?;RC110?RD%0;110@[[RE%0?RFg00K<RGA;?;3UW1R;%0@\GRH^1FRIf7RJ,C?f8RK#0f9RL,4?,10[\Df:RM=;?3VGX1F14?MRN#0\G^1Fg00KXRO#gRP%fORQ%a2RR%Z2RS%X2RT1L20RU1L2?RV'9'3RW1VT6RXP1P8g00LkRYg00MKRZ'G1T18=:YZdAS203CRRZb7b9b:PFP1b2bCb3b4b59;?A14?ARY#0P214?B,6JR[15<LR\,E1,7<14?J,6K/A\,7<R\5:=X=2P215<KR],A[R^17<1=:=\X=217<^,G=1E[]PJP]PBPCPEP;PI1C?KR]%0L110N[\DRNf;R^=;?3VGX1FR\14?^R?#0\G^1FRGPPPQ1D23PSPT1@29R_,9U,3TR`%P5RaP`C2PXPZb7b9b:X02Rb%01RcP>[^02RdP1f<RePMO2b2b3b4b5b8PCPEP;PIP]PNP\PGPbPdP1P^PLO2b2b3b4b5b8PCPEP;PIP]PNP\PGp-0RdPPPQP21D28RbP3PRCFRRPSPTPTP4P5P5P6f4RfEO9HT`PaPT1@2:R:,=_,3TRgPaAHT`gC2C2PXPZb7b9b:X02X62W;1?c81138%081187'?[[^02^62^;dP1f=,5<Rd/1@P?PdPBPJO5b2b3b4b5b8ENEK17<[,5<PCPEP;PIP]PNP\PGg00W@Rd#<Rc#<#<Rg,>2Rh%<g,>21>2cRc5B2=J2c5B21>2d9B2h5J2g00W_'e=dOPPQP2PbP31D27CFPSPTPT1=UV,3TPaPT%`9,@2,9U,3TR9Pa1=U:,3TC2C2PaPTPTPWPaPTPTP4P5P5P6D\PaA[2V<RV,9U,3TC2C2PaPTP9PaPTP`PaAY2_:R:,9U,3TC2C2C2C2PXPZb7b9b:X02X62X<2%07RU1107[\DPH\F%0f16fA#0\U[[[^02^62^<2P1P^P?PeP8P7PLPMO7b2b3b4b5b8PCPEP;PIP]PNP\PGPPPQPRPSPT1=:V,3TRTPaPTC2PXPZb7b9b:X02X621613/1@1638/1@[^02^62P1P?PePKO3b2b3b4b5b85][EKb?16BYRY,7</^J15<J,AY,7<5:=eb>WBW@XA>W1XE2XD2WFo"). Qed.

(* [comment removed for export] *)
Definition M8 : Z := 72340172838076673.

Lemma M8_digit : forall c k, (0 <= c < 256)%Z ->
  (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%Z ->
  (Z.shiftr (c * M8) (8 * k) mod 256 = c)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"] "h01Hh17__arithh24__ffh38__varmaph45__with54__x1h61kh71zh86__sat2h94__x2h:4__x3h;4__x4h<1Bh=3Mhih>3Mloh?1Gh@2HBhA2HMhB2HchC2HkhD3HlohE3HlthF3Hm1hG1cp%0p&0p;1p;2p;4p;3p;6p;7p;8g002Yj16Tg006`j12Tg007[j2=Tg0087j2STg00V[j17Tg01Y>j20Tg01j5j2GTg009<j2ATg01jUj2lTg00RTj2QTg01kFj2jTg00STj2iTg00S5j1MTg00R6j1^Tg00UOj2RTg01koj2tTg00;ej1sTg00<Ej1rTg00<ej2XTg00Noj1qTg00OMj4VTg00=Cj1pTg00=aj1oTg00>Lj2dTg00>oj2UTg00@ak10<Tg00Okj3bTg00ACk20;Tg005Cj2[Tg00Aek20:Tg00:?j3>Tg00BQk309Tg00C0k408Tg01lXj2ZTg01m5k305Tg01mXk104Tg01n9k303Tg00QZj6kTg01n`k102Tg01oAj4cTg01obk301Tg001:j6_Tg020Ek600Tg020ij4~Tg021Lj3{Tg022Aj4zTg007>j2?Tg022oj2gTg023Oj2yTg024;j3xTg00FWR0j2|Tg00l5R1j2PTg01g=j3mTg00T=j3wTg00Tfj3WTg00V;j3fTg00?Rj4`Tg00G3j7aTg01hJj3vTg00GWj7uTg00H;k806Tg012Sk707Tg00H_R2f0R3'|p=4%63#6p=hg006BR4?>32p=Yf1R5=>43p=1f3R6f2R75>4A>453'Pp=Ef4R8=>46A>475/P3'Pp=31P53,P7p=e%63#6#6p=C%63#6#6#6p=B1?53,Z7p=F1G75=>43p=;Am453p=D1i43p=LAw453p=NAW4539W47p=\g00KXR9Af9537f7p=KP7g00I=R:g00I\R;P;g00J<R<P4P5g00LDP3C`g00J\R=Fap=:Av453p=H1d43p=5P7P:P;P;P<P4P5g00XKP3C`P=Fap=<P4P5g00MkP3C`p=TP5P:P;P;P<P3P=Fap=OP7P:P;P;P<P5P3Fup=nP6P:P;P;P<P7P5P3L06p=81Z67/G5=>43p=@P4P8P6P7P5P3E_p=9AW453p=]Am475=W43p=J1053,?7p=}P7P:P;P;P<P5P3K07p=I%45g005]R=#6R>#6R?#6R@#6S00#6S01#hRA#6#2RB,=5'SRC%Y5RD%2=RE,15P5%2>RFP5%7=RG#2RHP5%2?RIP5%7>RJ#2RKP5%6GS02#2RLP5%7GRM#2RNCED3D33e%7AS03#C#B#7S04#C#B#7S05#C#B#7S06#C#B#7RA#C#B#7RO#C#B#7#2RP,06RQ%2@R@/07RR7FF1G3BRS/18X741=23RT1065/A7/1PRU%46RV%7M#7#7#7RW#7RX#2RY/08/=6RZf6R[?;BER\f7R]/lB%4]%4BR^f9R_/GB#4[[1Q4ES07,j4g00W@R`,i4Ra'DRb%M`R`#LRc%M`R`#MRd#MRe#LRf'DRg%^X,Q4/Nf3\g00W_RX'R%^=,Q4Rh/Ng1t4YRi/Df5\b/RX%s9Rb3K%r9R9P4P41X48S08P7%q4RjCVP51X46CV%p4Rk%o4Rl1d42Rm1U4?R?5:l&0<;RnPl1U4>R>1U4GRG'H=b4?%5PRo5<lPnPl1TmG,OlS09PnPl1U4=Rp9:lm%5B,Tp,Ol5nlRqPn1Hp>Rr/HG1Hp?5b41Hpo5<lC8C8C8C820;l<R?P3P7g00LkRsg00MKRt'[20:37=>stdB09425H08Rtb2b3b4X54X94X:4X;41076/A8/1P1=281=6B,SVf5Rs,08/0[108]'A108P'1[[[\V^54^94^:4^;4P3f8RuP]P_f=RvP8PsP[f;RwO8b1b810w]/0s10w['A10wPRx'1P4f<Ry/0uRz/0[10y]R{'AR|P3P]PBPvC@X741Z{[S0:,Az11SvX74RSP4P210v_/A3?;BvX74PzPSP41GuBR},0y/GB113vX74PE10v3?;BvX74PyPS1luBRS%4uf:R~/GB#4\^[R^PbP91X45S0;PkPlPqPnPqC8P?Ptb2b3b4X54%431=3B'SPC[^54P3f>RCPyO2b1b8:05yB10yE&04yD9P}P5D91GzBB03uyBEk1Az2&02zD9Q0:PSP^P4Q07P=1Q42S07CcR}/Nf/]a1j4}/DfR}%Ld/Dc%L`R`%MeRe#M#L%BW#B#7#^,Q4/Nf9Jig9J`a3J3\7Jc/RXP4PhP=Q07Cc/Nf/]a%Le,D`Re,D`1Dca9Jce5\}7J`/RX;KbP9P41X47P5P4Q08P6PjCVCVPkPl%5Y/H>/TG,OlPnPlA:lm>PnPl1U4J/HG=b4>=<loPnPlQ09PnPlPqPnA:lmr1TrG,Ol5nlC8C8C8C8C8P?Ptb2b3b4X54X94X:4X;410Y5/=7%4710s8/A6/1P1=2s%481=8B'S10s[RY#41=Y]'S[[[[[^54^94^:4^;4P3P~PuP_PCP8PsP[P]PyO9b1b8:01{[E_1Z|[PzP[P{PSP^PbP9Q0;PkPl1Tmp,OlPnPlP:P;P;P<A<lpmR<J00C8P?Ptb2b3b4X54g024d\D\T^54P3PuP]O2b1b8C~D910yPP3Ekb0WFWEWDWAW@X<4X>4X=4PxPsPBPwC@\\\Z\V\U\T^<4^>4^=4P1%Y6P6PEP6PFP6PHP6PIP6PKP6PL116ND3D3D310sP10@87FF?;BsP5%Y8P4P210]PRTA}F@3RUPBP]C@X64P7PPP2PEg025Ag025g'[R71[4PRVP4P0g026M9{40P2CzP71[4ER2O8PsP3E_W0P3O1P8PEP8PFP8PHP8PIP8PKP8PL118ND3D3D3P111sEPsPFPsPHPsPIPsPKPsPLPsPNCED3D310@[9FTF?;B]P311[EPE10_PRTPUPBP_C@X64P8%2OROPE1?F@P7PVPbP9PjPk%5ER89:lmP?Ptb2b3b4%4EP3b1P7P2O8P]P3D9W0P3O1P[PFP[PHP[PIP[PKP[PLP[PNCED3D3P111]FP]PHP]PIP]PKP]PL11]ND3D310@u9FTF?;B_P311uFPFPxPUPBPwC@X64P[%2ARAQ03#2R[Q00#2,?FP7PVPbP9PjPk%5[9:lmP?Ptb2b3b4%4[P3b1P7P2O8P_P3D9W0P3O1PuPHPuPIPuPKPuPL11uND3D3P111_HP_PIP_PKP_PLP_PNCED310@~9FxF?;BwP311~HPH10vPRxPUPBPvC@X64PuQ06#2RuQ04#2R_Q02#hRT#2,?FP7PVPbP9PjPk%5_9:lmP?Ptb2b3b4%4_P3b1P7P2O8PwP3D9W0P3O1P~PIP~PKP~PLP~PNCED3P111wIPwPKPwPL11wND310@y9FxF?;BvP311yIPIf?Rx/0PRwPUPBPxC@X64P~Q05#2R~P~Q01#2,?FP7PVPbP9PjPk%5~9:lmP?Ptb2b3b4%4~P3b1P7P2O8PvP3D9W0P3O1PyPKPyPL11yND3P111vKPvPLPvPNCE10@C9FwF?;BxP311CKPKfARw/0PRvPUPBPwC@X64PyP_Pu%CJ#2,?FP7PVPbP9PjPk%5u9:lmP?Ptb2b3b4%4uP3b1P7P2O8PxP3D9W0P3O1PCPLPCPNCEP111xL11xNf@Rx,0@9FvF?;BwP311xLPLfCRv/0PPUPBPvC@X64RvPCP[PA%6T#2,?FP7PVPbP9PjPk%5A9:lmP?Ptb2b3b4%4AP3b1P7P2O8PwP3D9W0P3O111xNPNPvPCPEPO%CM#2,?FP7PVPbP9PjPk%5O9:lmP?Ptb2b3b4%4OP3b1P7P2O8PwP3D9W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000b?1gQR1Nh`,]a/RX,yaRaAKaab9Kaa9Kaa7KaP9Q0;PkPlA<lp8%5F9<lp%5H9<lp%5I9<lp%5K9<lp%5L9<lp%5N9<lp5Il5Il5Il5Il5Il5Il9Il<Pn%5@/Hp9:lmC8P?Ptb2b3b4X54%Y3113EP3PFP3PHP3PIP3PKP3PLP3PNCED3D33e10@5#4[^54P3P6P5O2b19xQRD9g0272,06/gR?;B6eWCWBX64XG4o"). Qed.

Lemma byte_eq_mod : forall x y, (x mod 256 = y mod 256)%Z -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"] "h02b1h12b2h21nh31zh41Hh52H0h61xh71yp;1p;2p;3p;6g002Yj11Tg006`j1;Tg01j5j27Tg00:?j30Tg003\j13Tg008Rj22Tg0287j3:Tg003>j19Tg009Yj26Tg028[j24Tg029Aj25Tg001:j68Tg006BR0f1R1g005]#1#1#1R2#1#1#1#1#1#;R3'7f0R4/73500g02:0R3%34R5%31R6g0087f2R7#3?014f3R8/271281500R9[12711274500%38?071[R:f4R;#3?087\9A:714P4n2001000000120000000W1W0W2P:^16^05^23P4%92R21628R31627R5P014281223R39004X30P01427142;=004X30P112251527E8P31528E8O4b5W4X70W6o"). Qed.

(* [comment removed for export] *)
Lemma rep8_bytes : forall c, (0 <= c < 256)%Z ->
  word_to_le_bytes 8 (Z_to_bv 64 (c * M8)) = repeat (Z_to_bv 8 c) 8.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"] "h01zh17__arithh24__ffh38__varmaph45__with54__x1h64__p1h72Hah81Dh92Hch:6__sat0h;6__sat1h<1ch=1kh>5lemmap%0p&0p;1p;2p;3p;6p;7p;4p;8g002Yj14Tg006`j18Tg007[j2ITg0087j2OTg01Y>j2GTg003>j1^Tg003\j1oTg00<Ej1ZTg00S5j1@Tg02:Nj2XTg009Yj26Tg01T:j3_Tg00:?j33j1jTg009<j2MTg022oj21Tg00;ej1\Tg00V;j35j2>j1mTg02;Kj1}Tg00V[j19Tg005Cj2QTg01j5j2JTg02<Vj1iTg02=Gj3hTg02>9j1fTg02>hj6eTg02?Sj7dTg00<ej2cTg00=Cj1bTg00=aj1aTg00>Lj2`Tg00>ok207Tg00?Rj4NTg00@ak106Tg00ACk205Tg00Aek204Tg00BQk303Tg00C0k402Tg00Nok101Tg00l5j2;Tg02@Nj1~Tg01m5j3|Tg00fOj87Tg02A2j4LTg008Rj2uTg00STj2[Tg00Tfj3sTg00UOj2rTg023Oj2qTg00@=j6tTg01hJj3pTg00:Yj2vTg007>j2wTg00;Aj3nTg00Cbj3xTg00DEj3yTg02AYj2zTg00FWj2{Tg00G3j7RTg00GWj7lTg00H;k800Tg012Sj7WTg001:j6]Tg02Baj3kTg00H_R0f0R1'{p=:%41#4p=Ff4R2f3R3f2R4f1R5;5135p=2g006BR6f7R7f6R833f5R9=362A3634A3651';';';p=CA3670A3689A3623A3645/;1';';';p=E1134/J5=361p==A3651p=Y1145/J1p=gP6P5g00LDP1CNp=VP5g00I=R7g00I\R:P:g00J<R;P1g00J\R<FRp=P1`61p=<P4P7P:P:P;P5P1Flp=TP3P7P:P:P;P4P5P1L00p=UP8P7P:P:P;P9P7P:P:P;P6P2g00XKR=P3CNP<FRP4P7P:P:P;P6P5P=P1CNP<FRFWp=?P2P7P:P:P;P3P7P:P:P;P6P4P=P5CNP<FRP1FWp=0A3601p=H1;51,;4p=SP6P2P3P4P5P1E]p=AP6P2P3P4P5P1E]9k89p=D1645=531p=B%41#4#4#4p=K%:1R9g005]R8#4R<#4R=#4R>#4#FR?#4R@#4#8RA,I1RB'ORCg0272RD,G5RE%^>RF#oRG#ZRHg00W@RI#@#@RJ#@#@#@#@#@#@RK/X116F4RL=_GK33X06%8>R>/M>RM,1ERNPG1G4DRO,6FRPPG11O>S00,6FRQPG16F1RRPG111>RS,6FRTPG11S>RS,6FRUPG11S>RS,6FRVPG11S>RS,6FRWPG11S>,6F%\GRSD2D2D2D2A5GLSS0195GLS0295GLS0395GLS0495GLS0595GLS0695GLRX95GLRY53HX061MM>RZ,1ER[PGPPPGPQPG11OMS07,6FR\PGPRPGPTPGPUPGPVPGPWPSD2D2D2D2=3HYX061MZ>RW,1ER]PGPPPGPQPGP\PG11OZS08,6FR^PGPRPGPTPGPUPGPVPSD2D2D2D2=3HYX061MW>RV,1ER_PGPPPGPQPGP\PGP^PG11OWS09,6FR`PGPRPGPTPGPUPSD2D2D2D2=3HYX061MV>RU,1ERaPGPPPGPQPGP\PGP^PGP`PG11OVS0:,6FRbPGPRPGPTPSD2D2D2D2=3HYX061MU>RT,1ES0;PGPPPGPQPGP\PGP^PGP`PGPbPG11OUS0<,6FRcPGPRPSD2D2D2D2=3HYX06%}5%:41I4AS0='OP5P5%88RYP5%8<RRP5%98Rd#8ReP5%8=R=P5%9<#8R<P5%4d#8RfP5%9d#8RdGCGE1G2D1G>4PAP2C=[[^=6PHPH1>GP1>GLRg11OTS0>,6FRh=5GSS0?95GcS0@95GbS0A95G`S0B95G^S0C95G\S0D95GQPXPGPH\HRX%mGRiPiPPPLPX\G/QiRPPOP4P41G3DRD/JARj/Y1X06PO1G>0RkPAP4C=P6%j6Rl%i69h6lPjP3AgDkARkP6Pl%f6PkP3P1EeFdW>P1P0g00KXRk#\Rl%ZkRm1c65Rn%b6Ro%a6Rp1`60Rq20768R8'V,PpRrP6P8g00MkS0E%<ACN,PpRs5TpRt&06:RuPtCU205p;RtP1P4g00LkRvg00MKRw'Q20414=3vwdB03605H02Rwb2b3b4X56%:51I5A'O\C^56P1P3P4O2b1RCPlPm&016RvPoPpPpPqPqPpPpPq%<YRxPpPpPq%<RRyPpPpPq%<eRzPpPpPq%<=R{PpPpPq%<<R|PpPpPq%<fR}PpPq%<dR~F?D0D0D0D0D0D0PtPwb2b3b4A3600%HY%HR%He%H=%H<%Hf%Hd';3S3S3SP1b1O3PO1J1A,YjX061JOA,Q611O0%~ODAO21J4AROA|4ACRjFDG7PHPH1>GQPgQ0DQ06PGPXPiPiPQPLPPQ00P4P4PDP>PAP1C=X06P1PYPCPlPmPvPoPpPpPxPqPpPpPxPxPpPpPxPyPpPpPxPzPpPpPxP{PpPpPxP|PpPpPxP}PpPxP~F?D0D0D0D0D0D0PtPwb2b3b4PYPYPYPYPRPYPePYP=PYP<PYPfPYPdGCGEP1b1O3POPjFDG7PHPH1>G\PgQ0CQ05PGPXPiPiP\PLPPQ07P4P4PDPMPAP1C=X06P1PRPCPlPmPvPoPpPpPyPqPpPpPyPxPpPpPyPyPpPpPyPzPpPpPyP{PpPpPyP|PpPpPyP}PpPyP~F?D0D0D0D0D0D0PtPwb2b3b4PRPRPYPRPRPRPePRP=PRP<PRPfPRPdGCGEP1b1O3POPjFDG7PHPH1>G^PgQ0BQ04PGPXPiPiP^PLPPQ08P4P4PDPZPAP1C=X06P1PePCPlPmPvPoPpPpPzPqPpPpPzPxPpPpPzPyPpPpPzPzPpPpPzP{PpPpPzP|PpPpPzP}PpPzP~F?D0D0D0D0D0D0PtPwb2b3b4PePePYPePRPePePeP=PeP<PePfPePdGCGEP1b1O3POPjFDG7PHPH1>G`PgQ0AQ03PGPXPiPiP`PLPPQ09P4P4PDPWPAP1C=X06P1P=PCPlPmPvPoPpPpP{PqPpPpP{PxPpPpP{PyPpPpP{PzPpPpP{P{PpPpP{P|PpPpP{P}PpP{P~F?D0D0D0D0D0D0PtPwb2b3b4P=P=PYP=PRP=PeP=P=P=P<P=PfP=PdGCGEP1b1O3POPjFDG7PHPH1>GbPgQ0@Q02PGPXPiPiPbPLPPQ0:P4P4PDPVPAP1C=X06P1P<PCPlPmPvPoPpPpP|PqPpPpP|PxPpPpP|PyPpPpP|PzPpPpP|P{PpPpP|P|PpPpP|P}PpP|P~F?D0D0D0D0D0D0PtPwb2b3b4P<P<PYP<PRP<PeP<P=P<P<P<PfP<PdGCGEP1b1O3POPjFDG7PHPH1>GcPgQ0?Q01PGPXPiPiPcPLPPQ0<P4P4PDPUPAP1C=X06P1PfPCPlPmPvPoPpPpP}PqPpPpP}PxPpPpP}PyPpPpP}PzPpPpP}P{PpPpP}P|PpPpP}P}PpP}P~F?D0D0D0D0D0D0PtPwb2b3b4PfPfPYPfPRPfPePfP=PfP<PfPfPfPdGCGEP1b1O3POPjFDG7PHPH1>GhPgPSPSPGPXPiPiPhPLPPQ0>P4P4PDPTPAP1C=X06P1PdPCPlPmPvPoPpPpP~PqPpPpP~PxPpPpP~PyPpPpP~PzPpPpP~P{PpPpP~P|PpPpP~P}PpP~P~F?D0D0D0D0D0D0PtPwb2b3b4PdPdPYPdPRPdPePdP=PdP<PdPfPdPdGCGEP1b1O3POPjFDG71QHSG7G7G7G7G7G7G7G7b8PGPFPEPGPF11E>RjPGPFPNPGPFP[PGPFP]PGPFP_PGPFPaPGPFQ0;PSCBCBCBCBCBCBCBCBPG16F5RFPGPFPGPFPGPFPGPFPGPFPGPFPGPFPSD2D2D2D253He11a>PEPUP>PlPmPvPo%<>,Vq,PpPtPwb2b3b4%:>P1b1RvCLDA11_>PEPVP>PvCLDA11]>PEPWP>PvCLDA11[>PEPZP>PvCLDA11N>PEPMP>PvCLDA11j>PEP>P>PvCLDA1XKEA_GFKRF53He%^?RG16GERv'up-0R>1[6IRI1[6J9s6Ig00W_'r'q=5klRlPmPnPoPpPpP7P:P:P;P3EtR;9TprPu%9@#4#F#K#9#4#F#K#9#4#F#K#9#4#F#K#9#4#F#K#9#4#F#K#9#8R@#<9p68R8,Vq,PpCUPtPwb2b3b4X56W61O951G5@R@#:[^56^6>P1Q0=P4P5O3b1%:Ee%8?R?,vR1I0R%:?1wR?R4,I0[[%:RR0g00K<R9AnR?5UW7%:4\9^70PlPmPnPoPpATp;sPuP6P8Q0EAx6yGCN,PpCUPtPwb2b3b4X56X6>1O5B1I@4[^56^6>P1%:2P2P3O3b1b:b;1IE4e5yEDA1zKv=3HFeW9X<6o"). Qed.

(* [comment removed for export] *)
Lemma sb_byte_u : forall c : word, Z_to_bv 8 (bv_unsigned c) = Z_to_bv 8 (bv_unsigned c mod 256).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"] "h07__arithh14__ffh28__varmaph35__with41ch51zp;1p;2p;3p;4p;7p;6g002Yj10Tg003>j1GTg003\j1<Tg008Rj23Tg006`j1FTg01j5j21Tg00:?j32Tg005Cj24Tg00;ej1:Tg00<Ej17Tg00Noj16Tg00=Cj18Tg00=aj19Tg00>Lj25Tg00?Rj4ETg00G3j7DTg020Ej6@Tg00ACj2?Tg00Aej2>Tg00BQj3=Tg00C0j4ATg02Coj3BTg001:j6;Tg02Baj3CTg005]#0#0#0#0#0#0R0#GR1#<f0R2,31R3%00#0#FR0,13R4g006BR5P4f1R6,31/10=252X5514541140g00KXR4#:%74%65%85%95R4g00I=R1g00I\R7P7g00J<R8P4P1P7P7P8P51550g00XKg00H_R7,55CEg00J\FDE@1?48P2f2R8g00LkR4g00MKR1'41>28=241dA=576CAb1b2b3A2507g024d[P2b09B30E;3CW4o"). Qed.

(* [comment removed for export] *)
Lemma step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_or (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["FPX_2"] "h01bh12Hdh22Heh32Hfh43Hrdh52Hvh61mh73memh82pch92rdh:4regsh;3romh<3rs1h=3rs2h>4segsh?1vh@1wp;1p;2p;3p;4p;5p;6p;=g00<Ej1LTg002Yj12Tg00V[j1DTg003>j16Tg003\j17Tg000Nj2GTg00Y2j18Tg01;aj2CTg00a1j2=Tg00:?j30Tg01<cj1@Tg01=cj2?Tg01>Cj1>Tg02DPj4KTg006`j1JTg01?`j4ITg02E<j3FTg02E_j3<Tg01@@j23Tg01hmj29Tg01I<j1ETg02FLj34Tg01B0j2;Tg01JDj51Tg01LHj25Tg005Cj2BTg001:j6:Tg01KLj2HTg02GVl=ATg02Ha#Lg005]#2R0#D#6R1%20R0#2R2#2#2R3#2#6#7R4'GR5%62#7#8\4R2%63#7R3%71R6%83f9R7f7R8'Cf4R9,=330g00LkR3f5R:#@g01FXR;30g01G8R<g006BR='?R>#8f6R?#>P<P=g02I`P:P9f3R=CK%J0R0CI,=>30g00H_g02JL5F1R>9<1?=03;f<R</3?13<:'9=049g01Q5R@#ERAp,2fxRBP3P5f8RC=<1>R>f=R11318131?'9RD941Cn01000000200001;<0REf;RFf:RGD1,5@f0RHPBf>RI?47?1;10R0P<PFD1,5@RJ50AX6AP3P;PBP3P5PHPI13IC13I8'994I7n0100000020000P0P<PFD1,5@=0AJX03P4P:PBA4I7HP0P<PFD1,5@=0AJX04PBA41C:PEPFPGD1,5@,BAPDPHE:P>f1E:PBP1P<PFPGD1,HIPBPIP1P<PFPGP7PCP8P?P9P=f2M=AE:W5W4W1W2W3X?4X=6X<6W9W@X;2W7X84W:W>o"). Qed.
End FPX_2.


(* [comment removed for export] *)
Ltac av_or F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_or_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
  | step_simpl ]; vn.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

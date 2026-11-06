(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Export StartupTac RefMemcpyLib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import PropExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_SumsLib () := "C47Corelib7Program6Basics4flipC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilC46Stdlib5Lists4List=repeat_lengthK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib2AS5Hoare3at_C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib2AS7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5v_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C47Corelib4Init5Logic7f_equalK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib2AS<RefMemcpyLib4at_uC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthC47Corelib5Lists7ListDef6firstnC59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_allC56Stdlib6ZArith6BinInt1Z6to_natc59OSSVerify5KrLib2AS7SumsLib4memkC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec3rdnC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib2AS<RefMemcpyLib3subC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC59OSSVerify5KrLib2AS<RefMemcpyLib7sub_nthC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C59OSSVerify5KrLib2AS<RefMemcpyLib7rdn_subC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3minI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3minC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List=length_firstnC59OSSVerify5KrLib2AS7CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SumsLib2b_C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib2AS<RefMemcpyLib;store_ok_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib2AS<RefMemcpyLib>wbytes_extend'C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr06K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SumsLib7rd_src1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare7at_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8step_lbuC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize01c59OSSVerify5KrLib2AS7SumsLib>asanreflect_fxC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01c59OSSVerify5KrLib2AS7SumsLib6wr_dstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim:step_sb_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SumsLib<memk_extend1C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib2AS8PropExec8u8_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib5Lists7ListDef6repeatc59OSSVerify5KrLib2AS7SumsLib5msetkC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib2AS<RefMemcpyLib:wbytes_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:repeat_appc59OSSVerify5KrLib2AS7SumsLib<msetk_extendC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1ZAmul_pow2_bits_lowC46Stdlib4Bool4Bool<andb_false_rC59OSSVerify5KrLib2AS8PropExec>Z_testbit_highC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z4lxorc59OSSVerify5KrLib2AS7SumsLibAland_shl_disjointC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lxor_lorC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib2AS8PropExec6v_slliC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SumsLib@lor_shl_disjointC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib2AS8PropExec4v_orC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz07C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7mul_1_rC46Stdlib6ZArith4ZdivAZmult_mod_idemp_rC56Stdlib6ZArith6BinInt1Z7add_0_rK46Stdlib9micromega7EnvRing3Pol03C56Stdlib6ZArith6BinInt1Z9div_smallK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z9div_add_lC47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC47Corelib7Classes?RelationClasses;reflexivityC56Stdlib6ZArith6BinInt1Z6shiftrK46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02C56Stdlib6ZArith6BinInt1Z;le_preorderc59OSSVerify5KrLib2AS7SumsLib2M8C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesc59OSSVerify5KrLib2AS7SumsLib8M8_digitC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC56Stdlib6ZArith6BinInt1Z=shiftr_shiftrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc59OSSVerify5KrLib2AS7SumsLib;byte_eq_modC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_modK4ELinuxProcessSemantics5Riscv5Instr5instr0:C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7step_orC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K4ELinuxProcessSemantics5Riscv5Instr5aluop09K47Corelib4Init5Logic4True01".  (* [comment removed for export] *)
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint code_at (segs : list Segment) (base : word) (off : Z) (ws : list (bv 32)) : Prop :=
  match ws with
  | [] => True
  | w :: ws' => fetch_word segs (at_ base off) = Some w /\ code_at segs base (off + 4)%Z ws'
  end.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma at_fold : forall (a : word) d, Z_to_bv 64 (bv_unsigned a + d) = at_ a d.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) [] "h01ah11dp;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210p1001:p4p710R1p8p1001Xp4p710P1p8p10027p4p710P1p8g002Yj10Tg003>j14Tg003\j12Tg004?j21Tg0050j23Tg005J#0#0#0#0#0#0#4#2R1g005of1f0'1,31W1W0o"). Qed.

Lemma v_add_at : forall (a : word) z, (0 <= z < 2 ^ 64)%Z -> v_add a (Z_to_bv 64 z) = at_ a z.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) [] "h04__p1h14__x1h22Hah37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with91zh:2Hzh;1ap;1p;2p;3p;4p;6p;7p;8g002Yj10Tg003>j1XTg003\j1FTg006Mj1>Tg006kj2OTg007Hj22Tg007dj26Tg008?j25Tg008ij24Tg009Fj23Tg009lj37Tg0050j2=Tg00:Fj2WTg00:nj3UTg00;Rj1TTg00<2j1NTg00<Rj2LTg00=0j1KTg00=Nj1HTg00>9j2;Tg00>\j2GTg00??j4:Tg00?jj6ETg00@Nj1DTg00A0j2CTg00ARj2ITg00B>j3JTg00B]j4BTg00COj3ATg00D2j3MTg001:j6@Tg00Dhj2PTg004?j2QTg00E^j2?Tg00F:j7RTg00F^j7STg00GBj8VTg00GfR0f0R1'?p=1f1R2g00HDR3g00HcR4P4g00ICR5P1g00IcFRp=8f2R6P3P4P4P5P2P1FSp=9f3R7P3P4P4P5P6P2P1GVp=<g005JR8#0R9#0#0#0#0#0R:#XR;#FR<g005oR=%11R>%>9R9%>:R:'OR?,21R@'6P=P215;7RA/41,3;14A6,3;57<X9=15;6/42,3;,=<13;2RA,5;1W9:RB1209%1:120?[[RC%19RDg00JCREAU9:2UW2R:%1?\E^2DRDp-0REg00J_RF#TRG%NFRF1L=2RH%K=RI%H=RJP=1;=0g00KK1G=8R8C:,8JRKPJP3P4P4P5P7EER359J%D4R4PKC<1CJ5R5P1P6g00L2RKg00LRRL'=1I16=7KLdAJ=02CBR0b4b7b8X1=W016>2%12[^1=^0EP1f4R>/2?P>P7O3b3b5b6PBPCP:PDPGPFPHPIPJP=P8g00M21;=9=A=;C:,8JR;99J3P4P;C<P5P0b4b7b8X1=X0E162@122?[^1=^0EP1%1>P>P7O3b3b5b65M2E@1P6A1Q6257<eW:W9W;o"). Qed.

Lemma at_eq_u : forall (a : word) d e,
  (0 <= bv_unsigned a + d < 2 ^ 64)%Z -> (0 <= bv_unsigned a + e < 2 ^ 64)%Z ->
  at_ a d = at_ a e -> d = e.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) [] "h04__x1h14__x2h27__arithh36__sat0h46__sat1h51Hh64__p1h74__ffh88__varmaph95__with:2Hah;4__x3h<1zh=2Hdh>2Heh?1ah@1dhA1ep;1p;2p;3p;6p;4p;7p;8g002Yj16Tg003>j1eTg003\j1NTg008?j20j1FTg008ij21Tg006Mj1ATg006kj2MTg007Hj23Tg007dj27Tg004?j25Tg009lj3<Tg00MYj6dTg00:Fj2XTg00:nj3WTg00;Rj1UTg00<2j1TTg00<Rj2@Tg00N6j1OTg00NTj4BTg00=0j1LTg00=Nj1KTg00>9j2>Tg00>\j2;Tg00O2j3:Tg00??j48Tg00?jj6JTg00@Nj1ITg00A0j2HTg0050j2GTg00ARj2PTg00B>j3QTg00B]j4RTg00COj3STg00OUj4CTg00PNj6ETg00Pjj1cTg00QHj2bTg00Qij1]Tg00RHj2DTg00S1j3\Tg00SZj3YTg00TCj2ZTg00Toj3[Tg00UOj1VTg00E^j2^Tg00F:j7_Tg00F^j7`Tg00GBj8aTg00GfR0f0R1'^p=2g005oR2f1R3;<1p=4P3g00HDR4g00HcR5P5g00ICR6P1g00IcF_p=9f2R7P4P5P5P6P3P1F`p=?f3R8P4P5P5P6P7P3P1Gap==g005JR9#6R:#6#6#6#6#6R;#eR<#NR=10<7/13R>#2%A:R?%A;R;'MR@,3>'710<8/13R>#213>@'7f4R>/5815>75<=P=P2%F<f5R=/5>RA15=8RBP1Ed10<A10<B'4P2f6RB/5=,0<f7RA/5=,0<RC,41X<2P110<B/1=RDPBP=1X?;RE130?%2;130@[[RF%2?RGg00JCRHAW?;3UW:R;%2@\H^:GRGp-0RHg00J_RI#URJ%TIRKP21@27RLP3%O2CBRM%L2RN%K2ROP21>20g00KK1;29RP1;2:R:5:2RQC8,9ORRPOP4P5P5P6P>EJR45?O%I5R5PRC=1HO6R6P1P7g00L2RRg00LRRS'G1P17=<RSdAQ203CRR0b7b8b9X02X12W6RS1113RR#2/771137RT#2[^02^12^6HRUP1f9RV,0<RWf8RX'1RY/3@PXPWPBO4b2b3b4PEPFP;PGPJPKPMPNPOP2PQg00M21>2?=S2<C8,9OR?9?O4P5P?C=P6P0b7b8b9X02X12X6HR?13R@,7713T@[^02^12^6HRHP1%2YPXPWPBO4b2b3b4CCEE15B>,0<,4DP2PC10<X/1A/41X<2P110<ARC/1=RDPAP=PEPFP;PGPSPUP1f:RU,0<RS/1XR=/3@PXPSPBO4b2b3b4PEPFP;PGP?PHP1%2=PXPSPBO4b2b3b4CCEE11CB/4DPEPFP;PG%c9,b2g00V4RG#],D25\21D2G5Y2g00VS'Z=[IJPKP2PLP31@28CBPNPOP2%V9,;2R9=:2Pg00W?RNA:29:C8,9OP5P2PPPNP:C8,9OC=P6P0b7b8b9X02X12X;211711173'41437[^02^12^;2P1f;,0<PVPUP8O4b2b3b4b5b5b5W5W>W=XA2X@2W?o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["MEMK"] "p;1p;2g002Yj10Tg003>j12Tg003\j11Tg00Wfj13Tg0050j24Tg005J#0#0#0R0#0#0#0#2#1%20#1#3[p,4mem0'4o"). Qed.

  Lemma memk_n : memk n = wbytes mem0 dst bs.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["MEMK"] "h01lh11np;1p;2p;3p;6g002Yj10Tg003>j15Tg003\j13Tg00XHj26Tg00Wfj1>Tg00Xhj34Tg00YGj32Tg009lj31Tg00<2j1;Tg0050j2:Tg00Z=j27Tg001:j68Tg00Z\j19Tg00PNj6=Tg00[<j1<Tg00\0R0g005J#0#0#0R1#5#3R2p,2bsR3'6R4%01#0#0#5#3%>2[R1p,4mem0R5p,3dstR6f0R7=42332A2563R831X10%;2R0P3A2567=118X001:18A42431723E8p,1nR3#9p,4HlenE=%<3=118eo"). Qed.

  Lemma rd_src1 : forall k j,
      (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
      rdn segs (memk k) (at_ src j) 1 = Some [b_ j].
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["MEMK"] "h04__x1h14__x2h24__x3h34__p1h44__x4h54__p2h62H2h75Hlen0h87__arithh94__ffh:8__varmaph;5__with<4cstrh=2z2h>1nh?6__sat4h@1xhA2H3hB6__sat5hC2z3hD4__p3hE4__x5hF4__x6hG4__x7hH6__sat3hI1yhJ2H4hK2HahL4__p4hM6__sat6hN4__x8hO1ohP1zhQ2z4hR1HhS2H0hT2H1hU2HjhV2HkhW1bhX1jhY1khZ1lh[1mp%0p&0p;2p;1p;4p;3p;<p;8p;6p;9p;7p;Bg00E^R0j20Tg007dj22Tg006Mj1kTg008iR1j21Tg00\Ok109Tg002Yj1PTg003>k103Tg008?j2cTg006kk20JTg007HR2j23Tg003\j1xTg00<2k101Tg00Wfk10jTg004?j2^k10YTg00Qij1ATg00]Ij4]Tg00Z\R3j1gTg009Fk20]Tg00^=k406Tg00;Rk105Tg00Toj3NTg00^Yj2[Tg009lj38j1}Tg00_;R4j1BTg0050j2bTg00_[j1{Tg00`9l<\Tg00XHk200Tg00`^k20?Tg00aAk30>Tg00a^k40<Tg00bEk10;Tg00bjj2vTg00:Fk20aTg00:nk30`Tg00Pjk10_Tg00QHk20^Tg00S1j3rTg00RHk208Tg00=0k10\Tg00=Nk10[Tg00>9j2qTg00>\k204Tg00@Nk10ZTg00UOj1dTg00A0k20XTg00ARk20WTg00B>k30QTg00B]k40PTg00cLj4UTg00d7k80OTg00dTk40NTg00eLR5j2~Tg00N6k10ITg00edk30HTg001:j6STg00f`j2zTg00g7R6j2yTg00gQm90ETg00PNk60DTg00Xhk30CTg00YGk30BTg00hMj2`Tg00hdj2;Tg00i>R7j2oTg00i[k40ATg00j>k60KTg00jfk20LTg00COk30STg00OUk40TTg00kHk30UTg00kjm90iTg00[<k10hTg00lhk10gTg00mZk20fTg00n7m<0:Tg00SZj3hTg00TCj2tTg00<Rk20eTg00NTk40dTg00??j4ZTg00F:j7_Tg00F^j7iTg00O2k30bTg00GBj8fTg00n\j7sTg00?jk60cTg00o@lBuTg00GfR8f0R9'0p=5g005oR:f1R;;89p=M20f89p=I1b:9p=?P:g00\0R<P:P:P3f4R3P4f3R=g00off2R>P;P9N<0:p=mP<P:P:P:P4P4f5R?P3P=P>P;P9N<0:p=l1389p=C1098p=LA8:98p=KA8:>;,2=/;9p==208:9p=@Ah:;9p=9Ah:;9g00VSR@'tp=G1t9@p>07g00J_RAANA;97N>p=J1t;@=NA9p=<20e:9p=QP:P>P;P9H0dp=6204:9p=EP:P;g00M2R@P9CZp=pP>g00HDRBg00HcRCPCg00ICRDP:P;g00W?REP9CZg00IcRFF_p=RP=PBPCPCPDP>PBPCPCPDP;PFF_P9Fip=OP:P;g00KKRGP9CZp=eB0b:;9p=:P>PBPCPCPDP:P;PGP9CZPFF_p=4f6RGPBPCPCPDP?P3P=PBPCPCPDP>P;P9GfGfp=7P?PBPCPCPDP3PBPCPCPDP=P>FsP;P9Gfp=HP<P:P5P4P2g010SP?P3P=P>P;P9M<\p>0MAh:;99h:>p=DANA;9p=nP>PBPCPCPDP:P;P@P9CZPFF_p=FP;PBPCPCPDP9J0cp=XP>PBPCPCPDP;P9Fip=YP3PBPCPCPDP=PBPCPCPDP>P;FiP9Fsp=|11>;/09p=>P<P3P=P>P;P9ESp=TP<P<P<P:P:P:g0115P4P4P4P1g011UP?P3P=P>P;P9MBup>0GP<P:P6P4P0g0128P?P3P=P>P;P9M<\p>0FP:P:P:P:P:P:P1P9P;P>P1P=P3P?PGf7R1f8R6f9R@MBup=wP:P:P0P1P0PGP?P3P=P>P;P9M<\p=aP<P<P<P:P:P:g012ZP4P4P4P7g013:P?P3P=P>P;P9MBup>0@A8:;9,2>p=jP:P;PEP9CZp=VP=PBPCPCPDP>P;PBPCPCPDP9PFF_Fip=WP>PBPCPCPDP;P9Fsp>0=12;9,;>p>0212=>12;9';p>0RP=PBPCPCPDP>P;P9Gfp>0V%5;S00p,1nRB,0;'2Q00g005JRF#kRE,1>R7/0Bp,3srcR0$09%PFR2#PR5#PRH#P#P#PRI$03RJ/c0RK#5S01%k2RL%kIRI+0JRM,3KS02'2p,3dstRN$091cJNRO#5S0313OMS04'2&03HRP#xRQ$01RR$0jRSp,4segsRTp,4mem0RU1^0?RVg00V4RW#ARXC]PQ%gGRYp,2bsRZ20]P8RPH06&05QS055NQS06,[RS0798S9XOSP:%xJR[&0Y0R\P\%g?R]#BR^P?P[\:/b\1M^?%I?R\/M?P:P:%}:R_P9X@:R`P_1M;9#{XI:X@:P^P\P`P`%B9Ra#?X@<S08P]P\P`%I9X@:R\P?P?%??R]DmElP?P?P]M<\200QZR]%gBRb58<%B]Rc%IBRd'MReP<P:%}<P4P_%B;/MaA8<;920?;940>XI<X@<P]Pc%?cPbP\PBO1P`P\PBPB%?BDmR_M<\p,4HlenS09H0<R4Pe&0;]Rf%5cRc1v81%C1%I1RgP1%L1%Kg'2C=%I6P:1v8BRg%CBS0:PdPB%LBS0;%Kd'2C=RhPdP:20aLIRi%CL%5I%CM[[Rj%5LRkg00JCRlB0`LI;UWKRI%5M\l^KkRk%AXRl#ARm#ARn#@S0<&0_F-0^:Ro%@mRm5r:S0=208:WRW'9Rp'9Rq%@XRr/9WRs,GmS0>&07p&05ARp3J'<&01ARA%Q>Rt%Q=S0?76;&0\:Ru&0[:RvPvPvPv1q:8Rw%E2Rx'p204:FRy=RvxRzCOPvPv1exwARvywR{CO&0ZCRCPv1q:ER|,:xS0@%dFRF#ER}54vS0APCPvA4vwxS0BPCPzF7EH20XvDRDP9P>g00L2Rzg00LRR~'b20W9>=8z~dB0Q:8;H0PR~b9b:b;X0:X1:X2:%C;P9P;%L;%K9Rz'2C=107=S0C%5=1M=3[[[^0:^1:^2:P9PBf>S0DP?PGf;R7f<S0EO6b8b?bBbCbAb=b6b<b7CUL0O1^0^=8[VP[%BY,^0S0FPTPUP9PXC]PQ%g1R^PZPPH06Q055NQ,[RRP58SXW[PSPQPZPYPXH0NR[,[RA8S9PXOSPRQ061[R9=8SPXZRQ07,bSP[Pb1~^9X><1~Yb%IGR[/3dPYP[P`P\PGPG%?GDmS07PbPdP_J0MP4PePfPcPgPhPdP:f:R\,v8S06%C\%I\R8P\%L\%K8'2C=S0G%I7S0HP:PiPjPIPkp-0R8%@lRl/9rRr,GmRP%AnS0I#@Rn/GqQ0=19lWRl5Dn1nPp'<3JS0=PA&0I:RP%Q3S0J76=96t;S0KPuPvPvPv%dF#ERt9FvwARvyt1XvGRq=Yv{D|S0LPCPvPvPvAFvw}S0MARvx}PvPv1e}w1Xv1COS0ND|S0OPCPv1:t|=4v}S0PPCPvA4vwtS0QPCAFvyxF7F7PDP~b9b:b;X0:X1:X2:X4:X38W5%C=RtP9P=123zC=S0RPtP>P=%L=/2GC=RtA>?E3Rz%5GR{133?[[[[^0:^1:^2:^4:^38^58P9%K?f?S0S#LQ0SPBP?P=P3PGQ0Ef=S0SO:S0Tb8b?bBbCbAb=b6b<b7CUP]Q09DT:0HZYESPTPUQ0FPXC]PTPUP]P0PZPYPXp,4HsrcPb1z^X/y9X><1zYXS0F/yb11[ES0U/0dQ0FQ0UPYP[Q07PXPE%?ES0UJ0GPbPdP_J0FP4PePfPcPgPhPdP:Q06Q0GQ0HP:PiPjPIPkQ0=PAQ0KPuPvQ0LPCPvQ0OPCPvQ0PPCPvQ0QPC1:y|=4vxF7F7PDP~b9b:b;X0:X1:X2:X4:X38X58Q0R113ES0Q/0?S0P\{\z\t[^0:^1:^2:^4:^38^58Q0Tb8b?bBbCbAb=b6b<b7CUP]Q09DTN90EES1^0GRtP9J0Db6PTB0CQYZS0T:0BUNPVPXC]PTQ0TPUPNPVPX1`Y]S0R1cJtRt%BXRN;>ORU11OaS0O/0t';X><Pb1`^9#B,1OS0L/0t,;UX><P:11K?RU119NS0K/0O1`^b#B=>O9';XP:11UNR^/0OS0=1`YbS0F#BS0V,1ORt/0US0W';S0X11UERa/0OS0Y1o[dRz,1OR{/0US0Z';Q0=Q0WQ0YQ0ZP`10;9#{XI:X@:S0ZP^PaP`P`P`P:P:g013]11;9H0A#?X[:X>:S0YPUPU%?US0WPNPEP`P`Q08PXPEQ0UElM:wS0UPOPO%?ORNGaP`Q0ZPtP{P`P`P`Q0YPOPOPNQ0VPzP`P`Q08Q0FPzPYP[Q07PbPdP_J0@ElM:wS07PUPUQ0WGaJ0KP4PePfPcPgPhPdP:Q06Q0GQ0HP:20L9>S0W139>1o9>R_P910>9?j_>C=S0F1o;=S08P:PiPjPIPkQ0I#AR_#AR[#@Rz19nsS0I'GS0VQ0V%A[S0Y#AS0=#@R[%@_R_Ar:on5Dz'GS0[Q0[Q0</GrRNADnmlS0<,9[S0\$07Q0Y#@RmQ0I'GS0IQ0IAr:o_=Dzn,G[Q0=#A#@Q0\'9Q0<9D[mADz_s1nNp'<'<9JNN'<5JN3J3J3J3JPA%Q1S0V?63P%QGS0[76>%Q6?6?P?6=P76;PuPvPvPv%d5#ERN%EHRH5FvS0IPv%E5R5/VNCWPvA4vHNS0<Pv1V5HCWPCPvPvPvPv%PF#ERF,pwARvNFCOPv1Xv\S0\Pv1VNwCWPCPvPvPvPv%d2#ER2,pwARvH2CO1Xv7S0=ARvHwS0Y5YvPCPvQ0@=4v2PCPvQ0BPCPvPv1:}2=4vy1:y2=4v}PC1:yxR2/:|Rs=4v}1:}5=4v260=vEHF7EHEHEHPDP~b9b:b;X0:X1:X2:X4:XE:XF:XG:XN:X38X58131GP=P110G1?j=GC=%CG?j6GR[%K6Ro802@B02[7oQ0Q/01%5?RoA>1@?A>?@1';11G1R[?>E6A>6@[';[[[[[[^0:^1:^2:^4:^E:^F:^G:^N:^38^58P9Q0;fAR[#LP?P1P[PBP=POf@S0QPKP3PGP6Q0SQ0Dp,5HdisjO@b8bBbMbQbJbCbAb=b6b<b7CUQ0Xe1cJVS0XP0P?P4PePfPcPgPhPdP:PiPjPIPk19nrQ0>/npRr'<PAQ0J?6>PQ0?76;RVPuPvPvQ0M=YvqQ0NPCPvPvPv1ew51Xv6COPCPvPvPv1ewy1Xv@S0NCOPCPvQ0APCPvQ0BPCA4vw2F7F7EHPDP~b9b:b;X0:X1:X2:X4:X38X58XD8XL8%C>P3%L>P?H0R%53/21%5>/2@Q0P11?G#5\o[[[[^0:^1:^2:^4:^38^58^D8^L8P9Q02Q04%K=1M=BPOPBQ0EPKP3P1P6P@P\O=b8bHb?b=b6b<b7%5UeP4PePfPcPgPhPdP:PiPjPIPkPrPAPVPuPv1q:L>0S:JRJ9FvyRL9YvqS04PCPvQ0APCPv1:5}=FvJR5PCPv1:y}=FvJRyPCAFv2JF7F7PDP~b9b:b;X0:X1:X2:X4:X38139M,23RqQ0C11?3/3MR\11=?/3MRo113?R[/3M[[[[^0:^1:^2:^4:^38P9Q01POPBQ0EPKP6P@p,4HnwdS0Ep,4HnwsS01O9S02b8bHb?b=b6b<b713UMeH0TS0PESP]Q09DTQ0T-00QS0TB0UQYZRZDTP:PUQ0K/0MXP:10^MRU10aMP`Q0ZP^PaQ0UPMPM%?MRaGaP4PePfPcPgPhPdP:PiPjPIPkPrPAPVPuPvQ04PCPvQ0APCPvP5PCPvPyPCA4vsJF7F7PDP~b9b:b;X0:X1:X2:X4:X38Q0CA>[EM\o\\[\q^0:^1:^2:^4:^38Q02b8bHb?b=b6b<b7CUPUeQ0XQ0PESQ0RQ0O/0MX><PbQ0L/0MX><10tM10{MP`Q0ZPtP{Q07PMPMPaGaP4PePfPcPgPhPdP:Q06Q0GQ0HP:Q0WQ0FQ08P:PiPjPIPk19nW9Dz_RnADz_lR_19m_19mn/<p'<'<'<PAQ0[?63P%Q?76>Q0V?61P?6=P76;PuPvPvPvQ0IPv1VxNCWPvQ0<Pv1VxHCWPCPvPvPvQ0NPv1VH}CWQ0\Q0Y5YvPCPvQ0==YvLPCPv1:F|=4v}PCPvA4vwFPCPvPyPCPvP5PCA4v2JH0VF7F7EHEHPDP~b9b:b;X0:X1:X2:X4:XE:XF:XG:X38X58XD813G?P;PG10?G?j;?C=P6PGP=%KG,2@C=13>M,27A>1E?%5611?1/3M11@6/3MA>16M[[[[[[[^0:^1:^2:^4:^E:^F:^G:^38^58^D8P9Q03Q0;Q0:P?P1Q0QPKPBP=POP3P6P7Q0SQ0DQ0EQ01OAb8bBbMbQbJbCbAb=b6b<b7CUP]Q09DTQ0TPZDTN90iESbSbRPT&0h31^0=PXC]&0g=Q055NQ,[R58SeWTWUWVXX:XY:o"). Qed.

  Lemma wr_dst : forall k j m,
      (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      store_ok segs (memk k) (at_ dst j) m = true.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["MEMK"] "h01xh14__p1h24__x1h34__x2h44__x3h54__x4h61nh72H1h82Hah95Hlen0h:7__arithh;4__ffh<6__sat2h=6__sat3h>8__varmaph?5__with@4cstrhA5cstr0hB1mhC1yhD2z1hE2HjhF2HmhG1jhH1kp&0p;1p;2p;3p;4p;<p;6p;;p;Bp;7p;8g00_;R0j14Tg008iR1j22Tg00E^R2j20Tg002Yj1;Tg003>j1TTg003\j1oTg00XHj2hTg00Z\R3j1LTg00Xhj3_Tg008?j2KTg006Mj1JTg006kj2[Tg00mZj2YTg00_[k102Tg00i[j4~Tg009lj33j1OTg00`^j2eTg00aAj3dTg00`9l<MTg00a^j4aTg00bEj1ITg00bjj2^Tg007Hj2:Tg007dj29Tg00hdj2ETg00:Fj2]Tg00:nj3\Tg00Qij1ATg00RHj2=Tg00TCj2BTg00;Rj1ZTg00Toj3CTg00<2k103Tg00<Rj2XTg00N6k101Tg00NTj4VTg00=0k100Tg00=Nj1}Tg00>9j2UTg00UOj1yTg00>\j2?Tg00?jj6wTg00@Nj1pTg00O2j3FTg00COj3mTg00A0j2jTg0050j2QTg00ARj2kTg00B>j3iTg00B]j4lTg00cLj4STg001:j6NTg00Pjj1gTg00QHj2fTg00S1j3rTg014Al;sTg00[<j1tTg004?j2uTg015Aj4vTg00n7l<WTg00o@lBcTg00SZj3bTg00??j4GTg00F:j7zTg00F^j7{Tg00n\j7|Tg00GBj8`Tg00GfR4f0R5'0p=7g005oR6/Q5p=6P6g00\0R7P6P6P3f4R3P0f3R8g00off2R9f1R:P5M<Wp=xP7P6P6P6P0P0f5R;P3P8P9P:P5M<Wp=qP6P6P6P6P6P6P1P5P:P9P1P8P3P;f6R1f7R<f8R=f9MBcp=nP6P6P2P<P2P1P;P3P8P9P:P5M<Mp=PA3654p=DAb6:5p=5P6P:g00M2P5CGp=HP:g00HDR2g00HcR<P<g00ICR>P5g00IcFzp=1P6P:g00W?P5CGp=>P9P2P<P<P>P:P5F{p=@P9P2P<P<P>P:P5F|p=RP6P:g00KKP5CGp=<P8P2P<P<P>P9P:P5G`p=8%7:%4:R?,29p,1nR@'0p,4segsRAp,4mem0p,3dstRBg005JRC#;RD#;RE#;RF#T#oRGp,2bsRH'hRI%L3=_GHP8P9P7%L@RH%;F#;#;RF#TRG/KBRJ%45RK'2%JDRL%JFRF'[RM'0X67%4HRN,2JRO/0M1Y4@RP,2JRQ/0MP5X06RR10:5$02XC6X06RSPOPQPRPRPRP6P6g013]12:5C~#6XB6X66PJPJ%6JPNPPPRPR%6KX07PHPPPR1Y45X06RQP@P@%6@DxROEqRTM:nPMPM%6MGPA37IH%4IRU=36PRVP7P6%O7P0%O6A36?KA37:51e:53dXC7X07PIPU%6UPHPQP@O1POM<Mp,4HlenROCaRQPV%IIR?%7URU%I3R0%43#7RW1^4@RX1:4@RYA36P@'910@4RZ%DP'9'ER[PPP61]LFR\1:4L%7F1:4M[[R]%7LR^g00JCR_A\LF:UW8RF%7M\_^8^R^p-0R_g00J_R`g00V4Ra#ARb#ARc#ARd#A,=6Re1=6dRd1=6b1=6aRa'5Rb'5'5g00VSRf'B15da,5e/Bf%Z`Re5C`3C&03`RaP6P61X63P9&016CVP:1X68CVRg&006Rh%}6Ri1U64Rj%yC,?6Rk'H,1i1?6DRD/>k,1i5@iPiP2P<P<P>P1EwR11>Dj,1i5@i5Ri%p<R<Pi1?6CR2=F6k1U6L=m6GRL'H,1iP<Pi1?6ERE=F6k/HL,1iP<Pi1<jk,1iP<AF62DR2/<L,1iC8C8C8C81ji>R>P5P9g00L2RLg00LRRD'Q1k59=3LDdAi64:ClRlb;b>b?X26X36X46X56W11:49A36:9'9%D:,93'E12:8/:M12;3/:M%7;123;/0M[[[[^26^36^46^56^1_P5PZp,3src,KGP@P8PJP3p,4Hnwdp,4Hnwsp,2HnO9b:b<b=bDb7bAb@b9CSPIPOENp,4HdstP:P7PH%48,23/0KX67%49,28RK/0N10KPPRPSPKPK%6KPNPPPTGPPQPVP?PUP0PWPXP[PPP6P\P]PFP^%gC,f61=6c5r6/5bRb,5d/Bf1Bbf=C`e5C`PaPgPhPi1>kE,1i9@i11<Ej,1i1>kj,1i5@i5RiP<Pi1<2E,1iP<1<2k,1iC8C8P>Plb;b>b?X26X36X46X56X1_A3698,931084%D9'9'E12:9/031298/03[[^26^36^46^56^1_P5PYP@P8f:#4f;P3P=O7b:b<b=bDb7bAb@b9CSPIPOENM;sPA%t31uB8P9Cv=3LDeWFWEXB7XG6XH6o"). Qed.

  Lemma memk_extend1 : forall k,
      (0 <= k)%Z -> (k + 1 <= n)%Z ->
      wbytes (memk k) (at_ dst k) [b_ k] = memk (k + 1).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["MEMK"] "h04__x1h14__x2h24__x3h34__p1h44__x4h51xh62H2h72H3h85Hlen0h97__arithh:4__ffh;4__p2h<6__sat5h=8__varmaph>5__with?4cstrh@2z2hA2z3hB6__sat4hC2HahD1nhE1yhF1HhG2H1hH2H4hI2HkhJ6__sat6hK1bhL1khM1lhN1ohO2z4p%0p&0p;1p;2p;<p;3p;4p;8p;6p;7p;Bg006Mj1\Tg008iR0j2?Tg00E^R1j2<Tg002Yj1BTg003>j1mTg003\j1kTg004?k10?j2KTg00Z\R2j1DTg00_;R3j1ETg0050j2HTg009lj1sj31Tg00_[k10PTg00`9l<OTg00XHk20JTg00`^k20FTg00aAk30>Tg00a^k40<Tg00bEk10:Tg00bjj2PTg00:Fj2{Tg006kj2zTg00:nj3yTg00Qij1GTg00Pjj1uTg00QHj2tTg00S1j3_Tg00RHj2rTg00;Rj1qTg00<2j1pTg00<Rj2^Tg00NTj4]Tg00=0k10OTg00=Nk10NTg00>9j2nTg00>\j2QTg00@Nk10KTg00O2j3ZTg00UOk10ITg00A0k20GTg00ARk20ETg00B>k30DTg00B]k40CTg00cLj4RTg00d7j8VTg00Wfk10=Tg00Xhj3Jj2ck105Tg00YGj38k207Tg009Fk20;Tg00^=j4dTg00Toj3;Tg00dTk409Tg00f`k208Tg00N6k103Tg00g7R4j2eTg001:j6XTg016Aj6~Tg00eLR5j2fTg007HR6j2WTg00edj3|Tg00PNj6`Tg00[<j1iTg00lhk10@Tg00mZk20ATg00n7l<lTg007dj2oTg00hdk20BTg00SZj3xTg00TCj2hTg00??j4TTg00F:j7YTg00F^j7jTg00n\j7wTg00GBj8[Tg00o@lBvTg00?jk60MTg00GfR7f0R8'<p=@g005oR9f1R:;18p=920A78p=21H98p=CP9g00\0R;P9P9P2f4R2P3f3R<g00off2R=P:P8M<lp=UP;P9P9P9P3P3f5R>P2P<P=P:P8M<lp>0LP;P9P8P3P:P=P<P2P>f6R?f7R@f8RAM<Op=g1W78p=4A19:8,o=p=51<87p=:A1987p=A1o:8-0B=p=31r98p=IAx9:8p=0g00J_RBg00VSRC,h:;;8p=7P9P:g00M2P8CTp=LP9P:g00W?P8CTp=FP:g00HDRDg00HcREPEg00ICRFP8g00IcRGFYp==P<PDPEPEPFP=PDPEPEPFP:PGFYP8Fjp=6P9P:g00KKRHP8CTp=SP=PDPEPEPFP:P8Fwp=MP=PDPEPEPFP9P:PHP8CTPGFYp=NP<PDPEPEPFP=P:P8G[p>0HP?PDPEPEPFP>P2P<PDPEPEPFP=P:P8G[G[p=>P;P;P;P9P9P9g0115P3P3P3P0g011UP>P2P<P=P:P8MBvp>04P:PDPEPEPFP8J0Mp=aP;P9P4P3P1g0128P>P2P<P=P:P8M<Op>021h8Cp=bA;B:8p>01A;B:89;B=p>00P=PDPEPEPFP:P8Fjp>06P;P9P5P3P6g010SP>P2P<P=P:P8M<Op=}%@8g005JR6#\R3,?:p,1nR5'<P9%B6RD#B#BRC#B#B#BR1#m#kR4p,3dstR0$0?RGPG%D=RH#ERIP=P4\9/HG19I=%2=RG/9=P9P9%s9RJP8X59RKPJ19:8$0PXE9X59PIPGPKPK%E8RL#CX5;PHPGPK%28X59RGP=P=%C=RHDUJ0LP=P=PHM<O%mCRC#kRHp,2bsRM+0JRN%D5RO51;%ENRP%25RQ'9RR%s;S00PJ%E:/9LA1;:820F:840>XE;X5;RLPNPP%CPPOPGP5O1PKPGP5P5%C5DURSM9gp,4HlenRTH0<RUPR&0:NRV%@PRP1P72%42%22RW;52%:2%AW33%2>P91P75RW%45?5Q5%:5%AQ33RXPQP9%\DRY%\1R1'{RZ%4Y%@11zY1R[#4[[R\%@YR]g00JCR^AyY1:UWCR1%@[\^^C]R]g00V4R^#GR[#GRY#GR_#GR`#I%u6,t9Ra%I_R_5_9Rb1r9^R^'0Rc'0Rd%I[Re/0^,0_%qBRf,7c'7'7%pBRBP91^9=P:1^9<RgC]&0O9Rh&0N9RiPiPi1n97Rj1Q9DRD'L1Q96Rk/FD,=iRlC6PiPi1SDj1Fkj,=iRmC65Mi&0KEREPi1n93Rn9Z9D&0I6R6,Q9Ro5NiPEPiANijDPEPlH0HF>20GiFRFP8P=g00L2Rlg00LRRp'H20E8==1lpdB0D97:H0CRpb:b=b>X09X19X29%4:?58:%::%A8Rl331?=3Rq/<<%@<19<2[[[^09^19^29P8P5f;S01P>P?f9f:S02O6b9bBb<bAb7b@b6b?b8CRGV1K0I1K0=RI514P4%D<Rr#E,K0Rs&0=H\4Rtp,4mem0Ru%D2Rv=JHM780RwPHPvPM20;C7S03Cd%qHRC5;H7881?23Rx#D=JHM98u0Ry31XK4%pHR4PHPMPrP[H09Rz%Ev,K0=8w8=1tyXM4Pt208r[Rw=JHMR{98u0A1t8yXNtP4Pt207u0RyPyP{1?<3R{#DR|=JHMPt\4/HyP4P41cHw1cH|PMPMP;P4\4Ry&05HR}P}PwP|Py\;/H}A1;w|%2<R}/?3Ry%2{R~'9Q00PJPLPwPyPrP}PKPGP<P<%C<DURyP[P3%C3J04P|P~PKPGP{P{%C{DUM9gPUPRPVPP1?>3R{,P7%4{%2{RG;5{%:{%AG331??3#2P91P7@R7%4@%2@R3;5@%:@%A333R3%2ARGP9PWPXPQP9PZP\P1P]p-0RK%G`R`#IR~10ec'0%G`#IA_9a~10_^'0Ra'010~c/7f,7a'7'7PBP9P9&039P=1^92C]P:PgC]RgPhPiPiPi%B6,Q9R6,Lj1Fk6,=iC6R:PiPi1S6jPmC65MiPEPiPiPiAZ96nRa,Lj1FDa,=iC6PiPi1Saj1ai?RcC65MiPEPiANiaoRaPEPiANij6R6PEAZ9kn/FD,=iF>F>PFPpb:b=b>X09X19X29X49W3%4<Rn?58<R`%:<R|;3l%4x?5=x%:x;3>1<{2R{%@?Rw19x>[[[[^09^19^29^49^3KP8%A@f>P5P@P>P?PAf<RAf=O9b9b<bJbObHbAb7b@b6b?b8CRGV1H4MGVGVAJHrM98u0?8szPuP0PMPrP[P;PO1ev8XD;1erO1<}QPrP}PyPOPQPSJ02PUPRPVPPPWPXPQP9P7P3PGP9PZP\P1P]%IYRY/0e,0_#bR_10~d#b10Y^,0b,0~201_f'7400R_PBPgPhPiB06icm9Mi:R:PEPiPiPi1Ljo1FDo,=iC6PiPi1Soj1ai@C65MiR@PEPiPaPEPiP6PEANikDF>F>PFPpb:b=b>X09X19X29X49X3KX;KA3`2lR`A5n=<?3|?R|1<2>\w\{[[^09^19^29^49^3K^;KP8%A>%:APAP5P>P<P2P?Q02Q01O:R?b9bBb<bAb7b@b6b?b8CRPNPTEXE~EXPHPrPMQ03Cd=;HCP;PO1fv8XD;1frO1W}QPrP}PyPOPQPSE}PUPRPVPPPWPXPQP9P7P3PGP9PZP\P1P]P_PBPgPhPiP:PEPiP@PEPiPaPEPiP6PE1LkD,=iF>F>PFPpb:b=b>X09X19X29X49X3KX;K1W2>\w\{\|\`^09^19^29^49^3K^;KP?b9bBb<bAb7b@b6b?b8CRPNPTEX9|MrE`1K0<P8E`bF%i=&0@==;HC78I%iq51teWGWIXL9o"). Qed.

  (* [comment removed for export] *)
  Lemma mc_lbu : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
    RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned (b_ j)))) (v_addi pc 4) (memk k) rom).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["MEMK"] "h04__x1h14__x2h22H2h35Hlen0h47__arithh54__ffh66__sat3h76__sat4h88__varmaph95__with:4cstrh;1xh<2z2h=2Hah>1bh?2Hdh@2HehA2HfhB2HjhC3Hj0hD3Hj1hE2HkhF3HrshG3immhH1jhI2j0hJ1khK2pchL2rdhM4regshN3romhO2rshP1whQ1yhR1zp;1p;2p;3p;5p;4p;<p;7p;6p;?p;8g002Yj13Tg00UOj1PTg003>j16Tg003\j15Tg000Nj2xTg00Wfj18Tg017Dj2dTg00^Yj2@Tg009lj30j1ETg018Fj1[Tg019Fj2XTg019fj1VTg01:Wj5QTg006Mj1:Tg01;Cj4rTg01;cj2MTg004?j29Tg01<Xj2BTg008ij27Tg00E^j21Tg007dj24Tg00[<j1NTg00lhj1OTg00<2j1ITg01=@j2HTg00Qij1\Tg00]Ij4<Tg00;Rj1GTg00Toj3ZTg00XHj2YTg00Z\R0j1WTg00_;R1j1;Tg00mZj2FTg00`^j2UTg00aAj3TTg0050j2DTg00`9l<STg00a^j4wTg00bEj1vTg00bjj2uTg007Hj2CTg00hdj2qTg00:Fj2pTg006kj2oTg00:nj3nTg00<Rj2JTg00N6j1jTg00NTj4iTg00=0j1hTg00=Nj1fTg00>9j2LTg00>\j2KTg00F^j7eTg00@Nj1cTg00A0j2gTg00ARj2bTg00B>j3kTg00B]j4lTg00O2j3aTg01>7j5mTg001:j6=Tg01>nj3`Tg01?cl?_Tg00n7l<^Tg00??j4]Tg00F:j7sTg00GBj8tTg00GfR2f0R3'1p=2g005oR4g00\0R5P4P4P0f4R0P1f3R6g00off2R7f1R8P3M<^p=RP4P8g00KKP3C]p=?P8g00HDR9g00HcR:P:g00ICR;P3g00IcFsp=>P6P9P:P:P;P7P8P3Gtp=Ag005JR<#3R=#P#6R>%3=R?#3R@#3#3RA#3RB#6#5RC'x%6@#5R@#8\C%6A#5RA%5>R>%P<#3#3#6RD#5%8Ap,4segsREf8RF'df6RG,@A30g00L2RAf7RH#[g01@\RI30g01A<RJ/X4RK#8%VFPJP4g01AhPIPHPGf5RIDQ%:?Cr,@K30f<RK/MHp,3srcR?/9050C1BDH,7I=040%2Hp,1nRJ,1H'4%2G%:<RL,7H/1Jg01BTPEfARMf@f:RN#Nf?ROf>f=PKf;RP%OFPHPGPIPCf9RI,9?RG%I@RQ#8RRPE%NPRS1BDK,H3g00V4#\RTC<%OI%G@5Z@,@QRQ30X>CPC1BDPRP,7IRD,9?PEPSP3PTC<=0RQX>CP4PFPEPS19?3PTC<=0RQXR4PNPFp,2bs,Y@R@%WJRN505%;@RQ1F2JRR504RTP5P4%E5P1%E4%;8%;3504A05831U833TXQ5X;5P@PQ1D4QPN1F23X;4RNPJO1P3X;4PNPJPJ1D4JDRM<Sp,4HlenCwRNPT%v@R@%2QRQ1u2JR51C2JA04RJ'411J2A04R2'4'qR1PRP4%:=RS%:BRB'pRE1C2S%2B1oSBRU,C2[[RV%2SRWg00JCRXAnSB8UW=RB%2U\X^=WRWg00J_RX#GRU%IXRXP41J47P8%j4CiRS%h4RY%f4RZPZP9P:P:P;1L421K4<R<'?,>ZR91K4=R=,?<,>ZFeR[%c:R:P[CA1gZ;R;P3P7g00LRR[,DA1b37=0A[dAk428ClR2b5b8b9X04X14%23R[1138'4%28RA1187'4[^04^14P3PJPMPIO3b4b6b7b<b2b:b3PNPTP@PQP5P1PRP4PEPVPBPWPUPX1J48PYPZP9P:P9CAP;P2b5b8b9X04PA\[^04P3POPFO2b4b6b7b<b2b:b3PNPTP@PQP5P1PRP4PEPVPBPWPUPXPSPYPZ1L4L9a4</?=,>ZRZP:PZCAP;P2b5b8b9X04X14173L/18178L/17[^04^14P3PJPOPHO3b4b6b7b<b2b:b3DmPDP6E=1HGPA`?IPE=1MMKP0E=M?_WDWCWEWBWFW?W@WAXH4XI4XJ4WGXO>WLWPWNXKCWMo"). Qed.

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
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["MEMK"] "h01xh14__x1h22H3h32Hah45Hlen0h57__arithh64__ffh76__sat4h86__sat5h98__varmaph:5__with;4__x2h<1bh=4cstrh>1yh?2z3h@2HbhA2HdhB2HehC2HfhD2HkhE3Hk0hF3Hk1hG4Hrs1hH4Hrs2hI3immhJ1khK2k0hL1mhM1nhN1ohO2pchP4regshQ3romhR3rs1hS3rs2hT1vhU1whV1zp&0p;1p;2p;3p;4p;5p;6p;<p;Dp;7p;8p;Bg002Yj11Tg00UOj1RTg003>j17Tg003\j18Tg000Nk206Tg00Wfj1=Tg017Dj2lTg00^Yj2KTg009lj30j1PTg018Fj1]Tg019Fj2ZTg019fj1XTg01CRj4UTg006Mj1:Tg01;Ck404Tg01;cj2@Tg004?j26Tg01<Xj2>Tg008iR0j22Tg008?j2kTg009Fj2hTg00lhj1CTg00E^R1j23Tg00[<j1ATg00;Rj1ETg00Toj3_Tg00YGj3^Tg01D>j1\Tg01EFj5DTg01F;j2[Tg01=@j2<Tg01G7j2YTg0050j2BTg001:j6;Tg01>nj3WTg00Qij1VTg00XHj2TTg00Z\R2j1STg00_;R3j19Tg00mZj2QTg00`^k205Tg00aAk303Tg00`9l<NTg00a^j4yTg00bEj1xTg00bjj2sTg007Hj2?Tg007dj2MTg00hdj2rTg00:Fj2qTg006kj2pTg00:nj3oTg00<2j1nTg00<Rj2HTg00=0j1jTg00=Nj1iTg00>9j2FTg00>\j2GTg00??j4ITg00@Nj1gTg00A0j2mTg00ARj2fTg00B>j3eTg00B]j4dTg00_[j1cTg00i[j4tTg00N6j1vTg00NTj4wTg00O2j3aTg00cLj4`Tg01H?j5zTg01I5lD{Tg01Ioj3|Tg00PNj6}Tg00n7l<OTg00F:j7~Tg00GBk800Tg00o@mB01Tg00GfR4f0R5'3p=4g005oR6/B5p=5P6g00\0R7P6P6P2f4R2P3f3R8g00off2R9f1R:P5M<Op>02P:g00HDR;g00HcR<P<g00ICR=P5g00IcF~p=LP8P;P<P<P=P9P:P5L00p=JP7P6P6P6P3P3f5R;P2P8P9P:P5M<Op=uP6P6P6P6P6P6P0P5P:P9P0P8P2P;f6R0f7R>f8R?f9R@NB01p=bg005JRA#1RB#R#7RC%1BRD#1RE#1#1RF#1RG#7RH#8RI+06%7ERE#8RJ#=\IRK%7F#8RF%8CRC%RA#1#1#7RL#8%=Fp,4segsRM/l?1KF030g00L2RF%]>g01@\30g01A<RN/Z6RO#=%X?PNP6g01AhP>P0P;CU%:DRDH04,KO30f<RO/@?p,3dstRN/6250I1>L>,2;=060f>RP/@@=0I;1kH0,hE%C?50J%4@f:RE%:ARH'2p,1nRQ'3PKf;RR#ARS16NRRT%CRRU%EJ5_J3^g01JkRV#\g01BTRWfCRXfBRY%AOfARZDD,[MPWPX1<YDP5PZDD,YV30XNKPWPMPYPZPSf@f?PPf=RSPOPTP@PUP?P>P0PI16NER01>LS,<516NORS50IX<IPI1>LORO,2ERL,6NA0I5SX<IP6PR16N5=0ISXV61BITPLP2E;1<0OAWNEOE;1@YPP;E;P8P9PRPRg00V4#VR8p,2bs,TJRJ%SQR;507%9JRP1Q4QRO506REP7P6%P7P3%P6%9:%95R3506A07:5205:5403X>7X07PJPP%5PP;1Q45X06R;PQO1P5X06RNP;PQPQ%5QR;I02M<Np,4HlenCyR0PE%xJRJ%4PRP1s4QR21?4QA06OQ'M13Q4A06O4'M'rRLPOP6%:BRT%:GRG'qRS1?4T%4G1pTGRU,?4[[R@%4TRZg00JCRMAoTG:UW3RG%4U\M^3ZRZg00J_RM#ERU%nMRM1H6:%j6RT%i6RWP61F64g00KKRK1G6ARACI,LWRV%g<R<PVCJ1mW=R=P5P9g00LRRV,BF1f59=0FVdAe64:CdR4b6b9b:X16%45%4:[^16P5PYP?O2b5b7b8b?b2b=b4R?%4Re%98RV,2RRF/3QRD12RHRX/3QP6P6P1PNP113:5#cX>6X06PFPXPNPNPNP6P6g013]12:5Ct#5XL6XM6PRPR%5RPVPHPNPN%53X07P8PH%5HEuM:bPQPQP;M<NP0PEPJPPP2PLPOP6PSP@PGPZPUPMP61H69P:%v6CwPTPWP61F6H9a6APK1G6BCI,LWRWP<PWCJP=P4b6b9b:X16X;6125H/3:12:H/39[^16^;6P5PQPYP>O3b5b7b8b?b2b=b4R>C`PDeDzMD{%AXA|R?>E}WFWEW@WHWDWGWAWBWCXTIXK6XJ6WIXSCWRWUWQXOIWPo"). Qed.

End MEMK.

Lemma sb_val_b : forall bs j, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned (b_ bs j)))) = b_ bs j.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) [] "h04__p1h14__x1h22Hah37__arithh44__ffh58__varmaph65__with71Hh86__sat0h96__sat1h:2bsh;1jh<1zp;1p;2p;3p;4p;6p;7p;8g002Yj10Tg003>j1?Tg003\j1HTg00<2j1:Tg00lhj24Tg01L2j1RTg008?j23Tg006Mj19Tg007Hj22Tg007dj28Tg009Fj2=Tg009lj3>Tg01Lkj2XTg00;Rj1VTg00<Rj2UTg00=0j1QTg00=Nj1NTg00>9j25Tg00>\j2LTg00??j47Tg00?jj6GTg00@Nj1FTg00A0j2ETg0050j2ITg00ARj2DTg00B>j3JTg00B]j4KTg00:Fj2CTg006kj2BTg00:nj3MTg00COj3ATg00D2j3OTg001:j6PTg00E^j2@Tg00F:j7STg00F^j7TTg00GBj8WTg00GfR0f0R1'@p=1f1R2g00HDR3g00HcR4P4g00ICR5P1g00IcFSp=6f2R6P3P4P4P5P2P1FTp=<f3R7P3P4P4P5P6P2P1GWp=;g005JR8#0R9#0#0R:#?R;#HR<#:g005oR=1421R>#R13;>R>#1%0:#0#0R:#0#0#9R?,2>'8P=1462R>,3;R@1=;11476RA5><X<=1X;>%?:R>1=>@'3p-0R<g00J_RB#VRC%:BRB1U=2RD%Q=RE%N=RFP=15=0g00KK1L=8R8C7,6FRGPFP3P4P4P5P7EGR35<F%F4R4PGC;1EF5R5P1P6g00L2RGg00LRRH'I1D16=>GHdAJ=02CKRHb4b5b6X1=W0%11/82%12[^1=^0<P113;ARA/2?PAP2O3b3%99R9%9:R:'C1209%1:1B9:RA,20[[%19R0g00JCRGAM9:2UW2%1A\G^20PCPBPDPEPFP=P8g00M2RE15=?C7,6F9<F3P4P=P8PE15=9=A=>C7,6FC;P5PHb4b5b6X1=X0<121?,82122A[^1=^0<P1f5f4'4,3;R;#1P;P7O3b3b8b95O@EPb7W;W:o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["MSETK"] "p;1p;2g002Yj10Tg003>j12Tg003\j11Tg00Wfj13Tg0050j24Tg005J#0#0#0R0#0#0#0#2#1%20#1#3[p,4mem0'4o"). Qed.

  Lemma wr_s : forall k j m,
      (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      store_ok segs (msetk k) (at_ s j) m = true.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["MSETK"] "h04__p1h14__x1h24__x2h34__x3h41xh52H1h62Hah77__arithh84__ffh94__p2h:6__sat2h;6__sat3h<8__varmaph=5__with>4__x4h?4cstrh@1mhA2z1hB2HjhC2HmhD1jhE1khF1nhG1yp;1p;2p;3p;4p;;p;<p;Bp;6p;7p;8g00_;R0j1:Tg008iR1j22Tg00E^R2j20Tg00Z\R3j1STg002Yj15Tg003>j1MTg003\j1cTg01M]j3^Tg008?j2[Tg006Mj1JTg006kj2XTg00mZj2ITg00_[j1|Tg00i[j4zTg00bEj1eTg00bjj2dTg007Hj2?Tg009lj36Tg007dj24Tg00hdj2FTg00:Fj2\Tg00:nj3ZTg00Qij1ETg00RHj2<Tg00TCj2=Tg00;Rj1YTg00Toj3@Tg00<2j1WTg00<Rj2DTg00NTj4HTg00=0j1VTg00=Nj1UTg00>\j2BTg00UOj1{Tg00>9j2RTg00@Nj1yTg00O2j3QTg00COj3uTg00??j4GTg00A0j2qTg0050j2NTg00ARj2oTg00B>j3nTg00B]j4gTg00cLj4LTg00Pjj1fTg00QHj2hTg00S1j3iTg00N6j1jTg014Al;kTg01N<j1lTg004?j2mTg015Aj4bTg00n7l<OTg00o@lBaTg00`9l<`Tg00SZj3sTg00?jj6tTg00F:j7_Tg00F^j7wTg00n\j7xTg00GBj8]Tg00GfR4f0R5'0p=7g005oR6/N5p=8P6g00\0R7P6P6P3f4R3P0f3R8g00off2R9f1R:P5M<Op=vP7P6P6P6P0P0f5R0P3P8P9P:P5M<Op=rP6P6P6P6P6P6P1P5P:P9P1P8P3P0f6R1f7R;f8R<f9R=MBap=pP6P6P2P;P2P1P0P3P8P9P:P5M<`p=PA6654p=CAs6:5p=3P:g00HDR2g00HcR;P;g00ICR>P5Etp=TP6P:g00W?P5CGp=AP:P2P;P;P>P5g00IcF_p=1P9P2P;P;P>P:P5Fwp=>P9P2P;P;P>P:P5Fxp=KP6P:g00KKP5CGp=9P8P2P;P;P>P9P:P5G]p=;%7:%::,29p,1nR2'0p,4segsR?p,4mem0p,1sR@%S2RAg005JRB#5RC#5RD#5RE#M#cp,1b%S33^P8P9%5E#5#5RE#MRF/[@RG%:ARH'2RI%JCRJ%JERE'XRK'01I42RL,2GRM/0KP5X46RN10:5#|XG6X46ROPIPMPNPNPNP6P6g013]12:5Cz#8X@6XF6PGPG%8GPHPLPNPN%:5#8X47PAPLPN1I45X46P2P2%82DvErRAM:pPKPK%8KGP%e9RM%:9RI#7RP1d42RQ1?42RRA66L2'41024RS%CL'4'FRTPLP61\JERU1?4J%7E1?4K[[RV%7JRWg00JCRXAZJE:UW6RE%7K\X^6WRWp-0RXg00J_RYg00V4RZ#ER[#ER\#E,<6R]1<6\R\1<6[1<6ZRZ'3R['3'3g00VSR^'=13\Z,3]/=^%YYRZ5@Y3@%WYR_P61D69P:1D68R`CH%V6Ra%U6Rb1Tb01B6CRC%{B,B6R0'A,1b5>b1Tb1Rc1R64Rd,AC,1b5>b5Kb%y;R;PbP61B6BRe=Q60g00M21R6J=u6FRFCG,1bP;Pb19d0,1bP;AQ6eCRe/9F,1bC;C;C;1qb>R>P5P9g00L2RFg00LRRC'N1o59=6FCdAn64:CgRJb8b<b=X16X26X36X0XW9A66:9,48%C:,43'F12:8/?K%731283/0K[[[^16^26^36^0X^9XP5PSPRP2P8PGP3p,3Hnwp,2HnO8b7b:b;bAb5b?CLp,3HokP:128IRI/0H10ILPNPOPIPI%8IPHPLPAGPPMPPPQPTPLP6PUPVPEPW%fB,h6=i6\/3[R[,3]/=^1=[^=@YZ5@YP_P6P61D63P9%j6CHP:P`CHPaPb1B6DRD,A0,1b9>bc19Dd,1b1A0d,1b5>b5KbP;Pb19eD,1bP;19e0,1bC;C;P>PJb8b<b=X16X26X36X>6X0XA6698,431084%C9'4'F12:9/031298/03[[^16^26^36^>6^0XP5PRP2P8%:<P=P3P1O7b7b:b;bAb5b?CLM;kP?%l31m@8P9Cb=6FCeWCWBX@7XD6XE6o"). Qed.

  Lemma msetk_extend : forall k m,
      (0 <= k)%Z ->
      wbytes (msetk k) (at_ s k) (repeat b m) = msetk (k + Z.of_nat m).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["MSETK"] "h01xh14__p1h24__x1h34__x2h42H1h52Hah67__arithh74__ffh86__sat3h98__varmaph:5__with;4__x3h<4__x4h=1nh>1yh?2z1h@1HhA2H2hB2HkhC6__sat2hD6__sat4hE4cstrhF1khG1lhH1mhI1ohJ2z2p&0p;1p;2p;3p;<p;4p;8p;6p;Bp;7g00Z\R0j1ITg00f`j2[Tg00_;R1j1<Tg008iR2j2;Tg009lj33j1bTg00`^j2kTg00aAj3gTg0050j24Tg00`9l<dTg00bEk106Tg00bjj2QTg007dj22Tg00E^j2ATg00hdj2DTg002Yj1=Tg006Mj1XTg00:Fj2pTg006kj2oTg00:nj3mTg00Pjj1lTg00QHj2jTg00Qij1CTg00S1j3JTg00RHj2WTg00;Rj1fTg00<2j1VTg00N6j1eTg00<Rj2STg00NTj4MTg00=0k10<Tg00=Nk10;Tg00>9k20:Tg00UOk108Tg00>\j2KTg00??j4UTg00@Nk105Tg00O2j3`Tg00A0k204Tg00ARk203Tg00B>k302Tg00B]j4zTg00cLj4^Tg003>j1]Tg003\j1\Tg00Wfj1yTg01M]j38Tg00YGj35j2Zj1rTg004?j2Bj1qTg01O1j3xTg00XHj2sTg00_[j1tTg00d7j8PTg0027j3wTg001:j6OTg01ONj4nTg01PMj4{Tg00PNj6|Tg01N<j1YTg00mZj2}Tg00n7l<_Tg00o@lB~Tg007Hk200Tg00SZk301Tg00TCj2NTg00Toj3TTg00F:j7cTg00F^j7iTg00n\k707Tg00?jj6hTg00GBk809Tg00GfR3f0R4'Ap=>1}34p=6g005oR5f1R6;34p=1P5g00\0R7P5P5P0f4R0P1f3R8g00off2R9P6P4M<_p=LP7P7P7P5P5P5g0115P1P1P1P2g011Uf5R2P0P8P9P6P4MB~p>0=20034p=9A3543p=F1W54p=@B01564p=0g00J_R:g00VSR;,N91N6;=T:43Tp=HP6g00HDR<g00HcR=P=g00ICR>P4g00IcR?Fcp=:P9P<P=P=P>P5P6g00W?P4CUP?Fcp=7P9P<P=P=P>P6P4Fip=GP5P6g00KKP4CUp=EP9P<P=P=P>P6P4K07p=RP6P<P=P=P>P4Ehp=aP8P<P=P=P>P9P6P4L09p=?P7P5P5P5P1P1P2P0P8P9P6P4M<_p=u1N6;=T:4p=v%>6R;%I9R</[6R?%<6R@,;9RA#IRB537RC%69RD/;@RE%6ARF'1P7P5%b7P1%b5R1%<4RG,1@A37641k643gX>7X07P?PEP<PDP4X05RD%64X05R<P9P91459DLP6P@145@J0=PBPFPDP<PAPA145ADLM<d&066%>@%<9,;8R@,Q3%9@%6@RF/1@'21A@3%FF'2'D%<8,;0#6P51Q32%92%62RF/12'21A23%FF'2'Df6RF#6P5g005JRB#=RE#XR?%=E#=RH#=#=#=RI#XRJ'pRK%9?%>J1o?JRL#9[[RM%>?RNg00JCROAm?J6UW5RJ%>L\O^5NRNp-0RO%lB,j5RLg00V4R?#CRP#CRQ#CRR#CRS#CRT#@RU5J5%@RRR%@QRQ1W5?R?'0'0'0RV%@SRSAJ5LRRW%@P/0?RP'0'0RX,0UAJ5LS10R?'0RY,0U10W?,0SRS10US%CT#@/0V%f:RV3H5HY5HX3H%V:R:P5P5%e5RXP91S50CMP61S58CM&0<5RY&0;5RTP520:53RSg00M2&08BRU#=,K5RWCU,:T1K5BRB=7TW5GT1EWS,:TA7TBS5GT5RT&05=R=PT1aTF1K5URU1K5ERE9`5WRZ57T5GT1EZS,:TA7TUS5GT5RTP=PT1ESE,:TP=PT1ESW,:TP=A`5BE=7TUC?C?C?C?204T>R>P4P9g00L2RUg00LRRW'420349=3UWdB02536CzRWb7b9b:X25X35X;5X<5W1%98RU1148'21A83RZ%F4'2'D1;09R[,18,221A[3%F8'2'D%>8%>F1;02/1F[[[[^25^35^;5^<5^1OP4f:R[f9#<R\';#9P[P2P\P8P0PFf7f8R\O9b6b8bDbJbAb?b4bEC^PCP7%I8RC/[9R2%]I#\RI%]H#\RH#y[R[p,4mem0R]p,1sR^p,1bR_%I058H35R`1B^0A8H_8Ra35RbA8H_495]^33X=7%VHRcA8H_CRdA8H_9Re5xHRfA5]^493[bXGcP[A5]^dRg1sHdRh#<,B^;5eA3[b4XI[P7PC1B^G=5`a93[bX=7PcP[1B^8Rb,Zg%<CRa,B^R`,ZgPePePIP[\cRi%rgRgPgPbP`Pi\I/4gP5PI%q^RgPgP8PaPI\5/4g118a%68Rg,18P5P5P1PDP11164R1#tX>5X05P8P81458RIPaPgPDPD145GX07PCPgPDP<P8P8PIDLEuM<d1Q3811g8,2U%Fg,2Z'D%60P5PKPMPJPNAJ5LQ/0?R?,0R10QP1v?V3HP:P51S59P6PXCMPYPT1aT0A7TEB5GT1EBS,:TA7TES5GT5RTP=PT1ESB,:TP=A7TBEC?C?P>PWb7b9b:X25X35X1O12911A43%F6'2'D1198\;[^25^35^1OP4%9\P8P\P0PFO5b6bCb8b?b4C^GPGP14ceGPPhAwH_CEOA5]^fPdPeP]P^CnEOA8H_2PHP_PCP9C{EO%I@P4E|b@%Y91B^9A8H_635%YA53[eWBXH7XF5o"). Qed.

  Lemma msetk_extend1 : forall k, (0 <= k)%Z -> wbytes (msetk k) (at_ s k) [b] = msetk (k + 1).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) ["MSETK"] "h02Hkh11kp;2p;1p;3g00E^j22Tg00Qij11Tg01Plj30Tg005og00Gff0R0'2f1g00V4#1;00W0W1o"). Qed.
End MSETK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.land (a * 2 ^ k) b = 0%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) [] "h04__x1h14__x2h21bh37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with92Hah:2Hbh;2Hhh<2Hih=2Hkh>2Hlh?1ah@1ihA1khB1op;1p;2p;3p;4p;7p;6p;8g002Yj1]Tg006Mj1KTg006kj21Tg007Hj22Tg007dj2<Tg01Qhj25Tg01REj2?Tg01Rcj20Tg01SDj26Tg009lj37Tg01Sbj2DTg00E^j24Tg00hdR0j2\Tg0050j2ATg00:Fj2VTg00:nj3UTg00;Rj1TTg00<2j1PTg00<Rj2@Tg00N6j1OTg00NTj4JTg00=0j1ITg00=Nj1HTg00>\j2>Tg00??j4;Tg00@Nj1GTg00A0j2LTg00ARj2FTg00B>j3ETg00B]j4MTg01TGj4NTg01U2j1QTg00>9j2CTg00F^j7RTg01URj6STg01VQj1[Tg01W1j3ZTg001:j6BTg01WTj3WTg00F:j7XTg00GBj8YTg00GfR1f0R2'4p=3g00L2R3g01@\R4772p==f1R5g00HDR6g00HcR7P7g00ICR8P2g00IcFXp=9f3R9P6P7P7P8f2R:P5P2GYp=8P3P4P9P:P5P2EBp=:g005oR;%3:%35R<%39g005JR=#]R>#KR?/1:,29'<f5R@11?9'5f4RA'?%32RBP3f7RC11?@'5RD/05f6RE/05'6101:9732X23f8RF11?E'5/0:10C:'6=732X231D5@125@14@5'\P012:E14E:f9R011?C'5/0910F9'6#=P2129Cf:RG/0@,62#=X231A3411?F,5G/0AR4PGPFPA1V?FRH121?%3011?G,21[[RG%3?RIg00JCRJf;RK=U?5UW9RL11?KRM#3\J^9IRIg00J_RJ#TRN%PJRJP;1@;:P5%O;CJRO%I;RP%H;RQP;1>;=R=g00M21>;>R>C;,9QRR%G7RSPRC81LQ8RTP2P:g00LRRU,A31F2:=73UdAE;15CMRUb4b7b8X0;X1;1225RV125:RW[^0;^1;P2PKPCP9O3b3b5b6CNC:W>P2O114C911?0,5K/0@/62#=X23%Q4100APFP0PAPHPGPLPIPNPJ1@;5PPPQP;1C;1g00KKRAP=C;,9QR4PSP4C8PTPUb4b7b8X0;P<\B^0;P2PKP0O2b3b5b6PHPGPLPIPNPJPOPPPQPQP6P7P7P8P4PRFRRRPSPRC8PTPUb4b7b8X0;X1;1<BV1<<W[^0;^1;P2PMf<PFO3b3b5b6PHPGPLPIPNPJPOPPPQP;P=PAP>C;,9QRQPSPQC8PTPUb4b7b8X0;X1;1425145:[^0;^1;P2PCPKP9O3b3b5b6ESC:W;P2O1n200100000021000011000bB1015%[5C:1?DE/05AZDE5EBW<X@;7W1W:W=W9XA;X2;W?o"). Qed.

Lemma lor_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) [] "h04__x1h12Hah27__arithh36__sat0h46__sat1h54__ffh68__varmaph75__with84__x2h92Hbh:2Hkh;1ah<1bh=1kh>1zp;1p;2p;3p;4p;7p;6p;8g002Yj1WTg006Mj1CTg006kj22Tg007Hj21Tg007dj23Tg01Qhj2:Tg01X7j2BTg008ij25Tg009lj39Tg00:Fj2?Tg00:nj3=Tg00;Rj1<Tg00<2j1VTg00<Rj2;Tg00=0j1UTg00=Nj1LTg00>9j2KTg00>\j27Tg00??j48Tg00@Nj1FTg00A0j2DTg0050j2ETg00ARj2ATg00B>j3GTg00B]j4HTg00N6j1@Tg00NTj4ITg00F^j7JTg01XUj6>Tg01YVj3MTg01Z@j4NTg01Z\j2OTg01[9j3PTg00PNj6QTg00E^j2RTg00F:j7STg00GBj8TTg00GfR0f0R1'Rp=0f1R2g00HDR3g00HcR4P4g00ICR5P1g00IcFSp=4f3R6P3P4P4P5f2R7P2P1GTp=6g005oR8%07%02R9%06g005JR:#WR;#CR</27,16'3P8f5R=12<6':R>f4R?'BR@f6RA12<?':/5=9981X>8P815>?P@P=P?P61?<6R@110<%0?12<=,10[[RB%0<RCg00JCRDA=<A2UW1RE12<AR<#0\D^1CRCg00J_RD#<RF%VDRD1;82%U8RG%L8RHP81K80g00KK178:R:C8,4HRI%F4RJPIC61DH5RKP1P7g00L2RLg00LRRM'E1A17=9LMdAG802CHR0b5b6b7X08RM%01RLP9[^08RNP1f8P=O2b2b3b4P@PBPEPCPMPNP1PAP?O2b2b3b4P@PBPEPCPFPDP81;87P2%@8CIPGPHPHP3P4P4P5PIP8P:g00M2178;C8,4HFJRHPJPHC6PKP0b5b6b7X08X881112,3L1127,39[^08^88P1P<f7P6O3b2b3b4E>R69M>?CN1O>?AP>?6EQW9W:W1X=8X<8W;o"). Qed.

Lemma v_slli_mul : forall (x : word) k, (0 <= k)%Z -> v_slli x k = Z_to_bv 64 (bv_unsigned x * 2 ^ k).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) [] "h04__x1h12Hkh27__arithh34__ffh48__varmaph55__with61kh71xh81zp;1p;2p;3p;4p;7p;8p;6g002Yj10Tg003>j1MTg003\j1=Tg00E^j24Tg008?j27Tg006Mj1FTg006kj25Tg01Qhj26Tg009Fj22Tg009lj31Tg0050j23Tg01[[j28Tg00;Rj19Tg00<2j1LTg00<Rj2KTg00=0j1JTg00=Nj1ETg00>9j2BTg00>\j2?Tg00??j4>Tg00F:j7@Tg00@Nj1ATg00GBj8<Tg00A0j2CTg00ARj2DTg00B>j3;Tg00B]j4GTg01\;j3HTg001:j6:Tg01\dj2ITg005JR0#0R1#0#0#0#0#0#MR2#=R3g005oR4g00GfR5f0R6'4R7P4f2R8,72R9%F1R1f1R:'5'6R;1226f3,721518'6,22513X84122;R;,33189:g00J_R2#9%L21K4:%J4%E4R2g00HDR1g00HcR<P<g00ICR=P2P1P<P<P=P41B45g00KK1?40C>g00IcF@R0%A<P0G<1C2=P6P8g00L2R=g00LRR2'31D68=1=2dA;45:CGb3b4b5X04145:\7^04P6P8P:O2b29H9:E:1I8:=13;eW1W6W7o"). Qed.

Lemma v_or_shl : forall (x : word) a k, (0 <= a)%Z -> (0 <= k)%Z -> (a * 2 ^ k < 2 ^ 64)%Z ->
  (bv_unsigned x < 2 ^ k)%Z ->
  v_or (Z_to_bv 64 (a * 2 ^ k)) x = Z_to_bv 64 (a * 2 ^ k + bv_unsigned x).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) [] "h04__x1h12Hah27__arithh36__sat1h46__sat2h56__sat3h64__x2h74__ffh86__sat4h98__varmaph:5__with;4__p1h<4__x3h=1zh>1Hh?2H0h@3HakhA2HkhB2HxhC6__sat0hD1ahE1khF1xp;1p;2p;3p;4p;6p;5p;7p;8g002Yj18Tg003>j1hTg003\j1UTg006Mj1MTg006kj24Tg01Qhj26Tg007Hj21Tg008?j25Tg00\Oj1QTg007dj2?Tg00:Fj2CTg00:nj3;Tg00;Rj1gTg00<2j1fTg00N6j1aTg00=0j1ZTg00=Nj1XTg00>9j2LTg00A0j2VTg0050j2GTg00ARj2TTg009lj3:Tg00B>j3STg00B]j4RTg01Z\j2ETg009Fj27Tg008ij2ATg00<Rj2DTg00>\j2@Tg00@Nj1PTg00NTj4FTg00?jj6OTg01][j6NTg001:j6KTg00Qij1<Tg00RHj2>Tg01^[j3BTg00SZj3JTg00TCj2eTg00Toj3dTg00UOj1`Tg01_Dj5\Tg00COj3[Tg01_hj3YTg00D2j3]Tg01`Kj2^Tg00E^j2_Tg00??j4ITg00F:j7bTg00GBj8WTg00F^j7cTg00GfR0f0R1'_p=0g005oR2f1R3g00KKP1CIp=9P3g00HDR4g00HcR5P5g00ICR6P1g00IcFbp=3f3R7P4P5P5P6f2R8P3P1GWp=2P8P4P5P5P6P3P1Fcp=HP2P3g00M2P1CIp==g005JR9#8R:#8#8#8#8#8R;#hR<#UR=%03R>%M:R?/48,67%M;R;,4?R@'1f5RA,5<14?7'1f6RB#Q15<BRC#011C@'?1C?;RC110?RD%0;110@[[RE%0?RFg00JCRGA;?;3UW1R;%0@\GRH^1FRIf7RJ,C?f8RK#0f9RL,4?,10[\Df:RM=;?3VGX1F14?MRN#0\G^1Fg00J_RO#gRP%fORQ%a2RR%Z2RS%X2RT1L20RU1L2?RV'9'3RW1VT6RXP1P8g00L2RYg00LRRZ'G1T18=:YZdAS203CRRZb7b9b:PFP1b2bCb3b4b59;?A14?ARY#0P214?B,6JR[15<LR\,E1,7<14?J,6K/A\,7<R\5:=X=2P215<KR],A[R^17<1=:=\X=217<^,G=1E[]PJP]PBPCPEP;PI1C?KR]%0L110N[\DRNf;R^=;?3VGX1FR\14?^R?#0\G^1FRGPPPQ1D23PSPT1@29R_,9U,3TR`%P5RaP`C2PXPZb7b9b:X02Rb%01RcP>[^02RdP1f<RePMO2b2b3b4b5b8PCPEP;PIP]PNP\PGPbPdP1P^PLO2b2b3b4b5b8PCPEP;PIP]PNP\PGp-0RdPPPQP21D28RbP3PRCFRRPSPTPTP4P5P5P6f4RfEO9HT`PaPT1@2:R:,=_,3TRgPaAHT`gC2C2PXPZb7b9b:X02X62W;1?c81138%081187'?[[^02^62^;dP1f=,5<Rd/1@P?PdPBPJO5b2b3b4b5b8ENEK17<[,5<PCPEP;PIP]PNP\PGg00V4Rd#<Rc#<#<Rg,>2Rh%<g,>21>2cRc5B2=J2c5B21>2d9B2h5J2g00VS'e=dOPPQP2PbP31D27CFPSPTPT1=UV,3TPaPT%`9,@2,9U,3TR9Pa1=U:,3TC2C2PaPTPTPWPaPTPTP4P5P5P6D\PaA[2V<RV,9U,3TC2C2PaPTP9PaPTP`PaAY2_:R:,9U,3TC2C2C2C2PXPZb7b9b:X02X62X<2%07RU1107[\DPH\F%0f16fA#0\U[[[^02^62^<2P1P^P?PeP8P7PLPMO7b2b3b4b5b8PCPEP;PIP]PNP\PGPPPQPRPSPT1=:V,3TRTPaPTC2PXPZb7b9b:X02X621613/1@1638/1@[^02^62P1P?PePKO3b2b3b4b5b85][EKb?16BYRY,7</^J15<J,AY,7<5:=eb>WBW@XA>W1XE2XD2WFo"). Qed.

(* [comment removed for export] *)
Definition M8 : Z := 72340172838076673.

Lemma M8_digit : forall c k, (0 <= c < 256)%Z ->
  (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%Z ->
  (Z.shiftr (c * M8) (8 * k) mod 256 = c)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) [] "h01Hh17__arithh24__ffh38__varmaph45__with54__x1h61kh71zh86__sat2h94__x2h:4__x3h;4__x4h<1Bh=3Mhih>3Mloh?1Gh@2HBhA2HMhB2HchC2HkhD3HlohE3HlthF3Hm1hG1cp%0p&0p;1p;2p;4p;3p;6p;7p;8g002Yj16Tg006Mj12Tg007Hj2=Tg007dj2STg00UOj17Tg01Qhj20Tg01a@j2GTg008ij2ATg01a`j2lTg00QHj2QTg01bQj2jTg00RHj2iTg00Qij1MTg00Pjj1^Tg00TCj2RTg01c:j2tTg00;Rj1sTg00<2j1rTg00<Rj2XTg00N6j1qTg00NTj4VTg00=0j1pTg00=Nj1oTg00>9j2dTg00>\j2UTg00@Nk10<Tg00O2j3bTg00A0k20;Tg0050j2[Tg00ARk20:Tg009lj3>Tg00B>k309Tg00B]k408Tg01ccj2ZTg01d@k305Tg01dck104Tg01eDk303Tg00PNj6kTg01ekk102Tg01fLj4cTg01fmk301Tg001:j6_Tg01gPk600Tg01h4j4~Tg01hWj3{Tg01iLj4zTg006kj2?Tg01j:j2gTg01jZj2yTg01kFj3xTg00E^R0j2|Tg00hdR1j2PTg01^[j3mTg00S1j3wTg00SZj3WTg00Toj3fTg00??j4`Tg00F:j7aTg01_hj3vTg00F^j7uTg00GBk806Tg00n\k707Tg00GfR2f0R3'|p=4%63#6p=hg005oR4?>32p=Yf1R5=>43p=1f3R6f2R75>4A>453'Pp=Ef4R8=>46A>475/P3'Pp=31P53,P7p=e%63#6#6p=C%63#6#6#6p=B1?53,Z7p=F1G75=>43p=;Am453p=D1i43p=LAw453p=NAW4539W47p=\g00J_R9Af9537f7p=KP7g00HDR:g00HcR;P;g00ICR<P4P5g00KKP3C`g00IcR=Fap=:Av453p=H1d43p=5P7P:P;P;P<P4P5g00W?P3C`P=Fap=<P4P5g00M2P3C`p=TP5P:P;P;P<P3P=Fap=OP7P:P;P;P<P5P3Fup=nP6P:P;P;P<P7P5P3L06p=81Z67/G5=>43p=@P4P8P6P7P5P3E_p=9AW453p=]Am475=W43p=J1053,?7p=}P7P:P;P;P<P5P3K07p=I%45g005JR=#6R>#6R?#6R@#6S00#6S01#hRA#6#2RB,=5'SRC%Y5RD%2=RE,15P5%2>RFP5%7=RG#2RHP5%2?RIP5%7>RJ#2RKP5%6GS02#2RLP5%7GRM#2RNCED3D33e%7AS03#C#B#7S04#C#B#7S05#C#B#7S06#C#B#7RA#C#B#7RO#C#B#7#2RP,06RQ%2@R@/07RR7FF1G3BRS/18X741=23RT1065/A7/1PRU%46RV%7M#7#7#7RW#7RX#2RY/08/=6RZf6R[?;BER\f7R]/lB%4]%4BR^f9R_/GB#4[[1Q4ES07,j4g00V4R`,i4Ra'DRb%M`R`#LRc%M`R`#MRd#MRe#LRf'DRg%^X,Q4/Nf3\g00VSRX'R%^=,Q4Rh/Ng1t4YRi/Df5\b/RX%s9Rb3K%r9R9P4P41X48S08P7%q4RjCVP51X46CV%p4Rk%o4Rl1d42Rm1U4?R?5:l&0<;RnPl1U4>R>1U4GRG'H=b4?%5PRo5<lPnPl1TmG,OlS09PnPl1U4=Rp9:lm%5B,Tp,Ol5nlRqPn1Hp>Rr/HG1Hp?5b41Hpo5<lC8C8C8C820;l<R?P3P7g00L2Rsg00LRRt'[20:37=>stdB09425H08Rtb2b3b4X54X94X:4X;41076/A8/1P1=281=6B,SVf5Rs,08/0[108]'A108P'1[[[\V^54^94^:4^;4P3f8RuP]P_f=RvP8PsP[f;RwO8b1b810w]/0s10w['A10wPRx'1P4f<Ry/0uRz/0[10y]R{'AR|P3P]PBPvC@X741Z{[S0:,Az11SvX74RSP4P210v_/A3?;BvX74PzPSP41GuBR},0y/GB113vX74PE10v3?;BvX74PyPS1luBRS%4uf:R~/GB#4\^[R^PbP91X45S0;PkPlPqPnPqC8P?Ptb2b3b4X54%431=3B'SPC[^54P3f>RCPyO2b1b8:05yB10yE&04yD9P}P5D91GzBB03uyBEk1Az2&02zD9Q0:PSP^P4Q07P=1Q42S07CcR}/Nf/]a1j4}/DfR}%Ld/Dc%L`R`%MeRe#M#L%BW#B#7#^,Q4/Nf9Jig9J`a3J3\7Jc/RXP4PhP=Q07Cc/Nf/]a%Le,D`Re,D`1Dca9Jce5\}7J`/RX;KbP9P41X47P5P4Q08P6PjCVCVPkPl%5Y/H>/TG,OlPnPlA:lm>PnPl1U4J/HG=b4>=<loPnPlQ09PnPlPqPnA:lmr1TrG,Ol5nlC8C8C8C8C8P?Ptb2b3b4X54X94X:4X;410Y5/=7%4710s8/A6/1P1=2s%481=8B'S10s[RY#41=Y]'S[[[[[^54^94^:4^;4P3P~PuP_PCP8PsP[P]PyO9b1b8:01{[E_1Z|[PzP[P{PSP^PbP9Q0;PkPl1Tmp,OlPnPlP:P;P;P<A<lpmR<J00C8P?Ptb2b3b4X54g01ko\D\T^54P3PuP]O2b1b8C~D910yPP3Ekb0WFWEWDWAW@X<4X>4X=4PxPsPBPwC@\\\Z\V\U\T^<4^>4^=4P1%Y6P6PEP6PFP6PHP6PIP6PKP6PL116ND3D3D310sP10@87FF?;BsP5%Y8P4P210]PRTA}F@3RUPBP]C@X64P7PPP2PEg01lLg01m2'[R71[4PRVP4P0g01mX9{40P2CzP71[4ER2O8PsP3E_W0P3O1P8PEP8PFP8PHP8PIP8PKP8PL118ND3D3D3P111sEPsPFPsPHPsPIPsPKPsPLPsPNCED3D310@[9FTF?;B]P311[EPE10_PRTPUPBP_C@X64P8%2OROPE1?F@P7PVPbP9PjPk%5ER89:lmP?Ptb2b3b4%4EP3b1P7P2O8P]P3D9W0P3O1P[PFP[PHP[PIP[PKP[PLP[PNCED3D3P111]FP]PHP]PIP]PKP]PL11]ND3D310@u9FTF?;B_P311uFPFPxPUPBPwC@X64P[%2ARAQ03#2R[Q00#2,?FP7PVPbP9PjPk%5[9:lmP?Ptb2b3b4%4[P3b1P7P2O8P_P3D9W0P3O1PuPHPuPIPuPKPuPL11uND3D3P111_HP_PIP_PKP_PLP_PNCED310@~9FxF?;BwP311~HPH10vPRxPUPBPvC@X64PuQ06#2RuQ04#2R_Q02#hRT#2,?FP7PVPbP9PjPk%5_9:lmP?Ptb2b3b4%4_P3b1P7P2O8PwP3D9W0P3O1P~PIP~PKP~PLP~PNCED3P111wIPwPKPwPL11wND310@y9FxF?;BvP311yIPIf?Rx/0PRwPUPBPxC@X64P~Q05#2R~P~Q01#2,?FP7PVPbP9PjPk%5~9:lmP?Ptb2b3b4%4~P3b1P7P2O8PvP3D9W0P3O1PyPKPyPL11yND3P111vKPvPLPvPNCE10@C9FwF?;BxP311CKPKfARw/0PRvPUPBPwC@X64PyP_Pu%CJ#2,?FP7PVPbP9PjPk%5u9:lmP?Ptb2b3b4%4uP3b1P7P2O8PxP3D9W0P3O1PCPLPCPNCEP111xL11xNf@Rx,0@9FvF?;BwP311xLPLfCRv/0PPUPBPvC@X64RvPCP[PA%6T#2,?FP7PVPbP9PjPk%5A9:lmP?Ptb2b3b4%4AP3b1P7P2O8PwP3D9W0P3O111xNPNPvPCPEPO%CM#2,?FP7PVPbP9PjPk%5O9:lmP?Ptb2b3b4%4OP3b1P7P2O8PwP3D9W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000b?1gQR1Nh`,]a/RX,yaRaAKaab9Kaa9Kaa7KaP9Q0;PkPlA<lp8%5F9<lp%5H9<lp%5I9<lp%5K9<lp%5L9<lp%5N9<lp5Il5Il5Il5Il5Il5Il9Il<Pn%5@/Hp9:lmC8P?Ptb2b3b4X54%Y3113EP3PFP3PHP3PIP3PKP3PLP3PNCED3D33e10@5#4[^54P3P6P5O2b19xQRD9g01n=,06/gR?;B6eWCWBX64XG4o"). Qed.

Lemma byte_eq_mod : forall x y, (x mod 256 = y mod 256)%Z -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) [] "h02b1h12b2h21nh31zh41Hh52H0h61xh71yp;1p;2p;3p;6g002Yj11Tg006Mj1;Tg01a@j27Tg009lj30Tg003\j13Tg008?j22Tg01noj3:Tg003>j19Tg009Fj26Tg01oSj24Tg0209j25Tg001:j68Tg005oR0f1R1g005J#1#1#1R2#1#1#1#1#1#;R3'7f0R4/73500g020hR3%34R5%31R6g007df2R7#3?014f3R8/271281500R9[12711274500%38?071[R:f4R;#3?087\9A:714P4n2001000000120000000W1W0W2P:^16^05^23P4%92R21628R31627R5P014281223R39004X30P01427142;=004X30P112251527E8P31528E8O4b5W4X70W6o"). Qed.

(* [comment removed for export] *)
Lemma rep8_bytes : forall c, (0 <= c < 256)%Z ->
  word_to_le_bytes 8 (Z_to_bv 64 (c * M8)) = repeat (Z_to_bv 8 c) 8.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) [] "h01zh17__arithh24__ffh38__varmaph45__with54__x1h64__p1h72Hah81Dh92Hch:6__sat0h;6__sat1h<1ch=1kh>5lemmap%0p&0p;1p;2p;3p;6p;7p;4p;8g002Yj14Tg006Mj18Tg007Hj2ITg007dj2OTg01Qhj2GTg003>j1^Tg003\j1oTg00<2j1ZTg00Qij1@Tg021Fj2XTg009Fj26Tg01M]j3_Tg009lj33j1jTg008ij2MTg01j:j21Tg00;Rj1\Tg00Toj35j2>j1mTg022Cj1}Tg00UOj19Tg0050j2QTg01a@j2JTg023;j1iTg023lj3hTg024^j1fTg025Mj6eTg0268j7dTg00<Rj2cTg00=0j1bTg00=Nj1aTg00>9j2`Tg00>\k207Tg00??j4NTg00@Nk106Tg00A0k205Tg00ARk204Tg00B>k303Tg00B]k402Tg00N6k101Tg00hdj2;Tg0273j1~Tg01d@j3|Tg00d7j87Tg027Wj4LTg008?j2uTg00RHj2[Tg00SZj3sTg00TCj2rTg01jZj2qTg00?jj6tTg01_hj3pTg00:Fj2vTg006kj2wTg00:nj3nTg00COj3xTg00D2j3yTg028>j2zTg00E^j2{Tg00F:j7RTg00F^j7lTg00GBk800Tg00n\j7WTg001:j6]Tg029Fj3kTg00GfR0f0R1'{p=:%41#4p=Ff4R2f3R3f2R4f1R5;5135p=2g005oR6f7R7f6R833f5R9=362A3634A3651';';';p=CA3670A3689A3623A3645/;1';';';p=E1134/J5=361p==A3651p=Y1145/J1p=gP6P5g00KKP1CNp=VP5g00HDR7g00HcR:P:g00ICR;P1g00IcR<FRp=P1`61p=<P4P7P:P:P;P5P1Flp=TP3P7P:P:P;P4P5P1L00p=UP8P7P:P:P;P9P7P:P:P;P6P2g00W?R=P3CNP<FRP4P7P:P:P;P6P5P=P1CNP<FRFWp=?P2P7P:P:P;P3P7P:P:P;P6P4P=P5CNP<FRP1FWp=0A3601p=H1;51,;4p=SP6P2P3P4P5P1E]p=AP6P2P3P4P5P1E]9k89p=D1645=531p=B%41#4#4#4p=K%:1R9g005JR8#4R<#4R=#4R>#4#FR?#4R@#4#8RA,I1RB'ORCg01n=RD,G5RE%^>RF#oRG#ZRHg00V4RI#@#@RJ#@#@#@#@#@#@RK/X116F4RL=_GK33X06%8>R>/M>RM,1ERNPG1G4DRO,6FRPPG11O>S00,6FRQPG16F1RRPG111>RS,6FRTPG11S>RS,6FRUPG11S>RS,6FRVPG11S>RS,6FRWPG11S>,6F%\GRSD2D2D2D2A5GLSS0195GLS0295GLS0395GLS0495GLS0595GLS0695GLRX95GLRY53HX061MM>RZ,1ER[PGPPPGPQPG11OMS07,6FR\PGPRPGPTPGPUPGPVPGPWPSD2D2D2D2=3HYX061MZ>RW,1ER]PGPPPGPQPGP\PG11OZS08,6FR^PGPRPGPTPGPUPGPVPSD2D2D2D2=3HYX061MW>RV,1ER_PGPPPGPQPGP\PGP^PG11OWS09,6FR`PGPRPGPTPGPUPSD2D2D2D2=3HYX061MV>RU,1ERaPGPPPGPQPGP\PGP^PGP`PG11OVS0:,6FRbPGPRPGPTPSD2D2D2D2=3HYX061MU>RT,1ES0;PGPPPGPQPGP\PGP^PGP`PGPbPG11OUS0<,6FRcPGPRPSD2D2D2D2=3HYX06%}5%:41I4AS0='OP5P5%88RYP5%8<RRP5%98Rd#8ReP5%8=R=P5%9<#8R<P5%4d#8RfP5%9d#8RdGCGE1G2D1G>4PAP2C=[[^=6PHPH1>GP1>GLRg11OTS0>,6FRh=5GSS0?95GcS0@95GbS0A95G`S0B95G^S0C95G\S0D95GQPXPGPH\HRX%mGRiPiPPPLPX\G/QiRPPOP4P41G3DRD/JARj/Y1X06PO1G>0RkPAP4C=P6%j6Rl%i69h6lPjP3AgDkARkP6Pl%f6PkP3P1EeFdW>P1P0g00J_Rk#\Rl%ZkRm1c65Rn%b6Ro%a6Rp1`60Rq20768R8'V,PpRrP6P8g00M2S0E%<ACN,PpRs5TpRt&06:RuPtCU205p;RtP1P4g00L2Rvg00LRRw'Q20414=3vwdB03605H02Rwb2b3b4X56%:51I5A'O\C^56P1P3P4O2b1RCPlPm&016RvPoPpPpPqPqPpPpPq%<YRxPpPpPq%<RRyPpPpPq%<eRzPpPpPq%<=R{PpPpPq%<<R|PpPpPq%<fR}PpPq%<dR~F?D0D0D0D0D0D0PtPwb2b3b4A3600%HY%HR%He%H=%H<%Hf%Hd';3S3S3SP1b1O3PO1J1A,YjX061JOA,Q611O0%~ODAO21J4AROA|4ACRjFDG7PHPH1>GQPgQ0DQ06PGPXPiPiPQPLPPQ00P4P4PDP>PAP1C=X06P1PYPCPlPmPvPoPpPpPxPqPpPpPxPxPpPpPxPyPpPpPxPzPpPpPxP{PpPpPxP|PpPpPxP}PpPxP~F?D0D0D0D0D0D0PtPwb2b3b4PYPYPYPYPRPYPePYP=PYP<PYPfPYPdGCGEP1b1O3POPjFDG7PHPH1>G\PgQ0CQ05PGPXPiPiP\PLPPQ07P4P4PDPMPAP1C=X06P1PRPCPlPmPvPoPpPpPyPqPpPpPyPxPpPpPyPyPpPpPyPzPpPpPyP{PpPpPyP|PpPpPyP}PpPyP~F?D0D0D0D0D0D0PtPwb2b3b4PRPRPYPRPRPRPePRP=PRP<PRPfPRPdGCGEP1b1O3POPjFDG7PHPH1>G^PgQ0BQ04PGPXPiPiP^PLPPQ08P4P4PDPZPAP1C=X06P1PePCPlPmPvPoPpPpPzPqPpPpPzPxPpPpPzPyPpPpPzPzPpPpPzP{PpPpPzP|PpPpPzP}PpPzP~F?D0D0D0D0D0D0PtPwb2b3b4PePePYPePRPePePeP=PeP<PePfPePdGCGEP1b1O3POPjFDG7PHPH1>G`PgQ0AQ03PGPXPiPiP`PLPPQ09P4P4PDPWPAP1C=X06P1P=PCPlPmPvPoPpPpP{PqPpPpP{PxPpPpP{PyPpPpP{PzPpPpP{P{PpPpP{P|PpPpP{P}PpP{P~F?D0D0D0D0D0D0PtPwb2b3b4P=P=PYP=PRP=PeP=P=P=P<P=PfP=PdGCGEP1b1O3POPjFDG7PHPH1>GbPgQ0@Q02PGPXPiPiPbPLPPQ0:P4P4PDPVPAP1C=X06P1P<PCPlPmPvPoPpPpP|PqPpPpP|PxPpPpP|PyPpPpP|PzPpPpP|P{PpPpP|P|PpPpP|P}PpP|P~F?D0D0D0D0D0D0PtPwb2b3b4P<P<PYP<PRP<PeP<P=P<P<P<PfP<PdGCGEP1b1O3POPjFDG7PHPH1>GcPgQ0?Q01PGPXPiPiPcPLPPQ0<P4P4PDPUPAP1C=X06P1PfPCPlPmPvPoPpPpP}PqPpPpP}PxPpPpP}PyPpPpP}PzPpPpP}P{PpPpP}P|PpPpP}P}PpP}P~F?D0D0D0D0D0D0PtPwb2b3b4PfPfPYPfPRPfPePfP=PfP<PfPfPfPdGCGEP1b1O3POPjFDG7PHPH1>GhPgPSPSPGPXPiPiPhPLPPQ0>P4P4PDPTPAP1C=X06P1PdPCPlPmPvPoPpPpP~PqPpPpP~PxPpPpP~PyPpPpP~PzPpPpP~P{PpPpP~P|PpPpP~P}PpP~P~F?D0D0D0D0D0D0PtPwb2b3b4PdPdPYPdPRPdPePdP=PdP<PdPfPdPdGCGEP1b1O3POPjFDG71QHSG7G7G7G7G7G7G7G7b8PGPFPEPGPF11E>RjPGPFPNPGPFP[PGPFP]PGPFP_PGPFPaPGPFQ0;PSCBCBCBCBCBCBCBCBPG16F5RFPGPFPGPFPGPFPGPFPGPFPGPFPGPFPSD2D2D2D253He11a>PEPUP>PlPmPvPo%<>,Vq,PpPtPwb2b3b4%:>P1b1RvCLDA11_>PEPVP>PvCLDA11]>PEPWP>PvCLDA11[>PEPZP>PvCLDA11N>PEPMP>PvCLDA11j>PEP>P>PvCLDA1XKEA_GFKRF53He%^?RG16GERv'up-0R>1[6IRI1[6J9s6Ig00VS'r'q=5klRlPmPnPoPpPpP7P:P:P;P3EtR;9TprPu%9@#4#F#K#9#4#F#K#9#4#F#K#9#4#F#K#9#4#F#K#9#4#F#K#9#8R@#<9p68R8,Vq,PpCUPtPwb2b3b4X56W61O951G5@R@#:[^56^6>P1Q0=P4P5O3b1%:Ee%8?R?,vR1I0R%:?1wR?R4,I0[[%:RR0g00JCR9AnR?5UW7%:4\9^70PlPmPnPoPpATp;sPuP6P8Q0EAx6yGCN,PpCUPtPwb2b3b4X56X6>1O5B1I@4[^56^6>P1%:2P2P3O3b1b:b;1IE4e5yEDA1zKv=3HFeW9X<6o"). Qed.

(* [comment removed for export] *)
Lemma sb_byte_u : forall c : word, Z_to_bv 8 (bv_unsigned c) = Z_to_bv 8 (bv_unsigned c mod 256).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) [] "h07__arithh14__ffh28__varmaph35__with41ch51zp;1p;2p;3p;4p;7p;6g002Yj10Tg003>j1GTg003\j1<Tg008?j23Tg006Mj1FTg01a@j21Tg009lj32Tg0050j24Tg00;Rj1:Tg00<2j17Tg00N6j16Tg00=0j18Tg00=Nj19Tg00>9j25Tg00??j4ETg00F:j7DTg01gPj6@Tg00A0j2?Tg00ARj2>Tg00B>j3=Tg00B]j4ATg02:Aj3BTg001:j6;Tg029Fj3CTg005J#0#0#0#0#0#0R0#GR1#<f0R2,31R3%00#0#FR0,13R4g005oR5P4f1R6,31/10=252X5514541140g00J_R4#:%74%65%85%95R4g00HDR1g00HcR7P7g00ICR8P4P1P7P7P8P51550g00W?g00GfR7,55CEg00IcFDE@1?48P2f2R8g00L2R4g00LRR1'41>28=241dA=576CAb1b2b3A2507g01ko[P2b09B30E;3CW4o"). Qed.

(* [comment removed for export] *)
Lemma step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_or (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsLib ()) [] "h01bh12Hdh22Heh32Hfh43Hrdh52Hvh61mh73memh82pch92rdh:4regsh;3romh<3rs1h=3rs2h>4segsh?1vh@1wp;1p;2p;3p;4p;6p;=p;5g00<2j1NTg002Yj13Tg00UOj1ETg003>j16Tg003\j17Tg000Nj2HTg00Wfj18Tg017Dj2DTg00^Yj2>Tg009lj30Tg018Fj1ATg019Fj2@Tg019fj1?Tg02:bj4MTg006Mj1LTg01;Cj4KTg02;Nj2GTg02<1j3=Tg02<Tj3<Tg01;cj22Tg01`Kj29Tg01D>j1FTg02=Aj34Tg01=@j2;Tg01G7j25Tg0050j2CTg001:j6:Tg01F;j2BTg02>8l=ITg01EFj5JTg01BTR0f3R1f2R2f1R3f0R4DJp=1g02?0#Ng005J#3R5#E#6R6%35R5#3R7#3#3R8#3#6#7R9'HR:%67#7#8\9R7%68#7R8%76R;%88f9R<f7R='Df4R>,>830g00L2R8f5R?#Ag01@\R@30g01A<RAg005oRB'@RC#8f6RD#?PAPBg02?oP?P>P1CM%L5R5CK,>C30g00GfRCg02@[RB1G6Cd5=69<6D=08@f<RA/2D12A?'9=09>g01JkRE#FRFP8P:f8RGA=6CB5<6R6f=RB12B=12BD'9RC94BGn01000000200001;A5RHf;RIf:RJC1,5Ef>RK?4<D1;B5R5PAPIC1,5ERL90F4X6FP8P@P8P:P4PK12KG12K='994K<n0100000020000P5PAPIC1,5E=0FLX08P9P?A4K<4P5PAPIC1,5E=0FLX09A4BG?PHPIPJC1,5E,CFPCP4E:P6P3E:PBPAPIPJC1,BKP0PKPBPAPIPJP<PGP=PDP>P1P2M=IE:W5W4W1W2W3X?9X=;X<;W9W@X;7W7X89W:W>o"). Qed.

(* [comment removed for export] *)
Ltac av_or F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_or_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
  | step_simpl ]; vn.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

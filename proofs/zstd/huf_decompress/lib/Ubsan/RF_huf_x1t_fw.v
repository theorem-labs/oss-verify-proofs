(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats HufPure_HufX1
  HufPure_HufTableX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Step MState.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_bdt_model
  RF_huf_x1t_model RF_huf_x1t_cls RF_huf_x1t_wk RF_huf_x1t_fk RF_huf_x1t_f1 RF_huf_x1t_f2 RF_huf_x1t_f4
  RF_huf_x1t_f8 RF_huf_x1t_f16.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x1t_fw () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List=nth_error_mapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC47Corelib4Init9Datatypes:option_mapC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C47Corelib5Lists7ListDef3nthK47Corelib4Init5Logic2eq01C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List>nth_error_nth'C47Corelib5Lists7ListDef3mapC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signedC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX1<fill_weightsK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x1t_cls7x1f_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init3Nat3mulC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega6VarMap1t01C47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x1t_model3ox1C5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model6omergeI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchK46Stdlib9micromega5Tauto8GFormula01C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib3Arr@u32arr_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u32arrC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x1t_cls8x1_slotsK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC56Stdlib6ZArith6BinInt1Z3divC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7to_byteC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x1t_model>fill_weights_SC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model;bind_Ok_invI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5shl32C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model7load_OkC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;Forall_ZnthC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3u32K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z;le_lt_transK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z7mul_1_lC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z8mul_commC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C56Stdlib6ZArith6BinInt1Z6shiftlI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2wac5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_fw=nth_map_Znth'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u32arr_readC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv7Prelude4sextK4ELinuxProcessSemantics5Riscv3Sem4core01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4C56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sllwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_sllwC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sraiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sraiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x1t_model<fill_syms_okC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x1t_model=fill_syms_symC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwK4ELinuxProcessSemantics5Riscv5Instr5instr0BC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_mulC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5m_mulK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1K46Stdlib;setoid_ring<Ring_polynom5PExpr07C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x1t_model:pow2_casesC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z6ltb_ltc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_fw>signed_small64C5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_f46f4_clsC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x1t_f167f16_clsC46Stdlib4Bool4Bool>negb_false_iffC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_f86f8_clsC56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_f16f1_clsC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_f26f2_clsC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x1t_model9srai_pow2C5ARocqVerifyHarness?AgentSubmission6Common9FseRdKit2:sx32_smallC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C47Corelib4Init9Datatypes7nat_indC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX19fill_symsK46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega5Tauto4kind02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5aluop01I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x1t_cls5X1REPI47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5msize03I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop08K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma nth_map_Znth' : forall (l : list Z) i, 0 <= i < zlen l ->
  nth_error (map (Z_to_bv 64) l) (Z.to_nat i) = Some (Z_to_bv 64 (Znth i l)).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_fw ()) [] "h04__p1h14__p2h24__x1h34__x2h44__x3h51oh61xh71Hh82H0h97__arithh:4__ffh;8__varmaph<5__with=4cstrh>1ih?1lh@2z0p;1p;2p;3p;4p;7p;5p;6p;<p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9g000NR1p4p7210g0010R0p4p710p8g001Nj1MTg001nj24Tg002Jj2=Tg002jR2j1>Tg003JR3j23Tg003fj22Tg004Aj11Tg004fj1[Tg005Dj1WTg005gj1FTg006Ij1Uj2:Tg006oR4j1CTg007Oj3HTg007mj4OTg008Qj2ITg009Ij27Tg009kj30Tg00:Ej4NTg00:aj29Tg00;;R5j2\Tg00;Sj28Tg00<0j1XTg00<Uj2VTg00=7j2GTg00=Qj1?Tg00>0j2;Tg00>Yj3<Tg00?Bj2KTg00?nj1TTg00@Nj3ETg00@nj2DTg00ALj4STg00Ajj1RTg00BHj1QTg00C3j2@Tg00CVj1PTg00D;j45Tg00Dfj2mTg00EIj7lTg00Emj1kTg00FOj2jTg00G1j2iTg00G]j3dTg00H<j4cTg00Hnj4bTg00IYj5`TP0j6JTg00J<j4aTP1j5_Tg00JXl<eTg00K=l<fTg00Kbj6^Tg00LFj7]Tg00Ljj7gTg00MNj8hTg00N2R1g00NPR0P1P1P4f4R4P2f3R6g00Nof2R7f1R8f0R9M<ep=ZP0P1P5P2P3g00O\f5R3P4P6P7P8P9M<fp=YP8g00P>R2g00P]R5P5g00Q=R0P9E^p=BP8P2P5P5P0P9g00Q]F]p=6P7P2P5P5P0P8P9Fgp=AP6P2P5P5P0P7P8P9Ghp=L%M1g00R=R:/491=18#>,39'2g00R[R;#1R<#1#1#1#1#1#[R=#WR>#FR?P1P>%U=R@%C8RA9H17RBCORC1I76,:=,7>90?9X5?%F1RDP1PAP7P:CNRE,71P1P>P@P9COP1%C7P6P:CN,:=,7>50?X5D1:=E,7>,9?PBP1P7PAP:1=17RB,\A18:8RE%>BRD'3PAPEP9X6118:9X61P8P81918DZPBPD191DEY%XB14:D1V:713:718:7RD=017'2147:A01D:'2'G18:6P1p-0RDg00S@RBg00SlRE#?RF#?RG#?,;1RH1;1G1;1F1;1E5<1RE5<15<1g00TKRF'KA<1HE/KF%TB5EB3E%MBP11D17P81D16CS%R1%Q1RBPBP2P5P5P01BB3P11@1;R2g00U7RF%P;,@1R;C5,6B5ABf6RE,BBP1P2PF1m1:RFC5,6B5ABFl%k5R5PBP1PFg00U^P;C5,6BP1P;g00VER;1@1<R<C5,6B5ABP5P1P2P;P<C5,6BCLCL1jB0P9P7g00VlRBg00WLR0'91i97=0B0dAd1:8Ccb:b;b<X21X31X41X0DW1A0197,26A019:,24'G14:61367'21376[[^21^31^41^0D^1DP9143:13:3P31=1E#>P8P7P4O7b9b@b8b=CbD`EJ1I87,:=,7>90?CeP1P>P@P7Ca=H>AP1P>P@PAP7D_EJW7X>1W?o"). Qed.

Lemma signed_small64 : forall x, 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_fw ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51zh61Hh71xp;2p;1p;3p;4p;8p;6p;7g001nj2<Tg004Aj10Tg00Wlj16Tg00CVj14Tg00XJj2XTg003Jj28Tg003fj27Tg004fj1DTg00Xgj2CTg009kj33Tg00YNj2=Tg00Ykj2>Tg00?nj1VTg001Nj1UTg00@nj2RTg00Ajj1QTg00BHj1OTg00C3j2NTg00Dfj29Tg00ZHj3MTg00Zkj3ETg00D;j42Tg00FOj2GTg00:aj2HTg00G1j2ITg00G]j3JTg00H<j4KTg00[Nj2LTg00Emj1BTg00MNj8ATg00[nj3@Tg0010j6;Tg006Ij2PTg00\Qj2?Tg00]9j2STg00LFj7TTg00Ljj7WTf0R0#0#0#0#0p=F%00#0#0#0#0#0#0#0p=1f1R1g00P>R2g00P]R3P3g00Q=R4P0g00Q]FTp=5f2R5P2P3P3P4P1P0FWp=:g00N2R6g00R=R7/<0R8g00R[R9#0R:#6%49#4#4#4#4#6'X,80'7P6%0:#FR:#DR;/C1R<A3605X56P6%0:#1#1#1#1#1#1#1R:#6R=,=1R>1>0==365X56g00S@R?#VR@%U?R?1R61RA%Q6RB%O6RCP61N69R9196=RD5M6RE=E6Dg00U7P9C2'51GC4RFP0P5g00VlRGg00WLRH'H1I05=3GHdAJ671CKRHb2b3b4X061=0=/>==360^06P0P5O1b1%0:#6R:,L>P@P?PAPBPCP2P3P3P4P61967R4g00U^R2P9C2,5CP6P9g00VER9PDC2,5C5:C%B3P6P4P2PEC2,5CP6PEP9196:C2,5C5:CGAPFPHb2b3b4X06180=,781<7>18>:'7[^06P0P5P1O2b19@>:E;A36<1e1P;1,?;1S;1E;W6W7o"). Qed.

Section FW.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : fmem) (WK DT SY tl : Z) (rank : list Z) (syms : list (option Z)) (js jt : list byte) (ncells : nat).
  Variable POST : machine_state -> Prop.
  Notation SP := (bv_unsigned sp).
  Hypothesis HTL : 1 <= tl <= 12.
  Hypothesis LR : zlen rank = 13.
  Hypothesis RR : Forall (fun v => 0 <= v <= 256) rank.
  Hypothesis HJT : length jt = (2 * ncells)%nat.
  Hypothesis HJS : length js = length syms.
  Hypothesis LSY : length syms = 256%nat.
  Hypothesis HSYR : forall i v, nth i syms None = Some v -> 0 <= v < 256.
  Hypothesis HNC : Z.of_nat ncells <= 8192.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 2 * Z.of_nat ncells <= 2^47.
  Hypothesis HSY : 0 < SY /\ SY + zlen js <= 2^47.
  Hypothesis HWK : 0 < WK /\ WK + 52 <= 2^47.
  Hypothesis DJ : DT + 4 + 2 * Z.of_nat ncells <= SY \/ SY + zlen js <= DT + 4.
  Hypothesis DJW : DT + 4 + 2 * Z.of_nat ncells <= WK \/ WK + 52 <= DT + 4.
  Hypothesis HSP : 240 <= SP /\ SP <= 2^47.
  Hypothesis DSD : DT + 4 + 2 * Z.of_nat ncells <= SP + -240 \/ SP <= DT + 4.
  Hypothesis DSS : SY + zlen js <= SP + -240 \/ SP <= SY.
  Hypothesis DSW : WK + 52 <= SP + -240 \/ SP <= WK.
  Hypothesis RKA0 : u32arr usegs m WK (map (Z_to_bv 64) rank).
  Notation INV m1 cells := (x1w_inv m m1 SP DT SY js jt syms ncells cells).

  Lemma fw_join : forall w len cnt u sym cells m2
      (y5 y6 y7 y8 y10 y11 y12 y14 y15 y17 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    1 <= w <= tl -> len = 2^(w-1) -> 0 <= cnt <= 256 -> 0 <= sym -> sym + cnt <= 256 -> 0 <= u ->
    u + cnt * len <= Z.of_nat ncells ->
    INV m2 cells -> rw_cells usegs m2 (SP + -208) (x1_fr DT tl WK (Z_to_bv 64 u) (Z_to_bv 64 sym) (Z_to_bv 64 w) (Z_to_bv 64 cnt)) ->
    (forall m3 (cw cc z1 z5 z6 z7 z8 z10 z12 z14 z15 z17 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
       w + 1 <= tl -> INV m3 cells ->
       rw_cells usegs m3 (SP + -208) (x1_fr DT tl WK (Z_to_bv 64 (u + cnt * len)) (Z_to_bv 64 (sym + cnt)) cw cc) ->
       evt usegs POST (MS (mkR z1 (Z_to_bv 64 (SP + -240)) gp tp z5 z6 z7 z8 (Z_to_bv 64 (-9)) z10 (Z_to_bv 64 (w + 1)) z12
                               (Z_to_bv 64 SY) z14 z15 (Z_to_bv 64 (2^64 - 1 - SY)) z17 (Z_to_bv 64 (-17)) (Z_to_bv 64 (DT + 4))
                               (Z_to_bv 64 (-25)) z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31)
                          F (Z_to_bv 64 (PHUF_RDT_X1 + 1520)) fc None m3 (seg_rom usegs))) ->
    (forall m3 (cu cs cw cc : word)
            (z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
       w = tl -> INV m3 cells -> rw_cells usegs m3 (SP + -208) (x1_fr DT tl WK cu cs cw cc) ->
       evt usegs POST (MS (mkR z1 (Z_to_bv 64 (SP + -240)) gp tp z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20
                               z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31)
                          F (Z_to_bv 64 (PHUF_RDT_X1 + 2992)) fc None m3 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR (Z_to_bv 64 len) (Z_to_bv 64 (SP + -240)) gp tp y5 y6 y7 y8 (Z_to_bv 64 (-9))
                            y10 y11 y12 (Z_to_bv 64 SY) y14 y15 (Z_to_bv 64 (2^64 - 1 - SY)) y17 (Z_to_bv 64 (-17))
                            (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                       F (Z_to_bv 64 (PHUF_RDT_X1 + 2912)) fc None m2 (seg_rom usegs)).
  Proof using All.
    intros w len cnt u sym cells m2 y5 y6 y7 y8 y10 y11 y12 y14 y15 y17 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
      HW HLEN HC HS0 HS1 HU0 HU1 INV FRM KL KE.
    assert (LP : 1 <= len <= 2048) by (subst len; split; [change 1 with (2^0); apply Z.pow_le_mono_r; lia
                                                      | change 2048 with (2^11); apply Z.pow_le_mono_r; lia]).
    assert (CP : 0 <= cnt * len <= 256 * 2048) by nia.
    destruct INV as (DTA & LC & SYA & MU & WM & MI).
    unfold x1_fr in FRM. unfold PHUF_RDT_X1.
    pose proof (ox1_length cells jt) as LOX. pose proof (omerge_length syms js) as LOM.
    x1k_rd4at FRM 56%nat (Z_to_bv 64 (bv_unsigned sp + -152)).
    x1k_to 2956.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -208) _ |- _ => x1k_rd4at H 48%nat (Z_to_bv 64 (bv_unsigned sp + -160)) end.
    x1k_to 2999. x1k_nm.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -208) _ |- _ => rename H into FR3 end.
    repeat (first [ rewrite sx32_small in FR3 by lia | rewrite unsigned_lit in FR3 by lia
                  | rewrite FseWalkKit.swrap32_small in FR3 by lia | rewrite Z.add_0_r in FR3 ]).

    let U := fresh "U" in if_cases U; zify_cond U.
    -
      eapply KL.
      all: first [ lia | exact FR3 | (unfold x1w_inv; refine (conj DTA (conj LC (conj SYA (conj MU (conj WM MI)))))) ].
    -
      eapply KE.
      all: first [ lia | exact FR3 | (unfold x1w_inv; refine (conj DTA (conj LC (conj SYA (conj MU (conj WM MI)))))) ].
  Qed.

  Ltac fw_frn := match goal with H : rw_cells _ _ (bv_unsigned sp + -208) _ |- _ =>
    repeat (first [ rewrite sx32_small in H by lia | rewrite unsigned_lit in H by lia
                  | rewrite FseWalkKit.swrap32_small in H by lia | rewrite Z.add_0_r in H ]) end.

  Ltac fw_lit := repeat match goal with H : context [2 ^ (?k - 1)] |- _ => is_Zlit k;
    let v := eval vm_compute in (2 ^ (k - 1)) in change (2 ^ (k - 1)) with v in H end.

  Ltac fw_pre w :=
    fw_lit;
    lazymatch goal with RKA1 : u32arr _ ?mm WK (map (Z_to_bv 64) rank), LDV : ?cnt = Znth w rank |- _ =>
      let c := eval vm_compute in (4 * w) in
      pose proof (u32arr_read usegs mm WK _ w _ (Z_to_bv 64 (WK + c)) RKA1 (nth_map_Znth' rank w ltac:(lia)) ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as RKL;
      rewrite <- LDV in RKL end.

  Ltac fw_inv := unfold x1w_inv; split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eassumption|];
    split; eassumption.

  Ltac fw_kl vw vL c1 vcnt vu vsym vr IH FW KC :=
    let m3 := fresh "m3" in let INV3 := fresh "INV3" in let FR3 := fresh "FR3" in let Hw1 := fresh "Hw1" in
    intros m3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hw1 INV3 FR3;
    eapply IH with (w := vw + 1) (cells := c1) (u := vu + vcnt * vL) (sym := vsym + vcnt) (r := vr);
    try first [ exact FW | exact INV3 | exact FR3 | exact KC | lia ].

  Ltac fw_ke vf FW KC :=
    let m3 := fresh "m3" in let INV3 := fresh "INV3" in let FR3 := fresh "FR3" in let Hwt := fresh "Hwt" in
    intros m3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hwt INV3 FR3;
    destruct vf; [ cbn in FW; injection FW as <-; eapply KC; [ exact INV3 | exact FR3 ] | lia ].

  Ltac fw_tail vw vL c1 vcnt vu vsym vr vf IH FW KC :=
    let m2 := fresh "m2" in let cells2 := fresh "cells2" in let HR := fresh "HR" in let INV2 := fresh "INV2" in
    let FR2 := fresh "FR2" in let HC1 := fresh "HC" in let HU1 := fresh "HU" in
    intros m2 cells2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? HR INV2 FR2;
    injection HR as HC1 HU1; subst cells2;
    eapply fw_join with (w := vw) (len := vL) (cnt := vcnt) (u := vu) (sym := vsym) (cells := c1);
    [ lia | lia | lia | lia | lia | lia | lia | exact INV2 | exact FR2 | fw_kl vw vL c1 vcnt vu vsym vr IH FW KC | fw_ke vf FW KC ].

  Ltac fw_post CL0 vw vL c1 u1 vcnt vu vsym vcells vr vf IH FW KC :=
    fw_frn; x1k_nm;
    let CL := fresh "CL" in pose proof CL0 as CL; unfold x1cls_stmt in CL;
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply CL with (m := m) (m1 := mm) (WK := WK) (DT := DT) (SY := SY) (tl := tl) (w := vw) (cnt := vcnt) (len := vL)
        (nb := tl + 1 - vw) (u := vu) (sym := vsym) (syms := syms) (js := js) (jt := jt) (ncells := ncells) (cells := vcells)
        (r := (c1, u1)) (POST := POST)
    end;
    clear CL;
    try first [ reflexivity | eassumption | fw_inv | lia ];
    fw_tail vw vL c1 vcnt vu vsym vr vf IH FW KC.

  Lemma fw_loop : forall f w cells u sym m1 (cw cc : word)
      (x1 x5 x6 x7 x8 x10 x12 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) r,
    fill_weights f w tl rank syms cells sym u = Ok r -> Z.of_nat f = tl + 1 - w -> 1 <= w <= tl ->
    0 <= sym <= 256 -> 0 <= u <= Z.of_nat ncells ->
    INV m1 cells ->
    rw_cells usegs m1 (SP + -208) (x1_fr DT tl WK (Z_to_bv 64 u) (Z_to_bv 64 sym) cw cc) ->
    (forall m2 (cu cs cw' cc' : word)
            (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       INV m2 r -> rw_cells usegs m2 (SP + -208) (x1_fr DT tl WK cu cs cw' cc') ->
       evt usegs POST (MS (mkR y1 (Z_to_bv 64 (SP + -240)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20
                               y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (Z_to_bv 64 (PHUF_RDT_X1 + 2992)) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -240)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (-9)) x10 (Z_to_bv 64 w) x12
                             (Z_to_bv 64 SY) x14 x15 (Z_to_bv 64 (2^64 - 1 - SY)) x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 (DT + 4))
                             (Z_to_bv 64 (-25)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 (PHUF_RDT_X1 + 1520)) fc None m1 (seg_rom usegs)).
  Proof using All.
    induction f as [|f IH]; intros w cells u sym m1 cw cc x1 x5 x6 x7 x8 x10 x12 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27
      x28 x29 x30 x31 r FW HF HW HSYM HU INV FRM KC; [lia|].
    rewrite fill_weights_S in FW.
    destruct (load rank w) as [cnt|e| |] eqn:LD; cbn [bind] in FW; try discriminate.
    apply load_Ok in LD. destruct LD as [LDR LDV].
    rewrite shl32_ok in FW by lia. cbn [bind] in FW.
    assert (LEN : u32 (1 * 2 ^ w) / 2 = 2 ^ (w - 1)).
    { assert (C : w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/ w = 10 \/ w = 11 \/ w = 12) by lia.
      repeat (destruct C as [C|C]; [subst w; reflexivity|]); subst w; reflexivity. }
    rewrite LEN in FW. unfold to_byte in FW. rewrite (Z.mod_small (tl + 1 - w)) in FW by lia.
    destruct (fill_syms (S (Z.to_nat cnt)) 0 cnt sym (2 ^ (w - 1)) (tl + 1 - w) syms cells u) as [[cells1 u1]|e| |] eqn:FS;
      cbn [bind] in FW; try discriminate.
    assert (LP : 1 <= 2 ^ (w - 1) <= 2048) by (split; [change 1 with (2^0); apply Z.pow_le_mono_r; lia
                                                      | change 2048 with (2^11); apply Z.pow_le_mono_r; lia]).
    assert (HCNT : 0 <= cnt <= 256) by (rewrite LDV; exact (Forall_Znth _ rank w RR ltac:(lia))).
    destruct INV as (DTA & LC & SYA & MU & WM & MI).
    destruct (fill_syms_ok _ _ _ _ _ _ _ _ _ _ FS ltac:(lia) ltac:(lia) ltac:(lia)) as (FL1 & FL2 & FL3).
    cbn [fst snd] in FL1, FL2, FL3.
    assert (HNX : u + cnt * 2 ^ (w - 1) <= Z.of_nat ncells /\ sym + cnt <= 256).
    { destruct (Z.eq_dec cnt 0) as [->|NZ]; [lia|]. specialize (FL3 ltac:(lia)).
      pose proof (fill_syms_sym _ _ _ _ _ _ _ _ _ _ FS ltac:(lia) ltac:(lia) ltac:(lia)) as SYB. nia. }
    pose proof (u32arr_transport usegs _ m m1 WK _ RKA0 MU WM ltac:(cbn [disjoint_from]; rewrite length_map; lia)) as RKA1.
    pose proof (ox1_length cells jt) as LOX. pose proof (omerge_length syms js) as LOM.
    unfold x1_fr in FRM. unfold PHUF_RDT_X1.
    assert (C : w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/ w = 10 \/ w = 11 \/ w = 12) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]].
    -x1k_to 1556. fw_pre 1. x1k_to 2524. fw_post f1_cls 1 1 cells1 u1 cnt u sym cells r f IH FW KC.
    -x1k_to 1556. fw_pre 2. x1k_to 1608. fw_post f2_cls 2 2 cells1 u1 cnt u sym cells r f IH FW KC.
    -x1k_to 1556. fw_pre 3. x1k_to 2692. fw_post f4_cls 3 4 cells1 u1 cnt u sym cells r f IH FW KC.
    -x1k_to 1556. fw_pre 4. x1k_to 1856. fw_post f8_cls 4 8 cells1 u1 cnt u sym cells r f IH FW KC.
    -x1k_to 1556. fw_pre 5. x1k_to 2132. fw_post f16_cls 5 16 cells1 u1 cnt u sym cells r f IH FW KC.
    -x1k_to 1556. fw_pre 6. x1k_to 2132. fw_post f16_cls 6 32 cells1 u1 cnt u sym cells r f IH FW KC.
    -x1k_to 1556. fw_pre 7. x1k_to 2132. fw_post f16_cls 7 64 cells1 u1 cnt u sym cells r f IH FW KC.
    -x1k_to 1556. fw_pre 8. x1k_to 2132. fw_post f16_cls 8 128 cells1 u1 cnt u sym cells r f IH FW KC.
    -x1k_to 1556. fw_pre 9. x1k_to 2132. fw_post f16_cls 9 256 cells1 u1 cnt u sym cells r f IH FW KC.
    -x1k_to 1556. fw_pre 10. x1k_to 2132. fw_post f16_cls 10 512 cells1 u1 cnt u sym cells r f IH FW KC.
    -x1k_to 1556. fw_pre 11. x1k_to 2132. fw_post f16_cls 11 1024 cells1 u1 cnt u sym cells r f IH FW KC.
    -x1k_to 1556. fw_pre 12. x1k_to 2132. fw_post f16_cls 12 2048 cells1 u1 cnt u sym cells r f IH FW KC.
  Qed.
End FW.

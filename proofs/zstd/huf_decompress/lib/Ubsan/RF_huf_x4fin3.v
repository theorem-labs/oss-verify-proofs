(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface RF_huf_x4fin RF_huf_x4fin2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x4fin3 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission3Lib3ArrCnth_error_upd_otherK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin3X4MK47Corelib4Init9Datatypes3nat02C46Stdlib5Lists4List9nth_errorC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib5Lists7ListDef3mapI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC56Stdlib6ZArith6BinInt1Z3divC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u64arr_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib4Init5Logic3and01I4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin7x4m_stkC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin6x4_epiC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqK46Stdlib9micromega6VarMap1t03C47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u64arrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genK4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litI47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02C5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u64arr_store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u64arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherI47Corelib4Init5Logic2or00C46Stdlib5Lists4List:length_mapK46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u64arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula02C5ARocqVerifyHarness?AgentSubmission3Lib3Arr:upd_lengthK47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega5Tauto4kind02K47Corelib4Init5Logic4True01c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fin34WSOKC46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andK4ELinuxProcessSemantics5Riscv5Instr5instr0BC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_mulC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5m_mulC56Stdlib6ZArith6BinInt1Z6shiftrK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC56Stdlib6ZArith6BinInt1Z=shiftr_nonnegC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin:ctz_tab_rdC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin=ctz_tab_rangec5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fin38wsok_updc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fin38x4f_nextC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit:signed_litC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fin28x4f_elseC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8byte_litC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin9x4f_loop4C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge7zr_wordC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_land_lI47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_NoneK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin6x4_errC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC47Corelib5Lists7ListDef3nthC46Stdlib9micromega;ZifyClasses6mkapp2K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop09C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin7CTZ_TABC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_leK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C47Corelib7Program6Basics4implI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C47Corelib7Classes?RelationClasses>impl_ReflexiveC46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03C46Stdlib5Lists4List6nth_okK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fin38x4f_donec5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fin38x4f_stepC47Corelib4Init9Datatypes7nat_ind".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Ltac u64_sok ARR i :=
  lazymatch type of ARR with u64arr ?segs ?mx ?A ?ws =>
    let a := cur_mem_addr in
    pose proof (u64arr_store_ok segs mx A ws i a ARR ltac:(rewrite ?upd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK
  end.
Ltac u64_store ARR i :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx ?a (le8 ?v)) _) =>
    lazymatch type of ARR with u64arr ?segs mx ?A ?ws =>
      let E := addr_expr a in
      let ARR' := fresh "ARR" in
      assert (ARR' : u64arr segs (write_to_mem mx (wa E) (le8 v)) A (upd ws (Z.to_nat i) v));
      [ replace (wa E) with (wa (A + 8 * i)) by (unfold wa; f_equal; lia);
        apply (u64arr_write segs mx A ws i v ARR); rewrite ?upd_length; lia
      | clear ARR; store_done; rename ARR' into ARR ]
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
Section X4F3.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x1_table_ok cells 11.
  Hypothesis ECB : cbs = firstn 4096 (x1_bytes' cells).
  Hypothesis LCB : zlen cbs = 4096.
  Hypothesis D8 : 8 <= DST.
  Hypothesis DC : 0 < dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 4096 <= lo.
  Hypothesis DJ1 : DT + 4 + 4096 <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation X4M := (RF_huf_x4fin.X4M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs).
  Notation XF l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT lo src cells cbs
                     TOK ECB LCB D8 DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).

  Ltac x4pack OUT LB :=
    split; [eexists; split; [exact OUT| rewrite ?Zupd_length; exact LB]|];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    split; [eexists; eassumption|];
    repeat (split; [eassumption|]); eassumption.

  Ltac fwk stops := fwalk stops sp DT cells cbs ECB TOK SS src DST.
  Ltac fwf := fw_one sp DT cells cbs ECB TOK SS src DST.

  (* [comment removed for export] *)
  Notation HK pc mm k prev xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x26 x27 t6 :=
    (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 (Z_to_bv 64 2) x8 x9 (Z_to_bv 64 66784) (Z_to_bv 64 k) a2 a3 a4 a5
             (Z_to_bv 64 (- DT - 5)) a7 x18 x19 x20 (Z_to_bv 64 (DT + 4)) x22 (Z_to_bv 64 9) (Z_to_bv 64 4) (Z_to_bv 64 prev)
             x26 x27 (Z_to_bv 64 (-1)) (Z_to_bv 64 ((dcap + 3) / 4)) (Z_to_bv 64 64) t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  (* [comment removed for export] *)
  Definition WSOK (ws : list word) (k : Z) : Prop :=
    forall i, k <= i < 4 -> exists ipi opi, nth_error ws (Z.to_nat i) = Some (Z_to_bv 64 ipi)
      /\ nth_error ws (Z.to_nat (4 + i)) = Some (Z_to_bv 64 opi) /\ SS <= ipi /\ ipi + 8 <= SS + n /\ DST <= opi <= DST + dcap
      /\ (exists bi, nth_error ws (Z.to_nat (8 + i)) = Some bi /\ bv_unsigned bi <> 0)
      /\ (exists ei, nth_error ws (Z.to_nat (15 + i)) = Some ei /\ 9 <= bv_unsigned ei).

  Lemma wsok_upd : forall ws k v, 0 <= k < 4 -> WSOK ws k -> WSOK (upd ws (Z.to_nat (4 + k)) v) (k + 1).
  Proof.
    intros ws k v K W i Hi. destruct (W i ltac:(lia)) as (ipi & opi & A & B & C & D & E & (bi & F1 & F2) & (ei & G1 & G2)).
    exists ipi, opi. rewrite !nth_error_upd_other by lia.
    split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [exact E|].
    split; [exists bi | exists ei]; split; assumption.
  Qed.

  Notation DN pc mm xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 :=
    (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Notation SENDk pc mm k SE OPk xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x23 x24 x27 :=
    (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 (Z_to_bv 64 2) x8 x9 (Z_to_bv 64 66784) (Z_to_bv 64 k) a2 a3 a4 a5
             (Z_to_bv 64 (- DT - 5)) a7 x18 x19 x20 (Z_to_bv 64 (DT + 4)) x22 x23 x24 (Z_to_bv 64 SE) (Z_to_bv 64 (SE - OPk)) x27
             (Z_to_bv 64 (-1)) (Z_to_bv 64 ((dcap + 3) / 4)) (Z_to_bv 64 64) (Z_to_bv 64 (SP + -344 + 8 * k)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Lemma x4f_done : forall mm sps ws fa
      (xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    X4M mm sps ws fa -> nth_error sps 3 = Some (Z_to_bv 64 SS) -> nth_error sps 4 = Some (Z_to_bv 64 DT) ->
    nth_error sps 5 = Some (Z_to_bv 64 n) -> nth_error sps 6 = Some (Z_to_bv 64 dcap) -> nth_error sps 7 = Some (Z_to_bv 64 DST) ->
    evt usegs POST (DN 0x17840 mm xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6).
  Proof using All.
    intros mm sps ws fa xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 XM S3 S4 S5 S6 S7.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof ((XF x4m_stk) _ _ _ _ XM) as STK.
    x4open XM.
    fwf.
    time "WALK" (fwk [0x1826c; 0x1785c]).
    all: first [ eapply (XF x4_epi); eassumption | exfalso; lia | showpc; fail ].
  Qed.

  (* [comment removed for export] *)
  Lemma x4f_endt : forall k SE OPk mm sps ws fa (xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x23 x24 x27 : word),
    0 <= k < 4 -> DST <= OPk <= SE -> SE <= DST + dcap -> nth_error ws (Z.to_nat (4 + k)) = Some (Z_to_bv 64 OPk) ->
    X4M mm sps ws fa -> nth_error ws 13 = Some (Z_to_bv 64 SS) -> WSOK ws k ->
    (forall prev mm' ws' (xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x26 x27 t6 : word),
       X4M mm' sps ws' fa -> nth_error ws' 13 = Some (Z_to_bv 64 SS) -> WSOK ws' (k + 1) -> DST <= prev <= DST + dcap ->
       k + 1 < 4 -> evt usegs POST (HK 0x173d4 mm' (k + 1) prev xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x26 x27 t6)) ->
    (forall mm' ws' (xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
       X4M mm' sps ws' fa -> k + 1 = 4 ->
       evt usegs POST (DN 0x17840 mm' xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)) ->
    evt usegs POST (SENDk 0x17804 mm k SE OPk xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x23 x24 x27).
  Proof using All.
    intros k SE OPk mm sps ws fa xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x23 x24 x27 K4 H1 H2 WOP XM W13 WK K1 K2.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    x4open XM.
    fwf.
    time "WALK" (fwk [0x173d4; 0x17840; 0x18268]).
    all: lazymatch type of WS with u64arr _ _ _ ?ws2 =>
           assert (LW2 : length ws2 = 19%nat) by (rewrite ?upd_length; exact LW); clear LW; rename LW2 into LW;
           first [ eapply (K1 _ _ ws2);
                   [ x4pack OUT LB | rewrite nth_error_upd_other by lia; exact W13 | apply wsok_upd; [lia | exact WK] | lia | lia ]
                 | eapply (K2 _ ws2); [ x4pack OUT LB | lia ]
                 | exfalso; lia | showpc; fail ] end.
  Qed.

  (* [comment removed for export] *)
  Lemma x4f_step : forall k prev mm sps ws fa (xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x26 x27 t6 : word),
    0 <= k < 4 -> X4M mm sps ws fa ->
    nth_error sps 8 = Some (Z_to_bv 64 0x218a392cd3d5dbf) -> nth_error sps 9 = Some (Z_to_bv 64 (DST + dcap)) ->
    nth_error ws 13 = Some (Z_to_bv 64 SS) -> WSOK ws k -> DST <= prev <= DST + dcap ->
    (forall prev mm' ws' (xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x26 x27 t6 : word),
       X4M mm' sps ws' fa -> nth_error ws' 13 = Some (Z_to_bv 64 SS) -> WSOK ws' (k + 1) -> DST <= prev <= DST + dcap ->
       k + 1 < 4 -> evt usegs POST (HK 0x173d4 mm' (k + 1) prev xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x26 x27 t6)) ->
    (forall mm' ws' (xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
       X4M mm' sps ws' fa -> k + 1 = 4 ->
       evt usegs POST (DN 0x17840 mm' xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)) ->
    evt usegs POST (HK 0x173d4 mm k prev xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x26 x27 t6).
  Proof using All.
    intros k prev mm sps ws fa xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x26 x27 t6 K4 XM S8 S9 W13 WK PV K1 K2.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (WK k ltac:(lia)) as (ipk & opk & WI & WO & I1 & I2 & O1 & (bk & WB & BK) & (ek & WE & EK)).
    x4open XM.
    fwf.
    time "WALK" (fwk [0x174fc; 0x176a8; 0x18268]).
    all: first
      [ eapply (XF x4_err); x4pack OUT LB
      | exfalso; lia
      | (let r := getreg 22%Z in lazymatch r with Z_to_bv 64 ?SEe =>
          first [ eapply (XF RF_huf_x4fin2.x4f_else k SEe opk sps ws fa)
                | eapply (XF x4f_loop4 k SEe opk sps ws fa _ _ _ _ _ (Z.to_nat dcap)) ] end;
         try first [ lia | exact WO | weq | x4pack OUT LB ]);
        first [ lia | exact WO | weq | x4pack OUT LB
              | intros; eapply x4f_endt; [lia | lia | lia | exact WO | eassumption | exact W13 | exact WK | exact K1 | exact K2]
              | match goal with H : bv_signed (Z_to_bv 64 ?e) < _ |- _ => rewrite (signed_lit e) in H by lia; lia end ]
      | showpc; fail ].
    Unshelve.
    all: first [ lia | exact WO
               | intros; eapply x4f_endt; [lia | lia | lia | exact WO | eassumption | exact W13 | exact WK | exact K1 | exact K2] ].
  Qed.

  (* [comment removed for export] *)
  Lemma x4f_kloop : forall (j : nat) k prev mm sps ws fa (xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x26 x27 t6 : word),
    k + Z.of_nat j = 3 -> 0 <= k -> X4M mm sps ws fa ->
    nth_error sps 3 = Some (Z_to_bv 64 SS) -> nth_error sps 4 = Some (Z_to_bv 64 DT) -> nth_error sps 5 = Some (Z_to_bv 64 n) ->
    nth_error sps 6 = Some (Z_to_bv 64 dcap) -> nth_error sps 7 = Some (Z_to_bv 64 DST) ->
    nth_error sps 8 = Some (Z_to_bv 64 0x218a392cd3d5dbf) -> nth_error sps 9 = Some (Z_to_bv 64 (DST + dcap)) ->
    nth_error ws 13 = Some (Z_to_bv 64 SS) -> WSOK ws k -> DST <= prev <= DST + dcap ->
    evt usegs POST (HK 0x173d4 mm k prev xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x26 x27 t6).
  Proof using All.
    induction j as [|j IH]; intros k prev mm sps ws fa xra t0 t1 x8 x9 a2 a3 a4 a5 a7 x18 x19 x20 x22 x26 x27 t6
      KJ K0 XM S3 S4 S5 S6 S7 S8 S9 W13 WK PV.
    - eapply x4f_step; try eassumption; [lia | intros; lia | intros; eapply x4f_done; eassumption].
    - eapply x4f_step; try eassumption; [lia | intros; eapply IH; try eassumption; lia | intros; lia].
  Qed.

End X4F3.
End CANSEC1.

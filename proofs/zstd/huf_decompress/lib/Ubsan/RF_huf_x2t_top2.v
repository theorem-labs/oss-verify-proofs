(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT
  HufPure_HufStats HufPure_HufStatsRT HufPure_HufX1 HufPure_HufTableX1 HufPure_HufTableX1RT HufPure_HufX2 HufPure_HufTableX2
  HufPure_HufTableX2RT HufPure_FseReadBridge.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem RunConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2 WStr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_h_iface RF_huf_tbl_iface RF_huf_tbl_iface2
  RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_tk RF_huf_bdt_model RF_huf_x2t_model RF_huf_x2t_fr RF_huf_x2t_pre RF_huf_x2t_path
  RF_huf_x2t_top RF_huf_x2t_top_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x2t_top2 () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_mulC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I46Stdlib;setoid_ring<Ring_polynom5PExpr00I47Corelib4Init9Datatypes4prod00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr07K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z7div_addC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats:read_statsC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_x2t_path6X2PATHC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats6hs_retC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats;hs_tableLogC56Stdlib6ZArith6BinInt1Z3ltbC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C56Stdlib6ZArith6BinInt1Z6to_natC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats:hs_weightsC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats<hs_nbSymbolsC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats7hs_rankC47Corelib5Lists7ListDef6repeatK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_rdt_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX29find_maxWC47Corelib4Init3Nat3mulK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX27fill_x2C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX26rv_idxC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX28x2_cellsC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC47Corelib4Init3Nat3addK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List:length_appC46Stdlib5Lists4List=repeat_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le4C5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions8bv_swrapC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr0;C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8K4ELinuxProcessSemantics5Riscv5Instr5instr07I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2or00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith6BinInt1Z:pow_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z6ltb_geC4ELinuxProcessSemantics5Riscv3Sem5alu64K4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC46Stdlib9micromega;ZifyClasses5mkrelC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC47Corelib4Init5Logic7f_equalK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC46Stdlib9micromega;ZifyClasses9and_morphC5ARocqVerifyHarness?AgentSubmission3Lib3Arr@u32arr_transportC5ARocqVerifyHarness?AgentSubmission3Lib5FrameFstk_transport_disjointC47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u32arr_store_okC56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u32arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_boundC46Stdlib9micromega;ZifyClasses6eq_iffC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7upd_natC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model;map_upd_natC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZupdC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model?upd_nat_length2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx32C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le4C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model6omergeC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model;omerge_noneC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_top5x2_p2C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_pre8so2_loopc5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_x2t_top28sl32sr30C5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model;zx32_small2C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_pre7rs_loopC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u32arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX2;rank_start2C5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX25sort2C5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX29rank_val0C56Stdlib6ZArith6BinInt1Z3maxC47Corelib5Lists7ListDef3nthI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX2=rank_val_rowsC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib5Lists4List:length_mapC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u32arr_frameK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u8arr_transportC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init9Datatypes3nat00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litI4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init5Logic4True00I5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats6hstats00C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface=HUF_RDT_STACKC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_iface9huf_dt_okK4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5msize04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize03K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas@Forall_all_bytesC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufStatsRT>read_stats_retC5ARocqVerifyHarness?AgentSubmission4SpecEHufPure_FseReadBridge@read_stats_safe'C5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufStatsRT8stats_okK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02C5ARocqVerifyHarness?AgentSubmission4SpecDHufPure_HufTableX1RT;WF_of_statsC5ARocqVerifyHarness?AgentSubmission4SpecDHufPure_HufTableX1RT2WFC5ARocqVerifyHarness?AgentSubmission4SpecDHufPure_HufTableX1RT3cntC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_tk=stk_frame_endC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_top6x2_epiC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_x2t_path=x2_model_pathC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_sltiuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9alu_sltiuC56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andc5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_x2t_top28dtd_sr24C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z8leb_specc5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_x2t_top26x2_p1bC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_pre7fm_loopC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;v_sltiu_b2zC5ARocqVerifyHarness?AgentSubmission6Common9FseRdKit2:sx32_smallI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufStatsRT4ksumI47Corelib7Numbers7BinNums1N00K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop0:".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sl32sr30 : forall x, 0 <= x < 2 ^ 32 -> ((x ≪ 32) mod 18446744073709551616) ≫ 30 = 4 * x.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x2t_top2 ()) [] "h07__arithh14__ffh28__varmaph35__with41zh54__x1h61Hh72Hxh81xp;2p;1p;3p;4p;6p;8p;7g0000j29Tg000Lj10Tg0011j15Tg001Oj2LTg001lj2?Tg002Hj2>Tg002cj21Tg003@j2FTg003`j1<Tg004Ej2ATg004ej2@Tg005Bj1dTg005bj1bTg006Bj2[Tg006`j1YTg007>j1XTg007ij2WTg008Lj3;Tg008oj47Tg009Zj2VTg00:<j2GTg00:Vj2UTg00;Bj3BTg00;\j3TTg00<;j4STg00<mj1QTg00=Kj2ETg00=nj6PTg00>Rj3OTg00?3j6:Tg00?Qj6NTg00?mj3MTg00@Vj2RTg00A?j1=Tg00A^j2CTg00BGj3eTg00C0j3KTg00CYj2JTg00DEj2cTg00E1j3HTg00EQj1aTg00F3j8\Tg00FWj3ZTg00G:j2]Tg00GZj3^Tg00HCj7_Tg00Hgj7`Tf0R0#0#0p=D%00#0#0#0#0#0#0#0p=4g00IKR1f1R2;B0p=31E10p=6P2g00IiR3g00JHR4P4g00JhR5P0g00KHF_p=2P1P2g00KhP0C7p=8f2R6P3P4P4P5P2P0F`p=Ig00LOR7/90R8g00LmR9#0R:#5R;%0:R:#0#DR<#5R='LR>,?0'>P1112>R>%0<#4#4#4R<#DR?#4#4#4#4#5R@,F0%<9#<#<#0#5RA'A%5:R:/16RB'3X41P1P>1A0A/3BX41P11L;A,@>130BX41g00MRR;#dRC%b;RD1[12RE%Y1RF%X1RGP1%6:1W19R95;1%5<R<#6RH5;1g00N>RI%5?R?#6RJ9;19RKC7'21VG5RLP0P6g00NeRMg00OERN'G1U06=BMNdAT172CSRNb1b2b3X5111:0/1<110?'3^51P0P6O1b011:2/1<112?RM'3P111B<RO1@0<f3,1:R:'3X41P1PB130:X411G1B1@O<PCPD%Q1ROPFPGP3P4P4P5P1PHPI1E17RIC7,2GEPPLPNb1b2b3AB1<7g00Oe[P0b09OB<E:116?P0ENb61A>APCPDPOPF%6A,8I,2GPLPNb1b2b3197AP0b09M>AE:1F>@1R1?g00PBRA#=R<,C15e11C1ARA5K1g00PaRB'J%=<#=,C19K1A/JB,cA=H;C5H;PDPEPFPGP3P4P4P518I9,2GP1P9g00QMR9PJC7,2G5IG%a418IK,2GP1PKP9%6@C7,2G5IGG\PLPNb1b2b3X511?0?,>8197M1?M@'>[^51P0P6P2O2b09Z>@E:1]2=PCPDPOPF%6=,8I,2GPLPNb1b2b3197=P0b09^2=E:W7X81o"). Qed.

Lemma dtd_sr24 : forall x, 0 <= x < 256 -> (x * 16777217) ≫ 24 = x.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x2t_top2 ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h51zh61Hh72Hxh87fv_listh98hyp_listh:3lmph;1xp;2p;1p;3p;4p;7p;8p;6p;:p;<g0000j2>Tg000Lj10Tg0011j12Tg001lj2ETg002Hj2CTg003`j1BTg002cR0j28Tg001Oj2NTg004ej2;Tg00R4j1HTg00R^j2@Tg005Bj1<Tg005bj1:Tg00E1j3[Tg00S>j2YTg00Shj2FTg00TRj3DTg00U<j3WTg00:<j2VTg00Ufj1QTg00VNj4PTg00;Bj36Tg00W4j7OTg00WcR1j25Tg006Bj2MTg006`j1LTg007>j1KTg00=Kj27Tg007ij2JTg00X@j3ITg008oj44Tg009Zj2STg00:Vj2TTg00;\j3UTg00<;j4gTg00EQj1fTg00F3j8eTg00Xcj3dTg00?3j6=Tg00<mj1cTg00=nj6bTg00YFj4\Tg00?Qj6ZTg004Ej2]Tg00?mj3^Tg00Ygl:_Tg00ZXl<`Tg00HCj7aTg00Hgj7XTf0R2#0#0p=?%02#0#0#0p=9g00IKR3f1R4;62p=3P3g00LOR5P4P1P0g00[ER6g00[bR7g00\?R8g00\\R9P2M:_p=RP3P5f2R:P1P0P6P7P8P9g00]=R9P4P2M<`p=AP4g00IiR7g00JHR6P6g00JhR0P2g00KHFap=1P:P7P6P6P0P4P2FXp=G1>52g00LmR1#0R;#0#?#9R<#2R=,E2'CR>P3%0<#?#9#9#9R<#B#2R?,84R@%2;%B1#0#?#2R;'N';132:X53%H3RA/@ARA#<%:A%<39[3:%:3P9P2P41Y31R9%0<#2R<,F39D395W3RA1F3?9D39R9g00]lg00NeRBg00OERC'VRD%21RE/R4g00^H,@3%Q3'@#:P3P8AAE2AAAE29CPb:=6BCdFOb8b9184<,54/3@REePEP318:<,5:RE1;2<f3R9'3X53P31;:<RA/5:1329X53P3P51529/39X53g00MRR8#<RF%:8R81M34RG%L3RH%K3RIP31735RJ1J31R15I3g00N>RKP1C4'11SI0RLP2P:PD1T2:=6BCdAU354CgRCb1b2b3X431552/32^43P2P9O1b0PAPFP8PGPHPIP7P6P6P0P3PJg00KhRGP1C4,1IRAP3P1g00QMRB173=C4,1I5GI%f6P3P1PB173<RBC4,1I9GIAGePLPCb1b2b3X431>541E4<'C\>^43P2P9P:O2b09d:<E=1;E<P:P:P<PFP8%c3REPHPIP7P6P6P0P3PBPKPJC4,1IEbPLPCb1b2b3A63<5g00Oe[P2b0C\E=18:?P2EZb61]@;PFP8PEPHP3PJPG173;C4,1IPLPCb1b2b31>5;P2b09^@;E=W7X;3o"). Qed.

Section CANSEC. Context {rc : runConstT}.
Section TOP2.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : fmem) (DT W S mtl lo : Z) (src : list Z).
  Notation SP := (bv_unsigned sp).
  Notation FB := (bv_unsigned sp - 272).
  Notation POST := (huf_rdt_post huf_dt_ok ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DT W S mtl src lo m).
  Notation WALL := [(bv_unsigned sp - HUF_RDT_STACK, bv_unsigned sp); (DT, DT + DTABLE_BYTES mtl); (W, W + 8704)].

  (* [comment removed for export] *)
  Lemma x2_p1b : forall m1 h maxW rs0a nz rs0d sorted rv0 rv cells jdt jrest SYj RVj j8 j40 j16a j16b j152
      (q0 q8 x5 x6 x7 x9 x15 x16 x17 x18 x28 x29 x30 : word),
    read_stats src = Ok h -> X2PATH mtl h maxW rs0a nz rs0d sorted rv0 rv cells -> 1 <= mtl <= 12 ->
    1 <= hs_ret h <= 129 ->
    let tl := hs_tableLog h in let T := (if (tl <=? 11) && (11 <? mtl) then 11 else mtl) in
    0 < DT -> DT mod 8 = 0 -> DT + 4 * (1 + 2 ^ mtl) <= lo -> 0 < W -> W + 8704 <= lo -> lo <= SP - 4096 -> SP <= 2 ^ 47 ->
    (DT + 4 * (1 + 2 ^ mtl) <= W \/ W + 8704 <= DT) ->
    rw_cells usegs m1 DT [C4 (Z_to_bv 64 (mtl * 16777217))] ->
    u8arr usegs m1 (DT + 4) jdt -> length jdt = Z.to_nat (4 * 2 ^ mtl) ->
    u8arr usegs m1 (W + 992) (map (Z_to_bv 8) (hs_weights h) ++ jrest) -> zlen jrest = 256 - hs_nbSymbols h ->
    u32arr usegs m1 (W + 624) (map (Z_to_bv 64) (hs_rank h)) ->
    u32arr usegs m1 (W + 676) (map (Z_to_bv 64) (repeat 0 15)) ->
    u8arr usegs m1 W RVj -> length RVj = 624%nat ->
    u8arr usegs m1 (W + 736) SYj -> length SYj = 256%nat ->
    rw_cells usegs m1 (SP + -400) [C8 q0; C8 q8; CB 8 j8; C8 (Z_to_bv 64 (mtl * 16777216)); C8 (Z_to_bv 64 (hs_ret h));
                                   CB 40 j40; C8 (Z_to_bv 64 mtl); CB 16 j16a; C8 (Z_to_bv 64 (tl + 1)); CB 16 j16b;
                                   C8 (Z_to_bv 64 (W + 676)); CB 152 j152] ->
    rw_cells usegs m1 (SP + -112) [C4 (Z_to_bv 64 (hs_nbSymbols h))] ->
    rw_cells usegs m1 (SP + -108) [C4 (Z_to_bv 64 tl)] ->
    rw_cells usegs m1 (SP + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m1 lo (SP + -400) ->
    munch WALL m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 T) (Z_to_bv 64 (SP + -400)) gp tp x5 x6 x7 (Z_to_bv 64 maxW) x9
                            (Z_to_bv 64 (- (W + 624) - 1)) (Z_to_bv 64 (tl - maxW)) (Z_to_bv 64 (1 + 2 * (tl - maxW)))
                            (Z_to_bv 64 (W + 680)) (Z_to_bv 64 13) x15 x16 x17 x18 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (W + 992))
                            (Z_to_bv 64 (W + 624)) (Z_to_bv 64 DT) (Z_to_bv 64 W) s8 s9 s10 s11 x28 x29 x30 (Z_to_bv 64 tl))
                       F (Z_to_bv 64 (PHUF_RDT_X2 + 392)) fc None m1 (seg_rom usegs)).
  Proof.
    intros m1 h maxW rs0a nz rs0d sorted rv0 rv cells jdt jrest SYj RVj j8 j40 j16a j16b j152 q0 q8 x5 x6 x7 x9 x15 x16 x17 x18 x28 x29 x30
      RS XP MTL RET tl T DT0 DTA DTL W0 WL LOS SPB DJ RDT RDJ LJD HWr LJR RKr ZRS RVa LRV SYa LSY FRa NSr TLr FRb ST MU WM MI.
    unfold PHUF_RDT_X2. unfold HUF_RDT_STACK, DTABLE_BYTES, HufHarness.DT_BYTES in *.
    pose proof XP as (FM & MW & RS2 & SO2 & RV0 & RVR & FX & TL1 & TT & TL & LWS & NBS & LRK & RKR & WSR & XR).
    x2upto 428. x2norm. x2mk.
    rewrite (Z.mod_small (tl + 1 - (tl - maxW))) by lia. rewrite sl32_sr30 by lia. rewrite x2k_not.
    eapply evt_eq; [ | eapply (rs_loop (Z_to_bv 64 (SP + -400)) gp tp F fc) with (WK := W) (wEnd := maxW + 1) (rank := hs_rank h) (f := Z.to_nat maxW) (w := 1) (next := 0)
                         (rs0 := repeat 0 15) (m1 := m1) (m := m1) ].
    1: x2st.
    all: try (first [ exact RS2 | (split; lia) | lia | assumption
                    | refine (conj ZRS (conj (repeat_length _ _) (conj (munch_refl _ _) (conj (wmono_refl _ _) MI)))) ]).
    intros m2 rs0' next' E NX (RA & LR & MU2 & WM2 & MI2). injection E as <- <-.
    transport_after_call usegs m1 m2 MU2 WM2. clear MU2 WM2.
    x2upto 520. x2s32 RA (W + 676) 1 (Z_to_bv 64 nz).
    x2upto 520.
    replace (tl + 1 - (tl - maxW)) with (maxW + 1) by lia. rewrite (Z.shiftl_mul_pow2 (maxW + 1) 2) by lia. change (2 ^ 2) with 4.
    x2s32 RA (W + 676) (maxW + 2) (Z_to_bv 64 nz).
    x2upto 520. x2norm. x2mk. rewrite !x2k_not.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?M _) => set (m3 := M) in * end.
    set (rs0c := Zupd (maxW + 1 + 1) nz (Zupd (0 + 1) nz rs0a)).
    assert (RAc : u32arr usegs m3 (W + 676) (map (Z_to_bv 64) rs0c)).
    { subst rs0c. unfold Zupd. rewrite !map_upd_nat. replace (Z.to_nat (0 + 1)) with (Z.to_nat 1) by reflexivity.
      replace (Z.to_nat (maxW + 1 + 1)) with (Z.to_nat (maxW + 2)) by (f_equal; lia). exact RA. }
    assert (LRc : length rs0c = 15%nat) by (subst rs0c; unfold Zupd; rewrite !upd_nat_length2; exact LR).
    clear RA.
    pose proof (proj1 (proj2 XR)) as RC.
    rewrite (Z.shiftl_mul_pow2 (maxW + 1) 32) by lia. change (2 ^ 32) with 4294967296.
    eapply evt_eq; [ | eapply (so2_loop (Z_to_bv 64 (SP + -400)) gp tp F fc) with (m := m3) (WK := W) (nbS := hs_nbSymbols h) (ws := hs_weights h)
                         (jk := jrest) (js := SYj) (f := Z.to_nat (hs_nbSymbols h)) (s := 0) (rs0 := rs0c) (sorted := repeat None 256) (m1 := m3) ].
    1: x2st.
    all: try (first [ exact SO2 | (split; lia) | lia | eassumption | exact RC ]).
    1: { split; [exact RAc|]. split; [exact LRc|]. split; [rewrite omerge_none; exact SYa|]. split; [apply repeat_length|].
         split; [apply munch_refl|]. split; [apply wmono_refl| assumption]. }
    intros m4 rs0' sorted' y28 y29 y30 E (RA4 & LR4 & SY4 & LS4 & MU4 & WM4 & MI4). injection E as <- <-.
    transport_after_call usegs m3 m4 MU4 WM4. clear MU4 WM4.
    try x2mk.
    eapply evt_eq; [ | eapply x2_p2 ]; [ x2st | .. ].
    all: try (first [ eassumption | lia | reflexivity ]).
  Qed.

  (* [comment removed for export] *)
  Lemma x2_p1 : forall m1 h jdt jrest SYj RVj j64 j40 j152 (q0 q8 : word)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
    read_stats src = Ok h -> Forall (fun c => 0 <= c < 256) src -> 1 <= mtl <= 12 ->
    0 < DT -> DT mod 8 = 0 -> DT + 4 * (1 + 2 ^ mtl) <= lo -> 0 < W -> W + 8704 <= lo ->
    lo <= SP - 4096 -> SP <= 2 ^ 47 ->
    (DT + 4 * (1 + 2 ^ mtl) <= W \/ W + 8704 <= DT) ->
    rw_cells usegs m1 DT [C4 (Z_to_bv 64 (mtl * 16777217))] ->
    u8arr usegs m1 (DT + 4) jdt -> length jdt = Z.to_nat (4 * 2 ^ mtl) ->
    u8arr usegs m1 (W + 992) (map (Z_to_bv 8) (hs_weights h) ++ jrest) -> zlen jrest = 256 - hs_nbSymbols h ->
    u32arr usegs m1 (W + 624) (map (Z_to_bv 64) (hs_rank h)) ->
    u32arr usegs m1 (W + 676) (map (Z_to_bv 64) (repeat 0 15)) ->
    u8arr usegs m1 W RVj -> length RVj = 624%nat ->
    u8arr usegs m1 (W + 736) SYj -> length SYj = 256%nat ->
    rw_cells usegs m1 (SP + -400) [C8 q0; C8 q8; CB 64 j64; C8 (Z_to_bv 64 mtl); CB 40 j40;
                                   C8 (Z_to_bv 64 (W + 676)); CB 152 j152] ->
    rw_cells usegs m1 (SP + -112) [C4 (Z_to_bv 64 (hs_nbSymbols h))] ->
    rw_cells usegs m1 (SP + -108) [C4 (Z_to_bv 64 (hs_tableLog h))] ->
    rw_cells usegs m1 (SP + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m1 lo (SP + -400) ->
    munch WALL m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -400)) gp tp x5 x6 x7 (Z_to_bv 64 (mtl * 16777217)) x9 (Z_to_bv 64 (hs_ret h))
                            x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (W + 992)) (Z_to_bv 64 (W + 624)) (Z_to_bv 64 DT)
                            (Z_to_bv 64 W) s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X2 + 240)) fc None m1 (seg_rom usegs)).
  Proof.
    intros m1 h jdt jrest SYj RVj j64 j40 j152 q0 q8 x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31
      RS SRCB MTL DT0 DTA DTL W0 WL LOS SPB DJ RDT RDJ LJD HWr LJR RKr ZRS RVa LRV SYa LSY FRa NSr TLr FRb ST MU WM MI.
    unfold PHUF_RDT_X2. unfold HUF_RDT_STACK, DTABLE_BYTES, HufHarness.DT_BYTES in *.
    assert (P2 : 2 <= 2^mtl <= 4096) by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    destruct (read_stats_safe src read_ncount_safe (Forall_all_bytes _ SRCB)) as [(h' & RS' & SOK) | (e & RS')];
      rewrite RS in RS'; [ | discriminate]. assert (h' = h) by congruence. subst h'.
    pose proof (read_stats_ret src h (Forall_all_bytes _ SRCB) RS) as RET1.
    pose proof SOK as (STL & SLW & SNB & _). assert (TLR : 1 <= hs_tableLog h <= 12) by exact STL.
    assert (NBR : 2 <= hs_nbSymbols h <= 256) by exact SNB. clear STL SNB.
    assert (LWS : zlen (hs_weights h) = hs_nbSymbols h) by exact SLW. clear SLW.
    pose proof (repeat_length 0 15) as LR15.
    pose proof (x2k_mtl_byte' mtl MTL) as MTB'.
    x2upto 268. x2norm.
    if_cases B1; zify_cond B1.
    { x2upto 2036. x2norm. try x2mk.
      pose proof (stk_of_rw_cells usegs _ _ _ FRa) as S1. cbn [cells_size csize Nat.add] in S1.
      pose proof (stk_of_rw_cells usegs _ _ _ NSr) as S2. pose proof (stk_of_rw_cells usegs _ _ _ TLr) as S3.
      cbn [cells_size csize Nat.add] in S2, S3.
      pose proof (stk_merge usegs _ _ _ _ ST S1 ltac:(lia)) as S4.
      replace (SP + -400 + Z.of_nat 288) with (SP + -112) in S4 by lia.
      pose proof (stk_merge usegs _ _ _ _ S4 S2 ltac:(lia)) as S5. replace (SP + -112 + Z.of_nat 4) with (SP + -108) in S5 by lia.
      pose proof (stk_merge usegs _ _ _ _ S5 S3 ltac:(lia)) as S6. replace (SP + -108 + Z.of_nat 4) with (SP + -104) in S6 by lia.
      eapply evt_eq; [ | eapply x2_epi with (r := 18446744073709551572) ]; [ x2st | .. ];
        first [ eassumption | lia | (intros; lia) ]. }
    destruct (x2_model_path mtl src h MTL SRCB RS ltac:(lia)) as (maxW & rs0a & nz & rs0d & sorted & rv0 & rv & cells & XP).
    pose proof XP as (FM & MW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LRK & RKR & _).
    x2br. x2norm. rewrite (x2k_tsel mtl (hs_tableLog h)) by lia.
    destruct ((hs_tableLog h <=? 11) && (11 <? mtl)) eqn:C.
    all: x2upto 352; x2norm; try x2mk; rewrite ?x2k_not;
      match goal with H : rw_cells usegs _ (SP + -400) _ |- _ => rewrite ?x2k_hdr in H by lia end.
    all: eapply evt_eq; [ | eapply (fm_loop (Z_to_bv 64 (SP + -400)) gp tp F fc) with (WK := W) (tl := hs_tableLog h)
                             (c11 := 0) (c12 := 1) (rank := hs_rank h) (f := Datatypes.S (Z.to_nat (hs_tableLog h))) (w := hs_tableLog h) ];
           [ x2st | .. ].
    all: try (first [ exact FM | (split; lia) | lia | eassumption ]).
    all: intros y15; eapply evt_eq; [ | eapply x2_p1b with (h := h) (maxW := maxW) (rs0a := rs0a) (nz := nz) (rs0d := rs0d)
                                          (sorted := sorted) (rv0 := rv0) (rv := rv) (cells := cells) ];
           [ cbv zeta; rewrite ?C; x2st | .. ].
    all: first [ eassumption | lia | reflexivity ].
  Qed.

End TOP2.
End CANSEC.

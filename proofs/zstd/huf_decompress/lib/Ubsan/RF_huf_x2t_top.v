(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT
  HufPure_HufStats HufPure_HufStatsRT HufPure_HufX1 HufPure_HufX2 HufPure_HufTableX2 HufPure_HufTableX2RT HufPure_FseReadBridge.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem RunConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2 WStr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_h_iface RF_huf_tbl_iface RF_huf_tbl_iface2
  RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_tk RF_huf_bdt_model RF_huf_x2t_model RF_huf_x2t_fr RF_huf_x2t_pre RF_huf_x2t_fx RF_huf_x2t_path RF_huf_x2t_top_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x2t_top () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3mulC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX28x2_cellsC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model3ox2C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_iface9huf_dt_okC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_iface8x1_bytesC47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_iface8x2_bytesI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission4SpecDHufPure_HufTableX2RT?x2_cells_lengthC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List<firstn_skipnC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_appI47Corelib4Init5Peano2le00C47Corelib4Init5Peano2ltC56Stdlib6ZArith4Znat5Nat2Z2idC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model:ox2_prefixK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or02C47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes4list02C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula06I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_defaultC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100K46Stdlib9micromega:ZMicromega;ZArithProof01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_rdt_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiI4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;stk_releaseC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64K46Stdlib9micromega7EnvRing5PExpr03C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface=HUF_RDT_STACKK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC56Stdlib6ZArith4Znat5Nat2Z8inj_succI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr07K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<Z_to_bv8_modC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00I47Corelib4Init5Logic5False00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats:read_statsC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_x2t_path6X2PATHC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats6hs_retC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats;hs_tableLogC56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u32arrC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_pre3PRwC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model5rv_atC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model6omergeC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x2t_fx8x2_frameC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats7hs_rankC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX29find_maxWC47Corelib5Lists7ListDef6repeatC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats<hs_nbSymbolsC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats:hs_weightsK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX27fill_x2C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX26rv_idxC56Stdlib6ZArith6BinInt1Z4to_NK46Stdlib;setoid_ring<Ring_polynom5PExpr09C56Stdlib6ZArith6BinInt1Z9pow_add_rC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7upd_natC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model?upd_nat_length2C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model8ox2_noneK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC46Stdlib5Lists4List=repeat_lengthC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x2t_fx7x2A_invC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init5Logic2or01C47Corelib4Init5Logic8iff_reflK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le4C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u8arr_transportC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib5FrameFstk_transport_disjointC47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr:upd_lengthc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_top9upd4_all2C5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_fdw_tk=stk_frame_endc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_top8x2_dt_okc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_top6x2_epiC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_top7dtw_b02C5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x2t_fx7fx_loopC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZupdC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX2;rank_start2C5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX25sort2C5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX29rank_val0C5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX2=rank_val_rowsC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameI47Corelib4Init5Logic4True00I5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats6hstats00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5msize01C56Stdlib6ZArith4Znat5Z2Nat2idC5ARocqVerifyHarness?AgentSubmission3Lib3Arr@u32arr_transportC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model=omerge_lengthC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge=bv_lts_zero_lC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffK46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula0:C47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool>negb_false_iffC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8K4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC56Stdlib6ZArith6BinInt1Z6shiftlC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeK4ELinuxProcessSemantics5Riscv5Instr5instr03C45stdpp9bitvector;definitions8bv_swrapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_top5x2_p3C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u32arr_frameK46Stdlib9micromega5Tauto4kind02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop03C5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u32arr_store_okC56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u32arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_boundK46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model;map_upd_natC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC56Stdlib6ZArith6BinInt1Z6shiftrK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission6Common4WStr?u32arr_of_u8arrC5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u32sK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC47Corelib4Init5Logic7f_equalC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x2t_model<rv_at_weakenc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_top6x2_p2tK4ELinuxProcessSemantics5Riscv5Instr5instr0BC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_mulhuC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7m_mulhuC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_pre9rvr_outerC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zb_shl_shrC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x2t_pre8rv0_loopC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrK4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5mulop04".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma x2_dt_ok : forall m3 DT mtl T cells jt,
  1 <= mtl <= 12 -> T <= mtl -> zlen cells = 2 ^ mtl -> length jt = (4 * length cells)%nat ->
  x2_table_ok (x2_cells cells) T ->
  (forall i, 0 <= i < 2 ^ T -> exists c, nth (Z.to_nat i) cells None = Some c) ->
  u8arr usegs m3 DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 T; Z_to_bv 8 mtl] ->
  u8arr usegs m3 (DT + 4) (ox2 jt cells) ->
  huf_dt_ok m3 DT mtl.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x2t_top ()) [] "p'0h04__x1h13LJ0h24__p1h34__x2h44cstrh55cstr0h67__arithh75cellsh84__ffh94__p2h:8__varmaph;5__with<4__x3h=1ch>1ih?2DCh@1HhA2H4hB1nhC1xi001xhD2z4hE2HchF2_HhG4__p3hH4__x4hI1ahJ3bs1hK3bs2hL1lhM1mhN4segshO2tlhP3COVhQ2DDhR2DThS2H5hT2HMhU2HThV2HihW3Hi0hX2LChY2LJhZ1Ph[2PTh\1Th]2T1h^2T2h_3XOKh`5cstr1ha1ehb2jthc2m3hd3mtlhe2tthf1yhg2z5p%0p&0p;1p;2p;4p;3p;5p;6p;Bp;<p;7p;8p10000p4p7210g000\R0p4p710p8g001:j1RTg001_k10BTg002=k10=Tg002`k103Tg003Bj1ZTg003bj1kTg004@j1wTg004eR1j28Tg005Aj21Tg005^j25Tg006>j1mTg006]j2?Tg0074j1<Tg0089j2bTg009<R2j2JTg009XR3j22Tg00:3R4j17Tg00:Sk10>Tg00;5j2uTg00;WS00j2FTg00<1j2GTg00<Wk108Tg00=7k404Tg00=ij26Tg00>Fj2LTg00?Ej2oTg00@@j2dTg00ABk300Tg00BCR5j10Tg00BcR6j2:Tg00C@k10?j3XTg00CZk20CTg00D=k30`Tg00DZj4[Tg00EAj1DTg00Efk10YTg00FDk10XTg00Fbk10WTg00GMj2lTg00H0k20UTg00HRk20@Tg00Hlk20TTg00IXk30STg00J7k40RTg00Jij2jTg00KGj2VTg00Kjk50QTg00LQk40PTg00M9k20<Tg00N<k10OTg00O<j3ATg00O[j1hTg00P[j2tTg00Q5j4sTg00Qgk30:Tg00RBk10NTP0k609Tg00SPj2eTg00T2k20MTg00T[j2_Tg00UDk305Tg00Umk106Tg00VKk207Tg00Vlj3rTg00WUj2^Tg00XAk302Tg00Xdk401Tg00YOj3qTg00Ymj3pTg00ZJk30LTg00Zkj4HTg00[`k50KTg00\YR0k20JTg00]3R7j2~Tg00]Kk10HTg00]ij6vTg00^Ej4gTg00^_k60FTg00_ej4`Tg00`@k30ETg00`Zj4}Tg00a6j3zTg00aVmB0DTg00b<l<yTg00baj4{Tg00cLk70ATg00d0k40VTg00dNj8|Tg00e2k60_Tg00eVk70^Tg00f:k20]Tg00fWm<0\Tg00g<k30[Tg00gek70ZTf2R8f1R9'8f0R:'2p=>159:#0p=Bg00hIR;?X9:p=4g00hgR<?X9:p=Qg00iFR=/8:p=;f5R>f4R?f3R@P8P9C};X:p=PAz89:9z?@p=Mg00idRAP9P:g00jdC}p=c20@;:p=9P<P<P<P;P;P;g00kfP5P5P5P6g00lFP>P?P@P8P9P:NB0Dp=]P<P;P:P5P9P8P@P?P>f6R6f7RBf8RCM<yp=\P;P9g00liP:C{p=YP9g00mPRDg00moREPEg00nORFP:g00noRGK0Ap==1J=:p=CP;P8P9P:H0Vp=IP8PDPEPEPFP;P9g00oOP:C{PGK0Ap=OP@PDPEPEPFP8P9P:G|p=xP9PDPEPEPFP:J0_p=iP8PDPEPEPFP9P:K0^p=Eg0106RGP8P9P:CHp=3AX;:=p=S129:,28p=W1289/t:p>0;20]=:p=@P;P<P;P;P4P?P5P@g010kP8P9P:N<0\p=fAX;@8,2?189=/2:'tp=NB0[;9:p=Kg011XR4?z9:p=TP;P9g012DP:C{p=UP8PDPEPEPFP9P:K0Zp=nP6PDPEPEPFP>P?P@PDPEPEPFP8P9P:G|G|p=aP<P;P0P5P1g012kP>P?P@P8P9P:M<yp>0IP<P;P7P5P2g013MP>P?P@P8P9P:M<yp>0Gg013oR2#RR5#RR7#RS01#R#R#R$0B$0=Q01$0BR1$0=R0$03[RD&03ARH#Z%Z0RI%k2RJ%w2S02#RS03#R#kRK,8@7>@18@?1BH@%k5RL/1>'4150@S04g014TS05#mS06#mS07#mS08#mRM15H?'?'Q%<>/b6%;:RN11LC,J:'2PHPH%78f9RO&0>ARP1uA:RQEPX=A,FA[^>;PGf;RRf:RSP01G1ORTP01G1JRUP01G1CP0PT&080RTDMDMH04PGf<RV%k7RW,6R1LBCH04P@%<O/bSP3g0153RX,8R9>JR11LR%<S,oA11LV,J:,2Nf=RY%79RZ%<V'c'd[^>;3>f?R[f>R\<00YP:18YX9>JY11L\%<Y,oA11L[RX,J:,2Nf@R]%<[,cZ'd[^>;3>P3%<\,oA,8X11L],J:,2NfARX%<]R^,cZ'd[^>;fCR_fBR`<00XP:11LX1oA^'811L_R^,J:,2NfDRN%<_,cZ'd[^>;PLP_PN150XRX15H`RZ,?MRa'Q%0XRb%0ZRc,:WRd'4Re&0?<Rf&0?;Rg%09Rh%0:S09'41Q9:20C9:40`Xf<XC<RiPXPb%9bPaPdPMPW%9WRdPZPc%9cE]M9\PYC[RYPe15H_Rc#DRZ%0cRa#;Rb150_RX#DRj%0XRk#;Rl&084Rm%Z4R4&0Y;Rn&0X;Ro&0W;Rp1l;=Rq1l;L'Y'=20UpFRFP:P8g016;Rrg016[Rs+0@20T:8=XrsdB0S;=9H0RRsb8b:b;%CLP:b6Rrb5b4b1PYPePZPbPjPlPmP41j;8S0:?I9nPoPp1V;2Rl1V;5Rj5OpS0;&0>EREQ0;CxPFPsb8b:b;X0;X3;S0<18:91898[^0;^3;S0=P:fHRbfGRZP_O3b6b5b4b1I0Q11LNRe,8^PLPN150`R`1?McR^'Q%0`RY1:WaRt'4RuPfPgPiP`PY%9YP^PtPMPWPdPcPa%9aE]M9\P\C[RaPu15HNRc#DRt%0cR^#;RY150NR`#DRv%0`Rw#;RxPrb5b4b1PaPuPtPYPvPxp-0RxPmP41j;9PoPp1l;J=Opl1ip@5EpPEAOpqlS0>CxPFPsb8b:b;X0;W2A>J:9%;9S0?[^0;^2xP:18bKPbPSO3b6b5b4b1H0P%CeP;fJRefIRSP01G1bRKP01G19P01G1:RvP0PKPTDMDM33%S9S0@g017;RK#ZRY1BK:RK16SJRt,1L'420<:9RufKRa16eWRr11L9Ry,:L#7&0O:S0A5A0Rz339>9t3WX7Y'F149J%ZARt1BA:R{11LSR|'41b:9R}1:Wy#7%h:S0B5A0Ry93ar9>9S3WX7t'F'240;'2XO;,F;Xe;PJP;P01G1ZR~P0PUP0PvP0P~PTDMDM93Sb%SJS0C16bJR~,1L,4K16SWRv=3ez9>9~7WuX7Y,FY14JJRu11LbR~,4{A3evy9>9b7W}X7t,Ft'240;'2XO;fER}P0fFRy,G1RzP0PUP01G1}P0PzPTDMDMRT93bZRzQ0C16ZJR1,1L,4K20<:y16bWRK11LyRU,:L#7Q0A5A053S9>y13WX7Y,FY'2S0C11LZRY,4{1b:y1:WU#7S0AQ0B5A093SK9>yZ3WX7tR{,FtR1,2uS0B'tPGPbPZ1B0TCs>0:zVQ0CQ0BPuP1%9JPtP{%<NR{15A{S0D#0/4U1b{}Rt18}yRJ16ZW11L}R1,:WRu#7Rz%h{5A053bR{'2RT'2P<PcQ09/4YXB<P]Q0D&0NNJ09PtPTP\PJP{1?McR{,QX1:W^RJ,4kR\PfPgPiPXPk%9kP{PJPMPWPdPcP^%9^E]M9\P[C[S0DP\15H}R[#DS09%0[R^#;S0E150}Rc#DRJ%0c#;RcQ0<Q0=P:PePSP}O3b6b5b4b1%71R{,?MRk/QzS0=%@1RX,:WRT%@uRt'4PfPgPiPkPTPMPWPdP{PXP:XC;S0<%@:XC;RXP1P1%91DfE]PzPtQ0<PXPuPu%9uDfM9\Q0DP\Q09Q0EPJPc1:W~Rc,e=%Cc%@cRJPcPc%SJDN1:W|#@P;11LeRJ,e=%CJ%@JS0EPJPJQ0E#SDN11La#@P;20M;WRcQ08,_;R\605;&062-07;S08Q07,_;R25r;Q05,_;Ru'K'Kg018;Rt'^&067-07;=r;\1K2uS05'K/^tQ06,_;S06:05;c/K2/^tRc1Tcm'T'T'TP4Q0:1j;@Rc9In@7I9PoPpQ02#w,V;R\,Yq,=pR71Ul\,=p5EpAOp\q1ip>S025Ep5npPEPp1ip6Rz1l;WR1>02;\R\,Uj,=p5EpAOp\q1ipBS0:5Ep5npPEPpP7PEB02;1l/Uj,=pCxFaPFPsb8b:b;X0;X3;X<;X2xX9xXGx%C8P:P8P8P@DNP>P81:W@R1P1P6DN%C?R7141?[[[^0;^3;^<;^2x^9x^GxP:%S@fMR1,1LR\,:W#CQ0@P\P@P9P8P?PCO9b6bgbSbDbAb5b4b1H01Q0=P<%7UR{,?MRT%<y#h9A0:93evXB<PI1LN}Rk9A0TA3ev:XLIP3A3SKkPGPSPK1B0kCs%7YRY,?M1L}y5A093evPV1LyZ93arPGfLRr16aW1LZb,B0CsPI1LbSRVfNRv161W;3:XLIP9%7J,?MRJ=A0VAq0JV5p0RkB0L0JVJ0916rW=31kg018g#ZRkP3P?P@P8Ap09:CHP>P?P@P8CHP>P?1B08,6@P9CH'2[R3P?P@P8P9CHP?P@1B09,68P:CH'2P>P?P@Ap089CHRJ[P6P>P?P@CHP6P>Q04#0,6?P8CH'2\JP?P@P8P9P:I0KP9n2001000000120000000XKIXJIXI;XMDWNP3^KI^JI^I;^MD^NkP:PGfORG16vWRk11LrRD#7,?MRI1LeaR35A0RJAq0I3R3P9O6A3GkJ1B0J,6k=3G3'2fPR316GWRG%7\,?MRk1LarRJ5A0RI331B0I,6GAq0kJ533<0::b?b@b?WFW?P9P:O2n2001000000121000000%<}#h9A0TP{P}PN20J{[%@URN/8^P{PNQ0<PXPUPU%9UDfP[P^%9^RUJ0I1?M[RN,Q`1:W^R{,4wR}PfPgPiP`Pw%9wPNP{PMPWPdP[P^PUE]M9\P]C[P}15HyR}#D%0}#;150yRy#D%0y#;1e=|%C|%@|RyP|P|%SyDNQ0EP;1_;MRyQ08Q065r;/Ku,K2'K/^t/TmP41j;?9In8AIc?n7I9PoPpQ03,V;R2,Ul,=p9EpzAOp2qQ0:5Ep5npPEPp1Yq2,=pPEPp%w5,V;R59Op2PEPp1Uj5,=pPEQ0;FaFaPFPsb8b:b;X0;X3;X<;XH;X2xX9xP?P:P@P@P>DN18>?14?>18?>[[\7[^0;^3;^<;^H;^2x^9xP:Q0@%CDPDP\1BHaP9P8PBPCPZO:b6bDbAb5b4b1H01P]1~:YP]Ph%7~R],~9%@~,JhRYP9Ph%9hP]PXP~O1Q0<PXP~P~%9~DfJ0GP:C[PY150ZRZ15HbRY,?MR~'Q%0ZRX%0YR],:WRh'4RCPfPgPiPZPX%9XP~PhPMPWPdPYP]%9]E]M9\P_C[PC%D@%0@RC#;15HeR_#D%0_#;150eR0#D%00#;1e=\%C\%@\R=P\P\%S=DN11Lv#@P;Q05,Ky/^t/TmP4AIc@n?I8n?I9nPoPpQ02Q01,V;Ro/Uj,=p5EpAOpjq=Epz5npPEPpQ0>PEPp1Ylo,=pPEPp1Yqj,=pPEQ0>1Ylj,=p5EpFaFaPFPsb8b:b;X0;X3;X<;X2xX9xP@P8P9P9P?DNQ0?1J8?%;?1J?>'2\7[[[^0;^3;^<;^2x^9xP:Q0@11L3R3#CP9P3%0OP8P>PBPRO9b6bDbAb`b5b4b1bWO2PHPH%08#7PbPPPQEPX=A,FAQ00PAPHPH%7CPSPPPQEPX=APHPHP?PePPPQEPX=A,FAP:PHPH%0>#7PaPPPQEPPAPHPHPBP1PPPQEPX=AP9P<%06#7PHPHP:P1PP1uA8EPXB<P:P6&0H6EvPHPHP6PrPP1uA9EPP:bECgWEX=AP9P:O2n2001000000120100000baWVX><J0FEvQ0AP:Evb@C`C`C`CgC`40EC`CgCgb[bZWFW^P9P:O2n2001000000121000000W@W]P9P:O2n2001000000121000000b@W?WQWPW_WYWXWUWTWbW7X\;Xd;XR;Wco"). Qed.

Section CANSEC. Context {rc : runConstT}.
Section TOP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : fmem) (DT W S mtl lo : Z) (src : list Z).
  Notation SP := (bv_unsigned sp).
  Notation FB := (bv_unsigned sp - 272).
  Notation POST := (huf_rdt_post huf_dt_ok ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DT W S mtl src lo m).
  Notation WALL := [(bv_unsigned sp - HUF_RDT_STACK, bv_unsigned sp); (DT, DT + DTABLE_BYTES mtl); (W, W + 8704)].

  (* [comment removed for export] *)
  Lemma x2_epi : forall m' r (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    400 <= SP -> SP <= 2^47 ->
    rw_cells usegs m' (SP + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m' lo (SP + -104) -> lo <= SP + -104 ->
    munch WALL m m' -> wmono usegs m m' -> mem_inv usegs m' -> 0 <= r < 2^64 -> (r < 2^64 - 119 -> huf_dt_ok m' DT mtl) ->
    evt usegs POST (MS (mkR y1 (Z_to_bv 64 (SP + -400)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 r) y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                       F (Z_to_bv 64 (PHUF_RDT_X2 + 2036)) fc None m' (seg_rom usegs)).
  Proof.
    intros m' r y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 SP0 SPB FR ST LOS MU WM MI R0 ROK. unfold PHUF_RDT_X2.
    repeat zstep.
    eapply stk_release in FR; [| exact ST | lia]. cbn [cells_size csize Nat.add] in FR.
    replace (SP + -104 + Z.of_nat 104) with SP in FR by lia.
    apply evt_done. unfold huf_rdt_post. do 16 eexists. split; [reflexivity|].
    unfold HUF_RDT_STACK in *. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FR|]. split; [exact R0|exact ROK].
  Qed.

  Lemma upd4_all2 : forall (l : list byte) a b c d, length l = 4%nat -> upd (upd (upd (upd l 0 a) 1 b) 2 c) 3 d = [a; b; c; d].
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x2t_top ()) ["CANSEC"; "TOP"] "p'0h01Hh14__p1h22H0h37__arithh44__ffh58__varmaph65__with72l0h84__x1h91li001lh:1xh;1ah<1bi011bh=1ch>4cstrh?1dh@2x0hA2x1hB2x2hC2x3hD2x4hE1yp;1p;2p;3p;<p;4p;7p;6p;8g001:j1ITg001_j1dTg002=j1ZTg003BR0j1JTg005^j2HTg006>R1j16Tg00<Wj1KTg00C@j38j1OTg003bj1GTg00BCR2j1ATg00CZj2\Tg00D=j3[Tg00HRj27Tg00b<l<MTg00DZj4?Tg00Efj1YTg00FDj1XTg00Fbj1WTg00GMj2>Tg00:Sj1VTg00H0j2UTg00Hlj2TTg00IXj3STg00J7j4RTg00a6j31Tg004@j1QTg00=ij2CTg00EAj1cTg004ej2PTg00Jij2bTg00KGj2aTg00baj4NTg021=j3@Tg02>_j4FTg00cLj7_Tg00e2j6^Tg00dNj8`Tg00fWl<]Tg00hgR3f1R4f0R538p=:f2R6/H4=835p=2P6P4g014TR7P5CFp=5f6R8f5R9f4R:f3R;P6CFP4P5CFp=3A164591:;p=0P:P;P6P4CF=895p=4g00hIR<?845p=<P<P4g012DP5CNp==P4g00mPR=g00moR>P>g00nOR?P5g00noF_p=9P4P=P>P>P?P5E^p=LP;P=P>P>P?P6P4P5G`p=;P3P<P5P2P4P6P;P:P9P8f7R=f8R@M<Mp=D1C64/C5p=EP3P3P<P<P1P2P2P;g02?OP6P4P5M<]p=Bg013oR1#IRA#IRB#I#d#ZRC#JRD1HC:RE%67RF#6RG#6RH#6RI':P0PCA2C5IPDPCPCPCA5C48PFP9PGP:F3PHP;PCP8PCP9PCP:PCP;%KCRJD0D0E4]0P9A2CJIA837Ig00iFRK%GBRB58<RLP3P<%O3RMP2%O<R2%A4%A5'<1:451\453[XE3X:3R3P7PK17<KPIPB17<BR7M<MP5C?PLp-0RNg011XRO#KRP%JORO%Y<RQ%X<RR%W<RS1><KRT1><BRU'=,9S%V>R>1LS6RVC;1US?R?P5P6g016;RWg016[RX'71T56=8WXdAS<K4CRRXb4b5b6W1P4\L^1NP5PDPCPCPCA5CJ=PFP8PGP9F3PHP:PCP=PCP8A1C:JRL91C9D0E4P4O2b3b2W0P0PCA1C65RW=2CIPDPCPCPCA1C;4RYf:RZ55CPFf9R[PGP@F3PHP=PCPZPCP[PCP@PCP=PJD0D0E4]0P5A1C4JR\=2CI1:FI%G1R]/<BR^PMP2P3PFP]17<]PIPBP7M9DP5C?P^PPPOPQPRPS1><]R_/=U,9SP>PVC;P?PXb4b5b6X1NP4\^^1NP5PDPCPCPCf;R^95CLPFPZPGP[F3PHP@PCP^PCPZPCP[PCP@PJD0D0E4P4O2b3b2W0P0PCA1C8WRW=2CIPDPCPCPCA1C=YRYf>R=55CPFf=R8PGf<R`F3PHP^PCP=PCP8PCP`PCP^PJD0D0E4]0P5A1C9\R\=2CI1:GI%GARA/<BRaPMP2P3PGPA17<APIPBP7M9DP5C?PaPPPOPQPRPS1><A/=U,9SP>PVC;P?PXb4b5b6X1NP4\a^1NP5PDPCPCPCA1C@LRLf?R@55CPFP=PGP8F3PHP`PCP@PCP=PCP8PCP`PJD0D0E4P4O2b3b2W0P0PCA1CZWRW=2CIPDPCPCPCA1C^YRYfBR^55CPFfARZPGf@RaF3PHP@PCP^PCPZPCPaPCP@PJD0D0E4]0P5A1C[\R\=2CI1:HI%Q1#GRA/<BRbPMP2P3PHPA17<APIPBP7M9DP5C?PbPPPOPQPRPS1><A/=U,9SP>PVC;P?PXb4b5b6X1NP4\b^1NP5PDPCPCPCA1C`LfCRL55CPFP^PGPZF3PHPaPCPLPCP^PCPZPCPaPJD0D0E4P4O2b3b2W0P0PCA1C=W=2CIPDPCPCPCA1C@YfFRY55CPFfER@PGfDRWF3PHPLPCPYPCP@PCPWPCPLPJD0D0E4]0P5A1C8\=2CIPCP@PCPWPCPLPCP^PJD0D0,7DW0PCPZPCP8PCP[PCP9A1C45D0D0=2CI1HC4R^#6RL#6RW#6R\#6RY#6R=/:I%A^R0/C]?E]]?E]]/<BRaPMP2P3P=1C5]X:<R=P=P=P=P=P0O1R3O1R2O1RMO1R`O1P=PYP`P=P\PMP=PWP2P=PLP3P=P^P017<0CBCBCBCBCBPIPBP7M9DP5C?Pa1HC6Ra#c%Aa,PKPPPO1b<4PRPSP<PTg00oO1a<1R1CN,9SP>PSA@<1_=@<_=@<_=@<_=@<_/=U,9SP>1LS;C;C;P?PXb4b5b6X8<X1N1PK51C4]?E]]?E]]/<BP;[[^8<^1NP5PDPCPCPCPCP@PCPZPCP8PCP[A1C9:D0D0fLR:55CPFfKRFPGfJRGF3PHfIRHPCP:PCPFPCPGPCPHPJD0D0E4%AEP4P6O4b3b>b2W0X9DXDCP4P5O2n10110000020021101100X7DXCCP4P5O2n10110000020121101100X7DXBCP4P5O2n10110000020121101100X7DXACP4P5O2n10110000020121101100X7DX@CP4P5O2n10110000020121101100P5O1W0X?CX=CX<CX;CW9o"). Qed.

  Lemma dtw_b02 : forall mtl, 0 <= mtl < 256 -> Z_to_bv 8 (mtl * 16777217) = Z_to_bv 8 mtl.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x2t_top ()) ["CANSEC"; "TOP"] "h01zh11Hh22H0h37__arithh44__ffh58__varmaph65__with77fv_listh88hyp_listh93lmph:4mtl0p;2p;1p;3p;4p;7p;6p;:p;<g004ej2[Tg003bj14Tg009<j2BTg009Xj2ZTg001:j10Tg004@j1GTg00BcR0j22Tg02@3j1CTg01<Xj27Tg00<Wj19Tg003Bj15Tg00a6j3YTg02@]j2TTg02AGj2:Tg02B1j38Tg02B[j3OTg00HRj2>Tg02CEj1JTg02Cmj4FTg00C@j31Tg02DSj7ETg00=iR1j2=Tg02EBj26Tg00Efj1DTg00FDj1HTg00Fbj1ITg00GMj2<Tg00baj4ATg00cLj7MTg02Ebj6NTg00H0j2@Tg00Hlj2PTg00IXj3QTg00J7j4?Tg02FFj4RTg000\j6STg00]ij6XTg02Fgj3WTg02G`l:UTg02HQl<VTf0R2#0#0#0#0p=3%02#0p=Lg00hIR3g00iFR4f1R5P1P0g01:PR6g02I>R7g02I[R8g02J8R9P2M:Up=KP3P4f2R:P1P0P6P7P8P9g02JYR9P5P2M<Vp=;1[42g013oR7#3#3R6#4R0,B2'Z%36#3R6#0#L#3#G#4R1,25R;%C3R</7<R<#9%5<%939Y3:%53P9P2P51T37R9%46R6,:398391:305835O3R<1:319839R9g02KHg016;R=g016[R>'>R?%47R7/K5g02Kd,73%J3'7#5P3P8A;72<A;729CFb9=1=>dFEb7b81256/20,=5=13;R;eP;P312:6R6/20,=:R;1620f3/60R7513X03P316:0R9A1327X031>3916;0P:P6P0g011XR6#9%56%D3%H3%I3R6g00mPR;g00moR9P9g00nOR7P6P;P9P9P7P31<30g012D1<34CAg00noFMEN1@67P2P:P?1P2:=1=>dAQ345C?b4b5b6A1304g02LL[P2b3CRES12:1P2EXb27W5W1X:3o"). Qed.

  (* [comment removed for export] *)

  Lemma tp_shl2 : forall x, x ≪ 2 = 4 * x.
  Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia. Qed.

  Lemma tp_lx63 : forall o, 0 <= o < 9223372036854775808 -> (Z.lxor o 9223372036854775808 <? 9223372036854775808) = false.
  Proof. intros o Ho. change 9223372036854775808 with (2 ^ 63). rewrite zb_lxor_pow2_small by lia. apply Z.ltb_ge. lia. Qed.

  Local Ltac pnorm U :=
    repeat match type of U with
           | context [Z.lxor ?o 9223372036854775808 <? 9223372036854775808] => rewrite (tp_lx63 o) in U by lia
           end;
    repeat match type of U with
           | context [?a <? ?b] => rewrite (proj2 (Z.ltb_ge a b)) in U by (rewrite ?Z.mod_small by lia; lia)
           end;
    cbn in U.

  Local Ltac pchk U := exfalso; rewrite ?tp_shl2 in U; rewrite ?signed_small2 in U by lia;
    first [ lia | (Z.div_mod_to_equations; lia)
          | (pnorm U; first [discriminate | lia | (Z.div_mod_to_equations; lia)]) ].

  Local Ltac cgo stops := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
        let b := eval vm_compute in (existsb (Z.eqb pc) stops) in lazymatch b with false => zstep end
    | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 82516 else _) _ _ _ _) =>
        rewrite ?sx32_small by lia; rewrite ?zx32_small2 by lia; rewrite ?swrap32_small by lia; rewrite ?tp_shl2;
        let U := fresh "U" in if_cases U; zify_cond U; [pchk U |]
    | |- evt _ _ (MS _ _ (if _ then _ else Z_to_bv 64 82516) _ _ _ _) =>
        rewrite ?sx32_small by lia; rewrite ?zx32_small2 by lia; rewrite ?swrap32_small by lia; rewrite ?tp_shl2;
        let U := fresh "U" in if_cases U; zify_cond U; [| pchk U]
    end).

  Local Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map,
    ?omerge_length, ?ox2_length, ?upd_bytes_length, ?Zupd_length in *.

  Local Ltac fixpc := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
    let v := eval vm_compute in z in change z with v end.

  Local Ltac trside := cbn [disjoint_from cells_size csize Nat.add]; rewrite ?length_map, ?omerge_length;
    repeat split; try exact I; lia.

  Local Ltac trall M0 M1 MU2 WM2 := repeat match goal with
    | H : rw_cells usegs M0 ?A ?cs |- _ =>
        let T := fresh "TT" in pose proof (rw_cells_transport usegs _ M0 M1 A cs H MU2 WM2 ltac:(trside)) as T;
        clear H; rename T into H
    | H : u8arr usegs M0 ?A ?bs |- _ =>
        let T := fresh "TT" in pose proof (u8arr_transport usegs _ M0 M1 A bs H MU2 WM2 ltac:(trside)) as T;
        clear H; rename T into H
    | H : u32arr usegs M0 ?A ?bs |- _ =>
        let T := fresh "TT" in pose proof (u32arr_transport usegs _ M0 M1 A bs H MU2 WM2 ltac:(trside)) as T;
        clear H; rename T into H
    | H : stk usegs M0 ?l ?hi |- _ =>
        let T := fresh "TT" in pose proof (stk_transport_disjoint usegs _ M0 M1 l hi H MU2 WM2 ltac:(trside)) as T;
        clear H; rename T into H
    end.





  Lemma tp_split : forall m1 A cs k, rw_cells usegs m1 A cs ->
    rw_cells usegs m1 A (firstn k cs) /\ rw_cells usegs m1 (A + Z.of_nat (cells_size (firstn k cs))) (skipn k cs).
  Proof. intros m1 A cs k H. rewrite <- (firstn_skipn k cs) in H. exact (proj1 (rw_cells_app' usegs m1 A _ _) H). Qed.

  Lemma tp_cb_at : forall m1 A cs k n j, nth_error cs k = Some (CB (8 * n) j) -> rw_cells usegs m1 A cs ->
    exists ws, length ws = n /\ rw_cells usegs m1 A (firstn k cs ++ map C8 ws ++ skipn (Datatypes.S k) cs).
  Proof.
    intros m1 A cs k n j HN H.
    assert (HK : (k < length cs)%nat) by (apply nth_error_Some; rewrite HN; discriminate).
    assert (EN : nth k cs (CB 0 []) = CB (8 * n) j) by (apply nth_error_nth; exact HN).
    rewrite <- (firstn_skipn k cs) in H.
    rewrite (x2k_skipn_nth_cons cs k (CB 0 []) HK), EN in H.
    apply (proj1 (rw_cells_app' usegs m1 A _ _)) in H as (H1 & H2).
    apply (proj1 (rw_cells_app' usegs m1 _ [CB (8 * n) j] _)) in H2 as (H3 & H4).
    destruct (cb_to_c8s n m1 _ j H3) as (ws & LW & HW).
    exists ws. split; [exact LW|].
    apply (proj2 (rw_cells_app' usegs m1 A _ _)). split; [exact H1|].
    apply (proj2 (rw_cells_app' usegs m1 _ _ _)). split; [exact HW|].
    rewrite cells_size_map_C8, LW. cbn [cells_size csize] in H4. rewrite Nat.add_0_r in H4. exact H4.
  Qed.

  Lemma tp_merge_all : forall m1 A cs, rw_cells usegs m1 A cs -> rw_cells usegs m1 A [CB (cells_size cs) (cells_bytes cs)].
  Proof.
    intros m1 A cs H. pose proof (rw_cells_merge usegs m1 A [] cs []) as M. rewrite app_nil_r in M. exact (M H).
  Qed.

  Lemma x2_hdr_bytes : forall a b, 1 <= a <= 12 -> 1 <= b <= 12 ->
    cells_bytes [C4 (Z_to_bv 64 (Z.lor (Z.lor (Z.lor (b * 65536) (a * 16777216)) a) 256))]
    = [Z_to_bv 8 a; Z_to_bv 8 1; Z_to_bv 8 b; Z_to_bv 8 a].
  Proof.
    intros a b HA HB.
    assert (a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12) as C by lia.
    assert (b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12) as D by lia.
    cbn [cells_bytes cbytes app]. unfold le4. rewrite unsigned_lit by (split; [apply Z.lor_nonneg; split; [apply Z.lor_nonneg; split; [apply Z.lor_nonneg|]|]|]; lia || (repeat destruct C as [C|C]; repeat destruct D as [D|D]; subst; vm_compute; reflexivity)).
    repeat destruct C as [C|C]; repeat destruct D as [D|D]; subst; cbn [Z_to_le_bytes]; rewrite app_nil_r;
      repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]); reflexivity.
  Qed.

  Lemma x2_tail : forall m1 h cells jt q0 q8 j8 ja jb T (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    1 <= mtl <= 12 -> 1 <= T <= mtl -> 1 <= hs_ret h <= 129 ->
    0 < DT -> DT + 4 * (1 + 2 ^ mtl) <= lo -> lo <= SP - 4096 -> SP <= 2 ^ 47 ->
    zlen cells = 2 ^ mtl -> length jt = (4 * length cells)%nat -> x2_table_ok (x2_cells cells) T ->
    (forall i, 0 <= i < 2 ^ T -> exists c, nth (Z.to_nat i) cells None = Some c) ->
    rw_cells usegs m1 DT [C4 (Z_to_bv 64 (mtl * 16777217))] -> u8arr usegs m1 (DT + 4) (ox2 jt cells) ->
    rw_cells usegs m1 (SP + -400) [C8 q0; C8 q8; CB 8 j8; C8 (Z_to_bv 64 (mtl * 16777216)); C8 (Z_to_bv 64 (hs_ret h));
                                   C8 (Z_to_bv 64 DT)] ->
    rw_cells usegs m1 (SP + -352) [CB 32 ja] ->
    rw_cells usegs m1 (SP + -320) [C8 (Z_to_bv 64 mtl)] ->
    rw_cells usegs m1 (SP + -312) [CB 200 jb] ->
    rw_cells usegs m1 (SP + -112) [C4 (Z_to_bv 64 (hs_nbSymbols h))] ->
    rw_cells usegs m1 (SP + -108) [C4 (Z_to_bv 64 (hs_tableLog h))] ->
    rw_cells usegs m1 (SP + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m1 lo (SP + -400) ->
    munch WALL m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 T) (Z_to_bv 64 (SP + -400)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
                            y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                       F (Z_to_bv 64 (PHUF_RDT_X2 + 2000)) fc None m1 (seg_rom usegs)).
  Proof.
    intros m1 h cells jt q0 q8 j8 ja jb T y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26
      y27 y28 y29 y30 y31 HM HT HRT HDT0 HDTL HLO HSP LC LJ TOK CS HDR ARR F0 F1 F2 F3 NSP TLP SVR STK MU WM MI.
    fixpc. unfold HUF_RDT_STACK, DTABLE_BYTES, HufHarness.DT_BYTES in MU.
    pose proof (Z.pow_pos_nonneg 2 mtl ltac:(lia) ltac:(lia)) as P2.
    cgo [0x148c4].
    rewrite Z.shiftl_mul_pow2 in HDR by lia. change (2 ^ 16) with 65536 in HDR.
    rewrite (Z.mod_small (T * 65536)) in HDR by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mz end.
    apply (rw_cells_merge usegs mz DT [] [C4 (Z_to_bv 64 (Z.lor (Z.lor (Z.lor (T * 65536) (mtl * 16777216)) mtl) 256))] [])
      in HDR.
    apply u8arr_of_rw_cells in HDR. rewrite (x2_hdr_bytes mtl T) in HDR by lia.
    pose proof (x2_dt_ok mz DT mtl T cells jt HM ltac:(lia) LC LJ TOK CS HDR ARR) as DOK.
    eapply stk_release in STK; [| exact F0 | lia]. cbn [cells_size csize Nat.add] in STK.
    replace (SP + -400 + Z.of_nat 48) with (SP + -352) in STK by lia.
    eapply stk_release in STK; [| exact F1 | lia]. cbn [cells_size csize Nat.add] in STK.
    replace (SP + -352 + Z.of_nat 32) with (SP + -320) in STK by lia.
    eapply stk_release in STK; [| exact F2 | lia]. cbn [cells_size csize Nat.add] in STK.
    replace (SP + -320 + Z.of_nat 8) with (SP + -312) in STK by lia.
    eapply stk_release in STK; [| exact F3 | lia]. cbn [cells_size csize Nat.add] in STK.
    replace (SP + -312 + Z.of_nat 200) with (SP + -112) in STK by lia.
    eapply stk_release in STK; [| exact NSP | lia]. cbn [cells_size csize Nat.add] in STK.
    replace (SP + -112 + Z.of_nat 4) with (SP + -108) in STK by lia.
    eapply stk_release in STK; [| exact TLP | lia]. cbn [cells_size csize Nat.add] in STK.
    replace (SP + -108 + Z.of_nat 4) with (SP + -104) in STK by lia.
    apply (x2_epi mz (hs_ret h)); try lia; try assumption.
    intros _. exact DOK.
  Qed.

  Lemma x2_p2t : forall m0 m1 h maxW rs0a nz rs0d sorted rv0 rv cells jdt SYj q0 q8 j8 j40 j88 j152
      (x5 x6 x9 x11 x12 x13 x15 x16 x17 x20 x21 x24 x25 x26 x27 x29 x30 : word),
    read_stats src = Ok h -> X2PATH mtl h maxW rs0a nz rs0d sorted rv0 rv cells -> 1 <= mtl <= 12 ->
    1 <= hs_ret h <= 129 ->
    let tl := hs_tableLog h in let T := (if (tl <=? 11) && (11 <? mtl) then 11 else mtl) in
    let rs0 := Zupd (0 + 1) 0 rs0d in let mB := tl + 1 - maxW in
    0 < DT -> DT mod 8 = 0 -> DT + 4 * (1 + 2 ^ mtl) <= lo -> 0 < W -> W + 8704 <= lo ->
    lo <= SP - 4096 -> SP <= 2 ^ 47 ->
    (DT + 4 * (1 + 2 ^ mtl) <= W \/ W + 8704 <= DT) ->
    rw_cells usegs m0 DT [C4 (Z_to_bv 64 (mtl * 16777217))] ->
    u8arr usegs m0 (DT + 4) jdt -> length jdt = Z.to_nat (4 * 2 ^ mtl) ->
    u32arr usegs m0 (W + 676) (map (Z_to_bv 64) rs0) ->
    u8arr usegs m0 (W + 736) (omerge SYj sorted) -> length SYj = 256%nat ->
    rw_cells usegs m0 (SP + -400) [C8 q0; C8 q8; CB 8 j8; C8 (Z_to_bv 64 (mtl * 16777216)); C8 (Z_to_bv 64 (hs_ret h));
                                   C8 (Z_to_bv 64 DT); CB 32 j40; C8 (Z_to_bv 64 mtl); CB 8 j88; C8 (Z_to_bv 64 mB);
                                   C8 (Z_to_bv 64 (tl + 1)); C8 (Z_to_bv 64 W); C8 (Z_to_bv 64 (- W - 1));
                                   C8 (Z_to_bv 64 (W + 676)); CB 152 j152] ->
    rw_cells usegs m0 (SP + -112) [C4 (Z_to_bv 64 (hs_nbSymbols h))] ->
    rw_cells usegs m0 (SP + -108) [C4 (Z_to_bv 64 tl)] ->
    rw_cells usegs m0 (SP + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m0 lo (SP + -400) ->
    munch WALL m m0 -> wmono usegs m m0 ->
    munch [(W, W + 624)] m0 m1 -> wmono usegs m0 m1 -> mem_inv usegs m1 ->
    rv_at m1 W rv (PRw (maxW + 1) mB (T - mB + 1) 1) ->
    evt usegs POST (MS (mkR (Z_to_bv 64 T) (Z_to_bv 64 (SP + -400)) gp tp x5 x6 (Z_to_bv 64 (- W - 1)) (Z_to_bv 64 maxW) x9
                            (Z_to_bv 64 ((maxW + 1) * 4294967296)) x11 x12 x13 (Z_to_bv 64 (T - mB + 1)) x15 x16 x17
                            (Z_to_bv 64 (W + 736)) (Z_to_bv 64 (DT + 4)) x20 x21 (Z_to_bv 64 DT) (Z_to_bv 64 W) x24 x25 x26 x27 (Z_to_bv 64 mB) x29 x30
                            (Z_to_bv 64 tl))
                       F (Z_to_bv 64 (PHUF_RDT_X2 + 868)) fc None m1 (seg_rom usegs)).
  Proof.
    intros m0 m1 h maxW rs0a nz rs0d sorted rv0 rv cells jdt SYj q0 q8 j8 j40 j88 j152
      x5 x6 x9 x11 x12 x13 x15 x16 x17 x20 x21 x24 x25 x26 x27 x29 x30
      HRS XP HM HRT tl T rs0 mB HDT0 HDT8 HDTL HW0 HWL HLO HSP DJ HDR ARR LJ RSA SYB LSY FR NSP TLP SVR STK MU WM
      MU1 WM1 MI1 RVA.
    subst tl T rs0 mB. set (tl := hs_tableLog h) in *. set (T := if (tl <=? 11) && (11 <? mtl) then 11 else mtl) in *.
    pose proof XP as XP0.
    unfold X2PATH in XP. cbv zeta in XP. fold tl in XP. fold T in XP.
    destruct XP as (FM & HMW & RS & SO & RV0 & RVS & FX & HTL & HT & HTM & LWS & HNS & LRK & RKR & RKW & LRS0a & RS0c &
                    LRS & LSO & HSO & LRV0 & LRV' & RV0B & RSB & RVB & RVR & TOK & LC & CS).
    fixpc. unfold HUF_RDT_STACK in MU.
    trall m0 m1 MU1 WM1.
    assert (SUBW : sub_fp [(W, W + 624)] [(SP + -4096, SP); (DT, DT + DTABLE_BYTES mtl); (W, W + 8704)]).
    { intros x HX. cbn [outside] in *. destruct HX as (_ & _ & H3 & _). split; [intro; apply H3; lia | exact I]. }
    pose proof (munch_trans _ m m0 m1 MU (munch_weaken _ _ m0 m1 SUBW MU1)) as MU2.
    pose proof (wmono_trans usegs m m0 m1 WM WM1) as WM2. clear MU WM MU1 WM1. rename MU2 into MU, WM2 into WM.
    destruct RVA as (rvw & LW & UW & EQW).
    cgo (@nil Z).
    if_cases B0; zify_cond B0; [exfalso; lia|].
    cgo [0x144c4].
    destruct ((fun HQ => tp_cb_at _ _ _ 17 4 _ HQ FR) eq_refl) as ([|a1 [|a2 [|a3 [|a4 [|]]]]] & LA & FR1); try discriminate LA.
    clear FR LA. cbn [firstn skipn app map] in FR1.
    destruct ((fun HQ => tp_cb_at _ _ _ 22 7 _ HQ FR1) eq_refl) as ([|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|]]]]]]]] & LB & FR2); try discriminate LB.
    clear FR1 LB. cbn [firstn skipn app map] in FR2.
    destruct ((fun HQ => tp_cb_at _ _ _ 30 2 _ HQ FR2) eq_refl) as ([|c1 [|c2 [|]]] & LC2 & FR3); try discriminate LC2.
    clear FR2 LC2. cbn [firstn skipn app map] in FR3.
    destruct ((fun HQ => tp_cb_at _ _ _ 33 3 _ HQ FR3) eq_refl) as ([|d1 [|d2 [|d3 [|]]]] & LD & FR4); try discriminate LD.
    clear FR3 LD. cbn [firstn skipn app map] in FR4.
    destruct (tp_split _ _ _ 6 FR4) as (P0 & FR5). clear FR4. cbn [firstn skipn cells_size csize Nat.add] in P0, FR5.
    destruct (tp_split _ _ _ 29 FR5) as (Q & P3). clear FR5. cbn [firstn skipn cells_size csize Nat.add] in Q, P3.
    apply (rw_cells_merge usegs _ _ [] [C8 d3] []) in P3. cbn [app cells_size csize Nat.add] in P3.
    replace (((maxW + 1) * 4294967296) ≫ 32) with (maxW + 1) in Q
      by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 32) with 4294967296; rewrite Z.div_mul by lia; reflexivity).
    rewrite (swrap32_small (tl + 1 - T)) in Q by lia.
    rewrite zb_lxor_ones in Q by lia.
    replace (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (- (DT + 4) - 1)) in Q
      by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
    replace (tl + 1 - maxW) with (tl + 1 - (maxW + 1) + 1) in Q by lia.
    replace (tl ≪ 1 + 1) with (2 * (tl + 1) - 1) in Q by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (Z_to_bv 64 maxW) with (Z_to_bv 64 (maxW + 1 - 1)) in Q by (f_equal; lia).
    pose proof (proj2 (rw_cells_app' usegs _ _ _ _) (conj Q P3)) as FRX. cbn [app] in FRX. clear Q P3.
    rewrite zb_lxor_ones by lia.
    replace (Z_to_bv 64 (18446744073709551615 - (W + 676))) with (Z_to_bv 64 (- (W + 676) - 1))
      by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    rewrite (Z.mod_small (tl * 2 + 1)) by lia.
    rewrite (swrap32_small (tl * 2 + 1 - T)) by lia.
    replace (Z_to_bv 64 (tl * 2 + 1 - T)) with (Z_to_bv 64 (tl + 1 - 1 + (tl + 1 - T))) by (f_equal; lia).
    replace (Z_to_bv 64 tl) with (Z_to_bv 64 (tl + 1 - 1)) by (f_equal; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
    x2mk. x2pc 1012.
    destruct (stk_split usegs mf lo (SP + -4096) (SP + -400) STK ltac:(lia)) as (STKa & STKb).
    pose proof fx_loop as FXL. unfold fx_loop_stmt in FXL.
    eapply FXL with (sp := Z_to_bv 64 (SP + -400)) (m := mf) (DT := DT) (SY := W + 736) (WK := W) (T := T) (nbb := tl + 1)
      (wEnd := maxW + 1) (lo := SP + -4096) (sorted := sorted) (js := SYj) (jt := jdt) (ncells := Z.to_nat (2 ^ mtl))
      (rs0 := Zupd (0 + 1) 0 rs0d) (rv := rv) (p80 := Z_to_bv 64 mtl)
      (PRV := PRw (maxW + 1) (tl + 1 - maxW) (T - (tl + 1 - maxW) + 1) 1)
      (f := Z.to_nat (maxW + 1)) (w := 1) (dt := repeat None (Z.to_nat (2 ^ mtl))) (m1 := mf) (r := cells).
    all: first [ exact HSO | exact LSO | exact LRV' | exact FX | exact RSA | reflexivity
               | (rewrite LJ; rewrite Z2Nat.inj_mul by lia; reflexivity)
               | (rewrite Zupd_length; exact LRS)
               | (rewrite ?unsigned_lit by lia; rewrite ?Z2Nat.id by lia; Z.div_mod_to_equations; lia)
               | (rewrite Z2Nat.id by lia; change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia)
               | (intros w0 Hw0; apply RSB; lia)
               | (intros w0 Hw0; unfold PRw; left; lia)
               | (intros c0 w0 Hc Hw0; unfold PRw; right; exists c0, w0; split; [lia|]; split; [left; split; lia | reflexivity])
               | (intros w0 Hw0; exact (RVB w0 ltac:(lia)))
               | (intros c0 w0 Hc Hw0; apply RVR; lia)
               | idtac ].
    { exists rvw. exact (conj LW (conj UW EQW)). }
    { unfold x2A_inv. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (munch_refl _ mf) (conj (wmono_refl usegs mf) _))))))).
      - rewrite ox2_none. exact ARR.
      - apply repeat_length.
      - exact (proj1 SYB).
      - exists a1, a2, a3, a4, b1, b2, b3, b4, b5, b6, b7, c1, c2, d1, d2, (cells_bytes [C8 d3]).
        rewrite unsigned_lit by lia. exact FRX.
      - rewrite unsigned_lit by lia. exact STKb.
      - assumption. }
    intros m2 dt' y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
      HR AI. subst dt'.
    destruct AI as (ARR2 & LDT2 & SYB2 & (z136 & z144 & z152 & z160 & z176 & z184 & z192 & z200 & z208 & z216 & z224 & z240 &
                    z248 & z264 & z272 & jz & FR2) & STK2 & MU2 & WM2 & MI2).
    rewrite unsigned_lit in FR2, STK2, MU2 by lia.
    unfold x2_frame in FR2.
    destruct (tp_split _ _ _ 4 FR2) as (G1 & FR3). clear FR2. cbn [firstn skipn cells_size csize Nat.add] in G1, FR3.
    destruct (tp_split _ _ _ 1 FR3) as (G2 & G3). clear FR3. cbn [firstn skipn cells_size csize Nat.add] in G2, G3.
    apply tp_merge_all in G1. apply tp_merge_all in G3. cbn [cells_size csize Nat.add] in G1, G3.
    clear FRX.
    trall mf m2 MU2 WM2.
    pose proof (stk_merge usegs m2 lo (SP + -4096) (SP + -400) STKa STK2 ltac:(lia)) as STK3.
    assert (SUB : sub_fp [(DT + 4, DT + 4 + 4 * Z.of_nat (Z.to_nat (2 ^ mtl))); (SP + -4096, SP + -400);
                          (SP + -400 + 136, SP + -400 + 288)]
                         [(SP + -4096, SP); (DT, DT + DTABLE_BYTES mtl); (W, W + 8704)]).
    { unfold DTABLE_BYTES, HufHarness.DT_BYTES. rewrite Z2Nat.id by lia.
      intros x HX. cbn [outside] in *. destruct HX as (H1 & H2 & H3 & _).
      split; [intro; apply H1; lia | split; [intro; apply H2; lia | split; [intro; apply H3; lia | exact I]]]. }
    pose proof (munch_trans _ m mf m2 MU (munch_weaken _ _ mf m2 SUB MU2)) as MU3.
    pose proof (wmono_trans usegs m mf m2 WM WM2) as WM3.
    replace (SP + -400 + 48) with (SP + -352) in G1 by lia.
    lazymatch type of G2 with rw_cells _ _ ?a _ => replace a with (SP + -320) in G2 by lia end.
    lazymatch type of G3 with rw_cells _ _ ?a _ => replace a with (SP + -312) in G3 by lia end.
    replace (SP + -400 + Z.of_nat 0) with (SP + -400) in P0 by lia.
    eapply (x2_tail m2 h cells jdt q0 q8 j8); try eassumption; try lia.
  Qed.

  Lemma x2_p2 : forall m1 h maxW rs0a nz rs0d sorted rv0 rv cells jdt SYj RVj j8 j40 j16a j16b j152
      (q0 q8 x5 x6 x7 x9 x12 x14 x15 x16 x17 x20 x21 x24 x25 x26 x27 x28 x29 x30 : word),
    read_stats src = Ok h -> X2PATH mtl h maxW rs0a nz rs0d sorted rv0 rv cells -> 1 <= mtl <= 12 ->
    1 <= hs_ret h <= 129 ->
    let tl := hs_tableLog h in let T := (if (tl <=? 11) && (11 <? mtl) then 11 else mtl) in
    0 < DT -> DT mod 8 = 0 -> DT + 4 * (1 + 2 ^ mtl) <= lo -> 0 < W -> W + 8704 <= lo ->
    lo <= SP - 4096 -> SP <= 2 ^ 47 ->
    (DT + 4 * (1 + 2 ^ mtl) <= W \/ W + 8704 <= DT) ->
    rw_cells usegs m1 DT [C4 (Z_to_bv 64 (mtl * 16777217))] ->
    u8arr usegs m1 (DT + 4) jdt -> length jdt = Z.to_nat (4 * 2 ^ mtl) ->
    u32arr usegs m1 (W + 676) (map (Z_to_bv 64) rs0d) ->
    u32arr usegs m1 (W + 624) (map (Z_to_bv 64) (hs_rank h)) ->
    u8arr usegs m1 W RVj -> length RVj = 624%nat ->
    u8arr usegs m1 (W + 736) (omerge SYj sorted) -> length SYj = 256%nat ->
    rw_cells usegs m1 (SP + -400) [C8 q0; C8 q8; CB 8 j8; C8 (Z_to_bv 64 (mtl * 16777216)); C8 (Z_to_bv 64 (hs_ret h));
                                   CB 40 j40; C8 (Z_to_bv 64 mtl); CB 16 j16a; C8 (Z_to_bv 64 (tl + 1)); CB 16 j16b;
                                   C8 (Z_to_bv 64 (W + 676)); CB 152 j152] ->
    rw_cells usegs m1 (SP + -112) [C4 (Z_to_bv 64 (hs_nbSymbols h))] ->
    rw_cells usegs m1 (SP + -108) [C4 (Z_to_bv 64 tl)] ->
    rw_cells usegs m1 (SP + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m1 lo (SP + -400) ->
    munch WALL m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 T) (Z_to_bv 64 (SP + -400)) gp tp x5 x6 x7 (Z_to_bv 64 maxW) x9
                            (Z_to_bv 64 ((maxW + 1) * 4294967296)) (Z_to_bv 64 (tl - maxW)) x12 (Z_to_bv 64 (W + 680))
                            x14 x15 x16 x17 (Z_to_bv 64 (W + 736)) (Z_to_bv 64 (DT + 4)) x20 x21 (Z_to_bv 64 DT) (Z_to_bv 64 W) x24 x25 x26 x27
                            x28 x29 x30 (Z_to_bv 64 tl))
                       F (Z_to_bv 64 (PHUF_RDT_X2 + 584)) fc None m1 (seg_rom usegs)).
  Proof.
    intros m1 h maxW rs0a nz rs0d sorted rv0 rv cells jdt SYj RVj j8 j40 j16a j16b j152
      q0 q8 x5 x6 x7 x9 x12 x14 x15 x16 x17 x20 x21 x24 x25 x26 x27 x28 x29 x30
      HRS XP HM HRT tl T HDT0 HDT8 HDTL HW0 HWL HLO HSP DJ HDR ARR LJ RSA RKA RVA LRV SYB LSY FR NSP TLP SVR STK MU WM MI.
    subst tl T. set (tl := hs_tableLog h) in *. set (T := if (tl <=? 11) && (11 <? mtl) then 11 else mtl) in *.
    pose proof XP as XP0.
    unfold X2PATH in XP. cbv zeta in XP. fold tl in XP. fold T in XP.
    destruct XP as (FM & HMW & RS & SO & RV0 & RVS & FX & HTL & HT & HTM & LWS & HNS & LRK & RKR & RKW & LRS0a & RS0c &
                    LRS & LSO & HSO & LRV0 & LRV' & RV0B & RSB & RVB & RVR & TOK & LC & CS).
    fixpc. unfold HUF_RDT_STACK in MU.
    pose proof (u32arr_store_ok usegs m1 (W + 676) _ 1 (wa (W + 676 + 4 * 1)) RSA ltac:(rewrite length_map, LRS; lia) eq_refl)
      as SOK.
    cgo [0x14320]. zstep.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (W + 676 + 4 * 1) by lia
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (W + 676 + 4 * 1) by lia
    end.
    pose proof (u32arr_write usegs _ (W + 676) _ 1 (Z_to_bv 64 0) RSA ltac:(rewrite length_map, LRS; lia)) as RS2.
    clear RSA. store_done. rename RS2 into RSA.
    cgo [0x14350].
    if_cases B0; zify_cond B0; [exfalso; lia|].
    cgo [0x14350].
    rewrite zb_lxor_ones by lia.
    replace (Z_to_bv 64 (18446744073709551615 - W)) with (Z_to_bv 64 (- W - 1))
      by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
    rewrite !swrap32_small by lia.
    replace (Z_to_bv 64 (T - tl)) with (Z_to_bv 64 (1 + (T - tl - 1))) by (f_equal; lia).
    replace (Z_to_bv 64 (W + 628)) with (Z_to_bv 64 (W + 624 + 4 * 1)) by (f_equal; lia).
    replace (((maxW + 1) * 4294967296) ≫ 30) with (4 * (maxW + 1))
      by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 30) with 1073741824; Z.div_mod_to_equations; lia).
    replace (Z_to_bv 64 4) with (Z_to_bv 64 (4 * 1)) by reflexivity.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
    destruct (u32arr_of_u8arr usegs mc W RVj 156 RVA ltac:(rewrite LRV; reflexivity)) as (rvw & LW & _ & UW).
    eapply rv0_loop with (m := mc) (WK := W) (wEnd := maxW + 1) (rsc := T - tl - 1) (rank := hs_rank h)
      (f := Z.to_nat maxW) (w := 1) (next := 0) (rv := repeat 0 (12 * 13)) (m1 := mc) (r := rv0).
    all: try exact RV0.
    all: try lia.
    all: first [ exact RKR | exact RKA | idtac ].
    { refine (conj _ (conj _ (conj (munch_refl _ mc) (conj (wmono_refl usegs mc) MI)))).
      - exists rvw. refine (conj LW (conj UW _)). intros i Hi. lia.
      - rewrite repeat_length. reflexivity. }
    intros m2 rv' y5 y11 y12 y15 y17 HR (RV2 & LV2 & MU2 & WM2 & MI2). subst rv'.
    assert (SUBW : sub_fp [(W, W + 624)] [(SP + -4096, SP); (DT, DT + DTABLE_BYTES mtl); (W, W + 8704)]).
    { intros x HX. cbn [outside] in *. destruct HX as (_ & _ & H3 & _). split; [intro; apply H3; lia | exact I]. }
    pose proof (munch_trans _ m mc m2 MU (munch_weaken _ _ mc m2 SUBW MU2)) as MU3.
    pose proof (wmono_trans usegs m mc m2 WM WM2) as WM3.
    clear MU WM. rename MU3 into MU, WM3 into WM.
    trall mc m2 MU2 WM2.
    clear MU2.
    destruct RV2 as (rvw2 & LW2 & UW2 & EQ2).
    cgo [0x14390; 0x14434].
    rewrite zb_lxor_ones in FR by lia.
    replace (Z_to_bv 64 (18446744073709551615 - W)) with (Z_to_bv 64 (- W - 1)) in FR
      by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
    replace (tl - maxW + 1) with (tl + 1 - maxW) in * by lia.
    replace (Z_to_bv 64 (T - (tl - maxW))) with (Z_to_bv 64 (T - (tl + 1 - maxW) + 1)) by (f_equal; lia).
    if_cases B1; zify_cond B1.
    - rewrite Z.max_l in RVS by lia. cbn in RVS. injection RVS as <-.
      cgo [0x14434].
      eapply x2_p2t with (m0 := m0) (m1 := m0) (h := h) (maxW := maxW) (rs0a := rs0a) (nz := nz) (rs0d := rs0d)
        (sorted := sorted) (rv0 := rv0) (rv := rv0) (cells := cells) (jdt := jdt) (SYj := SYj) (q0 := q0) (q8 := q8)
        (j8 := j8) (j40 := skipn 8 j40) (j88 := firstn 8 j16a) (j152 := j152).
      all: first [ exact HRS | exact XP0 | exact HDR | exact ARR | exact LJ | exact SYB | exact LSY | exact FR | exact NSP
                 | exact TLP | exact SVR | exact STK | exact MU | exact WM | lia | exact (munch_refl _ _) | exact (wmono_refl usegs _)
                 | (unfold Zupd; change (Z.to_nat (0 + 1)) with 1%nat; rewrite map_upd_nat; exact RSA) | idtac ].
      all: try assumption.
      exists rvw2. refine (conj LW2 (conj UW2 _)). intros j Hj Hb. apply EQ2; [|exact Hb].
      unfold PRw in Hj. subst tl T.
      destruct Hj as [Hj | (c' & w' & H1 & [(H2 & H3) | (H2 & H3)] & H4)]; lia.
    - cgo [0x14390].
      rewrite (Z.mod_small (tl + 1 - maxW)) by lia.
      replace (Z_to_bv 64 maxW) with (Z_to_bv 64 (maxW + 1 - 1)) by (f_equal; lia).
      rewrite Z.max_r in RVS by lia.
      eapply rvr_outer with (m := m0) (WK := W) (wEnd := maxW + 1) (mB := tl + 1 - maxW) (T := T)
        (f := Z.to_nat (T - (tl + 1 - maxW) + 1 - (tl + 1 - maxW))) (c := tl + 1 - maxW) (rv := rv0) (m1 := m0) (r := rv).
      all: try (replace (maxW + 1 - 1) with maxW by lia; exact RVS).
      all: try lia.
      { refine (conj _ (conj LRV0 (conj RV0B (conj (munch_refl _ m0) (conj (wmono_refl usegs m0) _))))); [|assumption].
        exists rvw2. refine (conj LW2 (conj UW2 _)). intros j Hj Hb. apply EQ2; [|exact Hb].
        unfold PRw in Hj. destruct Hj as [Hj | (c' & w' & H1 & [(H2 & H3) | (H2 & H3)] & H4)]; lia. }
      intros m3 rv' z5 z6 z15 z16 z17 HR (RV3 & LV3 & VB3 & MU3 & WM3 & MI3). subst rv'.
      replace (Z_to_bv 64 (maxW + 1 - 1)) with (Z_to_bv 64 maxW) by (f_equal; lia).
      eapply x2_p2t with (m0 := m0) (m1 := m3) (h := h) (maxW := maxW) (rs0a := rs0a) (nz := nz) (rs0d := rs0d)
        (sorted := sorted) (rv0 := rv0) (rv := rv) (cells := cells) (jdt := jdt) (SYj := SYj) (q0 := q0) (q8 := q8)
        (j8 := j8) (j40 := skipn 8 j40) (j88 := firstn 8 j16a) (j152 := j152).
      all: first [ exact HRS | exact XP0 | exact HDR | exact ARR | exact LJ | exact SYB | exact LSY | exact FR | exact NSP
                 | exact TLP | exact SVR | exact STK | exact MU | exact WM | lia | exact (munch_refl _ _) | exact (wmono_refl usegs _)
                 | (unfold Zupd; change (Z.to_nat (0 + 1)) with 1%nat; rewrite map_upd_nat; exact RSA) | idtac ].
      all: try assumption.
  Qed.

End TOP.
End CANSEC.
(* [comment removed for export] *)
(* [comment removed for export] *)

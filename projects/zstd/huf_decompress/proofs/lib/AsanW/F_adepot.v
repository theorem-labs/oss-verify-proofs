(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg ABase AKit ShadowTac ADepot_iface ADepot ADepotKit F_adepot1.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_adepot () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z9mul_assocC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C46Stdlib6ZArith4ZdivAZmult_mod_distr_rC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib5AsanW6ADepot3bktC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00c59OSSVerify5KrLib5AsanW8F_adepot:bkt_offsetC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesI45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv3Sem7amo_valC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3MemDle_bytes_to_word_le4C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCbv_extract_unsignedC45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions?bv_add_unsignedC35stdpp7tactics<f_equal_helpK46Stdlib9micromega5Tauto8GFormula03K4ELinuxProcessSemantics5Riscv5Instr5amoop02K47Corelib7Numbers7BinNums1N01I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5AsanW6ADepot2dNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot3dtfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot6dcellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot7dlayoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot;munch_pointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot4dinsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib5AsanW6ADepot3dhdC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init5Logic2or01C59OSSVerify5KrLib5AsanW6ADepot>rw_cells_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot3dhsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot3dlkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot4dsidC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib3Lib5Frame9stk_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot9stk_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame?stk_of_rw_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib5Frame9stk_mergeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot5NUNIQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot4SSTFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot4SSSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot5SSPTRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot4MAP1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I59OSSVerify5KrLib5AsanW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW6ADepot6dstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot3TABC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC59OSSVerify5KrLib4LibA5ExecF8rng_sub'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib5AsanW5ABase4al_UC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot3dwfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot7ADEPOTiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<ADepot_iface>depot_put_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot5lk_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib5AsanW6ADepot3BUDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot:CNT_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot3CNTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot:BUD_nonnegC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW4AKit5boxed01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW4AKit5boxed00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot=mz_init_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot7mz_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot7mz_addsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot=mz_adds_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot<mz_fin_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot6mz_finC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot5hashUC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF6acc_inC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K4ELinuxProcessSemantics5Riscv5Instr5instr02C59OSSVerify5KrLib3Lib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib3Lib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics5Riscv3Sem4core01C56Stdlib6ZArith6BinInt1Z9add_assocC59OSSVerify5KrLib4LibA5StepF=rng_acc_litZ'C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFast=munch_write_nC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC45stdpp9bitvector;definitions8bv_swrapK4ELinuxProcessSemantics5Riscv5Instr5instr0;C59OSSVerify5KrLib3Lib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C59OSSVerify5KrLib3Lib8PropExec7w_addiwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MStateAunsigned_lit_wrapC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions>bv_swrap_smallC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib3Lib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image>ro_cells_imageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP9bv_lit_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5v_andC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_andC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0BC59OSSVerify5KrLib3Lib8PropExec5v_mulC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC59OSSVerify5KrLib3Lib8PropExec5m_mulC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C59OSSVerify5KrLib3Lib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5v_xorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_xorC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorC59OSSVerify5KrLib3Lib8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z8max_specC47Corelib5Lists7ListDef3mapC56Stdlib6ZArith6BinInt1Z7sub_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr01C59OSSVerify5KrLib3Lib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5b_luiC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C59OSSVerify5KrLib3Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0>C47Corelib4Init5Logic5proj1I47Corelib4Init5Peano2le00C59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib5AsanW6ADepot<adepot_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot5chainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepotAdwf_absent_budgetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3TacArw_cells_split_CBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac;mk_CB_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC59OSSVerify5KrLib3Lib3Tac7sum_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5StepF=stk_lo_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_adepot19lock_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_adepot19lock_bodyC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr@u64arr_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0FC4ELinuxProcessSemantics5Riscv3Sem5is_x0C4ELinuxProcessSemantics5Riscv3Sem7reg_getC4ELinuxProcessSemantics5Riscv3Sem;amo_alignedC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv3Sem3eff06K4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff08K4ELinuxProcessSemantics5Riscv3Sem3eff07C59OSSVerify5KrLib3Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib3Lib7ZBridge=bv_lts_zero_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6leb_gtC59OSSVerify5KrLib5AsanW9ADepotKit<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ADepotKit@rw_cells_C8_C4C4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_adepot1;nstore_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_adepot1;nstore_bodyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C59OSSVerify5KrLib3Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ADepot:dwf_insertC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8F_adepot:dcells_insC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib6ExElim:ex_elim_16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8evtF_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge:zb_shl_shrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4AKit8sx32_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8F_adepotAamo_add_w_le4_genC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula02C59OSSVerify5KrLib5AsanW9F_adepot19find_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge:zr_mod_anyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge9zr_shiftrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge7zr_lxorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_adepot19hash_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC59OSSVerify5KrLib4LibA5StepF<lift_resultFC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib4LibA5StepF9stepF_genC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib3Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFast@rw_cells_frame_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFast>u64arr_frame_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFast;stk_write_nC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu32C59OSSVerify5KrLib3Lib8PropExec8alu_srliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib3Lib4Step@ro_cells_read_atC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C56Stdlib6ZArith6BinInt1Z3maxC59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF=evtF_step_accC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula0:C56Stdlib6ZArith4Znat5Nat2Z8inj_succK4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5aluop07C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5msize03C4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto4kind02K4ELinuxProcessSemantics5Riscv5Instr6awidth01I4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums8positive00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c59OSSVerify5KrLib5AsanW8F_adepot8put_bodyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<ADepot_iface>depot_put_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase3ATPC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma bkt_offset : forall h, (0 <= h)%Z ->
  Z.shiftr ((Z.shiftl h 44) mod 18446744073709551616) 42 = (4 * bkt h)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adepot ()) ["CANSEC1"] "h07__arithh14__ffh28__varmaph35__with41zh52Hah64__x1h74__x2h84__x3h94__x4h:4__x5h;1Hh<2H0h=2H1h>3H10h?2H2h@2H3hA2H4hB2H5hC2H6hD2H7hE2H8hF2H9hG2HhhH6__sat0hI6__sat1hJ6__sat2hK6__sat3hL1hp&0p;1p;2p;3p;4p;6p;7p;8p10000p4p7210g000\R0p4p710p8g001:j10Tg001_j1<Tg002=j1DTg002bj2OTg003?j22Tg003\j21Tg004<j2FTg004\j27Tg0059j3aTg005jk200Tg006Rj26Tg006nj3yTg007Rj2\Tg0083j1[Tg008Lj2HTg008ij2XTg009Pj2?Tg009kj2YTg00:Rj2MTg00:nj2^Tg00;Tj2_Tg00<:j2UTg00=6j2TTg00=_j1hTg00>=j2gTg00>^j19Tg00?=j3ETg00?fj2fTg00@Oj3eTg00A8j2STg00Adj2ITg00BPj1dTg00C0j3bTg00CPk101Tg00D0j2`Tg00DNj1~Tg00Dlj4PTg00EJj1}Tg00Ehj1{Tg00FSj2>Tg00G6j1xTg00GXj2CTg00H;j3GTg00H^j3ZTg00IAj1VTg00I_j3WTg00JBj2vTg00Jdj2uTg00K>j2tTg00Kjj3LTg00LDj3qTg00Lcj4pTg00MUj3oTP0j6BTg00N6j3nTg00NYj3mTg00OBj3rTg00Oij2sTg00PIj3lTg00Q2j1wTg00Qgj3]Tg00RPj4QTg00S;j7jTg00S_j7zTg00TCj8iTg00Tgj6|Tg00UKR0f0R1'Mp=5%01#0p=c%01#0#0#0#0#0#0#0p=:%01#0#0#0p=kg00UiR2f1R3;L1p=4AL210p=A1T21p=;f2R4A]2315]2p=@P2P3g00VGP1CQp=JP3g00VnR5g00WMR6P6g00WmR7P1g00XMFjp=3P2P3g00XmP1CQp=KP4P5P6P6P7P3P1Fzp=Rf3R8P5P6P6P7P4P3P1Gip=8P2P3g00YTP1CQp==P3P5P6P6P7P1E|p=N%51P2g00Z;R5#0R9#<R:%D9R;#D#c#<R<'OR=,23R>%09R?#c#:#:R@#k#:#:#:#:#:#<RA,11%0;RB#D#0RC#<RD'F%<?RE%<@R@,14'2RF'4X42P2%0BRB#<RG,O:RH,13RI/2=RJ1F1D/4FX42P21O:DRK,7J141FX42RLP212IERM/2KRN171K/4FX42P2PMPLAa3H1%5HRL114H#5[200:G160:%5G160HRF[[%5:ROg00Z`RPAy:G3UW5PL\P^5Of4RO?a@8%5@f5RP/1@#5[1\PH%AHRL#[f6RG17GH,2H11GH'H'4[1XGHf7RQ/1HRR#516RH'?\F1YQH16H0f8RR/1HRS,6H1MS0'?[1^RHf9RR/7H#A\L1_RHf:RR/1H/4R\Lg00[<RS1URHRRePRf;RR/\@%A@RT#[f<RU17U@,2@11U@'H'4[1XU@160@RVf=RW/1@RX#516X@'?[1YW@16@0f>RW/1@RX,6@1MX0'?[1^W@f?RW/7@#A\T1_W@f@RW/1@/4W\TPS1UW@RWePWg00[XRWg00\DRS,T2RX%h5,g2RY%9S#9RS#9RZ#9R[#9R\#;R]5E2%;SRS5@X1f2@=e2XR^%9\R\#9R_#;%;\R\%;ZRZ9E2Y7@]3@g00\cR`'S'I'IAE2YS9@X]%9_#;AE2Y\%;[;@Z5@^/S`'I,IX%dWRX5bW3b&01WRWP2P21`2OP4%~2R`CPP3P21`2PP8P`CPCP%}2R^%{2RZPZ1>20R[1>2@R\'J,3Z%x6R61C29R9,K[,3Z1J9\,3Z5RZC8P6PZPZ1=\[,3Z,NZP6%D5,C2RY1C2;9G2\=Z29'=,3ZC8P6PZPZ1>2:R:%VB5W2RB,J[,3ZP61C25R5,K[,3Z1J5B,3Z5RZC8P6PZPZ1=B[,3Z,NZP61C2?9G2B=Z25,=Y,3ZC8P61>2ER69G25AG269'=,3ZC8C8C8C81vZ7R7P1P4g00]OR6g00]oR9'u1t14=L69dAq203CpR0b1b2b3X62X72X82X92X:2%54164@'?\Vg00^ORV\T12@G/H8,4O[%58168H'?\FPV\L12HQ/HO,4G[12OE12EP'4[[[[^62^72^82^92^:2P1fBRO/7@17OHPO11O@11OHPPPGPRPUO9b0fARU/1H/2E11U@,2E'4eb>bFbEbDbCbBbAb@b?b=b<b;bHbIbJbK17NKPXPWP`P^%VC9W2:/=[,3Z,NZP7P0b1b2b3%AKPV[P1b09oMKEB12EK,2IAnIEKEB1FJDPXPWP`P^1>2D,K[,3ZP7P0b1b2b3%5DP1b09mJDEB12H=,1>Ar3H=EB1s3<RHPXPWP`P^1>2<,K[,3ZP7P0b1b2b3%5<P1b09l3<EB11HA/FD%w3,2E'4eWGXL2o"). Qed.
Lemma bkt_offset_land : forall h, (0 <= h)%Z ->
  Z.shiftr (Z.land (Z.shiftl h 44) 18446744073709551615) 42 = (4 * bkt h)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adepot ()) ["CANSEC1"] "h02Hhh17__arithh24__ffh38__varmaph45__with51hh61zp;2p;1p;3p;4p;7p;6g00:Rj25Tg001:j10Tg002=j12Tg001_j11Tg00Oij2LTg002bj2@Tg003\j2<Tg004<j2;Tg00Q2j18Tg003?j27Tg00Kjj33Tg00^lj26Tg00_jj19Tg00`Hj2KTg00BPj1JTg00CPj1ITg00DNj1?Tg00EJj1=Tg00Ehj1>Tg00FSj24Tg00RPj4ATg00S;j7BTg00JBj2:Tg00Jdj2CTg00K>j2DTg00LDj3ETg00Lcj4FTg00`fj3GTg000\j6HTg00UiR0g00UKR1f0R2'5P0f1R3g00Z;#0R4#2R5#2#0#0#1'LR6%14%04R4#0#0#0#0#1R7'@'<%05#2#0#1,;2%14f2R4#8'7530X601632%97,K6g00[XR5#J%I5%?0%=0%>0R5g00Vng00WMR8P8g00WmR8P01401g00Xm1407CAg00XMFB1:58P2P4g00]OR8g00]oR5'C1D24=385dAE013CFb2b3b41517P2b19G67EHW0W5o"). Qed.

(* [comment removed for export] *)
Lemma amo_add_w_le4_gen : forall tf (c : bv 32), (0 <= tf)%Z -> (tf + bv_unsigned c < 2^32)%Z ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) c))
  = le4 (Z_to_bv 64 (tf + bv_unsigned c)).
Proof.
ltac2:(KReplay.run1 (kr_t_F_adepot ()) ["CANSEC1"] "h04__p1h14__x1h24__x2h31zh47__arithh54__ffh68__varmaph75__with82Hah92E1h:1Hh;2H0h<2H1h=2H2h>2H3h?2H4h@2H5hA2H6hB2HChC6__sat3hD6__sat4hE6__sat5hF1chG2tfp&0p;1p;2p;4p;3p;8p;7p;6g001:j1<Tg00IAj1MTg00aIj1STg00alj21Tg008Lj27Tg001_j1HTg002bj2VTg006Rj28Tg00bVj2eTg00cIj1dTg00CPj1NTg00>^j1CTg00d2j2LTg00dXj1KTg00eHj1[Tg00fHj4ZTg00g1j4YTg00g[j2Jj1qTg00Kjj3;Tg00Jdj2ATg00hXj29Tg00i>j1iTg004<j2@Tg003\j23Tg00=6j2BTg00Qgj3DTg00A8j2QTg00BPj1cTg00C0j3PTg00D0j2OTg00DNj1bTg00Dlj4aTg00EJj1`Tg00Ehj1_Tg00FSj2TTg00GXj2UTg00G6k103Tg00H^k302Tg00I_j3]Tg00JBk201Tg00K>k200Tg00LDj3~Tg00Lcj4}Tg009Pj2ITg00i\j3GTg005jj2{Tg006nj3yTg0059j3xTg007Rj2wTg0083j1sTg004\j2WTg003?j2rTg008ij2pTg009kj2oTg00:Rj2\Tg00:nj2nTg00;Tj2mTg00<:j2lTg00j?j1kTg00jcj2XTg00k_j1tTg00l`j4jTg00mRj3uTg00n7j3vTg00nej8hTg00RPj4RTg00S;j7zTg00oBj6gTg00S_j7|Tg00TCj8FTg000\j6fTg00UKR0f0R1'\p=2f2R2f1R3/81'Ip=6g00UiR4?;31p=0P4P3g00XmP1CRp=EP3g00VnR5g00WMR6P6g00WmR7P1g00XMFzp=5P3P5P6P6P7P1Egp=^P2P5P6P6P7P3P1F|p==P4P3g00VGP1CRp=>f3R8P5P6P6P7P2P3P1GFp=:f6R9P5P6P6P7f5R:f4R;P8P5P6P6P7P2P3P1GFGFp=?P4P;P8P2P3P1Efp=4g00Z;R5#<R<#<#<R=#<#<R>#MR?#S%23R@11?3,72%H<RA%H>RB'VRC'81e?211?2RD#2%d?76D11?8RD,7;RE%M=#S#NR=g00\DRF#CRG#CRH#CRI#CRJP?g00ofRK%<>R>#MRLg010RRMP?1LL:#K#[CZRNP;CY,1?'J1JJ13;X34P4P=%qJROPOP?PKPLPMP?1LL;RK#K#[RPCZRQP8CY,1?RRPEP=\4/AO11?QRO/7D,9?11?;RD,7:RS,01X3411LPRT%iMRU'@,9?101:X34RV11LKRW/3C1@1U,9?/0:X34P;131C/@U,9?/0:X3413;CRU19?1/0:X34PUPVP;PV1A4;PUp-0RVg00[XRX1B4IRI1B4H1B4FRF5D45D4g00\cRH'Q%cXRY3PRZ%NXR[P41O42P3%b4CaR\%`4R]%_4R^1T40R_1U4<R<'E,5^1^^;5=^R`&036R6P^1U45R5>024<R<1T4ARa=]4?Rb'>,5^RcP6P^1E_5,5^RdP61>5b,5^Re9=^dRfC:F?201^7R7P1P2g00]ORgg00]oRh'A20012=;ghdA~403C}Rhb5b6b7X14X24W01I@2R@1732/8CRg%22Ri%28Rj?68C[[[^14^24^0VP118DCPDP:P3P2P8O6RDb49G;CD413UC1{AB180A%2B180CRk[[%2ARlg00Z`RmAyAB3UW8%2CRB\m^8lAx9C;f7Rl/3C#2\B1wlCA;4C0Rm#sf8Rn1WnC,rC13nC'7'0[1pnCf9Rn/3CRo#2?6oC\k1onC18C0f:Rn/3CRo,8C1\o0'I[1nnCf;Rn/WC=;40\m1mnCf<Rn/3C/0n\mg00[<1lnCRnePnPYP[1O43P]P^P^1>_b,5^P61^^8==^eC:P6P^P^1E_b,5^P6PdC:P6PfF?P7Phb5b6b7X14X0VA623C\kPi\BA6i2C[[^14^0VP1f>/3CRB#2PBP:PlO4b4f=/3CRl#2?6lCebAb@b?b>b<b:bCbDbE9GUCD419?U/0;e1@U0%kUD4PWPZP[P\P]P^P`P6P^PcP6P^PdP6A]4aLRa,>5,5^9=^dC:F?P7Phb5b6b7X14X24X0V%H>,VARA96j8\i\g\@^14^24^0VPDb4,X;D4PT%tKD4POPLPMP?PPCjD410O;P:11?:R:,71,9?179:RO'0X34PS101OX341A4S13SC1B4G=D4F9D4I/QH=PXYRYP[P\P]P^P`P6P^PcP6P^PdP61E_<,5^R_==^cC:F?P7Phb5b6b7X14X24X0V178;RX#2RH?6XC\i\g\@^14^24^0VP118:CP:P9P2P8P;O6b49GSCD419?S/0Se11?NP1D4b9Au?Q8,1?Av?Q8D410REeGh1LLERQ,1LPYP[P\P]P^P`P6P^PcP6P^PdP61><a,5^9=^_C:F?P7Phb5b6b7X14X24X0VA6HXA\i\g\@^14^24^0VPDb4,XED41JJR%KQ5;=ebBW=W;WFXG4o"). Qed.

End CANSEC1.
Ltac amo_stepW4c :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i;
        erewrite amo_add_w_le4_gen;
        [ match goal with |- context [le4 (Z_to_bv 64 (_ + bv_unsigned ?c))] =>
            let v := eval vm_compute in (bv_unsigned c) in change (bv_unsigned c) with v end;
          mem_after_store_opt
        | lia
        | match goal with |- context [bv_unsigned ?c] =>
            let v := eval vm_compute in (bv_unsigned c) in change (bv_unsigned c) with v end; lia ] ]
    end end
  end.

(* [comment removed for export] *)
Notation WFINE sp BA NDp FA sz :=
  ([(sp + -1024, sp); (BA, BA + 4); (5871704, 5871704 + 4); (NDp, NDp + 16);
    (1611848, 1611848 + 8); (1611872, 1611872 + 4); (FA, FA + 8 * (sz + 1))]%Z) (only parsing).

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma dcells_ins : forall L D m m' (sp h v sid : Z) (u : list Z) csF,
  let N := dN D in let tf := dtf D in let b0 := bkt h in
  let BA := (TAB + 4 * b0)%Z in let NDp := (al_nodes L + 16 * (N + 1))%Z in let FA := (al_store L + 8 * tf)%Z in
  let sz := Z.of_nat (length u) in
  dcells L D m -> dlayout L -> (ATOP <= sp - 1024)%Z -> (sp <= 2^64)%Z -> (0 <= h)%Z ->
  (1 <= N)%Z -> (16 * (N + 2) <= 1048576)%Z -> (0 <= tf)%Z -> (8 * (tf + sz + 1) <= 8388608)%Z ->
  munch (WFINE sp BA NDp FA sz) m m' -> wmono asegs m m' ->
  rw_cells asegs m' BA [C4 (Z_to_bv 64 (N + 1))] ->
  rw_cells asegs m' NUNIQ [C4 (Z_to_bv 64 (N + 1))] ->
  rw_cells asegs m' NDp [C8 (Z_to_bv 64 h); C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 sid)] ->
  rw_cells asegs m' SSTF [C8 (Z_to_bv 64 (tf + sz + 1))] ->
  rw_cells asegs m' SSST [C4 (Z_to_bv 64 (tf + sz + 1))] ->
  rw_cells asegs m' SSPTR [C8 (Z_to_bv 64 (al_store L))] ->
  rw_cells asegs m' MAP1 [C8 (Z_to_bv 64 (al_nodes L))] ->
  rw_cells asegs m' FA csF -> Z.of_nat (cells_size csF) = (8 * (sz + 1))%Z ->
  dcells L (dins D b0 h v sid sz) m'.
Proof.
  intros L D m m' sp h v sid u csF N tf b0 BA NDp FA sz DC LY SPL SPH Hh N1 NR TF0 TFR MU WM CBA CNU CND CTF CST CPTR CMAP CFA SF.
 assert (HB : (0 <= b0 < 1048576)%Z) by (subst b0; unfold bkt; apply Z.mod_pos_bound; lia).
  destruct DC as (_ & _ & _ & _ & _ & CT & CN & SKN & SKS).
  pose proof LY as (_ & _ & LN0 & LN1 & LS0 & LS1 & DISJ). unfold AIMG_HI, TAB, NUNIQ, MAP1, SSTF, SSPTR, SSST in *.
  subst N tf BA NDp FA.
  assert (OUT : forall x,
    ((1677400 <= x < 1677400 + 4 * 1048576 /\ ~ (1677400 + 4 * b0 <= x < 1677400 + 4 * b0 + 4))
     \/ (al_nodes L + 16 <= x < al_nodes L + 1048576 /\ ~ (al_nodes L + 16 * (dN D + 1) <= x < al_nodes L + 16 * (dN D + 1) + 16))
     \/ (al_store L <= x < al_store L + 8388608 /\ ~ (al_store L + 8 * dtf D <= x < al_store L + 8 * dtf D + 8 * (sz + 1))))%Z ->
    m' (wa x) = m (wa x)).
  { intros x Hx. apply (munch_point _ m m' x MU); [lia|]. cbn [outside]. lia. }
  clear MU.
  split; [exact CTF|]. split; [exact CPTR|]. split; [exact CST|]. split; [exact CNU|]. split; [exact CMAP|].
  split.
  { intros b Hb. cbn [dhd dins]. destruct (Z.eqb_spec b b0) as [->|NE]; [exact CBA|].
    eapply rw_cells_agree; [exact (CT b Hb) | | exact WM]. intros x Hx. apply OUT. unfold TAB in Hx. cbn in Hx. left. lia. }
  split.
  { intros i Hi. cbn [dN dhs dlk dsid dins] in Hi |- *. destruct (Z.eqb_spec i (dN D + 1)) as [->|NE]; [exact CND|].
    eapply rw_cells_agree; [exact (CN i ltac:(lia)) | | exact WM]. intros x Hx. apply OUT. cbn in Hx. right; left. lia. }
  split.
  { cbn [dN dins]. destruct (stk_split asegs m _ (al_nodes L + 16 * (dN D + 1 + 1)) _ SKN ltac:(lia)) as [_ SK2].
    eapply stk_agree; [exact SK2 | | exact WM]. intros x Hx. apply OUT. right; left. lia. }
  { destruct (stk_split asegs m _ (al_store L + 8 * dtf D) _ SKS ltac:(lia)) as [SK1 SK23].
    destruct (stk_split asegs m _ (al_store L + 8 * dtf D + 8 * (sz + 1)) _ SK23 ltac:(lia)) as [_ SK3].
    apply (stk_merge asegs m' _ (al_store L + 8 * dtf D)); [| | lia].
    - eapply stk_agree; [exact SK1 | | exact WM]. intros x Hx. apply OUT. right; right. lia.
    - apply (stk_merge asegs m' _ (al_store L + 8 * dtf D + 8 * (sz + 1))); [| | lia].
      + pose proof (stk_of_rw_cells asegs m' _ _ CFA) as SKF. rewrite SF in SKF. exact SKF.
      + eapply stk_agree; [exact SK3 | | exact WM]. intros x Hx. apply OUT. right; right. lia. }
Qed.

Section PUT.
  Variables (L : alayout) (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo T sz pc : Z) (tb : list word) (tr : list Z).
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis ALO : (ATOP <= lo)%Z.
  Hypothesis LO : (lo <= bv_unsigned sp - 1024)%Z.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis A0 : a0 = Z_to_bv 64 T.
  Hypothesis A1 : a1 = Z_to_bv 64 sz.
  Hypothesis SZ1 : sz = (1 + Z.of_nat (length tr))%Z.
  Hypothesis SZ2 : (sz <= 255)%Z.
  Hypothesis TB : u64arr asegs m T tb.
  Hypothesis LTB : length tb = 255%nat.
  Hypothesis TR : map bv_unsigned (firstn (S (length tr)) tb) = pc :: tr.
  Hypothesis INU : In (pc :: tr) (al_U L).
  Hypothesis SPT : (bv_unsigned sp <= T)%Z.
  Hypothesis T47 : (T + 2040 <= 2^47)%Z.
  Hypothesis AD : ADEPOTi L m.
  Hypothesis LN0 : (AIMG_HI <= al_nodes L)%Z.
  Hypothesis LN1 : (al_nodes L + 1048576 <= ATOP)%Z.
  Hypothesis LS0 : (AIMG_HI <= al_store L)%Z.
  Hypothesis LS1 : (al_store L + 8388608 <= ATOP)%Z.
  Hypothesis RI : rng RNG 0x10000 0x5fd000.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RT : rng RNG T 2040.
  Hypothesis RNODES : rng RNG (al_nodes L) 1048576.
  Hypothesis RSTORE : rng RNG (al_store L) 8388608.

  Notation POST := (depot_put_post L ADEPOTi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  Lemma put_body :
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x71fe8) fc None m (seg_rom asegs)).
Proof.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    unfold AIMG_HI in *.
 assert (RSTK' : rng RNG (bv_unsigned sp + -1024) 1024) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (SZ : (1 <= sz <= 255)%Z) by lia.
    assert (LU : Z.of_nat (length (pc :: tr)) = sz) by (cbn [length]; lia).
    destruct AD as (D & WF & DC & LY). pose proof DC as DC0. pose proof LY as LY0.
    pose proof WF as (N1 & LK & HD & ND & CMP & TF0 & TFB & NB).
    destruct DC as (CTF & CPTR & CST & CNU & CMAP & CT & CN & SKN & SKS).
    unfold TAB, NUNIQ, MAP1, SSTF, SSPTR, SSST in *.
    remember (al_nodes L) as NODES eqn:ENODES. remember (al_store L) as STORE eqn:ESTORE.
    pose proof (CNT_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as CNT0.
    pose proof (BUD_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as BUD0.
    remember (dN D) as N eqn:EN. remember (dtf D) as tf eqn:ETF.
    assert (BN : (1 <= N < 65536 /\ 0 <= tf < 1048576)%Z) by lia.
    clear TFB NB CNT0 BUD0.
    destruct LY as (AN & AS & _ & _ & _ & _ & DISJ). rewrite <- ENODES in AN. rewrite <- ESTORE in AS, DISJ. box DISJ.
    pose proof (mz_init_range sz) as HR0.
    remember (mz_adds (mz_init sz) (pc :: tr)) as HA eqn:EHA.
    pose proof (mz_adds_range (pc :: tr) (mz_init sz) HR0) as HRA. rewrite <- EHA in HRA.
    pose proof (mz_fin_range HA) as HRH. remember (mz_fin HA) as HSH eqn:EHSH.
    assert (HU : hashU (pc :: tr) = HSH).
    { rewrite EHSH, EHA. unfold hashU. rewrite LU. reflexivity. }
    assert (HB : (0 <= bkt HSH < 1048576)%Z) by (unfold bkt; apply Z.mod_pos_bound; lia).
    remember (bkt HSH) as b0 eqn:EB0.
    pose proof (CT b0 HB) as CB0. destruct (HD b0 HB) as [VR VB]. remember (dhd D b0) as v eqn:EV.
    remember (1677400 + 4 * b0)%Z as BA eqn:EBA.
    remember (NODES + 16 * (N + 1))%Z as NDp eqn:ENDp.
    remember (STORE + 8 * tf)%Z as FA eqn:EFA.
    pose proof (munch_refl [(bv_unsigned sp + -1024, bv_unsigned sp)]%Z m) as MU1.
    pose proof (munch_refl (WFINE (bv_unsigned sp) BA NDp FA sz) m) as MU2.
    pose proof (wmono_refl asegs m) as WM.
    subst a0 a1.
    do 8 zstep.
    carve_frame 112%nat ST.
    do 16 zstep. zstep. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true; cbv iota.
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    { exfalso. clear -K1 SZ. rewrite Z.add_0_r in K1. rewrite bv_swrap_small in K1 by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      rewrite Z.mod_small in K1 by lia. lia. }
    zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2 SPT LO LO0. lia. }
    do 14 zstep.
    setreg 12%Z (Z_to_bv 64 (mz_init sz))
      ltac:(f_equal; unfold mz_init;
            first [ replace (Z.land sz 4294967295) with sz by (change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity)
                  | rewrite (Z.mod_small sz 4294967296) by lia
                  | idtac ];
            reflexivity).
    setreg 13%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2, Z.div_small by lia; reflexivity).
    setreg 14%Z (Z_to_bv 64 (T + 8 * sz))
      ltac:(f_equal;
            first [ replace (Z.land sz 4294967295) with sz by (change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity)
                  | rewrite (Z.mod_small sz 4294967296) by lia
                  | idtac ];
            rewrite Z.shiftl_mul_pow2 by lia; lia).
    setreg 11%Z (Z_to_bv 64 (T + 8 * 0)) ltac:(f_equal; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply (hash_loop RNG) with (m := mc) (tb := tb) (k := Z.to_nat sz) (i := 0%Z);
      [ eassumption | exact LTB | exact SZ | lia | exact RT | lia | lia | exact HR0 | ]
    end.
    intros x15' x16'.
    replace (map bv_unsigned (firstn (Z.to_nat (sz - 0)) (skipn (Z.to_nat 0) tb))) with (pc :: tr)
      by (rewrite <- TR, Z.sub_0_r; replace (Z.to_nat sz) with (S (length tr)) by lia; reflexivity).
    rewrite <- EHA.
    do 16 zstep.
    setreg 19%Z (Z_to_bv 64 (mz_fin HA)) ltac:(reflexivity). rewrite <- EHSH.
    do 3 zstep.
    match goal with |- context [Z.shiftr ?e 42] =>
      replace (Z.shiftr e 42) with (4 * bkt HSH)%Z by (symmetry; first [apply bkt_offset | apply bkt_offset_land]; lia) end.
    rewrite <- EB0. rewrite <- EBA.
    zstep. rewrite sx32_lit by lia.
    zstep. zstep. fold_lits. zstep.
    zstep. setreg 25%Z (Z_to_bv 64 v) ltac:(f_equal; change 2147483647%Z with (Z.ones 31); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zstep. zstep. fold_lits. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (CN1 : forall i, (1 <= i <= N)%Z ->
        rw_cells asegs mc (NODES + 16 * i) [C8 (Z_to_bv 64 (dhs D i)); C4 (Z_to_bv 64 (dlk D i)); C4 (Z_to_bv 64 (dsid D i))])
        by (intros i Hi; apply (rw_cells_transport asegs [(bv_unsigned sp + -1024, bv_unsigned sp)]%Z m mc);
            [apply CN; exact Hi | exact MU1 | exact WM | cbn [disjoint_from fst snd cells_size csize Nat.add]; lia])
    end.
    eapply (find_loop RNG) with (N := N) (hs := dhs D) (lk := dlk D) (sid := dsid D) (k := Z.to_nat v) (j := v);
      [ exact HRH | lia | exact CMAP | exact CN1 | unfold AIMG_HI; lia | exact LK
      | intros i Hi; exact (proj1 (ND i Hi)) | exact RI | exact RNODES | lia | lia | |].
    {
      intros j' x11 x12' Hj' Hhs Hin.
      do 13 zstep.
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. unfold depot_put_post. exists j'. do 15 eexists. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU1]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [lia|].
      eapply (adepot_frame L m _ [(bv_unsigned sp + -1024, bv_unsigned sp)]%Z); [exact AD | exact MU1 | assumption |].
      constructor; [| constructor]. cbn [fst snd]. intros a Ha. subst NODES STORE. lia. }
    intros x10' x12' FA0. cbv delta [MAP1].
    assert (FA1 : Forall (fun j => dhs D j <> HSH) (chain (dlk D) (dhd D (bkt HSH)))) by (rewrite <- EB0, <- EV; exact FA0).
    pose proof (dwf_absent_budget (al_U L) D (pc :: tr) HSH WF INU HU FA1) as BUDG.
    rewrite LU, <- ETF, <- EN in BUDG. destruct BUDG as [BTF BNN].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      destruct (stk_split asegs mc _ (NDp + 16) _ SKN ltac:(lia)) as [SKa SKN'];
      destruct (stk_carve asegs mc _ _ 16 SKa ltac:(lia)) as [_ [jn NODEC]];
      replace (NDp + 16 - Z.of_nat 16)%Z with NDp in NODEC by lia;
      apply (rw_cells_split_CB asegs mc NDp [] 16 jn [] [8;4;4]%nat) in NODEC; [| reflexivity]; cbn [mk_CB_cells app] in NODEC;
      destruct (stk_split asegs mc _ FA _ SKS ltac:(lia)) as [SKS1 SKS23];
      destruct (stk_split asegs mc _ (FA + 8 * (sz + 1)) _ SKS23 ltac:(lia)) as [SKSm SKS3];
      destruct (stk_carve asegs mc _ _ (Z.to_nat (8 * (sz + 1))) SKSm ltac:(lia)) as [_ [jf FRC]];
      replace (FA + 8 * (sz + 1) - Z.of_nat (Z.to_nat (8 * (sz + 1))))%Z with FA in FRC by lia;
      apply (rw_cells_split_CB asegs mc FA [] _ jf [] [8; Z.to_nat (8 * sz)]%nat) in FRC; [| cbn [sum_nat]; lia]; cbn [mk_CB_cells app] in FRC
    end.
    clear SKa SKSm MU1 CN1.
    zstep. zstep.
    name_sp sp (-112)%Z.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evtF_cut;
      [ eapply (lock_body RNG) with (lo := lo) (B := BA) (v := v);
        [ eassumption | rewrite Hsp; exact ST | rewrite Hsp; lia | unfold AIMG_HI; lia | reflexivity | exact CB0 | lia
        | unfold TAB, NUNIQ; lia | rewrite Hsp; eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RI | lia] ]
      | post_call asegs mc ]
    end.
    unname_sp.
    zstep. zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3. lia. }
    zstep. zstep. fold_lits. zstep.
    amo_stepW4c. rewrite sx32_lit by lia.
    zstep. rewrite bv_swrap_small by (change (bv_half_modulus 32) with 2147483648%Z; lia).
    zstep. zstep.
    setreg 9%Z (Z_to_bv 64 (N + 1))
      ltac:(f_equal; first [ rewrite Z.mod_small by lia; reflexivity
                           | change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity ]).
    zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4 BN. lia. }
    zstep. zstep. shr0.
    zstep. zstep. fold_lits. zstep. zstep. if_cases K5; zify_cond K5. { exfalso. clear -K5 LN0. lia. }
    zstep. setreg 11%Z (Z_to_bv 64 (N + 1)) ltac:(f_equal; change 65535%Z with (Z.ones 16); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zstep. zstep. setreg 9%Z (Z_to_bv 64 NDp) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. zstep. zstep. zstep. zstep.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [FRa FRbc].
    cbn [cells_size csize Nat.add] in FRbc. change (Z.of_nat 8) with 8%Z in FRbc.
    replace (bv_unsigned sp + -112 + 8)%Z with (bv_unsigned sp + -104)%Z in FRbc by lia.
    apply (proj1 (rw_cells_app asegs _ _ [_; _] _)) in FRbc. destruct FRbc as [FRb FRc].
    cbn [cells_size csize Nat.add] in FRc. change (Z.of_nat 16) with 16%Z in FRc.
    replace (bv_unsigned sp + -104 + 16)%Z with (bv_unsigned sp + -88)%Z in FRc by lia.
    apply (rw_cells_C8_C4C4 asegs _ _ [_] [] sz) in FRb; [cbn [app] in FRb | lia].
    unbox DISJ.
    name_sp sp (-112)%Z.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evtF_cut;
      [ eapply (nstore_body RNG) with (lo := lo) (NDp := NDp) (AR := (bv_unsigned sp + -104)%Z) (T := T) (sz := sz) (tf := tf)
                                      (STORE := STORE) (HW := Z_to_bv 64 HSH) (tb := tb);
        [ eassumption | rewrite Hsp; eassumption | rewrite Hsp; lia | atop_facts; lia | reflexivity | reflexivity | reflexivity
        | exact FRb | rewrite Hsp; lia | exact NODEC | exact CTF | exact CPTR | exact CST | rewrite EFA in FRC; exact FRC | eassumption | exact LTB | exact SZ
        | lia | lia | unfold AIMG_HI; lia | unfold AIMG_HI; lia | lia
        | exact RI | rewrite Hsp; eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RSTK' | lia]
        | eapply rng_sub'; [exact RNODES | lia] | eapply rng_sub'; [exact RSTORE | lia] | exact RT ]
      | let ms' := fresh "ms'" in let PO := fresh "PO" in
        intros ms' PO; cbv beta delta [nstore_post SSTF SSST] in PO; revert ms' PO; post_call asegs mc ]
    end.
    unname_sp.
    zstep. zstep. zstep. zstep.
    zstep. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true; cbv iota.
    do 13 zstep.
    match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.
    release_frame FRa STK (bv_unsigned sp + -104)%Z.
    release_frame FRb STK (bv_unsigned sp + -88)%Z.
    release_frame FRc STK (bv_unsigned sp).
    apply evtF_done. unfold depot_put_post. exists (N + 1)%Z. do 15 eexists. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn [outside]. intros ax Hax. subst NODES STORE. lia. }
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [lia|].
    exists (dins D b0 HSH v (tf + 1) (Z.of_nat (length (pc :: tr)))). split; [| split; [| exact LY0]].
    - rewrite EB0, EV, EB0. eapply dwf_insert; [exact WF | exact INU | exact HU | reflexivity | rewrite <- EB0, <- EV; exact FA0 | lia].
    - rewrite EB0.
      lazymatch goal with |- dcells _ _ ?mf => eapply (dcells_ins L D m mf (bv_unsigned sp) HSH v (tf + 1)%Z (pc :: tr)) end.
      all: cbv zeta; unfold TAB, NUNIQ, MAP1, SSTF, SSPTR, SSST.
      all: rewrite <- ?ENODES, <- ?ESTORE, <- ?EN, <- ?ETF, ?LU, <- ?EB0.
      all: rewrite <- ?EBA, <- ?ENDp, <- ?EFA.
      all: try assumption. all: try lia.
      { rewrite EFA. eassumption. }
      cbn [cells_size csize Nat.add]. lia.
  Qed.
End PUT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem adepot_put : depot_put_stmt ADEPOTi.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adepot ()) ["CANSEC2"] "h01Fh11Lh23RNGh31Th42a0h52a1h62a2h72a3h82a4h92a5h:2a6h;2a7h<2fch=2gph>2loh?1mh@2pchA2rahB2s0hC2s1hD3s10hE3s11hF2s2hG2s3hH2s4hI2s5hJ2s6hK2s7hL2s8hM2s9hN2sphO2szhP2t0hQ2t1hR2t2hS2t3hT2t4hU2t5hV2t6hW2tbhX2tphY2trp;1p;2p;4p;3p;rg001:j11Tg00IAj1=Tg00aIj1?Tg002=j15Tg0000j2VTg0110j1UTg00CPj1CTg00alj2;j1JTg01Rjj4ITg015ej1HTg00:Rj23Tg001_j12Tg016[j2ETg04Ggj2WTg00d2j2DTg00Kjj39Tg01P?j2ATg01;2j1TTg008Lj2<Tg04LRj4STg00>^j10Tg02X:j3KTg034]j4GTg00C0j3BTg01fMj1MTg0467j3FTg002bj2PTg01h7j3Qj1YTg019@j1>Tg013;j1@Tg01doj38Tg04m7lrZTg04n3j2XTf0R0#1#1p=:%10#1#1#1p=7%50#5p=6%00#0p=R%00#0#0#0p=O%00#0#0#0#0#0#0#0p=N%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=L%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=4g01]Ag04o9g00Z;R1#1R2#:R3#:R4#1R5#=R6#?R7%52R8#=/V7%=4#?%=3#?#U\7g00UiR3%C7%C3R4g01V0R9f6R:f5R;fVR<,;6CIp,2rcR=#HR>/3:f7R?fXR@,;6%75R5#2'E'3f9RA,W9g0502,D6997@fSRB1D6A597RCf:RD%211A3?#T'<593f;RE%51#6#6#6RF#2'3P9f?R9f=RGPDCSg01\b1A7Eg00\D#0#R#O#N#L#4#4#4#4#4#4#439P7P3%J61A3E#0f<RH5K7CGAB3GE594f>RI=B3HfeRJ#M5F4fcR4,;6fARK'3fBRL%1F#:#2RF'<%22%58#6#2'P'3fhR8fER25Q=g01[jRMfiRN#>'3fjRO#>%:5#7R5#7RP#2RQ'</3>fkRR#@,3MflRM#@%1P#:#2RP'</3>%25%11#5#6#6#6#1#5#7#7#7#258MfmR1fJR51;6R/E538fnR6?85FfoRFfpR>#>;8QfqRQ#@=8>PfrPQP>PFP6P1PMPRPOPNP8fgffPJfdP4fbfaf`f_f^f]f\f[fZfYP@fWP<fUfTPBfRfQfPfOfNfMfLfKP5fIfHfGfFP2fCPLPKf@P9PIPGPHPEPDPAf8P?P:P;f4f3f2f1P0MrZUUUUUUUUUUUUUUUUUUVCUUUUUUWYWWX@3XO3X33W>W?W<W0XV7XU7XT7XS7XE7XD7XM7XL7XK7XJ7XI7XH7XG7XF7X;7X:7X97X87X77X67X57X47XC7XB7XR7XQ7XP7XX7X=7XN7WAW2W1%Y=,X=eo"). Qed.

Definition adepot_iface : ADepotIface := mkADepotIface ADEPOTi adepot_put adepot_frame.
End CANSEC2.

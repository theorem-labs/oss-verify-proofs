(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer HufHarness.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase ABytes AMalloc_iface AProg_kit AHarness_iface
     AKit AH_huf_kit AH_huf_iface AH_huf_prod Stdio_kit AH_huf_rdt2 AHarness_bm.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AH_huf_lib () := "C46Stdlib5Lists4List2hdC46Stdlib5Lists4List:firstn_mapC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib5Arith8PeanoNat3Nat3minI47Corelib4Init5Peano2le00C56Stdlib5Arith8PeanoNat3Nat5min_lC47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List=length_firstnC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leI47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit>Forall_firstnAK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C47Corelib4Init5Logic9False_indK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission4Spec7Harness=PRODUCER_SIZEI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind00K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface7src_inAc5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_lib7src_lenC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init5Logic3and01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface?HUF_RDT_STACK_AC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface?HUF_DEC_STACK_AK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeC46Stdlib5Lists4List:in_app_iffK47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit9aca_monoAC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree;magree_monoC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSI47Corelib5Lists7ListDef6Forall00K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC45stdpp9bitvector;definitions;bv_unsignedc5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_lib8hC_postAK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr03C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_ifaceAhuf_iserror_postAC5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prodBhuf_iserror_proofAC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge>zb_b2z_nonzeroC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zb_b2z_zeroC56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics5Riscv3Sem4core01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAK47Corelib4Init5Logic2or01c5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_lib6mg_libC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree<magree_transC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8evtF_cutC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00c5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_lib5geomCc5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_lib;PC_HC_JOIN1c5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_lib9src_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litc5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_lib9PC_HC_OUTK4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_lib8noframe0c5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_lib6src_inK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7hinv_bmC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface8prod_atAC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>chunk_user_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=ablock_shadowC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kitAablock_unpoisonedC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC56Stdlib6ZArith6BinInt1Z6shiftrC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission4LibA6ShadowBunpoisoned_full_rdC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit?fse_rt_of_aheapK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflK46Stdlib9micromega=RingMicromega5Psatz07C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit@bytes_at_firstnFC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?AI_block_boundsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeK5ARocqVerifyHarness?AgentSubmission5BothW4AKit5boxed01I5ARocqVerifyHarness?AgentSubmission5BothW4AKit5boxed00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase>ablk_disj_bandC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow@unpoisoned_munchC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC5ARocqVerifyHarness?AgentSubmission3Lib3Tac7sum_natC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3sxbC56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib3MemAsext_extract_byteC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission3Lib5Bytes;lor_lt_pow2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC35stdpp7tactics<f_equal_helpC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem;wr_at_writeC46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le4C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface>prod_rem_postAC5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod?prod_rem_proofAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?wr_at_transportC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_aci_imgC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_aci_loC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?magree_of_munchC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit@stack_not_clientC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit8cr_blockC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit8cr_stackC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kitAshad_stack_clientC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit>rclean_magreeAC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm>hinv_bm_clientC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm>hinv_bm_magreeC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_rdt_postAC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit?shad_not_in_blkC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit8cl_blockC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?bytes_at_magreeC5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit8cl_stackC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?rw_cells_magreec5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_lib3pC2C5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_15C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2c5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_lib7snez01AC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zC5ARocqVerifyHarness?AgentSubmission5BothW4AKit7sxb_litC35stdpp4base6lookupC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoK46Stdlib9micromega=RingMicromega5Psatz05C46Stdlib9micromega;ZifyClasses6mkapp2K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00C5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface6AEMPTYC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop05C56Stdlib6ZArith4Znat5Nat2Z8inj_succc5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_lib;PC_HC_ENTRYC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5msize03C46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7AHBM_LOC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7AHBM_HIC5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_rdt2@HUF_RDT_STACK_A2".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac cl := repeat match goal with H : _ |- _ => clear H end.
(* [comment removed for export] *)
Ltac callt tac := lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply evtF_cut; [ tac | post_call segs m ];
      try (lazymatch goal with |- rng _ _ _ => solve_rng end)
  end.

Definition PC_HC_ENTRY : Z := 0x800dc.   (* [comment removed for export] *)
Definition PC_HC_JOIN1 : Z := 0x8019c.    (* [comment removed for export] *)
Definition PC_HC_OUT : Z := 0x801e8.      (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma snez01A : forall f, 0 <= f <= 1 -> Z.b2z (0 <? f) = f.
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_lib ()) [] "p'0h02Hfh11fh24__x1h31Hh41Nh57__arithh64__ffh78__varmaph85__with91ei001eh:1si011si021np;2p;1p;3p;7p;4p;6p;8p-1p10000p4p710p8p1000Gp4p7210g000fR0p4p710p8g001Bj21Tg001^j1OTg002<j28Tg002Wj2?Tg0037j15Tg003PR1j2ETg0040j26Tg004Mj17Tg004jj30Tg005Dj29Tg005^j7=Tg006<j1<Tg006\j1NTg007<j2MTg007Zj1LTg0088j1ITg008cj2HTg009Fj2;Tg009ij42Tg00:Tj6DTg00;8j1CTg00;Zj7BTg00<>j2ATg00<`j2FTg00=Lj3GTg00=kj4@TP0j6JTg00>]j7KTg00?Aj8>Tg00?eR0f0R2g00@CR330p=4f1R4g00@aR5g00A@R6P6g00A`R7P2g00B@FKp=3f3R8P5P6P6P7f2R9P4P2G>p=:1132g00B`R:#OR;,12'8R<1?43%44R=%5='EP1%49R1%511638#7=008P2%48R1P0P31634#7=004^0<X101133113;'81903W0f4R<P2P8F=W9P2O1%51g00CER1#<%N11M04%L0%I0R1P1P5P6P6P7P01H0:R:g00D1R81;03R=C2,31ED%C6R>P1P1P5P6P6P7P0P=g00DXR=P:C2,31P0P:P=1;0;R=C2,31FBP>P0P=P8P:C2,31C:C:1A17P2P9g00E?R1g00E_R7'91F29=017dAG034C@b6b7b8X20%42g00F?[1134114;'8A00;9[[^20P2f5R9P4P<O3b5A00;<P0P;1632#7=002X10190;P9P2EJb3W4P2O1n200110100021010010102b:W0X10o"). Qed.

Section CANSEC1. Context {rc : runConstT}.

Section PhaseC.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Variable dt_ok : amem -> Z -> Z -> Prop.
  (* [comment removed for export] *)
  Hypothesis RDT1 : huf_rdt_stmtA2 AI rng_fs dt_ok AHUF_RDT_X1.
  Hypothesis RDT2 : huf_rdt_stmtA2 AI rng_fs dt_ok AHUF_RDT_X2.
  Hypothesis DEC1 : huf_dec_stmtA AI rng_fs dt_ok AHUF_DEC_1X.
  Hypothesis DEC4 : huf_dec_stmtA AI rng_fs dt_ok AHUF_DEC_4X.
  (* [comment removed for export] *)
  Hypothesis CIBM : forall a, AHBM_LO <= a < AHBM_HI -> in_ranges CI a.

  (* [comment removed for export] *)
  Variables (L : alayout) (RNG : footprint) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (st : astate).
  Variables (SP lo P D DT W DST dbs mtl streams symbols : Z) (pl : list Z) (rest : Z).
  Variables (pP pd pw : AsanCtrl.aptr) (LB0 LBd : list ablock).
  Notation SPV := (SP - 128).
  Notation LBh := (LBd ++ HB pw W 8704 :: HB pd DT (DTABLE_BYTES mtl) :: HB pP P PRODUCER_SIZE :: LB0).
  Hypothesis HLB0 : forall b, In b LB0 -> exists p A n, b = HB p A n.
  Hypothesis HLBd : forall b, In b LBd -> exists p A n, b = HB p A n.
  Hypothesis DSTC : (DST = 0 /\ dbs = 0 /\ LBd = []) \/ (exists pb, LBd = [HB pb DST dbs] /\ 0 < dbs).
  Hypothesis DBS : 0 <= dbs <= 2^29 + 500.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis STR : 0 <= streams <= 1.
  Hypothesis SYM : 0 <= symbols <= 1.
  Hypothesis RESTR : 0 <= rest <= zlen pl.
  Hypothesis SZ : zlen pl < 2^26.
  Hypothesis PLB : Forall (fun c => 0 <= c < 256) pl.
  Hypothesis PAYL : (pl = [] /\ D = AEMPTY) \/ (exists p, In (HB p D (zlen pl)) LB0 /\ 0 < zlen pl).
  Hypothesis D16 : D mod 16 = 0.
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - AHARNESS_STACK.
  Hypothesis SPT : SP + 16 <= al_top L.
  Hypothesis SP47 : al_top L <= 2^47.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RFS : rng_fs L RNG.
  Hypothesis RFRM : rng RNG SPV 128.                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HBLK : forall b, In b LBh -> exists p A n, b = HB p A n.
  Hypothesis ABLK : forall b, In b LBh -> ablk (ab_addr b) (ab_addr b + ab_size b).
  Hypothesis SRCIN : 0 < rest -> exists p A n, In (HB p A n) LBh /\ A <= D /\ D + rest <= A + n.
  Hypothesis SEP1 : DT + DTABLE_BYTES mtl <= D \/ D + rest <= DT.
  Hypothesis SEP2 : W + 8704 <= D \/ D + rest <= W.
  Hypothesis SEP3 : DST + dbs <= D \/ D + rest <= DST.
  Hypothesis SEP4 : DT + DTABLE_BYTES mtl <= DST \/ DST + dbs <= DT.
  Hypothesis SEP5 : P + PRODUCER_SIZE <= DT \/ DT + DTABLE_BYTES mtl <= P.
  Hypothesis D16' : 16 <= D.
  (* [comment removed for export] *)
  Hypothesis OWN : forall a, aclient_addr CI LB0 SPV a -> ~ (DT <= a < DT + DTABLE_BYTES mtl) /\ ~ (W <= a < W + 8704)
                                                           /\ ~ (DST <= a < DST + dbs).

  Notation src := (firstn (Z.to_nat rest) pl).
  Lemma src_len : zlen src = rest.
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_lib ()) ["CANSEC1"; "PhaseC"] "h02Hah14__p1h24__p2h34__x1h44__x2h54__x3h61xh71Hh83H48h97__arithh:4__ffh;7__sat49h<7__sat50h=7__sat51h>7__sat52h?7__sat53h@7__sat54hA7__sat55hB7__sat56hC8__varmaphD5__withE4__x4hF4cstrhG3z48hH1nhI1yp&0p;1p;2p;<p;3p;4p;6p;7p;8p100F\p4p7210g005^R0p4p710p8g00GHR1k100Tg00Ghj2[Tg00HHj2fTg00H_R2j1GTg00I?j1tTg00J=j13Tg00Jbj10Tg001^j18Tg00KGj1~Tg001BR3j22Tg002<j25Tg00L=j2WTg004jj1sj3CTg00LZj1qTg005Dj2ETg00M8l<YTg00M]j1cTg00NBj2aTg00Ndj2ATg00O@j2ITg00OZj2JTg00PBj2KTg00P_j3HTg00QCj2PTg00R4j2OTg00RTj1?Tg00S3j2=Tg00S\j1^Tg00T:j2]Tg00T[j3\Tg00UDj2BTg006<j1}Tg00V0j3@Tg006\j1|Tg007<j2NTg00VPj1{Tg007Zj1xTg0088j1wTg008cj2DTg009Fj2UTg00;8j1pTg00<>j2lTg00<`j2kTg00=Lj3iTg00=kj4jTg00Vnj4VTg00WYj2mTg00X9R4j2nTg00XSj3eTP0j6STg00Y5j3dTg00YTj3rTg00Z6l<ZTg00Z[j3uTg00[Dj4bTg00[bj6vTg009ij4XTg00>]j7`Tg00;Zj7yTg00\Fj7zTg00?Aj8_Tg00?eR0f1R5f0R63Cp=:%36#3#3#3p=6%06#0p=R%06#0#0#0p=Q%06#0#0#0#0#0#0#0p=FP0g00\jR7P0P0P1f4R1P2f3R8g00]If2R9P5P6M<Zp=hP7P0P0P0P2P2f5R:P1P8P9P5P6M<Zp=gg00@CR;/26p=1Au056p=;P0P9P5P6Cbp=7P5g00@aR<g00A@R=P=g00A`R>P6Evp=LP0P5g00D1P6CXp=MP5P<P=P=P>P6g00B@F`p=4P9P<P=P=P>P5P6Fyp=<P0P5g00DXP6CXp=>P9P<P=P=P>P5P6Fzp=TP8P<P=P=P>P9P5P6G_p=9P7P0P4P2P3g00^6P:P1P8P9P5P6M<Yp=oP7p,4restR3$00R2p,2plR4,[0R<'f%G6R?/:3XH7R@P7P2P@p,2rcR@#tRAg00B`RB#3RC#3RD#6#6#6RE#0#6#6#0#R#Q#F#F#8%~@R@'2%3E#6#6#0#R#Q#F#F#8,2@'5R@%G2RE/:31W;3RF/:3RGP0P0%s0RHP6X60RIPH1:56#qXI0X60PEPFPIPI1E0?X67P2PFPI1W;6X60P3P31E03RIDhR7EgP3P3PIM<Y%c<RI%G<R?#1RE1a;3RH1A;3RJ/5G123;RGAC0F;'5'IRKPFP0%0BRL#8RM%6L#8RN'JRO1A;MRP%1N1KMNRQ,A;[[RR%1MRSg00^XRTAHMN5UW0RN%1Q\T^0SRQp,2SPRU%0LRV#0RW#0#8RX'PRY%1U%1XRZ1OUX#1[[RU%0D#3#8RD,JMR[%1D1KMDR\,A;[\PR]AHMD5VTX0SRD%1\\T^0SR\%0C#3#0#8RC,JMR^%1C1KMCR_,A;[\PRPAHMC5VTX0SRC%1_\T^0SRSp,1DRT/PXR_%1T1OTX#1\Z[RZp-0RMg00CER`g00_4Ra#?Rb#?Rc#?Rd#?Re,=0%^B,]01=0dRd5\01=0aRa';Rf';g00_SRg'B1=0b/;aRa,;d/Bg1Bfg%}`Rf5@`5@`3@%|`Rd1N091N08Rb%{0Rh778?78h775%x0Ri%w0Rj1Lj:1D0BRB1D0LRL'M,4jRk5<j1U0;Rl,>L,4j1MBl,4jRm5<j5Tj%p=R=Pj1U0X%3V,D0'>,4jRVP=Pj1>lL,4jRnf6Ro,LjRp5<jP=PkC9C9C91lj>R>P6P9g00E?Rkg00E_Rq'E1k69=CkqdAi0;5CjRqb:bCbDX30X40X50X1MW21:65,58125;AC06;R;'5'I12X8%18/5o1:81[[[^30^40^50^1M^2MP6123?PJPTP3f9R8f:Rop,4D16'Rkp,5RESTRRrO8b9b;b<b=b>b?b@bAbBbGb8bFCVb71m2<PAP@1n2<12F?P2PFP7P<P?1E0?EoPIPEPHPKPFP0POPRPNPQPYPUP[P]PDP\P^PPPCPSP_PZ%?e,=0Re1=0c/;a';/Bg1;ea/Bg=@`f5@`PdA7b1h?79h1N01?71h?71h775PiPj1D0WRW,MB,4j9<jpf7,Lj=<jm5TjP=PjPnP=PjPVP=Pj1>lW,4j1>WL,4j5<jP=1>BL,4jC9C9C9C9P>Pqb:bCbDX30X40X50XE0X1MX2M1:69,5115:;'I%1912X:%1:12:1'5121:[[[[^30^40^50^E0^1M^2MP6PGPJPTP3P?P8Pof;PkPrO:b9b;b<b=b>b?b@bAbBbGb8bFCVb79e2<ESAd024,[0Ar024ESo"). Qed.
  Lemma src_bytes : Forall (fun c => 0 <= c < 256) src.
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_lib ()) ["CANSEC1"; "PhaseC"] "h01cp;2p;1p;5p100`?p4p70R0p10000p4p710p8P0p1000fp4p710p8P0p100a6p4p710p8P0p1005^p4p710p8P0p100aSp4p710p8g001Bj26Tg00Jbj10Tg001^j12Tg00Ndj21Tg002<j25Tg00GHj14Tg00b0j53Tg00?eR0g00@Cf0R1'6g00B`#0#0#0#0#0#0#0#0#2,11'5X00p,4rest#4p,2plp,3PLBD3o"). Qed.
  Lemma noframe0 : forall F k, ~ In (mkABlock (ABFake 0) F k) LBh.
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_lib ()) ["CANSEC1"; "PhaseC"] "p'0h01nh11Ah21Hh31pi001ph41eh51Eh61Fh73Hinh81ki011ai027ab_addri037ab_kindi047ab_sizei053clsi061xp;1p;3p;2p;6g00c3j1BTg00clj30Tg00Jbj15Tg00J=j1ATg001^j1;Tg00dej1:Tg00V0j36Tg00aSj39Tg00eij38Tg00f@R0j27Tg000fj6@Tg00fZj2?Tg0037j1<Tg00g9j1=Tg004jj3>Tf0R1#5#5p=4f2R2#=f1R3;01p=1g00h2R4?>31p=3g00?eR5/71p=2g00@C#BR6?031p,3LBdp,2pwp,1Wg00B`#5#4#A#5#4#4#4#4#;31p,2pdp,2DTp,3mtl#:31p,2pPp,1Pg00hk31p,3LB0564564564594584R7p,4HBLKA0623P1O2g00`?R8f5R9f4R:506A1231R;'3X05#2X15#2X38'7P0P8f6R<=069/3;X05#2X15#2X38g00F?R=P1f8R>f7506/3;X05#2X15#2P0P5f9R;=06>f3?131'3X05#2X15P=P1f;R?f:506A1931'3X05#2P0P5f<=06?A1<21'3X05P=P1f>R<f=506A1>:1'3P4f?=06<P4p-0R<P1g00ijP<P2P=g00^Xn0110100021010010105n01101000130103102104X44g00jcA1;93P1E@P=1?=1b2W5X05P3P1O2n2001000000120106000W2X15P3P1O2n2001000000120106000W2X38P3P1O2n2001000000120106000b4W7%<7eX85X65o"). Qed.
  Lemma src_in : src_inA LBh D src.
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_lib ()) ["CANSEC1"; "PhaseC"] "h01Hh11zh21Ah31nh41pp;1p;3p;2p;6g00GHj1ETg00Y5j3DTg00Ghj2>Tg00H_j1<Tg00Ndj26Tg00g9j13Tg00clj32Tg00Jbj11Tg00J=j1=Tg001^j1;Tg00dej1:Tg00V0j34Tg00aSj3CTg00eij3BTg001Bj29Tg00k?j28Tg002<j27Tg00f@j25Tg000fj6?Tg005^j6@Tg00k\j3ATf0R0#1#1p=0g00@CR1g00?eR2p,4restR3#Ep,2pl5D2R4'>#<R5'6P2P3g00`?R6g00h2R7f2#3f1R8;20p,3LBdp,2pw#3p,1Wg00B`#1#0#=#1#0#0#0#0#;32p,2pd#3p,2DTp,3mtl#:32p,2pP#3p,1Pg00hk32p,3LB05475475475C7R73Bp,1DR9,98f3,891880'9'7'7X32,52X22,52X46'5X12P2P51610X12P0P3g00l[R2E?1613p,5SRCINP0O1b0P5P2E@W0AA794eo"). Qed.

  (* [comment removed for export] *)
  Definition hC_postA (m : amem) : machine_state -> Prop :=
    fun ms' => exists (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y18 y19 y24 y25 y26 y27 x28 x29 x30 x31 : word) (m' : amem),
      ms' = MS (mkR x1 (Z_to_bv 64 SPV) gp tp x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 D) x10 x11 x12 x13 x14 x15 x16 x17
                    y18 y19 (Z_to_bv 64 DT) (Z_to_bv 64 W) (Z_to_bv 64 DST) (Z_to_bv 64 dbs) y24 y25 y26 y27 x28 x29 x30 x31)
               FR (Z_to_bv 64 PC_HC_OUT) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo SPV
      /\ magree bsegs (aclient_addr CI LB0 SPV) m m'
      /\ AHEAP AI L RNG st LBh m'.

  Lemma geomC : 0 <= SPV /\ SPV + 16 < al_top L /\ ATOP + 4096 + 16384 <= SP /\ lo <= SPV - HUF_RDT_STACK_A /\ lo <= SPV - HUF_DEC_STACK_A
                /\ SPV mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_lib ()) ["CANSEC1"; "PhaseC"] "h04__x1h14__x2h22Hah34__p1h44__x3h54__x4h67__arithh74__ffh87__sat48h97__sat49h:7__sat50h;7__sat51h<7__sat52h=7__sat53h>7__sat54h?7__sat55h@8__varmaphA5__withB4cstrhC4__x5hD4__x6hE4__x7hF4__x8hG3ATRhH1HhI2H0hJ2H1hK3H10hL3H11hM3H12hN3H13hO3H14hP3H15hQ3H16hR2H2hS2H3hT2H4hU2H5hV2H6hW2H7hX2H8hY2H9hZ7__sat56p%0p&0p;1p;2p;3p;4p;6p;7p;8g00I?k10;Tg00J=j16Tg00Jbj10Tg001^j17Tg00KGj1yTg001Bj23Tg002<j21Tg00mXj2ETg00k?j25Tg00n5k109Tg00Ndj24Tg00R4j2eTg00Ghk203Tg00M]k100Tg00H_j1}Tg00OZj2ZTg00PBj2\Tg00P_j3[Tg00QCj2gTg00RTj18Tg00S3j2mTg00UDj2VTg006<j1rTg00V0j3OTg006\j1qTg00VPj1pTg007Zj1oTg0088k10:Tg00;8k108Tg008cj2kTg009Fj2jTg00<>k206Tg005Dk205Tg00<`k204Tg004jj3cTg00=Lk302Tg00=kk401Tg00nlj2aTg0037j1~Tg00oMj2`Tg00ojj2MTg010Gj2_Tg010nj2^Tg011Uj2WTg012;j2]Tg012aj2XTg00S\j1{Tg00T:j2zTg00T[j3YTg013]j2hTg00:Tj6xTg014Ij3lTg014lj4JTg00Z[j3wTg007<j2vTg00[Dj4dTg009ij4TTg00>]j7QTg00[bj6uTg00;Zj7tTg015Gj3sTg015jk307Tg00?Aj8NTf0R0#6#6#6#6p=@%00#0p=U%00#0#0#0p=f%00#0#0#0#0#0#0#0p=Pg00@CR1/30p=2f2R2f1R3/E0'3p==g00?eR4?c01p=B%60#6p=|1m40p=<Aw430p=;1v40p=GP4P2P3P0Cdp=IP4P4f4R5f3R6P2CdP3P0Cdp=D1j40p=H1k40p=9P2g00@aR7g00A@R8P8g00A`R9P4P3g00DXR:P0CTg00B@R;FQp=:P3P7P8P8P9P0Eup=nP2P7P8P8P9P3P0Ftp=SAs430p=AB07430p=CP6P7P8P8P9P2P3P0GNp=Rf5R<P7P8P8P9P5P7P8P8P9P4P6P:P2CTP;FQP3P0GNp=>f6R:P7P8P8P9P<P5P6P7P8P8P9P2P3P0GNGNp=LP4P3g016MP0CTp=bP3P7P8P8P9P0P;FQp=FAc430p=?P4P3g00D1P0CTp=KP5P7P8P8P9P6P7P8P8P9P2P;FQP3P0GNp=ip,2rcR;$0;g00B`R=#6R>#6R?#@#@#@R@#0#@#@#0#U#f#P#P#7RA%y;R;'3%6@#@#@#0#U#f#P#P#7,3;R@'1p,2SPRB%0=RC#0RD#URE#0#URF#7RG'ERH#2RI%7ERJ,5Hp,1L$09S00'4RK%0F#fRF#7RL,5;%0FRF#0#7RM'5/3BRNp,2loRO%7FRF7=HRP1eHJRQ#BRR,1PS01'1S02'1S03'1p,2pl-034RS$00RT%}S#2RS%7CRU%6CS04#6S05#|#7RV'ZRW141URX%2V1\UVRY,41[[RZ%2UR[g00^XR\A[UV3UW2RV%2Y\\^2[RY1gBJR]%2B%2JR^1eBJR_#2S06[[R`%0?S07#6#7R?,ZURa%2?1\U?Rb,41[\XRcA[U?3V\X2[R?%2b\\^2[Rb%0>R>#6Rd#0#7Re,ZURf%2e1\UeRg,41[\XRXA[Ue3V\X2[Re%2g\\^2[R[p,1DR\/gJRg%2\1e\JRU#2S08\^[Rhp-0Rig00CERjg00_4Rk#8Rl#8Rm#8S09#8S0:#<S0;%<m%<lS0<1m4k';S0=';S0>';g00_SRk'V%rjRl3O%qjRm%p4Rn%G6Ro7I5P5PnP3%G2RpP5%G5S0?P5PnDDDD%o4Rq&0:4Rr%HARs%0>S0@#9R>5:rS0A1nr:Rt5Sr&088RuPr%HJRv%6D#95:rS0BPuPrPr%9dRd1k4=RD%HMRw'APuPr%HLRx,C>=:rdS0CPu1j41R>%HGRy,ADRz5:rCRE>FL206r9R{P0P2g00E?R|g00E_R}+0520402=c|}dB02413H01R}b7b@bAX04X14X44X54W313A2/1513J2A=<2M15<L/3:1E5G#2[[[[^04^14^44^54^3iP0P@POP;P\PBf:R|p,4D16'S0Dp,3LOSR~p,3BOTS0EO9b6b8b9b:b;b<b=b>b?bBPKQ03PTPSPWPZPVPYP]P`PaPcP?PbPfPXPeP[PgPhPlPmAIp3nS03PqPrPr1CDv%9CRCPu1Czv/bC,FrE>P{P}b7b@bAX04X14150J/331E3G/5J/42[^04^14P0Q00PBp,3SPTO3b6b8b9b:b;b<b=b>b?bBPNQ02PTPSPWPZPVPYP]P`PaPcP?PbPfPXPeP[PgPhQ0>/Vk=OjlPmPnP2AIo5nP3PnP5Q0?P5PnDDDDPqPrA:rsD=SrtPuPrQ04#0#99:rvPuPrPrPd1ACwRtPuPrPr1CDxRxPdPu1Cxw=:rCE>E>FLP{P}b7b@bAX04X14X44X54X3i13A0/1513J6A=<6M156L/3:155L/5M/3<[[[[^04^14^44^54^3iP0P@POP\PBP;P|Q0DP~Q0EO9b6b8b9b:b;b<b=b>b?bBPPQ01PTPSPWPZPVPYP]P`PaPcP?PbPfPXPeP[PgPhPlPmQ03PqPrPrPDPtPu1ACy%HF'A9:rDE>P{P}b7b@bAX04X14A=03M1E2G==3F[^04^14P0PBPOP~O3b6b8b9b:b;b<b=b>b?bBRFPPPRPFPTPS1gHJ%2QRS\^\IPWPZPVPYP]P`PaPcP?PbPfPXPeP[PgPh1aHJ%BJRh#~Rg1`HJR[,MJ/5Q,?H[1_HJ141JRe14QJ,1S[1^HJ14J1RS14JQ13Q1'1[1WHJ%B[\h1]HJ1?QH\hg00jcRX1XHJRfePf1a\J1`\JRf,MJ/5U,?\\g1_\JQ0814UJ'1\e1^\J14JU13U1'1\S1W\J%Bf\h1]\J1?U\\hPX1X\JRUePU1aBJ1`BJRU,MJ/5_,?B\g1_BJQ0614_J'1\e1^BJ14J_13_1'1\S1WBJ%BU\h1]BJ1?_B\hPX1XBJRXePX%{=,z4R=Q0:#8#8#8RX#8RS#8#8R1#<5Y4%<SRS%<XQ09#<9Y4=';';';%81#<AY4=SQ0;Q0<';';';Q0=/Vk'h'hRkAOjkl5OjPm%G:f8Rm%GmPmPoDDPmf7Ro#G?I<n9InmP3PpPmQ0?PmPnDDDDPqPrPrPrP7P8P8P91Kv>,FrExR9PuQ07#9R8Q0@#0#99l4v%9ERE'C'K,FrCRPuPrPrPr1b>vPuA:r>DR71bDv,Fr5SrDiPuPrPrP9Pu1A8yRyQ05#0#99l4v/CD'K,FrCRPuPrPrPrP>PyPuPrPrP>PvPuP7E>E>PuPrQ0A1nr|5SrPuPrQ0BPuPrPr1KE>PuPrPrPd1A8wPuPrQ0CPu1KD>,FrCRE>DiFLFLFLP{P}b7b@bAX04X14X44X54XC4XD4XE4XF4X3ig00F?\hRh1MJm/5:,?<[%22142J'1\e1EoGRof9RG,MJ/56'?\h%2o%2<\^[13A:f<'113J:f;RJ#BA=|JM15|L/3J%BG[[[[[[[[[^04^14^44^54^C4^D4^E4^F4^3iP0P@PUP[P_PBPOP;P\PQP:fAfBfKfMQ0Dp,4SP16P~Q0EOBb6PRebQbPbObNbMbLbKbYbXbWbVbUbTbSbRbJbIbHb8b9b:b;b<b=b>b?bZbBCJCJCJCJCJg01749=OHg018;9=OH/1R'1,1N,1K,1IebGo"). Qed.

  (* [comment removed for export] *)
  Lemma mg_lib : forall (X : Z -> Prop) m m',
    (forall a, aclient_addr CI LB0 SPV a -> X a) ->
    magree bsegs (fun a => aclient_addr CI LBh SPV a /\ X a) m m' -> magree bsegs (aclient_addr CI LB0 SPV) m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_lib ()) ["CANSEC1"; "PhaseC"] "h02Hah11ah21Ah31Hh44__x1h51lh62l'h72HXh82Hbh92MGh:1Xh;7__arithh<4__ffh=7__sat48h>7__sat49h?7__sat50h@7__sat51hA7__sat52hB7__sat53hC7__sat54hD7__sat55hE8__varmaphF5__withG1bhH4cstrhI1mhJ2m'p;1p;2p;5p;3p;4p;7p;:g00Jbj10Tg019Bj1LTg019`j1HTg01:Cj1iTg01:ej2WTg001^j13Tg00mXj2JTg01;aj5?j4TTg00g9j1@Tg00J=j12Tg00clj3CTg00dej1hTg00V0j3DTg00aSj3<Tg002<R0j2FTg01<fj4UTg006\j1ATg00eij35Tg00O@j2KTg01=aj4STg004jj39Tg01>@j3:Tg00I?j1RTg00KGj1QTg001Bj2=Tg00Ghj2PTg00M]j1OTg00H_j1NTg00OZj2>Tg00Ndj28Tg00PBj2ETg00P_j3BTg00QCj2GTg00R4j2MTg006<j1gTg007<j2fTg007Zj1]Tg0088j1\Tg008cj2YTg009Fj2XTg015Gj3ZTg009ij4[Tg00>]j7VTg00<>j2^Tg005Dj2_Tg00<`j2`Tg00=Lj3aTg00=kj4bTg01>Zl:cTg014lj4dTg01?Yj7eTf0R1#0#0p=;%01#0#0#0#0#0#0#0p=7g00h2R2f1R3;51p=6%21#2#2#2p=4%01#0#0#0p=Ig00@CR4/=1p=1g00?eR5p-0[g00B`R6#0R7#;R8#0R9#;R:#L#H%L8#H#i[R;p,2rcR<p,2AI,W<R=p,3LB0R>p,2SPR?%0:#3R:'JR@P1D?RAf4RBP3O1[^15g01@YRCP<P=p,3LBdRDp,2pw#@p,1W%28#0#7#33CR8p,2pd#@p,2DTp,3mtl#h3CREp,2pP#@p,1Pg00hk3CRF=D2>RG5D2RH5D2RI5<2RJP@P1D?RKPBP1O1'FX15f2RLP3CUPCf5RCP1O1,FKX15P<P=P>P@CTf3RKPLP1P<P=PJP@P3D?f6P3O1P<P=P>PJP@P@P3P1161>g00a6p4p710R@%A1RJ%A3R=P0A<KL395K1A5B3KA5B3L'KR0[A5K1LA5K13'KA<BKL95B3[RMA<CBK95CL\0PKPLP3P1CSP1n2001000000120000000X1LW6W5W2PM^1L^6=^5J^2@P1P2PDPIPL16LD16LIA928L16LHA92EL16LGA92FL16L>;:33:3:3:O5b3W8XG2%R<%26R2#2R>#4#4#4RF#0#4#4#0#;#I#7#7#3%Q<R<'=%2F#4#4#0#;#I#7#7#3,=<'Fp,2pl,P5R<#O%N<#1%37R<%47#3R7'>184<RF%171E<7RG,84[[%1<REg00^XRHAB<73UW0%1G\H^0E%39R9,G?%1?%19RG1M?9#1[[%0>#2#3R>,><%1>1E<>R7,84[\FAB<>3VHX0E%17\H^0E%02#2#0#3R2,><%121E<2R7,84[\FAB<23VHX0E%17\H^0Ep,1DRE/G9%1E1ME9#1\G[g00CERG#g%AG1f53%]5%\5RGg00@ag00A@REPEg00A`REP51Y561X5:5Z5R6g00DXP6C[g00B@FV1^GEP1PLg00E?REg00E_RG'_1`1L=9EGdAa543Cbb<bEbFX451J1:R:/=:^45P1P?O1b;b=b>b?b@bAbBbCbDbHb3M:cPKP3P1O2CdX0AX15FeW9W7XJ;WIW:o"). Qed.

  (* [comment removed for export] *)
  Lemma pC2 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 y24 y25 y26 y27 x28 x29 x30 x31 : word) (m0 m1 : amem) (r flags : Z)
      (rstk : region),
    0 <= r < 2^64 -> (r < 2^64 - 119 -> dt_ok m1 DT mtl) -> 0 <= flags < 64 ->
    AHEAP AI L RNG st LBh m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo SPV ->
    rclean m1 rstk -> r_lo rstk <= lo -> SP <= r_hi rstk -> ATOP <= r_rlo rstk -> rrng RNG rstk ->
    magree bsegs (aclient_addr CI LB0 SPV) m0 m1 ->
    bytes_at bsegs m1 D (map (Z_to_bv 8) src) ->
    rw_cells bsegs m1 SPV [C8 (Z_to_bv 64 streams); C8 (Z_to_bv 64 ASHOFF); C8 (Z_to_bv 64 symbols)] ->
    evtF bsegs RNG (hC_postA m0)
      (MS (mkR x1 (Z_to_bv 64 SPV) gp tp x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 D) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 flags) (Z_to_bv 64 rest) (Z_to_bv 64 DT) (Z_to_bv 64 W) (Z_to_bv 64 DST) (Z_to_bv 64 dbs)
               y24 y25 y26 y27 x28 x29 x30 x31)
          FR (Z_to_bv 64 PC_HC_JOIN1) fc None m1 (seg_rom bsegs)).
Proof.
intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 y24 y25 y26 y27 x28 x29 x30 x31 m0 m1 r flags rstk
  R0 DTOK FL AH MI ST RC RLO RHI RRLO RR MG BY CS.
unfold PC_HC_JOIN1.
pose proof geomC as (GA & GB & GC & GD & GE & GF).
Local Ltac pw2 := try change (2^26) with 67108864 in *; try change (2^29) with 536870912 in *;
  try change (2^32) with 4294967296 in *; try change (2^47) with 140737488355328 in *;
  try change (2^64) with 18446744073709551616 in *; lia.
assert (SPR : 0 <= SP - 128 < 2^64) by pw2.
Local Ltac dside := rewrite ?unsigned_lit in * by assumption; first [ assumption | reflexivity | exact noframe0 | exact src_in
  | exact src_bytes | (unfold harness_invA; exact I) | (rewrite src_len; first [ reflexivity | assumption | pw2 ])
  | (apply in_or_app; right; cbn [app In]; right; left; reflexivity) | pw2 ].
Local Ltac uptodec := repeat (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?n) _ _ _ _) =>
  let b := eval vm_compute in (orb (Z.eqb n AHUF_DEC_1X) (Z.eqb n AHUF_DEC_4X)) in
  lazymatch b with false => zstep end end).
Local Ltac retlit := match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  rewrite (ret_pc_even n); [| change (2^64) with 18446744073709551616; lia | reflexivity] end.
Local Ltac decpost := intros ms' PO; destruct PO as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & MI' & ST' & MG' & AH');
  subst ms'; rewrite ?unsigned_lit in MG', ST' by pw2; retlit.
Local Ltac cfin := apply evtF_done; unfold hC_postA; do 23 eexists; split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|];
  split; [eapply magree_trans; [eassumption| refine (mg_lib _ _ _ (fun a Ha => proj2 (proj2 (OWN a Ha))) _); eassumption] | eassumption].
do 4 zstep.
zstep. if_cases K; zify_cond K.
- apply evtF_done. unfold hC_postA. do 23 eexists. split; [reflexivity|].
  split; [exact MI|]. split; [exact ST|]. split; [exact MG| exact AH].
- assert (RL : r < 2^64 - 119).
  { revert K. match goal with |- Z.lxor (Z.b2z (r <? ?N)) 1 = 0 -> _ => destruct (r <? N) eqn:EQ; intro K;
      [apply Z.ltb_lt in EQ; change (2^64 - 119) with N; exact EQ | cbn in K; discriminate] end. }
  pose proof (DTOK RL) as DT1.
  assert (DSTL : (DST = 0 /\ dbs = 0) \/ (exists pb, In (HB pb DST dbs) LBh)).
  { destruct DSTC as [(E1 & E2 & E3)|(pb & E1 & E2)]; [left; split; assumption|].
    right. exists pb. rewrite E1. apply in_or_app. left. left. reflexivity. }
  zstep. zstep. if_cases K2; zify_cond K2.
  + uptodec.
    eapply evtF_cut; [ first [
        eapply (DEC1 L RNG _ (Z_to_bv 64 (SP - 128)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                FR fc m1 st LBh DST dbs D DT mtl flags pd src lo rstk)
      | eapply (DEC4 L RNG _ (Z_to_bv 64 (SP - 128)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                FR fc m1 st LBh DST dbs D DT mtl flags pd src lo rstk) ] | ].
    all: try dside.
    all: decpost. cfin.
  + uptodec.
    eapply evtF_cut; [ first [
        eapply (DEC1 L RNG _ (Z_to_bv 64 (SP - 128)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                FR fc m1 st LBh DST dbs D DT mtl flags pd src lo rstk)
      | eapply (DEC4 L RNG _ (Z_to_bv 64 (SP - 128)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                FR fc m1 st LBh DST dbs D DT mtl flags pd src lo rstk) ] | ].
    all: try dside.
    all: decpost. zstep. cfin.
Qed.

  (* [comment removed for export] *)
  Lemma pC1 : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 y22 x28 x29 x30 x31 : word) (m : amem) (f1 f2 f3 f4 f5 : Z) (jdt : list byte)
      (rstk : region),
    0 <= f1 <= 1 -> 0 <= f2 <= 1 -> 0 <= f3 <= 1 -> 0 <= f4 <= 1 -> 0 <= f5 <= 1 ->
    AHEAP AI L RNG st LBh m -> mem_inv bsegs m -> stk bsegs m lo SPV ->
    rclean m rstk -> r_lo rstk <= lo -> SP <= r_hi rstk -> ATOP <= r_rlo rstk -> rrng RNG rstk ->
    rw_cells bsegs m DT [CB (Z.to_nat (DTABLE_BYTES mtl)) jdt] ->
    hinv_bm m ->
    prod_atA m P D rest ->
    bytes_at bsegs m D (map (Z_to_bv 8) pl) ->
    rw_cells bsegs m SPV [C8 (Z_to_bv 64 streams); C8 (Z_to_bv 64 ASHOFF); C8 (Z_to_bv 64 symbols)] ->
    evtF bsegs RNG (hC_postA m)
      (MS (mkR (Z_to_bv 64 PC_HC_ENTRY) (Z_to_bv 64 SPV) gp tp x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 D) (Z_to_bv 64 DST)
               x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f5) (Z_to_bv 64 mtl) (Z_to_bv 64 DT) (Z_to_bv 64 W) y22 (Z_to_bv 64 dbs)
               (Z_to_bv 64 f1) (Z_to_bv 64 f2) (Z_to_bv 64 f3) (Z_to_bv 64 f4) x28 x29 x30 x31)
          FR (Z_to_bv 64 PC_HC_ENTRY) fc None m (seg_rom bsegs)).
Proof.
intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 y22 x28 x29 x30 x31 m f1 f2 f3 f4 f5 jdt rstk
  F1 F2 F3 F4 F5 AH MI ST RC RLO RHI RRLO RR JD HBM PR BY CS.
unfold PC_HC_ENTRY.
pose proof geomC as (GA & GB & GC & GD & GE & GF).
pose proof ATOP_range as AR. unfold ATOP_MIN, ATOP_MAX in AR.
destruct (AI_block AI _ _ _ _ _ pd DT (DTABLE_BYTES mtl) AH ltac:(apply in_or_app; right; cbn [In]; right; left; reflexivity))
  as (NB & (BR1 & BR2 & BR3 & BR4) & RDTA & RDTS & BSH & _).
assert (RSH1 : rng RNG (Z.shiftr DT 3 + ASHOFF) 1).
{ unfold shad, shlen in RDTS. eapply rng_sub; [exact RDTS| rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia |]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  assert (8 <= DTABLE_BYTES mtl + 7) by lia. Z.div_mod_to_equations. lia. }
unfold ablk, AIMG_HI, KLS in BR1.
assert (PM : 2 <= 2^mtl <= 4096) by (split; [change 2 with (2^1)| change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
assert (NB12 : 12 <= DTABLE_BYTES mtl) by (unfold DTABLE_BYTES, DT_BYTES; lia).
assert (A8 : DT mod 8 = 0) by (clear - BR4; Z.div_mod_to_equations; lia).
pose proof (ablock_unpoisoned m DT (DTABLE_BYTES mtl) BSH A8 ltac:(lia) ltac:(lia) ltac:(lia)) as UNP.
pose proof (unpoisoned8_rd_off m DT (DT + DTABLE_BYTES mtl) DT 0 UNP ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact A8)) as RD0.
rewrite Z.add_0_r in RD0.
zstep. if_cases K1; zify_cond K1.
- exfalso; lia.
- zstep. zstep. zstep. if_cases K2; zify_cond K2.
  + exfalso. apply K2. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. clear - BR4. Z.div_mod_to_equations. lia.
  + zstep. zstep. zstep. zstep.
    zstep. if_cases K3; [exfalso; clear - K3; vm_compute in K3; discriminate K3|].
    do 16 zstep.
    assert (SZN : Z.to_nat (DTABLE_BYTES mtl) = (0 + 4 + Z.to_nat (4 * 2^mtl))%nat)
      by (unfold DTABLE_BYTES, DT_BYTES; clear - PM; lia).
    assert (JD2 : rw_cells bsegs m DT [CB 4 (firstn 4 jdt); CB (Z.to_nat (4 * 2^mtl)) (skipn 4 jdt)]).
    { eapply rw_cells_cb_split with (k := 0%nat) (n := 4%nat); [exact JD| |].
      all: rewrite SZN; assert (XP : (0 < Z.to_nat (4 * 2^mtl))%nat) by (clear - PM; lia);
        destruct (Z.to_nat (4 * 2^mtl)) as [|X'] eqn:EX; [exfalso; lia| reflexivity]. }
    clear JD SZN.
    assert (WBC : Forall (fun iv => aclient_range CI LBh (ATOP + 4096) (fst iv) (snd iv - fst iv))
                    [(DT, DT + 4); (SP - 128 - 16, SP - 128)]).
    { constructor; [| constructor; [| constructor]].
      - right; left. exists (HB pd DT (DTABLE_BYTES mtl)).
        split; [apply in_or_app; right; cbn [In]; right; left; reflexivity|]. cbn. lia.
      - left; left. cbn [fst snd]. pw2. }
    assert (WBA : appW [(DT, DT + 4); (SP - 128 - 16, SP - 128)]).
    { unfold appW. apply Forall_cons; [|apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd].
      - unfold KLOW, KHIGH in *. destruct BR1 as [[? ?]|[? ?]]; [left|right]; lia.
      - right. unfold KHIGH in *. pw2. }
    pose proof (munch_refl [(DT, DT + 4); (SP - 128 - 16, SP - 128)] m) as MU0.
    pose proof (wmono_refl bsegs m) as WM0.
    assert (DTOP : D + rest <= ATOP).
    { destruct PAYL as [[E1 E2]|(p0 & IN0 & _)].
      - rewrite E1 in RESTR. cbn in RESTR. unfold AEMPTY in E2. unfold ATOP_MIN in *. lia.
      - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH ltac:(apply in_or_app; right; right; right; right; exact IN0)) as (_ & _ & BB).
        cbn [ab_addr ab_size] in BB. lia. }
    assert (LEN : (Z.to_nat rest <= length (map (Z_to_bv 8) pl))%nat)
      by (rewrite length_map; change (zlen pl) with (Z.of_nat (length pl)) in RESTR; lia).
    pose proof (bytes_at_firstnF m D (map (Z_to_bv 8) pl) (Z.to_nat rest) BY LEN) as BYS.
    rewrite firstn_map in BYS. clear BY.
    assert (BYU : forall m1, munch [(DT, DT + 4); (SP - 128 - 16, SP - 128)] m m1 -> bytes_at bsegs m1 D (map (Z_to_bv 8) src)).
    { intros m1 MU. eapply bytes_at_transport; [exact BYS| exact MU|]. rewrite length_map.
      replace (Z.of_nat (length src)) with rest by (pose proof src_len as SL; change (zlen src) with (Z.of_nat (length src)) in SL; lia).
      cbn [disjoint_from]. repeat (split; [first [lia | pw2]|]); exact I. }
    clear BYS. unfold PRODUCER_SIZE in SEP5.
    unfold prod_atA in *.
    zstep.
    assert (AH1 : AHEAP AI L RNG st LBh m0) by (eapply (AI_frame AI); [exact AH| exact MU0| exact WM0| exact WBC]).
    destruct (AI_block AI _ _ _ _ _ pP P PRODUCER_SIZE AH1 ltac:(apply in_or_app; right; cbn [In]; right; right; left; reflexivity))
      as (NBP & (BP1 & BP2 & BP3 & BP4) & RPA & RPS & BSP & _).
    unfold ablk, AIMG_HI, KLS in BP1.
    pose proof (fse_rt_of_aheap AI _ _ _ _ _ AH1) as (RTG & _ & _ & RTS & _).
    assert (P8 : P mod 8 = 0) by (clear - BP4; Z.div_mod_to_equations; lia).
    pose proof (ablock_unpoisoned m0 P PRODUCER_SIZE BSP P8 ltac:(lia) ltac:(unfold PRODUCER_SIZE; lia) ltac:(lia)) as UNPP.
    pose proof (ABLK (HB pP P PRODUCER_SIZE) ltac:(apply in_or_app; right; cbn [In]; right; right; left; reflexivity)) as ABP.
    cbn [ab_addr ab_size] in ABP. unfold PRODUCER_SIZE in ABP, UNPP, RPA, RPS, BP3.
    pose proof prod_rem_proofA as PREM. unfold prod_rem_stmtA, APROD_REM in PREM.
    zstep. zstep.
    call (PREM RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP - 128) P D rest lo).
    all: try first [ (unfold prod_atA; assumption) | assumption | reflexivity | exact RI | (unfold KHIGH; lia) | pw2
                   | (unfold HUF_RDT_STACK_A in GD; lia)
                   | (eapply rng_sub; [exact RSTK| lia| lia])
                   | (replace 2 with (shlen (16 + 7)) by reflexivity; exact RPS) ].
    clear PREM AH1 RTG RTS UNPP.
    match goal with MU : munch _ m ?mc |- _ => rename mc into m2 end.
    assert (AH2 : AHEAP AI L RNG st LBh m2) by (eapply (AI_frame AI); [exact AH| exact MU0| exact WM0| exact WBC]).
    assert (HBM2 : hinv_bm m2) by (eapply hinv_bm_munch; [exact HBM| exact MU0| exact WBA]).
 zstep. zstep. zstep.
    assert (SPR : 0 <= SP - 128 < 2^64) by pw2.
    assert (RC2 : rclean m2 rstk) by (eapply rclean_transport; [exact RC| exact MU0| exact WM0| exact WBA]).
    assert (INW : In (HB pw W 8704) LBh) by (apply in_or_app; right; cbn [In]; left; reflexivity).
    assert (INT : In (HB pd DT (DTABLE_BYTES mtl)) LBh) by (apply in_or_app; right; cbn [In]; right; left; reflexivity).
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH2 INW) as (_ & _ & WB). cbn [ab_addr ab_size] in WB.
    pose proof (ABLK _ INW) as ABW. pose proof (ABLK _ INT) as ABT. cbn [ab_addr ab_size] in ABW, ABT.
    match goal with H : rw_cells _ m2 DT (C4 ?v :: _) |- _ =>
      replace v with (Z_to_bv 64 (mtl * 16777217)) in H by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia) end.
    lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?fa ?fb)] => remember (Z.lor fa fb) as flg eqn:EFL end.
    assert (FLB : 0 <= flg < 64).
    { rewrite EFL. rewrite !snez01A by lia. clear - F1 F2 F3 F4 F5.
      assert (C1 : f1 = 0 \/ f1 = 1) by lia. assert (C2 : f2 = 0 \/ f2 = 1) by lia. assert (C3 : f3 = 0 \/ f3 = 1) by lia.
      assert (C4 : f4 = 0 \/ f4 = 1) by lia. assert (C5 : f5 = 0 \/ f5 = 1) by lia.
      destruct C1 as [->| ->]; destruct C2 as [->| ->]; destruct C3 as [->| ->]; destruct C4 as [->| ->]; destruct C5 as [->| ->];
        (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity). }
    Local Ltac uprdt := repeat (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?n) _ _ _ _) =>
      let b := eval vm_compute in (orb (Z.eqb n AHUF_RDT_X1) (Z.eqb n AHUF_RDT_X2)) in
      lazymatch b with false => zstep end end).
    Local Ltac upj1 := repeat (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?n) _ _ _ _) =>
      let b := eval vm_compute in (Z.eqb n PC_HC_JOIN1) in
      lazymatch b with false => zstep end end).
    if_cases K4; zify_cond K4.
    all: uprdt.
    all: eapply evtF_cut; [ first [
        eapply (RDT1 L RNG _ (Z_to_bv 64 (SP - 128)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                FR fc m2 st LBh DT W D mtl flg pd pw src _ lo rstk)
      | eapply (RDT2 L RNG _ (Z_to_bv 64 (SP - 128)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                FR fc m2 st LBh DT W D mtl flg pd pw src _ lo rstk) ] | ].
    all: try first [ dside | exact AH2 | exact HBM2 | exact RC2 | exact INW | exact INT | exact (BYU _ MU0)
                   | (rewrite ?unsigned_lit by exact SPR; unfold HUF_RDT_STACK_A2, AHARNESS_STACK in *; lia)
                   | (lazymatch goal with |- rw_cells _ _ DT _ => eassumption end) ].
    all: intros ms' PO; destruct PO as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & r & m3
                                        & E & MI3 & ST3 & MG3 & AH3 & R3 & DT3);
      subst ms'; rewrite ?unsigned_lit in ST3, MG3 by exact SPR; retlit.
    all: upj1.
    all: assert (RC3 : rclean m3 rstk) by (eapply rclean_magreeA; [exact RC2| exact MG3| | exact RRLO]; intros a Ha; split;
           [apply shad_stack_client; exact Ha | split; [exact (shad_not_in_blk a DT _ Ha ABT) | exact (shad_not_in_blk a W _ Ha ABW)]]).
    all: assert (BY3 : bytes_at bsegs m3 D (map (Z_to_bv 8) src))
           by (eapply bytes_at_magree; [exact MG3| exact (BYU _ MU0)|]; rewrite length_map; intros a Ha;
               pose proof src_len as SL; change (zlen src) with (Z.of_nat (length src)) in SL;
               assert (RP : 0 < rest) by lia; destruct (SRCIN RP) as (p0 & A0 & n0 & IN0 & L0 & H0);
               split; [eapply cl_block; [exact IN0| cbn [ab_addr ab_size]; lia] | split; lia]).
    all: assert (CS3 : rw_cells bsegs m3 SPV [C8 (Z_to_bv 64 streams); C8 (Z_to_bv 64 ASHOFF); C8 (Z_to_bv 64 symbols)])
           by (eapply rw_cells_magree; [exact MG3| eassumption|]; cbn [cells_size csize]; intros a Ha;
               split; [apply cl_stack; lia | split; lia]).
    all: assert (MGF : magree bsegs (aclient_addr CI LB0 SPV) m m3)
           by (eapply magree_trans;
               [ eapply munch_magreeA; [exact MU0| exact WM0| ]
               | refine (mg_lib _ _ _ (fun a Ha => conj (proj1 (OWN a Ha)) (proj1 (proj2 (OWN a Ha)))) _); exact MG3 ];
               intros a Ha; cbn [outside]; split; [| split; [| exact I]];
               [ intro HX; apply (proj1 (OWN a Ha)); lia
               | intro HX; eapply (stack_not_client CI LB0 (SP - 128) (SP - 128 - 16) a);
                 [ exact (AI_aci_img AI) | exact (AI_aci_lo AI)
                 | intros b Hb; apply ABLK; apply in_or_app; right; right; right; right; exact Hb
                 | pw2 | lia | exact Ha ] ]).
    all: eapply (pC2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m3 r flg rstk).
    all: first [ assumption | exact FLB | exact RC3 | exact MGF | exact BY3 | exact CS3 ].
Qed.
End PhaseC.
End CANSEC1.

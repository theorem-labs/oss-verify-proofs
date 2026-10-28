(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_ax2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import Stdio_kit AF_huf_tbl_iface2 AF_huf_bitd.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_ax2g () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax24AX2MC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC56Stdlib6ZArith6BinInt1Z6shiftrK4ELinuxProcessSemantics5Riscv5Instr5instr01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_luiC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5b_luiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm1C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit;brute_rangeC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm2C5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm3C56Stdlib6ZArith6BinInt1Z4lxorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit3nsmC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_aC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_bC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_cK4ELinuxProcessSemantics5Riscv5Instr5instr0BC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_mulC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5m_mulC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_dK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z;log2_nonnegC56Stdlib6ZArith6BinInt1Z<log2_le_monoK47Corelib4Init5Logic3and01K4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwK47Corelib4Init5Logic2or01C5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2f9ax2_setupc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2g;ax2_addiw41c5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2g9ax2_slli3C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8all_fromC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula03C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5aluop09I47Corelib4Init5Logic4True00K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop03I47Corelib4Init5Logic2ex00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax27ax2_unpC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax2=ax2_sp_boundsC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax28ax2_outbI47Corelib4Init5Logic2or00C46Stdlib5Lists4List:length_mapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC47Corelib4Init9Datatypes3appI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk05C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6all_roC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01C5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03C5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC47Corelib4Init5Peano2ltC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry04K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6rv_chkC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C47Corelib4Init9Datatypes4negbC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C46Stdlib5Lists4List6filterC5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26erangeC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax27ax2_epiC56Stdlib6ZArith6BinInt1Z7eqb_neqc5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2g9ax2_sjoinC56Stdlib5Arith8PeanoNat3Nat3ltbC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06C5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK46Stdlib9micromega5Tauto8GFormula06C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo9zk_img_okK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zur_ok_blkC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201K46Stdlib5Lists4List7Forall202C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC47Corelib5Lists7ListDef3nthK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01C5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxl_execC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9rv_chk_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk5rv_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk>kxl_know_finalC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_erange_evC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFLC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init9Datatypes3nat00I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00K4ELinuxProcessSemantics5Riscv5Instr5aluop05I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXI46Stdlib5Lists4List6Exists00K47Corelib4Init5Logic4True01I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Section AX2G.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr) (SBL SBH : Z).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -64).
  Notation n := (zlen src).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis HOUT : (DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB).
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  (* [comment removed for export] *)
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl.
  (* [comment removed for export] *)
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis NSM : 1 <= n < 2^26.
  Hypothesis S16 : 16 <= SS.
  Hypothesis SBB : SBL <= SS /\ SS + n <= SBH.
  Hypothesis SBA : ablk SBL SBH /\ SBL mod 8 = 0.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  (* [comment removed for export] *)
  Hypothesis DJ1 : KXGoM.apart DST dcap DT DTL.
  Hypothesis DJ2 : KXGoM.apart DST dcap SS n.
  Hypothesis DJ3 : KXGoM.apart SS n DT DTL.
  (* [comment removed for export] *)
  Hypothesis UDT : unpoisoned m0 DT (DT + DTL).
  Hypothesis UDB : unpoisoned m0 DST (DST + dcap).
  Hypothesis USB : unpoisoned m0 SBL SBH.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WDT : rng RNG DT DTL.
  Hypothesis WSB : rng RNG SBL (SBH - SBL).
  Hypothesis WDTS : rng RNG (shad DT) (shlen (DTL + 7)).
  Hypothesis WSBS : rng RNG (shad SBL) (shlen (SBH - SBL + 7)).
  Hypothesis WDB : 0 < dcap -> rng RNG DST dcap.
  Hypothesis WDBS : 0 < dcap -> rng RNG (shad DST) (shlen (dcap + 7)).

  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).

  Notation A2 l := (l AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      pdt SBL SBH AH HDT HOUT LOA LOS SPT SP16 TOK ECB LCB MTL TLM DC NSM S16 SBB SBA BYS DJ1 DJ2 DJ3 UDT UDB USB
                      WSK WIM WDT WSB WDTS WSBS WDB WDBS) (only parsing).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Notation G2 l := (l AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs) (only parsing).

  Ltac e2_walk_to p :=
    repeat (lazymatch goal with
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                let b := eval vm_compute in c in change c with b; cbv iota
            | |- _ => zstep
            end).

  Notation ST76 mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 (AHUF_DX2_1X + 76)) (Z_to_bv 64 (SP + -112)) gp tp x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST)
             x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 DT) (Z_to_bv 64 (2^31 - 2^15)) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        FR (Z_to_bv 64 (AHUF_DX2_1X + 76)) fc None mm (seg_rom bsegs)) (only parsing).

  Ltac e2_land K :=
    repeat match type of K with context [Z.land ?x ?c] =>
      is_Zlit c;
      let k := eval vm_compute in (Z.log2 (c + 1)) in
      let ok := eval vm_compute in (Z.eqb (2 ^ k) (c + 1)) in
      lazymatch ok with true =>
        replace (Z.land x c) with (x mod 2 ^ k) in K by (change c with (Z.ones k); symmetry; apply Z.land_ones; lia)
      end
    end.
  Ltac e2_zk K :=
    rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in K; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in K; fold_lit_ux_in K; zsimp_in K;
    repeat match type of K with
      | context [bv_unsigned (sxb (Z_to_bv 8 ?z))] =>
          is_Zlit z; let v := eval vm_compute in (bv_unsigned (sxb (Z_to_bv 8 z))) in
          change (bv_unsigned (sxb (Z_to_bv 8 z))) with v in K
      | context [bv_unsigned (Z_to_bv ?w ?z)] =>
          is_Zlit z; let v := eval vm_compute in (bv_unsigned (Z_to_bv w z)) in change (bv_unsigned (Z_to_bv w z)) with v in K
      end;
    try (rewrite ?Z_to_bv_unsigned in K); try (unfold bv_wrap, bv_modulus in K); cbn [Z.of_N] in K; e2_land K;
    repeat (first [ rewrite negb_true_iff in K | rewrite negb_false_iff in K | rewrite andb_true_iff in K
                  | rewrite andb_false_iff in K | rewrite orb_true_iff in K | rewrite orb_false_iff in K
                  | rewrite Z.ltb_lt in K | rewrite Z.ltb_ge in K | rewrite Z.leb_le in K | rewrite Z.leb_gt in K
                  | rewrite Z.eqb_eq in K | rewrite Z.eqb_neq in K ]).
  Ltac e2_prune K := try (e2_zk K); try (exfalso; first [lia | (Z.div_mod_to_equations; lia)]).

  Ltac e2_pw1 :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        let K := fresh "K" in destruct c eqn:K; cbv iota; e2_prune K
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?e) _ _ _ _) =>
        is_Zlit e;
        let o := eval vm_compute in (e - AHUF_DX2_1X) in
        lazymatch o with
        | 200 => fail | 2052 => fail | 5288 => fail | 5328 => fail
        | _ => zstep end
    end.
  Ltac e2_pwn k := lazymatch k with O => idtac | S ?j => tryif e2_pw1 then e2_pwn j else idtac end.
  Ltac e2_pw := e2_pwn 150%nat.

  Notation XF2 := (AX2F ra sp s0 s1 s2 s3 s4 s5 s6 m0 DST dcap SS DT lo src cbs).
  Notation BD2 := (ax2_bd sp SS).

  Ltac e2_res H :=
    repeat lazymatch type of H with
      | bind ?m _ = _ => let E := fresh "E" in destruct m eqn:E; cbn [bind] in H; try discriminate H
      | (if ?c then _ else _) = _ => let E := fresh "E" in destruct c eqn:E; try discriminate H
    end.

  Lemma e2_load_byte : forall bs i z, Forall (fun c => 0 <= c < 256) bs -> load bs i = Ok z -> 0 <= z < 256.
  Proof.
    intros bs i z BY HL. unfold load in HL. destruct (_ && _) eqn:C; [| discriminate HL]. injection HL as <-.
    apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. unfold FseNCount.Zlength in C2.
    unfold Znth. apply (proj1 (Forall_nth _ _) BY). lia.
  Qed.

  Lemma e2_hb : forall z h, highbit32 z = Ok h -> 0 <= z < 256 -> (z =? 0) = false -> 0 <= h <= 7.
  Proof.
    intros z h HH Z1 Z2. unfold highbit32 in HH. destruct (_ && _); [| discriminate HH]. injection HH as <-.
    apply Z.eqb_neq in Z2. split; [apply Z.log2_nonneg |].
    change 7 with (Z.log2 255). apply Z.log2_le_mono. lia.
  Qed.

  Lemma e2_init_ok : forall bs d, Forall (fun c => 0 <= c < 256) bs -> init_dstream bs = Ok d ->
    (bd_ptr d = 0 \/ (8 <= zlen bs /\ bd_ptr d = zlen bs - 8)) /\ 1 <= bd_bits d <= 64 /\ bd_zero d = false.
  Proof.
    intros bs d BY H. unfold init_dstream in H. cbv beta zeta in H. e2_res H.
    all: injection H as <-; cbn [bd_ptr bd_bits bd_zero].
    all: repeat match goal with
         | E : (_ <? _) = true |- _ => apply Z.ltb_lt in E
         | E : (_ <? _) = false |- _ => apply Z.ltb_ge in E
         | E : (_ <=? _) = true |- _ => apply Z.leb_le in E
         | E : (_ <=? _) = false |- _ => apply Z.leb_gt in E
         end.
    all: match goal with E : highbit32 ?z = Ok ?h, Z0 : (?z =? 0) = false, LZ : load _ _ = Ok ?z |- _ =>
           pose proof (e2_hb _ _ E (e2_load_byte _ _ _ BY LZ) Z0) end.
    all: unfold FseNCount.Zlength in *; split; [lia | split; [lia | reflexivity]].
  Qed.

  Lemma e2_init_err : forall bs e, init_dstream bs = Err e -> 1 <= e <= 119.
  Proof.
    intros bs e H. unfold init_dstream in H. cbv beta zeta in H. e2_res H.
    all: first
      [ injection H as <-; match goal with |- 1 <= ?c <= 119 => let v := eval cbv in c in change c with v end; lia
      | exfalso; match goal with E : _ = Err _ |- _ =>
          unfold add_byte, load, readLE64, highbit32 in E; cbv beta zeta in E;
          repeat (cbn [bind] in E; lazymatch type of E with context [if ?c then _ else _] => destruct c end);
          discriminate E end ].
  Qed.

  Lemma e2_dbuf : exists buf, u8arr bsegs m0 DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap.
  Proof using All.
    pose proof (A2 ax2_outb) as OB.
    destruct HOUT as [[D0 C0] | [pb HPB]].
    - exists []. subst DST dcap. unfold u8arr, bytes_at, wr_at. cbn [map length Z.of_nat].
      repeat split; try lia; intros; lia.
    - pose proof (AI_block AI L RNG st LB m0 pb DST dcap AH HPB) as (BN & _ & _ & _ & _ & WR & _).
      assert (DLO : AIMG_HI <= DST) by (destruct OB as [[D0 C0] | [(C1 & D1 & D2) | (C1 & D1 & D2)]]; unfold AIMG_HI in *; lia).
      destruct (rw_cells_of_wr_at bsegs m0 DST dcap WR (no_image_asan DST (DST + dcap) ltac:(unfold AIMG_HI in *; lia)) ltac:(lia))
        as (bs & LBS & RWC).
      pose proof (u8arr_of_rw_cells bsegs m0 DST _ bs RWC) as U.
      exists (map bv_unsigned bs). rewrite map_map.
      assert (EM : map (fun x => Z_to_bv 8 (bv_unsigned x)) bs = bs).
      { clear. induction bs as [|x bs IH]; [reflexivity |]. cbn [map]. rewrite IH. f_equal.
        apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. }
      rewrite EM. split; [exact U |]. rewrite length_map, LBS. lia.
  Qed.

  Lemma e2_hdr : forall a b, 1 <= a <= 12 -> 0 <= b <= 12 ->
    zext 64 (bv_extract 0 32 (le_bytes_to_word [Z_to_bv 8 a; Z_to_bv 8 1; Z_to_bv 8 b; Z_to_bv 8 a]))
    = Z_to_bv 64 (a + 256 + 2 ^ 16 * (b + 256 * a)).
  Proof.
    intros a b HA HB.
    assert (IA : In a [1;2;3;4;5;6;7;8;9;10;11;12]) by (cbn; lia).
    assert (IB : In b [0;1;2;3;4;5;6;7;8;9;10;11;12]) by (cbn; lia).
    clear HA HB. cbn [In] in IA, IB.
    repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; try contradiction; subst a b;
      apply bv_eq; vm_compute; reflexivity.
  Time Qed.

  Lemma e2_hdr16 : forall a b, 0 <= a <= 255 -> 0 <= b <= 255 -> Z.shiftr (a + 256 + 2 ^ 16 * (b + 256 * a)) 16 = b + 256 * a.
  Proof.
    intros a b HA HB. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. Z.div_mod_to_equations. lia.
  Time Qed.

  Lemma e2_err : forall mm csB e (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    XF2 mm -> rw_cells bsegs mm (SP + -104) csB -> cells_size csB = 40%nat -> 1 <= e <= 119 ->
    evtF bsegs RNG POST (ST76 mm x5 x6 x7 (Z_to_bv 64 (- e)) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof using All.
    intros mm csB e x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 XM FRD CS E1.
    let v := eval vm_compute in (AHUF_DX2_1X + 76) in change (AHUF_DX2_1X + 76) with v.
    e2_pw.
    all: eapply (A2 ax2_ret); [exact XM | exact FRD | exact CS].
  Time Qed.

  Ltac e2_close G200 G52 XM0 BDM BC PI :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?e) _ _ _ _) =>
      let o := eval vm_compute in (e - AHUF_DX2_1X) in
      lazymatch o with
      | 200 =>
          unfold ax2_goal_200 in G200; eapply (G200 _ _ _ (mtl + 256));
          [exact XM0 | exact BDM | exact BC | exact PI | lia | lia]
      | 2052 =>
          unfold ax2_goal_2052 in G52;
          first
            [ eapply G52; [exact XM0 | exact BDM | exact BC | exact PI | lia]
            | let G := fresh "G" in pose proof G52 as G;
              assert (D0 : dcap = 0) by lia;
              replace (DST + dcap) with DST in G by lia;
              eapply G; [exact XM0 | exact BDM | exact BC | exact PI | lia] ]
      end
    end.

  Lemma e2_ok : forall mm cont bc pad P (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    G2 ax2_goal_200 -> G2 ax2_goal_2052 ->
    XF2 mm -> BD2 mm cont bc pad P -> 1 <= bc <= 64 -> (P = SS \/ (SS + 1 <= P /\ P + 8 <= SS + n)) ->
    bytes_at bsegs mm DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl] ->
    evtF bsegs RNG POST (ST76 mm x5 x6 x7 (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof using All.
    intros mm cont bc pad P x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 G200 G52 XM BDM BC PI HD.
    pose proof XM as XM0. destruct XM as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    pose proof (A2 ax2_sp_bounds) as SB. unfold HUF_DEC_STACK_A in LOS.
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (A2 ax2_unp' mm MU) as (UDT' & UDB' & USB').
    pose proof TOK as (TL & _ & _). unfold HUF_TABLELOG_MAX in TL.
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR.
    assert (DSP : 0 <= DST /\ DST + dcap + 4096 <= SP - 2352 /\ (1 <= dcap -> 4096 <= DST))
      by (pose proof (A2 ax2_outb) as OB; unfold AIMG_HI, KLS in *; lia).
    assert (DTL8 : 8 <= DTL) by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; pose proof (Z.pow_pos_nonneg 2 mtl); lia).
    unfold AIMG_HI in *.
    assert (RSH : ov_read_bytes bsegs mm (wa (Z.shiftr DT 3 + ASHOFF)) 1 = Some [Z_to_bv 8 0]).
    { rewrite Z.add_comm. change (ASHOFF + Z.shiftr DT 3) with (shad DT).
      eapply unpoisoned_full_rd; [exact UDT' | lia | rewrite shad_div; Z.div_mod_to_equations; lia]. }
    assert (RSR : rng RNG (Z.shiftr DT 3 + ASHOFF) 1).
    { eapply rng_sub; [exact WDTS | rewrite shad_div, Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia |].
      rewrite shad_div. unfold shlen. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
    unfold ASHOFF in RSH, RSR.
    remember [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl] as hb eqn:EHB.
    assert (RHD : ov_read_bytes bsegs mm (wa DT) 4 = Some hb).
    { pose proof (bytes_at_read bsegs mm DT _ 0 4 HD ltac:(lia) ltac:(subst hb; cbn; lia)) as R.
      rewrite Z.add_0_r in R. subst hb. exact R. }
    let v := eval vm_compute in (AHUF_DX2_1X + 76) in change (AHUF_DX2_1X + 76) with v.
    e2_pw.
    all: subst hb; rewrite (e2_hdr mtl tl) by lia; rewrite (unsigned_lit (mtl + 256 + 2 ^ 16 * (tl + 256 * mtl))) by lia;
      rewrite (e2_hdr16 mtl tl) by lia.
    all: e2_close G200 G52 XM0 BDM BC PI.
  Time Qed.

  Lemma e2_post : forall m2 ret (w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 : word),
    G2 ax2_goal_200 -> G2 ax2_goal_2052 ->
    XF2 m2 -> bytes_at bsegs m2 DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl] ->
    match init_dstream src with
    | Ok d => ret = n /\ bd_zero d = false /\ exists jp, rw_cells bsegs m2 (SP + -104) (bitdz_cellsA SS d jp)
    | Err e => ret = - e /\ exists j', rw_cells bsegs m2 (SP + -104) [CB 40 j']
    | Ub | NoFuel => False
    end ->
    evtF bsegs RNG POST (ST76 m2 w5 w6 w7 (Z_to_bv 64 ret) w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31).
  Proof using All.
    intros m2 ret w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 G200 G52 XM HD RES.
    destruct (init_dstream src) as [d | e | |] eqn:ID; [| | contradiction | contradiction].
    - destruct RES as (Eret & BZ & jp & RW). subst ret.
      destruct (e2_init_ok src d BYS ID) as (PT & BB & _).
      unfold bitdz_cellsA in RW. rewrite BZ in RW.
      eapply (e2_ok m2 (Z_to_bv 64 (bd_cont d)) (bd_bits d) jp (SS + bd_ptr d)); [exact G200 | exact G52 | exact XM | exact RW | lia | lia | exact HD].
    - destruct RES as (Eret & j' & RW). subst ret.
      exact (e2_err m2 [CB 40 j'] e w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 XM RW eq_refl (e2_init_err src e ID)).
  Time Qed.

  Lemma e2_call : forall (rstk : region) m1 j g (y5 y6 y7 x10 x11 x12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    G2 ax2_goal_200 -> G2 ax2_goal_2052 ->
    bytes_at bsegs m0 SS (map (Z_to_bv 8) src) ->
    bytes_at bsegs m0 DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl] ->
    bytes_at bsegs m0 (DT + 4) cbs ->
    rclean m0 rstk -> r_lo rstk <= lo -> SP <= r_hi rstk -> rrng RNG rstk ->
    stk bsegs m1 lo (SP + -112) -> rw_cells bsegs m1 (SP + -112) [CB 8 g] -> rw_cells bsegs m1 (SP + -104) [CB 40 j] ->
    rw_cells bsegs m1 (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    mem_inv bsegs m1 -> artcells m1 -> munch [(SP + -2352, SP)] m0 m1 -> wmono bsegs m0 m1 ->
    x10 = Z_to_bv 64 (SP + -104) -> x11 = Z_to_bv 64 SS -> x12 = Z_to_bv 64 n ->
    evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 (AHUF_DX2_1X + 76)) (Z_to_bv 64 (SP + -112)) gp tp y5 y6 y7
                               (Z_to_bv 64 dcap) (Z_to_bv 64 DST) x10 x11 x12 y13 y14 y15 y16 y17
                               (Z_to_bv 64 DT) (Z_to_bv 64 (2^31 - 2^15)) s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                            FR (Z_to_bv 64 ABIT_INIT_D) fc None m1 (seg_rom bsegs)).
  Proof using All.
    intros rstk m1 j g y5 y6 y7 x10 x11 x12 y13 y14 y15 y16 y17 y28 y29 y30 y31 G200 G52 BS0 HD0 CB0
      RCL RLO RHI RRS STK GAP FRB FRC MI ART MU WM E10 E11 E12.
    subst x10 x11 x12.
    pose proof RCL as (SH0 & _). pose proof (shclean_hull _ _ _ _ _ SH0) as (H1 & H2 & H3 & H4 & H5 & H6).
    pose proof (A2 ax2_sp_bounds) as SB. pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (A2 ax2_outb) as OB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof LOS as LOS'. unfold HUF_DEC_STACK_A in LOS'.
    pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    unfold AIMG_HI, KLS in *.
    assert (DSP : 0 <= DST /\ DST + dcap + 4096 <= SP - 2352) by lia.
    pose proof TOK as (TL & _ & _). unfold HUF_TABLELOG_MAX in TL.
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia).
    assert (DTL8 : 8 <= DTL) by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; pose proof (Z.pow_pos_nonneg 2 mtl); lia).
    assert (BS1 : bytes_at bsegs m1 SS (map (Z_to_bv 8) src)).
    { eapply bytes_at_transport; [exact BS0 | exact MU |]. cbn [disjoint_from]. rewrite length_map. lia. }
    assert (US1 : unpoisoned m1 SS (SS + n)).
    { eapply unpoisoned_munch; [eapply unpoisoned_sub; [exact USB | lia | lia] | exact MU |].
      cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    let v := eval vm_compute in (AHUF_DX2_1X + 76) in change (AHUF_DX2_1X + 76) with v.
    remember (Z_to_bv 64 (SP + -112)) as sp1 eqn:Esp1.
    assert (SP1 : bv_unsigned sp1 = SP + -112) by (subst sp1; apply unsigned_lit; lia).
    pose proof bit_init_proofAD as BI. unfold bit_init_stmtA in BI.
    eapply evtF_cut.
    { eapply (BI RNG) with (D := SP + -104) (S := SS) (bs := src) (lo := lo) (RLO := r_rlo rstk) (RHI := r_rhi rstk).
      all: rewrite ?SP1.
      all: lazymatch goal with
        | |- rw_cells _ _ _ [CB 40 _] => exact FRB
        | |- _ mod 8 = 0 => Z.div_mod_to_equations; lia
        | |- bytes_at _ _ _ _ => exact BS1
        | |- Forall _ _ => exact BYS
        | |- stk _ _ _ _ => exact STK
        | |- mem_inv _ _ => exact MI
        | |- artcells _ => exact ART
        | |- shclean _ _ _ _ _ =>
            eapply shclean_transport; [eapply shclean_sub; [exact SH0 | lia | lia | lia] | exact MU | exact WM | | lia];
            cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia
        | |- unpoisoned _ _ _ => exact US1
        | |- _ -> ablk _ _ /\ _ =>
            intros _; split; [eapply ablk_sub; [exact (proj1 SBA) | lia | lia] | lia]
        | |- _ -> rng _ _ _ /\ _ =>
            intros _; split;
            [ eapply rng_sub; [exact WSB | lia | lia]
            | eapply rng_sub; [exact WSBS | rewrite !shad_div; Z.div_mod_to_equations; lia |];
              rewrite !shad_div, nshad_div; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8;
              pose proof (proj2 SBA); Z.div_mod_to_equations; lia ]
        | |- rng _ (shad (r_rlo _)) _ => unfold rrng in RRS; exact RRS
        | |- rng _ (shad _) _ =>
            unfold rrng in RRS; eapply rng_sub; [exact RRS | |]; rewrite !shad_div; Z.div_mod_to_equations; lia
        | |- rng_aimg _ => exact WIM
        | |- rng _ _ _ => eapply rng_sub; [exact WSK | lia | lia]
        | |- _ = Z_to_bv 64 _ => reflexivity
        | |- _ <= _ => try unfold ABIT_INIT_STACK; lia
      end. }
    intros ms' PO. unfold bit_init_postA in PO.
    destruct PO as (w5 & w6 & w7 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & ret & m2
                    & E & MUc & WMc & MI2 & STK2 & BYS2 & RES).
    subst ms'.
    unfold ABIT_INIT_STACK in MUc. rewrite SP1 in MUc, STK2.
    lazymatch type of MUc with munch _ ?m1 _ => transport_after_call bsegs m1 m2 MUc WMc end.
    clear MUc WMc.
    lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
    subst sp1.
    assert (XM : XF2 m2).
    { unfold AX2F. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
      - destruct e2_dbuf as (buf & U & LBF). exists buf. split; [| exact LBF].
        eapply u8arr_transport; [exact U | exact MU | exact WM |]. cbn [disjoint_from]. rewrite length_map, LBF. lia.
      - exact BYS2.
      - eapply bytes_at_transport; [exact CB0 | exact MU |]. cbn [disjoint_from]. rewrite LCB. lia.
      - exact STK2.
      - exists g. exact GAP.
      - exact FRC.
      - exact MI2.
      - eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in *. tauto.
      - exact WM. }
    assert (HD2 : bytes_at bsegs m2 DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl]).
    { eapply bytes_at_transport; [exact HD0 | exact MU |]. cbn [disjoint_from length Z.of_nat]. lia. }
    let v := eval vm_compute in (AHUF_DX2_1X + 76) in change v with (AHUF_DX2_1X + 76).
    exact (e2_post m2 ret w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 G200 G52 XM HD2 RES).
  Time Qed.

  Lemma ax2_entry_ok : G2 ax2_goal_200 -> G2 ax2_goal_2052 ->
    forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (rstk : region),
    bytes_at bsegs m0 SS (map (Z_to_bv 8) src) ->
    bytes_at bsegs m0 DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl] ->
    bytes_at bsegs m0 (DT + 4) cbs ->
    stk bsegs m0 lo SP -> mem_inv bsegs m0 ->
    rclean m0 rstk -> r_lo rstk <= lo -> SP <= r_hi rstk -> ATOP <= r_rlo rstk ->
    rng_aimg_sh RNG -> rrng RNG rstk ->
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SS) (Z_to_bv 64 n)
                               (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            FR (Z_to_bv 64 AHUF_DX2_1X) fc None m0 (seg_rom bsegs)).
  Proof using All.
    intros G200 G52 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 rstk BS0 HD0 CB0 STK MI RCL RLO RHI RRL WIS RRS.
    pose proof (conj BS0 (conj HD0 CB0)) as KEEP. clear BS0 HD0 CB0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof LOS as LOS'. unfold HUF_DEC_STACK_A in LOS'.
    pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (AI_rtcells AI L RNG st LB m0 AH) as ART. unfold artcells in ART.
    repeat match type of ART with _ /\ _ => let H := fresh "A" in destruct ART as [H ART] end.
    pose proof (munch_refl [(SP + -2352, SP)] m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
    carve_frame 64%nat STK.
    lazymatch goal with F : rw_cells bsegs _ (bv_unsigned _ + -64) [CB 64 _] |- _ =>
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8;8;8;8]%nat) in F; [| reflexivity]; cbn [mk_CB_cells app] in F end.
    carve_frame 40%nat STK. carve_frame 8%nat STK.
    unfold AHUF_DX2_1X.
    let p := eval cbv in ABIT_INIT_D in e2_walk_to p.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (ART1 : artcells m1) by (unfold artcells; repeat (split; [eassumption|]); eassumption) end.
    destruct KEEP as (BS0 & HD0 & CB0).
    eapply (e2_call rstk); [exact G200 | exact G52 | exact BS0 | exact HD0 | exact CB0 | exact RCL | exact RLO | exact RHI | exact RRS
      | eassumption | eassumption | eassumption | eassumption | eassumption | exact ART1 | eassumption | eassumption
      | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia]].
  Time Qed.

End AX2G.
End CANSEC1.

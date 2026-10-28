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
Ltac2 kr_t_AF_huf_ax2g2 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdK47Corelib4Init9Datatypes3nat02K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions9bv_signedC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC56Stdlib6ZArith6BinInt1Z9add_assocC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC56Stdlib6ZArith6BinInt1Z3lorC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm1C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit;brute_rangeC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm2C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit3sm3K4ELinuxProcessSemantics5Riscv5Instr5instr01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_luiC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5b_luiK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC56Stdlib6ZArith6BinInt1Z4lxorC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit3nsmK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_aC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_bC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_cC56Stdlib6ZArith6BinInt1Z3mulK4ELinuxProcessSemantics5Riscv5Instr5instr0BC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_mulC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5m_mulC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit4pc_dK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwK4ELinuxProcessSemantics5Riscv5Instr5instr03K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit7src_rd2C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK47Corelib5Lists7ListDef6Forall01K4ELinuxProcessSemantics5Riscv5Instr5instr09C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8all_fromC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop03C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax24AX2MI47Corelib4Init5Logic2ex00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax27ax2_unpC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax2=ax2_sp_boundsC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax28ax2_outbI47Corelib4Init5Logic2or00C46Stdlib5Lists4List:length_mapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC56Stdlib6ZArith6BinInt1Z6moduloC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega=RingMicromega5Psatz02C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp04C5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zur_ok_blkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC47Corelib4Init5Peano2ltC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxl_execC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6rv_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9rv_chk_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk5rv_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk>kxl_know_finalC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26erangeC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_erange_evC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_ax27ax2_epiC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z;log2_nonnegC56Stdlib6ZArith6BinInt1Z<log2_le_monoC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'K47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2f9ax2_setupc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_ax2g2:ax2_le64pcC56Stdlib5Arith8PeanoNat3Nat3ltbC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFLC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr04C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okK46Stdlib5Lists4List7Forall202K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01K46Stdlib9micromega5Tauto8GFormula07C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00K46Stdlib9micromega:ZMicromega;ZArithProof01I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXI46Stdlib5Lists4List6Exists00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Section AX2G2.
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

  Notation DW := [(SP + -56, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS6 := [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation A2 l := (l AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      pdt SBL SBH AH HDT HOUT LOA LOS SPT SP16 TOK ECB LCB MTL TLM DC NSM S16 SBB SBA BYS DJ1 DJ2 DJ3 UDT UDB USB
                      WSK WIM WDT WSB WDTS WSBS WDB WDBS) (only parsing).
  Notation AX2M' mm := (AX2M ra sp s0 s1 s2 s3 s4 s5 m0 DST dcap SS DT lo src cbs mm).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End AX2G2.
Section ZERO2.
  Variable AI : AMallocIface.
  Variable rng_fs : alayout -> footprint -> Prop.
  Notation zlen l := (Z.of_nat (length l)).

  Ltac z2_walk_to p :=
    repeat (lazymatch goal with
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                let b := eval vm_compute in c in change c with b; cbv iota
            | |- _ => zstep
            end).

  Section Z2E.
    Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
    Variables (DST dcap lo : Z).
    Notation SP := (bv_unsigned sp).
    Hypothesis AH : AHEAP AI L RNG st LB m0.
    Hypothesis LOA : ATOP + 4096 <= lo.
    Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
    Hypothesis SPT : SP + 16 < al_top L.
    Hypothesis WSK : rng RNG lo (al_top L - lo).
    Notation W1 := [(SP + -2352, SP)].
    Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
    Notation FRS8 := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

    Lemma z2_aheap : forall mm, munch W1 m0 mm -> wmono bsegs m0 mm -> AHEAP AI L RNG st LB mm.
    Proof using All.
      intros mm MU WM. unfold HUF_DEC_STACK_A in LOS.
      pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
      eapply (AI_frame AI L RNG st LB m0 mm _ AH MU WM).
      constructor; [| constructor]. cbn [fst snd]. unfold aclient_range, aclient_app_range. left. left. lia.
    Qed.

    Lemma z2_magree : forall mm, munch W1 m0 mm -> wmono bsegs m0 mm ->
      magree bsegs (fun a => aclient_addr (aci AI) LB SP a /\ ~ (DST <= a < DST + dcap)) m0 mm.
    Proof using All.
      intros mm MU WM. apply (munch_magreeA W1 m0 mm); [exact MU | exact WM |].
      intros a [CA ND]. cbn [outside]. split; [| exact I].
      pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold HUF_DEC_STACK_A in LOS.
      destruct CA as [S | [R | [B | (a' & A' & E)]]].
      - lia.
      - destruct R as (iv & IN & R1 & R2). pose proof (AI_aci_img AI iv IN) as HI. unfold ABase.AIMG_HI in HI. lia.
      - destruct B as (b & IN & B1 & B2). pose proof (AI_block_bounds AI _ _ _ _ _ b AH IN) as (BB1 & BB2 & BB3).
        unfold ABase.AIMG_HI in BB1. lia.
      - subst a. unfold shad, ASHOFF. rewrite ?Z.shiftr_div_pow2 by lia.
        assert (A'B : 0 <= a' < 2^47).
        { destruct A' as [A1 | [(iv & IN & R1 & R2) | (cls & A & k & IN & F1 & F2)]].
          - lia.
          - pose proof (AI_aci_img AI iv IN). pose proof (AI_aci_lo AI iv IN). unfold ABase.AIMG_HI in *. lia.
          - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (BB1 & BB2 & BB3). cbn [ab_addr ab_size] in BB1, BB2, BB3.
            unfold ABase.AIMG_HI in *. lia. }
        Z.div_mod_to_equations. lia.
    Qed.

    Lemma z2_ret : forall mm g (csB : list cell)
        (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
      stk bsegs mm lo (SP + -112) -> rw_cells bsegs mm (SP + -112) [CB 8 g] ->
      rw_cells bsegs mm (SP + -104) csB -> cells_size csB = 40%nat -> rw_cells bsegs mm (SP + -64) FRS8 ->
      mem_inv bsegs mm -> munch W1 m0 mm -> wmono bsegs m0 mm ->
      evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 (SP + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                                   x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31) FR (Z_to_bv 64 AX2_RET) fc None mm (seg_rom bsegs)).
    Proof using All.
      intros mm g csB x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 STK GAP FRD CS FRC MI MU WM.
      destruct (rw_cells_forget _ _ _ _ FRD) as [dj FRJ]. rewrite CS in FRJ. clear FRD CS.
      unfold HUF_DEC_STACK_A in LOS.
      pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
      pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
      unfold AX2_RET.
      repeat zstep.
      release_frame GAP STK (SP + -104).
      release_frame FRJ STK (SP + -64).
      release_frame FRC STK (bv_unsigned sp).
      apply evtF_done. unfold huf_dec_postA.
      do 16 eexists. split; [reflexivity|]. split; [exact MI|]. split; [exact STK|].
      split; [exact (z2_magree mm MU WM) | exact (z2_aheap mm MU WM)].
    Time Qed.

    Lemma z2_mid : forall mm g (csB : list cell)
        (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
      stk bsegs mm lo (SP + -112) -> rw_cells bsegs mm (SP + -112) [CB 8 g] ->
      rw_cells bsegs mm (SP + -104) csB -> cells_size csB = 40%nat -> rw_cells bsegs mm (SP + -64) FRS8 ->
      mem_inv bsegs mm -> munch W1 m0 mm -> wmono bsegs m0 mm ->
      evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 (SP + -112)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (- ZSTD_error_srcSize_wrong))
                                   x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                               FR (Z_to_bv 64 (AHUF_DX2_1X + 76)) fc None mm (seg_rom bsegs)).
    Proof using All.
      intros mm g csB x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 STK GAP FRD CS FRC MI MU WM.
      let v := eval vm_compute in (AHUF_DX2_1X + 76) in change (AHUF_DX2_1X + 76) with v.
      let p := eval cbv in AX2_RET in z2_walk_to p.
      all: eapply z2_ret; eassumption.
    Time Qed.
    Lemma z2_call : forall (SS : Z) (rstk : region) m1 j g
        (y5 y6 y7 y8 y9 x10 x11 x12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31 : word),
      SP mod 16 = 0 -> 16 <= SS -> SS <= 2^64 -> rng_aimg RNG -> rrng RNG rstk ->
      rclean m0 rstk -> r_lo rstk <= lo -> SP <= r_hi rstk ->
      stk bsegs m1 lo (SP + -112) -> rw_cells bsegs m1 (SP + -112) [CB 8 g] -> rw_cells bsegs m1 (SP + -104) [CB 40 j] ->
      rw_cells bsegs m1 (SP + -64) FRS8 -> mem_inv bsegs m1 -> artcells m1 -> munch W1 m0 m1 -> wmono bsegs m0 m1 ->
      x10 = Z_to_bv 64 (SP + -104) -> x11 = Z_to_bv 64 SS -> x12 = Z_to_bv 64 0 ->
      evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 (AHUF_DX2_1X + 76)) (Z_to_bv 64 (SP + -112)) gp tp y5 y6 y7 y8 y9 x10 x11 x12
                                   y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                               FR (Z_to_bv 64 ABIT_INIT_D) fc None m1 (seg_rom bsegs)).
    Proof using All.
      intros SS rstk m1 j g y5 y6 y7 y8 y9 x10 x11 x12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31
        SP16 S16 SSB WIM RRS RCL RLO RHI STK GAP FRB FRC MI ART MU WM E10 E11 E12.
      subst x10 x11 x12.
      pose proof RCL as (SH0 & _). pose proof (shclean_hull _ _ _ _ _ SH0) as (H1 & H2 & H3 & H4 & H5 & H6).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
      pose proof LOS as LOS'. unfold HUF_DEC_STACK_A in LOS'.
      pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
      pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
      let v := eval vm_compute in (AHUF_DX2_1X + 76) in change (AHUF_DX2_1X + 76) with v.
      remember (Z_to_bv 64 (SP + -112)) as sp1 eqn:Esp1.
      assert (SP1 : bv_unsigned sp1 = SP + -112) by (subst sp1; apply unsigned_lit; lia).
      pose proof bit_init_proofAD as BI. unfold bit_init_stmtA in BI.
      eapply evtF_cut.
      { eapply (BI RNG) with (D := SP + -104) (S := SS) (bs := []) (lo := lo) (RLO := r_rlo rstk) (RHI := r_rhi rstk).
        all: rewrite ?SP1.
        all: lazymatch goal with
          | |- rw_cells _ _ _ [CB 40 _] => eassumption
          | |- _ mod 8 = 0 => Z.div_mod_to_equations; lia
          | |- bytes_at _ _ _ _ =>
              unfold bytes_at; cbn [map length Z.of_nat]; split; [lia | split; [lia | intros i Hi; cbn in Hi; lia]]
          | |- Forall _ _ => constructor
          | |- stk _ _ _ _ => eassumption
          | |- mem_inv _ _ => eassumption
          | |- artcells _ => exact ART
          | |- shclean _ _ _ _ _ =>
              eapply shclean_transport; [eapply shclean_sub; [exact SH0 | lia | lia | lia] | exact MU | exact WM | | lia];
              cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia
          | |- rng _ (shad (r_rlo _)) _ => unfold rrng in RRS; exact RRS
          | |- rng _ (shad _) _ =>
              unfold rrng in RRS; eapply rng_sub; [exact RRS | |]; rewrite !shad_div; Z.div_mod_to_equations; lia
          | |- rng_aimg _ => exact WIM
          | |- rng _ _ _ => eapply rng_sub; [exact WSK | lia | lia]
          | |- _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia]
          | |- _ -> _ => let HZ := fresh "HZ" in intros HZ; cbn in HZ; lia
          | |- _ <= _ => try unfold ABIT_INIT_STACK; lia
          | |- _ => red; cbn [length Z.of_nat]; split; [lia | split; [lia | intros; lia]]
        end. }
      intros ms' PO. unfold bit_init_postA in PO.
      destruct PO as (w5 & w6 & w7 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & ret & m2
                      & E & MUc & WMc & MI2 & STK2 & BYS2 & RES).
      subst ms'.
      assert (EI : init_dstream [] = Err ZSTD_error_srcSize_wrong) by reflexivity. rewrite EI in RES. cbv beta iota in RES.
      destruct RES as (Eret & j' & BD2). subst ret.
      unfold ABIT_INIT_STACK in MUc. rewrite SP1 in MUc, STK2.
      lazymatch type of MUc with munch _ ?m1 _ => transport_after_call bsegs m1 m2 MUc WMc end.
      clear MUc WMc.
      lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
      subst sp1.
      eapply z2_mid; [exact STK2 | exact GAP | exact BD2 | reflexivity | exact FRC | exact MI2 | exact MU | exact WM].
    Time Qed.

  End Z2E.

  Lemma dec_1x2_zero :
      forall (L : alayout) (RNG : footprint)
             (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
             (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
             (DST dcap S DT mtl : Z) (pdt : aptr) (src : list Z) (lo : Z) (rstk : region),
      AHEAP AI L RNG st LB m ->
      (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->
      (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
      1 <= mtl <= 12 -> In (HB pdt DT (DTABLE_BYTES mtl)) LB -> x2_tabA m DT mtl ->
      ((DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB)) ->
      0 <= dcap < 2^32 ->
      bytes_at bsegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
      zlen src < 2^26 -> 16 <= S -> src_inA LB S src ->
      (DT + DTABLE_BYTES mtl <= S \/ S + zlen src <= DT) -> (DST + dcap <= S \/ S + zlen src <= DST) ->
      (DT + DTABLE_BYTES mtl <= DST \/ DST + dcap <= DT) ->
      stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HUF_DEC_STACK_A ->
      rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
      bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
      mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
      harness_invA m ->
      rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
      a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 dcap -> a2 = Z_to_bv 64 S -> a3 = Z_to_bv 64 (zlen src) -> a4 = Z_to_bv 64 DT ->
      zlen src = 0 ->
      evtF bsegs RNG (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (Z_to_bv 64 AHUF_DX2_1X) fc None m (seg_rom bsegs)).
  Proof.
    intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      FR fc m st LB DST dcap SS DT mtl pdt src lo rstk AH NFK ABL MTL HDT XT HOUT DC BYS FBY SRCL S16 SRI DJ1 DJ2 DJ3
      STK LOA LOS RCL RLO RHI RRL SPT SP16 MI TPA HINV WSK WIM WIS WFS RRS E0 E1 E2 E3 E4 N0.
    destruct src as [|c src']; [| cbn in N0; lia]. subst a0 a1 a2 a3 a4.
    clear NFK ABL MTL HDT XT HOUT DC FBY SRCL SRI DJ1 DJ2 DJ3 TPA HINV WIS WFS N0.
    destruct BYS as (BS0 & BS1 & _). cbn [map length Z.of_nat] in BS1.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof LOS as LOS'. unfold HUF_DEC_STACK_A in LOS'.
    pose proof (AI_layout AI L RNG st LB m AH) as (_ & _ & TOP & _).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (AI_rtcells AI L RNG st LB m AH) as ART. unfold artcells in ART.
    repeat match type of ART with _ /\ _ => let H := fresh "A" in destruct ART as [H ART] end.
    pose proof (munch_refl [(bv_unsigned sp + -2352, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    carve_frame 64%nat STK.
    lazymatch goal with F : rw_cells bsegs _ (bv_unsigned _ + -64) [CB 64 _] |- _ =>
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8;8;8;8]%nat) in F; [| reflexivity]; cbn [mk_CB_cells app] in F end.
    carve_frame 40%nat STK. carve_frame 8%nat STK.
    unfold AHUF_DX2_1X.
    let p := eval cbv in ABIT_INIT_D in z2_walk_to p.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (ART1 : artcells m1) by (unfold artcells; repeat (split; [eassumption|]); eassumption) end.
    eapply (z2_call L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m DST dcap lo AH LOA LOS SPT WSK SS rstk);
      [exact SP16 | exact S16 | lia | exact WIM | exact RRS | exact RCL | exact RLO | exact RHI
      | eassumption | eassumption | eassumption | eassumption | eassumption | exact ART1 | eassumption | eassumption
      | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia]].
  Time Qed.
End ZERO2.
End CANSEC1.

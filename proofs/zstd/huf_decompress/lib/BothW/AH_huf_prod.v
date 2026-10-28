(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AH_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AH_huf_prod () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8map_consK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit:swrap32_eqC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit9wrap32_eqK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod<wrap_swrap32C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z9land_diagC56Stdlib6ZArith6BinInt1Z:land_assocC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z@land_lor_distr_lC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;Z_to_bv_eqmC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C5ARocqVerifyHarness?AgentSubmission4Spec<FuzzProducer8lor_byteC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1ZAmul_pow2_bits_lowC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z6eq_decC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC56Stdlib6ZArith6BinInt1Z8lxor_lorK46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes4bool02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase>ablk_disj_bandC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow@unpoisoned_munchC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow>unpoisoned_nilC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFK47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission4Spec<FuzzProducer9draw_loopI47Corelib4Init9Datatypes3nat00C45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atI47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthK47Corelib4Init9Datatypes6option01C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib5Lists7ListDef3nthC47Corelib4Init9Datatypes:option_mapC46Stdlib5Lists4List>nth_error_nth'C46Stdlib5Lists4List=nth_error_mapC46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List6nth_InC47Corelib4Init5Logic5proj1C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod3INVK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface?prod_u32r_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_remuwK4ELinuxProcessSemantics5Riscv5Instr5instr0CC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_remuwC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic6eq_symK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame;stk_releaseC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3u32C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface8prod_atAK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas6u32_idC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prodAwrap_swrap32_landC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<wrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop08K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6shiftrC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission3Lib3Mem>bytes_at_boundC46Stdlib5Lists4List:length_mapc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod:inv_shadowC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z6eqb_eqc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod8land_m64c5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod6pl_nthC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission4LibA6ShadowBunpoisoned_full_rdC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5nshadC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow9nshad_divC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC46Stdlib9micromega;ZifyClasses:impl_morphC46Stdlib4Bool4Bool>negb_false_iffK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission4LibA6ShadowCunpoisoned_check_rdC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4svalC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:sval_rangeK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3sxbC5ARocqVerifyHarness?AgentSubmission3Lib3MemAsext_extract_byteC5ARocqVerifyHarness?AgentSubmission3Lib3Arr9u8ro_readC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr0<C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_slliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_slliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_srliwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_srliwC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC35stdpp7tactics<f_equal_helpc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod;draw_loop_0K4ELinuxProcessSemantics5Riscv5Instr5instr03c5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod@lor_swrap32_bytec5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod9lor_mod64C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit8byte_litC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow9land7_modK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission4LibA6ShadowBsigned_lit_small64C56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8sxb_svalC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith4Znat5Nat2Z8inj_succK4ELinuxProcessSemantics5Riscv5Instr5msize01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod4ASHBK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitK4ELinuxProcessSemantics5Riscv5Instr5instr02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_subwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_subwc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod:u32r_tailAc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod:u32r_loopAK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop02C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface:APROD_U32RC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface;payload_atAC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod:u32r_bodyAC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface?prod_u32r_stmtAC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface?prod_i32r_postAC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit:signed_litc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod<inv_shadow_iC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge=bv_lts_zero_rC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission4Spec<FuzzProducer;uint32RangeK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC5ARocqVerifyHarness?AgentSubmission4Spec<FuzzProducerAuint32Range_rangeC5ARocqVerifyHarness?AgentSubmission4Spec<FuzzProducer:int32RangeC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit;swrap32_eqmC5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_15C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8evtF_cutC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit<unsigned_negC56Stdlib6ZArith6BinInt1Z6leb_gtC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_monoC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface:APROD_I32Rc5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_prod:i32r_bodyAC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface?prod_i32r_stmtAC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface>prod_rem_postAC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface>prod_rem_stmtAC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface9APROD_REMC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_ifaceAhuf_iserror_postAC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_sltiuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9alu_sltiuC56Stdlib6ZArith6BinInt1Z3b2zC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z8leb_specC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;v_sltiu_b2zC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<AHUF_ISERRORK4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_ifaceAhuf_iserror_stmtA".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.


(* [comment removed for export] *)
Lemma wrap_swrap32 : forall r, 0 <= r < 2^32 -> bv_wrap 32 (bv_swrap 32 r mod 18446744073709551616) = r.
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_prod ()) [] "h02Hah14__x1h24__x2h34__x3h44__x4h54__x5h64__x6h74__x7h81zh91Hh:2H0h;2H1h<3H10h=3H11h>3H12h?3H13h@2H2hA2H3hB2H4hC2H5hD2H6hE2H7hF2H8hG2H9hH2HrhI7__arithhJ4__ffhK7__sat14hL7__sat15hM8__varmaphN5__withO1qhP2q0hQ2q1hR1rhS2r0hT2r1hU2r2p;1p;2p;3p;4p;6p;7p;8p10000p4p7210g000\R0p4p710R1p8p1001:p4p7210P1p8g001Wj11Tg002<j1ETg002Zj2~Tg0037j23Tg003Sj29Tg003nj1mTg004Lj2hTg0053j20Tg005Sj2VTg0064j1^Tg006Mj22Tg006jj28Tg007Gj2BTg007dj2NTg008Kj2OTg0092j2JTg009Nj2KTg00:4j2STg00:Zj2fTg00;Bj3eTg00;fj1dTg00<Dj2cTg00<ej1;Tg00=Dj3ATg00=mj2ZTg00>Vj2bTg00??j3aTg00?hj2XTg00@Tj2WTg00A@j1}Tg00A`j3`Tg00B@j1|Tg00B`j2FTg00C>j4UTg00C\j1{Tg00D:j1vTg00Dej2DTg00EHj1tTg00Ejj3HTg00FMj1RTg00G2j3QTg00GUj3rTg00H8j2\Tg00H[j4ITg00IFj3qTg00Iij2pTg00JKj2oTg00Jej2nTg00KQj3MTg00Kkj3lTg00LJj4kTg00M<j2LTg00MYj1jTP0j6_Tg00NZj2uTg00O@j1iTg00P@j3TTg00Pij7wTg00QMj6xTg00R1j8yTg00RUj7zTg00S9R0f0R1'Jp=7%11#1p=Y%11#1#1#1#1#1#1#1p=<g00SWR2f1R3;M1p=5f3R4f2R5'2/03/L1p=4AM210p=C1053/L1p=s1253/01p=g1Z21p==AT231p=GAT2319T25p=?P2P3g00T5P1CIp=@P3g00T\R6g00U;R7P7g00U[R8P1g00V;Fwp=6P3P6P7P7P8P1Exp=]1\21p=>P4P6P7P7P8P5P3P1Gyp=:P2P3g00V[P1CIp=PP5P6P7P7P8P3P1Fzp=[%71g00WBR6#1R9#ER:%19R;#1#YR<#ER='~R>,31'9P2%m<R?/h3R@%Y<#<#<#<R<#1RA#<#<#<#<#ERB'0RC%EARA'01515X82P2P3%E<R<PAP<C4RD101B/0A/55X8210DB/VA%CARD#^RE125<RF?sA</0BRG18GA,BA10GA'2'5[1NGA130ARGP4P<PAP<C4/0BRH/0ARI#713IA'9[1OHA13A0RHf4RIP<PAP<C4/0BRJ/0ARK,3A1JK0'9[1KJAf5RJP<PAP<C4/0BRK/8A#C\D1SKAf6RKP<PAP<C4/0BRL/0A/5L\D18LAP2f7RLP<PAP<C4/0B/0AP2f8P<PAP<C4/VB%CBRM#^f9RNP<PAP<C4RO18OB,BB10OB'2'5[1NOB130Bf:ROP<PAP<C4RP/0BRQ#713QB'9[1OPB13B0f;RPP<PAP<C4RQ/0BRR,3B1JR0'9[1KQBf<P<PAP<C4RQ/8B#C\M1SQBf=P<PAP<C4RQ/0B/5Q\M18QBP2f>P<PAP<C4/0BP2f?/2</VAf@RQ/2<RR18RA,BA10RA'2'5\E1NRAfARR/2<RE/0ARS#713SA'9\G1OEAfBRE/2<RS/0ART,3A1JT0'9\H1KSAfC/2<RS/8A#C\D1SSAfD/2<RS/0A/5S\D18SAP2fE?g<AP21f:=130:%7=130>[[%7:RSg00WgRHAe:=3UW0%7>\H^0Sg00XCRS%d6,c2RHg00XoR=#;#;RT#;RU#;RV#;RW#;RX#;RY#=RZ5A2R[%=XRX9A2H%=URU9A2H1Z2=R='G3?1b2A=a2=R\%;Y#=RY%=W%=VRV/GU5?Z3?g00YNRW'X'W1GU=9?ZXAA2HYAA2HV%=T'G9?[X5?\/XW'W%}S5`S3`%|SP2P21F2IP51F2KCUP3P21F2JP41F2LCUCU%{2%v2RSPS1D2ARW1D20R\'@,6S,]SRX%t7R7%>9R[1D2<RT5H2%R6RV#R#>9Q2W%R9#>R95H2'@,6SC:P7PSPS1D2BRH/@\,6S,]SP7Ar29T%1V#>9Q2H%>VRV5H2'@,6SC:P7PSPS1P\W,6SP7P2P\g00Z:RH1\26R6CI,6S1P6W,6S5[SC:P7PSPSPXP7%>;9Q2W=H26,@V,6SC:P7PSP2P\PHP[CI,6S1D2:=q2?,P[,6S5[SP71@6[,6SC:C:C:C:C:1pS8P1P5g00ZaRSg00[AR8'o1n15=MS8dAl203CkbJbMbNX12X22X32X42X52X62X72g00[aR0\DRD1BALR8/2J,5F[P0\M1LK<1BBL/2I'5[%74134A'9\G128I,5K\D%7J13J>'915JK[[[[[^12^22^32^42^52^62^72P1PIPPP4PEPOfIPRPNPQfFfGfHO<bIbKbLbUbQb?b>b=b<bGbTbPbFbEbDbCbBbSbObAb@b;b:b9P@%j3E_1u?C%iCE_WHXR2o"). Qed.

(* [comment removed for export] *)
Lemma land_m64 : forall x, Z.land x 18446744073709551615 = x mod 18446744073709551616.
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_prod ()) [] "h07__arithh14__ffh28__varmaph35__with41xh51zp;1p;2p;3p;4p;7p;6g001Wj10Tg002<j12Tg002Zj27Tg0053j23Tg00KQj34Tg00JKj26Tg00\>j1;Tg00\\j28Tg00A@j19Tg00B@j1:Tg00]:j1ITg00C\j1HTg00D:j1GTg00Dej25Tg00H[j4ETg00Pij7BTg00Iij2?Tg00Jej2@Tg00Kkj3ATg00LJj4=Tg0092j2CTg00]Xj3DTg000\j6<Tf0R0#0#0#0#0p=>%00#0p=F%00#0#0#0#0#0#0#0p=1g00SWR1P1g00WB#0R2#2%02#>R2#2R3'7,30f1R4%F2#1#1#1#1#1#1#1#2R2'39410X511302,61%;3,80g00XCR2#9%:2%I1%H1%G1R2g00T\g00U;R5P5g00U[R5P1g00S9R6,51g00Z:1513CEg00V;FB1?25P0f2R5g00ZaR2g00[AR7'61@05=427dAA164C=b1b2b31C63P0b09D03E<W4o"). Qed.


Lemma wrap_swrap32_land : forall r, 0 <= r < 2^32 -> bv_wrap 32 (Z.land (bv_swrap 32 r) 18446744073709551615) = r.
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_prod ()) [] "h02Hrh17__arithh24__ffh38__varmaph45__with51rh61zp;2p;1p;3p;4p;7p;6g0092j25Tg001Wj10Tg002<j11Tg002Zj23Tg0037j2LTg003Sj2@Tg003nj1<Tg004Lj2;Tg0053j28Tg00NZj27Tg00KQj32Tg00^;j26Tg00\>j19Tg00\\j2KTg00A@j1JTg00B@j1ITg00]:j1?Tg00C\j1=Tg00D:j1>Tg00Dej24Tg00H[j4ATg00Pij7BTg00Iij2:Tg00JKj2CTg00Jej2DTg00Kkj3ETg00LJj4FTg00]Xj3GTg000\j6HTg00SWR0g00S9R1f0R2'5g00WB#0R3#1R4%03#0#0#0R3#1'3,L2'@P0%<3R5f1R6';R7%03#1R3,34'81752f2R5520X601662%93,K7g00XCR4#J%I4%?0%=0%>0R4g00T\g00U;R8P8g00U[R8P01401g00Z:1403CAg00V;FB1:48P2P5g00ZaR8g00[AR4'C1D25=284dAE016CFb2b3b41513P2b19G73EHW0W5o"). Qed.


Lemma lor_mod64 : forall a b, Z_to_bv 64 (Z.lor (a mod 18446744073709551616) b) = Z_to_bv 64 (Z.lor a b).
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_prod ()) [] "h01zh17__arithh24__ffh38__varmaph45__with51ah61bp;1p;2p;6p;3p;4p;7g001Wj10Tg002<j18Tg0053j25Tg00_>j22Tg002Zj2BTg00\>j1ATg00\\j21Tg00JKj2:Tg00_[j1>Tg000\j69Tg00`>j3OTg00`bj66Tg00a>j3=Tg00A@j1NTg00B@j1MTg00]:j1LTg00C\j1KTg00D:j1HTg00Dej2<Tg00H[j4DTg00Pij7ETg00Iij2FTg00Jej2GTg00KQj3;Tg00Kkj3@Tg00LJj4ITg0092j2JTg00]Xj37Tg00ahj3?Tf0R0#0#0#0#0p=P%00#0p=C%00#0#0#0#0#0#0#0p=4g00SWR1f1R2;;0p=3g00WB#0R3#0#PR4#C#4#4#4#4#4#4#4#8,52/201220R5P1%83%84R4'BR3,52R6/20R7%A4R8'1f2R9/22R:/53R;,30X01P11128R<1202/18/3;X01P11158R;1198R=/22/18/30X01P111<8R>1108R?'211:8,30X01P112<?R?11=8/2</30X01P11188R:,12120<12=<R='3X01P1P81190/2</3=X011:1?P:%>8E9P>AO288E6P;A=208E912<0/18A=<08E91553g00XCR<#N%M<%L1%K1%H1R<g00T\g00U;R8P8g00U[R8P1g00S9R;,<1g00Z:1<14CDg00V;FE1F<8P0P9g00ZaR8g00[AR<':1G09=;8<dA@1;2CIb2b3b41J;4P0b1R09754E6P6A7240E61573A7740E63?X61X51o"). Qed.


Lemma lor_swrap32_byte : forall x b, 0 <= x < 2^24 -> 0 <= b < 256 ->
  Z.lor (bv_swrap 32 (x * 256)) b = bv_swrap 32 (x * 256 + b).
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_prod ()) [] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with54__p1h61zh74__x2h81Hh91bh:4__x3h;2Hbh<1si001sh=2H0h>2H1h?2H2h@2H3hA2HahB6__sat4hC6__sat5hD4__x4hE1ahF1li011lhG1qhH1rhI1GhJ2HkhK2HxhL1LhM4LANDhN2N0hO6__sat1hP6__sat2hQ1ei021ehR1khS1xi031np%0p&0p;1p;2p;3p;4p;6p;7p;5p;8g001Wj18Tg002<j1LTg00FMk10:Tg002Zj2\Tg007Gj23Tg006Mj20Tg0053j24Tg00M<j22Tg003nj1jTg004Lj2nTg00bdj2|Tg0037j21Tg0092j2:Tg00cKR0j2kTg00A@k10RTg00B@k10QTg00B`j2^Tg00C\k10OTg00D:k10NTg00H8j2_Tg00G2j3cTg00Iik209Tg00JKj2dTg00Jek206Tg00KQj3DTg00Kkk303Tg00LJk402Tg00]:j1~Tg00C>j4YTg00Dej2}Tg00EHk10TTg003SS00j2CTg00ckk40STg00<ej1FTg00>Vj2{Tg00=mj2zTg00??j3`Tg00@Tj2ITg00djj3yTg000\j6Xk70>Tg005Sj2xTg0064j1]Tg006jj2VTg007dj2wTg008Kj2vTg009Nj2uTg00:4j2tTg00:Zk20MTg00;Bk30LTg00;fk10HTg00<Dk20GTg00=Dj3gTg00IFj3rTg00_>j2qTg00\\j2oTg00eMj26Tg00enj2ZTg00fLk40FTg00g7k10ETg00gWk20DTg00h7j1UTg00hUk30=Tg00i;k508Tg00ibk50;Tg00jGk40<Tg00k0k107Tg00kPk30?Tg00l3k30@Tg00lVk20ATg00m4k30BTg00m^k30CTg00MYj1pTg00Ejk305Tg00GUk304Tg00H[j4hTg00Pij7lTg00n@k60ITg00RUk70JTg00R1j8iTg00`bk60KTg00P@j3mTg00?hk201Tg00A`k300Tg00QMk60PTg00S9R1f0R2':p=5%82#8p=bf2R3f1R4/12'Cp=9%82#8#8#8p=[g00SWR51q34;D2p=@1034/02p=>1}52p=SB05542p=TB04542p=KP3g00T\R6g00U;R7P7g00U[R8P5P4g00T5P2Chg00V;R9Flp=?12429D53p=JP5P4g00Z:P2Chp=RP4P6P7P7P8P2P9Flp=QP4P6P7P7P8P2J0Ip=aP3P6P7P7P8P4P2K0Jp==f3R:P6P7P7P8P3P4P2Gip=;P3P6P7P7P8P5P4g00V[P2ChP9Flp=7P5f4R9P:P3P4P2J0Kp=H1z52p=EAm5429m53p=Mg00YN-012p=Ng00XCR;@0042p=Pf6R<P6P7P7P8f5R=P9P:P6P7P7P8P3P4P2GiGip=OAm542p=BAD521p=GAD542p=<1112p=WP4P6P7P7P8P2J0Pp=s1234/32p=Ag00ZaR6g00ndR>7D2p=fP6P>P:P3P4P2EXp=e%54R?g00WBR@#8RA#LRB&0:@S01#8#bS02#LRC'\RD794%8AS03#8RE#bRF#8#bRG#LRH99?4RIP513:HRJ%[G#[#[#[S04#8#b#[RG#LRK'0%8G#LRG'4/2K%jFRF139HRL/0:'n9@2:X65P510J3RM/0K/4G/2K10LKS05/4G/2K?@:2X651|JK11JK1:KJ'kP011LK1:KL13=HRL/0K/4G/2KA>L9K/4G/2K7@9P211LKP513<HRN/0KRO122KRPf7RQ/3HRR/0<RS/0KRT/4GS06/2K7@<X65P5A>N=KRU10RKRV/2KRW?@<PX65&0R;RX&0Q;R;1^54RY&0O5RZ&0N5R[1_5@R\%SHR]5c5R^%SKR_,T^R`/K_3?209[8R8P2P3g00[ARa,d620623=D6adB03514H02Rab2b3b4X05132HRb10bKS07;JK^05P2PQO1b1AJNOKPRf8RR/3HRN/0QRc/0KRd/2KRe9@2QX65PXP;P51^53P4%~5RfCYS08PZ1_5ARA,T^Rg1Tg_Rg/K_5?[P8Pab2b3b4X05X7510b4Rh10hKS09;JK^05^75P2PQPRO2b1AJSTKPcf9Rc/3HRS?@R2X65PRPQp-0RhPXP;PYPZP[1}51Ri/R\,Q[Rj1a[:S0:5=[S0;&0T7R7PjC;P8Pab2b3b4X05W5S0<%52Rk/C4P?[^05^5hS0=P211cDPcPQO3b1PXP;PYPZP[A7[\]S0>9=[jRlP7PlC;P8Pab2b3b4X05112HS0?,CkS0@PI[^05P2PRP<O2b1H0SPeP2DHb8PWP2DHb814UGg00XoRW#FRe#FRI#FRl#FRm#ERn1{5HRo1z5WRW5`5Rp%ElRl%EeRe3M#N'IA`5oe=MlW#N/PX'PP;Q08PZP[A7[^_RqP7P[1RiA,Q[RrA7[A]5=[S0AP7P[1a[99=[jP71Rig,Q[%SGRj97[g5=[C;FOP8Pab2b3b4X05X75X5h11bKRb%53Rs?93H1Cs9A>J9KRt#5?9tG[[[^05^75^5hP211QDRtP<PQP4P9P=O6b19yUGEX14OGS0B%EIRI,BW#N,IW/PXP;PYPZP[PqP7P[Q0;P71Ri`,Q[A7[`j5=[FOP8Pab2b3b4X05X5h1C?3S0C133HR?/0KRq#5?9qG[\b^05^5hP2PtPQP4P=O4b19yOGEXWLP2O11:KL1xOG%GGRt#]Rb1VVG,3G14VGS0D'0,<V[1wVG%WGRU10NKRN/4GRu#5?9uG[1vNG11G1Ru10SKRv/4GRw,1G1:w1'C[1uvGf:Rw/3HRx/0KRy/VG#G\t1tyGf;Ry/3HRz/0KR{/4G/<{\t1V{GP5f<R{/3HR|/0K/4GP520MBCS0E%WBS0F%5C%WD[[S0G%5BR}g00WgR~B0LBC4UWAS0H%5D\~^A}S0I1Bnl1Bpl&0H@-0G5R@%FmRm#ERp5g5R}/BI1BeW#N'I'I'I1BlW1{5G=`5WRe%FmRm#ER~Ag5@nA`5oIRI'B3M#N'I/PX'PP;P5P51^5:S0JP3PfCYP4PfCYPZP[P[A7[ijS0KP7A7[Aj9=[rC;P7P[P[A?[ji,s[S0LP7Q03,_59c5jRr/TA9?[`C;P7P[1R_^,Q[S03P7P[1a[=%SBR^Q02#j5r597[\Ro5=[P71K`jS02=?[AFOFOP8Pab2b3b4X05X75X:5X5hA9s3G\Ug00[aS0M\tRs13G9/0:,<q[1:K?RqA9<:DQ05/2G/<=[[[[^05^75^:5^5hP2f@R`#5P9P:P`PRPcPwf>RCO8b1bBbCbHbGb@b?b>b=b812OGQ0B'<12VG14dGRV/2K9@PQX651xTG1VdG,3G/0V,<d\b1wdGA>SRKRS/4GRb#5?9bG\U1vSGA>xcKRx/4GRb,1G1:b1'C\u1uxGA>zwKRz/VG#G\t1tzGA>|yKR|/4G/<|\t1V|GP5f=R|/3H?>{K/4GP5Q0EQ0GQ0HQ0I1BpW%FmRm#F#EAg5@~?MlI5Me#N'I1B}W%EmAM~pn5Me#N'I/PX'PP;P5P51^59P3PfCYP4Q0JCYPZP[P[Q0KP7Q01,_5Re,Ri,Q[A7[ej5=[C;P7P[P[Q0LP71Tre9?[gC;P7P[Q03P7P[Q0AP7P[1a[<==[oP71KgjRj=?[eC;FOFOP8Pab2b3b4X05X75X:5XD5X5h%5:?9:G\UA>?:K13G=/09'<\s%59?99HA9R9DA>L<K/2G/<Q[[\q[[^05^75^:5^D5^5hP2fARq#5P9P:P`PqPRPcPyPCf?RQO:b1bBbCbHbGb@b?b>b=b812TGQ06'<12dG12vG/2KRv?@RPX65PXP;PYPZQ04#LRP#S,K\=c5]R]Q02/K_5?[P8Pab2b3b4X05AA2PHRdQ07/2G;JK^05P2PcO1b1AARPH12NG;JKAAcPHRN12xG/2KRx9@2cX65PXP;Q08PZ1T]A1Kj_5?[P8Pab2b3b4X05X7510d4Q09/2G;JK^05^75P2PcPwO2b110NR12SG;JKAAwPHRK/0cAAyPHRS/qwRG/<2X651oKcRKP6AA{PHRN/6416y4'Z16139D62X96AA|PH/6316{3'Z=D62X96%LER{,|4114{Rd1:{4Rj'kP0113{1:{3AACPH/6:16|:'Z#fP211:{16Q=,Z2#fX961d6>12QPR>1\B{R_'3/69P>P{P9PXP;PYPZP[%S{R]97[\RAP7PAC;P8Pab2b3b4X05112{Pd[^05P2P=P4O2b1H0FCeWFP2O11:{:AA`PH/6=/Z2#fX9613>H/69$0E16C9PCP9Q0<Q0=P211QHPQP|O3b120DC1%GCRC%]C'kP0%GQR0%]0%U`/1<P2%G`R`P5P1Q0@%U4/1c];X951:11%WH'CPXP;PYPZP[1R]\,Q[R]P7A7[i\R<C;P8Pab2b3b4X051:{2R0%W4RC[^05P2PcP=O2R=b1%U1/1ReW;PqP2PQK0>WQP2O1%]`Q001\B4,13%U:/13[R`%U3/141\B3,1:RQ[%U9/1:\QB0=342P4n2001000000120000000VCX95XE5P`\C^95^E5P2fBRCPRQ0EQ0GQ0HQ0IPXP;PYPZP[A?[\i,s[P7P[Q0;P7P<FOP8Pab2b3b4X05X5h%G2Q0M[Q0C%W3[[^05^5hP2fER3/1HP3P9fCR9O4b1bObPPCP_1\BRPXP;PYPZP[Q0:Q0>5=[P7%jE9r5^97[\C;P8Pab2b3b4X05X5hQ0?,C4114_[^05^5hP2%59P9PqO3b111C_ePBP{PRPXP;PfPZA7[i^P8Pab2b3b4Q0FP2b1PXP;PYPZP[P]P7P]C;P8Pab2b3b4X05Pj\0^05P=b1I08I0;O4b8WNP2O1n200110000021010211103b<H0<CeWFP2O1n200110000021110111101b<1614&074Ce1oNy/64B0?Ny4EXXJkXR580@1%GK20ASwRK10Ny,<2X65RN10SwRyPN1d5yPKB0BSw2DHPGB0CSw2DHbMPxP2DHb8PvP2DHb8PVP2DHb8Q0DP2DHb8WIP2O1n200110001021110111101b<1nFM%pMEX1nFJ%pJEXW;WKX95XS5o"). Qed.


Ltac sw32m y :=
  match goal with |- context [bv_swrap 32 ?x] =>
    rewrite (FseWalkKit.swrap32_eqm x y) by (rewrite ?land_m64; first [ lia | Z.div_mod_to_equations; lia ])
  end.

Section CANSEC1. Context {rc : runConstT}.
Section U32R.
  Variables (RNG : footprint)
            (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (SP P D : Z) (pl : list Z) (size mn mx lo : Z).
  Hypothesis PR : prod_atA m P D size.
  Hypothesis PL : payload_atA m D pl.
  Hypothesis SZ : 0 <= size <= zlen pl.
  Hypothesis P0 : 0 < P.
  Hypothesis P8 : P mod 8 = 0.
  Hypothesis D0 : 0 < D.
  Hypothesis ST : stk bsegs m lo SP.
  Hypothesis LO : lo <= SP - 16.
  Hypothesis RSP : 0 <= SP < 2^64.
  Hypothesis PLO : P + 16 <= lo.
  Hypothesis DLO : D + zlen pl <= lo.
  Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis MM : 0 <= mn <= mx.
  Hypothesis MX : mx < 2^31.
  Hypothesis BLKP : ablk P (P + 16).
  Hypothesis BLKD : 0 < zlen pl -> ablk D (D + zlen pl).
  Hypothesis D8 : D mod 8 = 0.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis UNP : unpoisoned m P (P + 16).
  Hypothesis UND : unpoisoned m D (D + zlen pl).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RP : rng RNG P 16.
  Hypothesis RPS : rng RNG (shad P) 2.
  Hypothesis RD : rng RNG D (zlen pl).
  Hypothesis RDS : rng RNG (shad D) (nshad (zlen pl)).

  Notation POST := (prod_u32r_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP P D pl size mn mx lo m).

  Notation W := [(P + 8, P + 16); (SP - 16, SP)].
  Notation range := (mx - mn).
  Definition ASHB : Z := 0x7fff8000.

  Ltac zify_lts K :=
    unfold bv_lts in K; rewrite ?land7_mod in K;
    rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
    zify_bool K.

  
  Lemma inv_shadow : forall m1, munch W m m1 -> unpoisoned m1 P (P + 16) /\ unpoisoned m1 D (D + zlen pl).
Proof.
intros m1 MU. pose proof (ablk_lin _ _ BLKP) as LP.
pose proof (ablk_disj_band _ _ BLKP) as DBP. unfold KHIGH, KLS, AIMG_HI in *.
split.
- (eapply unpoisoned_munch; [eassumption| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
- destruct (Z.eq_dec (zlen pl) 0) as [E0|N0].
+ replace (D + zlen pl) with D by lia. apply unpoisoned_nil. change (2^64) with 18446744073709551616 in *. lia.
+ pose proof (ablk_lin _ _ (BLKD ltac:(lia))) as LD. unfold AIMG_HI in LD.
(eapply unpoisoned_munch; [eassumption| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
Qed.

  Definition INV (m1 : amem) (sz : Z) : Prop :=
    rw_cells bsegs m1 P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 sz)]
    /\ bytes_at bsegs m1 D (map (Z_to_bv 8) pl)
    /\ (exists junk8, rw_cells bsegs m1 (SP + -16) [CB 8 junk8; C8 ra])
    /\ stk bsegs m1 lo (SP + -16)
    /\ munch W m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1.

  Ltac inv_close PRx PLx FRx STx MUx WMx MIx :=
    split; [exact PRx|]; split; [exact PLx|]; split; [eexists; exact FRx|]; split; [exact STx|]; split; [exact MUx|]; split; [exact WMx| exact MIx].

  
  Notation STpc pc mm x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 mn) x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Lemma draw_loop_0 : forall f sz result, draw_loop f pl sz 0 result = (result, sz).
Proof. intros [|f] sz result; reflexivity. Qed.

  Lemma pl_nth : forall i, 0 <= i < zlen pl ->
    nth_error (map (Z_to_bv 8) pl) (Z.to_nat i) = Some (Z_to_bv 8 (Znth i pl)) /\ 0 <= Znth i pl < 256.
Proof.
intros i Hi. destruct PL as [_ PLR]. unfold Znth.
assert (L : (Z.to_nat i < length pl)%nat) by lia.
split.
- rewrite nth_error_map. rewrite (nth_error_nth' pl 0 L). reflexivity.
- apply (proj1 (Forall_forall _ _) PLR). apply nth_In. exact L.
Qed.

  
  Lemma u32r_tailA : forall m1 result sz (x5 x6 x7 x10 x13 x14 x16 x17 x28 x29 x30 : word),
    0 <= result < 2^32 -> INV m1 sz ->
    (result, sz) = draw_loop 4 pl size range 0 ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 x6 x7 s0 s1 x10 (Z_to_bv 64 mn) (Z_to_bv 64 (bv_swrap 32 result)) x13 x14 (Z_to_bv 64 range) x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
          F (Z_to_bv 64 0x9afd4) fc None m1 (seg_rom bsegs)).
Proof.
intros m1 result sz x5 x6 x7 x10 x13 x14 x16 x17 x28 x29 x30 RR (PR1 & PL1 & [junk8 FR1] & ST1 & MU1 & WM1 & MI1) DL.
zstep. zstep. unfold v_remuw.
zsimp.
rewrite (wrap32_small (range + 1)) by lia. rewrite ?wrap_swrap32_land, ?wrap_swrap32 by lia. rewrite ?(wrap32_small result) by lia.
replace (range + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
assert (RM : 0 <= result mod (range + 1) < range + 1) by (apply Z.mod_pos_bound; lia).
rewrite FseWalkKit.swrap32_small by lia.
zstep. rewrite FseWalkKit.swrap32_small by lia.
zstep. zstep. zstep.
release_frame FR1 ST1 SP.
zstep.
apply evtF_done. unfold prod_u32r_postA, uint32Range.
rewrite (u32_id range) by lia. rewrite <- DL.
replace (range =? 2^32 - 1) with false by (symmetry; apply Z.eqb_neq; lia).
cbn [fst snd]. rewrite (u32_id (mn + result mod (range + 1))) by lia.
replace (result mod (range + 1) + mn) with (mn + result mod (range + 1)) by lia.
do 14 eexists. exists m1. split; [reflexivity|].
split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1| exact PR1].
Qed.

  
  Lemma u32r_loopA : forall f sz rolling result m1 (x6 x14 x29 x30 : word),
    0 < rolling < 2^(8 * Z.of_nat f) -> 0 <= result < 2^(32 - 8 * Z.of_nat f) -> (f <= 4)%nat ->
    0 <= sz <= zlen pl -> x6 = Z_to_bv 64 (sz + -1) -> INV m1 sz ->
    (forall m2 (y6 y14 y28 y29 y30 : word), INV m2 (snd (draw_loop f pl sz rolling result)) ->
       0 <= fst (draw_loop f pl sz rolling result) < 2^32 ->
       evtF bsegs RNG POST (STpc 0x9afc4 m2 (Z_to_bv 64 (-1)) y6 (Z_to_bv 64 (Z.shiftr P 3 + ASHB))
                                 (Z_to_bv 64 (bv_swrap 32 (fst (draw_loop f pl sz rolling result)))) (Z_to_bv 64 (P + 8)) y14 (Z_to_bv 64 range)
                                 (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (P + 8) 3 + ASHB)) y28 y29 y30)) ->
    evtF bsegs RNG POST (STpc 0x9af54 m1 (Z_to_bv 64 (-1)) x6 (Z_to_bv 64 (Z.shiftr P 3 + ASHB))
                              (Z_to_bv 64 result) (Z_to_bv 64 (P + 8)) x14 (Z_to_bv 64 range)
                              (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (P + 8) 3 + ASHB)) (Z_to_bv 64 rolling) x29 x30).
Proof.
induction f as [|f IH]; intros sz rolling result m1 x6 x14 x29 x30 RO RE F4 SZ1 -> (PR1 & PL1 & [junk8 FR1] & ST1 & MU1 & WM1 & MI1) K.
{ exfalso. cbn in RO. lia. }
pose proof (bytes_at_bound _ _ _ _ PL1) as DB. rewrite length_map in DB.
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
pose proof (ablk_lin _ _ BLKP) as LP. unfold KHIGH, AIMG_HI, ASHB in *.
destruct (inv_shadow m1 MU1) as [UNP1 UND1].
assert (P8' : 2^(8 * Z.of_nat (S f)) = 256 * 2^(8 * Z.of_nat f)).
{ replace (8 * Z.of_nat (S f)) with (8 + 8 * Z.of_nat f) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
assert (Q8 : 2^(32 - 8 * Z.of_nat f) = 256 * 2^(32 - 8 * Z.of_nat (S f))).
{ replace (32 - 8 * Z.of_nat f) with (8 + (32 - 8 * Z.of_nat (S f))) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
assert (Q24 : 2^(32 - 8 * Z.of_nat (S f)) <= 2^24) by (apply Z.pow_le_mono_r; lia).
assert (Q32 : 2^(32 - 8 * Z.of_nat f) <= 2^32) by (apply Z.pow_le_mono_r; lia).
assert (P32 : 2^(8 * Z.of_nat (S f)) <= 2^32) by (apply Z.pow_le_mono_r; lia).
assert (PP0 : 0 < 2^(8 * Z.of_nat f)) by (apply Z.pow_pos_nonneg; lia).
assert (QQ0 : 0 < 2^(32 - 8 * Z.of_nat (S f))) by (apply Z.pow_pos_nonneg; lia).
cbn [draw_loop] in K. change (2^8) with 256 in K.
replace (0 <? rolling) with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in K.
change (2^24) with 16777216 in Q24. change (2^32) with 4294967296 in Q32, P32.
zstep. if_cases B; zify_cond B; rewrite ?land_m64 in B.
-
assert (sz = 0) by (Z.div_mod_to_equations; lia). subst sz.
replace (0 <? 0) with false in K by reflexivity. cbn [fst snd] in K.
rewrite (FseWalkKit.swrap32_small result) in K by lia.
apply K; [| lia].
inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1.
- assert (SZP : 0 < sz) by (Z.div_mod_to_equations; lia).
pose proof (ablk_lin _ _ (BLKD ltac:(lia))) as LD. unfold AIMG_HI in LD.
replace (0 <? sz) with true in K by (symmetry; apply Z.ltb_lt; lia).
destruct (pl_nth (sz - 1) ltac:(lia)) as [NTH NR].
pose proof (unpoisoned_full_rd bsegs m1 P (P + 16) (Z.shiftr P 3 + 0x7fff8000) UNP1
ltac:(rewrite shad_div; unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)
ltac:(unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)) as RDP.
zstep. zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep. zstep. zstep.
zstep. if_cases GA; zify_cond GA; [exfalso; lia|].
zstep. if_cases GB; zify_cond GB; [exfalso; lia|].
zstep. if_cases GC; zify_cond GC; [exfalso; lia|].
zstep. if_cases GD; zify_cond GD; [exfalso; lia|].
destruct (unpoisoned_check_rd bsegs m1 D (D + zlen pl) (sz + -1 + D) 1 UND1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (b & RDB & CK).
unfold shad, ASHOFF in RDB. replace (0x7fff8000 + Z.shiftr (sz + -1 + D) 3) with (Z.shiftr (sz + -1 + D) 3 + 0x7fff8000) in RDB by lia.
pose proof (sval_range b) as SR.
zstep. zstep. zstep. rewrite sxb_sval.
assert (JOIN : forall (y29 y30 : word), evtF bsegs RNG POST
(STpc 0x9af8c m1 (Z_to_bv 64 (-1)) (Z_to_bv 64 (sz + -1)) (Z_to_bv 64 (Z.shiftr P 3 + 0x7fff8000))
(Z_to_bv 64 result) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 (sz + -1 + D)) (Z_to_bv 64 range)
(Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (Z.shiftr (P + 8) 3 + 0x7fff8000)) (Z_to_bv 64 rolling) y29 y30)).
{ intros y29 y30.
pose proof (unpoisoned_full_rd bsegs m1 P (P + 16) (Z.shiftr (P + 8) 3 + 0x7fff8000) UNP1
ltac:(rewrite shad_div; unfold ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)
ltac:(unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)) as RDS8.
zstep. zstep. if_cases G3; zify_cond G3; [exfalso; lia|].
assert (RDV : ov_read_bytes bsegs m1 (Z_to_bv 64 (sz + -1 + D)) 1 = Some [Z_to_bv 8 (Znth (sz - 1) pl)]).
{ eapply (u8ro_read bsegs m1 D _ (sz - 1)); [exact PL1| exact NTH| lia| unfold wa; f_equal; lia]. }
zstep. cbv beta. rewrite byte_lit by exact NR.
zstep.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
zstep. rewrite (wrap32_small rolling) by lia. rewrite (Z.shiftr_div_pow2 rolling 8) by lia. change (2^8) with 256.
assert (RD8 : 0 <= rolling / 256 < 2^(8 * Z.of_nat f)).
{ split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
rewrite (FseWalkKit.swrap32_small (rolling / 256)) by lia.
zstep.
rewrite ?land_m64, ?lor_mod64. rewrite (lor_swrap32_byte result (Znth (sz - 1) pl)) by lia.
rewrite (u32_id (result * 256)) in K by lia.
assert (LOR : Z.lor (result * 256) (Znth (sz - 1) pl) = result * 256 + Znth (sz - 1) pl) by (apply (lor_byte result); lia).
rewrite LOR in K.
zstep. zstep.
if_cases B2; zify_cond B2.
+
assert (F1 : (1 <= f)%nat). { destruct f; [|lia]. exfalso. change (2^(8 * Z.of_nat 0)) with 1 in RD8. lia. }
assert (Q16 : 2^(32 - 8 * Z.of_nat f) <= 2^24) by (apply Z.pow_le_mono_r; lia).
change (2^24) with 16777216 in Q16.
rewrite (FseWalkKit.swrap32_small (result * 256 + Znth (sz - 1) pl)) by lia.
eapply (IH (sz - 1) (rolling / 256) (result * 256 + Znth (sz - 1) pl)); try lia.
* f_equal. lia.
* replace (sz - 1) with (sz + -1) by lia. inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1.
* exact K.
+
assert (R0 : rolling / 256 = 0) by lia. rewrite R0 in K. rewrite draw_loop_0 in K.
zstep.
apply K; [| cbn [fst]; lia].
cbn [snd]. replace (sz - 1) with (sz + -1) by lia. inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1. }
zstep. if_cases G2; zify_cond G2.
+
zstep. zstep. if_cases G2'; zify_lts G2'; [| exfalso; Z.div_mod_to_equations; lia].
apply JOIN.
+ apply JOIN.
Qed.

  Lemma u32r_bodyA : evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 mn) (Z_to_bv 64 mx) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APROD_U32R) fc None m (seg_rom bsegs)).
Proof.
unfold APROD_U32R. pose proof PR as PR0. unfold prod_atA in PR0. destruct PL as [PLB PLR].
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
pose proof (ablk_lin _ _ BLKP) as LP. unfold KHIGH, AIMG_HI in *.
carve_frame 16%nat ST.
zstep. zstep. zstep. zstep. zstep.
zstep. if_cases K; zify_cond K. { exfalso. lia. }
zstep. rewrite FseWalkKit.swrap32_small by lia. zstep.
if_cases K2; zify_cond K2.
-
zstep.
eapply (u32r_tailA _ 0 size); [lia| | ].
+ inv_close PR0 PLB FR ST MU WM MI.
+ rewrite K2. reflexivity.
- assert (K2' : 0 < range) by lia.
destruct (inv_shadow _ MU) as [UNP1 UND1].
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
pose proof (unpoisoned_full_rd bsegs m1 P (P + 16) (Z.shiftr (P + 8) 3 + 2147450880) UNP1
ltac:(rewrite shad_div; unfold ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)
ltac:(unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)) as RDS8 end.
zstep. if_cases GN; zify_cond GN; [exfalso; lia|].
zstep. rewrite land7_mod. rewrite P8.
zstep. if_cases GAL; zify_cond GAL; [exfalso; lia|].
zstep. zstep. zstep. zstep. zstep. if_cases G0; zify_cond G0; [exfalso; lia|].
do 6 zstep.
eapply (u32r_loopA 4 size range 0);
[ change (2^(8 * (Z.of_nat 4 - 1))) with (2^24); lia | cbn; lia | lia | lia | reflexivity | | ].
+ inv_close PR0 PLB FR ST MU WM MI.
+ intros m2 y6 y14 y28 y29 y30 I2 R2.
zstep. zstep. if_cases K3; zify_cond K3.
* eapply u32r_tailA; [exact R2| exact I2| ]. destruct (draw_loop 4 pl size range 0); reflexivity.
* exfalso. lia.
Qed.
End U32R.

Lemma prod_u32r_proofA : prod_u32r_stmtA.
Proof.
intros until lo. intros PR PL SZ P0 P8 D0 ST LO RSP PLO DLO DP MI MM MX BLKP BLKD D8 KLO GOT SHB UNP UND RI RSTK RP RPS RD RDS -> -> ->.
eapply u32r_bodyA; eassumption.
Qed.



Section I32R.
  Hypothesis U32R : prod_u32r_stmtA.
  Variables (RNG : footprint)
            (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (SP P D : Z) (pl : list Z) (size mn mx lo : Z).
  Hypothesis PR : prod_atA m P D size.
  Hypothesis PL : payload_atA m D pl.
  Hypothesis SZ : 0 <= size <= zlen pl.
  Hypothesis P0 : 0 < P.
  Hypothesis P8 : P mod 8 = 0.
  Hypothesis D0 : 0 < D.
  Hypothesis ST : stk bsegs m lo SP.
  Hypothesis LO : lo <= SP - 32.
  Hypothesis RSP : 0 <= SP < 2^64.
  Hypothesis PLO : P + 16 <= lo.
  Hypothesis DLO : D + zlen pl <= lo.
  Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis MM : - 2^31 <= mn <= mx.
  Hypothesis RG : mx - mn < 2^31.
  Hypothesis MX : mx < 2^31.
  Hypothesis BLKP : ablk P (P + 16).
  Hypothesis BLKD : 0 < zlen pl -> ablk D (D + zlen pl).
  Hypothesis D8 : D mod 8 = 0.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis UNP : unpoisoned m P (P + 16).
  Hypothesis UND : unpoisoned m D (D + zlen pl).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RP : rng RNG P 16.
  Hypothesis RPS : rng RNG (shad P) 2.
  Hypothesis RD : rng RNG D (zlen pl).
  Hypothesis RDS : rng RNG (shad D) (nshad (zlen pl)).

  Notation W := [(P + 8, P + 16); (SP - 32, SP)].

  
  Lemma inv_shadow_i : forall m1, munch W m m1 -> unpoisoned m1 P (P + 16) /\ unpoisoned m1 D (D + zlen pl).
Proof.
intros m1 MU. pose proof (ablk_lin _ _ BLKP) as LP.
pose proof (ablk_disj_band _ _ BLKP) as DBP. unfold KHIGH, KLS, AIMG_HI in *.
split.
- (eapply unpoisoned_munch; [eassumption| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
- destruct (Z.eq_dec (zlen pl) 0) as [E0|N0].
+ replace (D + zlen pl) with D by lia. apply unpoisoned_nil. change (2^64) with 18446744073709551616 in *. lia.
+ pose proof (ablk_lin _ _ (BLKD ltac:(lia))) as LD. unfold AIMG_HI in LD.
(eapply unpoisoned_munch; [eassumption| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
Qed.

  Lemma i32r_bodyA : evtF bsegs RNG (prod_i32r_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP P D pl size mn mx lo m)
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 mn) (Z_to_bv 64 mx) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APROD_I32R) fc None m (seg_rom bsegs)).
Proof.
unfold APROD_I32R. pose proof PR as PR0. unfold prod_atA in PR0. destruct PL as [PLB PLR].
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
change (2^31) with 2147483648 in *. change (2^24) with 16777216 in *.
pose proof ST as (LO0 & _ & _).
pose proof (ablk_lin _ _ BLKP) as LP. unfold KHIGH, AIMG_HI in *.
carve_frame 16%nat ST.
zstep. zstep. zstep. zstep.
if_cases K. { exfalso. unfold bv_lts in K. rewrite !signed_lit in K by lia. apply Z.ltb_lt in K. lia. }
clear K.
destruct (inv_shadow_i _ MU) as [UNP1 UND1].
zstep. zstep.
if_cases K; rewrite bv_lts_zero_r in K.
-
assert (MN : mn < 0).
{ destruct (Z.lt_ge_cases mn 0) as [L|G]; [exact L| exfalso]. rewrite unsigned_lit in K by lia. apply Z.leb_le in K. lia. }
clear K.
zstep. zstep. sw32m (mx - mn).
zstep.
rewrite ?land_m64. replace (Z_to_bv 64 (mx mod 18446744073709551616 - mn mod 18446744073709551616)) with (Z_to_bv 64 (mx - mn))
by (apply Z_to_bv_eqm; change (2^64) with 18446744073709551616; lia).
unfold bv_eqb. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
zstep. sw32m (mx - mn). zstep. zstep.
unfold APROD_U32R in U32R.
call (U32R RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -16) P D pl size 0 (mx - mn) lo);
[ exact PR0 | split; [exact PLB| exact PLR] | exact SZ | exact P0 | exact P8 | exact D0 | exact ST
| lia | lia | exact PLO | exact DLO | exact DP | exact MI | lia | lia
| exact BLKP | exact BLKD | exact D8 | unfold KHIGH; lia | exact GOT | exact SHB | exact UNP1 | exact UND1
| reflexivity | reflexivity | reflexivity | ].
pose proof (uint32Range_range pl size 0 (mx - mn) ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)
ltac:(change (2^32) with 4294967296; lia)) as UR.
assert (I32 : int32Range pl size mn mx = ((uint32Range pl size 0 (mx - mn)).1 + mn, (uint32Range pl size 0 (mx - mn)).2)).
{ unfold int32Range. replace (mn <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
destruct (uint32Range pl size 0 (mx - mn)); reflexivity. }
destruct (uint32Range pl size 0 (mx - mn)) as [r size'] eqn:EU. cbn [fst snd] in *.
zstep. zstep. sw32m (r + mn).
zstep.
rewrite ?land_m64. replace (Z_to_bv 64 (r + mn mod 18446744073709551616)) with (Z_to_bv 64 (r + mn))
by (apply Z_to_bv_eqm; change (2^64) with 18446744073709551616; lia).
unfold bv_eqb. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
zstep. sw32m (r + mn).
zstep. zstep. zstep.
release_frame FR PC SP.
zstep.
apply evtF_done. unfold prod_i32r_postA. rewrite I32. cbn [fst snd].
do 14 eexists. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact PC| exact POST].
-
assert (MN : 0 <= mn).
{ destruct (Z.lt_ge_cases mn 0) as [L|G]; [exfalso| exact G]. rewrite (unsigned_neg mn) in K by lia. apply Z.leb_gt in K. lia. }
clear K.
zstep. zstep. zstep. zstep.
release_frame FR ST SP.
zstep.
unfold APROD_U32R in U32R.
eapply evtF_mono.
{ eapply (U32R RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP P D pl size mn mx lo);
[ exact PR0 | split; [exact PLB| exact PLR] | exact SZ | exact P0 | exact P8 | exact D0 | exact ST
| lia | lia | exact PLO | exact DLO | exact DP | exact MI | lia | lia
| exact BLKP | exact BLKD | exact D8 | unfold KHIGH; lia | exact GOT | exact SHB | exact UNP1 | exact UND1
| exact RI | exact RSTK | exact RP | exact RPS | exact RD | exact RDS
| reflexivity | reflexivity | reflexivity ]. }
cbv beta. intros ms' PO. unfold prod_u32r_postA in PO. unfold prod_i32r_postA.
destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU' & WM' & MI' & ST' & PR').
assert (I32 : int32Range pl size mn mx = uint32Range pl size mn mx).
{ unfold int32Range. replace (mn <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
rewrite I32.
do 14 eexists. exists m'. split; [reflexivity|].
split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp. cbn [outside]. intros; lia. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'| exact PR'].
Qed.
End I32R.

Lemma prod_i32r_proofA : prod_u32r_stmtA -> prod_i32r_stmtA.
Proof.
intros U32R. intros until lo. intros PR PL SZ P0 P8 D0 ST LO RSP PLO DLO DP MI MM RG MX BLKP BLKD D8 KLO GOT SHB UNP UND RI RSTK RP RPS RD RDS -> -> ->.
eapply i32r_bodyA; eassumption.
Qed.


Lemma prod_rem_proofA : prod_rem_stmtA.
Proof.
intros RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV P D size lo PR SZ P0 P8 ST LO RSP PLO MI BLKP KLO GOT SHB UNP RI RSTK RP RPS ->.
unfold APROD_REM. unfold prod_atA in PR.
pose proof (munch_refl [(SPV - 16, SPV)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof (ablk_lin _ _ BLKP) as LP. pose proof (ablk_disj_band _ _ BLKP) as DBP. unfold KHIGH, KLS, AIMG_HI in *.
carve_frame 16%nat ST.
zstep. zstep. zstep.
if_cases K1; zify_cond K1; [exfalso; lia|].
zstep. zstep. rewrite land7_mod, P8.
if_cases K2; zify_cond K2; [exfalso; lia|].
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) => assert (UNP0 : unpoisoned m1 P (P + 16)) by ((eapply unpoisoned_munch; [exact UNP| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from]; (split; [Z.div_mod_to_equations; lia| exact I])) end.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) => pose proof (unpoisoned_full_rd bsegs m1 P (P + 16) (Z.shiftr (P + 8) 3 + 0x7fff8000) UNP0
ltac:(rewrite shad_div; unfold ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)
ltac:(unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)) as RDS8 end.
repeat (zstep; lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?n) _ _ _ _) => is_Zlit n end).
zstep. unfold bv_eqb. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
repeat (zstep; lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?n) _ _ _ _) => is_Zlit n end).
release_frame FR ST SPV.
zstep.
apply evtF_done. unfold prod_rem_postA.
do 14 eexists. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

Lemma huf_iserror_proofA : huf_iserror_stmtA.
Proof.
intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c RC ->.
unfold AHUF_ISERROR.
zstep. zstep. zstep.
apply evtF_done. unfold huf_iserror_postA.
match goal with |- context [Z.lxor (Z.b2z (c <? ?M)) 1] =>
  replace (Z.lxor (Z.b2z (c <? M)) 1) with (Z.b2z (2^64 - 119 <=? c))
    by (destruct (Z.ltb_spec c M); destruct (Z.leb_spec (2^64 - 119) c); first [ exfalso; lia | reflexivity ])
end.
reflexivity.
Qed.
End CANSEC1.

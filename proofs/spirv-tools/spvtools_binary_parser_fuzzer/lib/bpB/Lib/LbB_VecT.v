(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
Ltac2 kr_t_LbB_VecT () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init9Datatypes3appC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BellsX<rw_cells_appK47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7hull_loC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic2eq00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7hull_hiC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame9stk_emptyC47Corelib4Init5Logic6eq_indC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5shvisK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3memK47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums1Z03C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv3Sem7mul_divC4ELinuxProcessSemantics5Riscv3Sem5alu64C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions6bv_mulC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloI46Stdlib;setoid_ring<Ring_polynom5PExpr00I47Corelib4Init9Datatypes4prod00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr03C56Stdlib6ZArith6BinInt1Z4to_NK46Stdlib;setoid_ring<Ring_polynom5PExpr09K46Stdlib;setoid_ring<Ring_polynom5PExpr07K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z9mod_smallC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec=bv_wrap64_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_mul_unsignedC45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions?bv_add_unsignedC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterI47Corelib7Numbers7BinNums1N00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions6bv_andC56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K46Stdlib9micromega:ZMicromega;ZArithProof03C45stdpp9bitvector;definitions>Z_to_bv_signedC45stdpp9bitvector;definitions:bv_ashiftrC45stdpp9bitvector;definitionsCbv_ashiftr_unsignedK4ELinuxProcessSemantics5Riscv5Instr5aluop08C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface4bptrC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8map_consC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_AKRELC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_VISC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullI4ARocqVerifyHarness?AgentSubmission6CatSim6msteps00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3mkRC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_MPRESC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC6ARocqVerifyHarness?AgentSubmission3bpB3Lib6LbB_SR6sr_blkK45stdpp9bitvector;definitions2bv01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface=aclient_rangeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface;aimg_clientC46Stdlib5Lists4List2InC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_sizeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3nshC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_FSBC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02I47Corelib4Init5Logic2ex00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8AFS_SIZEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow6AHI_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface@aclient_write_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface=aimg_client_wK47Corelib4Init5Logic2ex01C47Corelib4Init9Datatypes3sndC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_RHEAPC47Corelib4Init5Logic3notC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame:munch_reflC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame:wmono_reflK47Corelib5Lists7ListDef6Forall01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib6LbB_SR;apres_freshC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5apresC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap9ah_blocksC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ablock_rangeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4aappC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap6ah_fsbC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7afsb_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6blk_idC46Stdlib5Lists4List6in_mapC47Corelib4Init5Logic6eq_symC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap7ah_disjC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;sh_nsh_highK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs<ASHADOW_BASEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow@ASHADOW_BASE_valC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3memC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3ivlC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7AAPP_HIC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2wzC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2b8C47Corelib5Lists7ListDef6repeatC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4SHADC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BsWalk7wins_hiC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack09stack0_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<afs_write_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst9aconst_okc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecT5vdisjC56Stdlib6ZArith6BinInt1Z6to_natC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;addressableC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface;as_rauxv_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_RFSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack06stack0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecT:vtail_postC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7ff_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8ff_classC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3fszC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib<regs_ok_seedK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02C47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib;regs_ok_srsC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst=ACONST_shbaseC47Corelib4Init5Logic8iff_reflC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<sh0_of_SHAD0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit2gzC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv=sh0_of_stack0K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry08K5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6kn_fixC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv:kwr_of_stkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit3sh0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8kshadow0C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_addC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotK4ARocqVerifyHarness?AgentSubmission8PropExec7FPState01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C4ARocqVerifyHarness?AgentSubmission7SymRun39run_soundC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26e_addrC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28expr_eqbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv9sb_insideC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7forallbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvBmunch_mem_denot_sbC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC35stdpp7tactics<f_equal_helpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv9munch_eqWC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?wmono_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<wr_at_of_stkC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem2waC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv7sb_disjC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells6cbytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib5Lists7ListDef3nthC56Stdlib6ZArith6BinInt1Z4of_Nc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecT>rw_cells_cons8C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge9rfull_mkRC4ARocqVerifyHarness?AgentSubmission8PropExec4mkstC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge;msteps_fullC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call=regs_keep_mkRK46Stdlib9micromega7EnvRing5PExpr06C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6w_addmC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap?stack_window_okI47Corelib5Lists7ListDef6Forall00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack0=stack0_ok_appC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge>msteps_mem_invC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv=stk_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap>ah_RHEAP_frameC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst<ACONST_frameC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap>ah_rauxv_frameC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap<ah_RFS_frameC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack0@stack0_transportC56Stdlib6ZArith6BinInt1Z7pos_subC57Corelib7BinNums6PosDef3Pos3addK46Stdlib9micromega5Tauto8GFormula01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame=disjoint_fromC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BsWalkHaddressable_transport_hiC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BsWalkBshvis_transport_hiC47Corelib4Init9Datatypes6lengthC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BsWalkASHAD_transport_hiC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep>xpres_of_munchC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep<xpres_weakenC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep5xpresC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BellsXArw_cells_CB_splitC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell05C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<amemcpy_postC47Corelib4Init5Peano2ltC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem3mrdC46Stdlib5Lists4List9nth_errorC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow:accessibleC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow>accessible_nilc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecT9shvis_nilC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow9shvis_subC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame9stk_splitC47Corelib4Init5Logic5proj1C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow:in_app_memC6ARocqVerifyHarness?AgentSubmission3bpB3Lib6LbB_SR=aconst_ok_appC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap9ah_memcpyC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState6ret_pcC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap=RFS_via_apresC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep>xpres_of_apresC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack0<stack0_xpresC47Corelib4Init5Logic5proj2C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrameFstk_transport_disjointC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame9stk_mergec6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecTDaclient_range_weakenC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap>apres_rw_cellsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap<apres_weakenC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState;ret_pc_evenC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells8cells_atC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<kwr_of_wr_atK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond03C46Stdlib5Lists4List:Forall_invC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit:div8_boundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit9estart_shC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S4flatK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr05K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03C47Corelib4Init3Nat3addC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame6insideC46Stdlib9micromega;ZifyClasses8or_morphC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?munch_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv@rw_cells_log_nthC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_mulc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecT6w_sra4c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecT8w_negaddc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecTEaclient_write_ok_consc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecTAclient_fresh_disjC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow9shadow_ofC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface6cc_genC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface;cc_gen_fullC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec3evtC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec6v_addiC45stdpp9bitvector;definitions6bv_notC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState;ret_pc_foldC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude4sextC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec9b_addsextK4ELinuxProcessSemantics5Riscv5Instr5instr04K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv7Prelude4tree02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib8BtepFast8sf_congTC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec8evt_doneC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib8BtepFast;sf_evt_stepC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge=evt_of_mstepsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap>ah_mpres_transC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep;xpres_transC6ARocqVerifyHarness?AgentSubmission3bpB3Lib6LbB_SR6sr_evtC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap<ahh_evt_thenc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecT9sr_blk_eqK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invK46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6reg_evK5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvAkword_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC5ARocqVerifyHarness?AgentSubmission8SymExec33SX27e_widthC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvCrw_cells_log_nth_sbC46Stdlib9micromega;ZifyClasses6eq_iffC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrameBrw_cells_transportC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6BXXRep7rin_ivsC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem8bytes_atC4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msI5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst;AGOT_SHBASEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst<ASHBASE_CELLC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5aluop07I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00C56Stdlib6ZArith4Znat5Nat2Z6inj_leI5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow9ALOWSH_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3ATPC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface=AINTRIN_STACKI5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6fframec6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecT?VAPP_MEMSET_RETC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ATLS_PRIV_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ATLS_PRIV_HII5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecT;HTLbAVecT_0C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<AASAN_MEMCPYK47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_VecT;HTLbAVecT_1C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<AANNOTATE_CCC4ELinuxProcessSemantics5Riscv3Sem2w1C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState6w1_litK47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition VAPP_MEMSET_RET : Z := 0xe9304.

Definition VTAIL_STACK : Z := 96 + 48 + 4096.

Definition vdisj (V spz : Z) : Prop := V + 24 <= spz - 8320 \/ spz <= V.

Ltac lgcell Hlf WA k :=
  eapply (rw_cells_log_nth _ _ _ k);
  [ exact Hlf | reflexivity
  | repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]); apply Forall_nil
  | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
  | exact WA | reflexivity | exact I
  | first [ reflexivity | evs; rewrite ?w_add by lia; reflexivity
          | evs; match goal with HRx : ?R = mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite HRx; reflexivity end ] ].

Lemma rw_cells_cons8 : forall m A (w : word) cs, rw_cells asegs m A [C8 w] -> rw_cells asegs m (A + 8) cs -> rw_cells asegs m A (C8 w :: cs).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_VecT ()) [] "h01Ah11mh23cs1h33cs2h44segsh51Hh62H1h72H2h82csh91wp;1p;3p;4p;2p;5p10000p4p7210p1000\p4p710p8g001:j11Tg001_j1;Tg002=j16Tg002`j1<Tg003Bj17Tg003bj19Tg004_j1>Tg005?j38Tg005_j40Tg006]j1=Tg007;j22Tg007Xj33Tg0085j15Tg0096j14Tg009VR0j2:Tg00:1j5@Tg00;4j4?Tg00;O#1#1#1R1#1#1#1#;#6R2%;1#6#<[R3g00<4R4g00<RR5#7R6g00=OR7f3R8f2R9f1R:#9%>5R;585C0P7f4R<%=1,28P:C0g00>F#7R1P0P<P8P9f0R0935:C0f5R=P<P8P9C0P=P<%59#4,28P:C0':R>[P<P8P9P:C0P<P8%5:#4,29P0C0':P=P<P8A359:C0[R?f6R@P=P<A3589C0\>P<P8P9P:P0D@P0n2001000000120000000X36X26X04X13W4P?^36^26^04^13^41P0P7P@P=%9<=85;R;P8P7P@P=P;C0P7P@%5;#4,2=P8C0P9P:C?O6b5W7W6W8X92W0W1o"). Qed.

Lemma shvis_nil : forall m, shvis m 0 0.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_VecT ()) [] "h01Hh12Hah26__sat1h31zh47__arithh54__ffh66__sat0h78__varmaph85__with91mp;1p;2p;3p;4p;7p;6g00?Ej1TTg00@Aj1>Tg00A8j24Tg00ARj16Tg001:j13Tg006]j15Tg00B7j37Tg00BQj1BTg00CMj4<Tg00DHj2?Tg00E0j29Tg00ELj22Tg00Ehj2STg00FEj3RTg00Fij2OTg004_j1NTg003Bj1LTg00GJj1GTg00Ghj1FTg00HFj1ETg00I1j28Tg00ITj4:Tg001_j1DTg00J?j3CTg00Jbj7HTg00KFj2ITg00Khj2JTg00LTj3KTg00M3j4ATg009Vj2@Tg00Mej4MTg00Nfj6=Tg00OBj3PTg00P<j7QTf0R0#6#6p=1%30#3p=0f1R1g00P`R2g00Q?R3P3g00Q_R4P0g00R?FQp=;g00R_g00<4R5g00SWR6#T#>R7'4g00;OR8#6#1#1#1#1#1#1#1#3#0#0#0#0#0#0#0#5R9=757P5P9g00=OR:f2R;P0%B6#>R<C<X35145<A759<P5P9P:f3P9P0C<X35P:P;P9%38R8#5R:%38#0#0R8#5R='?196:R>126=1S:=R?,96[R@[126:RAg00T5RBAR:=1UW1126?\B^1AP1g00TQ1O6:'4P>eO1P@g00U7R@#N%L@%G5%F5%E5R@P2P3P3P4P51856g00UcR31859R2C:,;@P5P2P3185:%D85C5C:,;@FH1I@4P0P;g00VJR@g00VjR4'41J0;=7@4dAK561CAb5b7b81269129?'@P0b4b2b6b2CMP<P0E=b0P7P0E=b0AP066eW9o"). Qed.

Lemma w_negadd : forall p q, 0 <= p <= q -> q < 2 ^ 64 ->
  alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 p)) (Z_to_bv 64 q) = Z_to_bv 64 (q - p).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_VecT ()) [] "h01zh16__sat4h24__x1h34__x2h41Hh57__arithh64__ffh76__sat3h88__varmaph95__with:2Hah;2b1h<2b2h=1nh>2H1h?2H2h@7fv_listhA8hyp_listhB3lmphC1phD1qp&0p;2p;1p;3p;4p;7p;6p;:p;<p;8g00ELj29Tg009VR0j2ITg001:j1;Tg006]j1JTg00Ehk205Tg00E0j2?Tg002=j1@Tg00B7j37Tg00WJj25Tg00X4j3bTg001_j1_Tg00XXj1]Tg00Y6j2=Tg00Y\j4~Tg00ZFj3wTg00ZnR1j2>Tg00[Kj3sTg007;R2j26Tg00\0j21Tg00\VR3j23Tg00]3j20Tg00A8j2ATg00]Sj1gTg00^=j2KTg004_j1OTg003Bj1DTg005?j3BTg00^]j2UTg00_Gj3TTg00`1j2STg00`[j1aTg00a9j3`Tg00acj3RTg00bMj3QTg00c7j1\Tg00c_j4[Tg00dEk704Tg00DHk202Tg00FEj3}Tg00Fij2zTg00GJj1xTg00Ghj1vTg00HFj1uTg00I1j2YTg00J?j3tTg00ITj4FTg00e4j6rTg00KFj2qTg00Khj2pTg00LTj3oTg00M3j4nTg00eXj4mTg00Nfj6WTg00f9j4kTg00fbj1MTg00gAj2CTg00gjj3NTg00hSj2XTg00i?j2jTg00i]j4iTg00j;j2VTg00j^j1hTg00k@j3ZTg00kcj1<Tg00lkj2HTg00mZj3fTg00nHj3eTg00nmj3yTg00o[l:dTg010Ll<{Tg00P<j7|Tg000\j6cTg00Jbk700Tg0119k801Tg00<4R4f1R5f0R637p=4f3R7f2R8'6/05=746p=8P4g00SWR9P5P2P3P1g011]R:g012:R;g012WR<P6M:dp=^P4P9P8P2P3P1P:P;P<g0138R<P5P6M<{p=P1085=746p>03P5g00P`R:g00Q?R1P1g00Q_R3P6g00R?F|p=:P4f4R2P7P8P5P6Ecp=21685/06p=lP4P5g00UcP6CFp=EP8P:P1P1P3P5P6K00p=LP7P:P1P1P3P8P5P6L01p=G1995R=1956'Ig00;OR>#;R?#JR@%;?#;#;#;#;RA#JRB+05RC,?5RDg013gRE%@6RF%@5RGP0%@8?75615781575'4R0[15851586'4%@7?785[RH%@2?778\0Ab856P6n2001000000120000000W<W;W=PH^<G^;F^=EP6%_ARAg014EPAg0151%]>RE,=ARF1=A2RGC~1=A7RH3wR01>72RI,=ARJAsAFGRK,5ARL15AHRM'6,1Af5RN,>2RO,=A,5ARP,46X0415AFRQ15AGRR'3,1A166R,1A/4PX0411AERS1=AN,5A,36,1A/6R,1A/4PX0411A2RT13S6,1A/6R,1A/4PX0411A7RU11ANRV,3S,1ARW/66,1A/4PX0411AIRP16WT,1A/46X0413STRW,1ARX/6URY/0C11AORZ,46X0410WCP6PTPCPZC8X0410ECR[136V/0CPTPCPZC8X04102CRV13[6/0CR\PTPCPZC8X04107CR]10NC,3[/0CR^P6PCPZC8X0410ICP^PVPCP6C8X04P2P\PVPC10OCR\C8X04P713[N/0CP6PCP\C8X041A4[%J>R\,>CR^/4[P4P^f6RZ,36/0CPNPC1>NZR_/0CR`C8X0413^NRa/62Rb/0C146`X04%g4Rc/KcRc#O%Dc%O49B4Z9B4N%D4P<P6P51U4>R<1U4?Rc5T41S4@%aB5`4Rd9R4c5Q4Re1S4\9T4d=R4c=Q4<R<g015]g00VJRcg00VjRd'ARf1^\5g0169,K4%\4'K#DP4P;AP\6eAP\6<C[bB=7cddK04b@bA13NC,6O/4bRbePbP413ZC,6_Rbf7RO,>Z/0CR<:036CX04P`146<X041A4`10bCP_PZPC202@BR_1?9@Rb199B1?9C[R`[R<199@R\g00T5ReA}@B5UW:RB199C\e^:\R\P5g00TQ1z9@'APbeO1RbP`g00U7Re#OR;%DeRg%x4Rh%v4Ri%u4RjP:P1P1P3P41Y4@=t4AR@g016a1Y49R:CF,:jEr1qj3R3P6P8Pf1p68=7cddAo495CnRdb6b8b9A74C9g017H[P6b5b1b7b1RcCmD213^Z/6NP6EWb410aC?l2CPaP2PCPcCkD2P[P6EWb4P]P_P<PBP\PbP`g017eR]#MR[#MRc,C41C4[1C4]5N4R]5N4g018DR['X=Be;PgP41j48P5PhCiRhPiPjP41V4>R>g0190RaP@CF,:jR^%h1R1Pj1V4?R?,E:,:j1E?>,:j5LjP11E:>,:jR:=Lj^R^CGCGP3Pdb6b8b9X24X341?6C1998R91985'I1?8C,I9R9[[^24^34P6f8RfPOPNPZO4b5b1b7b19Z7CD2PVP_P<PBP\PbP`%Mc,C4=N4]/X[=Be;PgPhPiPjP4P?PaP@CF,:jP1Pj1E>?,:j9Lj:P1P^CGCGP3Pdb6b8b9X24X341958,I=P9[\D^24^34P6POPfPNPZO4b5b1b7b19Z2CD2PP%<ID2PU%<7D2PT%<2D2PS%<ED2PX%<WD211AY%<YD215AJRJ1HAID2PM1HA7D2PR1HA2D2PQ1HAED2PLAfAFGD2AeAKH,5AAyAKHD215A0/4JeO4b4W?W>XD4XC4o"). Qed.

Lemma w_sra4 : forall k, 0 <= k -> 4 * k < 2 ^ 63 -> alu64 ALU_SRA (Z_to_bv 64 (4 * k)) (Z_to_bv 64 2) = Z_to_bv 64 k.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_VecT ()) [] "h01zh16__sat4h21Hh32Hah47__arithh54__ffh66__sat3h78__varmaph85__with94__x1h:6__sat6h;2b1h<2b2h=1nh>2H1h?2H2h@6__sat5hA1kp;1p;2p;3p;4p;6p;7p;8g001:j1;Tg006]j1CTg00\Vj25Tg00ARj1=Tg00Ehj2ITg00E0j29Tg002=j1>Tg00B7j3:Tg00WJj21Tg00X4j3TTg001_j1JTg00Y6j2@Tg00ZFj3tTg019Wj2pTg01:?j3jTg01:dj22Tg00\0j23Tg01;Dj2HTg00A8j2?Tg007;j2ATg00Znj2BTg00]3j28Tg00DHj2MTg00FEj3LTg00Fij2[Tg004_j1ZTg003Bj1YTg00i?j2XTg00Ghj1WTg00HFj1VTg00I1j2ETg00j;j2UTg01;kj3STg00J?j3KTg01<Nj3RTg01=1j3QTg00ITj4<Tg00KFj2wTg00Khj2vTg00LTj3uTg00M3j4sTg01=Tj2DTg00GJj1qTg00e4j6oTg01>1j3nTg01>Rj2iTg00Nfj6GTg01?4j3gTg00gAj2OTg00fbj1NTg00gjj3fTg00hSj2eTg01?]j2dTg005?j3cTg00j^j1bTg00Jbj7hTg009VR0j2aTg00k@j3kTg00lkj2`Tg01@Ij2lTg01A6j3mTg01A_j3_Tg00ELj2^Tg00P<j7]Tg000\j6\Tg0119j8rTg00SWR1f0R2'^p=4g00<4R3f1R4;:2p=0P4g00P`R5g00Q?R6P6g00Q_R7P2g00R?F]p=6P3f4R8f3R9f2R:P4P2E\p=7P3P4g00UcP2C<p=FP9P5P6P6P7P:P4P2Grp=P%42g00;OR;#;R<#;R=#CR>/54%C<R<%=;#=#=#=#=R?#CR@'IRA'9g013gRB%>2RC%>4RDP0%>:?:42119:1194'0R0[11:411:2'0%>9?::4[RE%>8?:9:\0AT:42P2n2001000000120000000W<W;W=PE^<D^;C^=BP2%;=#;#;#;R=#JRBg01BQ15>9RC,@BRD1@B<RE3tR01@B9RF1pBDRG1@B@9jBERE,1BRH'2,3B1@B8,1BRI,02X031HBC122H,3B/0IX0313B915>8RI,HBRJ/2H,3B/02X031?3<10<HRKdPKP3P<f5RK,5>RL,HB/22,3B13BK'0X031AIARM1B2A/2<%C=R=,I<RN'818KN'0X031M<@RO191<RP%4@191A[RQ[RR%4<RSg00T5RTAL<@4UW3R@%4A\T^3SRUP4g00TQ1[1<'?PPeRVO1RWPQg00U7RX#ZRY%YXRZ1X34R[%W3R\%V3R]P31E3>R^1U3;R;5S3R_g016aR`1E3<Ra%J?5K3R?9R3_Rb=Q3?C<'61w]7RcP2P:g00VJRdg00VjRe'?1v2:=:dedAu314CsReb5b7b8X9315>2Rd1AdA/BA'0^93P2f8O1b4b1b6b11BMA,0IP3PL122</8Nf6RI/8NRf'0X031I<<Rg,DLRh182NRi/0fX0315K>Rj1D2g,0IX03PK10I2X031?3K1Dj>POPRP@PUPWPQPYPZ%q3RjP\P]P5P6P6P7P3P^P`1E31R`C<,6]EoPcPeb5b7b8A:3>1g017H[P2b4b1b6b19nK>D7PL1i>KD710KhP3PIf7/8N,0iX031?3f15>I/DgP2EGb212L<POPRP@PUPWPQPYPZPjP\1F`a,6]PcPeb5b7b8PSP2b4b1b6b19gL<D71ALA/BAP2EGb218MNPOPRP@PU1M<=%4=191N[R1\PAL<=4VTX3S%4N\T^3SPWP1P8PVO1PQg017eRQ,O3RV%NQ#N,O39f3Vg018D'e'd=cXYPZP[P\P]P3P_g0190R_P?C<,6]%b6R?P]1F`;,6]P?P]P5P6P6P71F`b,6]P3PbP_AK3aBC<,6]FhCPCPPcPeb5b7b8X9319dA%4415>:/AARA#419AN'a[[^93P2f;f9f:O3b4b:b1b6b1b@b:9kMND712J<,3B13B8'0ePHP2EGb211BFRF1`B9D7PG1lBCD7AmBDE,1BA_BDED711B0/0FeO4b2W?W>XA3o"). Qed.

Section VFill.
  Context {HCEIL : HeapCeil}.

  Definition VFILL : Z := 0xe9624.
  Definition VFILL_LP : Z := 0xe96b0.
  Definition VFILL_EX : Z := 0xe9700.
  Definition VFILL_RET : Z := 0xe9718.

  Definition vf_sha (sb : Z) : word :=
    alu64 ALU_ADD (alu64 ALU_SRL (alu64 ALU_ADD (Z_to_bv 64 sb) (Z_to_bv 64 16)) (Z_to_bv 64 3)) (Z_to_bv 64 LbB_Kit.SHBASE).

  Ltac vf_dj := cbn [sc_denot]; unfold flat, estart, elenZ; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off a_base]; lia.

  Lemma vf_pro : forall (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (sb e al n spz : Z),
    1 <= n <= 2 ^ 24 -> 2 ^ 45 <= spz <= 2 ^ 47 -> spz <= sb -> sb + 40 <= 2 ^ 47 ->
    rw_cells asegs m (sb + 16) [C8 (wz e)] -> rw_cells asegs m (sb + 32) [C8 (wz al)] -> 0 < al < 2 ^ 64 ->
    sh0 m (sb + 16) -> sh0 m (sb + 32) -> 0 < e -> e mod 4 = 0 -> e + 4 * n <= 2 ^ 47 ->
    wr_at asegs m (spz - 16) 16 -> ACONST m ->
    exists M1,
      CatSim.msteps asegs
        (MS (mkR ra (wz spz) gp tp t0 t1 t2 s0 s1 (wz sb) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz VFILL) fc None m (seg_rom asegs))
        (MS (mkR ra (wz (spz - 16)) gp tp (wz 0) (wz (2 ^ 64 - 4)) t2 s0 s1 (wz (sb + 16)) (wz e) (wz (e + 4 * n))
                 (vf_sha sb) (wz LbB_Kit.SHBASE) (wz e) (wz (4 * n)) (wz al) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz VFILL_LP) fc None M1 (seg_rom asegs))
      /\ munch [(spz - 8, spz)] m M1 /\ wmono asegs m M1 /\ (forall lo hi, stk asegs m lo hi -> stk asegs M1 lo hi)
      /\ rw_cells asegs M1 (spz - 8) [C8 ra].
  Proof.
    intros until spz. intros Hn SPR SB SBH CE CA AL SH16 SH32 E0 E4 EH WS AC.
    pose proof (ACONST_shbase m AC) as [CG CS].
    remember (mkR ra (wz spz) gp tp t0 t1 t2 s0 s1 (wz sb) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      as R eqn:HR0.
    pose (E := Eseed R [wz sb; wz spz; wz n; wz e; wz al]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (11%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (HK : know_ok asegs E m
      (kn_fix 30 [VFILL_LP] (SCR [false] [] []) VFILL (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (11%bv, EVar 34)])
        [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL); KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit LbB_Kit.SHBASE);
          KWord (SA (EVar 32) 16) 8 (EVar 35); KWord (SA (EVar 32) 32) 8 (EVar 36); KWr (SA (EVar 33) (-16)) (ELit 16);
          KRange (EVar 34) 1 (2 ^ 24); KRange (EVar 35) 1 (2 ^ 47); KAlign (EVar 35) 4; KRange (EVar 36) 1 (2 ^ 64 - 1);
          KRange (EVar 32) 0 (2 ^ 47) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m AGOT_SHBASE _ 0%nat (C8 (wz ASHBASE_CELL)));
          [exact CG | reflexivity | reflexivity | lia | reflexivity | unfold AGOT_SHBASE; lia | unfold AGOT_SHBASE; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m ASHBASE_CELL _ 0%nat (C8 (wz LbB_Kit.SHBASE)));
          [exact CS | reflexivity | reflexivity | lia | reflexivity | unfold ASHBASE_CELL; lia | unfold ASHBASE_CELL; lia | reflexivity]. }
      apply Forall_cons. { kword_cell CE 0%nat (C8 (wz e)). }
      apply Forall_cons. { kword_cell CA 0%nat (C8 (wz al)). }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WS | unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
      do 5 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; first [lia | split; [lia | rewrite u64_of_Z by lia; exact E4]]|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R VFILL m (seg_rom asegs) HR HK 100%nat [VFILL_LP] (SCR [false] [] []) 40%N.
    { split_scs.
      all: first [ vf_dj | sc_shdj
                 | cbn [sc_denot]; evs; rewrite ?w_mul, ?w_add by lia; rewrite ?br_ltu by lia; bool_lia ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 2%bv L2. rreg HR' 5%bv L5. rreg HR' 6%bv L6. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rreg HR' 13%bv L13. rreg HR' 14%bv L14. rreg HR' 15%bv L15. rreg HR' 16%bv L16. rreg HR' 17%bv L17.
    unfold wz in L2, L10, L11, L12, L15, L16, L17.
    rewrite (w_addm spz (-16)) in L2 by lia. rewrite (w_add sb 16) in L10 by lia.
    rewrite (w_mul 4 n) in L12, L16 by lia. rewrite (w_add (4 * n) e) in L12 by lia.
    replace (4 * n + e) with (e + 4 * n) in L12 by lia. replace (spz + -16) with (spz - 16) in L2 by lia.
    exists M1. split.
    { rewrite !mkst_MS, HRe, L2, L5, L6, L10, L11, L12, L13, L14, L15, L16, L17 in Hms. exact Hms. }
    assert (WA8 : wr_at asegs m (spz - 8) 8).
    { destruct WS as (W1 & W2 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (spz - 8 + i) with (spz - 16 + (8 + i)) by lia. apply W. lia. }
    split.
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    split; [subst M1; apply wmono_mem_denot|].
    split; [intros lo0 hi0 ST0; subst M1; apply stk_mem_denot; exact ST0|].
    subst M1. lgcell Hlf WA8 0%nat.
  Qed.

  Lemma vf_sc_meta : forall E M (a : saddr) (ev : expr) (A v : Z),
    adenot E a = Z_to_bv 64 A -> mrd asegs M (wa A) = Some (b8 v) -> 0 <= v < 128 -> edenot E ev = Z_to_bv 64 v ->
    sc_denot asegs M E (SCReadBase a 1 true ev).
  Proof.
    intros E M a ev A v Ha Hm Hv He. cbn [sc_denot]. exists [b8 v]. split.
    - rewrite Ha. exact (rdn1_of_mrd asegs M (wa A) (b8 v) Hm).
    - rewrite He. f_equal. unfold extz. cbn [bytes_le_to_Z]. unfold b8. rewrite Z_to_bv_unsigned.
      unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
      change (2 ^ Z.of_N (8 * N.of_nat 1)) with 256. change (Z.of_N 8) with 8. change (0 ≪ 8) with 0.
      rewrite Z.lor_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia.
      change (256 / 2) with 128. rewrite Z.mod_small by lia. lia.
  Qed.

  Ltac vf_it_post E mk cur rem HF HR0 WA Hlf Hms HR' :=
    match goal with HK : know_ok _ _ _ _ |- _ => clear HK end;
    let M1 := fresh "M1" in
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E mk lg) in Hms; set (M1 := mem_denot E mk lg) in Hms end end;
    let HF1 := fresh "HF1" in pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1;
    let HRe := fresh "HRe" in readback HR' HF1 HR0 HRe;
    let L5 := fresh "L5" in let L6 := fresh "L6" in let L11 := fresh "L11" in let L14 := fresh "L14" in
    let L15 := fresh "L15" in let L16 := fresh "L16" in let L17 := fresh "L17" in
    rreg HR' 5%bv L5; rreg HR' 6%bv L6; rreg HR' 11%bv L11; rreg HR' 14%bv L14; rreg HR' 15%bv L15;
    rreg HR' 16%bv L16; rreg HR' 17%bv L17;
    unfold wz in L11, L15, L16, L17;
    rewrite (w_add cur 4) in L11, L15 by lia; try (rewrite (w_addm rem (-4)) in L16 by lia;
         replace (rem + -4) with (rem - 4) in L16 by lia);
    eexists; eexists; exists M1; split;
    [ rewrite !mkst_MS, HRe, L5, L6, L11, L14, L15, L16, L17 in Hms; exact Hms | ];
    split;
    [ subst M1; apply munch_mem_denot; [exact Hlf|];
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]);
      apply Forall_nil | ];
    split; [subst M1; apply wmono_mem_denot|];
    split; [intros lo0 hi0 ST0; subst M1; apply stk_mem_denot; exact ST0|];
    subst M1; lgcell Hlf WA 0%nat.

  Lemma vf_it_n : forall (x1 x2 x3 x4 x7 x8 x9 x10 x12 x13 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (mk : mem) (cur rem al : Z),
    1 <= cur -> cur mod 4 = 0 -> cur + rem <= 2 ^ 47 -> 8 <= rem <= 2 ^ 26 -> 0 < al < 2 ^ 64 ->
    wr_at asegs mk cur 4 -> accessible mk cur 4 ->
    exists x7' x28' M',
      CatSim.msteps asegs
        (MS (mkR x1 x2 x3 x4 (wz 0) (wz (2 ^ 64 - 4)) x7 x8 x9 x10 (wz cur) x12 x13 (wz LbB_Kit.SHBASE) (wz cur) (wz rem) (wz al)
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wz VFILL_LP) fc None mk (seg_rom asegs))
        (MS (mkR x1 x2 x3 x4 (wz 0) (wz (2 ^ 64 - 4)) x7' x8 x9 x10 (wz (cur + 4)) x12 x13 (wz LbB_Kit.SHBASE) (wz (cur + 4)) (wz (rem - 4)) (wz al)
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28' x29 x30 x31) F (wz VFILL_LP) fc None M' (seg_rom asegs))
      /\ munch [(cur, cur + 4)] mk M' /\ wmono asegs mk M' /\ (forall lo hi, stk asegs mk lo hi -> stk asegs M' lo hi)
      /\ rw_cells asegs M' cur [C4 (wz 0)].
  Proof.
    intros until al. intros C1 C4m CH RM AL WA AX.
    pose proof AX as (AX0 & AX1 & AXv).
    destruct (AXv (cur + 3) ltac:(lia)) as (v & V8 & RDv & OKv).
    assert (Hsh : sh (cur + 3) = sh cur) by (unfold sh; f_equal; Z.div_mod_to_equations; lia).
    rewrite Hsh in RDv.
    remember (mkR x1 x2 x3 x4 (wz 0) (wz (2 ^ 64 - 4)) x7 x8 x9 x10 (wz cur) x12 x13 (wz LbB_Kit.SHBASE) (wz cur) (wz rem) (wz al)
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    destruct (Z.eq_dec v 0) as [V0|V0].
    - subst v.
      assert (S0 : sh0 mk cur) by (apply sh0_of_mrd; [lia | exact RDv]).
      pose (E := Eseed R [wz cur; wz rem; wz al]).
      assert (HR : regs_ok E (srs sr_id [(11%bv, EVar 32); (15%bv, EVar 32); (16%bv, EVar 33); (17%bv, EVar 34); (5%bv, ELit 0); (6%bv, ELit (2 ^ 64 - 4)); (14%bv, ELit LbB_Kit.SHBASE)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E mk [KRange (EVar 32) 1 (2 ^ 47); KAlign (EVar 32) 4; KRange (EVar 34) 1 (2 ^ 64 - 1); KWr (SA (EVar 32) 0) (ELit 4); KRange (EVar 33) 8 (2 ^ 26); KWord (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) LbB_Kit.SHBASE) 1 (ELit 0)]).
      { unfold know_ok.
        do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|]).
        apply Forall_cons.
        { eapply kwr_of_wr_at; [exact WA | unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                               | unfold estart, elenZ; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                               | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
        apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R VFILL_LP mk (seg_rom asegs) HR HK 40%nat [VFILL_LP; VFILL_EX] (SCR [] [] []) 36%N.
      { split_scs. }
      vf_it_post E mk cur rem HF HR0 WA Hlf Hms HR'.
    - pose (E := Eseed R [wz cur; wz rem; wz al; wz v]).
      assert (HR : regs_ok E (srs sr_id [(11%bv, EVar 32); (15%bv, EVar 32); (16%bv, EVar 33); (17%bv, EVar 34); (5%bv, ELit 0); (6%bv, ELit (2 ^ 64 - 4)); (14%bv, ELit LbB_Kit.SHBASE)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E mk [KRange (EVar 32) 1 (2 ^ 47); KAlign (EVar 32) 4; KRange (EVar 34) 1 (2 ^ 64 - 1); KWr (SA (EVar 32) 0) (ELit 4); KRange (EVar 33) 8 (2 ^ 26); KRange (EVar 35) 1 7]).
      { unfold know_ok.
        do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|]).
        apply Forall_cons.
        { eapply kwr_of_wr_at; [exact WA | unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                               | unfold estart, elenZ; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                               | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
        do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|]).
        apply Forall_nil. }
      xrun_at (PropExec.mkFP F fc) asegs R VFILL_LP mk (seg_rom asegs) HR HK 40%nat [VFILL_LP; VFILL_EX] (SCR [true] [] []) 35%N.
      { split_scs.
        - cbn [sc_denot]. evs. unfold wz. rewrite (land7_val cur) by lia. rewrite (w_add (cur mod 8) 3) by (Z.div_mod_to_equations; lia).
          rewrite br_lts_small by (Z.div_mod_to_equations; lia). apply Z.ltb_lt.
          destruct OKv as [OKv|OKv]; [lia|]. Z.div_mod_to_equations. lia.
        - eapply vf_sc_meta; [| exact RDv | lia | evs; reflexivity].
          pose proof (sh_below_app cur ltac:(unfold AAPP_HI; lia)) as SB1. pose proof (sh_above_image cur ltac:(lia)) as SB2.
          apply adenot_of_estart; [| unfold AHI_LO, AIMG_TOP in *; lia].
          erewrite estart_sh; [apply sh_kit | evs; reflexivity | lia]; lia. }
      vf_it_post E mk cur rem HF HR0 WA Hlf Hms HR'.
  Qed.

  Lemma vf_it_l : forall (x1 x2 x3 x4 x7 x8 x9 x10 x12 x13 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (mk : mem) (cur rem al : Z),
    1 <= cur -> cur mod 4 = 0 -> cur + rem <= 2 ^ 47 -> rem = 4 -> 0 < al < 2 ^ 64 ->
    wr_at asegs mk cur 4 -> accessible mk cur 4 ->
    exists x7' x28' M',
      CatSim.msteps asegs
        (MS (mkR x1 x2 x3 x4 (wz 0) (wz (2 ^ 64 - 4)) x7 x8 x9 x10 (wz cur) x12 x13 (wz LbB_Kit.SHBASE) (wz cur) (wz rem) (wz al)
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wz VFILL_LP) fc None mk (seg_rom asegs))
        (MS (mkR x1 x2 x3 x4 (wz 0) (wz (2 ^ 64 - 4)) x7' x8 x9 x10 (wz (cur + 4)) x12 x13 (wz LbB_Kit.SHBASE) (wz (cur + 4)) (wz (rem - 4)) (wz al)
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28' x29 x30 x31) F (wz VFILL_EX) fc None M' (seg_rom asegs))
      /\ munch [(cur, cur + 4)] mk M' /\ wmono asegs mk M' /\ (forall lo hi, stk asegs mk lo hi -> stk asegs M' lo hi)
      /\ rw_cells asegs M' cur [C4 (wz 0)].
  Proof.
    intros until al. intros C1 C4m CH RM AL WA AX.
    subst rem.
    pose proof AX as (AX0 & AX1 & AXv).
    destruct (AXv (cur + 3) ltac:(lia)) as (v & V8 & RDv & OKv).
    assert (Hsh : sh (cur + 3) = sh cur) by (unfold sh; f_equal; Z.div_mod_to_equations; lia).
    rewrite Hsh in RDv.
    remember (mkR x1 x2 x3 x4 (wz 0) (wz (2 ^ 64 - 4)) x7 x8 x9 x10 (wz cur) x12 x13 (wz LbB_Kit.SHBASE) (wz cur) (wz 4) (wz al)
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    destruct (Z.eq_dec v 0) as [V0|V0].
    - subst v.
      assert (S0 : sh0 mk cur) by (apply sh0_of_mrd; [lia | exact RDv]).
      pose (E := Eseed R [wz cur; wz 4; wz al]).
      assert (HR : regs_ok E (srs sr_id [(11%bv, EVar 32); (15%bv, EVar 32); (16%bv, EVar 33); (17%bv, EVar 34); (5%bv, ELit 0); (6%bv, ELit (2 ^ 64 - 4)); (14%bv, ELit LbB_Kit.SHBASE)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E mk [KRange (EVar 32) 1 (2 ^ 47); KAlign (EVar 32) 4; KRange (EVar 34) 1 (2 ^ 64 - 1); KWr (SA (EVar 32) 0) (ELit 4); KRange (EVar 33) 4 4; KWord (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) LbB_Kit.SHBASE) 1 (ELit 0)]).
      { unfold know_ok.
        do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|]).
        apply Forall_cons.
        { eapply kwr_of_wr_at; [exact WA | unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                               | unfold estart, elenZ; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                               | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
        apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R VFILL_LP mk (seg_rom asegs) HR HK 40%nat [VFILL_LP; VFILL_EX] (SCR [] [] []) 36%N.
      { split_scs. }
      vf_it_post E mk cur 4 HF HR0 WA Hlf Hms HR'.
    - pose (E := Eseed R [wz cur; wz 4; wz al; wz v]).
      assert (HR : regs_ok E (srs sr_id [(11%bv, EVar 32); (15%bv, EVar 32); (16%bv, EVar 33); (17%bv, EVar 34); (5%bv, ELit 0); (6%bv, ELit (2 ^ 64 - 4)); (14%bv, ELit LbB_Kit.SHBASE)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E mk [KRange (EVar 32) 1 (2 ^ 47); KAlign (EVar 32) 4; KRange (EVar 34) 1 (2 ^ 64 - 1); KWr (SA (EVar 32) 0) (ELit 4); KRange (EVar 33) 4 4; KRange (EVar 35) 1 7]).
      { unfold know_ok.
        do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|]).
        apply Forall_cons.
        { eapply kwr_of_wr_at; [exact WA | unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                               | unfold estart, elenZ; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                               | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
        do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|]).
        apply Forall_nil. }
      xrun_at (PropExec.mkFP F fc) asegs R VFILL_LP mk (seg_rom asegs) HR HK 40%nat [VFILL_LP; VFILL_EX] (SCR [true] [] []) 35%N.
      { split_scs.
        - cbn [sc_denot]. evs. unfold wz. rewrite (land7_val cur) by lia. rewrite (w_add (cur mod 8) 3) by (Z.div_mod_to_equations; lia).
          rewrite br_lts_small by (Z.div_mod_to_equations; lia). apply Z.ltb_lt.
          destruct OKv as [OKv|OKv]; [lia|]. Z.div_mod_to_equations. lia.
        - eapply vf_sc_meta; [| exact RDv | lia | evs; reflexivity].
          pose proof (sh_below_app cur ltac:(unfold AAPP_HI; lia)) as SB1. pose proof (sh_above_image cur ltac:(lia)) as SB2.
          apply adenot_of_estart; [| unfold AHI_LO, AIMG_TOP in *; lia].
          erewrite estart_sh; [apply sh_kit | evs; reflexivity | lia]; lia. }
      vf_it_post E mk cur 4 HF HR0 WA Hlf Hms HR'.
  Qed.

  Lemma vf_epi : forall (x1 x3 x4 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (mk : mem) (sb en spz : Z),
    2 ^ 45 <= spz <= 2 ^ 47 -> spz <= sb -> sb + 40 <= 2 ^ 47 -> 0 <= en <= 2 ^ 47 ->
    rw_cells asegs mk (spz - 8) [C8 x1] -> wr_at asegs mk (sb + 16) 8 -> sh0 mk (sb + 16) ->
    exists M',
      CatSim.msteps asegs
        (MS (mkR x1 (wz (spz - 16)) x3 x4 x5 x6 x7 x8 x9 (wz (sb + 16)) x11 (wz en) (vf_sha sb) x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wz VFILL_EX) fc None mk (seg_rom asegs))
        (MS (mkR x1 (wz spz) x3 x4 x5 x6 x7 x8 x9 (wz (sb + 16)) (wz 0) (wz en) (vf_sha sb) x14 (wz en) x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wz VFILL_RET) fc None M' (seg_rom asegs))
      /\ munch [(sb + 16, sb + 24)] mk M' /\ wmono asegs mk M' /\ (forall lo hi, stk asegs mk lo hi -> stk asegs M' lo hi)
      /\ rw_cells asegs M' (sb + 16) [C8 (wz en)].
  Proof.
    intros until spz. intros SPR SB SBH EN CR WA SH16.
    remember (mkR x1 (wz (spz - 16)) x3 x4 x5 x6 x7 x8 x9 (wz (sb + 16)) x11 (wz en) (vf_sha sb) x14 x15 x16 x17
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose (E := Eseed R [wz en; wz spz; wz sb; x1]).
    assert (HR : regs_ok E (srs sr_id [(12%bv, EVar 32); (2%bv, EAlu ALU_ADD (EVar 33) (ELit (-16)));
                                       (10%bv, EAlu ALU_ADD (EVar 34) (ELit 16));
                                       (13%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 34) (ELit 16)) (ELit 3)) (ELit LbB_Kit.SHBASE))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; unfold vf_sha, wz;
        first [ reflexivity | rewrite (w_addm spz (-16)) by lia; replace (spz + -16) with (spz - 16) by lia; reflexivity
              | rewrite (w_add sb 16) by lia; reflexivity ]. }
    assert (HK : know_ok asegs E mk
      [ KWord (SA (EVar 33) (-8)) 8 (EVar 35);
        KWr (SA (EVar 34) 16) (ELit 8); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 34) 0 (2 ^ 47);
        KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 34) (ELit 16)) (ELit 3)) LbB_Kit.SHBASE) 1 (ELit 0) ]).
    { unfold know_ok.
      apply Forall_cons. { kword_cell CR 0%nat (C8 x1). }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WA | unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
      do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R VFILL_EX mk (seg_rom asegs) HR HK 40%nat [VFILL_RET] (SCR [] [] []) 40%N.
    { split_scs. all: vf_dj. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E mk lg) in Hms; set (M1 := mem_denot E mk lg) in Hms end end.
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rreg HR' 13%bv L13. rreg HR' 15%bv L15.
    unfold wz in L2, L10. rewrite (w_add sb 16) in L10 by lia.
    assert (WA16 : wr_at asegs mk (sb + 16) 8) by exact WA.
    exists M1. split.
    { rewrite !mkst_MS, HRe, L1, L2, L10, L11, L12, L13, L15 in Hms. exact Hms. }
    split.
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    split; [subst M1; apply wmono_mem_denot|].
    split; [intros lo0 hi0 ST0; subst M1; apply stk_mem_denot; exact ST0|].
    subst M1. lgcell Hlf WA16 0%nat.
  Qed.

  Lemma vf_ret : forall (Q : machine_state -> Prop) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
      x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (ret_pc x1) fc None m (seg_rom asegs)) ->
    evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 VFILL_RET) fc None m (seg_rom asegs)).
  Proof.
    intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HQ.
    unfold VFILL_RET. step. apply evt_done. exact HQ.
  Qed.

  Lemma vf_munch_step : forall W W' m1 m2 m3,
    munch W m1 m2 -> munch W' m2 m3 -> (forall x, outside W x -> outside W' x) -> munch W m1 m3.
  Proof. intros W W' m1 m2 m3 A B C x Hx. rewrite (B x (C _ Hx)). exact (A x Hx). Qed.

  Lemma vf_sh0_munch : forall W m m' x, sh0 m x -> munch W m m' -> 0 <= x < 2 ^ 47 -> outside W (sh x) -> sh0 m' x.
  Proof.
    intros W m m' x S MU Hx OUT. unfold sh0, shk in *. rewrite <- S.
    pose proof (sh_below_app x ltac:(unfold AAPP_HI; lia)) as SB1. pose proof (sh_above_image x ltac:(lia)) as SB2.
    rewrite (sh_kit x) by lia. unfold AHI_LO, AIMG_TOP in SB1, SB2.
    apply rdn_ext; [rewrite u64_of_Z by lia; lia|].
    intros y Hy. rewrite u64_of_Z in Hy by lia. apply MU.
    replace (bv_unsigned y) with (sh x) by lia. exact OUT.
  Qed.

  Lemma vf_sh_out : forall c d x lo hi, in_app_mem lo hi -> lo <= c -> c + d <= hi -> 0 <= x < 2 ^ 47 -> ~ (c <= sh x < c + d).
  Proof.
    intros c d x lo hi IA H1 H2 Hx. pose proof (sh_below_app x ltac:(unfold AAPP_HI; lia)) as SB.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). unfold in_app_mem, sh in *. unfold AHI_LO, AAPP_HI in *. lia.
  Qed.

  Lemma vf_iam_bound : forall lo hi, in_app_mem lo hi -> 0 <= lo /\ hi + 8 <= 2 ^ 47.
  Proof.
    intros lo hi IA. pose proof (sh_below_app 0 ltac:(unfold AAPP_HI; lia)) as SB0. pose proof (sh_above_image 0 ltac:(lia)) as SB1.
    unfold sh in SB0, SB1. rewrite Zdiv_0_l in SB0, SB1. unfold in_app_mem in IA. unfold AHI_LO, AAPP_HI, AIMG_TOP in *. lia.
  Qed.

  Lemma vf_sh_stk : forall c d x, aceil <= c -> 0 <= d -> 0 <= x < 2 ^ 47 -> ~ (c <= sh x < c + d).
  Proof. intros c d x H1 H2 Hx. pose proof (sh_below_aceil x ltac:(unfold AAPP_HI; lia)). lia. Qed.

  Lemma vf_cb_zeros : forall m A k,
    rw_cells asegs m A [CB (Z.to_nat (4 * k)) (repeat (b8 0) (Z.to_nat (4 * k)))] -> 0 <= k ->
    rw_cells asegs m (A + 4 * k) [C4 (wz 0)] ->
    rw_cells asegs m A [CB (Z.to_nat (4 * (k + 1))) (repeat (b8 0) (Z.to_nat (4 * (k + 1))))].
  Proof.
    intros m A k H1 Hk H2.
    apply rw_cells_to_CB in H2. cbn [cells_size csize Nat.add] in H2.
    change (cells_bytes [C4 (wz 0)]) with (repeat (b8 0) 4) in H2.
    replace (Z.to_nat (4 * (k + 1))) with (Z.to_nat (4 * k) + 4)%nat by lia.
    rewrite repeat_app. apply rw_cells_CB_join; [exact H1|].
    replace (A + Z.of_nat (Z.to_nat (4 * k))) with (A + 4 * k) by lia.
    exact H2.
  Qed.

  Definition vfill_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (sb e n lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(e, e + 4 * n); (sb + 16, sb + 24); (bv_unsigned sp - 16, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' e [CB (Z.to_nat (4 * n)) (repeat (b8 0) (Z.to_nat (4 * n)))]
      /\ rw_cells asegs m' (sb + 16) [C8 (wz (e + 4 * n))]
      /\ ACONST m'.

  Lemma vf_loop : forall (j : nat) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 x7 x28 : word)
      (F : bvmap 5 word) (fc : bv 32) (m mk : mem) (sb e al n lo spz k : Z),
    k + Z.of_nat j = n -> (1 <= j)%nat -> 0 <= k ->
    1 <= n <= 2 ^ 24 -> 2 ^ 45 <= spz <= 2 ^ 47 -> spz <= sb -> sb + 40 <= 2 ^ 47 -> 0 < al < 2 ^ 64 ->
    0 < e -> e mod 4 = 0 -> in_app_mem e (e + 4 * n) -> aceil <= lo -> lo <= spz - 16 ->
    (e + 4 * n <= lo \/ spz <= e) -> (e + 4 * n <= sb + 16 \/ sb + 24 <= e) ->
    aconst_ok (e, e + 4 * n) -> aconst_ok (sb + 16, sb + 24) ->
    munch [(e, e + 4 * n); (sb + 16, sb + 24); (spz - 16, spz)] m mk -> wmono asegs m mk -> mem_inv asegs mk ->
    stk asegs mk lo spz -> ACONST mk ->
    rw_cells asegs mk e [CB (Z.to_nat (4 * k)) (repeat (b8 0) (Z.to_nat (4 * k)))] ->
    wr_at asegs mk (e + 4 * k) (4 * Z.of_nat j) -> accessible mk (e + 4 * k) (4 * Z.of_nat j) ->
    rw_cells asegs mk (spz - 8) [C8 ra] -> wr_at asegs mk (sb + 16) 8 -> sh0 mk (sb + 16) ->
    evt asegs (vfill_post ra (wz spz) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sb e n lo m)
      (MS (mkR ra (wz (spz - 16)) gp tp (wz 0) (wz (2 ^ 64 - 4)) x7 s0 s1 (wz (sb + 16)) (wz (e + 4 * k)) (wz (e + 4 * n))
               (vf_sha sb) (wz LbB_Kit.SHBASE) (wz (e + 4 * k)) (wz (4 * Z.of_nat j)) (wz al)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (wz VFILL_LP) fc None mk (seg_rom asegs)).
  Proof.
    induction j as [|j IH]; intros until k; intros JK J1 K0 Hn SPR SB SBH AL E0 E4 IA CE LO DJS DJB ACE ACB
      MU WM MI ST AC CZ WR AX CR WB SH16; [lia|].
    assert (IAb : e + 4 * n + 8 <= 2 ^ 47) by (pose proof (vf_iam_bound _ _ IA); lia).
    assert (WC : wr_at asegs mk (e + 4 * k) 4).
    { destruct WR as (W1 & W2 & W). split; [lia|]. split; [lia|]. intros i Hi. apply W. lia. }
    assert (AXc : accessible mk (e + 4 * k) 4) by (eapply accessible_sub; [exact AX | lia | lia | lia]).
    assert (MOUT : forall x, 0 <= x < 2 ^ 47 -> outside [(e + 4 * k, e + 4 * k + 4)] (sh x)).
    { intros x Hx. cbn [outside]. split; [|exact I]. eapply vf_sh_out; [exact IA | lia | lia | exact Hx]. }
    destruct j as [|j].
    - replace (4 * Z.of_nat 1) with 4 in * by reflexivity.
      destruct (vf_it_l ra (wz (spz - 16)) gp tp x7 s0 s1 (wz (sb + 16)) (wz (e + 4 * n)) (vf_sha sb)
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6 F fc mk (e + 4 * k) 4 al
                  ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) eq_refl AL WC AXc)
        as (x7' & x28' & M1 & Hms1 & MU1 & WM1 & ST1 & C1).
      assert (CR1 : rw_cells asegs M1 (spz - 8) [C8 ra]) by (eapply rw_cells_transport; [exact CR | exact MU1 | exact WM1 | cbn; lia]).
      assert (WB1 : wr_at asegs M1 (sb + 16) 8) by (eapply wr_at_transport; [exact WB | exact WM1]).
      assert (SH1 : sh0 M1 (sb + 16)) by (eapply vf_sh0_munch; [exact SH16 | exact MU1 | lia | apply MOUT; lia]).
      destruct (vf_epi ra gp tp (wz 0) (wz (2 ^ 64 - 4)) x7' s0 s1 (wz (e + 4 * k + 4)) (wz LbB_Kit.SHBASE) (wz (e + 4 * k + 4))
                  (wz (4 - 4)) (wz al) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28' t4 t5 t6 F fc M1 sb (e + 4 * n) spz
                  SPR SB SBH ltac:(lia) CR1 WB1 SH1)
        as (M2 & Hms2 & MU2 & WM2 & ST2 & C2).
      eapply evt_of_msteps; [exact Hms1|]. eapply evt_of_msteps; [exact Hms2|].
      apply vf_ret. unfold vfill_post.
      assert (WMt : wmono asegs m M2) by exact (wmono_trans asegs _ _ _ WM (wmono_trans asegs _ _ _ WM1 WM2)).
      exists (wz 0), (wz (2 ^ 64 - 4)), x7', (wz (sb + 16)), (wz 0), (wz (e + 4 * n)), (vf_sha sb), (wz LbB_Kit.SHBASE),
             (wz (e + 4 * n)), (wz (4 - 4)), (wz al), x28', t4, t5, t6, M2.
      unfold wz at 1 2 3. rewrite ?u64_of_Z by lia.
      split; [reflexivity|].
      split.
      { eapply vf_munch_step; [eapply vf_munch_step; [exact MU | exact MU1 |] | exact MU2 |].
        - intros x (O1 & O2 & O3 & _). cbn [outside]. split; [lia | exact I].
        - intros x (O1 & O2 & O3 & _). cbn [outside]. split; [lia | exact I]. }
      split; [exact WMt|].
      split.
      { pose proof (msteps_mem_inv asegs _ _ Hms1 MI) as MI1. cbn [ms_mem] in MI1.
        pose proof (msteps_mem_inv asegs _ _ Hms2 MI1) as MI2. cbn [ms_mem] in MI2. exact MI2. }
      split; [exact (ST2 _ _ (ST1 _ _ ST))|].
      split.
      { replace n with (k + 1) by lia.
        eapply rw_cells_transport; [| exact MU2 | exact WM2 | cbn; lia].
        apply vf_cb_zeros; [| lia |].
        - eapply rw_cells_transport; [exact CZ | exact MU1 | exact WM1 | cbn; lia].
        - exact C1. }
      split; [exact C2|].
      eapply ACONST_frame; [| exact MU2 | exact WM2 | apply Forall_cons; [exact ACB | apply Forall_nil]].
      eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 |].
      apply Forall_cons; [|apply Forall_nil]. intros a Ha. apply ACE. cbn in Ha |- *. lia.
    - destruct (vf_it_n ra (wz (spz - 16)) gp tp x7 s0 s1 (wz (sb + 16)) (wz (e + 4 * n)) (vf_sha sb)
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6 F fc mk (e + 4 * k) (4 * Z.of_nat (S (S j))) al
                  ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) AL WC AXc)
        as (x7' & x28' & M1 & Hms1 & MU1 & WM1 & ST1 & C1).
      eapply evt_of_msteps; [exact Hms1|].
      replace (e + 4 * k + 4) with (e + 4 * (k + 1)) by lia.
      replace (4 * Z.of_nat (S (S j)) - 4) with (4 * Z.of_nat (S j)) by lia.
      apply (IH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 x7' x28' F fc m M1 sb e al n lo spz (k + 1));
        try assumption; try lia.
      + eapply vf_munch_step; [exact MU | exact MU1 |].
        intros x (O1 & O2 & O3 & _). cbn [outside]. split; [lia | exact I].
      + exact (wmono_trans asegs _ _ _ WM WM1).
      + pose proof (msteps_mem_inv asegs _ _ Hms1 MI) as MI1. cbn [ms_mem] in MI1. exact MI1.
      + exact (ST1 _ _ ST).
      + eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 |].
        apply Forall_cons; [|apply Forall_nil]. intros a Ha. apply ACE. cbn in Ha |- *. lia.
      + apply vf_cb_zeros; [| lia |].
        * eapply rw_cells_transport; [exact CZ | exact MU1 | exact WM1 | cbn; lia].
        * exact C1.
      + eapply wr_at_transport; [| exact WM1].
        destruct WR as (W1 & W2 & W). split; [lia|]. split; [lia|]. intros i Hi.
        replace (e + 4 * (k + 1) + i) with (e + 4 * k + (4 + i)) by lia. apply W. lia.
      + eapply accessible_transport; [eapply accessible_sub; [exact AX | lia | lia | lia] | exact MU1 |].
        intros x Hx. apply MOUT. pose proof AX as (_ & AXh & _). unfold AAPP_HI in AXh. lia.
      + eapply rw_cells_transport; [exact CR | exact MU1 | exact WM1 | cbn; lia].
      + eapply wr_at_transport; [exact WB | exact WM1].
      + eapply vf_sh0_munch; [exact SH16 | exact MU1 | lia | apply MOUT; lia].
  Qed.

  Lemma vfill_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (sb e al n lo : Z) (junk : list byte),
    a0 = Z_to_bv 64 sb -> a1 = Z_to_bv 64 n -> 1 <= n <= 2 ^ 24 ->
    bv_unsigned sp <= sb -> sb + 40 <= 2 ^ 47 ->
    rw_cells asegs m (sb + 16) [C8 (wz e)] -> rw_cells asegs m (sb + 32) [C8 (wz al)] -> 0 < al < 2 ^ 64 ->
    sh0 m (sb + 16) -> sh0 m (sb + 32) ->
    0 < e -> e mod 4 = 0 -> in_app_mem e (e + 4 * n) ->
    rw_cells asegs m e [CB (Z.to_nat (4 * n)) junk] -> accessible m e (4 * n) ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m -> ACONST m ->
    aconst_ok (e, e + 4 * n) -> aconst_ok (sb + 16, sb + 24) ->
    (e + 4 * n <= lo \/ bv_unsigned sp <= e) -> (e + 4 * n <= sb + 16 \/ sb + 24 <= e) ->
    evt asegs (vfill_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sb e n lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VFILL) fc None m (seg_rom asegs)).
  Proof.
    intros until junk. intros Ha0 Ha1 Hn SPB SBH CE CA AL SH16 SH32 E0 E4 IA CJ AX ST CEL LO SPH MI AC ACE ACB DJS DJB.
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof aceil_facts as ACF.
    assert (SPR : 2 ^ 45 <= spz <= 2 ^ 47) by lia.
    assert (IAb : e + 4 * n + 8 <= 2 ^ 47) by (pose proof (vf_iam_bound _ _ IA); lia).
    assert (WS : wr_at asegs m (spz - 16) 16).
    { destruct ST as (S1 & S2 & S). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (S (spz - 16 + i) ltac:(lia))). }
    rewrite Hsp, Ha0, Ha1.
    destruct (vf_pro ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sb e al n spz
                Hn SPR SPB SBH CE CA AL SH16 SH32 E0 E4 ltac:(lia) WS AC)
      as (M1 & Hms1 & MU1 & WM1 & ST1 & CR1).
    eapply evt_of_msteps; [exact Hms1|].
    assert (ACS : aconst_ok (spz - 8, spz)).
    { apply aconst_ok_high; [| right; left; lia].
      let v := eval vm_compute in (sh AIMG_TOP) in assert (Hs : sh AIMG_TOP = v) by reflexivity.
      rewrite Hs. lia. }
    replace (wz (4 * n)) with (wz (4 * Z.of_nat (Z.to_nat n))) by (f_equal; lia).
    replace (wz e) with (wz (e + 4 * 0)) by (f_equal; lia).
    apply (vf_loop (Z.to_nat n) ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 t2 t3 F fc m M1 sb e al n lo spz 0);
      try assumption; try lia.
    - intros x Hx. apply MU1. cbn [outside] in Hx |- *. destruct Hx as (O1 & O2 & O3 & _). split; [lia | exact I].
    - exact (msteps_mem_inv asegs _ _ Hms1 MI).
    - exact (ST1 _ _ ST).
    - eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | apply Forall_cons; [exact ACS | apply Forall_nil]].
    - change (Z.to_nat (4 * 0)) with 0%nat. cbn [repeat].
      split; [split; [cbn; tauto | split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]]
             | split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]].
    - eapply wr_at_transport; [| exact WM1]. replace (e + 4 * 0) with e by lia.
      replace (4 * Z.of_nat (Z.to_nat n)) with (Z.of_nat (cells_size [CB (Z.to_nat (4 * n)) junk])) by (cbn; lia).
      exact (proj2 CJ).
    - replace (e + 4 * 0) with e by lia. replace (4 * Z.of_nat (Z.to_nat n)) with (4 * n) by lia.
      eapply accessible_transport; [exact AX | exact MU1 |].
      intros x Hx. cbn [outside]. split; [|exact I]. pose proof AX as (_ & AXh & _). unfold AAPP_HI in AXh.
      pose proof (sh_below_aceil x ltac:(unfold AAPP_HI; lia)). lia.
    - eapply wr_at_transport; [exact (proj2 CE) | exact WM1].
    - eapply vf_sh0_munch; [exact SH16 | exact MU1 | lia |].
      cbn [outside]. split; [|exact I]. pose proof (sh_below_aceil (sb + 16) ltac:(unfold AAPP_HI; lia)). lia.
  Qed.
End VFill.

Section VTail.
  Context {HCEIL : HeapCeil}.

  Definition vt_sha (a : Z) : word :=
    alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 a) (Z_to_bv 64 3)) (Z_to_bv 64 LbB_Kit.SHBASE).

  Ltac vt_dj := cbn [sc_denot]; unfold flat, estart, elenZ; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off a_base]; lia.

  Lemma vt_wr_sub : forall m a n a' n', wr_at asegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at asegs m a' n'.
  Proof.
    intros m a n a' n' (W1 & W2 & W) H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi.
    replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
  Qed.

  Lemma vt_sltu0 : forall a, 0 <= a < 2 ^ 64 -> alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 a) = Z_to_bv 64 0.
  Proof. intros a Ha. apply bv_eq. rewrite u_sltu64, !u64_of_Z by lia. rewrite Z.ltb_irrefl. reflexivity. Qed.

  Lemma vt_sltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
    alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
  Proof.
    intros a b Ha Hb. apply bv_eq. rewrite u_sltu64, !u64_of_Z by lia.
    destruct (a <? b); rewrite u64_of_Z by lia; reflexivity.
  Qed.

  Lemma vt_srl62 : forall a, 0 <= a < 2 ^ 62 -> alu64 ALU_SRL (Z_to_bv 64 a) (Z_to_bv 64 62) = Z_to_bv 64 0.
  Proof.
    intros a Ha. apply bv_eq. cbn [alu64 alu]. rewrite bv_shiftr_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite (Z.mod_small a) by lia.
    replace (bv_unsigned (bv_and (Z_to_bv 64 62) (Z_to_bv 64 63))) with 62 by (vm_compute; reflexivity).
    rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
  Qed.

  Ltac vt_lg Hlf WS k :=
    eapply (rw_cells_log_nth _ _ _ k);
    [ exact Hlf | reflexivity
    | repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]); apply Forall_nil
    | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
    | eapply vt_wr_sub; [exact WS | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]
    | reflexivity | exact I
    | first [ reflexivity | evs; rewrite ?w_add by lia; reflexivity
            | evs; match goal with HRx : ?R = mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite HRx; reflexivity end ] ].

  Lemma vt_cells_tl : forall m A (w : word) cs, rw_cells asegs m A (C8 w :: cs) -> rw_cells asegs m A [C8 w] /\ rw_cells asegs m (A + 8) cs.
  Proof. intros m A w cs HC. exact (proj1 (rw_cells_app asegs m A [C8 w] cs) HC). Qed.

  Lemma vt_ret : forall (Q : machine_state -> Prop) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
      x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (ret_pc x1) fc None m (seg_rom asegs)) ->
    evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0xe9328) fc None m (seg_rom asegs)).
  Proof.
    intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HQ.
    step. apply evt_done. exact HQ.
  Qed.

  Lemma vt_sh_lo : forall a, 0 <= a -> ALOWSH_LO + 4096 <= sh a.
  Proof. intros a Ha. unfold sh. rewrite ASHADOW_BASE_val. unfold ALOWSH_LO. pose proof (Z.div_pos a 8 Ha ltac:(lia)). lia. Qed.

  Lemma vt_iam : forall A n, aapp A n -> 0 <= n -> in_app_mem A (A + n).
  Proof.
    intros A n HA Hn. pose proof aceil_facts as ((AC1 & AC2) & _).
    unfold in_app_mem. unfold aapp, aapp_lo, aapp_hi in HA. rewrite ASHADOW_BASE_val.
    unfold ALOWSH_LO, AHI_LO, AAPP_HI, AIMG_TOP in *. lia.
  Qed.

  Lemma vt_shP : forall A k, 0 <= A -> A mod 8 = 0 -> 0 <= k -> A + k <= aceil -> sh A + nsh k <= sh aceil.
  Proof.
    intros A k H0 H8 Hk HA. pose proof aceil_facts as ((AC1 & AC2) & AC3 & _).
    unfold sh, nsh. Z.div_mod_to_equations. nia.
  Qed.

  Lemma vt_r1 : forall (x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (S V n P : Z),
    1 <= n <= 2 ^ 24 -> 2 ^ 45 <= S -> S + 64 <= 2 ^ 47 -> 1 <= V -> V + 24 <= 2 ^ 47 -> 1 <= P < 2 ^ 47 -> P mod 16 = 0 ->
    (V + 24 <= S - 112 \/ S + 64 <= V) ->
    rw_cells asegs m V [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> rw_cells asegs m (S + 8) [C8 (wz P)] ->
    wr_at asegs m (S - 112) 112 ->
    sh0 m V -> sh0 m (V + 8) -> sh0 m (V + 16) -> sh0 m (S + 8) -> ACONST m ->
    exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 M1,
      CatSim.msteps asegs
        (MS (mkR x1 (wz S) x3 x4 x5 x6 x7 (wz V) (wz n) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                 x28 x29 x30 x31)
            F (wz VAPP_MEMSET_RET) fc None m (seg_rom asegs))
        (MS (mkR (wz 956436) (wz (S - 80)) x3 x4 t0 t1 t2 (wz S) (wz V) (wz P) (wz 0) (wz 0) a3 a4 a5 a6 a7
                 (wz (V + 8)) (wz (S + 8)) (wz P) (wz LbB_Kit.SHBASE) (vt_sha (V + 8)) (vt_sha (S + 8)) (vt_sha V) x25 x26 x27
                 t3 t4 t5 t6)
            F (wz AASAN_MEMCPY) fc None M1 (seg_rom asegs))
      /\ munch [(S - 112, S)] m M1 /\ wmono asegs m M1 /\ (forall lo hi, stk asegs m lo hi -> stk asegs M1 lo hi)
      /\ rw_cells asegs M1 (S - 80) [C8 x24; C8 x23; C8 x22; C8 x21; C8 x20; C8 x19; C8 x18; C8 (wz n); C8 (wz V); C8 (wz 955152)].
  Proof.
    intros until P. intros Hn S1 S2 V1 V2 P1 P16 DJ CV CB WS SV0 SV8 SV16 SS8 AC.
    pose proof (ACONST_shbase m AC) as [CG CS].
    remember (mkR x1 (wz S) x3 x4 x5 x6 x7 (wz V) (wz n) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                  x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [wz V; wz S; wz n; wz P]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (8%bv, EVar 32); (9%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (HK : know_ok asegs E m
      (kn_fix 30 [AASAN_MEMCPY] (SCR [false] [] []) VAPP_MEMSET_RET (srs sr_id [(2%bv, EVar 33); (8%bv, EVar 32); (9%bv, EVar 34)])
        [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL); KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit LbB_Kit.SHBASE);
          KWord (SA (EVar 32) 0) 8 (ELit 0); KWord (SA (EVar 32) 8) 8 (ELit 0); KWord (SA (EVar 32) 16) 8 (ELit 0);
          KWord (SA (EVar 33) 8) 8 (EVar 35); KWr (SA (EVar 33) (-112)) (ELit 112);
          KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 1 (2 ^ 47); KRange (EVar 34) 1 (2 ^ 24);
          KRange (EVar 35) 1 (2 ^ 47); KAlign (EVar 35) 16 ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m AGOT_SHBASE _ 0%nat (C8 (wz ASHBASE_CELL)));
          [exact CG | reflexivity | reflexivity | lia | reflexivity | unfold AGOT_SHBASE; lia | unfold AGOT_SHBASE; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m ASHBASE_CELL _ 0%nat (C8 (wz LbB_Kit.SHBASE)));
          [exact CS | reflexivity | reflexivity | lia | reflexivity | unfold ASHBASE_CELL; lia | unfold ASHBASE_CELL; lia | reflexivity]. }
      apply Forall_cons. { kword_cell CV 0%nat (C8 (wz 0)). }
      apply Forall_cons. { kword_cell CV 8%nat (C8 (wz 0)). }
      apply Forall_cons. { kword_cell CV 16%nat (C8 (wz 0)). }
      apply Forall_cons. { kword_cell CB 0%nat (C8 (wz P)). }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WS | unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
      do 5 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; first [lia | split; [lia | rewrite u64_of_Z by lia; exact P16]]|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R VAPP_MEMSET_RET m (seg_rom asegs) HR HK 220%nat [AASAN_MEMCPY] (SCR [false] [] []) 40%N.
    { split_scs.
      all: first [ vt_dj | sc_shdj
                 | cbn [sc_denot]; evs; rewrite ?w_mul, ?w_add by lia; rewrite ?br_ltu by lia; bool_lia
                 | cbn [sc_denot]; evs; unfold wz; rewrite vt_sltu0 by lia; reflexivity ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rreg HR' 12%bv L12. rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 21%bv L21. rreg HR' 22%bv L22.
    rreg HR' 23%bv L23. rreg HR' 24%bv L24.
    unfold wz in L2, L18, L19, L22, L23, L24.
    rewrite (w_addm S (-80)) in L2 by lia. replace (S + -80) with (S - 80) in L2 by lia.
    rewrite (w_add V 8) in L18 by lia. rewrite (w_add S 8) in L19 by lia.
    rewrite (w_add V 8) in L22 by lia. rewrite (w_add S 8) in L23 by lia.
    do 12 eexists. exists M1. split.
    { rewrite !mkst_MS, HRe, L1, L2, L8, L9, L10, L11, L12, L18, L19, L20, L21, L22, L23, L24 in Hms. exact Hms. }
    split.
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    split; [subst M1; apply wmono_mem_denot|].
    split; [intros lo0 hi0 ST0; subst M1; apply stk_mem_denot; exact ST0|].
    subst M1.
    apply rw_cells_cons8; [vt_lg Hlf WS 3%nat|]. apply rw_cells_cons8; [vt_lg Hlf WS 4%nat|].
    apply rw_cells_cons8; [vt_lg Hlf WS 5%nat|]. apply rw_cells_cons8; [vt_lg Hlf WS 6%nat|].
    apply rw_cells_cons8; [vt_lg Hlf WS 7%nat|]. apply rw_cells_cons8; [vt_lg Hlf WS 8%nat|].
    apply rw_cells_cons8; [vt_lg Hlf WS 9%nat|]. apply rw_cells_cons8; [vt_lg Hlf WS 10%nat|].
    apply rw_cells_cons8; [vt_lg Hlf WS 11%nat|]. vt_lg Hlf WS 12%nat.
  Qed.

  Lemma vt_r2 : forall (x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 y18 y19 y20 y21 y22 y23 y24 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (S V n P : Z),
    1 <= n <= 2 ^ 24 -> 2 ^ 45 <= S -> S + 64 <= 2 ^ 47 ->
    (7241728 <= V /\ V + 24 <= 2147446784) \/ 17594333495296 <= V -> V + 24 <= 2 ^ 47 ->
    1 <= P -> P + 4 * n <= 2 ^ 47 -> P mod 16 = 0 ->
    (V + 24 <= S - 112 \/ S + 64 <= V) ->
    rw_cells asegs m (S - 80) [C8 y24; C8 y23; C8 y22; C8 y21; C8 y20; C8 y19; C8 y18; C8 (wz n); C8 (wz V); C8 (wz 955152)] ->
    rw_cells asegs m V [C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    rw_cells asegs m (S + 16) [C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))] ->
    wr_at asegs m (S - 80) 112 -> wr_at asegs m V 24 ->
    sh0 m (S + 8) -> sh0 m V -> sh0 m (V + 8) -> sh0 m (S + 16) -> sh0 m (V + 16) -> sh0 m (S + 24) -> sh0 m S ->
    ACONST m ->
    exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 M3,
      CatSim.msteps asegs
        (MS (mkR (wz 956436) (wz (S - 80)) x3 x4 x5 x6 x7 (wz S) (wz V) (wz P) x11 x12 x13 x14 x15 x16 x17
                 (wz (V + 8)) (wz (S + 8)) (wz P) (wz LbB_Kit.SHBASE) (vt_sha (V + 8)) (vt_sha (S + 8)) (vt_sha V) x25 x26 x27
                 x28 x29 x30 x31)
            F (wz 956436) fc None m (seg_rom asegs))
        (MS (mkR (wz 958128) (wz (S - 16)) x3 x4 t0 t1 t2 (wz V) (wz n) (wz P) (wz (P + 4 * n)) (wz (P + 4 * n)) (wz (P + 4 * n))
                 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 x25 x26 x27 t3 t4 t5 t6)
            F (wz AANNOTATE_CC) fc None M3 (seg_rom asegs))
      /\ munch [(S - 80, S + 32); (V, V + 24)] m M3 /\ wmono asegs m M3 /\ (forall lo hi, stk asegs m lo hi -> stk asegs M3 lo hi)
      /\ rw_cells asegs M3 V [C8 (wz P); C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))]
      /\ rw_cells asegs M3 (S - 16) [C8 (wz V); C8 (wz 955152)]
      /\ rw_cells asegs M3 S [C8 (wz 0); C8 (wz 0); C8 (wz 0)].
  Proof.
    intros until P. intros Hn S1 S2 VB V2 P1 PE P16 DJ CF CV CE WS WV SS8 SV0 SV8 SS16 SV16 SS24 SS0 AC.
    pose proof (ACONST_shbase m AC) as [CG CS].
    remember (mkR (wz 956436) (wz (S - 80)) x3 x4 x5 x6 x7 (wz S) (wz V) (wz P) x11 x12 x13 x14 x15 x16 x17
                  (wz (V + 8)) (wz (S + 8)) (wz P) (wz LbB_Kit.SHBASE) (vt_sha (V + 8)) (vt_sha (S + 8)) (vt_sha V) x25 x26 x27
                  x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [wz V; wz S; wz n; wz P; wz (P + 4 * n); y18; y19; y20; y21; y22; y23; y24]).
    assert (HR : regs_ok E (srs sr_id [(1%bv, ELit 956436); (2%bv, EAlu ALU_ADD (EVar 33) (ELit (-80))); (8%bv, EVar 33);
                                       (9%bv, EVar 32); (10%bv, EVar 35); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 8));
                                       (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8)); (20%bv, EVar 35); (21%bv, ELit LbB_Kit.SHBASE);
                                       (22%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit LbB_Kit.SHBASE));
                                       (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 8)) (ELit 3)) (ELit LbB_Kit.SHBASE));
                                       (24%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit LbB_Kit.SHBASE))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; unfold wz;
        rewrite ?w_addm, ?w_add by lia; reflexivity. }
    assert (HK : know_ok asegs E m
      (kn_fix 30 [AANNOTATE_CC] (SCR [false; false; false; false; false] [] []) 956436
        (srs sr_id [(1%bv, ELit 956436); (2%bv, EAlu ALU_ADD (EVar 33) (ELit (-80))); (8%bv, EVar 33);
                    (9%bv, EVar 32); (10%bv, EVar 35); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 8));
                    (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8)); (20%bv, EVar 35); (21%bv, ELit LbB_Kit.SHBASE);
                    (22%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit LbB_Kit.SHBASE));
                    (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 8)) (ELit 3)) (ELit LbB_Kit.SHBASE));
                    (24%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit LbB_Kit.SHBASE))])
        [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL); KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit LbB_Kit.SHBASE);
          KWord (SA (EVar 33) (-80)) 8 (EVar 43); KWord (SA (EVar 33) (-72)) 8 (EVar 42); KWord (SA (EVar 33) (-64)) 8 (EVar 41);
          KWord (SA (EVar 33) (-56)) 8 (EVar 40); KWord (SA (EVar 33) (-48)) 8 (EVar 39); KWord (SA (EVar 33) (-40)) 8 (EVar 38);
          KWord (SA (EVar 33) (-32)) 8 (EVar 37); KWord (SA (EVar 33) (-24)) 8 (EVar 34); KWord (SA (EVar 33) (-16)) 8 (EVar 32);
          KWord (SA (EVar 33) (-8)) 8 (ELit 955152);
          KWord (SA (EVar 32) 0) 8 (ELit 0); KWord (SA (EVar 32) 8) 8 (ELit 0); KWord (SA (EVar 32) 16) 8 (ELit 0);
          KWord (SA (EVar 33) 16) 8 (EVar 36); KWord (SA (EVar 33) 24) 8 (EVar 36);
          KWr (SA (EVar 33) (-80)) (ELit 112); KWr (SA (EVar 32) 0) (ELit 24);
          KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 1 (2 ^ 47); KRange (EVar 34) 1 (2 ^ 24);
          KRange (EVar 35) 1 (2 ^ 47); KAlign (EVar 35) 16; KRange (EVar 36) 1 (2 ^ 47) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m AGOT_SHBASE _ 0%nat (C8 (wz ASHBASE_CELL)));
          [exact CG | reflexivity | reflexivity | lia | reflexivity | unfold AGOT_SHBASE; lia | unfold AGOT_SHBASE; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m ASHBASE_CELL _ 0%nat (C8 (wz LbB_Kit.SHBASE)));
          [exact CS | reflexivity | reflexivity | lia | reflexivity | unfold ASHBASE_CELL; lia | unfold ASHBASE_CELL; lia | reflexivity]. }
      apply Forall_cons. { kword_cell CF 0%nat (C8 y24). }
      apply Forall_cons. { kword_cell CF 8%nat (C8 y23). }
      apply Forall_cons. { kword_cell CF 16%nat (C8 y22). }
      apply Forall_cons. { kword_cell CF 24%nat (C8 y21). }
      apply Forall_cons. { kword_cell CF 32%nat (C8 y20). }
      apply Forall_cons. { kword_cell CF 40%nat (C8 y19). }
      apply Forall_cons. { kword_cell CF 48%nat (C8 y18). }
      apply Forall_cons. { kword_cell CF 56%nat (C8 (wz n)). }
      apply Forall_cons. { kword_cell CF 64%nat (C8 (wz V)). }
      apply Forall_cons. { kword_cell CF 72%nat (C8 (wz 955152)). }
      apply Forall_cons. { kword_cell CV 0%nat (C8 (wz 0)). }
      apply Forall_cons. { kword_cell CV 8%nat (C8 (wz 0)). }
      apply Forall_cons. { kword_cell CV 16%nat (C8 (wz 0)). }
      apply Forall_cons. { kword_cell CE 0%nat (C8 (wz (P + 4 * n))). }
      apply Forall_cons. { kword_cell CE 8%nat (C8 (wz (P + 4 * n))). }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WS | unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WV | unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
      do 6 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; first [lia | split; [lia | rewrite u64_of_Z by lia; exact P16]]|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R 956436 m (seg_rom asegs) HR HK 220%nat [AANNOTATE_CC]
      (SCR [false; false; false; false; false] [] []) 40%N.
    { split_scs.
      all: first [ vt_dj | sc_shdj
                 | cbn [sc_denot]; evs; rewrite ?w_mul, ?w_add by lia; rewrite ?br_ltu by lia; bool_lia
                 | cbn [sc_denot]; evs; unfold wz; rewrite w_negadd by lia; replace (P + 4 * n - P) with (4 * n) by lia;
                   rewrite w_sra4 by lia; rewrite ?w_mul, ?w_add by lia; rewrite ?vt_srl62, ?vt_sltu by lia;
                   rewrite ?br_ltu by lia;
                   first [ bool_lia | replace (P + 4 * n <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity ] ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M3 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rreg HR' 12%bv L12. rreg HR' 13%bv L13. rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 21%bv L21.
    rreg HR' 22%bv L22. rreg HR' 23%bv L23. rreg HR' 24%bv L24.
    unfold wz in L2, L13.
    rewrite (w_addm S (-16)) in L2 by lia. replace (S + -16) with (S - 16) in L2 by lia.
    rewrite w_negadd in L13 by lia. replace (P + 4 * n - P) with (4 * n) in L13 by lia.
    rewrite w_sra4, w_mul, w_add in L13 by lia.
    do 11 eexists. exists M3. split.
    { rewrite !mkst_MS, HRe, L1, L2, L8, L9, L10, L11, L12, L13, L18, L19, L20, L21, L22, L23, L24 in Hms. exact Hms. }
    split.
    { subst M3. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    split; [subst M3; apply wmono_mem_denot|].
    split; [intros lo0 hi0 ST0; subst M3; apply stk_mem_denot; exact ST0|].
    subst M3. split; [|split].
    - apply rw_cells_cons8; [vt_lg Hlf WV 9%nat|]. apply rw_cells_cons8; [vt_lg Hlf WV 7%nat|]. vt_lg Hlf WV 5%nat.
    - apply rw_cells_cons8; [vt_lg Hlf WS 1%nat|]. vt_lg Hlf WS 2%nat.
    - apply rw_cells_cons8; [vt_lg Hlf WS 3%nat|]. apply rw_cells_cons8; [vt_lg Hlf WS 8%nat|]. vt_lg Hlf WS 6%nat.
  Qed.

  Lemma vt_r3 : forall (x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (ra s0 s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (S V n : Z),
    1 <= n <= 2 ^ 24 -> 2 ^ 45 <= S -> S + 64 <= 2 ^ 47 -> 1 <= V -> V + 24 <= 2 ^ 47 ->
    rw_cells asegs m (S - 16) [C8 (wz V); C8 (wz 955152)] -> rw_cells asegs m S [C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    rw_cells asegs m (S + 40) [C8 s1; C8 s0; C8 ra] ->
    wr_at asegs m (S - 16) 16 -> sh0 m (S + 8) -> sh0 m (S + 16) -> sh0 m S -> ACONST m ->
    exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 M5,
      CatSim.msteps asegs
        (MS (mkR x1 (wz (S - 16)) x3 x4 x5 x6 x7 (wz V) (wz n) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                 x28 x29 x30 x31)
            F (wz 958128) fc None m (seg_rom asegs))
        (MS (mkR ra (wz (S + 64)) x3 x4 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (wz 955176) fc None M5 (seg_rom asegs))
      /\ munch [(S - 16, S)] m M5 /\ wmono asegs m M5 /\ (forall lo hi, stk asegs m lo hi -> stk asegs M5 lo hi).
  Proof.
    intros until n. intros Hn S1 S2 V1 V2 CF CB CR WS SS8 SS16 SS0 AC.
    pose proof (ACONST_shbase m AC) as [CG CS].
    remember (mkR x1 (wz (S - 16)) x3 x4 x5 x6 x7 (wz V) (wz n) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                  x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [wz V; wz S; wz n; s1; s0; ra]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-16))); (8%bv, EVar 32); (9%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; unfold wz;
        rewrite ?w_addm, ?w_add by lia; reflexivity. }
    assert (HK : know_ok asegs E m
      (kn_fix 30 [955176] (SCR [] [] []) 958128
        (srs sr_id [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-16))); (8%bv, EVar 32); (9%bv, EVar 34)])
        [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL); KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit LbB_Kit.SHBASE);
          KWord (SA (EVar 33) (-16)) 8 (EVar 32); KWord (SA (EVar 33) (-8)) 8 (ELit 955152);
          KWord (SA (EVar 33) 0) 8 (ELit 0); KWord (SA (EVar 33) 8) 8 (ELit 0); KWord (SA (EVar 33) 16) 8 (ELit 0);
          KWord (SA (EVar 33) 40) 8 (EVar 35); KWord (SA (EVar 33) 48) 8 (EVar 36); KWord (SA (EVar 33) 56) 8 (EVar 37);
          KWr (SA (EVar 33) (-16)) (ELit 16);
          KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 1 (2 ^ 47); KRange (EVar 34) 1 (2 ^ 24) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m AGOT_SHBASE _ 0%nat (C8 (wz ASHBASE_CELL)));
          [exact CG | reflexivity | reflexivity | lia | reflexivity | unfold AGOT_SHBASE; lia | unfold AGOT_SHBASE; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m ASHBASE_CELL _ 0%nat (C8 (wz LbB_Kit.SHBASE)));
          [exact CS | reflexivity | reflexivity | lia | reflexivity | unfold ASHBASE_CELL; lia | unfold ASHBASE_CELL; lia | reflexivity]. }
      apply Forall_cons. { kword_cell CF 0%nat (C8 (wz V)). }
      apply Forall_cons. { kword_cell CF 8%nat (C8 (wz 955152)). }
      apply Forall_cons. { kword_cell CB 0%nat (C8 (wz 0)). }
      apply Forall_cons. { kword_cell CB 8%nat (C8 (wz 0)). }
      apply Forall_cons. { kword_cell CB 16%nat (C8 (wz 0)). }
      apply Forall_cons. { kword_cell CR 0%nat (C8 s1). }
      apply Forall_cons. { kword_cell CR 8%nat (C8 s0). }
      apply Forall_cons. { kword_cell CR 16%nat (C8 ra). }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WS | unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R 958128 m (seg_rom asegs) HR HK 120%nat [955176] (SCR [] [] []) 40%N.
    { split_scs.
      all: first [ vt_dj | sc_shdj | cbn [sc_denot]; evs; rewrite ?w_mul, ?w_add by lia; rewrite ?br_ltu by lia; bool_lia ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M5 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9.
    unfold wz in L2. rewrite (w_add S 64) in L2 by lia.
    do 15 eexists. exists M5. split.
    { rewrite !mkst_MS, HRe, L1, L2, L8, L9 in Hms. exact Hms. }
    split.
    { subst M5. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?v_addi_Z, ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    split; [subst M5; apply wmono_mem_denot|].
    intros lo0 hi0 ST0; subst M5; apply stk_mem_denot; exact ST0.
  Qed.
End VTail.

Section VecT.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Hypothesis HANN : annotate_gen_stmt.

  Lemma sr_blk_eq : forall (Q : config -> Prop) s msF mo R F pc fc m ro R1 pc1 M1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
      x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F pc fc None m ro -> rfull R ->
    CatSim.msteps asegs (MS R F pc fc None m ro) (MS R1 F pc1 fc None M1 ro) ->
    R1 = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ->
    (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       as_VIS H s msF' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            F pc1 fc None M1 ro ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_VecT ()) ["VecT"] "h03Hmsh14VIS'h22R1h31mh43mo'h54msF'h61Fh72HFh83HReh91Kh:2KRh;3KR'h<2M1h=3MP'h>1Qh?1Rh@3VIShA2fchB2mohC3msFhD2pchE3pc1hF2rohG1shH2x1hI3x10hJ3x11hK3x12hL3x13hM3x14hN3x15hO3x16hP3x17hQ3x18hR3x19hS2x2hT3x20hU3x21hV3x22hW3x23hX3x24hY3x25hZ3x26h[3x27h\3x28h]3x29h^2x3h_3x30h`3x31ha2x4hb2x5hc2x6hd2x7he2x8hf2x9p%0p;1p;2p;3p;7p;Op;8p;6p;Ep101C=p4p70R0g00B7R1p4p710p8P0p101D5p4p710R2p8P0p101DLR3p4p7210p8P0p100Nfp4p710p8P0p101Dhp4p710p8P0p101EER0p4p7210p8p101Ebp4p70R4P2p8P4P3p4p710p8P4P0p4p710p8g01F[j1KTg001:j12Tg00ARj16Tg001_j19Tg002=j1=Tg0000j2ITg002`j1GTg01GTj2:Tg01HIj3;Tg01IEj38Tg00j^j1BTg01J?j73Tg01K9j1JTg01L6j3<Tg01LjlO4TP1j3ATg01Mej3?Tg01Naj3HTg01OZj20Tg00A8j2ETg000\j8Dj6FTg01PLlECTg006]j1@Tg01QFj3>Tg01QiR1f1R0f0R43Ap=7%@4g015]R35>0p=1%64#@=>03p=5g01S0p-0[p,1HR3#Kg01SeS00g00;OR2#2R5#6R6#9R7%25R8#2R9#2R:#2R;#2#9#=R<'IR=%9;#=%99#=#G\<S01Q01Q01fZR;fYR>fXR?':5;3f[R@=83;P?fWRAfVRBfURC%B<RDfTREfSRFF3'7%J>g00=OS02P;P>P?PAPDPBPCF3PEP>PFPAPDfRRGPCF33<PGfQRHfPRIfORJfNRKfMRLfLRMfKRNfJROfIRPfHRQfGRRfFRSfERTfDRUfCRVfBRWfARXf@RYf?RZf>R[f=S03f<S04f;S05f:R\f9R]f8f7S06f6S07f5S08f4R^MO49A=CQ00faR_1:04R`5;3f`Ra=?30fcS09f3Rb583PAPBPCPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[Q03Q04Q05P\P]MO4f_R]P>f]R\PDP?P@F3'7feS0:1:^b5H3[[[]4^51p,5HCEILP3p,2HHP_PaP]f^RcP\f\RdP@P;P>P?PAPBPCQ08P^Pbf2ReQ00fbRf=;3`A?3_0fdS0;=83b1172R`,0@1175R5,0@%62R2,17Rg,0@1178Rh,0@1176Ri,0@%22Rj,17Rk,0@%62R2,17Rl,0@1179Rm,0@%68R8,17Rn,0@%26Ro,17Rp,0@%66R6,17Rq,0@%2jRr,17Rs,0@%6jRj,17Rt,0@%22Ru,17Rv,0@%62R2,17Rw,0@117:R:,0@1579R9,0@%28,17Rx,0@1578R8,0@%2o,17Ry,0@157oRo,0@%26,17Rz,0@1576R6,0@%2r,17R{,0@157rRr,0@%2j,17R|,0@157jRj,0@%2u,17R},0@157uRu,0@%22,17R~,0@1572R2,0@MO4PaP;PcPDP>PdF3'7Q08P^PbPeP0P110d`10d510dg10dh10di10dk10dl10dm10dn10dp10dq10ds10dt10dv10dw10d:10d910dx10d810dy10do10dz10d610d{10dr10d|10dj10d}10du10d~10d2MO4P_P@P]PDP;P\F3P;P>P?PAPBPCPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[Q03Q04MO4RbPfPdPaPDP@PcF3,74X31P=P>P?PAPBPCPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[Q03Q04Q05MO4R7Q02Q09PfP_PaPDP]PcF3P4PfPdPaPDP@PcF33<fgQ07583100`1005100g100h100i100k100l100m100n100p100q100s100t100v100w100:1009100x1008100y100o100z1006100{100r100|100j100}100u100~1002MO4Q09P\P_PDPdP]F3'710e`10e510eg10eh10ei10ek10el10em10en10ep10eq10es10et10ev10ew10e:10e910ex10e810ey10eo10ez10e610e{10er10e|10ej10e}10eu10e~10e2MO4Q0;PcPfPDP\PaF3PdP@P;P>P?PAPBPCPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[MO4Q0;PcPfPDP\PaF3'7]1]0X2=Q02PfP_PaP]PDPcP\F3P7P_P@P]PDP;P\F33<ffQ0858310b`10b510bg10bh10bi10bk10bl10bm10bn10bp10bq10bs10bt10bv10bw10b:10b910bx10b810by10bo10bz10b610b{10br10b|10bj10b}10bu10b~10b2MO4PfPdPaPDP@PcF3'7P@P;P>P?PAPBPCPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[Q03MO4Q09P\P_PDPdP]F3,E1W1W0PdQ07Q06P4GDQ0:=83^P4EFO5W1W=W;W4X51MECW9W8W0W7W@W:X`<X_<X]<X\<X[<XZ<XY<XX<XW<XV<XU<XT<XR<XQ<XP<XO<XN<XM<XL<XK<XJ<XI<Xf<Xe<Xd<Xc<Xb<Xa<X^<XS<XH<W<XE<X2=WFW3WAXD<X6=W?WBXC1WGW>o"). Qed.

  Lemma aclient_range_weaken : forall LB SP SP' A n, aclient_range H LB SP' A n -> SP <= SP' -> aclient_range H LB SP A n.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_VecT ()) ["VecT"] "h01bh11Kh21ah34__x1h44__x2h54__x3h61Ah72HSh82LBh92SPh:3SP'h;7__arithh<4__ffh=8__varmaph>5__with?1np;1p;6p;2p;3p;4p;7p;8g003Bj1DTg01T[j6CTg00ELj21Tg007;j23Tg00E0j2>Tg01U\j1RTg01V[j3;Tg01W2j1MTg01Wnj1HTg009Vj22Tg00@Aj17Tg01Xjj1\Tg01Ybj1VTg01Z\j1UTg01[VR0j26Tg00fbj1ATg00gAj2=Tg00gjj3BTg00hSj2PTg004_j1OTg005?j3NTg00i?j2?Tg00i]j4LTg00Ghj1KTg00HFj1ITg00j;j2:Tg00ARj1JTg00j^j1GTg001:j1FTg00KFj2QTg00A8j2ETg00Khj2STg00B7j3TTg00LTj3_Tg00M3j4^Tg01\0j3]Tg01\Jj3[Tg01\dj2WTg00ITj4XTg00P<j7YTg0119j8ZTf2R1f1R2'1f0R3'2p=<f3R4/111123'2p=0g01EbR5/W3p=41623,61p=5g00<4R6P2g00UcP3CXp=9P2g00P`R7g00Q?R8P8g00Q_R9P3g00R?FYp=8P4P7P8P8P9P1P2P3GZp=@%D5p,5HCEILR7p,1HR:f4R;P1P2P3EC11;4R<P0P<13;4R<,>39<;3%R2R0[^26f7R=9;53R>%M3R?P;P<%H3R@,3?RAC0'2X05#4%7?RBP;P<%\@,3BR@C0,2>X05#4%V:R>P41341RCg01]>,3>RDC0%7>REP4PC%7DRFC0%U7#7RGP4PCg01^:RCC0'63535f6RH/1;f5RI13I;RJ,>37<3P0[^26f8RK9;53RLP?PIPJPAC0'2X05#4PBPIPJP@C0,2LX05#4P>P;P<PDC0PEP;P<PFC0PGP;P<PCC0'63535R<'6P211I;11=IR;13HIRL,>39<H3P0[^26f99;53R0P?PHPLPAC0'2X05#4PBPHPLP@C0,20X05#4P>PIPJPDC0PEPIPJPFC0PGPIPJPCC0'63535RCg00U7RJg017eRG#ARF#A,=61=6F1=6G5B65B6g018D'P%OJ3N%DJP61?61P21?64CL%K6%I6RJg00;ORG,:6RF%JG,:6RE'9,8J%G8R8PJ%FG,:6RG,9E,8JP819FG,8JC@C@1QJ9P3P1g00VJRJg00VjR9'E1S31=TJ9dg00SW=_62C^b<b=b>X36X46X56113111411114[[^36^46^56P3P=PHPKP4P2O5b;3]W1P3O1A[;C3X1<P3O1n200100000021100011000P7P:PHPIP4P1ECeW7W1X?6X66X:6X96W8o"). Qed.

  Lemma aclient_write_ok_cons : forall LB b iv, aclient_write_ok H LB iv -> aclient_write_ok H (b :: LB) iv.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_VecT ()) ["VecT"] "p'0h01bh12H0h21Kh32Hbh42b'h52LBh62ivi001xp;1p;2p;4p;3g003Bj1TTg00^=j2STg01_5j4MTg01Z\j1QTg00ELj21Tg01`9j2:Tg01W2j1DTg01Wnj1CTg007;j2@Tg00@Aj1ATg01Xjj1FTg01Ybj1RTg009VR0j20Tg01\0j3ETg01[VR1j26Tg01\Jj3<Tg00B7j3KTg00;4j4JTg01a:j4ITg01Dhj3PTg01aTj3OTg01V[j3HTg01\dR2j2BTg005?j3NTg00<4R3f0R47P3p=3AO334p=5g01EbR5f1R6;H4p=4f4R7f3R8f2R9'11164'0'0p=71B54p==f6R:f5R;'11178'01196g01^:,14'0'6p=811781196'0/64p=91B56/64,69,68p=?AN5649H59p=;11891164'0p=21B56/64p=>1B591B56/64'6p=GAN564p=L%T51S33p,5HCEILR3p,1HR<P9P4CMP1%Q3R=%36R>'1%56R?,:>1447R@%D4RA%39RB%59RC%C4RD,@ARED7X05#=P@%AAR@PBPC%FD,@@RDD7X05%R<RFP>P?g01]>,@FRG%AFRHP>P?%AGRI%A=RJP>P?F8D9C?11=BR?1:BCR>A;47;RKPA%38RL%58RMPEC2RN'0X05P@PLPMPDC2RO,0KX05PFPBPCPGPHPBPCPIPJPBPCF8D9RC'>C?P411=L1:LMRBA;4;:RKPA%37RP%57RQPEC2RR'0X05#=P@PPPQPDC2RS,0KX05PFPLPMPGPHPLPMPIPJPLPMF8D9RMC?;E4X2?P4O1P>144;R>/0NX05#=10>OX05PCC?P1PB144:RB/0RX0510BSX05;GM11=P1:PQRMf7RB9;4:RSPA%3;RR%5;RCPEC2R>'0X05P@PRPCPDC2RO,0SX05PFPPPQPGPHPPPQPIPJPPPQF8D9RQ'>C?P411=R1:RCRPf8RS9;4BRNPA%3:R?%5:R:PEC2RL'0X05P@P?P:PDC2RK,0NX05PFPRPCPGPHPRPCPIPJPRPCF8D9RC3GRR'6AEPR43<X2MP4O1144BRM/0>X0510MOX05;GQP1144SRQ/0LX05#=10QKX05/>C11=?1:?:f9RC9;4SRQPA%3BRK%5BRBPEC2RL'0X05P@PKPBPDC2RM,0QX05PFP?P:PGPHP?P:PIPJP?P:F8D9R:'>C?P4144CR?/0LX05#=P2P5f:RL,44RQPA%3SRO%5SRSPED7X0511=O1:OSf;R>9;4LRRPA%3CRP%5CRCPED7X05P@PPPCPDC2RN,0RX05PFPOPSPGPHPOPSPIPJPOPSF8D9RR'>C?RTP4f<RU,44RVPA%3LRW%5LRLPEC2RX'0P0f=RY,46%D6RZ%3>R[%5>R\%C6R],@ZC2%3UR^,1=%5UR_,:^f>R`f?Ra5;4RbPA%3YRc%5YRdPED7X05PbP@PcPdPDD7X05PFP^P_PGPHP^P_PIPJP^P_F8D9'>C?P4148a%D7Rb%3`Re%5`Rf%C7R7,@bC2%3aRg,1=%5aRh,:gRifARjfBRk5;4RlPAf@Rm#3Rn%5mRoPED7X05Rp#=RqPlP@PnPoPDD7X05PFPgPhPGPHPgPhPIPJPgPhF8D9'>Rl'6Rr'6P5PpP;1LmjRp,4;%D;RsPgPh%C;Rt,@sC2AK5m;14;j;<6P4CJCI9Eql9<ir3<W2W3P6P4O2n2001000000121000000W1X45P6P4O2n2001000000121100000W1P4O110?MX05/>:P1PQP@POPSPDD7X05#=PFPKPBPGPHPKPBPIPJPKPBF8D9PTP4144>/0NX05#=P2P5P@PWPLPDC2R2,0VX0511=W1:WLA;4UYRYPAP[P\PED7X05PYP@P[P\PDD7X05PFPWPLPGPHPWPLPIPJPWPLF8D9'>C?P4144`P@P^P_PDD7P0146a%AZRZPcPd%F],@ZC211=e1:ef144pRpPAPgPhPED7X05PpP@PgPhPDD7X05PFPePfPGPHPePfPIPJPePfF8D9'>C?P4148j%AbRbPnPo%F7,@bC2%3jRb,1=%5jRj,:bR7fCRofD5;4RnPA%3kRA%5kRfPED7X05#=REPnP@PAPfPDD7X05RD#=RfPFPbPjPGPHPbPjPIPJPbPjF8D9RA'6R@'6Rn'6P5PDP;A;;ko%AsRsPbPj%Ft,@sC2AK5k;14;o;<6P4CJCI9EfA9<E@9<7n3<W2W3P6P4O2n2001000000121000000W1X45P6P4O2n2001000000121100000W1P4O111=P1:PCR=A;4>URU/0XX05#=RX10U2X05#=RUPFPPPCPGPHPPPCPIPJPPPCF8D9RC'6RP'6RJ'6A<UC49<XP9<=J3<X2RP4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021000011000P3P<1L98P6CMeW2W6X05W5o"). Qed.

  Lemma client_fresh_disj : forall s LB p A n SP m0 X k,
    as_RHEAP H s ((p, A, n) :: LB) m0 -> ~ In p (map blk_id LB) -> aclient_range H LB SP X k -> aceil <= SP -> 0 < k ->
    A + n <= X \/ X + k <= A.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_VecT ()) ["VecT"] "p'0h04__x1h14__x2h24__p1h34__x3h44__x4h54__p2h62H0h74__p3h84__x5h97__arithh:4__ffh;8__varmaph<5__with=7__sat17h>7__sat18h?7__sat19h@1bi001bhA1KhB2H1hC3H11hD3H16hE2H6hF4__p4hG2RPhH7__sat20hI4__x6hJ1ahK2HbhL2K1hM2K2hN1zi011zhO3H10hP3H12hQ3H13hR3H14hS3H15hT3H17hU3H18hV3H19hW2H2hX2H3hY2H4hZ2H5h[2H7h\2H8h]2H9h^2Q0h_3Q16h`4QAPPha2QChb2QFhc2QIhd2Qnhe1qhf2q0hg2q1hh2q2hi1rhj2r0hk2r1hl2r2hm1Dhn2RFho1Ehp3H21hq3HI2hr2Hahs2SLht4__x7hu1li021lhv1pi031phw1Ahx6ACEILBhy3ACFhz2Abh{2F1h|2F2h}2F3h~2F4i043H20i053H22i063H23i073H24i082HRi093HSPi0:3Hb'i0;3Hidi0<2Hki0=2LBi0>2NIi0?2R0i0@3R16i0A4RAPPi0B2RCi0C2RHi0D2RIi0E2Rni0F3SA0i0G2SPi0H1Xi0I2_Hi0J7__sat21i0K7__sat22i0L2ivi0M1ki0N2m0i0O1ni0P2nbi0Q2p0i0R2pbi0S2q3i0T2r3i0U1si0V2Ini0W2l'i0X1xp%0p%1p%2p&0p&1p;1p;2p;3p;4p;6p;Cp;9p;7p;<p;5p;8g01F[k11OTg00^=S00k20`Tg003BR0k10ZTg005?k301Tg01b1k41FTg01V[k30[Tg01bmk10BTg01T[k612Tg01Z\k10|Tg00ELj20Tg001:j15Tg001_k10^Tg002=k10tTg00j^k10qTg004_k10nTg01cFk21<Tg01dHk217Tg01Dhk30NTg01aTk30ETg00@Aj1HTg01Xjj1|Tg01eJk211Tg01ekmC10Tg01fjk60~Tg00B7j3WTg01[VS01j2LTg00A8j2}Tg01\0j3tTg01gcm90dTg01W2j12Tg01Wnj13Tg01hbk40aTg006]j1wTg007;j21Tg01Ybk11HTg01ibj3;Tg01j[k71;Tg01kWk219Tg00]3j2:Tg009VR1j26Tg01lRk114Tg00ARj18Tg01mRk113Tg01U\k10iTg01nLj2ITg00fbk10;Tg00gAk20gTg00GJk10}Tg00Ghk10{Tg00HFk10zTg00j;k20fTg00I1k20eTg00KFk20yTg00Khk20xTg00LTk30wTg00M3k40vTg00Znj2UTg01=1k30bTg00E0j2@Tg01\Jj3rTg01o=S02k10ITg0207k61NTg00Nfk61MTg020Rk41LTg020nm<1KTg01=Tj2DTg021kj2aTg022Lj2hTg0233j2eTg023Zj2bTg024@j2gTg00Fik20STg00XXk11ETg024fk21DTg025Gk30RTg0260k20sTg026Yk30WTg01?]k20KTg01;kk30XTg00DHk21CTg00Ehk21BTg00FEk31ATg00J?k31>Tg027Bk51=Tg028Bk40FTg01DLk41:Tg01\dS03k20pTg00gjk30MTg00hSk20oTg00i?k21?Tg00i]k40GTg00ITj4nTg00P<j7uTg028bk618Tg00Jbk70>Tg01<Nk316Tg0119k804Tg00\Vk215Tg00e4k61ITg000\k61JTf3R2g00<4R3g01C=R4P3f2R5f1R6H0Ff0R7H0Fp==g01EbR8P4Q02P7H1:p>0mg00SWR9/@7p=B%57#5p>021167,05p=Z10251067'6p=if6R:f5R;'0f4R<'61025/66/L7'Lp>0Y1:67=W39p=Y1097p=41U67,05p=<g029FR=f7R>'010:;11<2/05/L6/67'6'6p=V1667,65p>0T1156/07p=71056/L7p=MP4P3P6P7H0Fp>07P5P3P6P7H0F#2p=^1096/67p>0D10251067'Lp=?10=7p=[10<21L56/67'6p>0O11:;/0<1U56,02'L/67p>0Q1156/17p>00%57#5#5#5p>0?AW379p=G%87#8p=R%87#8#8#8p=_%57#8p=P%57#5#5#5#5#5#5#5p=~%57#5#5#5#5#5#5#wp=l10251@67'6p=F1656/67p=]B0[867p=C10251067'6,6<p=E20p87p>0<%|7,16p>0C10:;10<2'61056g01^:R?,07'6'Lp=`10<21056'6/L7p=p20p86/L7p=s1L67,L5p>0h1:67,09p=T20g37p>0:B0M367p=\B0M367:0M35p=og00U7R@g018DRA-0o6<017p=q21?37p=yP3P5P6P7H0Gp=A20e37p=J20f37p=KP5g00P`RBg00Q?RCPCg00Q_RDP3P6g00UcREP7Cng00R?RFFup=>P6PBPCPCPDP7J18p>08P<PBPCPCPDP2PBPCPCPDP5P6K0>P7K0>p=xB16367p=QP5PBPCPCPDP3P6g0190RGP7CnPFFup>0AP2PBPCPCPDP5P6P7L04p>0@P:PBPCPCPDP;P<P2PBPCPCPDP5P6P7L04L04p=9P3P6PGP7Cnp>0VP<PBPCPCPDP2P5PBPCPCPDP3P6PGP7CnPFFuK0>p=mP<PBPCPCPDP2PBPCPCPDP5PFFuP6P7L04p>0U%87#8#5#5p>06%87#5p=S%57#5#5#wp>05%57#8#5#5p>0J1@67,65p=X1025/66/L7p>0u1056/67p>03%37,16p>1GB0E437p>0_P3P3P<P2P5H0GP6P7H0Gp=NP5PBPCPCPDP6P7K0>p=jP;PBPCPCPDP<PBPCPCPDP2P5K0>P6P7L04p=vP;PBPCPCPDP<PBPCPCPDP3P2PEP5CnPFFuP6P7L04p=kP5P3P6P7H0Fp>0=21556/179W32p=O10951@67'6p=c1@561079'6p=dAW367p=fB0M36700oAp>0rB01@67p>0]P5PBPCPCPDP3P6g016aRAP7CnPFFup>09P6PBPCPCPDP7J1Ip>0\P3P6PAP7Cnp=zP<PBPCPCPDP2P5P6PBPCPCPDP7PFFuL04p={P3P5P6P7g02:@g02;>J1Jp>0LP3P<P2P3P5P6P7H0GH0Gp>1@107?p>0j10=6/67p>0H1067,65p>0PP3P6PEP7Cnp>0lP2PBPCPCPDP5P6PBPCPCPDP7PFFuK0>p>0k1056107?'6p>0cp,1HR?$1O20`43RF00`3RB$0Zg02<CP?f8REPFP:P;P<C=S04>01B>P5H1F&0mE:0[4>$0Bp,5HCEILR=P?f9RAP;P2P5J12&0|=RG/0:%B<RHP=P?p,2HHS05f=RIf<RJf;RKf:RLPAPEP>g00;ORM#5S06#5S07#5S08#5S09$02RN$0^$0tQ08$0^$0t$0qUROPOg02=:$0nRPP<P221<POg00=O017O20`33RPPKB0N337RQB0E337RR?ZKL%HKS0:PQQ0:%|L5ZRPGPQPRPACiK0YZ0LP+11P6NC10P=P?PJPEPOPOJ0~P=P?Q05f>ROPFPJPKPLC=RP>01BIPEPPP;AW8PP&0Z8RRp-0RQ]u^J8P0P8PQP7g017HS0;AW862P<P2P7O2'Ln1011020002002010010WXuRXJ8p?100110VS0<PPPIO21}8P3tN90dP=P?%2P%3PH0aP1PFPIPJPKC=RP#2RR#BQ09#wR0,YR%3PRP#4PR11RPRSPGPSP0&1H?RSg01]>RT,1SRU?<R0A;=RPGV40T11IJRPA7AEI7MAP7f?S0=007O=^FI#BPFf@RRQ0=POC=RV#2RW/Y0%3VRV#4PW11WVRXPGPXP0PSA<UW0A;=WVGV40TP1PFfARVPRQ0=C=RW#2RX/Y0%3WRWPX11XWRYPGPYP0PSA<UX0A;=XWGV+0D11VRRWPIPPPVC?P7fCRPfBRX+07=^FV/Y0PFfDRYPPPXC=RZ#3R[%2ZRZ11Z[R\PGP\P0PSA<UZ0A;=Z[GV+0DP1PFfERZPYPPC=R[#3R\#4%2[R[11[\R]PGP]P0PSA<U[0A;=[\GV11ZYR[PVPWPZC?P7PFfGS0>fFS0?PZC=#3#4PFfHS0@Q0>Q0?C=RW#2R\%3WRW,1\R]PGP]P0PSA<U\0A;=\WGVP1PFfIRWQ0@Q0>C=R\#2R]#[%3\R\,1]R^PGA7^0SA<U]0A;=]\I0OQ0@,1WR\PZP[PWC?P7fKS0AfJS0B+07=^FW#[PFfLS0CQ0AQ0BC=R[#2R]%3[R['1R^PGA7^0SA<U]0A;=][I0OP1PFfMS0DQ0CQ0AC=R[#2R]%3[R['1R^/0GP^P0PSPUP]P0A;=][K0QQ0DQ0C'1R[PWP\Q0DC?P7PFfOR\fNS0EQ0DC=R]#2%3];7GPFfPR]P\Q0EC=R^#2R_%3^R^'1P0PSPUP_P0A;=_^K0QP1PFfQS0FP]P\C=R\#2R^%3\R\<000A<U^07MSA;=^\Q0F/1]Q0DP[Q0FC?P7PFfSS0GfRS0HQ0FC=R[#2R\%3[<000A<U\07MSPFfTS0IQ0GQ0HC=R\#2%3\5;=P=P?Q05fWS0JPFfUS0KQ0IQ0GC=fVS0L601BQ0FQ0EK1;219=?P1%[SS0M10UGS0N&02N$0?S0O#wRN,:SR\#GS0PA;=STS0Q'6S0R'6S0SQ0LQ0K'1RTQ0HQ0HQ0FQ0L373MP7Q0MQ0SP1Q0NQ0RfZR[fYR^'1R_Q0LPTP[C?P7Q0NQ0RP1Q0PQ0Qf^S0Tf]S0U'1RTP[P_Q0TC?P7Q0PQ0Q&14=S0V%8MS0W#8S0X#8S0Y#8#R#_#_R_#P#RS0Z#8#_#~#~#lS0[/0GS0\%8_S0]#_#_#~#~#lS0^,0GR_1:GNR`#GPG&13=RaPa11GNCFS0_'6Ra3]S0`Q01f`RbQ0T'0f_RcP7P7Q0T,1cRdCF&0i6Re[^J3feRf,C7Rg%27RhPcPd%37Ri,1hS0aDEX@8$0<Pg%HhRgPcPd20CgiS0bDEX@8PSQ0TPTPU%HSRiQ0TPT%HURj%HGRkQ0TPTF`Dp's40hfcS0cfbRT'1S0dPcPdQ0cC?P[faR[/0cfdS0eQ0c'1S0f/0b11bcRlQ0e'01IGNRm%4G%4NRn%4`S0g[[Ro1If0%4f%40RpfgRq/T0[[1ISNRr%4S%4\S0h\n[Rng017eRs$0;Rt$0;Ru$0;S0i$0;S0j$0:S0k&0:uS0l&0:tS0m20g3sS0n'\S0o3o&0n@Rs'q&0Z@R@%y<S0p&0}3Rt7A5S0q%y;S0r?A2tS0s7A6S0t&0{3Ru&0z3RvPvPvQ0[#JS0uQ06#8S0v#KS0w5>vS0x208v>S0y208vES0zDxS0{&0qCRCPv20f3MS0|Q06#KS0}'QRwQ0w5>vS0~PCPv20e39RxQ0|60AvS10PCPvQ0wQ07#KS115>vPCPvQ11Q0W#KS125>vS13PCQ129>vwS14H0@S15F9F920yvDRDP7P5g00VJRyg00VjRz'}20x75=WyzdB0w396H0vRzb:b;b<X03X13X33X43X83X2QX5QQ0[/0<S16?];:S171165S18/0;%B5S1910>:S1:Q1:11;:S1;/0>S1<[[[[[^03^13^33^43^83^2Q^5QP7PaP_PGffRyQ0ePqfhR{P:PWP^PcP<O<b9b=b>b?3tWAP7O1PbP7P7PlCFPe[^J31C7yR^PhPbPlQ0aDEX@8$0<P^PgPbPlQ0bDEX@8PSPcPdPUPiPcPdPjPkPcPdF`Dp's40hQ01P[P7P711[bS1=CFPe[^J31C7qRdPhP[Q1=Q0aDEX@8PdPgP[Q1=Q0bDEX@8PSPbPlPUPiPbPlPjPkPbPlF`Dp's'sQ0e,1fS1>P[Q1=PfC?P7PTP7P711T[S1?CFPe[^J311yfS1@/0TQ1?/0yP7Q1?%wMRe'URlPmPo1Iq0%4qfiS1A/T0\p[PrPnPsP@%y5S1B?A6tPuPvPvQ0}-0VxPCPvQ0|%Je:0b3wS1C5>vPvQ1CPwDmI0UPDPzb:b;b<X03X13%B6S1DP6Q18/UeRdPdQ18CF[^03^13P7PfPyPbO3b9b=b>b?O2&0ilQ01%5M#_$06$0?#lS1EQ0d/UeRlPl%8M$0?#R#P#R#S#S#P$05RdCF%8M$02$0J#R$0?#S#R$05S1FPl%8M$02#P#S$06#R#lR^,@l%8M$02#P#S$06$06#P$05S1GPl%8M$02#P#S$06#R#S#R$05R|,@l%8M#P#P#S#P#S#R$0J#S$05S1HPlPl%8M#P$06#R#S$0J#S#P$05S1ICFK0YQ0f/0{P7Q1EQ0f/UeRlPlPdCFPmPofjR}/I0%4}flR~/T0\p[PrPnQ0i$0:S0iQ0o'\S1J/qsS1KP@Q0q%y2S1L7A6S1MPuPvPvPvQ0uQ115>v208v:S1NQ0yDxS1OPCPv%8M#P#R#P#~#lS1P#JS1QQ125>vS1RPCPvQ12:0AvxS1SPCPvPvQ0zPvQ1C%JdDmPCQ14F9F9PDPzb:b;b<X03X13X33X43X2QX5QX7QQ0[/02?]<;S1TQ1P/02S1U112<S1V/UeS1W=XAd11<;S1X/0:S1Y[\H[[^03^13^33^43^2Q^5Q^7QP7Q1EQ1A/1{S1Z;<ePaP_PGfmRdP{Q1APKQ0HQ0TP<O;b9b=b>b?WAP7O1Q1FPl1@l^Q1GPl1@l|Q1HPlPlQ1ICFK0YQ01Q1FQ1>/UeRlPlP^CFQ1GPl1@l|Q1HPlPlQ1ICFH0uQ1@/0}P7Q1FQ1@/UeS1EQ1EP^CFPmPo1I~0%4~fnRl/T0\p[PrPnQ1KP@Q1MPuPvQ1OPCPvQ1RPCPvQ1SPCPvPvQ0zPvQ1C%J^DmPCQ14F9F9PDPzb:b;b<X03X13X33X43X2QX5QX7QQ1TQ1UQ1W=XA^Q1Y[\H[[^03^13^33^43^2Q^5Q^7QP7Q1FfkS1[/1}S1\;<ePaP_PGfoR^P}Q1[PIQ0IPbP<O;b9b=b>b?WAP7O1Q1GQ1EQ1E/@|Q1HQ1EQ1EQ1ICFH0uQ01Q1G11qyS1E/UeRbPbP|CFQ1HPbPbQ1ICF11{qS0I/0~S1FP7Q1GQ0I/UeS1]Q1]P|CFPmPo1Il0S1^%4lfpRb/T0\p[S1_PrPnQ1KP@Q1MPuPvQ1OPCPvQ1RPCPvQ1SPCPvPvQ0zPvQ1C%J|DmPCQ14F9F9PDPzb:b;b<X03X13X33X43X2QX5QX7QQ1TQ1UQ1W=XA|Q1Y[\H[[^03^13^33^43^2Q^5Q^7QP7Q1G11d~S1`/UeRe'0PaP_PGfqR|P~PdQ0=Q0LPTP<O;b9b=b>b?WAP7O1Q1HQ1]Q1]Q1ICFPmPoQ1^Q1_PrPnQ1KP@Q1MPuPvQ1OPCPvQ1RPCPvQ1SPCPvPvQ0zPvQ1CQ1I#JDmPCQ14F9F9PDPzb:b;b<X03X13X33X43X2QX5QX7QQ1TQ1UQ1WQ1I5XAQ1Y[\H[[^03^13^33^43^2Q^5Q^7QP7Q1H/0ePaP_PGP|P~PdQ0=Q0LPTP<O;b9b=b>b?WAP7O1n200100000021100011000W6P7O1n200100000021100011000W6P7O1n201100000021100011000bA3rWAP7O11C7{RePhPTQ1?Q0aDEX@8PePgPTQ1?Q0bDEX@8PSP[Q1=PUPiP[Q1=PjPkP[Q1=F`Dp's'sQ01Q1A,C7R[PhQ0cQ0dQ0aDEX@8$0<P[PgQ0cQ0dQ0bDEX@8PSPTQ1?PUPiPTQ1?PjPkPTQ1?F`Dp'sQ1EQ0cQ0dPqC?P71C7}S1?PhQ0eQ0fQ0aDEX@8$0<Q03P8Q1[,C7S1=PhPfQ1>Q0aDEX@8Q1ZPfQ1>Q1AC?S0LP71C7dS1HPhPqQ1EQ0aDEP11C6l%26S0aQ0IQ0a%36S1U3Z803{Q1`Q1AQ1ZPdC?S1WP71C2b%2<S1IQ1[Q1\Q1I%3<S1C3Z403P1%2;S1R/0~Q1[,1~S1OQ1R%3;S1M3Z11|bS1_/0dS1^Q1`/0|S1]'LS1GP7%2>S1a/0l11^lS1b%2ES1c%3ES1d'1S1e'0PFfuRhftS1ffsS1gC=RT=W8AfvR[,CA;r;B01BT[,CA&0IL=W4[RTP^P4&0IKS1hfyS1i$0m:0[47Xv4P8P4Q02fxRePKP>J1NfwS02P7J1MO1Wo&0BTRTePTP=P?Q05Q1iPFQ02P[PhC=RT>01BeS1jQ1gPTPKPbAW8TTQ0<PTPeO21}8T3tP6&0ITQ1h5W4P6P4PFPeQ02P[C=$0I&0IJP7H1LO1WoN<1K%2TS1h%3T<000%2KRB21GBKQ1h7703MQ01Q02/1[B0NF3J$0_RB770B0EF3J,1BQ02770Q02,1eS02Q1fQ1fQ1g;7e3MS1hP7Q02B0NF3I$0_S0<770Q1i?7ehS1kQ1f,1hS1lQ1i'0S1mPmPofzRB/I0S1n%4Bf|RB/T0\p[S1oPrPnQ0kQ0o'\/qsS1pP@Q0qQ0r9At2S1q7A6S0qPuPv%J0S1r,QwQ115>vS1sPCPvPvPvQ0uQ0X#KS0X5>vS1tQ0yQ0zDxS1uPCPvQ10PCQ15H0@S15F9PDPzb:b;b<X03X13X33X43X83X2QX5Q1176S1v?702Q0[/0;?]:>S1wQ1910:;Q1Y[[[[^03^13^33^43^83^2Q^5QP7PaP_PGB0NF3X$0_S19Q1iPBf}S1xP<Q0APlPLO;b9b=b>b?3tWmP7O1Q0<B0EF3I'1?70eQ1kQ1mPmPoQ1nQ1oPrPnQ1pP@Q0pP5%y:S1pP6Q0sDNPuPvPvQ11Q0w'QS1oQ1r'QQ12PCPvPvQ0uQ0W#5S0W#KS1n5>vS0uQ0z5jvS0<208vAS1yPCPvQ1SPCPvQ1o9>vwPCQ14F9S1zEvEkPDPzb:b;b<X03X13X33X43X83XI3X2QX5QQ1V?705Q0[/0:S1{?]>EQ1V11:>S1|'0Q1Y[\H[[^03^13^33^43^83^I3^2Q^5QP7PaP_PGB0EF3XQ19Q1xPeQ1iP<Q0APlPAO<b9b=b>b?3rWmP7O1n200100000021100011000bmc0;c0:WMWLP6P7O2n2001000000121000000W6WKP6P7O2n2001000000121000000W6X@8P6P7O2n200100000012110X000W6P7O1Q1?PgQ0eQ0fQ0bDEX@8PSQ0cQ0dPUPiQ0cQ0dPjPkQ0cQ0dF`Dp'sQ01Q1=PgPfQ1>Q0bDEX@8$0<PSQ0eQ0fPUPiQ0eQ0fPjPkQ0eQ0fF`DpQ0LP71C7~PgPyQ1@Q0bDEX@8$0<Q03P8Q1HPgPqQ1EQ0bDEX@8Q1\PqQ1EQ1[C?S1HP71C7^PgQ1AQ1ZQ0bDEP11C6bQ0a#HS0aQ1A,1}S0bQ0aQ1U#|3Z803}Q1bQ1[Q1\P^C?P7frRg,C2Q1I#HS1\Q1`Q1\Q1C#|3Z803dP1Q1R#HS1R/0l11ldS1\Q1RQ1M#|3ZQ1g/1gP^Q1bQ1gC?P7Q1a#H/0bQ1_Q1c#HQ1d#|3ZP=P?Q05Q1iQ1jQ1gPAPbAW8TA1CAe;r;N90dP=P?%2AS1j%3AS1iH0aP1%2LR?#B1Y?0%3LRT#4P?11?TS05PGQ05P0PSA<U?0A;=?TGV40TQ1hP7%2J#B%2IRT/Y0%3IR?#4PT11T?S1hPGQ1hP0PSA<UT0A;=T?GV40TP1%2OR?/Y0%3ORTP?11?TS1hPGQ1hP0PSA<U?0A;=?TGV+0Df{,1BS1hPeQ02PBC?P7%2R/Y0%3VRT%2VR?11?TS02PGQ02P0PSA<U?0A;=?TGV+0DP1%3XR?#4%2XRT11T?S02PGQ02P0PSA<UT0A;=T?GVp+01AS02p+01@S05'1S1dPBQ1hQ02C?P7%3Y#4%2ZRB%3ZRT,1BR?PGP?P0PSA<UB0A;=BTGVP1Q0?#2RT#[Q0?#3RB,1TR?PGA7?0SA<UT0A;=TBI0Op+01ES1hp+01DS1R'1S1CQ02Q1dQ1hC?P7Q0@#2#[%2WRB%3WRT'1R?PGA7?0SA<UB0A;=BTI0OP1Q0B#2RTQ0B#3RB'1R?/0GP?P0PSPUPTP0A;=TBK0Qp+01IS1dp+01HS02'1RBQ1hQ1CQ1dC?P7Q0C#2Q0C#3;7GQ0D#2RTQ0D#3R?'1P0PSPUPTP0A;=T?K0QP1Q0E#2R1Q0E#3R?<000A<U107MSA;=1?p+01MR?p+01LS1C'1Q1dPBP?C?P7%2]R?%3]<000A<U?07MSQ0F#2Q0F#35;=Q00PFP3p+01SR?,C7Q0ap+01NRB'0p+01O%25#H%35+0C77B%22#BQ1I/Y0Q1M#4%2:#[Q1a%3>;7GQ1e/10Q1c=<U07MSQ1jQ1i5;=p+01[RBp+01ZS1i'1S1jp+01WR1p+01VS1c=71B3M]`]b]a]c]d]_]^]M]L]KQ0HQ00P4P3B0=F67/C1A^F56#Hp+01RR1'0B0=F25RT#2#H%3T+0C97?1A^F<2#BA^F;</Y0B0=F:;#3#4A^F>:#[B0=FE>R1#2%31;7GB0=FAER1#2R?%31<000A<U?07MSB0=FLAR?#2%3?5;=p+01_R?p+01^S00'1PBQ1jP?C?]`]b]a]c]d]_]^]M]L]K^N3P7PFP5P6P7C=Q1i'C20725=^F6#Hp+01UR?'0Q1cPFP<P2P5C=RB#2#H%3B+0C77?207;<=^F2#BQ04#2/Y0PFP>P:P;C=#3#4207E>=^F:#[PFPAPEP>C=R?#2%3?;7GPFPLPAPEC=R?#2RB%3?<000A<UB07MSPFPKPLPAC=RB#2%3B5;=Q0]#~#lR=Q0Z#5$0?#lRBQ08#wR?,DJR1,17'@XN31aK?%G?RT$0BS0ZPJP?P11:J?CO[1hJ?%B?S0]1:I?R1?c1?[1eI?1@?9S041:O?R1=d?1[1bO?Q0=/D?#G\TQ0=/g?1:R?/fR\T1DR?P31:V?P31aX0%G0R1$0BS1cPPP01DP01:P0S1iCO[1hP0%B0S1j1:Y0S1eQ1e;c0[1eY01@09S1e1:Z0S1aQ1a5d0[1bZ0Q0?/D0#G\1Q0?/g0Q0>/:0Q0>'f\1Q0>/D0P3Q0@/:0P31aGNS0>%GNS0?$0BS1aPGPN1DGNS1MP`CO[S1I1hGNS0a%BNS1[Q0g?X`N[S0g1eGNS1U1@N9S03AdN``[S0L1bGNS0fQ0?Q1M#G[S1=1gGNS0dQ0?1f`G[S1?Q1MP3P`P31aSNS1mQ1aPSPN1DSNS1kP\CO[S1a1hSNS1xQ1[Q0h?X\N[S0h1eSNS19Q03AdN\\[S031bSNS1}Q0?Q1k#G[S1~1gSNS20Q0?1f\S[S21Q1kP3P\P3p+02>/a0Q1cp+02?S22P0Q22/D0Q22/:0CO[Q22/h0Q1jp+02@S22/:0S23Q23;c0[Q22/e0Q1ep+02AS22/:0S23Q235d0[Q22/b0p+02BS22/D0#G\1Q22/g0p+02CS22/:0Q22'f\1Q22/D0P3p+02D/:0P3P;g00TQS2220S90'}Q1jeS23O1S24%47S25?X70S26PIQ2220S9N'}Q1[eS1[O1S27AcEENS28PZQ1[O1S1[%4RS29?XRNS2:Q0DQ23O1Q0@#4S23Q0@;X0Q0KQ2220S9?'}Q0]eS0KO1Ac]]?&1EM-1D3S2;Q0j$0;RM$0:S0j60R3S2<Q0kQ0iQ2;Q0l60R3'\3oS2=&0;M$0:S2>Q0iQ0l3oQ0mQ06#wRM-0s3Q0n60W3Q0l'\+0r+0K+0K00]sP@Q0p?A;tS069At;P;Q1LP;PtP;PtDNP6Q1B?A;tS2?P;Q0r?A;tS2@P;PtDNDNPuPvPvQ1r>09vx-0\vPCPvQ08#8#KS08Q1rQ0v#5S2A#8#K60X3Q07#8S07#5#KS2B'Q'zD{PCPvPvQ0yPvQ2A#5#KS2A%J?S2CDmPCPvPvQ2C>09vx-0\vS2DPCPvQ08Q2CQ0|60X3S2EQ2A'Q'zD{PCPvQ2B>09vxPCPvPvQ08-0VxPC%JBS2A%J=S2FQ0|'QS2G60AvS2HI0UF9F9PDPzb:b;b<X03X13X33X43X83X2QQ0;\1P5P0P;P2CO[AX:<?S2IQ0;\TS2JP<P?P2P:CO[S2K%G;S2L%B;S2M11=;,@BS2N[[[[[^03^13^33^43^83^2QP7Q0H#4Q0CQ0HQ0AQ0eQ0GQ0FP6fXQ0TPcO;b9bBbEbCbDbpc0Tc0Sc07c06c05bpc04blbhbVbUbTbDbSbkbgbRbQbPbCbObjbfb]b\b[bEbZbibebYbXbWbBb640LQ0:,@BS0:eQ0:PJPKPmPop+01dS0:/I0S0TQ0:#4p+01fS0G/T0\p[S0e1IO0S0H%4O1TR0\p[S2OPrPnPsP@%y6S2PPuPvQ10PCQ0|9>vxROH0@PDPzb:b;b<X03%B7%46S2Q[^03P7PVPJO2b9b=b>b?bH%4JePmPoQ0TQ0eQ0HQ2OPrPnPsP@Q2PPuPvPOPCPOH0@PDPzb:b;b<X03Q25Q2Q[^03P7PRPLO2b9b=b>b?bH%4KePmPoQ0TQ0eQ0v#8S0v#RS0e#wRO-1CM%BMS0T%4O21BMOS25#B[S2Q[%4MS2Pg00T5S2OB1AMO6UWrQ2PQ2OQ25#4[]r1IR0Q291TX0\p[PrPnP2Q2220S9M'}Q0TeO1Q2QQ0jQ0lQ0n3o/qsP@Q1BP6Q0p?A<tS2QP<Q1LI1@PuPvPvPwQ0XPCPvQ10PCPvPvPvQ1tQ0XQ0^#JS0T5>vQ1NDxPCPvPvQ07#K-0VxPC%JMQ0e$0^61>39>vwI0UF9EkPDPzb:b;b<X03X13X33X43X2QQ1v/05Q1DQ16Q0^,0<;]:%B:S1vQ1XQ25'0[[[[^03^13^33^43^2QP7Pap+01kRMPGPPPYPKQ0=Pep+01\S1DO9b9bHb=b>b?bHc0Jc0Kg02>597JKeI1=%HJ00CK$0jQ01Q0:Q0:p+01c'1R9/0B+0HQ0O#5#_#_#_#_#~#lROQ0:P9PGCip+01eR9Q0:'1S0:p+01aS0OQ0Op+01`;793MQ05Q0:/0B-0H9Q0Gp+01bS05779S25Q05Q0O'1S0OQ0G'0S0ePmPop+01gS07/I0S0XQ07#4p+01i/T0\p[S221IV0S29%4VQ1i#4\p[S1iPrPnQ2>Q1J'\/qsS2PP@Q1pP:PtP<PtDNP5PtP6Q1qDNPuPvQ2AQ1160AvS1qPCPvQ09#KS09:0AvxS2OPCPvPvQ1tQ0z5jvQ1yPCPvPv208vLS1tQ2A9>vwS2APCQ15EvEvF9PDPzb:b;b<X03X13X33X43X83XI3X2QX5QX7Q1@B2S15Q1vQ1{?]EAQ1V>0PKB10E>S1{Q1|/0ES1|[\H[[[[^03^13^33^43^83^I3^2Q^5Q^7QP7%[MPaP_PYPG%HYS0HQ07p+01jS2RPMPEQ0=PeP;Q1DPVO?b9b=b>b?bH3tWGP7O1POP9Q0:PGCiQ25Q0ePmPoQ0XQ22Q29Q1iPrPnQ2PP@%y>P>PtP<PtDNP5Q1pP6Q0sDNPuPvPvQ1o%JOR9PCPvQ2OPCPvPvPvQ0uQ1yQ1tDxPCPvPvQ129>v9S2O208vKPCQ1zEvF9EkPDPzb:b;b<X03X13X33X43X83XI3Xt3X2QX5QX7QQ1V/0OS1z%B>Q0[/0>?]ALB03O;JQ1vQ1;?ZEAQ1|[[[[[[^03^13^33^43^83^I3^t3^2Q^5Q^7QP7Q2R=7MGPaP_PYPG%|PQ0HPMQ0GQ07P>Q0=PeP;Q1DPRO@b9b=b>b?bH3rWGP7O1n200100000021100011000bqbsQ0OQ00Q00p+01]Q05373MReePeeW`WbWaWcWdW_W^WMWLWKZ0P3Xz3Z0R4P6P7O2n2001103000121100101Z0QFP6P7O2n2001103000121103101Q0EQ0BPWPZPVPIPAP;P6P7O:W`WbP6P7O2n2001000000121000000W6WaP6P7O2n2001000000121000000W6WcP6P7O2n2001000000121000000W6WdP6P7O2n2001000000121000000W6W_P6P7O2n2001000000121000000W6W^P6P7O2n2001000000121000000b6WMWLP6P7O2n2001000000121000000W6WKP6P7O2n2001000000121000000W6X@8P6P7O2n200100000012110X000W6P7O1PSPfQ1>PUPiPfQ1>PjPkPfQ1>F`DpQ01PSPyQ1@PUCiPiPyQ1@PjPkPyQ1@F`Q1HP7PSPqQ1EPUCiQ01Q1O?70SQ0v#5$02$0J#S$0?#lRU,1SR8?<~0Q1WPWQ1`?70SQ1\/0}R}Q0b/0lRVPmPo1I^0RZ%4^1T|0\p[RFPrPnQ0jQ0o'\/qsP@Q0pP5Q0rP6Q1LDNS0oPuPvPvPvQ0uQ0yQ0zDxS0uPCPvQ1sPCPvPvQ1QQ0|PCPvPvPxQ0}PCPvQ10PCPvQ13Q1y5jvPCQ14F9EkEkF9PDPzb:b;b<X03X13X33X43X83X2QX5QX7QQ17Q18?70<Q1P/05%4<Q1{/6JQ1|[\H[[[[^03^13^33^43^83^2Q^5Q^7QP7Q1\/08PaP_PGPSPlP|PgPRP<Q0Jf[Q0cP:O>b9b=b>b?3tWnP7O1A<8d0PmPoPZPFPrPnQ1KP@Q0tPuPvQ0{PCPvQ11%JURF'QRZQ12Q1r60b35>vPCPvQ1SPCPvPvQ1yPv20lwZH0kPCQ14F9F9PDPzb:b;b<X03X13X33X43X83X2QX5QX7QQ1711<US1r?<20Q1V11:U60PLQ1Y[\H[[^03^13^33^43^83^2Q^5Q^7QP710SlPaP_PGPSPgPdPlPRP<Q0cP:O<b9b=b>b?9r}VWnP7O1n200100000021100011000Q1OQ1F7M{eWAP7O1PiPqQ1EPjPkPqQ1EF`Q01PiP{Q0IPjCiQ0I:0ck{Q1WP7PiQ1AQ1ZPjCi1DS?R{,17,@BXN31aS?Q0ZPSP?P{1:S?RVCO[1hS?Q0]AcVV?[1eS?Q04Ad?VV[1bS?%G{\T1gS?1fVS\TP{P3PVP3Q0>Q1IQ0aQ0gQ1UQ0LQ0fQ1=Q0dQ1?Q1MP3P`P3Q1mQ1aQ1xQ0hQ19Q03Q1}Q1~Q20Q21Q1kP3P\P3Q1R/a0S1RQ1cQ1hP0Q1h/D0Q1h/:0CO[S1WQ1h/h0S1hQ1jp+01FRV/:0R{?c{0[S0I1eV0S1EQ1ep+01GR{/:0R}=d0}[S1F1b{0S0cQ02/D0#G\1S17Q02/g0S1VQ1d/:0RRQ1d'f\1S12Q1d/D0S0{P3p+01JRd/:0S0tP3Q24Q26Q27Q28Q1[Q2:Q0DQ0KO1S0KQ23Q0@;X?S23Q2=20s3?RZQ0n60W3ReQ2>Q0iQ0lQ0m:0W3Z'\3o+0rS2>+0K00]sP@Q06?A;tS06P;Q2@?A;tP6Q1L9At;S2=Q2?7A;DNPuPvPv%JNRZ>09vx-0\vS2?PCPvQ0v#KRMQ2B:0X3ZRZQ0W#8#KRK'Q'zD{PCPvPvQ0yPvQ09Q2CDmPCPvPvQ2DPCPvQ2EQ09'Q,zMD{PCPvB09vKxPCPvPvQ1QPMPCQ2HEkF9F9PDPzb:b;b<X03X13X33X43X83X2QQ0?Q0;[P5PNP;P2CO[RNQ2IQ2KQ2LQ1P/0;Q2N[[[[[^03^13^33^43^83^2QP7Q0B#4RKPIQ0BPJPSQ0APXP6P]PcPqO;b9bBbEbCbDblbhbVbUbTbDbSbkbgbRbQbPbCbObjbfb]b\b[bEbZbibebYbXbWbBb660L=1@BiRcePc1D8?Rc=77OXN3Q0VQ0`eQ0`1a8?Q0ZP8P?Pc1:8?RXCO[1h8?Q0]AcXX?[1e8?Q04Ad?XX[1b8?%Gc\T1g8?1fX8\TPcP3PXP3Q0>Q1IQ0aQ0gQ1UQ0LQ0fQ1=Q0dQ1?Q1MP3P`P3Q1mQ1aQ1xQ0hQ19Q03Q1}Q1~Q20Q21Q1kP3P\P31aV0Q1cP{P01D{0P}CO[1h{0Q1jQ02/:0R{?c{0[Q02/e0Q1eAd0RR[Q1d/b01Dd0#G\11gd0p+01KRd/:0/fd\11Dd0P3Q1C/:0P3Q24Q26Q27Q28Q1[Q2:Q0KQ23Q0kQ2;Q0i60R3Q0lQ0m;oe3o/qsP@PtP<Q1BP6Q2QP<PtP<Q1L?A<tDNDNPuPvPvQ089>vxQ1NPCPvPvQ2DPCPv1QMFRMQ2EQ08'QRF'zD{PCPvPvPvQ0yQ1nQ0T5>vQ0zDxPCPvPvPMQ1nPCQ2G=>v9EkF9EvPDPzb:b;b<X03X13X33X43X2QX5QX7Q20D2<Q2JQ1rP?P5P;CO[Q0^,02=]>EA7;U<11=<RU/0O[[[[^03^13^33^43^2Q^5Q^7QP7%GPQ0_'6Q0\Q0B/@?Q0BPSPGQ0AP6P]Q0FPfO;b9bBbEbCbDblbhbVbUbTbDbSbkbgbRbQbPbCbObjbfb]b\b[bEbZbibebYbXbWbBb6bx60L=&0jjRfePfQ0111b^Rf/0B-0HbRSPOPbPfPGCiRMQ1GQ0CQ1_/0B-0H|11g|Re/0lRlQ1\/0gRdPmPoQ1g/I0R1Q1g#41Th0\p[RRPrPnQ0jQ1J'\/qsR{P@Q0qPuPvQ1qPCPvQ1uPCPvPvQ1yQ2APCPvQ10PCPvQ13Q1t5jvPCQ14F9EvR}F9PDPzb:b;b<X03X13X33X43X83X2QX5QX7QXFQQ15Q1w1152>0PAB%B2Q1:/6JQ1<[[[[RV[^03^13^33^43^83^2Q^5Q^7Q^FQP710ej%[[PaP_PGPiPgPhP[P>PYP<PqPEO>b9b=b>b?3tWGP7O1POP|Q1_PGCiPmPoP1PRPrPnP{P@PtP5Q0rP6Q0p?A2tRRDNPuPvPvQ0wP9PCPvQ0uPCPvQ2OQ1y5jvPCPvQ1SPCPvQ1tQ0~5jvPCQ14F9F9EkPDPzb:b;b<X03X13X33X43X83X2QX5QX7QXFQ102OQ1wB03O<AQ2MQ1X>0PJ>Q1<[[[[[^03^13^33^43^83^2Q^5Q^7Q^FQP710igA7[hGPaP_PGPjP[P|PgP:PYP<PqPEO>b9b=b>b?9rldWGP7O1n200100000021100011000bqbsWAP7O1Q1AQ1Z60ck1DG?Rd9Z=7XN31aG?Q0ZPGP?Pd1:G?RlCO[1hG?Q0]Acll?[1eG?Q04Ad?ll[1bG?%Gd\T1gG?1flG\TPdP3PlP3Q0>Q1IQ0aQ0gQ1UQ0LQ0fQ1=Q0dQ1?Q1MP3P`P3Q1mQ1aQ1xQ0hQ19Q03Q1}Q1~Q20Q21Q1kP3P\P3Q1RQ1WQ1hQ0IQ1EQ1FQ0cQ17Q1VQ12Q0{P3Q0tP3Q24Q26Q27Q28Q1[Q2:Q0KQ23Q2<Q0kQ0iQ2;Q0m60R3'\3oQ2>+0K00]sP@PtP;Q2@?A5tP6Q06Q2=7A;DNPuPvPvQ2?PCPvQ1nQ0Y#KR;,QZ'zD{PCPvPvQ0yPvQ08Q2CDmPCPvPvQ2DPCPvQ1n/zFD{PCPvQ0<B09v;xQ1y5jv5jvPCQ2FQ2G5>vF9F9PDPzb:b;b<X03X13X33X43X83X2QX5QX7QQ2IQ2KQ16Q2L/6L7]A10=U[[[\N^03^13^33^43^83^2Q^5Q^7QP7Q0_P_PKPYQ0BPPPGQ0APWP6P]Q0UO<b9bBbEbCbDblbhbVbUbTbDbSbkbgbRbQbPbCbObjbfb]b\b[bEbZbibebYbXbWbBb660L=10=kR]eP]Q01Q1b/0B-0H^POP^Q1bPGCiPfP~Q1OPbC?Q0AQ1^Q1]PmPo1Ig0R~%4gQ1f/T0\p[RpPrPnP{P@Q0oPuPvPvQ2FQ11PCPvQ0uPCP}H0@EkPDPzb:b;b<X03X13X33X43X83X2QX5QX7QXFQ10=2PV[^03^13^33^43^83^2Q^5Q^7Q^FQP7Q1_/0O%[hPaP_PGPkP|Q1fPhP:PPP<PyP>O>b9b=b>b?3tXGSP7O1Q1^Q1]PmPoP~PpPrPnQ1KP@Q1B?A6RPuPvPvQ0xQ1N5jvQ0yPCPvPvQ2OQ0zPCPvQ1SPCPvPvQ1yPv20lw9H0kPCQ14F9EvEvPDPzb:b;b<X03X13X33X43X2QX5QX7QXFQQ1TB03O2>Q1z,6LQ1Y[\H[[^03^13^33^43^2Q^5Q^7Q^FQP710k|Q1l/0GPaP_PGPhPbP|PPP<PyP>O<b9b=b>b?3rXGMP7O1n200100000021100011000c0FWAP7O1n200100000021100011000W6P7O1n200100000021100011000W6P7O1n200100000021100011000W6P7O1n200100000021100011000W6P7O1n200100000021100011000W6P7O1n200100000021100011000byW~W}P6P7O2n2001000000121000000W6W|P6P7O2n2001000000121000000W6W{P6P7O2n2001000000121000000b6Y0AWnP6P7O2n2001000000121000000W6Y0BP6P7O2n2001000000121000000W6Y0DP6P7O2n2001000000121000000W6Y0EP6P7O2n2001000000121000000W6Y0@P6P7O2n2001000000121000000W6Y0?P6P7O2n2001000000121000000b6c0IY0<Y09Y08Y0>Y0CZ0M3Z0H3Y0NZ0G3Z0O3Xw3Xv4Y0=Y0Uo"). Qed.

  Definition vtail_post (x3 x4 x21 x22 x23 x24 x25 x26 x27 ra s0 s1 s2 s3 s4 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (pid : bptr) (P n V spz lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
      as_VIS H s (cfg_ms c) = MS (mkR ra (Z_to_bv 64 spz) x3 x4 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 x21 x22 x23 x24 x25 x26 x27
                                      t3 t4 t5 t6)
                                 F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo spz
      /\ rw_cells asegs m' (errno_addr x4) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB spz [(V, V + 24)] m m'
      /\ as_RHEAP H s ((pid, P, 4 * n) :: LB) m'
      /\ rw_cells asegs m' V [C8 (wz P); C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))]
      /\ rw_cells asegs m' P [CB (Z.to_nat (4 * n)) (repeat (b8 0) (Z.to_nat (4 * n)))]
      /\ addressable m' P (4 * n)
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

  Definition vt_W (S P n V : Z) : list (Z * Z) :=
    [(S - 112, S); (S - 80 - 4096, S - 80); (S - 80, S + 32); (V, V + 24); (sh P, sh P + nsh (4 * n)); (S - 16 - 4096, S - 16);
     (S - 16, S)].

  Definition vt_post (x3 x4 x21 x22 x23 x24 x25 x26 x27 ra s0 s1 s2 s3 s4 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (P n V spz : Z) (m : mem) : machine_state -> Prop :=
    fun ms => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms = MS (mkR ra (Z_to_bv 64 spz) x3 x4 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
              F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (vt_W (spz - 64) P n V) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ xpres H LB spz [(V, V + 24)] m m'
      /\ rw_cells asegs m' V [C8 (wz P); C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))] /\ addressable m' P (4 * n).

  Lemma vt_evt : forall (x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (ra s0 s1 s2 s3 s4 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : as_St H) (LB : list block) (pid : bptr)
      (P n V spz lo shi : Z),
    1 <= n <= 2 ^ 24 ->
    rw_cells asegs m (spz - 64) [C8 (wz P); C8 (wz P); C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n)); C8 (wz V); C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m V [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> SHAD m V (repeat (b8 0) 3) ->
    wins_hi [(V, V + 24)] -> aconst_ok (V, V + 24) -> vdisj V spz -> (P + 4 * n <= V \/ V + 24 <= P) -> V + 24 <= 2 ^ 47 ->
    addressable m P (4 * n) -> shvis m P (P + 4 * n) ->
    as_RHEAP H s ((pid, P, 4 * n) :: LB) m -> ~ In pid (map blk_id LB) -> ablock_range H P (4 * n) ->
    stk asegs m lo spz -> aceil <= lo -> lo <= spz - 8320 -> spz <= 2 ^ 47 ->
    mem_inv asegs m -> ACONST m -> stack0 m lo shi -> spz <= shi ->
    evt asegs (vt_post x3 x4 x21 x22 x23 x24 x25 x26 x27 ra s0 s1 s2 s3 s4 F fc LB P n V spz m)
      (MS (mkR x1 (Z_to_bv 64 (spz - 64)) x3 x4 x5 x6 x7 (Z_to_bv 64 V) (Z_to_bv 64 n) x10 x11 x12 x13 x14 x15 x16 x17
               s2 s3 s4 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 VAPP_MEMSET_RET) fc None m (seg_rom asegs)).
  Proof.
    intros until shi. intros Hn CF CV SV WH ACV VD VP V2 AD SVP RH NI ABR ST LO1 LO2 SPH MI AC S0 SHI.
    pose proof aceil_facts as ((AF1 & AF2) & AF3 & AF4).
    pose proof ABR as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    assert (NUM : AIMG_TOP = 0x6e8000 /\ ALOWSH_LO = 0x7fff7000 /\ AHI_LO = 0x10007fff8000 /\ AAPP_HI = 2 ^ 47)
      by (vm_compute; repeat split).
    destruct NUM as (N1 & N2 & N3 & N4).
    unfold wins_hi in WH. apply Forall_inv in WH. cbn [fst snd] in WH.
    unfold vdisj in VD.
    set (S := spz - 64) in *. assert (HS : S = spz - 64) by reflexivity. clearbody S.
    assert (SL : 2 ^ 45 <= S) by lia.
    assert (SU : S + 64 <= 2 ^ 47) by lia.
    assert (DJ : V + 24 <= S - 112 \/ S + 64 <= V) by lia.
    assert (P2 : P + 4 * n <= 2 ^ 47) by lia.
    assert (VBn : (0x6e8000 <= V /\ V + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= V) by lia.
    assert (P8 : P mod 8 = 0) by (clear - B16; Z.div_mod_to_equations; lia).
    pose proof (vt_shP P (4 * n) ltac:(lia) P8 ltac:(lia) BC) as SPA.
    assert (SAC : sh aceil < aceil) by (apply sh_below_aceil; lia).
    pose proof (vt_sh_lo P ltac:(lia)) as SPL.
    pose proof (sh_nsh_high P (4 * n) ltac:(lia) ltac:(lia) ltac:(lia)) as SPH2.
    pose proof (vt_iam P (4 * n) BAPP ltac:(lia)) as IAP.
    destruct (vt_cells_tl _ _ _ _ CF) as [_ CF1].
    destruct (vt_cells_tl _ _ _ _ CF1) as [CB CF2]. replace (S + 8 + 8) with (S + 16) in CF2 by lia.
    destruct (vt_cells_tl _ _ _ _ CF2) as [CE1 CF3]. replace (S + 16 + 8) with (S + 24) in CF3 by lia.
    destruct (vt_cells_tl _ _ _ _ CF3) as [CE2 CF4]. replace (S + 24 + 8) with (S + 32) in CF4 by lia.
    destruct (vt_cells_tl _ _ _ _ CF4) as [_ CR]. replace (S + 32 + 8) with (S + 40) in CR by lia.
    assert (CE : rw_cells asegs m (S + 16) [C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))]).
    { apply rw_cells_cons8; [exact CE1 | replace (S + 16 + 8) with (S + 24) by lia; exact CE2]. }
    clear CF CF1 CF2 CF3 CF4 CE1 CE2.
    assert (WRS : forall mk a k, stk asegs mk lo spz -> lo <= a -> a + k <= spz -> 0 <= k -> wr_at asegs mk a k).
    { intros mk a k (T1 & T2 & T) Ha Hk H0. split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (T (a + i) ltac:(lia))). }
    assert (STK : forall mk, wmono asegs m mk -> stk asegs mk lo spz).
    { intros mk WMk. exact (BakeStackRep.stk_high_transport m mk lo spz ST WMk ltac:(lia)). }
    assert (SHm : forall x, lo <= x < spz -> sh0 m x) by (intros x Hx; exact (sh0_of_stack0 m lo shi x S0 ltac:(lia))).
    assert (SVm : forall x, V <= x < V + 24 -> sh0 m x) by (intros x Hx; exact (sh0_of_SHAD0 m V 3%nat x SV ltac:(lia))).
    assert (ACS : forall l h, aceil <= l -> aconst_ok (l, h)).
    { intros l h Hl. apply aconst_ok_high; [| right; left; lia].
      let v := eval vm_compute in (sh AIMG_TOP) in assert (Hs : sh AIMG_TOP = v) by reflexivity.
      rewrite Hs. lia. }
    assert (XS : forall W m1 m2, munch W m1 m2 -> wmono asegs m1 m2 ->
              Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= spz) \/ (forall a, fst iv <= a < snd iv -> rin_ivs [(V, V + 24)] a)) W ->
              xpres H LB spz [(V, V + 24)] m1 m2).
    { intros W m1 m2 MUk WMk FW. eapply (xpres_weaken H).
      - exact (xpres_of_munch H s ((pid, P, 4 * n) :: LB) spz [(V, V + 24)] W m m1 m2 HH RH MUk WMk FW).
      - lia.
      - intros b Hb. right. exact Hb.
      - intros a Ha. exact Ha. }
    destruct (vt_r1 x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m S V n P
                Hn SL SU ltac:(lia) V2 ltac:(lia) B16 DJ CV CB (WRS m (S - 112) 112 ST ltac:(lia) ltac:(lia) ltac:(lia))
                (SVm V ltac:(lia)) (SVm (V + 8) ltac:(lia)) (SVm (V + 16) ltac:(lia)) (SHm (S + 8) ltac:(lia)) AC)
      as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & M1 & Hms1 & MU1 & WM1 & SK1 & CR1).
    eapply evt_of_msteps; [exact Hms1|].
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms1 MI).
    assert (AC1' : ACONST M1).
    { eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 |]. apply Forall_cons; [apply ACS; lia | apply Forall_nil]. }
    pose proof (STK M1 WM1) as ST1.
    assert (SVP1 : shvis M1 P (P + 4 * n)) by (unfold shvis in *; exact (SK1 _ _ SVP)).
    assert (X1 : xpres H LB spz [(V, V + 24)] m M1).
    { apply (XS _ _ _ MU1 WM1). apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    eapply evt_cut.
    { eapply (ah_memcpy H HH (wz 0xe9814) (wz (S - 80))) with (src := []) (junk := []) (lo := lo); try unfold wz; rewrite ?u64_of_Z by lia.
      - split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]].
      - reflexivity.
      - split; [split; [cbn; tauto | split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]] | split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]].
      - lia.
      - apply accessible_nil; lia.
      - apply accessible_nil; lia.
      - exact (shvis_nil M1).
      - eapply shvis_sub; [exact SVP1 | lia | lia | lia | lia | lia].
      - exact (proj1 (stk_split asegs M1 lo (S - 80) spz ST1 ltac:(lia))).
      - exact LO1.
      - unfold AINTRIN_STACK; lia.
      - exact MI1.
      - exact AC1'.
      - lia.
      - unfold in_app_mem. left. split; [lia|]. rewrite ASHADOW_BASE_val. lia.
      - eapply in_app_mem_sub; [exact IAP | lia | lia].
      - eapply (aconst_ok_app P (4 * n)); [exact BAPP | lia | lia].
      - left; lia.
      - left; lia. }
    intros ms2 HP2. destruct HP2 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & M2 & EQ2 & MU2 & WM2 & MI2 & _ & _ & _ & AC2).
    subst ms2.
    assert (MU2' : munch [(S - 80 - 4096, S - 80)] M1 M2).
    { intros x Hx. apply MU2. cbn [outside] in Hx |- *. unfold AINTRIN_STACK. try unfold wz. rewrite ?u64_of_Z by lia.
      destruct Hx as [Hx _]. split; [lia | split; [lia | exact I]]. }
    clear MU2.
    assert (RP2 : ret_pc (wz 0xe9814) = wz 0xe9814) by (apply bv_eq; vm_compute; reflexivity).
    rewrite RP2.
    assert (WMa : wmono asegs m M2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
    pose proof (munch_app _ _ _ _ _ MU1 MU2') as MUa.
    pose proof (STK M2 WMa) as ST2.
    assert (X2 : xpres H LB spz [(V, V + 24)] M1 M2).
    { apply (XS _ _ _ MU2' WM2). apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (SHT2 : forall x, sh0 m x -> lo <= x < spz \/ V <= x < V + 24 -> sh0 M2 x).
    { intros x Hx Hb. eapply vf_sh0_munch; [exact Hx | exact MUa | lia |].
      pose proof (sh_below_aceil x ltac:(lia)). cbn [outside app]. repeat split; lia. }
    assert (CV2 : rw_cells asegs M2 V [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
    { eapply rw_cells_transport; [exact CV | exact MUa | exact WMa |]. cbn [disjoint_from app cells_size csize]. repeat split; lia. }
    assert (CE2 : rw_cells asegs M2 (S + 16) [C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))]).
    { eapply rw_cells_transport; [exact CE | exact MUa | exact WMa |]. cbn [disjoint_from app cells_size csize]. repeat split; lia. }
    assert (CF2 : rw_cells asegs M2 (S - 80) [C8 x24; C8 x23; C8 x22; C8 x21; C8 s4; C8 s3; C8 s2; C8 (wz n); C8 (wz V); C8 (wz 0xe9310)]).
    { eapply rw_cells_transport; [exact CR1 | exact MU2' | exact WM2 |]. cbn [disjoint_from cells_size csize]. repeat split; lia. }
    assert (WV2 : wr_at asegs M2 V 24) by exact (wr_at_transport _ _ _ _ _ (proj2 CV) WMa).
    destruct (vt_r2 x3 x4 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 x25 x26 x27 u3 u4 u5 u6 s2 s3 s4 x21 x22 x23 x24 F fc M2 S V n P
                Hn SL SU VBn V2 ltac:(lia) P2 B16 DJ CF2 CV2 CE2 (WRS M2 (S - 80) 112 ST2 ltac:(lia) ltac:(lia) ltac:(lia)) WV2
                (SHT2 _ (SHm (S + 8) ltac:(lia)) ltac:(lia)) (SHT2 _ (SVm V ltac:(lia)) ltac:(lia))
                (SHT2 _ (SVm (V + 8) ltac:(lia)) ltac:(lia)) (SHT2 _ (SHm (S + 16) ltac:(lia)) ltac:(lia))
                (SHT2 _ (SVm (V + 16) ltac:(lia)) ltac:(lia)) (SHT2 _ (SHm (S + 24) ltac:(lia)) ltac:(lia))
                (SHT2 _ (SHm S ltac:(lia)) ltac:(lia)) AC2)
      as (c0 & c1 & c2 & d4 & d5 & d6 & d7 & c3 & c4 & c5 & c6 & M3 & Hms2 & MU3 & WM3 & _ & CV3 & CF3 & CB3).
    eapply evt_of_msteps; [exact Hms2|].
    assert (MI3 : mem_inv asegs M3) by exact (msteps_mem_inv asegs _ _ Hms2 MI2).
    assert (AC3' : ACONST M3).
    { eapply ACONST_frame; [exact AC2 | exact MU3 | exact WM3 |].
      apply Forall_cons; [apply ACS; lia | apply Forall_cons; [exact ACV | apply Forall_nil]]. }
    assert (WMb : wmono asegs m M3) by (eapply wmono_trans; [exact WMa | exact WM3]).
    pose proof (munch_app _ _ _ _ _ MUa MU3) as MUb.
    pose proof (STK M3 WMb) as ST3.
    assert (X3 : xpres H LB spz [(V, V + 24)] M2 M3).
    { apply (XS _ _ _ MU3 WM3). apply Forall_cons; [left; cbn [fst snd]; lia|].
      apply Forall_cons; [right; intros a Ha; cbn [rin_ivs fst snd]; left; cbn [fst snd] in Ha; exact Ha | apply Forall_nil]. }
    assert (AD3 : addressable M3 P (4 * n)).
    { eapply addressable_transport; [exact AD | exact MUb | exact WMb |]. cbn [disjoint_from app]. repeat split; lia. }
    eapply evt_cut.
    { pose proof HANN as HA. unfold annotate_gen_stmt in HA.
      eapply HA with (beg := P) (len := 4 * n) (oldmid := 4 * n) (newmid := 4 * n) (lo := lo); try unfold wz; rewrite ?u64_of_Z by lia.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact P8.
      - lia.
      - lia.
      - lia.
      - exact BAPP.
      - lia.
      - rewrite cc_gen_full. exact (proj2 AD3).
      - exact (proj1 (stk_split asegs M3 lo (S - 16) spz ST3 ltac:(lia))).
      - exact LO1.
      - unfold AINTRIN_STACK; lia.
      - exact MI3.
      - exact AC3'.
      - exact IAP. }
    intros ms4 HP4.
    destruct HP4 as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & M4 & EQ4 & MU4 & WM4 & MI4 & _ & SH4 & AC4).
    subst ms4.
    assert (MU4' : munch [(sh P, sh P + nsh (4 * n)); (S - 16 - 4096, S - 16)] M3 M4).
    { eapply munch_eqW; [exact MU4 |]. try unfold wz. rewrite ?u64_of_Z by lia. unfold AINTRIN_STACK. reflexivity. }
    clear MU4.
    assert (RP4 : ret_pc (wz 0xe9eb0) = wz 0xe9eb0) by (apply bv_eq; vm_compute; reflexivity).
    rewrite RP4.
    assert (WMc : wmono asegs m M4) by (eapply wmono_trans; [exact WMb | exact WM4]).
    pose proof (munch_app _ _ _ _ _ MUb MU4') as MUc.
    pose proof (STK M4 WMc) as ST4.
    assert (X4 : xpres H LB spz [(V, V + 24)] M3 M4).
    { apply (xpres_of_apres H LB spz [(V, V + 24)] M3 M4).
      apply (apres_fresh H HH s LB pid P (4 * n) spz m M3 M4 _ RH NI MU4' WM4); [| lia].
      apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_cons; [right; right; cbn [fst snd]; lia | apply Forall_nil]]. }
    assert (SHT4 : forall x, sh0 m x -> lo <= x < spz -> sh0 M4 x).
    { intros x Hx Hb. eapply vf_sh0_munch; [exact Hx | exact MUc | lia |].
      pose proof (sh_below_aceil x ltac:(lia)). pose proof (vt_sh_lo x ltac:(lia)).
      pose proof (sh_below_app x ltac:(lia)). assert (sh aceil <= sh x) by (apply sh_mono; lia).
      cbn [outside app]. repeat split; lia. }
    assert (CF4 : rw_cells asegs M4 (S - 16) [C8 (wz V); C8 (wz 0xe9310)]).
    { eapply rw_cells_transport; [exact CF3 | exact MU4' | exact WM4 |]. cbn [disjoint_from cells_size csize]. repeat split; lia. }
    assert (CB4 : rw_cells asegs M4 S [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
    { eapply rw_cells_transport; [exact CB3 | exact MU4' | exact WM4 |]. cbn [disjoint_from cells_size csize]. repeat split; lia. }
    assert (CR4 : rw_cells asegs M4 (S + 40) [C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact CR | exact MUc | exact WMc |]. cbn [disjoint_from app cells_size csize]. repeat split; lia. }
    destruct (vt_r3 (wz 0xe9eb0) x3 x4 w0 w1 w2 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 x21 x22 x23 x24 x25 x26 x27 w3 w4 w5 w6 ra s0 s1 F fc M4 S V n
                Hn SL SU ltac:(lia) V2 CF4 CB4 CR4 (WRS M4 (S - 16) 16 ST4 ltac:(lia) ltac:(lia) ltac:(lia))
                (SHT4 _ (SHm (S + 8) ltac:(lia)) ltac:(lia)) (SHT4 _ (SHm (S + 16) ltac:(lia)) ltac:(lia)) (SHT4 _ (SHm S ltac:(lia)) ltac:(lia))
                AC4)
      as (e0 & e1 & e2 & f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & e3 & e4 & e5 & e6 & M5 & Hms3 & MU5 & WM5 & _).
    eapply evt_of_msteps; [exact Hms3|].
    apply vt_ret.
    assert (X5 : xpres H LB spz [(V, V + 24)] M4 M5).
    { apply (XS _ _ _ MU5 WM5). apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    unfold vt_post. rewrite <- HS. replace (S + 64) with spz by lia.
    exists e0, e1, e2, f0, f1, f2, f3, f4, f5, f6, f7, e3, e4, e5, e6, M5.
    split; [reflexivity|].
    split; [exact (munch_app _ _ _ _ _ MUc MU5)|].
    split; [eapply wmono_trans; [exact WMc | exact WM5]|].
    split; [exact (msteps_mem_inv asegs _ _ Hms3 MI4)|].
    split.
    { eapply (xpres_trans H); [eapply (xpres_trans H); [eapply (xpres_trans H); [eapply (xpres_trans H); [exact X1 | exact X2] | exact X3]
                                                         | exact X4] | exact X5]. }
    split.
    { eapply rw_cells_transport; [| exact MU5 | exact WM5 |].
      - eapply rw_cells_transport; [exact CV3 | exact MU4' | exact WM4 |]. cbn [disjoint_from cells_size csize]. repeat split; lia.
      - cbn [disjoint_from cells_size csize]. repeat split; lia. }
    eapply addressable_transport; [| exact MU5 | exact WM5 |].
    - split; [lia|]. rewrite cc_gen_full in SH4. exact SH4.
    - cbn [disjoint_from]. repeat split; lia.
  Qed.

  Lemma vtail_sr' : forall (x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (ra s0 s1 s2 s3 s4 : word) (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H)
      (LB : list block) (LF : list fframe) (pid : bptr) (P n V spz lo B shi : Z) (errv : word) (mo : Model),
    as_VIS H s msF = MS (mkR x1 (Z_to_bv 64 (spz - 64)) x3 x4 x5 x6 x7 (Z_to_bv 64 V) (Z_to_bv 64 n) x10 x11 x12 x13 x14 x15 x16 x17
                             s2 s3 s4 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 VAPP_MEMSET_RET) fc None m (seg_rom asegs) ->
    1 <= n <= 2 ^ 24 ->

    rw_cells asegs m (spz - 64) [C8 (wz P); C8 (wz P); C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n)); C8 (wz V); C8 s1; C8 s0; C8 ra] ->

    rw_cells asegs m V [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> SHAD m V (repeat (b8 0) 3) ->
    V mod 8 = 0 -> 0x6e6000 <= V -> V + 24 <= 2 ^ 47 -> wins_hi [(V, V + 24)] -> stack0_ok (V, V + 24) ->
    aclient_range H LB spz V 24 -> aclient_range H LB spz (sh V) 3 ->
    aclient_write_ok H LB (V, V + 24) -> afs_write_ok H LF (V, V + 24) -> aconst_ok (V, V + 24) -> vdisj V spz ->

    rw_cells asegs m P [CB (Z.to_nat (4 * n)) (repeat (b8 0) (Z.to_nat (4 * n)))] ->
    addressable m P (4 * n) -> shvis m P (P + 4 * n) ->
    as_RHEAP H s ((pid, P, 4 * n) :: LB) m -> ~ In pid (map blk_id LB) -> ablock_range H P (4 * n) ->
    as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> spz <= B ->
    stk asegs m lo spz -> aceil <= lo -> lo <= spz - 8320 ->
    rw_cells asegs m (errno_addr x4) [C4 errv] -> mem_inv asegs m -> x4 = Z_to_bv 64 ATP ->
    spz mod 16 = 0 -> spz <= 2 ^ 47 -> ACONST m -> as_RFS H LF m -> stack0 m lo shi -> spz <= shi ->
    as_SR H (vtail_post x3 x4 x21 x22 x23 x24 x25 x26 x27 ra s0 s1 s2 s3 s4 F fc s LB LF pid P n V spz lo B shi m mo) (mkCfg msF mo).
  Proof.
    intros until mo.
    intros VIS Hn CF CV SV V8 V0 V2 WH S0V ACR ACRS AWO AFS ACV VD CP AD SVP RH NI ABR KR RA SPB ST LO1 LO2 ERR MI TP SP16 SPH AC RF S0 SHI.
    pose proof aceil_facts as ((AF1 & AF2) & AF3 & AF4).
    pose proof ABR as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    assert (VP : P + 4 * n <= V \/ V + 24 <= P).
    { apply (client_fresh_disj s LB pid P (4 * n) spz m V 24 RH NI ACR); lia. }
    eapply (sr_evt H HH _ (vt_post x3 x4 x21 x22 x23 x24 x25 x26 x27 ra s0 s1 s2 s3 s4 F fc LB P n V spz m)); [exact KR | exact VIS | |].
    { exact (vt_evt x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ra s0 s1 s2 s3 s4 F fc m s LB pid
               P n V spz lo shi Hn CF CV SV WH ACV VD VP V2 AD SVP RH NI ABR ST LO1 LO2 SPH MI AC S0 SHI). }
    intros msF' mo' KR' MP' HP.
    destruct HP as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EQ & MU & WM & MI' & XP & CV' & AD').
    assert (NUM : AIMG_TOP = 0x6e8000 /\ ALOWSH_LO = 0x7fff7000 /\ AHI_LO = 0x10007fff8000 /\ AAPP_HI = 2 ^ 47)
      by (vm_compute; repeat split).
    destruct NUM as (N1 & N2 & N3 & N4).
    assert (NUM2 : ATP <= AIMG_TOP /\ ATLS_PRIV_HI <= AIMG_TOP) by (split; apply Z.leb_le; reflexivity).
    destruct NUM2 as (N5 & N6).
    pose proof (ah_fsb H HH _ _ _ RH) as (FS1 & FS2 & FS3 & FS4).
    unfold aapp, aapp_lo, aapp_hi in FS4, BAPP.
    assert (P8 : P mod 8 = 0) by (clear - B16; Z.div_mod_to_equations; lia).
    pose proof (vt_shP P (4 * n) ltac:(lia) P8 ltac:(lia) BC) as SPA.
    pose proof (vt_sh_lo P ltac:(lia)) as SPL.
    pose proof (sh_nsh_high P (4 * n) ltac:(lia) ltac:(lia) ltac:(lia)) as SPH2.
    assert (SPI : sh AIMG_TOP <= sh P) by (apply sh_mono; lia).
    unfold wins_hi in WH. apply Forall_inv in WH. cbn [fst snd] in WH.
    unfold vdisj in VD.
    subst x4.
    set (W := vt_W (spz - 64) P n V) in MU.
    assert (ACS : forall l h, aceil <= l -> aconst_ok (l, h)).
    { intros l h Hl. apply aconst_ok_high; [| right; left; lia].
      let v := eval vm_compute in (sh AIMG_TOP) in assert (Hs : sh AIMG_TOP = v) by reflexivity.
      rewrite Hs. lia. }
    assert (FA : Forall (aclient_write_ok H ((pid, P, 4 * n) :: LB)) W).
    { unfold W, vt_W. repeat apply Forall_cons; try apply Forall_nil;
        first [ left; cbn [fst]; lia
              | apply aclient_write_ok_cons; exact AWO
              | right; right; right; left; exists (pid, P, 4 * n); split; [left; reflexivity | cbn [blk_addr blk_size fst snd]; lia] ]. }
    assert (FF : Forall (afs_write_ok H LF) W).
    { unfold W, vt_W. repeat apply Forall_cons; try apply Forall_nil;
        first [ exact AFS | left; cbn [fst snd]; split; lia ]. }
    assert (FC : Forall aconst_ok W).
    { unfold W, vt_W. repeat apply Forall_cons; try apply Forall_nil;
        first [ exact ACV | apply ACS; lia | apply aconst_ok_high; [exact SPI | right; left; lia] ]. }
    assert (FS0 : Forall stack0_ok W).
    { unfold W, vt_W. repeat apply Forall_cons; try apply Forall_nil;
        first [ exact S0V | left; cbn [fst]; lia | right; cbn [snd]; lia ]. }
    destruct (client_frame H HH s _ LF B W m m' RH RF AC RA MU WM FA FF FC) as (RH' & RF' & AC' & RA').
    hnf. cbn [cfg_ms cfg_model].
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', errv.
    split; [exact EQ|]. split; [exact KR'|]. split; [exact MP'|]. split; [exact MI'|].
    split; [exact (BakeStackRep.stk_high_transport m m' lo spz ST WM ltac:(lia))|].
    split.
    { eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. rewrite u64_of_Z by (unfold ATP; lia).
      unfold W, vt_W. cbn [disjoint_from cells_size csize]. repeat split; lia. }
    split; [exact RA'|]. split; [exact XP|]. split; [exact RH'|]. split; [exact CV'|].
    split.
    { eapply rw_cells_transport; [exact CP | exact MU | exact WM |]. unfold W, vt_W. cbn [disjoint_from cells_size csize]. repeat split; lia. }
    split; [exact AD'|]. split; [exact RF'|]. split; [exact AC'|].
    exact (stack0_transport W m m' lo shi S0 MU WM FS0).
  Qed.

End VecT.

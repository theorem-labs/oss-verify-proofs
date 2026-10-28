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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGb2 LbB_RG2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_RGb1 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List=repeat_lengthC47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic7f_equalI47Corelib4Init5Logic3and00C46Stdlib4Bool4Bool=andb_true_iffC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_sizeC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic2or01C56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes6option01C46Stdlib5Lists4List2InK47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedI45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_readableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC56Stdlib6NArith6BinNat1N6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBsegment_read_bytesc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb1?find_segment_inC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs?asegs_below_topC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI47Corelib7Numbers7BinNums1N00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4SHADC56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BArr5u8arrC47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem8bytes_atC56Stdlib6ZArith6BinInt1Z6of_natC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem3mrdC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem2waC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb1:seg_rom_hiI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3memC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2b8C47Corelib5Lists7ListDef6repeatc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb15obandC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3mkRC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC4ARocqVerifyHarness?AgentSubmission8PropExec4getrI47Corelib4Init9Datatypes4prod00K7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2wzI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib<regs_ok_seedK45stdpp9bitvector;definitions2bv01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K47Corelib4Init9Datatypes4prod01C47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC47Corelib4Init3Nat3subC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6reg_evK5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib;regs_ok_srsC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst=ACONST_shbaseC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst:ACONST_uarK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell02C56Stdlib6ZArith6BinInt1Z3mulC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses;rew_iff_revC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<sh0_of_SHAD0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit2gzC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega5Tauto8GFormula07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry04K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry05K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry08K5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6kn_fixC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?kimg_of_mem_invC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_addC5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8srl3_valK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S4flatC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb19SHAD_baseC46Stdlib5Lists4List@nth_error_repeatC56Stdlib6ZArith4Znat5Z2Nat2idC35stdpp7tactics<f_equal_helpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<kwr_of_wr_atC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv:kwr_of_stkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8kshadow0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit3sh0C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotK4ARocqVerifyHarness?AgentSubmission8PropExec7FPState01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC4ARocqVerifyHarness?AgentSubmission7SymRun39run_soundC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC4ARocqVerifyHarness?AgentSubmission8PropExec4mkstC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<wr_at_of_stkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge9rfull_mkRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge;msteps_fullC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call=regs_keep_mkRK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6w_addmC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26e_addrC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28expr_eqbC5ARocqVerifyHarness?AgentSubmission8SymExec33SX27e_widthC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv9sb_insideC47Corelib4Init9Datatypes3orbC46Stdlib5Lists4List7forallbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvBmunch_mem_denot_2bC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv9munch_eqWC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?wmono_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge>msteps_mem_invC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv=stk_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv6blk_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv@other_disj_of_2bC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvBrw_cells_log_blockC47Corelib5Lists7ListDef6firstnC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells6cbytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvCrw_cells_log_nth_2bC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv@rw_cells_cons8_cK47Corelib4Init5Logic2ex01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoI4ARocqVerifyHarness?AgentSubmission6CatSim6msteps00K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvAkword_of_rw_cellsC4ELinuxProcessSemantics5Riscv3Sem5alu64K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv5tb_okC46Stdlib9micromega;ZifyClasses8or_morphI7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_RG28rg_cellsI5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst;AGOT_SHBASEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst<ASHBASE_CELLC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst8AGOT_UARC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst9AUAR_CELLK46Stdlib9micromega=RingMicromega3Op201C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs<ASHADOW_BASEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow@ASHADOW_BASE_valI5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK4ELinuxProcessSemantics5Riscv5Instr5aluop01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqI5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3memc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb18RG_STACKc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb17RG_CTORC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<AFS_MALLOC_1c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb19CS_SM_RETc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb15MT_FAc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb19CS_RET_RAI5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb1;HTLbARGb1_0C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idK4ELinuxProcessSemantics5Riscv5Instr5aluop07C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEI5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00K47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3ivlC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_RG28rg_words".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition RG_CTOR : Z := 0x100618.
Definition CS_SM_RET : Z := 0x100790.

Definition RG_STACK : Z := 2608 + AFS_STACK.
Definition MT_FA : Z := 6364136223846793005.
Definition CS_RET_RA : Z := 0x1006d8.

Lemma find_segment_in : forall segs x n seg, find_segment segs x n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= x /\ x + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_RGb1 ()) [] "p'0h01Hh11Eh22Hfh31nh43segh54segsh61xh72E1h82E2h97__arithh:4__x1h;4__x2h<4__x3h=4__x4h>2b1h?2b2h@4cstrhA5cstr0hB1ehC1mhD2H1hE2H2hF3HinhG2IHhH4__ffhI8__varmaphJ5__withK1ahL1bi001bhM2sgi011oi021sp;1p;3p;2p;6p;4p;7p;5p;8p10000p4p7210p1000\p4p710p8p1001:p4p710g001\R0p4p710p8g0028j1MTg002XR1j1iTg003:j3BTg004>j35Tg004Xj24Tg0055j1ITg005Uj1HTP0j6TTg0067j2gTg006Vj22Tg0073j2@Tg007Qj2GTg007kj6[Tg008HR0j2=Tg008cj2ZTg009Dj1FTg00:Bj1;Tg00:`j1CTg00;^j23Tg00<:j2YTg00<Zj3XTg00=4j1DTg00=Wj2KTg00>5j1WTg00>Sj4OTg00?1j1VTg00?Oj1UTg00@:j1JTg00@_j2ETg00ABj1hTg00Agj3STg00BJj4LTg00C5j7fTg00CYj2cTg00D;j2bTg00Dgj3aTg00EFj4_Tg00F8j4RTg00FSj3^Tg00Fmj5]Tg00GOj2`Tg00H1j3NTg00HHj3\Tg00Hhj7dTg00ILj8eTg00J0R2f0R3'`p=>%F3#;p=0%C3#;p=?f2R4f1R5/43'3p=A1345/=3p=6AN245/=3p=9A\253p=:%C3#;,45p=71445/33p=8g00JoR6g00KOR7753p=1AN253p=<P5g00KoR8g00LNR9P9g00LnR:P3g00MNFdp=Qf3R;P8P9P9P:P4P5P3Gep=P%M2R<P2g00MnR=%i2R>AB;45%>3R?35f4R@%05RA14;4RB%?57AA76;595[^42^3=]6RAX5<%I2RC?B45=5>?P>%H2P1P2p-0P3g00NLRDg00Nin10110100021000000XB>g00OE%>5P3ETPD%04RD14@;RE%?47AD76@994C/g3b0W2X42X3=X6=f5RC/:@?B45=5>?f6R?#0RD/2;17D?RF,2B'@P61G63f7RB#0RG/2@17GBRH,2E'@=563P6f9RE#0RI/2?14?C17IERJ'2'@=563P6P>P5f:RK#>RLABEB?n0100000020000%>CRM55>f;RN/:Kf8ROA8OBF56DRD59?]2]1P5%0ORF/2C14C@17FO'2'@RF#1%>E%>@RP55>P>P2P1P2P2P3P3PNn10110100021010200XB>PLPMP3E[A52KCA52N?P2f<RMf=RL/:M%03R114KERQ%?37A176K593X42P01@53#1%14R1%15RR'=[RS%13,=R1@45#1RR[%1;/=1\R1Z53P5n2001000000120000000X?6X>6PS^?6^>6P3%0LRS/2KRR17SLRS,2QRQP@O3%1R%1Q'=P0f>RQ#FRR#;R1/2N#114NKRT171QRU'2#1f?RV1:VQ%0VRW14MNRX%CVRY#;RZ7AW76M39P3f@RW#0/2L#114QLfAR[#0R\%?[R]'4'2#1P01253#11345[R^13531245#1R_[13;4\_1Y53P5n2001000000120000000XC=X3=R_P^^C=^3=R^P3fCR`#0RaPWP4O313aWP_P^P3fBR^/4[R[fER_#0/7_RaP;O313[afFRa1:a_'<%FaR[#;Rb17ba98`^76`A52aa1<a_1G2a3X%D[g00OaR[/3bfG#CRb#D%;b,3[g00P?Rb#I%MbP=P=1K=@P4%W=COP51K=;CO%V=%U=RbP=g00PkRc#JRd,E=Re%hc,E=5S=g00QPRf1E=cRc%Jd,E=5S=CL,QbRd%H9RgPbP=PcPfPeCL,QbRePgPbP8P9P9P:PePdFfCPCP1cb:P3P41G671b34#1dAa=[5C_bHbIbJX:=X;=X<=X==R7143;98541354144C98;@964;[[^:=^;=^<=^==RbP3fIR:#?P_Pa%0:P;PCO6b9bAb@CRb8b0b7b0W8W7P5P3O2n2001000000121000000b1b0PBP3ETW0P3O1b0W2W1g00R7956FABO?C=5>PPOPBP?PCP3O4%0CRP17PC98B?76B99CEP01<?KPD1:MNA8EOH96GE59BP31<OM13TJ96INP0%0KR0/3M%?K9AX01:WV%0NR0170N98LM76L59NP3%0M/3QA8VQS1:`^,<QA8WVU961WA52`Q1<Q^;^C%DR13[1%DY13[ZP7PbP3P]P^P`P\P;P@O6b9bAb@CRWEWDP5P3O2n2001000000121000000W0WFP5P3O2n2001000000121000000bKW2W1n0110000020101P3P4O2b1bLW2X42X3=X6=XGAX5<XM2P3D]W5o"). Qed.

Lemma seg_rom_hi : forall x, AIMG_TOP <= x < 2 ^ 64 -> BLPropExec.seg_rom asegs (Z_to_bv 64 x) = None.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_RGb1 ()) [] "p'0h06__sat4h14__x1h24__x2h31Eh44__p1h54__x3h64__x4h71xi001xh87__arithh94__ffh:6__sat3h;8__varmaph<5__with=4cstrh>5cstr0h?1Hh@2H0hA2H1hB2H2hC2HahD4__p2hE4__x5hF1zhG3HinhH2HxhI1mhJ1nhK1oi011ohL3segi023seghM1yi031bi041li052l0i061sp&0p;2p;1p;3p;5p;4p;6p;<p;Bp;7p;8g00;^R0j20Tg00@:j1@Tg00RWj1VTg00S5j2mTg00SRj2:Tg008HR1j26Tg00Snj1RTg00TLj2aTg00U2j2gTg00:BR2j1;Tg003:j3CTg002XR3j1STg007Qj2DTg004>j34Tg00U\k105Tg0028R4j1iTg00V?j1MTg00WAj1OTg00X@j2LTg00X]j1FTg00Y;j1xTg00Y[j3HTg005Uj1JTg00GOj2`Tg00Zej5qTg00[jj2nTg004XR5j23Tg00\kj1lTg00]Ij4kTg00]lj4]Tg00:`j1\Tg00=4j1PTg009Dj1[Tg00^Sk207Tg00_;k306Tg00__k204Tg00`@j1ATg00`_j2hTg00aHj2ZTg0055k103Tg00HHj3XTg00=Wj2NTg00>5k102Tg00>Sj4ETg00?1k101Tg00?Oj1{Tg00b4j2QTg00ABj1dTg00@_j2BTg00Agj3KTg00bWj3zTg00BJj4bTg00CYj2wTg00D;j2vTg00Dgj3uTg00EFj4tTg00c:j2fTg001\j6cTg00d4j2sTg00H1j3rTg00e6l<|Tg00e[lB}Tg00fAl<~Tg00ffj3pTg00Hhj7eTg00C5k700Tg00ILj8UTg00gOj6oTf2R6f1R7f0R8'a'gp=1%[8#;p=2g00J0R9g00h3R:7r8p=Y%\8#;p=8f3R;/361378'0p=91367/08p=>g00MnR</D8p=<g00hjR=P<P<P<P2P2f5R2f4R>P;P6P7P8M<|p=jP<P<P<P<P<P<P5P8P7P6P5P;P>P2f6R5f7R?f8R@f9RAMB}p=_P<P<P0P?P0P5P2P>P;P6P7P8M<~p=^g00OaR0/08p=51h<8p=?Ap<78p==P6g00KoRBg00LNRCPCg00LnRDP<P7g00QPP8Cbg00MNREFep=7P7PBPCPCPDP8PEFep=yP6PBPCPCPDP7P8K00p=GP;PBPCPCPDP6P7P8GUp=WP5PBPCPCPDP2P>P;PBPCPCPDP6P7P8GUGUp=IP7PBPCPCPDP8Eop=Tg00iHRB/08g00PkRE#@RF#VRG%@FRH#@RI#@#@#@RJ#VRK'mRL,:8'6%RJRJ1aJ7RM'g%RERN#;RO5C:%S9RP1DP8A1JJ6=C:O=4P8P3P9A1JJ>=C:O=4P8%RI$05RI#SRQP3%iIRRPQP3P9%SRRSP7g00JoRTPS%M8%O8A1JJ5RU%28'L#F%xNRV3H%JRRWn0100000020000PWn10110000021010200P4PIPQP8%JIR41`I7n10110400020020103105RIP4n10110000021010400;44]3P7A1JJ2=C:O1`9854PP:PUPOP7P8Dq%Y7%27RX/0UPUPOPX%87C9'6'6P1%Y6%26RXA1JJ?RU'0PUPOPX%86C9'6P3PRPQPTPS%M;%O;A1JJ@%2;'L#F;HVPWn0100000020000PIP4n10110000021010400=4Q4P8%Y>%22RXf:RU91JJRY'0PYPOPX%82C9'6P1%25R1f;RX91JJRY'0PYPOP1%85C9P3PRPQPTPS%M?%O?f<R191JJ%2?'L#F;HVPWn0100000020000PIP4n10110000021010400=4Q4P8%2@f=RY91JJ'0f>RZ91JJPO%2A%8AC91nU2%2U%8U;>BP<f@RU91JJR[%21R\/08XF<P6PU13[OR]%2XR^%8XRX'3R_'0%VER`=>[_RaP8X7<Rb1078#lXM<X7<RcP]PbP`O1R],3[PbPbPbP<P<g00jB1378Ck#<XI<XJ<RdP[P[%<[POP]PbPb%;8#<X7=PNP`%<`EjRNM:_P_PbP^O1PbPXO1'3RX%<XA4<_XeG^P7C]Pa%\1R1#P%;1R1#5%[YRa#P%;aRa#5207GKRX1:0GR_%5K1:0L[R=[R[%5GReg00NiRfB06GK7UWCRK%5L\f^CeReP7g00jf2040G'DP_eO1R_P=g00P?Rfg00kLRg#ARh#ARi#ARj#ARk#ARl#A#?%?l%?k%?j%?iRi1h<gRg'='=Rj'='='=g00kkRk'Z&03fRl3X%ifRmP<P<1N<>P6&02<RnCERoP7P<1N<2P;PnCECE&01<Rp%{<Rq1Q<0Rr%dE,B<Rs57qRt%JCRCPq1B<HRH1Q<`Ru5K<%dF,B<9K<sRv57qPCPq1B<FRF97qvPCPqA7qsHPCPq1B<ERE97qFP<PEg00lW1Q<G=z<JCb,yqRG5GqPCA7qrE=GqGRrCWFIFI1wqDRDP8P6g00KORv,DT1v86=4TvdAu<07CtR0b9b;b<X1<X2<X5<X6<XE<%56P>P`P;P2C9A>>5;1025102>1:>L'6%521:2L'6[[[[[^1<^2<^5<^6<^E<P8fBR2#8fGRv91JJ%22PBPvP>P5P?PAfFO:b8b0b:b0b>b=b@,fUEc10^UP<fAR^91JJRUP8POPa%\YRY#;RaC9XF<P6P^13UORA13\1R2'0A>U`2RwPbPcPA13U]PbPbPbPdPUPU%<UPOP]PNM:_P2PbP\O1PbP1O1'3R1%<1A4<21eG^P6C]Pw%PYRY%5aRa%[ZRZ#PRw%;Z#5RZPXP[PKPeP_P=p-0R11Zjk=XflPmP<PnP71N<6CEPpPqPtPCPqA7qsEPCPq1Tq>=GqGPCPrCWFIPDP0b9b;b<X1<X2<W4%5710671:6L,6>%5;1:;L'6[[[^1<^2<^41P8fHRr,0BfCRG#2RtPrP>P?PvO6b8b0b:b0b>b=b@,f^EcA>^O2PYPaPwPZPXP[PKPeP_P=%?h/=g,=i/Zk=XflPmP<PoP71N<;CEPpPqAK<sHRH=7qEPCPqAK<Fu=7qHPCPqA7qEF1Tq55GqPC1Tq?CWFIPDP0b9b;b<X1<X2<X5<X6<X41XD1A>6;8P6P`P;P>C9106;/65P@[[[^1<^2<^5<^6<^41^D1P8P3PRPQPTPS%MG%OGA1JJr/Lt#F;HVPWn0100000020000PIP4n10110000021010400=4Q41:rL%8GPtPrPBP@P5PvO9b8b0b:b0b>b=bBbAb?WBWAP7P8O2n2001000000121000000W?WGP7P8O2n2001000000121000000b3W3XL9P8O1A1JJ;=C:O%J954P1DQ4W3n10110100021110600P8O1b3bK1s:M=4Q4eWHX7<o"). Qed.

Lemma SHAD_base : forall m A sbs j, SHAD m A sbs -> (j < length sbs)%nat -> AIMG_TOP <= sh A ->
  m (wa (sh A + Z.of_nat j)) = nth_error sbs j.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_RGb1 ()) [] "p'0h01Bh11Hh22Emh31ih41oi001oh52Hah67__sat11h74__x1h84__x2h94__x3h:4__x4h;1Ah<2A0h=2A8h>2B0h?2B1h@2HjhA3Hj0hB2HshC2_HhD7__arithhE4__ffhF7__sat10hG6__sat9hH8__varmaphI5__withJ1bi011bhK4cstrhL5cstr0hM1jhN1mhO3sbsi021xp;1p;3p;2p;4p;7p;6p;<p;8g00@:j19Tg00Snj1^Tg00U\j1fTg0028j1STg00m>j3xTg00RWj1PTg00n7j2BTg00nWj10Tg00oNj4CTg008HR0j2>Tg010Hj21Tg010hR1j26Tg002XR2j1rTg011@j4XTg012=R3j13Tg012]j4GTg00S5j2eTg00;^j28Tg013Wj3ATg007Qj2:Tg004>j32Tg00GOj2VTg004Xj2=Tg014Oj1OTg00d4j2NTg015Fj3MTg005Uj1UTg00TLj2bTg00SRR4j2?Tg00]lj4`Tg015dj1RTg00^Sj2_Tg00_;j3wTg016Ij3vTg00__j2uTg00`@j1KTg00`_j2@Tg00ffj3ITg00aHj2]Tg0055j1qTg00HHj3TTg00>5j1mTg00=Wj2[Tg00>Sj4ZTg00?1j1lTg00?Oj1kTg00b4j2YTg00ABj1jTg00@_j2JTg00BJj4QTg00Agj3WTg00bWj3iTg00C5j7hTg00CYj2gTg00D;j2nTg00Dgj3oTg00EFj4dTg017:j2pTg001\j6\Tg00fAl<cTg00Hhj7sTg00ILj8tTg00OaR5f0R6'8p=4g00MnR7?265p=Dg00iHR8/86p=<f1R9%36'=#Op=7f4R:f3R;f2R<?M9632p=5%36,=9p=L1=96#Op=Eg018:R=P7P1P3P4g018Yf5R4P:P;P<P9P6M<cp=aP7P9g00QPP6CQp=HP9g00KoR3g00LNR1P1g00LnR>P6g00MNFsp=;P;P3P1P1P>P<P9P6Gtp=Fg019;g00PkR?#9R@#9#9RA#^#fRB#SAx;<9P0%4;%PARC,B;#Dg00h3RDP:%0;P<CC'>11B;,6<%04#<%rBREf7RFf6RG#0RH/7:O1PBP4P:D5[[P6%441BGC#DPDPFPHP4CC'>P01BFC#DPDf8RH%0FPGCC11BF,6Gf9RI#0#<PEf;RJf:RK#0RL/7HO1PBPIPHD5[[P61BIC#DPDPJPLPICCP0PDf<RI%0JRLPKCXPDPIPL11BK#3CG11BJ,6Kf=RK#0RJ#<PEf?RLf>RH#0RM/7IO1PBPKPID5[[P6PDPHPJPICXP0%4M11BK,LM%P@RM%9A#9#9RA#PRI'eRJ'811BHRN,66PEfAROf@RP#0RQ%39RR'E5ADPBPLP9D5[^3='>PDPP%0L%3NCG11BL,6H%0ORH#<PEfCRLfBRN#0RS/7PO1PBPOPPD5[[[P6%4Q11BP,LH/8J11BORH,66PEfDRP%0LRQ/ER5ADPBPNP9D5[^3='>P01LSH/8J11BNRH,66PEfERS%0PR0/ER5ADPBPLP9D5[^3=PDPPPQ%3HCG11BLRL,6N%0S#<PEfGRNfFRH#0RQ/7PO1PBPSPPD5[[[P61L0L/8J11BSRL,66PEfHR0%0N/ER5ADPBPHP9D5[^3=PDPNPQ%3LCG11BH,6S%00#<P;PNP9O2PEfJRSfIRH#0/7N5ADPBP0PND5fKRN%0S/70O1PE1:E6fLR0%0N/7HO1=2E6P2PBfNRHfMRL#0/7NRQO1=2E6P2PBPEP91VB6R2%0H%30RR'=RP#ORT,NDn10110200021010100AMBL0RU52EAMBHLRH92E<]0]2P9fORVPTO1=2E21VB9=2EHP6W0W2XJBP6O1PL%00/7SO1%UBRS52EPE1NDQPBP0PND5PE%^ARA/bP,NDA2E6HX4EP6PS11BLRD,60%3DRN,?RRQP0PR1:7RPDPN1:7NEaPGC`PQ%RL%3L#411BVRV#R%3V#41_MI1?5MRV%4I1?5J[RQ[%4MRNg00NiRDAwMI9UW5%4J\D^5NfS?vCL%4CfTRL/BC#4[P<g00jf1u5M':PVeO1PQg00P?RQg00kLRV#KRC#KRN#KRD#K,@71@7N1@7VRV5I75I7g00kkRN']1@7D1@7C=I7V5I7/]N%qQ5TQ3T%SQP7P7%m7P<1[7:CZP91[7;CZ%l7%k7RQ1Y75%j?RN,J7RV'H,;Q%U1RCPQP7PVg00lWRD%9N,J7RNCQ,;QPCPQ1J7?R?1J7@R@'H,;QPCPQAW7@N1Y7M=i7ARA'H,;QPCPQP3P1P1P>AW7@VR@,H?,;QP7P@PDPACQ,;QFhCFCFCFCF1gQ>P6P<g00JoRQg00KOR>':1n6<=2Q>dAo759CdbEbHbIX77X87X97X:7%4<1?;:18<;1=:G/8J1=4GR4,8:1?4J'>[[[[^77^87^97^:7P6fU,1B#3%3LfV#0P8PGPFPKPOO8bDb6bGbFb6bLbKbA,pPE\A2ESUPEPSA2ES6X4E1:ESPHP6E\b0W0W2n10110000021010101P6P<O2b2b4b0WBW@WCW0W?P9P6O2n2001000000121000000W1W>P9P6O2n2001000000121000000W1P9P6O2n2001000000121000000W1W=P9P6O2n2001000000121000000W1W<P9P6O2n2001000000121000000W1XM=WOX;7WNo"). Qed.

Definition oband (A n : Z) : Prop := (0x6e8000 <= A /\ A + n <= 0x7fff7000) \/ (0x10007fff8000 <= A /\ A + n <= 2 ^ 47).

Section RG.
  Context {HCEIL : HeapCeil}.

  Lemma rg_b1 : forall (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (obj D N sph lo : Z),
    sph mod 32 = 0 -> 2 ^ 45 <= sph <= 2 ^ 47 ->
    wr_at asegs m obj 2504 -> SHAD m obj (repeat (b8 0) 313) -> obj mod 8 = 0 -> 0x6e8000 <= obj -> obj + 2504 <= 2 ^ 47 -> oband obj 2504 ->
    (obj + 2504 <= sph - RG_STACK \/ sph <= obj) ->
    1 <= N < 2 ^ 26 -> 0 < D -> D + N <= 2 ^ 47 ->
    stk asegs m lo sph -> aceil <= lo -> lo <= sph - RG_STACK -> mem_inv asegs m -> ACONST m ->
    exists R' M',
      CatSim.msteps asegs
        (MS (mkR ra (Z_to_bv 64 sph) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 obj) (Z_to_bv 64 D) (Z_to_bv 64 N) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 RG_CTOR) fc None m ro)
        (MS R' F (Z_to_bv 64 AFS_MALLOC_1) fc None M' ro)
      /\ R' = mkR (Z_to_bv 64 CS_SM_RET) (Z_to_bv 64 (sph - 2592)) gp tp (getr R' 5) (getr R' 6) (getr R' 7)
                 (Z_to_bv 64 (sph - 2528)) (Z_to_bv 64 (sph - 2592)) (Z_to_bv 64 96) (getr R' 11) (getr R' 12) (getr R' 13)
                 (getr R' 14) (getr R' 15) (getr R' 16) (getr R' 17) (Z_to_bv 64 N) (Z_to_bv 64 D) (Z_to_bv 64 0x7fff8000)
                 s5 s6 s7 s8 s9 s10 s11 (getr R' 28) (getr R' 29) (getr R' 30) (getr R' 31)
      /\ munch [(obj, obj + 2504); (sph - 2592, sph)] m M' /\ wmono asegs m M' /\ mem_inv asegs M' /\ stk asegs M' lo sph
      /\ rw_cells asegs M' obj rg_cells
      /\ rw_cells asegs M' (sph - 2576) [C8 s4; C8 s3; C8 s2; C8 s1; C8 (wz MT_FA); C8 (wz CS_RET_RA)]
      /\ rw_cells asegs M' (sph - 16) [C8 s0; C8 ra].
  Proof.
    intros until lo. intros SP32 SPR WF SH0 O8 OLO OHI OB OS HN HD0 HD1 ST AL LO MI AC.
    unfold RG_STACK, AFS_STACK in OS, LO. unfold oband in OB.
    assert (HQ : obj = 8 * (obj / 8)) by (pose proof (Z.div_mod obj 8 ltac:(lia)); lia).
    assert (HSH : sh obj = obj / 8 + LbB_Kit.SHBASE) by (symmetry; apply sh_kit; lia).
    pose proof (ACONST_shbase m AC) as [CG CS].
    pose proof (ACONST_uar m AC) as [CU CV].
    remember (mkR ra (Z_to_bv 64 sph) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 obj) (Z_to_bv 64 D) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    assert (S2 : getr R 2 = Z_to_bv 64 sph) by (rewrite HR0; reflexivity).
    assert (S10 : getr R 10 = Z_to_bv 64 obj) by (rewrite HR0; reflexivity).
    assert (S11 : getr R 11 = Z_to_bv 64 D) by (rewrite HR0; reflexivity).
    assert (S12 : getr R 12 = Z_to_bv 64 N) by (rewrite HR0; reflexivity).
    pose (E := Eseed R [Z_to_bv 64 (obj / 8); Z_to_bv 64 sph; Z_to_bv 64 D; Z_to_bv 64 N]).
    assert (E32 : bv_unsigned (edenot E (EVar 32)) = obj / 8) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (E33 : bv_unsigned (edenot E (EVar 33)) = sph) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (EOB : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = obj)
      by (evs; rewrite rg_zmul, <- HQ, u64_of_Z by lia; reflexivity).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EMd M_MUL (ELit 8) (EVar 32)); (2%bv, EVar 33); (11%bv, EVar 34); (12%bv, EVar 35)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X);
        first [rewrite S2 | rewrite S10 | rewrite S11 | rewrite S12]; evs; rewrite ?rg_zmul, <- ?HQ; reflexivity. }
    assert (HK : know_ok asegs E m
       [ KImg 0x10000 0x91000;
         KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL); KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
         KWord (SA (ELit 0) AGOT_UAR) 8 (ELit AUAR_CELL); KWord (SA (ELit 0) AUAR_CELL) 4 (ELit 1);
         KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) 0) (ELit 2504); KZero (SA (EVar 32) SHBASE) (ELit 313);
         KRange (EVar 32) 905216 (2 ^ 44);
         KDisj (SA (EVar 32) SHBASE) (ELit 313) (SA (EMd M_MUL (ELit 8) (EVar 32)) 0) (ELit 2504);
         KDisj (SA (EVar 32) SHBASE) (ELit 313) (SA (EVar 33) (-2592)) (ELit 2592);
         KWr (SA (EVar 33) (-2592)) (ELit 2592); KAlign (EVar 33) 32; KRange (EVar 33) (2 ^ 45) (2 ^ 47);
         KRange (EVar 34) 1 (2 ^ 47); KRange (EVar 35) 1 (2 ^ 26);
         KDisj (SA (EMd M_MUL (ELit 8) (EVar 32)) 0) (ELit 2504) (SA (EVar 33) (-2592)) (ELit 2592) ]).
    { unfold know_ok.
      apply Forall_cons; [apply kimg_of_mem_inv; [exact MI | lia | lia]|].
      apply Forall_cons; [eapply (kword_of_rw_cells asegs E m _ _ 0%nat _); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | reflexivity]|].
      apply Forall_cons; [eapply (kword_of_rw_cells asegs E m _ _ 0%nat _); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | reflexivity]|].
      apply Forall_cons; [eapply (kword_of_rw_cells asegs E m _ _ 0%nat _); [exact CU | reflexivity | reflexivity | lia | reflexivity | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | reflexivity]|].
      apply Forall_cons; [eapply (kword_of_rw_cells asegs E m _ _ 0%nat _); [exact CV | reflexivity | reflexivity | lia | reflexivity | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | reflexivity]|].
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; rewrite EOB; lia
          | unfold estart, elenZ; cbn [a_base a_off]; rewrite EOB; evs; rewrite u64_of_Z by lia; lia
          | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off]. rewrite E32.
        assert (EL : bv_unsigned (edenot E (ELit 313)) = 313) by (evs; rewrite u64_of_Z by lia; reflexivity).
        rewrite EL. split; [unfold LbB_Kit.SHBASE; lia|].
        intros i Hi.
        pose proof (SHAD_base m obj (repeat (b8 0) 313) (Z.to_nat i) SH0 ltac:(rewrite repeat_length; lia)
                      ltac:(rewrite <- sh_kit by lia; unfold AIMG_TOP, LbB_Kit.SHBASE; lia)) as Hm.
        rewrite nth_error_repeat in Hm by lia. rewrite Z2Nat.id in Hm by lia. rewrite HSH in Hm. exact Hm. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite E32; lia|].
      apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off]; rewrite ?E32, ?E33, ?EOB; evs;
                          rewrite ?u64_of_Z by lia; unfold LbB_Kit.SHBASE; lia|].
      apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off]; rewrite ?E32, ?E33, ?EOB; evs;
                          rewrite ?u64_of_Z by lia; unfold LbB_Kit.SHBASE; lia|].
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite E33; lia
          | unfold estart, elenZ; cbn [a_base a_off]; rewrite E33; evs; rewrite u64_of_Z by lia; lia
          | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite E33; split; [lia | exact SP32]|].
      apply Forall_cons; [cbn [kentry_ok]; rewrite E33; lia|].
      do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off]; rewrite ?E33, ?EOB; evs;
                          rewrite ?u64_of_Z by lia; lia|].
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R RG_CTOR m ro HR HK 7000%nat [AFS_MALLOC_1] (SCR [] [] []) 40%N.
    { apply Forall_nil. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (MU : munch [(obj, obj + 2504); (sph - 2592, sph)] m M1).
    { pose proof (munch_mem_denot_2b [(0, 2504)] [(-2592, 0)] (EMd M_MUL (ELit 8) (EVar 32)) (EVar 33) E m _ Hlf
                    ltac:(vm_cast_no_check (@eq_refl bool true))) as MU.
      rewrite EOB, E33 in MU. cbn [map fst snd app] in MU. subst M1. eapply munch_eqW; [exact MU | repeat f_equal; lia]. }
    assert (WM : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI' : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST' : stk asegs M1 lo sph) by (subst M1; apply stk_mem_denot; exact ST).
    assert (RC : rw_cells asegs M1 obj rg_cells).
    { unfold rg_cells. subst M1.
      apply (rw_cells_log_block E m _ (EMd M_MUL (ELit 8) (EVar 32)) rg_words 0 obj Hlf).
      - vm_cast_no_check (@eq_refl bool true).
      - rewrite EOB. lia.
      - replace (8 * Z.of_nat (length rg_words)) with 2504 by (vm_compute; reflexivity). exact WF.
      - eapply (other_disj_of_2b E _ (EMd M_MUL (ELit 8) (EVar 32)) (EVar 33) (-2592) 0 obj (8 * Z.of_nat (length rg_words)));
          [vm_cast_no_check (@eq_refl bool true)
          | rewrite E33; replace (8 * Z.of_nat (length rg_words)) with 2504 by (vm_compute; reflexivity); lia]. }
    assert (WSK : forall a, sph - 2592 <= a -> a + 8 <= sph -> wr_at asegs m a 8).
    { intros a Ha1 Ha2. pose proof (wr_at_of_stk asegs m lo sph ST) as W. destruct W as (W1 & W2 & W).
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (C0 : rw_cells asegs M1 (sph - 2576) [C8 s4]).
    { subst M1. eapply (rw_cells_log_nth_sb _ _ _ 0%nat); [exact Hlf | reflexivity | vm_cast_no_check (@eq_refl bool true)
        | rewrite E33; lia | apply WSK; lia | reflexivity | exact I | first [reflexivity | evs; rewrite HR0; reflexivity]]. }
    assert (C1 : rw_cells asegs M1 (sph - 2568) [C8 s3]).
    { subst M1. eapply (rw_cells_log_nth_sb _ _ _ 1%nat); [exact Hlf | reflexivity | vm_cast_no_check (@eq_refl bool true)
        | rewrite E33; lia | apply WSK; lia | reflexivity | exact I | first [reflexivity | evs; rewrite HR0; reflexivity]]. }
    assert (C2 : rw_cells asegs M1 (sph - 2560) [C8 s2]).
    { subst M1. eapply (rw_cells_log_nth_sb _ _ _ 2%nat); [exact Hlf | reflexivity | vm_cast_no_check (@eq_refl bool true)
        | rewrite E33; lia | apply WSK; lia | reflexivity | exact I | first [reflexivity | evs; rewrite HR0; reflexivity]]. }
    assert (C3 : rw_cells asegs M1 (sph - 2552) [C8 s1]).
    { subst M1. eapply (rw_cells_log_nth_sb _ _ _ 3%nat); [exact Hlf | reflexivity | vm_cast_no_check (@eq_refl bool true)
        | rewrite E33; lia | apply WSK; lia | reflexivity | exact I | first [reflexivity | evs; rewrite HR0; reflexivity]]. }
    assert (C4 : rw_cells asegs M1 (sph - 2544) [C8 (wz MT_FA)]).
    { subst M1. eapply (rw_cells_log_nth_sb _ _ _ 4%nat); [exact Hlf | reflexivity | vm_cast_no_check (@eq_refl bool true)
        | rewrite E33; lia | apply WSK; lia | reflexivity | exact I | first [reflexivity | evs; rewrite HR0; reflexivity]]. }
    assert (C5 : rw_cells asegs M1 (sph - 2536) [C8 (wz CS_RET_RA)]).
    { subst M1. eapply (rw_cells_log_nth_sb _ _ _ 5%nat); [exact Hlf | reflexivity | vm_cast_no_check (@eq_refl bool true)
        | rewrite E33; lia | apply WSK; lia | reflexivity | exact I | first [reflexivity | evs; rewrite HR0; reflexivity]]. }
    assert (D0 : rw_cells asegs M1 (sph - 16) [C8 s0]).
    { subst M1. eapply (rw_cells_log_nth_2b _ _ _ 320%nat (EVar 33) (EMd M_MUL (ELit 8) (EVar 32)) _ _ _ 0 2504);
        [exact Hlf | reflexivity | vm_cast_no_check (@eq_refl bool true) | rewrite E33; lia
        | rewrite EOB; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | apply WSK; lia | reflexivity | exact I
        | first [reflexivity | evs; rewrite HR0; reflexivity]]. }
    assert (D1 : rw_cells asegs M1 (sph - 8) [C8 ra]).
    { subst M1. eapply (rw_cells_log_nth_2b _ _ _ 321%nat (EVar 33) (EMd M_MUL (ELit 8) (EVar 32)) _ _ _ 0 2504);
        [exact Hlf | reflexivity | vm_cast_no_check (@eq_refl bool true) | rewrite E33; lia
        | rewrite EOB; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | apply WSK; lia | reflexivity | exact I
        | first [reflexivity | evs; rewrite HR0; reflexivity]]. }
    assert (CC : rw_cells asegs M1 (sph - 2576) [C8 s4; C8 s3; C8 s2; C8 s1; C8 (wz MT_FA); C8 (wz CS_RET_RA)]).
    { apply rw_cells_cons8_c; [exact C0|]. replace (sph - 2576 + 8) with (sph - 2568) by lia.
      apply rw_cells_cons8_c; [exact C1|]. replace (sph - 2568 + 8) with (sph - 2560) by lia.
      apply rw_cells_cons8_c; [exact C2|]. replace (sph - 2560 + 8) with (sph - 2552) by lia.
      apply rw_cells_cons8_c; [exact C3|]. replace (sph - 2552 + 8) with (sph - 2544) by lia.
      apply rw_cells_cons8_c; [exact C4|]. replace (sph - 2544 + 8) with (sph - 2536) by lia. exact C5. }
    assert (DD : rw_cells asegs M1 (sph - 16) [C8 s0; C8 ra]).
    { apply rw_cells_cons8_c; [exact D0|]. replace (sph - 16 + 8) with (sph - 8) by lia. exact D1. }
    exists R', M1. split; [exact Hms|].
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    rreg HR' 1%bv L1.
    rreg HR' 2%bv L2.
    rreg HR' 3%bv L3.
    rreg HR' 4%bv L4.
    rreg HR' 8%bv L8.
    rreg HR' 9%bv L9.
    rreg HR' 10%bv L10.
    rreg HR' 18%bv L18.
    rreg HR' 19%bv L19.
    rreg HR' 20%bv L20.
    rreg HR' 21%bv L21.
    rreg HR' 22%bv L22.
    rreg HR' 23%bv L23.
    rreg HR' 24%bv L24.
    rreg HR' 25%bv L25.
    rreg HR' 26%bv L26.
    rreg HR' 27%bv L27.
    split.
    { rewrite (rfull_eq R' HF1) at 1. f_equal.
      all: first [reflexivity | (rewrite L1 || rewrite L2 || rewrite L3 || rewrite L4 || rewrite L8 || rewrite L9 || rewrite L10 || rewrite L18 || rewrite L19 || rewrite L20 || rewrite L21 || rewrite L22 || rewrite L23 || rewrite L24 || rewrite L25 || rewrite L26 || rewrite L27); rewrite ?rg_zadd; rg_zeq HR0]. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split; [exact RC|]. split; [exact CC|]. exact DD.
  Qed.
End RG.

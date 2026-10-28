(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface RF_huf_bdt_model RF_huf_bdt_fast.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AF_huf_tbl_iface AF_huf_bdt_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkArith StrFun.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_bdt_gen () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3mulI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions8bv_swrapC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic3and01C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03C5ARocqVerifyHarness?AgentSubmission6Common:STRW_merge=swrap32_smallK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula09C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes6option00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9skip_loopC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp:table_stepC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission5Plain?RF_huf_bdt_fast?land_mask_rangeK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C45stdpp9bitvector;definitions;bv_unsignedI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6ltb_ltc5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_gen4HTCAC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula07C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subK47Corelib7Numbers7BinNums1Z03C57Corelib7BinNums6PosDef3Pos4landC56Stdlib6ZArith6BinInt1Z4of_NC57Corelib7BinNums6PosDef3Pos6pred_NC57Corelib7BinNums6NatDef1N5ldiffC57Corelib7BinNums6NatDef1N3lorC57Corelib7BinNums6NatDef1N8succ_posC47Corelib4Init5Logic7f_equalC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC56Stdlib6ZArith6BinInt1Z8add_commK46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init9Datatypes7nat_indK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01c5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_gen3PTAC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8sym_loopc5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_gen7gnA_invC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model4tsymC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit=shad_outside1C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit=zshadow_munchC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface7zshadowC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6ostoreC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model;bind_Ok_invI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model9ostore_OkC56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4chkZC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3sxbC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib3MemAsext_extract_byteC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit7acc_shZK47Corelib5Lists7ListDef6Forall02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model;tsym_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waK46Stdlib9micromega7EnvRing3Pol01C5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8oupd_natC47Corelib4Init5Peano2ltC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model:tsym_storeK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT?oupd_nat_lengthC56Stdlib6ZArith6BinInt1Z6eqb_eqK4ELinuxProcessSemantics5Riscv5Instr5instr03c5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_gen8sk_loopAC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_bdt_lp;shl32_shr30C5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06I4ELinuxProcessSemantics5Riscv3Sem4core00K46Stdlib9micromega=RingMicromega3Op201C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4sxb0C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8gen_loopC47Corelib4Init5Logic8iff_reflC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit4u16sC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula01C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit;u16s_lengthC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model7load_OkC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;Forall_ZnthC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem8u16_znthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx16C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le2C56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC47Corelib4Init9Datatypes4andbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge=bv_lts_zero_lC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z7mod_addc5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_gen8sy_loopAC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem:sx16_shortC56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Section Gen.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).
  Variables (x1 x8 x9 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word).
  Variables (m : amem) (NC TD : Z) (nc : list Z) (tl stp M1 hT : Z) (jt : list byte).
  Variable POST : machine_state -> Prop.
  Hypothesis HTL : 1 <= tl <= 12.
  Hypothesis HSTP : 0 < stp < 8192.
  Hypothesis HSTPV : stp = table_step (2^tl).
  Hypothesis HM1 : 1 <= M1 <= 256.
  Hypothesis HNCL : M1 <= zlen nc.
  Hypothesis HNCR : Forall (fun c => - 32768 <= c < 32768) nc.
  Hypothesis HT0 : 0 <= hT < 2^32.
  Hypothesis HT1 : hT < 2^tl \/ hT = 2^32 - 1.
  Hypothesis HJT : length jt = (4 * Z.to_nat (2^tl))%nat.
  Hypothesis BNC : ablk NC (NC + 2 * zlen nc).
  Hypothesis BTD : ablk TD (TD + 4 * 2^tl).
  Hypothesis DNT : NC + 2 * zlen nc <= TD \/ TD + 4 * 2^tl <= NC.
  Hypothesis NCB0 : bytes_at bsegs m NC (u16s (map (Z_to_bv 64) nc)).     (* [comment removed for export] *)
  Hypothesis ZN : zshadow m NC (2 * zlen nc).
  Hypothesis ZT : zshadow m TD (4 * 2^tl).
  Hypothesis RN : rng RNG NC (2 * zlen nc).
  Hypothesis RNS : rng RNG (shad NC) (nshad (2 * zlen nc + NC mod 8)).
  Hypothesis RT : rng RNG TD (4 * 2^tl).
  Hypothesis RTS : rng RNG (shad TD) (nshad (4 * 2^tl + TD mod 8)).

  Definition gnA_inv (m1 : amem) (syms : list (option Z)) : Prop :=
    u8arr bsegs m1 TD (tsym jt syms) /\ munch [(TD, TD + 4 * 2^tl)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1.

  Lemma HTCA : forall q, 0 <= q < 2^tl -> (bv_swrap 32 hT mod 18446744073709551616 < q <-> hT < q).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_gen ()) ["CANSEC1"; "Gen"] "h04__x1h12Hah24__p1h33H28h44HJT0h57__arithh64__ffh77__sat29h87__sat30h97__sat31h:7__sat32h;7__sat33h<7__sat34h=8__varmaph>5__with?4cstrh@5cstr0hA3z28hB4__p2hC4__x2hD4__x3hE1xhF1HhG3H10hH2H9hI3HT0hJ3HT1hK1zhL2H0hM2H1hN3H11hO2H2hP2H3hQ2H4hR2H5hS2H6hT2H7hU2H8hV2HLhW2HqhX3P12hY7__sat35hZ7__sat36h[2hTh\1oh]1qh^1yp%0p&0p;1p;2p;3p;<p;4p;5p;6p;7p;8p;Bp10000p4p7210g000\R0p4p710p8g001:j12Tg001_j17Tg002=j2MTg002Zj20Tg0036j26Tg003Qj14Tg0046j1TTg004Tj1mTg0057j2WTg005Wj1ITg0066R1j1jTg006Vk208Tg006mj3Dj1aTg007GR2j1KTg007gj2bTg008DR3j2JTg008aj2wTg009Dj3uTg009aj2HTg00:;l<qTg00:`j4oTg00;Gj1eTg00;lj2lTg00<Nj23Tg00<jR4j2FTg00=Dj2OTg00=lj3NTg00>Pj2VTg00?Aj2>Tg00?aj1kTg00@Aj1iTg00@aj1hTg00A?j1gTg00A]k107Tg00BHj2fTg00Bkk206Tg00CMk205Tg00D9k304Tg00DXk403Tg00EJj2PTg00Ehj2RTg00FKk100Tg00Fmj5~Tg00GTj2xTg00H1j2`Tg00HXj25Tg00I1j2_Tg00INj4vTg00Iij6^Tg00JEj5CTg00Jbj3ZTg00KEj3tTP0j6]j8{Tg00Khj2LTg00LQj3ETg00M:j2\Tg00Mfj3XTg00NFj4YTg00Ndj2pTg00Ohj3yTg00PKj7zTg00Pol<|Tg00QTlBnTg00R:j4cTg00Rej7dTg00SIk601Tg00Smk702Tg00TQj8UTg00U5R0f0R5'3p=1%25#2p=Gg00USR6f1R7;D5p=;P6g00V1R8P6P6P1f4R1P2f3R9g00VPf2R:P7P5M<|p=sP8P8P8P6P6P6g00W=P2P2P2P3g00W]f5R3P1P9P:P7P5MBnp=r1005p=<1f65p=?P:g00X@R;g00X_R<P<g00Y?R=P6P7g00Y_P5Ccg00ZFR>Fdp=8P7P;P<P<P=P5J01p=SP6P7g00ZfP5Ccp=@P7P;P<P<P=P5P>Fdp=AP:P;P<P<P=P7P5K02p=9P9P;P<P<P=P:P7P5GUp=Q%25#2#2#2p=}%25#2#2#2#2#2#2#2p==%45#4p=[f6R>P;P<P<P=P3P1P9P;P<P<P=P:P7P5GUGUp=B%45#4#4#4#4#4#4#4p=:%15R?g00[MR@#2RA#7RBp,2tlRC'MRD,05'6PBPC%4@RE#G#7RF%2ARG#2RH#T#mp,2jt'WRIg00\2S00#IS01#I#IS02#IRJ%jDRK+08RL5D8%KIRM%7GRG1b0DRN'J';ROP8P6%a8P2%a6%K7%K5';AD8751w753uX^8XE8PIPM1H6MPL1b05XE6RLPDO1R8,JGPJPG1H6GPKP8P5XE6PLPDPD1H6DDsErM<qp,3HJTCoRLPOp,2nc,W6R8#eRK%K8R8#1R2%eIRI%1MRM1l0DRP%<DRQ1;ND'613D0AD6N0'6'FRRPNP6%GHRS#7RT,OBRU%<BRV%1T1MBTRW#<[[RX%1BRYg00\QRZANBT7UW1RT%1W\Z^1YR[p,2NCR\%7HRH'VR]%1\%1HR^1>\H#1[[R_p,2TDR`/VHRa%1`1>`H#1\^[R^1OBCRH%1CPQ[\VRQANBC7VZX1YRb%1D\Z^1YRcg00\mRd#kRe%idRf%h6S03%g6Rg&076Rh1f60Ri%?BRj38S04206h=RkP5P:g00]YRlg00^9Rm'H2055:=DlmdB04607H03R0b6b=b>PVP5b5b7b8b9b:b;b<bAb3b@b?b4PLPOPKP2PIPMPPPRPNP6PUPXPTP[P]P_PaP^PHPQPbPcp-0RmPePf1P67S05PgPh1Sh91R6@Rl%?F'@,AhRn59h&00<RoPnCQPkP0b6b=b>X06W2135F,67137F[^06^2mP5%7@R@/3CRnPCp,3HTLRpO3b5b7b8b9b:b;b<bAb3b@b?b4D~%2S#GRq#}Rr#7Rs,3Dp,3HT1S06p,2hTRt/0DRu1xW@Rv,;tRw'FP4PuPw%TSRS/`tS07%2rRr#2#G#=#=#=#=#=#=#7R4'>/0110t1'5P5P6Pt1>54/0>10t>Rx'5XK6P6Pt105>/5xXK6Pn13CFRF10t3Rx/5xp,3stpRx#<Ry%7r,0xRxf7Rr,0tRz/5zp,2M1Rz,3@R{%7q,3zRzf9,0tRq/5q%1tRq10tWR|f;,0tR}/5}f=R}#1R~10}D10t}R}/5}f>S08/0DPuPwf?,0tR}/5}1JB8,_\/3`R81JGD,_`/3\R\f@,0tR`/5`fAR`,0tRGfBS09,0t[R}P}P5XNGRGPGCvRGXG8PGXG\p,3DNTE^R\XHuP\XHwQ06E^WUXT~f<DCXS|XRqp,3HT0RqDCXQzXP{p,3HM1DCXOxXMyp,4HSTPDCXLFXFnPpDC1>t4PLPOPKP2PIPMPPPRPNP6PUPXPTP[P]P_PaP^PHPQPbPcPePfQ05PgPh1@il,AhRnAZ6jSRy98hl59hPo%?498hl99hnCQPkP0b6b=b>X06105W,6?R?%171074'6[^06P5PtPqO2b5b7b8b9b:b;b<bAb3b@b?b49tt4E]Q07PLPOPKP2PIPMPPPRPNP6PUPXPTP[P]P_%4ERE#[Rx#7R{,OB%1{1MB{Rz#<[\VANB{7VZX1Y%1z\Z^1YPaP^PHPQPbPc1L6JRJQ02,L6RYQ00,L65E65E6g00^YRZ'\=XdePfP61P6:P7P6Q03P91P69CYCYR{PgPhPhQ04PoPh1R6ARA,@i,AhPo1R6ERE98hiFBRiPoPhA8hlERBPoPh%?s,@E,AhREPoPh1Sh3R~99hnPoPh%?@R\/@A,Ah1Sh>59hRAPo%Tx9Z6j98hl99hnCQFBFBPkP0b6b=b>X06XC6XD6X2mXBm%1:%<1[\VRV1079131s%19/6>13@3f8R>'6%13103z'6[[[[[^06^C6^D6^2m^BmP5PFP|PDPCPtP:Q08P`PqPpO:b5b7b8b9b:b;b<bYbZbAb3b@b?b4,ptE]XVuP5O1P6Pv107D1;7v'F1`S:/>4/0>10:>'5]J^I?X[6%1v10vW'610vD1;vv'FPLPOPKP2PIPMPPPRPNP6PUPXPTP[P]P_PaP^PHPQPbPcQ01,L69E6Y9E6J/\Z=XdePfP{PgPhPiPoPhPEPoPhA9h~BPoPhPAPoPhP;P<P<P=%4x#[#:#:#:#:#:#:#:#7Rx#?=8hlAy6y\=8hlFzFBFBPkP0b6b=b>X06XC6XD6X2mXBm139s10:1,6313@1/6r10x110v1'5[[[\V^06^C6^D6^2m^BmP5PFfCRF#1PDPCPFP:P`Q09PpO9b5b7b8b9b:b;b<bAb3b@b?b4WJWIPtP5PqQ06G{XFwP5O1n200100000021100011000b\bXWWX]6o"). Qed.

  Lemma PTA : 2 <= 2^tl <= 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_gen ()) ["CANSEC1"; "Gen"] "h02Hah13H28h24HJT0h37__arithh44__ffh54__p1h67__sat29h77__sat30h87__sat31h97__sat32h:7__sat33h;7__sat34h<8__varmaph=5__with>4__x1h?4cstrh@5cstr0hA3z28hB1xhC7__sat35hD7__sat36hE1yp;1p;2p;3p;<p;4p;6p;5p;Bp;7p;8g001:j14Tg001_j13Tg002=j2@Tg00<Nj21Tg0046j1ETg004Tj1ZTg0057j2DTg005Wj18Tg0066R0j1STg006Vj2OTg006mj32j1HTg007GR1j1;Tg007gj2KTg008DR2j2ITg008aj2^Tg009Dj3\Tg009aj29Tg00:;l<WTg00:`j4VTg00;Gj1CTg00;lj2UTg002Zj2<Tg0036j26Tg00<jj2RTg00=Dj2?Tg00=lj3>Tg00>Pj2BTg00?Aj2ATg00?aj1NTg00@Aj1MTg00@aj1PTg00A?j1QTg00A]j1LTg00BHj2:Tg00Jbj3TTg00R:j4=Tg00Bkj2kTg00CMj2jTg00D9j3iTg00DXj4hTg00EJj2cTg00Ehj2bTg00SIj6`Tg00FKj1]Tg003Qj1_Tg00Fmj5FTg00INj4aTg00Pol<[Tg00QTlBdTg00Rej7eTg00Smj7fTg00TQj8gTf0R3#4#4p=5g00USR4g00V1R5P4P4P0f4R0P1f3R6g00VPf2R7f1R8P3M<[p=YP5P5P5P4P4P4g00W=P1P1P1P2g00W]f5P0P6P7P8P3MBdp=Xg00U5R0/13p=0P8g00X@R2g00X_R9P9g00Y?R:P3g00ZFFep=7P7P2P9P9P:P8P3Ffp=JP6P2P9P9P:P7P8P3Ggp=Gg00[MR;#4R<#3R=p,2tlR>,@=R?'1%4<R<#4R@#5RA#4#5#5#5#3,1?%3;RB,@=RCPBP>%E@#Zp,2jt'DRDg00\2#8#8#8#8RE%S?RF'ORG525%;DRH%3<R<1K0?RI'I524RJP5P4%H5P1%H4%;8%;3524A25831^833\XE5XB5PDPH194HPG1K03XB4RGP?O1R5,I<PEP<194<PFP5P3XB4PGP?P?194?DYEXM<Wp,3HJTCVRGPJp,2nc,D4R5#CRF%;5#0R5%CDRD%0HRH1U0?R<1<0?REA24I?'611?0A24I0'6'RR1PIP4%3ARA,?=RK1<0=RL%0A1@=ARM,<0[[RN%0=ROg00\QRPA>=A8UW0RA%0M\P^0ORMp,2NCRQ%3@R@'BRR%0Q%0@RS1AQ@#0[[RQ1?=B%0B1<0CRT[\LA>=B8VPX0O%0C\P^0Op,2TDRC/B@RU%0C1AC@#0\S[RS1?=>RC%0>PE[\LREA>=>8VPX0OR@%0?\P^0OROg00\mRP#NR?%MPRP%P4RV%Q4RW%L4RXP41:40RYg00Y_RZ1:4=R[%E;5T4C='71kX:R\P3P7g00]YR]g00^9R^'91j37=2]^dAi408ChR0b4b<b=PTP3b3b6b7b8b9b:b;bCbDbAb1b@b?b2PGPJPFP5PDPHP<P1PIP4PKPNPAPMPRPQPUPSPCPEP@POp-0RTP?PP1c48R^PWPXP41:4Bg00ZfR]1b4;R7C=,7XR_PXP2P9P9P:P6E`R65JX%]9R9P_CGP\P0b4b<b=X>4W511B3/6811B8[^>4^5TP3%_;#5#3R;,1>P>p,3HTLR_O3b3b6b7b8b9b:b;bAb1b@b?b2DFP=P>P;PGPJPFP5PDPHP<P1PIP4PKPNPAPMPRPQPUPSPCPEP@POP?PPPVPWP4PYPZP[C=,7XP\P0b4b<b=PLP3b3b6b7b8b9b:b;bAb1b@b?b2PGPJPFP5PDPHP<P1PIP4PKPNPAPMPRPQPUPSPCPEP@POP?PPP^PWPXP4P7P]1:4;C=,7XR]9JX6P9P]CGP\P0b4b<b=X>4X5T113;,68118;[^>4^5TP311B>P>P_O3b3b6b7b8b9b:b;bAb1b@b?b2DFCao"). Qed.

  Variables (SP : Z) (x6 x18 x31 : word).
  Hypothesis FRN : rw_cells bsegs m (SP + 72) [C8 (Z_to_bv 64 NC)].
  Hypothesis RSP : rng RNG (SP + 72) 8.
  Hypothesis DSP : TD + 4 * 2^tl <= SP + 72 \/ SP + 80 <= TD.

  Notation STG pc mm x5 x8 x9 x10 x12 x13 x14 x15 x30 :=
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 (Z_to_bv 64 ASHOFF) x8 x9 x10 (Z_to_bv 64 (- NC - 1)) x12 x13 x14 x15
             (Z_to_bv 64 (bv_swrap 32 hT)) (Z_to_bv 64 TD) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
             (Z_to_bv 64 (- TD - 1)) (Z_to_bv 64 (2^tl - 1)) x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Local Ltac acc_hint ::= wk_acc_hint.
  Lemma g_sw : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
  Proof.
    intros z Hz. assert (HM : bv_half_modulus 32 = 2^31) by reflexivity. assert (MM : bv_modulus 32 = 2^32) by reflexivity.
    unfold bv_swrap, bv_wrap. rewrite HM, MM. rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma g_mask : forall x, 0 <= Z.land x (2^tl - 1) < 2^tl.
  Proof.
    intros x. replace (2^tl - 1) with (Z.ones tl) by (rewrite Z.ones_equiv; lia). rewrite Z.land_ones by lia.
    apply Z.mod_pos_bound. pose proof PTA. lia.
  Qed.
  Lemma g_ht : forall q, 0 <= q < 2^tl -> (bv_unsigned (Z_to_bv 64 (bv_swrap 32 hT)) <? q) = (hT <? q).
  Proof.
    intros q Hq. pose proof PTA as PT. rewrite unsigned_lit_wrap. destruct HT1 as [H|H].
    - rewrite g_sw by lia. rewrite Z.mod_small by lia. reflexivity.
    - rewrite H. replace (bv_swrap 32 (2^32 - 1) mod 2^64) with (2^64 - 1) by reflexivity.
      rewrite (proj2 (Z.ltb_ge (2^64 - 1) q)) by lia. rewrite (proj2 (Z.ltb_ge (2^32 - 1) q)) by lia. reflexivity.
  Qed.
  Lemma g_ltneg : forall A x, 0 <= A -> 0 <= x -> A + x < 2^64 -> bv_ltu (Z_to_bv 64 (- A - 1)) (Z_to_bv 64 x) = false.
  Proof.
    intros A x HA Hx HAx. rewrite bv_ltu_Z, !unsigned_lit_wrap. rewrite (Z.mod_small x) by lia.
    rewrite <- (Z.mod_add (- A - 1) 1 (2^64)) by lia. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
  Qed.
  Lemma g_st : forall m1 syms p s, gnA_inv m1 syms -> 0 <= p < 2^tl -> 0 <= s < 256 -> length syms = Z.to_nat (2^tl) ->
    store_ok bsegs m1 (wa (TD + (4 * p + 2))) 1 = true /\
    gnA_inv (write_to_mem m1 (wa (TD + (4 * p + 2))) (le1 (Z_to_bv 64 s))) (oupd_nat (Z.to_nat p) s syms).
  Proof.
    intros m1 syms p s (U & MU & WM & MI) HP HS HL. pose proof PTA as PT.
    pose proof (ablk_lin _ _ BTD) as (Ta & Tb & Tc & Td).
    assert (LT : Z.of_nat (length (tsym jt syms)) = 4 * 2^tl) by (rewrite tsym_length, HJT; lia).
    assert (SOK : store_ok bsegs m1 (wa (TD + (4 * p + 2))) 1 = true)
      by (apply (u8arr_store_ok bsegs m1 TD (tsym jt syms) (4 * p + 2)); [exact U | lia | reflexivity]).
    split; [exact SOK|].
    rewrite le1_byte, (unsigned_lit s) by lia. rewrite (Z.mod_small s 256) by lia.
    unfold gnA_inv. split; [| split; [| split]].
    - rewrite <- tsym_store by (rewrite ?HJT, ?HL; lia).
      replace (4 * Z.to_nat p + 2)%nat with (Z.to_nat (4 * p + 2)) by lia.
      apply u8arr_write; [exact U | lia].
    - apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
    - apply wmono_write; exact WM.
    - apply mem_inv_store; [exact MI | exact SOK].
  Qed.
  Lemma g_lts0 : forall n, -2^15 <= n < 2^15 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 n) = (0 <? n).
  Proof.
    intros n Hn. rewrite bv_lts_zero_l, unsigned_lit_wrap. destruct (Z_lt_le_dec n 0) as [NEG|POS].
    - rewrite <- (Z.mod_add n 1 (2^64)) by lia. rewrite Z.mod_small by lia.
      rewrite (proj2 (Z.ltb_ge (n + 1 * 2^64) (2^63))) by lia. rewrite andb_false_r. symmetry. apply Z.ltb_ge. lia.
    - rewrite Z.mod_small by lia. rewrite (proj2 (Z.ltb_lt n (2^63))) by lia. rewrite andb_true_r. reflexivity.
  Qed.
  Lemma g_bf : forall (f g : Z -> Z) (L : list Z) s, forallb (fun t => Z.eqb (f t) (g t)) L = true -> In s L -> f s = g s.
  Proof. intros f g L s B IN. rewrite forallb_forall in B. apply Z.eqb_eq. exact (B s IN). Qed.
  Local Ltac bf_eq s n :=
    lazymatch goal with |- ?l = ?r =>
      let f := eval pattern s in l in let g := eval pattern s in r in
      lazymatch f with ?F s => lazymatch g with ?G s =>
        apply (g_bf F G (map Z.of_nat (seq 0 n)) s);
        [vm_compute; reflexivity| apply in_map_iff; exists (Z.to_nat s); split; [lia| apply in_seq; lia]]
      end end
    end.
  (* [comment removed for export] *)
  Lemma sk_loopA : forall f p p1 mm (x5 x8 x10 x12 x13 x14 x30 : word),
    skip_loop tl f (Z.land (p + stp) (2^tl - 1)) hT = Ok p1 -> 0 <= p < 2^tl ->
    (0 <= p1 < 2^tl -> (hT < p1 -> False) ->
       evtF bsegs RNG POST (STG 0x97dd4 mm x5 x8 (Z_to_bv 64 stp) x10 x12 x13 x14 (Z_to_bv 64 p1) x30)) ->
    evtF bsegs RNG POST (STG 0x97dc8 mm x5 x8 (Z_to_bv 64 stp) x10 x12 x13 x14 (Z_to_bv 64 p) x30).
  Proof.
    intros f. induction f as [|f IH]; intros p p1 mm q5 q8 q10 q12 q13 q14 q30 HS HP K; [discriminate HS|].
    pose proof PTA as PT.
    pose proof (g_mask (p + stp)) as QR.
    set (q := Z.land (p + stp) (2^tl - 1)) in *.
    unfold ASHOFF.
    zstep. zstep.
    rewrite (g_sw (stp + p)) by lia. rewrite (Z.mod_small (stp + p)) by lia.
    replace (Z.land (stp + p) (2^tl - 1)) with q by (unfold q; f_equal; lia).
    zstep.
    cbn [skip_loop] in HS. rewrite <- HSTPV in HS.
    rewrite bv_ltu_Z, (unsigned_lit q) by lia. rewrite (g_ht q QR).
    destruct (Z.ltb_spec hT q) as [LT|GE]; cbv iota in HS |- *.
    - apply (IH q p1 mm q5 q8 q10 q12 q13 q14 q30 HS QR K).
    - injection HS as <-. apply K; [exact QR | lia].
  Qed.
  (* [comment removed for export] *)
  Lemma sy_loopA : forall f s n i syms position r m1 (x5 x8 x12 x14 : word),
    sym_loop tl f i n s syms position hT = Ok r ->
    0 <= i < n -> n < 2^31 -> 0 <= s < 256 -> 0 <= position < 2^tl -> length syms = Z.to_nat (2^tl) ->
    gnA_inv m1 syms ->
    (forall m2 syms' p' (y5 y12 y14 : word), r = (syms', p') -> 0 <= p' < 2^tl -> length syms' = Z.to_nat (2^tl) ->
       gnA_inv m2 syms' ->
       evtF bsegs RNG POST (STG 0x97ddc m2 y5 x8 (Z_to_bv 64 stp) (Z_to_bv 64 n) y12 (Z_to_bv 64 n) y14 (Z_to_bv 64 p') (Z_to_bv 64 s))) ->
    evtF bsegs RNG POST (STG 0x97da4 m1 x5 x8 (Z_to_bv 64 stp) (Z_to_bv 64 n) x12 (Z_to_bv 64 i) x14 (Z_to_bv 64 position) (Z_to_bv 64 s)).
  Proof.
    intros f. induction f as [|f IH]; intros s n i syms position r m1 q5 q8 q12 q14 HS HI HN HSR HP HL INV K; [discriminate HS|].
    pose proof PTA as PT. pose proof INV as INV0. destruct INV as (U & MU & WM & MI).
    pose proof (ablk_lin _ _ BTD) as (Ta & Tb & Tc & Td).
    pose proof (zshadow_munch _ m m1 TD (4 * 2^tl) ZT MU (shad_outside1 TD (4 * 2^tl) TD (4 * 2^tl) BTD ltac:(lia) ltac:(lia))
      ltac:(lia) ltac:(lia)) as ZT1.
    unfold ASHOFF.
    zstep.
    zstep. rewrite (g_ltneg TD) by (rewrite ?Z.shiftl_mul_pow2 by lia; lia). cbv iota.
    (wk_go [0x97dc4; 0x97dc8]).
    destruct (g_st m1 syms position s INV0 HP HSR HL) as (SOK & INV2).
    replace (wa (TD + (4 * position + 2))) with (Z_to_bv 64 (TD + Z.shiftl position 2 + 2)) in SOK, INV2
      by (unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. clear SOK.
    cbn [sym_loop] in HS. rewrite (proj2 (Z.ltb_lt i n)) in HS by lia.
    assert (OS : ostore syms position s = Ok (oupd_nat (Z.to_nat position) s syms))
      by (apply ostore_ok; first [rewrite FseLemmas.Zlength_correct; lia | unfold FseNCount.Zlength; lia | rewrite Zlength_correct; lia]).
    rewrite OS in HS. cbn [bind] in HS.
    destruct (skip_loop tl (S (Z.to_nat (2 ^ tl))) (Z.land (position + table_step (2 ^ tl)) (2 ^ tl - 1)) hT) as [p1| | | ] eqn:SK;
      cbn [bind] in HS; try discriminate HS.
    rewrite <- HSTPV in SK.
    eapply (sk_loopA _ position p1 _ _ _ _ _ _ _ _ SK HP).
    intros P1R P1H.
    zstep. rewrite (g_sw (i + 1)) by lia.
    pose proof (oupd_nat_length (Z.to_nat position) s syms) as HL2.
    destruct (Z.eq_dec (i + 1) n) as [EQ|NE].
    - destruct f as [|f]; [discriminate HS|].
      cbn [sym_loop] in HS. rewrite (proj2 (Z.ltb_ge (i + 1) n)) in HS by lia. injection HS as <-.
      zstep. wk_if_false.
      rewrite EQ. apply (K _ _ _ _ _ _ eq_refl P1R ltac:(rewrite HL2; exact HL) INV2).
    - zstep. wk_if_true.
      eapply (IH s n (i + 1) _ p1 r _ _ q8 _ _ HS); [lia | lia | lia | exact P1R | rewrite HL2; exact HL | exact INV2 | exact K].
  Qed.
  (* [comment removed for export] *)
  Lemma gn_loopA : forall f s syms position r m1 (x5 x10 x12 x13 x14 : word),
    gen_loop nc tl f s syms position hT = Ok r ->
    Z.of_nat f = M1 - s -> 0 <= s < M1 -> 0 <= position < 2^tl -> length syms = Z.to_nat (2^tl) ->
    gnA_inv m1 syms ->
    (forall m2 syms' p' (y5 y10 y12 y13 y14 : word), r = (syms', p') -> 0 <= p' < 2^tl -> length syms' = Z.to_nat (2^tl) ->
       gnA_inv m2 syms' ->
       evtF bsegs RNG POST (STG 0x97efc m2 y5 (Z_to_bv 64 M1) (Z_to_bv 64 stp) y10 y12 y13 y14 (Z_to_bv 64 p') (Z_to_bv 64 M1))) ->
    evtF bsegs RNG POST (STG 0x97d6c m1 x5 (Z_to_bv 64 M1) (Z_to_bv 64 stp) x10 x12 x13 x14 (Z_to_bv 64 position) (Z_to_bv 64 s)).
  Proof.
    intros f. induction f as [|f IH]; intros s syms position r m1 q5 q10 q12 q13 q14 HG HF HS HP HL INV K; [lia|].
    pose proof PTA as PT. pose proof INV as INV0. destruct INV as (U & MU & WM & MI).
    pose proof (ablk_lin _ _ BTD) as (Ta & Tb & Tc & Td). pose proof (ablk_lin _ _ BNC) as (Na & Nb & Nc & Nd).
    pose proof (zshadow_munch _ m m1 TD (4 * 2^tl) ZT MU (shad_outside1 TD (4 * 2^tl) TD (4 * 2^tl) BTD ltac:(lia) ltac:(lia))
      ltac:(lia) ltac:(lia)) as ZT1.
    pose proof (zshadow_munch _ m m1 NC (2 * zlen nc) ZN MU (shad_outside1 NC (2 * zlen nc) TD (4 * 2^tl) BTD ltac:(lia) ltac:(lia))
      ltac:(lia) ltac:(lia)) as ZN1.
    assert (NCB1 : bytes_at bsegs m1 NC (u16s (map (Z_to_bv 64) nc)))
      by (apply (bytes_at_transport bsegs _ m m1 NC _ NCB0 MU); cbn [disjoint_from]; rewrite u16s_length, length_map; lia).
    assert (FRN1 : rw_cells bsegs m1 (SP + 72) [C8 (Z_to_bv 64 NC)])
      by (apply (rw_cells_transport bsegs _ m m1 (SP + 72) _ FRN MU WM); cbn [disjoint_from]; cbn; lia).
    assert (TAIL : forall mm syms1 p1 (y5 y10 y12 y13 y14 : word), gen_loop nc tl f (s + 1) syms1 p1 hT = Ok r ->
      0 <= p1 < 2^tl -> length syms1 = Z.to_nat (2^tl) -> gnA_inv mm syms1 ->
      evtF bsegs RNG POST (STG 0x97d64 mm y5 (Z_to_bv 64 M1) (Z_to_bv 64 stp) y10 y12 y13 y14 (Z_to_bv 64 p1) (Z_to_bv 64 s))).
    { intros mm syms1 p1 y5 y10 y12 y13 y14 HG1 HP1 HL1 INV1. unfold ASHOFF.
      zstep. rewrite (g_sw (s + 1)) by lia.
      zstep.
      destruct (Z.eq_dec (s + 1) M1) as [EQ|NE].
      - wk_if_true. destruct f as [|f]; [|lia]. cbn [gen_loop] in HG1. injection HG1 as <-.
        rewrite EQ. exact (K mm syms1 p1 _ _ _ _ _ eq_refl HP1 HL1 INV1).
      - wk_if_false. exact (IH (s + 1) syms1 p1 r mm _ _ _ _ _ HG1 ltac:(lia) ltac:(lia) HP1 HL1 INV1 K). }
    cbn [gen_loop] in HG.
    assert (LD : load nc s = Ok (Znth s nc))
      by (unfold load; replace ((0 <=? s) && (s <? FseNCount.Zlength nc)) with true; [reflexivity|];
          symmetry; apply andb_true_iff; split; [apply Z.leb_le; lia | apply Z.ltb_lt; unfold FseNCount.Zlength; lia]).
    rewrite LD in HG. cbn [bind] in HG.
    destruct (sym_loop tl (S (Z.to_nat (Znth s nc))) 0 (Znth s nc) s syms position hT) as [[syms1 p1]| | |] eqn:SY;
      cbn [bind] in HG; try discriminate HG.
    unfold ASHOFF.
    zstep. zstep.
    lazymatch goal with |- context [Z_to_bv 64 ((Z.shiftl s 32 mod ?M) ≫ 31)] =>
      replace ((Z.shiftl s 32 mod M) ≫ 31) with (2 * s) by (symmetry; bf_eq s 257%nat) end.
    zstep. rewrite (g_ltneg NC (2 * s)) by lia. cbv iota.
    (wk_go [0x97d98]).
    rewrite (Z.mod_small s) by lia.
    assert (NL : 0 <= s < Z.of_nat (length nc)) by lia.
    pose proof (u16_znth bsegs m1 NC nc s (Z_to_bv 64 (NC + Z.shiftl s 1)) NCB1 NL
      ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RDN.
    zstep. clear RDN.
    pose proof (Forall_Znth _ nc s HNCR ltac:(lia)) as NR. cbv beta in NR.
    rewrite sx16_short by lia.
    zstep. rewrite g_lts0 by lia.
    destruct (Z.ltb_spec 0 (Znth s nc)) as [NP|NN]; cbn [negb]; cbv iota.
    - zstep.
      eapply (sy_loopA _ s (Znth s nc) 0 syms position (syms1, p1) m1 _ _ _ _ SY); [lia | lia | lia | exact HP | exact HL | exact INV0 |].
      intros m2 syms' p' y5 y12 y14 EQ HP' HL' INV'. injection EQ as <- <-.
      zstep.
      exact (TAIL m2 syms1 p1 _ _ _ _ _ HG HP' HL' INV').
    - cbn [sym_loop] in SY. rewrite (proj2 (Z.ltb_ge 0 (Znth s nc))) in SY by lia. injection SY as <- <-.
      exact (TAIL m1 syms position _ _ _ _ _ HG HP HL INV0).
  Qed.
  Lemma gn_entryA : forall syms r m1 (x8 x10 x12 x14 x15 x30 : word),
    gen_loop nc tl (Z.to_nat M1) 0 syms 0 hT = Ok r -> length syms = Z.to_nat (2^tl) -> gnA_inv m1 syms ->
    (forall m2 syms' p' (y5 y10 y12 y13 y14 : word), r = (syms', p') -> 0 <= p' < 2^tl -> length syms' = Z.to_nat (2^tl) ->
       gnA_inv m2 syms' ->
       evtF bsegs RNG POST (STG 0x97efc m2 y5 (Z_to_bv 64 M1) (Z_to_bv 64 stp) y10 y12 y13 y14 (Z_to_bv 64 p') (Z_to_bv 64 M1))) ->
    evtF bsegs RNG POST (STG 0x97d48 m1 (Z_to_bv 64 (2^tl / 8)) x8 (Z_to_bv 64 M1) x10 x12 (Z_to_bv 64 (2^tl / 2)) x14 x15 x30).
  Proof.
    intros syms r m1 q8 q10 q12 q14 q15 q30 HG HL INV K. pose proof PTA as PT. unfold ASHOFF.
    zstep. zstep. zstep. zstep.
    zstep. zstep. zstep.
    rewrite (proj2 (Z.ltb_ge M1 1)) by lia. cbn [Z.b2z]. rewrite Z.add_0_r, (g_sw M1) by lia.
    replace (2 ^ tl / 8 + 2 ^ tl / 2 + 3) with stp
      by (rewrite HSTPV; unfold table_step; rewrite !Z.shiftr_div_pow2 by lia; change (2^1) with 2; change (2^3) with 8; lia).
    exact (gn_loopA (Z.to_nat M1) 0 syms 0 r m1 _ _ _ _ _ HG ltac:(lia) ltac:(lia) ltac:(lia) HL INV K).
  Qed.
  Lemma gn_doneA : forall mm (x5 x8 x9 x10 x12 x13 x14 x30 : word),
    evtF bsegs RNG POST (STG 0x97f08 mm x5 x8 x9 x10 x12 x13 x14 (Z_to_bv 64 0) x30) ->
    evtF bsegs RNG POST (STG 0x97efc mm x5 x8 x9 x10 x12 x13 x14 (Z_to_bv 64 0) x30).
  Proof.
    intros mm q5 q8 q9 q10 q12 q13 q14 q30 K. unfold ASHOFF.
    zstep. exact K.
  Qed.
End Gen.
End CANSEC1.

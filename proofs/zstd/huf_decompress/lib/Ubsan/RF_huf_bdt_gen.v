(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_bdt_model
  RF_huf_bdt_lp RF_huf_bdt_fast.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_bdt_gen () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3mulI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z6moduloC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic3and01C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula09C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes6option00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9skip_loopC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp:table_stepC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_bdt_fast?land_mask_rangeC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedK4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6ltb_ltc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_bdt_gen3HTCC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula07C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC57Corelib7BinNums6PosDef3Pos4landC56Stdlib6ZArith6BinInt1Z4of_NC57Corelib7BinNums6PosDef3Pos6pred_NC57Corelib7BinNums6NatDef1N5ldiffC57Corelib7BinNums6NatDef1N3lorC57Corelib7BinNums6NatDef1N8succ_posC47Corelib4Init5Logic7f_equalC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC56Stdlib6ZArith6BinInt1Z8add_commC47Corelib4Init9Datatypes7nat_indK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01c5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_bdt_gen2PTK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8sym_loopc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_bdt_gen6gn_invC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model4tsymC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6ostoreC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model;bind_Ok_invI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model9ostore_OkC56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model;tsym_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8oupd_natC47Corelib4Init5Peano2ltC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model:tsym_storeK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT?oupd_nat_lengthC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqK4ELinuxProcessSemantics5Riscv5Instr5instr03c5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_bdt_gen7sk_loopC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_bdt_lp;shl32_shr30C5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega3Op201C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize01I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8gen_loopC47Corelib4Init5Logic8iff_reflC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit4u16sC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula01C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit;u16s_lengthC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model7load_OkC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;Forall_ZnthK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem8u16_znthC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx16C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le2C56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC47Corelib4Init9Datatypes4andbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge=bv_lts_zero_lC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z7mod_addc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_bdt_gen7sy_loopC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem:sx16_shortC56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_lit".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Gen.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x8 x9 x10 x12 x13 x14 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word).
  Variables (m : fmem) (NC TD : Z) (nc : list Z) (tl stp M1 hT : Z) (jt : list byte).
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
  Hypothesis HNC : 0 < NC /\ NC + 2 * zlen nc <= 2^64.
  Hypothesis HTD : 0 < TD /\ TD + 4 * 2^tl <= 2^64.
  Hypothesis DNT : NC + 2 * zlen nc <= TD \/ TD + 4 * 2^tl <= NC.
  Hypothesis NCB0 : bytes_at usegs m NC (u16s (map (Z_to_bv 64) nc)).     (* [comment removed for export] *)

  Definition gn_inv (m1 : fmem) (syms : list (option Z)) : Prop :=
    u8arr usegs m1 TD (tsym jt syms) /\ munch [(TD, TD + 4 * 2^tl)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  Notation ST pc mm x7 x17 x29 x30 x31 :=
    (MS (mkR ra sp gp tp (Z_to_bv 64 M1) (Z_to_bv 64 (bv_swrap 32 hT)) x7 x8 x9 x10 (Z_to_bv 64 NC) x12 x13 x14
             (Z_to_bv 64 TD) (Z_to_bv 64 (2^tl - 1)) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 stp)
             x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Notation STC pc mm x7 x8 x9 x10 x12 x13 :=
    (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.lxor TD (2^64 - 1))) (Z_to_bv 64 (2^tl - 1)) x7 x8 x9 x10 (Z_to_bv 64 NC) x12 x13 x14
             (Z_to_bv 64 (2^tl)) x16 (Z_to_bv 64 TD) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (Z.lxor NC (2^64 - 1)))
             (Z_to_bv 64 M1) (Z_to_bv 64 (bv_swrap 32 hT)) (Z_to_bv 64 stp))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma HTC : forall q, 0 <= q < 2^tl -> (bv_swrap 32 hT mod 18446744073709551616 < q <-> hT < q).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_bdt_gen ()) ["Gen"] "h04__x1h12Hah24__p1h33H28h44HJT0h57__arithh64__ffh77__sat29h87__sat30h97__sat31h:7__sat32h;7__sat33h<7__sat34h=8__varmaph>5__with?4cstrh@5cstr0hA3z28hB4__p2hC4__x2hD4__x3hE1xhF1HhG3H13hH3H14hI3HT0hJ3HT1hK1zhL2H0hM2H1hN3H10hO3H11hP3H12hQ3H15hR2H2hS2H3hT2H4hU2H5hV2H6hW2H7hX2H8hY2H9hZ2HLh[2Hqh\3P12h]2hTh^1oh_1qh`1yp%0p&0p;1p;2p;3p;<p;4p;5p;6p;7p;8p;Bp10000p4p7210g000\R0p4p710p8g001:j11Tg001_j17Tg002=j2MTg002Zj20Tg0036j26Tg003Qj14Tg0046j1VTg004Tj1kTg0057j2WTg005Wj1JTg0066R1j1fTg006Vk208Tg006mj3Cj1^Tg007GR2j1HTg007gj2aTg008DR3j2KTg008aj2wTg009Dj3uTg009aj2FTg00:;l<oTg00:`j4mTg00;Gj1`Tg00;lj2jTg00<Nj22Tg00<jR4j2DTg00=Dj2PTg00=lj3NTg00>Pj1iTg00?0j1hTg00?Pj1gTg00?nj1eTg00@Lj1dTg00A7j2UTg00AZk207Tg00B<k206Tg00Bhk305Tg00CGk404Tg00D9j2STg00DWj2RTg00E:k101Tg00E\k500Tg00FCj2}Tg00F`j2_Tg00GGj2ITg00Ggj25Tg00H@j2]Tg00H]j4vTg00I8j6XTg00ITj5;Tg00J1j3tTg00JTj3sTP0j6[j8{Tg00K7j2LTg00K`j3GTg00LIj2YTg00M5j3ZTg00MUj4\Tg00N3j1pTg00NQj2xTg00OUj3yTg00P8j7zTg00P\l<|Tg00QAlBlTg00Qgj4bTg00RRj7cTg00S6k602Tg00SZk703Tg00T>j8TTg00TbR0f0R5'2p=3%15#1p=Eg00U@R6f1R7;C5p=>P6g00U^R8P6P6P1f4R1P2f3R9g00V=f2R:P7P5M<|p=rP8P8P8P6P6P6g00VjP2P2P2P3g00WJf5R3P1P9P:P7P5MBlp=q1005p=81U65p=:P:g00WmR;g00XLR<P<g00XlR=P6P7g00YLP5Cbg00Z3R>Fcp=9P7P;P<P<P=P5J02p=QP6P7g00ZSP5Cbp=AP7P;P<P<P=P5P>Fcp=@P:P;P<P<P=P7P5K03p=<P9P;P<P<P=P:P7P5GTp=O%15#1#1#1p=~%15#1#1#1#1#1#1#1p=?f6R>P;P<P<P=P3P1P9P;P<P<P=P:P7P5GTGTp=B%45#4#4#4p=n%45#4#4#4#4#4#4#4p==%35S00g00[:R?#1R@#7RAp,2tlRB'MRC,05'6PAPB%4?S01#E#7RD%1@RE#1RF#V#kp,2jt'WRGg00[_S02#JS03#J#JS04#JRH%fCRI+08RJ5C8%HGRK%7ERE1a0CRL'K'>RMP8P6%^8P2%^6%H7%H5'>AC8751w753uX`8XE8PGPK1F6KPJ1a05XE6RJPCO1R8,KEPHPE1F6EPIP8P5XE6PJPCPC1F6CDrEqM<op,3HJTCmRJPMp,2nc,W6R8#`RI%H8R8#3R2%`GRG%3KRK1j0CRN%8CRO1>LC'612C0AC6L0'6'DRPPLP6%EFRF#7RQ,PARR%8ARS%3Q1MAQRT#8[[RU%3ARVg00\>RWANAQ7UW1RQ%3T\W^1VRX%1FRY#7RZ,PAR[%3Z1MAZR\#8[\SR]ANAZ7VWX1VRZ%3\\W^1VR^1PABR_%3BPO[\SROANAB7VWX1VR`%3C\W^1VRVg00\ZRW#iRa%hWRb%g6S05%e6Rc%d6Rd1U60Re%:AS0639S07207d=RfP5P:g00]FRgg00]fRh'F2065:=CghdB05607H04R0b6b=b>PSP5b5b7b8b9b:b;b<bAb3b@b?b4PJPMPIP2PGPKPNPPPLP6PRPUPQPXP[P]PZP^P_POP`PVp-0RhPaPb1S67S08PcPd1Qd91R6?Rg%:D'A,@dRi5<d&01<RjPiCOPfP0b6b=b>X06W2125D,67127D[^06^2hP5%7?R?/2BRiPBp,3HTLRkO3b5b7b8b9b:b;b<bAb3b@b?b4I00%EYRY#~Rl#7Rm,2Cp,3HT1S09p,2hTRn/0CRo1}T?Rp,>nRq'DP4PoPq%VFRF/_nS0:%1lRl#E#?#?R4#1#?#?#?#?#7Rr'I/0110n1'5P5P6Pn1I5r/0>10n>Rs'5XK6P6Pn105>/5sXK6Pi12BDRD10n3Rs/5sp,3stpRs#8Rt%7l,0sRsf7S0;,0nRl/5lp,2M1Rl,2?Ru%7Y,2lRlf9,0nRY/5Y%3nRY10nTRvf;,0nRw/5wp,2NCRw#8Rx1KA8,]wR8/2\RAf=,0nRy/5yp,2TDRy#8Rz1KEC,]yRE/2\R\f?S0<,0nR{/5{fAR{#3R|10{C10n{R}/5}fBS0=/0CPoPqfCR},0nR~/5~128yRy12EwREfD,0nRw/5wfE,0nRwfF,0n[R8P8P5XQwRwPwCvRwXHyPwXHEp,3DNTEXREXGoPEXGqQ09EXWPXO|f@D;XN\XYzp,3HTDD;XXAXWxp,3HNCD;XVvXUYp,3HT0RYD;XTlXSup,3HM1D;XRsXMtp,4HSTPD;XLDXFiPkD;1InrPJPMPIP2PGPKPNPPPLP6PRPUPQPXP[P]PZP^P_POP`PVPaPbQ08PcPd1Aeg,@dRiQ06=t6FRt99dg5<dPj%:r99dg9<diCOPfP0b6b=b>X06Q00105T'6Rs%37107r'6[^06P5PnPYO2b5b7b8b9b:b;b<bAb3b@b?b49snrE[Q0:PJPMPIP2PGPKPNPPPLP6PRPUPQPXP[P]PZP^P_POP`PV1L6HRHQ04,L6RuQ02,L65G65G6g00^FRl'Y=ZWaPbP61S6:P7P6Q05P91S69C\C\RxPcPdPdQ07PjPd1R6@R@,Ae,@dPjQ01#4RA,R6Rz99deFBRePjPdA9dgzR\PjPd%:m,Az,@dRzPjPd1Qd3R|9<diPjPd%:?Ri/A@,@d1Qd>5<dR@Pj%p4RE#:/Ag,@d%74R4#:99dg5<dCOFBFBPfP0b6b=b>X06XC6XD6X2hXBh%3:%81[\SRS1079121m%39/6>12?3f8R>'612E31034'6[[[[[^06^C6^D6^2h^BhP5PDPvPCPBPnP:f<Q0<PYPkO:b5b7b8b9b:b;b<bAb3b@b?b4,xnE[XZoP5O1P6Pp107C1>7p'D1_F:/Ir/0>10:>'5]J^IsX]6%3p10pT'610pC1>pp'DPJPMPIP2PGPKPNPPPLP6PRPUPQPXP[P]PZP^P_POP`PVQ03,L69G6u9G6H/Yl=ZWaPbPxPcPdPePjPdPzPjPdA<d|\PjPdP@PjPdP;P<P<P=%4A#n#=#=#=#=#=#=#=#7RA#:=9dgAy6ti=9dgFzFBFBPfP0b6b=b>X06XC6XD6X2hXBh129m10:1,6312?1Q0;'610A110p1'5[[[\S^06^C6^D6^2h^BhP5PD%3}PCPBP}P:P{Q0=PkO9b5b7b8b9b:b;b<bAb3b@b?b4WJWIPnP5PYQ09G{XFqP5O1n200100000021100011000b^b\W[X_6o"). Qed.

  Lemma PT : 2 <= 2^tl <= 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_bdt_gen ()) ["Gen"] "h02Hah13H28h24HJT0h37__arithh44__ffh54__p1h67__sat29h77__sat30h87__sat31h97__sat32h:7__sat33h;7__sat34h<8__varmaph=5__with>4__x1h?4cstrh@5cstr0hA3z28hB1xhC7__sat35hD7__sat36hE1yp;1p;2p;3p;<p;4p;6p;5p;Bp;7p;8g001:j10Tg001_j14Tg002=j2;Tg00<Nj22Tg0046j1GTg004Tj1ZTg0057j2ATg005Wj1>Tg0066R0j1RTg006Vj2OTg006mj33j1FTg007GR1j17Tg007gj2BTg008DR2j2HTg008aj2\Tg009Dj3YTg009aj2=Tg00:;l<UTg00:`j4TTg00;Gj1@Tg00;lj2STg002Zj25Tg0036j2:Tg00<jj2QTg00=Dj28Tg00=lj36Tg00>Pj1NTg00?0j1LTg00?Pj1KTg00?nj1MTg00@Lj1JTg00A7j29Tg00J1j3PTg00Qgj4?Tg00AZj2ITg00B<j2hTg00Bhj3gTg00CGj4fTg00D9j2eTg00DWj2dTg00S6j6_Tg00E:j1[Tg003Qj1]Tg00E\j5CTg00H]j4^Tg00P\l<XTg00QAlB`Tg00RRj7aTg00SZj7bTg00T>j8cTg00U@R3g00U^R4P3P3P0f4R0P1f3R5g00V=f2R6f1R7f0R8M<Xp=WP4P4P4P3P3P3g00VjP1P1P1P2g00WJf5P0P5P6P7P8MB`p=Vg00TbR0/28p=1P7g00WmR2g00XLR9P9g00XlR:P8g00Z3Fap=<P6P2P9P9P:P7P8Fbp=EP5P2P9P9P:P6P7P8Gcp=Dg00[:R;#0R<#4R=p,2tlR>,;=R?'2%0<R<#0R@#0#0RA#0RB#0#0#0#0#0#0#4,2?%4;RC,;=RDPCP>%G@#Zp,2jt'AR@g00[_#>#>#>#>RE%R?RF'ORG534%7@RH%4<R<1B0?RI'H533RJP4P3%F4P1%F3%77%78533A34781\783YXE4XB4P@PH1=3HPG1B08XB3RGP?O1R4,H<PEP<1=3<PFP4P8XB3PGP?P?1=3?DWEVM<Up,3HJTCTRGPJp,2nc,A3R4#@RF%74#1R4%@@R@%1HRH1S0?R<150?REA33I?':12?0A33I0':'QR1PIP3%4ARA,8=RK150=RL%1A1;=ARM,50[[RN%1=ROg00\>RPA6=A7UW0RA%1M\P^0ORM18=C%1C150DRQ[\LA6=C7VPX0O%1D\P^0O%4BRB,8=RD%1B1;=BRR,50[\LRSA6=B7VPX0ORB%1R\P^0ORR18=>RT%1>PE[\LREA6=>7VPX0ORU%1?\P^0OROg00\ZRP#NR?%LPRP%K3RV%M3RW%J3RXP31930RYg00YLRZ193=R[%G;5P3C?'<1IX:R\P8P6g00]FR]g00]fR^'=1h86=3]^dAg307CfR0b4b<b=PQP8b3b6b7b8b9b:b;bCbDbAb1b@b?b2PGPJPFP4P@PHP<P1PIP3PKPNPAPMPDPSPBPRPTPEPUPOp-0RQP?PP1e37R^PWPXP3193Cg00ZSR]1d3;R6C?,<XR_PXP2P9P9P:P5E_R55EX%[9R9P_CDP\P0b4b<b=X>3W512C8/:712C7[^>3^5QP8%];#0#0#4R;,2>P>p,3HTLR_O3b3b6b7b8b9b:b;bAb1b@b?b2DCP=P>P;PGPJPFP4P@PHP<P1PIP3PKPNPAPMPDPSPBPRPTPEPUPOP?PPPVPWP3PYPZP[C?,<XP\P0b4b<b=PLP8b3b6b7b8b9b:b;bAb1b@b?b2PGPJPFP4P@PHP<P1PIP3PKPNPAPMPDPSPBPRPTPEPUPOP?PPP^PWPXP3P6P]193;C?,<XR]9EX5P9P]CDP\P0b4b<b=X>3X5Q128;,:7127;[^>3^5QP812C>P>P_O3b3b6b7b8b9b:b;bAb1b@b?b2DCC^o"). Qed.

  (* [comment removed for export] *)
  Lemma sk_loop : forall f p p1 mm (x7 x8 x9 x10 x13 : word),
    skip_loop tl f (Z.land (p + stp) (2^tl - 1)) hT = Ok p1 -> 0 <= p < 2^tl ->
    (0 <= p1 < 2^tl -> (hT < p1 -> False) ->
       evt usegs POST (STC 0x1f480 mm x7 x8 x9 x10 (Z_to_bv 64 p1) x13)) ->
    evt usegs POST (STC 0x1f474 mm x7 x8 x9 x10 (Z_to_bv 64 p) x13).
Proof.
  intros f. induction f as [|f IH]; intros p p1 mm y7 y8 y9 y10 y13 SK HP KONT; cbn [skip_loop] in SK; [discriminate|].
  pose proof PT as PT2. pose proof (land_mask_range (p + stp) tl ltac:(lia)) as QR.
  pose proof (HTC _ QR) as (HQ1 & HQ2).
  zstep; rewrite ?(swrap32_small (stp + p)), ?(swrap32_small (p + stp)) by lia; zstep;
    rewrite ?(Z.add_comm stp p); try replace (2^tl + -1) with (2^tl - 1) by lia.
  zstep; if_cases K; zify_cond K;
    revert SK; destruct (Z.ltb_spec hT (Z.land (p + stp) (2^tl - 1))) as [L|L]; intro SK; try (exfalso; lia).
  all: first [ eapply IH; [rewrite <- ?HSTPV in SK; exact SK | exact QR | exact KONT] | injection SK as <-; apply KONT; [exact QR | lia] ].
Qed.

  (* [comment removed for export] *)
  Lemma sy_loop : forall f s n i syms position r m1 (x9 x13 : word),
    sym_loop tl f i n s syms position hT = Ok r ->
    0 <= i < n -> n < 2^31 -> 0 <= s < 256 -> 0 <= position < 2^tl -> length syms = Z.to_nat (2^tl) ->
    gn_inv m1 syms ->
    (forall m2 syms' p' (y9 : word), r = (syms', p') -> 0 <= p' < 2^tl -> length syms' = Z.to_nat (2^tl) ->
       gn_inv m2 syms' ->
       evt usegs POST (STC 0x1f488 m2 (Z_to_bv 64 s) (Z_to_bv 64 n) y9 (Z_to_bv 64 n) (Z_to_bv 64 p') x13)) ->
    evt usegs POST (STC 0x1f464 m1 (Z_to_bv 64 s) (Z_to_bv 64 i) x9 (Z_to_bv 64 n) (Z_to_bv 64 position) x13).
Proof using All.
  intros f. induction f as [|f IH]; intros s n i syms position r m1 y9 y13 SL HI HN HS HP HL GI KONT; cbn [sym_loop] in SL; [discriminate|].
  revert SL; destruct (Z.ltb_spec i n) as [L|L]; intro SL; [|lia].
  pose proof PT as PT2. rewrite ostore_ok in SL by (unfold FseNCount.Zlength; rewrite HL; lia). cbn [bind] in SL.
  destruct (skip_loop tl (S (Z.to_nat (2^tl))) (Z.land (position + table_step (2^tl)) (2^tl - 1)) hT) as [p1| | |] eqn:SK;
    cbn [bind] in SL; try discriminate.
  rewrite <- HSTPV in SK. destruct GI as (ARR & MU & WM & MI).
  zstep; rewrite ?(Z.mod_small position (2^64)) by lia;
    rewrite ?(Z.mod_small (Z.shiftl position 2) (2^64)) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
    try replace (Z.shiftl position 2) with (4 * position) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep; if_cases K; zify_cond K;
    [exfalso; rewrite ?zb_lxor_ones in K by lia; Z.div_mod_to_equations; lia | clear K].
  zstep. tdb TD ARR position.
  eapply (sk_loop _ position p1); [exact SK | exact HP |]. intros QR1 QR2.
  zstep; rewrite ?(swrap32_small (i + 1)) by lia; zstep; if_cases K; zify_cond K.
  - eapply (IH s n (i + 1)).
    + exact SL.
    + lia.
    + lia.
    + lia.
    + exact QR1.
    + rewrite oupd_nat_length; exact HL.
    + unfold gn_inv; refine (conj _ (conj _ (conj _ _))); assumption.
    + exact KONT.
  - destruct f as [|f]; cbn [sym_loop] in SL; [discriminate|].
    revert SL; destruct (Z.ltb_spec (i + 1) n) as [L2|L2]; intro SL; [lia|].
    injection SL as <-. replace (i + 1) with n by lia.
    eapply KONT.
    + reflexivity.
    + exact QR1.
    + rewrite oupd_nat_length; exact HL.
    + unfold gn_inv; refine (conj _ (conj _ (conj _ _))); assumption.
Qed.

  Lemma g_shl32_shr31 : forall x, 0 <= x < 2^31 -> ((x ≪ 32) mod 18446744073709551616) ≫ 31 = 2 * x.
  Proof.
    intros x Hx. change 18446744073709551616 with (2^64). rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
    replace (x * 2^32) with ((2 * x) * 2^31) by (change (2^32) with (2 * 2^31); lia). apply Z.div_mul. lia.
  Qed.

  Lemma gn_next : forall s mm (x8 x9 x10 x12 x13 : word),
    0 <= s < M1 ->
    (s + 1 < M1 -> evt usegs POST (STC 0x1f440 mm (Z_to_bv 64 (s + 1)) x8 x9 x10 x12 x13)) ->
    (s + 1 = M1 -> evt usegs POST (STC 0x1f4fc mm (Z_to_bv 64 M1) x8 x9 x10 x12 x13)) ->
    evt usegs POST (STC 0x1f438 mm (Z_to_bv 64 s) x8 x9 x10 x12 x13).
  Proof using All.
    intros s mm y8 y9 y10 y12 y13 HS KH KE.
    zstep; rewrite ?(swrap32_small (s + 1)) by lia.
    zstep; if_cases K; zify_cond K.
    all: first [ replace (s + 1) with M1 by lia; apply KE; lia | apply KH; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma gn_loop : forall f s syms position r m1 (x8 x9 x10 x13 : word),
    gen_loop nc tl f s syms position hT = Ok r ->
    Z.of_nat f = M1 - s -> 0 <= s < M1 -> 0 <= position < 2^tl -> length syms = Z.to_nat (2^tl) ->
    gn_inv m1 syms ->
    (forall m2 syms' p' (y8 y9 y10 y13 : word), r = (syms', p') -> 0 <= p' < 2^tl -> length syms' = Z.to_nat (2^tl) ->
       gn_inv m2 syms' ->
       evt usegs POST (STC 0x1f4fc m2 (Z_to_bv 64 M1) y8 y9 y10 (Z_to_bv 64 p') y13)) ->
    evt usegs POST (STC 0x1f440 m1 (Z_to_bv 64 s) x8 x9 x10 (Z_to_bv 64 position) x13).
Proof using All.
  intros f. induction f as [|f IH]; intros s syms position r m1 y8 y9 y10 y13 GL HF HS HP HL GI KONT; [lia|].
  cbn [gen_loop] in GL. unfold FseNCount.load in GL.
  revert GL; destruct (Z.leb_spec 0 s), (Z.ltb_spec s (FseNCount.Zlength nc)); cbn [andb]; intro GL;
    unfold FseNCount.Zlength in *; try lia.
  cbn [bind] in GL.
  pose proof (Forall_Znth _ nc s HNCR ltac:(lia)) as NR; cbn beta in NR.
  destruct (sym_loop tl (S (Z.to_nat (Znth s nc))) 0 (Znth s nc) s syms position hT) as [[syms1 p1]| | |] eqn:SY;
    cbn [bind] in GL; try discriminate.
  pose proof PT as PT2. pose proof GI as GI0. destruct GI as (ARR & MU & WM & MI).
  assert (NCB : bytes_at usegs m1 NC (u16s (map (Z_to_bv 64) nc))).
  { apply (bytes_at_transport usegs _ m m1 _ _ NCB0 MU); cbn [disjoint_from]; rewrite u16s_length, ?length_map, ?map_length; lia. }
  zstep. zstep. rewrite ?(g_shl32_shr31 s) by lia.
  zstep.
  if_cases KC; zify_cond KC; [exfalso; rewrite ?zb_lxor_ones in KC by lia; rewrite ?(g_shl32_shr31 s) in KC by lia; lia | clear KC].
  zstep. rewrite ?(Z.mod_small s) by lia.
  zstep. zstep.
  replace (NC + s ≪ 1) with (NC + 2 * s) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  lazymatch goal with |- _ => let a := OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.STRW_tac.cur_mem_addr in
    pose proof (u16_znth usegs m1 NC nc s a NCB ltac:(lia) ltac:(OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.STRW_tac.addr_tac)) as RD end.
  zstep. rewrite ?(sx16_short (Znth s nc)) by lia.
  zstep. if_cases K; zify_cond K.
  - assert (NLE : Znth s nc <= 0).
    { destruct (Z_le_gt_dec (Znth s nc) 0) as [|G]; [assumption|]. exfalso.
      repeat match goal with H : context [Znth s nc mod _] |- _ => revert H end.
      rewrite Z.mod_small by lia. intro K'. apply andb_false_iff in K'; destruct K' as [K'|K']; apply Z.ltb_ge in K'; lia. }
    cbn [sym_loop] in SY. revert SY; destruct (Z.ltb_spec 0 (Znth s nc)) as [L0|L0]; intro SY; [lia|].
    injection SY as E1 E2. subst syms1 p1.
    eapply gn_next; [lia | intro HS1 | intro HS1].
    + eapply (IH (s + 1) syms position r m1); [exact GL | lia | lia | exact HP | exact HL | exact GI0 | exact KONT].
    + destruct f as [|f]; [|lia]. cbn [gen_loop] in GL. injection GL as GL. subst r.
      eapply KONT; [reflexivity | exact HP | exact HL | exact GI0].
  - assert (NPOS : 0 < Znth s nc).
    { destruct (Z_le_gt_dec (Znth s nc) 0) as [L|G]; [|lia]. exfalso.
      repeat match goal with H : context [Znth s nc mod _] |- _ => revert H end.
      clear - NR L. intros. Z.div_mod_to_equations. lia. }
    zstep.
    eapply (sy_loop _ s (Znth s nc) 0 syms position (syms1, p1) m1); [exact SY | lia | lia | lia | exact HP | exact HL | exact GI0 |].
    intros m2 syms' p' y9' E QR LL GI2. injection E as E1 E2. subst syms' p'.
    zstep.
    eapply gn_next; [lia | intro HS1 | intro HS1].
    + eapply (IH (s + 1) syms1 p1 r m2); [exact GL | lia | lia | exact QR | exact LL | exact GI2 | exact KONT].
    + destruct f as [|f]; [|lia]. cbn [gen_loop] in GL. injection GL as GL. subst r.
      eapply KONT; [reflexivity | exact QR | exact LL | exact GI2].
Qed.
End Gen.

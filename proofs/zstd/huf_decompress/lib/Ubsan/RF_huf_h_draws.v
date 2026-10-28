(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer HufHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_h_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_h_draws () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1Z02I47Corelib4Init9Datatypes4prod00K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness:huf_params01C5ARocqVerifyHarness?AgentSubmission4Spec<FuzzProducer;uint32RangeC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness9huf_drawsC5ARocqVerifyHarness?AgentSubmission4Spec<FuzzProducer:int32RangeK47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness7flag_ofI47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness@HUF_TABLELOG_MAXC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarnessFHUF_flags_preferRepeatC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarnessOHUF_flags_suspectUncompressibleC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarnessDHUF_flags_disableAsmC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarnessEHUF_flags_disableFastC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarnessFHUF_flags_optimalDepthI5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness:huf_params00K47Corelib7Numbers7BinNums8positive03C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zC47Corelib4Init5Logic8eq_ind_rK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface7prod_atC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface:payload_atC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_draws7hB_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib5Lists4List:length_mapc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_draws@huf_draws_unfoldC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness=int32Range_01C5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiI4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib6ZArith6BinInt1Z3divC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sltuK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sltuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC56Stdlib6ZArith6BinInt1Z3lorK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07C5ARocqVerifyHarness?AgentSubmission3Lib5Bytes;lor_lt_pow2K4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC5ARocqVerifyHarness?AgentSubmission4Spec<FuzzProducerAuint32Range_rangeC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface>prod_u32r_postC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z6shiftrK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sllwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_sllwC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness6hp_mtlC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness:hp_streamsC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness:hp_symbolsC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness7hp_dbufC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness7hp_restC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness8DT_BYTESC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C45stdpp9bitvector;definitions8bv_swrapK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC56Stdlib6ZArith6BinInt1Z:shiftl_1_lC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_15C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zb_shl_shrC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_draws6snez01C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:v_sltu_b2zC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtK47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface>prod_i32r_postK46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula03C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib4Exec7evt_cutC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic4True00K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop03c5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_draws;PC_HB_ENTRYI47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop07c5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_draws=PC_HB_EXIT_RAc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_draws?PFUZZ_MALLOC_HB".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_HB_ENTRY : Z := 0x13284.      (* [comment removed for export] *)
Definition PC_HB_EXIT_RA : Z := 0x13360.    (* [comment removed for export] *)
Definition PFUZZ_MALLOC_HB : Z := 0x21068.  (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma huf_draws_unfold : forall pl n,
  exists streams s1 symbols s2 f1 s3 f2 s4 f3 s5 f4 s6 f5 s7 dbs s8 mtl s9,
    int32Range pl n 0 1 = (streams, s1) /\ int32Range pl s1 0 1 = (symbols, s2)
    /\ int32Range pl s2 0 1 = (f1, s3) /\ int32Range pl s3 0 1 = (f2, s4) /\ int32Range pl s4 0 1 = (f3, s5)
    /\ int32Range pl s5 0 1 = (f4, s6) /\ int32Range pl s6 0 1 = (f5, s7)
    /\ uint32Range pl s7 0 (8 * n + 500) = (dbs, s8) /\ uint32Range pl s8 1 12 = (mtl, s9)
    /\ huf_draws pl n = mkHP streams symbols
         (flag_of f1 HUF_flags_optimalDepth + flag_of f2 HUF_flags_preferRepeat + flag_of f3 HUF_flags_suspectUncompressible
          + flag_of f4 HUF_flags_disableAsm + flag_of f5 HUF_flags_disableFast) dbs mtl s9.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_draws ()) [] "p'0h02s9i002s9h13mtli013mtlh22s8i022s8h33dbsi033dbsh42s7i042s7h52f5i052f5h62s6i062s6h72f4i072f4h82s5i082s5h92f3i092f3h:2s4i0:2s4h;2f2i0;2f2h<2s3i0<2s3h=2f1i0=2f1h>2s2i0>2s2h?7symbolsi0?7symbolsh@2s1i0@2s1hA7streamsi0A7streamshB1pi0B1phC2E1hD2E2hE2E3hF2E4hG2E5hH2E6hI2E7hJ2E8hK2E9hL1nhM2pli0C1xi0D1zp%0p;1p;2p;6p;4p;3g0000j1hTg000Pj1VTg000nR0j2cTg001Nj2\Tg001hj1LTg002Mj1QTg0032j6>Tg0043j4DTg0055j25Tg005Rj3<Tg005lj2:Tg006Gj4ZTg006bj2eTg007`j4TTg008aj4YTg009Aj2[Tg009^j2=Tg00:Zj2dTg00;4j4`Tf2R1f1R2g00;NR3f0R4CTp=2f4R5f3R6P1P3P2CT;<4p=4g00;lR7P7P2P4CYp=31[12/54p=FP1P2P3P4CDp=MP1P2P4g00<JCDp=Ag00=OR8,=4p=Bg00>ZR9,=4p=Eg00?nR:,=4p=Ng00A7R;,=4p=;g00BAR<,=5/56/51/52/54p=fg00CLR=?<24p=Gf6R>f5R?P5P6P1CD;<2/:4p=8f7R@P>P?P31[56/51CD;<2/:4p=9P5P6P3P1CT=<?2/:4p=1A<>?5A<612/:4':p=61d74p=0P5P6P31[12/54CDp=P1=2</54p=K1512/54p=CP>P?1556P1P2P4E>p=@1=1</52/54p=XP6P1P3P2CD=<54p=OP5P6P1P2CD=<?4p=W1=4<p=_1=68,55/51/52/54p=^A<=24,:1p=S1:24,:1p=J1=5<1=68'51=19'51=2:'5/54p=IP>P?P5P6P1P2E>=<=4p=?P7P7P1P2CY9<56/:4p=]P?P5P3P6CTP7P7P1P2CY5<>/:4p=71=49,52p=b1=2:,51/54p=U1=4:,52p=g1=4;,52p=aP>P?P5P6P1P2P4CZCZp=RP7P5P6P7P1P2P4C`C`p=H%h7g00DMR;#VR:92241c77R91\94R3P9P1P2P:P4D4P0P7P7P9P5P6P:P4D4P9fCR8fAS00f@R<'3RAP9fGRB?2<:f?RCf>RD'3REP9PBPDP:f=S01f<RF'3RGP9PBPFP:f;S02f:RH'3RIP9PBPHP:f9S03f8RJ'3RKP9PBPJP:13@>RLP9PBP>P:13?5RMP9PBP5%L;#L#L#VRNfFS04%Q;R;#Q#Q#Q#L#Q#L#L#VRO1361RPP9PBP1P:%L;#L#VR;1324RQP0P7P7P=P8P0P7P7P=fIS05?24:P0P7P7P=fKS06?24:P0P7P7P=fMRR?24:P0P7P7P=fOS07?24:P0P7P7P=fQS08?24:P0P7P7P=fSS09?24:P0P7P7P=fURSfTRT=FNORU7M4P0P7P7P=fWRV?A4:Q00PCQ01Q02#BS0:Q03#ERW%N@RX%;?RYDfS0;P6P2P4E>RZn200110C000120101100n200110C000120103102n200110C000120105104n200110C000120107106n200110C000120109108n200110C00012010;10:n200110C00012010=10<n200110C00012010?10>n200110C00012010A10@/GZF8G9E1E1E1E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7#0X=7#0X>7#0X?7#0X@7#0XA7#0]CP2P9P@P>P:PQD4A2J2:P9P3P9Q03P1P:P4D4P0P7P7P9Q02P5P:P4D4P9fHS0</3BS0=PAP9fNR[?2<:PEP9P[PDP:PGP9P[PFP:PIP9P[PHP:PKP9P[PJP:PLP9P[P>P:PMP9P[P5PNPRPOPPP9P[P1P:P;PQP0P7P7P=P8P0P7P7P=fPR\?24:P0P7P7P=fRR]?24:P0P7P7P=A2T4:P0P7P7P=fVR^?24:P0P7P7P=fXS0>?24:P0P7P7P=fZS0?P4PNfYR_PODPP0P7P7P=f\R`?A4:Q0>PCQ0;P6P2P4E>n200110C000120101100n200110C000120103102n200110C000120105104n200110C000120107106n200110C000120109108n200110C00012010;10:n200110C00012010=10<n200110C00012010?10>/GZF8G9E1E1E1E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7#0X=7#0X>7#0X?7#0X@7#0XA7#0]DP2P9PDP@P:PQD4A2C2:P9P3P9P<P1P:P4D4P0P7P7P9fBRaP5P:P4D4P9Q07/3[S0@PAP9A2S<:PEP9PSPDP:PGP9PSPFP:PIP9PSPHP:PKP9PSPJP:PLP9PSP>P:PMP9AMS5UPPP9PSP1P:P;CDPQP0P7P7P=P8P0P7P7P=A2V4:P0P7P7P=A2_4:P0P7P7P=f[RU?24:P0P7P7P=f]Rb?24:P0P7P7P=f_S0AP4PNf^RcPODPP0P7P7P=faS0B?A4:PbP^Q0;P6P2P4E>n200110C000120101100n200110C000120103102n200110C000120105104n200110C000120107106n200110C000120109108n200110C00012010;10:n200110C00012010=10</GZF6E1E1E1E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7#0X=7#0X>7#0X?7#0X@7#0XA7#0]EP2P9fES0CP@P:PQD4Q04?22:P9P3P9PBP1P:P4D4P0P7P7P9Q05P5P:P4D4P913^SS0DPAP9A2`<:PEP9P`PDP:PGP9P`PFP:PIP9P`PHP:PKP9P`PJP:PLP9P`P>P:PMP9P`P5PNPUPOPPP9P`P1P:P;PQP0P7P7P=P8P0P7P7P=A2c4:P0P7P7P=f`S0E?24:P0P7P7P=fbRd?24:P0P7P7P=fdReP4PNfcRfPODPP0P7P7P=ffRg?A4:PdPUQ0:,KT?CWXPYP6P2P4F@n200110C000120101100n200110C000120103102n200110C000120105104n200110C000120107106n200110C000120109108n200110C00012010;10:/GZF8G9E1E1E1E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7#0X=7#0X>7#0X?7#0X@7#0XA7#0]FP2P9fLS0FP@P:PQD4A2R2:P9P3P9P[P1P:P4D4P0P7P7P9P\P5P:P4D4P913b`S0GPAP9A2f<:PEP9PfPDP:PGP9PfPFP:PIP9PfPHP:PKP9PfPJP:PLP9PfP>P:PMP9AFNdORh9Mf5PPP9PfP1P:P;CDPQP0P7P7P=P8P0P7P7P=feRi?24:P0P7P7P=fgRj?24:P0P7P7P=fiRkP4PNfhRlPODPP0P7P7P=fkRm?A4:PjQ0E%B],K_?CWXPYP6P2P4F@n200110C000120101100n200110C000120103102n200110C000120105104n200110C000120107106n200110C000120109108/GZF6E1E1E1E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7#0X=7#0X>7#0X?7#0X@7#0XA7#0]GP2P9Q09P@P:PQD4A2T2:P9P3P9PSP1P:P4D4P0P7P7P9PVP5P:P4D4P913efS0HPAP9fjRn?2<:PEP9PnPDP:PGP9PnPFP:PIP9PnPHP:PKP9PnPJP:PLP9PnP>P:PMP9PnP5PNPkPOPPP9PnP1P:P;PQP0P7P7P=P8P0P7P7P=flRo?24:P0P7P7P=fnRpP4PNfmRqPODPP0P7P7P=fpRr?A4:PoPi%BV%E\5XcS0I/5XPYP6P2P4F@n200110C000120101100n200110C000120103102n200110C000120105104n200110C000120107106/GZF8G9E1E1E1E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7#0X=7#0X>7#0X?7#0X@7#0XA7#0]HP2P9Q0?P@P:PQD4A2U2:P9P3P9P`P1P:P4D4P0P7P7P9PcP5P:P4D4P913mnS0JPAP9fqRs?2<:PEP9PsPDP:PGP9PsPFP:PIP9PsPHP:PKP9PsPJP:PLP9PsP>P:PMP9AFNrOS0K9Ms5PPP9PsP1P:P;CDPQP0P7P7P=P8P0P7P7P=fsRtfrRu=FNOS0L7M4P0P7P7P=fuRv?A4:PsPn%B`,Kf%ES%N[3CS0MPYP6P2P4F@S0Nn200110C000120101100n200110C000120103102n200110C000120105104/GZF6E1E1E1E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7#0X=7#0X>7#0X?7#0X@7#0XA7#0]IP2P9Q0BP@P:PQD4PdP2PNQ0BPODPP9P3P9PfP1PhP4DOP0P7P7P9PiP5AFNeOP4DOP913usS0OPAP9fxRh?2<:PEP9PhPDP:PGP9PhPFP:PIP9PhPHP:PKP9PhPJP:PLP9PhP>P:PMD4S0PP9PhP5fwRw=FNOPPDOS0QP9PhP1P:P;PQEWS0RP0P7P7P=P8P0P7P7P=fzRx?A4:fvRyfoRz%_lS0SQ0BQ0?#EQ09#NQ0F#;D^S0TP6P2P4E>n200110C000120101100n200110C000120103102;SZ3JE1E1E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7#0X=7#0X>7#0X?7#0X@7#0XA7#0]JP2P9PlP@AFNjOPQDOAAk2:P9P3AAn1:=<94P0P7P7AAo5:=<94P9fyR3/3hS0UPAP9p+01@R{?2<:PEP9P{PDP:PGD4S0VP9P{PFP:PID4S0WP9P{PHP:PKD4S0XP9P{PJP:PLD4S0YP9P{P>P:PMD4S0ZP9P{P5f~S0[=FNOPPDOS0\P9P{P1P:P;PQEWS0]P0P7P7P=P8f{R0ftR|PqPgQ0AQ0>Q08#;DIS0^fJS0_P2P4E>n200110C000120101100;SZ3J3J3JF6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7#0X=7#0X>7#0X?7#0X@7#0XA7#0]KP2AAz@:=<9QP9f|R}/30PAP9p+01CR~?2<:PEP9P~PDP:PGP9P~PFP:PIP9P~PHP:PKP9P~PJP:PLP9P~P>P:PMP9P~P5PNp+01BS0`POPPP9P~P1P:P;PQP}PvPpPjQ0EP_%;]DIQ06fDS0aP8PZF?F8G9E1E1E1E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7#0X=7#0X>7#0X?7#0X@7#0XA7PnP9130xP0P<P9Q0`P<P:PEP9Q0`PDP:PGP9Q0`PFP:PIP9Q0`PHP:PKP9Q0`PJP:PLP9Q0`P>P:PMP9Q0`P5PNp+01AR~POPPP9Q0`P1P:P;PQP0P|Q0^Q0_P8PaP0PCQ0;P6P2P4E>F?F8G9E1E1E1E1E1E1D]X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7#0X=7#0X>7#0X?7#0X@7PkP913x3S0^Q0^P9A2~3:PEP9P~PDP:PGP9P~PFP:PIP9P~PHP:PKP9P~PJP:PLP9P~P>P:PMP9P~P5PNP{POPPP9P~P1P:P;PQPxPtPoPiPcPV%;\DIQ05PaQ00PxPCQ0;P6P2P4E>F?F8G9E1E1E1E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7#0X=7#0X>7#0X?7PfP9Q0UQ0UP9A2{h:13uDQ0VQ0WQ0XQ0YQ0ZQ0\Q0]P3Pu%Be,Km%Eb%N^3CQ07#;Q0<Q00P<F@P3PuQ0;P6P2P4E>3S3J3J3JF6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7#0X=7#0X>7PdP913hwR{P{P9Q0[?2w:13srS0WP9Q0[PrP:PGP9Q0[PFP:PIP9Q0[PHP:PKP9Q0[PJP:PLP9Q0[P>P:PMP9Q0[P5PNf}R{POPPP9Q0[P1P:P;PQPhPsPnPfP`PS%;[DIPBP<PCPhPsQ0;P6P2P4E>F?F8G9E1E1E1E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7#0X=7P`P913wyR~P~P9A2{y:13rzR~P9P{PzP:PkPFP9P{PFP:PIP9P{PHP:PKP9P{PJP:PLP9P{P>P:PMP9P{P5PNP}POPPP9P{P1P:P;PQPwPr%_kR{Pd%EU%NT%;RD^Q04PCPDPwPrQ0:,5{?CWXPYP6P2P4F@F?F8G9E1E1E1E1F7F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7PUP913yvR{P{P9A2}v:13zpR{P9P}PpP:13ljS0;P9P}PjP:PIP9P}PHP:PKP9P}PJP:PLP9P}P>P:PMP9P}P5PNP0POPPP9P}P1P:P;PQPyPzQ0TQ0CPDQ01PyPzQ0SQ0:'5?CWXPYP6P2P4F@F?F8G9E1E1E1E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7PSP913v|R}P}P9A20|:13pqR}P9P0PqP:13jgS0SP9P0PgP:Q0EPHP9P0PHP:PKP9P0PJP:PLP9P0P>P:PMP9P0P5PNPxPOPPP9P0P1P:P;PQPvPpQ0E#B,KjR0/b_Q06#;7U]Q0aQ01PFPvPpAC0WXPYP6P2P4F@F?F8G9E1E1E1F7E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7PTP913|tR0P0P9A2xt:13qoR0P9PxPoP:13giS0:P9PxPiP:Q0A/3cS0TP9PxPcP:PKP9PxPJP:PLP9PxP>P:PMP9PxP5PNP3POPPP9PxP1P:P;PQP|PqQ0A#B,KgRxQ0>'bQ08Q0_#;3UP8PFQ02P|PqACxWXPYP6P2P4F@F?F8G9E1E1E1E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97P[P913tuRxPxP9A23u:13omRxP9P3PmP:13ieS0[P9P3PeP:13cbS0VP9P3PbP:PVPJP9P3PJP:PLP9P3P>P:PMP9P3P5PNPhPOPPP9P3P1P:P;PQPtPo%Bc%EV5XiR3Q05#;7U\PaQ02PHPtPo153XPYP6P2P4F@F?F8G9E1E1F7E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87PRP9Q0OQ0OP9A2hs:Q0JP9PhPnP:Q0HP9PhPfP:Q0GP9PhP`P:Q0DP9PhPSP:PLQ0PQ0QQ0RPuPm%Bb%E^5XeRhQ07'gQ0<#;Q00PHQ03F@PuPm15hXPYP6P2P4F@3S3JE1E1E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77PBP9Q0WQ0WP9A2wr:13nkRhP9PwPkP:13fdRXP9PwPdP:13`UR3P9PwPUP:13STRWP9PwPTP:P[P>P9PwP>P:PMP9PwP5PNPyPOPPP9PwP1P:P;PQPsPnQ0M/aBP<Q03PJQ0NF?F8G9E1F7E1E1E1F6X07#0X17#0X27#0X37#0X47#0X57#0X67Q04P9P~P~P9A2yz:13klP9PyPlP:PdQ0BP9PyQ0BP:PUQ0?P9PyQ0?P:PTQ09P9PyQ09P:PRQ0FP9PyQ0FP:PMP9PyP5PNPvPOPPP9PyP1P:P;PQPrPk%BU,Kd%ET%NR3CRyQ04'aPCPJP@PrPkPyPYP6P2P4F@F?F8G9E1F7F7F7F7F6X07#0X17#0X27#0X37#0X47#0X57P<P9P{P{P9A2vp:Q0;P9PvPjP:Q0BQ0EP9PvQ0EP:Q0?P_P9PvP_P:Q09P]P9PvP]P:Q0FQ06P9PvQ06P:Q0CP5P9PvP5PNP|POPPP9PvP1P:P;PQPzPlQ0BQ0?Q09Q0FQ0C#;DIRvPDP@P>PzPlPvP6P2P4E>F?F8G9F7F7F7F7F7F6X07#0X17#0X27#0X37#0X47PCP9P}P}P9A2|q:Q0SP9P|PgP:Q0EQ0AP9P|Q0AP:P_Q0>P9P|Q0>P:P]Q08P9P|Q08P:Q06Q0_P9P|Q0_P:Q0aP8P9P|P8PNPtPOPPP9P|P1P:P;PQPpPjQ0EP_P]Q06Q0a#;DIR]Q01P>P?PpPjP]P6P2P4E>F?F8G9F7F7F7F7F7F6X07#0X17#0X27#0X37Q03P9P0P0P9A2to:Q0:P9PtPiP:Q0TP9PtPcP:Q0>PVP9PtPVP:Q08P\P9PtP\P:Q0_Q05P9PtQ05P:P8PaP9Q0L9MtaPFP1P9PtP1P:P;PQPqPgQ0AQ0>Q08Q0_%;8DIRtPFP?P5PqPgPtPFP2P4E>F?F8D]F7F7F7F7E1F6X07#0X17#0X27PJP9PxPxP9A2um:Q0[P9PuPeP:Q0VP9PuPbP:PVP^P9PuP^P:P\Q07P9PuQ07P:Q05Q0<P9PuQ0<P:PaQ00P9PuQ00PNPsPOPIP9PuPHP:P;PQPoPiQ0IQ05%;a3URuQ02P5P6PoPiPuQ02P2P4E>F?F8G9F7F7F7F7E1F6X07#0X17P1P9Q0JQ0JP9A2sn:Q0HP9PsPfP:Q0GP9PsP`P:Q0DP9PsPSP:Q0@P9PsP[P:Q0=P9PsPBP:PAP9Q0K9Ms<PHQ03P9PsQ03P:P;1364PmPePbP^Q07Q0<Q00#;DIR^PHP6P1PmPeP^PHP6P4E>F?F8D]E1E1E1E1E1F6X07P2A<9hhP9PrPkP:PXD4RXP9PrPdP:P3D4R3P9PrPUP:PWD4RWP9PrPTP:13[RD4RTP9PrPRP:Q04,3BD4RRP9PrQ04P:13<CD4RUP9PrPCAFNzOPKDORzP9PrPJP:P;1312EWRrPnPf%BS,K`%E[%NB3C%;<Q03P1P2F@RB/GBR[':R`':RS':Rf':Rn':RC':Rd':Rk':1\9hPXPkQ0BP3PdQ0?PWPCQ09PTPnQ0FPRPfQ0CPUPSPDPzP`P@PrP[P41\=BCZFRFRFRFRDHDHDHDHDHDHDHDHDHWKX07X17P2P4O2n200110B01012110D10DP4O1bKbBWJX27X37P2P4O2n200110B01012110D10DP4O1bJbBWIX47X57P2P4O2n200110B01012110D10DP4O1bIbBWHX67X77P2P4O2n200110B01012110D10DP4O1bHbBWGX87X97P2P4O2n200110B01012110D10DP4O1bGbBWFX:7X;7P2P4O2n200110B01012110D10DP4O1bFbBWEX<7X=7P2P4O2n200110B01012110D10DP4O1bEbBWDX>7X?7P2P4O2n200110B01012110D10DP4O1bDbBWCX@7XA7P2P4O2n200110B01012110D10DP4O1bCbBP9P8PaP:PAP9P8P<P:PEP9P8PDP:PGP9P8PFP:PIP9P8PHP:PKP9P8PJP:PLP9P8P>P:PMP9P8P5PNPaPOPPP9P8P1P:P;PQ1e8a/GZF8G9E1E1E1E1E1E1E1X07#0X17#0X27#0X37#0X47#0X57#0X67#0X77#0X87#0X97#0X:7#0X;7#0X<7#0X=7#0X>7#0X?7#0X@7#0XA7#0eXL7WMo"). Qed.

(* [comment removed for export] *)
Definition hB_post (gp tp s6 : word) (F : bvmap 5 word) (fc : bv 32)
    (SP P D : Z) (pl : list Z) (lo : Z) (m : fmem)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (f1 f2 f3 f4 f5 : Z) (j0 : list byte) (m' : fmem),
    ms' = MS (mkR (Z_to_bv 64 PC_HB_EXIT_RA) (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 D)
                  (Z_to_bv 64 (DT_BYTES (hp_mtl (huf_draws pl (zlen pl))))) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 f5) (Z_to_bv 64 (hp_mtl (huf_draws pl (zlen pl)))) s4 (Z_to_bv 64 1) s6
                  (Z_to_bv 64 (hp_dbuf (huf_draws pl (zlen pl))))
                  (Z_to_bv 64 f1) (Z_to_bv 64 f2) (Z_to_bv 64 f3) (Z_to_bv 64 f4) t3 t4 t5 t6)
             F (Z_to_bv 64 PFUZZ_MALLOC_HB) fc None m' (seg_rom usegs)
    /\ 0 <= f1 <= 1 /\ 0 <= f2 <= 1 /\ 0 <= f3 <= 1 /\ 0 <= f4 <= 1 /\ 0 <= f5 <= 1
    /\ munch [(P + 8, P + 16); (SP - 32, SP); (SP + 8, SP + 24)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SP
    /\ rw_cells usegs m' SP [CB 8 j0; C8 (Z_to_bv 64 (hp_streams (huf_draws pl (zlen pl))));
                             C8 (Z_to_bv 64 (hp_symbols (huf_draws pl (zlen pl))));
                             C8 x11; C8 x10; C8 x9; C8 x8; C8 x7; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra]
    /\ prod_at m' P D (hp_rest (huf_draws pl (zlen pl))).

(* [comment removed for export] *)
Lemma snez01 : forall f, 0 <= f <= 1 -> Z.b2z (0 <? f) = f.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_draws ()) [] "p'0h02Hfh11fh24__x1h31Hh41Nh57__arithh64__ffh78__varmaph85__with91ei001eh:1si011si021np;2p;1p;3p;7p;4p;6p;8g00E2j21Tg000Pj1OTg005lj28Tg00ENj2?Tg00Enj15Tg00FGR0j2ETg00Fgj26Tg00GDj17Tg005Rj30Tg001Nj29Tg00Gaj7=Tg00H?j1<Tg0000j1NTg00H_j2MTg00I=j1LTg00I[j1ITg00JFj2HTg00Jij2;Tg00KLj42Tg00L7j6DTg00L[j1CTg00M=j7BTg00Maj2ATg00NCj2FTg00Noj3GTg00ONj4@Tg00P@j6JTg00P\j7KTg00Q@j8>Tg00;lR1f0R2g00;NR330p=4f1R4g00QdR5g00RCR6P6g00RcR7P2g00SCFKp=3f3R8P5P6P6P7f2R9P4P2G>p=:1132g00DMR:#OR;,12'8R<1?43%44R=%5='EP0%49R0%501638#7=018P2%48R0P1P31634#7=014^0<X111133113;'81913W0f4R<P2P8F=W9P2O1%50g00ScR0#<%N01M14%L1%I1R0P0P5P6P6P7P11H1:R:g00TOR81;13R=C2,30ED%C6R>P0P0P5P6P6P7P1P=g00U6R=P:C2,30P1P:P=1;1;R=C2,30FBP>P1P=P8P:C2,30C:C:1A07P2P9g00U]R0g00V=R7'91F29=007dAG134C@b6b7b8X21%42g00V][1134114;'8A01;9[[^21P2f5R9P4P<O3b5A01;<P1P;1632#7=012X11191;P9P2EJb3W4P2O1n200110100021010010102b:W0X11o"). Qed.

Lemma carry : forall Wc (D SP : Z) (bs : list byte) (cs : list cell) W0 m mc m',
  munch Wc mc m' -> wmono usegs mc m' ->
  munch W0 m mc -> wmono usegs m mc -> sub_fp Wc W0 ->
  rw_cells usegs mc SP cs -> disjoint_from Wc SP (Z.of_nat (cells_size cs)) ->
  bytes_at usegs mc D bs -> disjoint_from Wc D (Z.of_nat (length bs)) ->
  munch W0 m m' /\ wmono usegs m m' /\ rw_cells usegs m' SP cs /\ bytes_at usegs m' D bs.
Proof.
  intros Wc D SP bs cs W0 m mc m' MU1 WM1 MU WM SF FR DF PB DB.
  split; [eapply munch_trans; [exact MU| eapply munch_weaken; [exact SF| exact MU1]]|].
  split; [eapply wmono_trans; [exact WM| exact WM1]|].
  split; [eapply rw_cells_transport; [exact FR| exact MU1| exact WM1| exact DF]|].
  eapply bytes_at_transport; [exact PB| exact MU1| exact DB].
Qed.

Ltac subfp := unfold sub_fp; intros ?x; cbn; intuition lia.

Ltac after_call ret MU WM FR PLB PR MI ST :=
  let ms := fresh "ms" in let PO := fresh "PO" in let mn := fresh "mc" in
  let MUn := fresh "MUn" in let WMn := fresh "WMn" in let MIn := fresh "MIn" in let STn := fresh "STn" in
  let PRn := fresh "PRn" in let MU' := fresh "MUx" in let WM' := fresh "WMx" in let FR' := fresh "FRx" in
  let PLB' := fresh "PLBx" in
  intros ms PO;
  destruct PO as (?u0 & ?u1 & ?u2 & ?b1 & ?b2 & ?b3 & ?b4 & ?b5 & ?b6 & ?b7 & ?u3 & ?u4 & ?u5 & ?u6 & mn & -> & MUn & WMn & MIn & STn & PRn);
  destruct (carry _ _ _ _ _ _ _ _ _ MUn WMn MU WM ltac:(subfp) FR ltac:(cbn; lia) PLB
             ltac:(rewrite length_map; cbn; lia)) as (MU' & WM' & FR' & PLB');
  unfold prod_at in PRn; clear MU WM FR PLB MUn WMn PR MI ST;
  rename MU' into MU; rename WM' into WM; rename FR' into FR; rename PLB' into PLB;
  rename PRn into PR; rename MIn into MI; rename STn into ST;
  replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

Ltac call_i32 I32R vSP vlo vP vD vpl vsz :=
  eapply evt_cut;
  [ eapply I32R with (SPV := vSP) (lo := vlo) (P := vP) (D := vD) (pl := vpl) (size := vsz) (mn := 0) (mx := 1);
    first [ reflexivity | eassumption | split; eassumption | lia ] | ].

Ltac call_u32 U32R vSP vlo vP vD vpl vsz vmn vmx :=
  eapply evt_cut;
  [ eapply U32R with (SPV := vSP) (lo := vlo) (P := vP) (D := vD) (pl := vpl) (size := vsz) (mn := vmn) (mx := vmx);
    first [ reflexivity | eassumption | split; eassumption | lia ] | ].

Section PhaseB.
  Hypothesis U32R : prod_u32r_stmt.
  Hypothesis I32R : prod_i32r_stmt.

  Theorem phaseB_proof :
    forall (ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra : word) (j : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP P D : Z) (pl : list Z) (lo : Z),
      prod_at m P D (zlen pl) -> payload_at m D pl -> zlen pl < 2^26 ->
      stk usegs m lo SP -> lo <= SP - 32 -> 0 <= SP -> SP + 128 < 2^64 ->
      P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) ->
      0 < P -> P mod 8 = 0 -> 0 < D -> SP mod 16 = 0 ->
      mem_inv usegs m ->
      rw_cells usegs m SP [CB 24 j; C8 x11; C8 x10; C8 x9; C8 x8; C8 x7; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra] ->
      evt usegs (hB_post gp tp s6 F fc SP P D pl lo m x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra)
          (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 (Z_to_bv 64 D) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
                   s2 s3 (Z_to_bv 64 (zlen pl)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 PC_HB_ENTRY) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros PR PL PLEN ST LO SP0 SPH PLO DLO DP P0 P8 D0 SPA MI FR.
  destruct PL as [PLB PLR].
  destruct (huf_draws_unfold pl (zlen pl)) as (streams & z1 & symbols & z2 & f1 & z3 & f2 & z4 & f3 & z5 & f4 & z6 & f5 & z7
    & dbs & z8 & mtl & z9 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & EH).
  pose proof (int32Range_01 pl (zlen pl) ltac:(lia)) as B1. rewrite E1 in B1.
  pose proof (int32Range_01 pl z1 ltac:(lia)) as B2. rewrite E2 in B2.
  pose proof (int32Range_01 pl z2 ltac:(lia)) as B3. rewrite E3 in B3.
  pose proof (int32Range_01 pl z3 ltac:(lia)) as B4. rewrite E4 in B4.
  pose proof (int32Range_01 pl z4 ltac:(lia)) as B5. rewrite E5 in B5.
  pose proof (int32Range_01 pl z5 ltac:(lia)) as B6. rewrite E6 in B6.
  pose proof (int32Range_01 pl z6 ltac:(lia)) as B7. rewrite E7 in B7.
  pose proof (uint32Range_range pl z7 0 (8 * zlen pl + 500) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B8. rewrite E8 in B8.
  pose proof (uint32Range_range pl z8 1 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B9. rewrite E9 in B9.
  pose proof (munch_refl [(P + 8, P + 16); (SP - 32, SP); (SP + 8, SP + 24)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold prod_i32r_stmt in I32R. unfold prod_u32r_stmt in U32R.
  unfold prod_at in PR.
  unfold PC_HB_ENTRY. do 5 zstep.
  call_i32 I32R SP lo P D pl (zlen pl). after_call 0x13298 MU WM FR PLB PR MI ST. rewrite E1 in *. cbn [fst snd] in *.
  do 5 zstep.
  call_i32 I32R SP lo P D pl z1. after_call 0x132ac MU WM FR PLB PR MI ST. rewrite E2 in *. cbn [fst snd] in *.
  do 5 zstep.
  call_i32 I32R SP lo P D pl z2. after_call 0x132c0 MU WM FR PLB PR MI ST. rewrite E3 in *. cbn [fst snd] in *.
  do 5 zstep.
  call_i32 I32R SP lo P D pl z3. after_call 0x132d4 MU WM FR PLB PR MI ST. rewrite E4 in *. cbn [fst snd] in *.
  do 5 zstep.
  call_i32 I32R SP lo P D pl z4. after_call 0x132e8 MU WM FR PLB PR MI ST. rewrite E5 in *. cbn [fst snd] in *.
  do 5 zstep.
  call_i32 I32R SP lo P D pl z5. after_call 0x132fc MU WM FR PLB PR MI ST. rewrite E6 in *. cbn [fst snd] in *.
  do 5 zstep.
  call_i32 I32R SP lo P D pl z6. after_call 0x13310 MU WM FR PLB PR MI ST. rewrite E7 in *. cbn [fst snd] in *.
  do 6 zstep.
  assert (A2 : bv_swrap 32 (Z.shiftl (zlen pl) 3 mod 18446744073709551616 + 500) = 8 * zlen pl + 500).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by lia. rewrite swrap32_small by lia. lia. }
  rewrite A2.
  call_u32 U32R SP lo P D pl z7 0 (8 * zlen pl + 500). after_call 0x13328 MU WM FR PLB PR MI ST. rewrite E8 in *. cbn [fst snd] in *.
  do 5 zstep.
  call_u32 U32R SP lo P D pl z8 1 12. after_call 0x1333c MU WM FR PLB PR MI ST. rewrite E9 in *. cbn [fst snd] in *.
  zstep. zstep. if_cases KS; zify_cond KS. { exfalso. lia. }
  do 7 zstep.
  replace (mtl mod 32) with mtl by (rewrite Z.mod_small; lia).
  assert (PM : 2 <= 2^mtl <= 4096).
  { split; [apply (Z.pow_le_mono_r 2 1 mtl)| apply (Z.pow_le_mono_r 2 mtl 12)]; lia. }
  rewrite Z.shiftl_1_l. rewrite swrap32_small by lia. rewrite (Z.mod_small (2^mtl)) by lia.
  rewrite (Z.shiftl_mul_pow2 (2^mtl) 2) by lia. change (2^2) with 4.
  replace (2^mtl * 4 + 4) with (DT_BYTES mtl) by (unfold DT_BYTES; lia).
  rewrite (Z.mod_small dbs) by lia.
  apply evt_done. unfold hB_post. rewrite EH. cbn [hp_mtl hp_dbuf hp_streams hp_symbols hp_rest].
  do 15 eexists. exists f1, f2, f3, f4, f5, (firstn 8 j), mc5. split; [reflexivity|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact PR].
Qed.
End PhaseB.

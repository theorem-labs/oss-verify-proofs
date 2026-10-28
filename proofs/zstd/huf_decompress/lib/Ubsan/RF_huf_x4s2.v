(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface
  RF_huf_x4s RF_huf_x4s31 RF_huf_x4s31b RF_huf_x4s32 RF_huf_x4s32b RF_huf_x4s33 RF_huf_x4s33b RF_huf_x4s34 RF_huf_x4s34b RF_huf_x4s3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x4s2 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Tac>rw_cells_mergeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC47Corelib4Init9Datatypes3appK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list02I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s4SPL3C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI47Corelib4Init5Logic2eq00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K47Corelib4Init5Logic2eq01K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s7x4s_errC56Stdlib6ZArith6BinInt1Z6ltb_geI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr08C56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s7x4s_epiC5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s38x4s3_allC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3BD4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepK47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics5Riscv3Sem4core00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_lit".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Lemma spl1_to_spl3 : forall segs m A j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 : word),
  rw_cells segs m A [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88;
                     C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 w136; C8 w144; C8 w152] ->
  exists j0' j72 j88 j104,
  rw_cells segs m A [CB 24 j0'; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; CB 8 j72; C8 w80; CB 8 j88; C8 w96;
                     CB 16 j104; C8 w120; C8 w128; C8 w136; C8 w144; C8 w152].
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4s2 ()) [] "h01Hh14j104h23j88h33j72h41Ah52j0h63j0'h71mh84segsh94w104h:4w112h;4w120h<4w128h=4w136h>4w144h?4w152h@3w16hA3w24hB3w32hC3w40hD3w48hE3w56hF3w64hG3w72hH2w8hI3w80hJ3w88hK3w96p;1p;4p;7p;3p;2p10000p4p7210p1000\p4p710p8g001:j1FTg001Zj1<Tg002?j1ETg002]j1DTg003@j1ITg003bj10Tg004Wj1GTg0057j46Tg005mj7=Tg006hj1ATg007aj18Tg008[j3?Tg0098j23Tg009mj29Tg00:Gj4@Tg00:aj1>Tg00;@j32Tf0R0#>#>#>#>p=:g00;`R1f1R2;20p=5f4R3f3R4f2R5A2120521521521p=11334A21209215521p=B1352=210p=;A21209215p=4f7R6f6R7f5R8521#8'3A2120921592149213521p=7%80,32p=HA2120#8p=Cg00<U#Fg00=T#<#<#<R9#<#<#<#E#DR:%E9#DR9#I[g00>9%F9R9fFR;fER<fDR=g00>W#:#:R>fCR?fB#0R@fA#0RAf@#0RBf?#0RCf>#0RDf=#0REf<#0RFf;#0RGf:#0RHf9#0RIf8#0RJ%06R6%07R7%08R8%03R3%04RK%05RL%02RM%00%G1RN'5D1D1D1D1DBC6fGROP;P<PNP>P=%0?R?P@PNDBRPPAPBPCPDPEPFPGPHPIPJP6P7P8P3PKPL15MND1D1D1D1RMP0F=POP;P<%AP%8P;;M9?1NC6fHRMPOP;%:>#:RP#:#:RQ13><%0=R=?4?NP@PAPBPC15ENRR,5DG7RS15FNRTPGPHPIPJP6P7P8P3A4KLND1D1RLP0F=PMPOP;%AT%8TRU;;L9?1SC6fIRSPMPOPQ13>;%0<R<?4=NP?P@PAPB%8RRR=;>T94CDG7RT15GNRLPHPIPJP6P7P8P3PKPND1D1RKP0F=PSPMPO%AL%8L;;K9?1TC6fJRTPSPMPQ13>O%0;R;?4<NP=P?P@PAPBPC15DN,H>RKPEA;>ULD1G7RLA4HINRUPJP6P7P8153ND1R3P0F=PTPSPM%AU%8U;;39?1LC6P9fOfNRLfMR1PQP4%0SR4%0MR3%0OROP;P<P=13>5R5P@13>2R2PB13P0RPPEPFPGPUD1D1D1DBC6X19,99X29,99X39,99X6913>MA4O;N'CP9PLP1fLRLPQfKRM,3>%0T?44NP3POP;P<P=P?P5PAP2PCPPPFPGPHPIPJPND1D1D1G7C6X19,99X29,99X391CCNP9P1PLPMPQ13>TA443NPOP;P<P=P>PAPNPBP2PDPPPGPHPIPJ156ND1G794?@G7C6X19,99X29PRP9PLPMPTPQ13>SA43ONP;P<P=P?P>PBPNPCPKPEPPPHPIPJP6157ND1G794@AG7C6X1915HN,CGP0C@C@C@C@b0b0b0b0W0X?:X>:X=:X<:X;:X::X9:XK:XJ:XI:XG:XF:XE:XD:XC:XB:XA:X@:XH:W5W4W7W8o"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section X4S2.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DP : 0 < dcap -> 8 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 2 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 2 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation XB l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).
  Notation X4F' mm spl b1 b2 b3 b4 := (X4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl b1 b2 b3 b4).

  Variables (L1 L2 L3 L4 SEG Q2 Q3 : Z).
  Notation O2 := (6 + L1). Notation O3 := (6 + L1 + L2). Notation O4 := (6 + L1 + L2 + L3).
  Hypothesis HL : 1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n.
  Hypothesis HQ : 0 < SEG <= Q2 /\ Q2 <= Q3 /\ Q3 <= dcap /\ 4 <= dcap.
  Notation A3 l := (XB l L1 L2 L3 L4 SEG Q2 Q3 HL HQ) (only parsing).

  (* [comment removed for export] *)
  Lemma x4s2_chk : forall q1 q2 q3 q4 pt1 pt2 pt3 pt4 c1 b1 c2 b2 c3 b3 c4 b4 v8 v16 v24 v32 v40 v48 v56 v128 mm j0 j96 j120
                          jp1 jp2 jp3 jp4 (xra t0 t1 x8 x9 a0 a1 a2 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word),
    X4F' mm (SPL3 v8 v16 v24 v32 v40 v48 v56 (DST + dcap) (DST + SEG) (DST + dcap - 3) (DST + Q2) dcap DST v128 j0 j96 j120)
            (BD4 c1 b1 (SS + 6 + pt1) (SS + 6) jp1) (BD4 c2 b2 (SS + O2 + pt2) (SS + O2) jp2)
            (BD4 c3 b3 (SS + O3 + pt3) (SS + O3) jp3) (BD4 c4 b4 (SS + O4 + pt4) (SS + O4) jp4) ->
    0 <= q1 -> 0 <= q2 -> 0 <= q3 -> 0 <= q4 <= dcap ->
    DST + q1 < 2^64 -> DST + q2 < 2^64 -> DST + q3 < 2^64 ->
    0 <= pt1 -> (pt1 = 0 \/ pt1 + 8 <= L1) -> 0 <= pt2 -> (pt2 = 0 \/ pt2 + 8 <= L2) ->
    0 <= pt3 -> (pt3 = 0 \/ pt3 + 8 <= L3) -> 0 <= pt4 -> (pt4 = 0 \/ pt4 + 8 <= L4) ->
    0 <= b1 < 2^31 -> 0 <= b2 < 2^31 -> 0 <= b3 < 2^31 -> 0 <= b4 < 2^31 ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 (Z_to_bv 64 DST) x8 x9 a0 a1 a2 (Z_to_bv 64 (DST + SEG))
                           a4 a5 a6 a7 (Z_to_bv 64 (DST + q1)) (Z_to_bv 64 (tl + 256 * mtl)) x20 (Z_to_bv 64 (DST + q4))
                           (Z_to_bv 64 (DST + q3)) (Z_to_bv 64 (DST + q2)) (Z_to_bv 64 (DST + Q3)) (Z_to_bv 64 (DT + 4))
                           (Z_to_bv 64 SEG) (Z_to_bv 64 (DST + dcap)) t3 t4 t5 t6)
                       F (Z_to_bv 64 101628) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros XF Q1 Q2' Q3' Q4 W1 W2 W3 HP1 HP1' HP2 HP2' HP3 HP3' HP4 HP4' HB1 HB2 HB3 HB4.
    pose proof XF as XF0.
    destruct XF as (BUF & SRC & CBS & ST & SPC & L0 & B1 & L1' & JJ & B4 & L4' & B3 & L3' & B2 & L2' & FR & MI & MU & WM).
    unfold SPL3 in SPC.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    zstep. if_cases K1; zify_cond K1.
    { zto 98924. eapply (XB x4s_epi); exact XF0. }
    zstep. zstep. if_cases K2; zify_cond K2.
    { zto 98924. eapply (XB x4s_epi); exact XF0. }
    zstep. if_cases K3; zify_cond K3.
    { zto 98924. eapply (XB x4s_epi); exact XF0. }
    eapply (A3 x4s3_all); [exact XF0 | first [assumption | lia] ..].
  Qed.

End X4S2.
End CANSEC1.

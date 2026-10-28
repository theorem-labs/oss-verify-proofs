(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_x4s RF_huf_y4s_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_y4s () := "K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z=shiftr_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t03C5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK47Corelib4Init9Datatypes3nat02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextI4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface=HUF_DEC_STACKc5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s7y4s_stkc5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s8y4s_epi0C5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtc5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s7y4s_epiC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5instr03c5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s4SPLYC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3BD4C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_xorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_xorK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC56Stdlib6ZArith6BinInt1Z4lxorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC56Stdlib6ZArith6BinInt1Z3lorC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge7zr_wordC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions8bv_swrapC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge7zr_lxorK4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Definition SPLY (v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 : Z) (j0 : list byte) : list cell :=
  [CB 24 j0; C8 (Z_to_bv 64 v24); C8 (Z_to_bv 64 v32); C8 (Z_to_bv 64 v40); C8 (Z_to_bv 64 v48); C8 (Z_to_bv 64 v56);
   C8 (Z_to_bv 64 v64); C8 (Z_to_bv 64 v72); C8 (Z_to_bv 64 v80); C8 (Z_to_bv 64 v88); C8 (Z_to_bv 64 v96);
   C8 (Z_to_bv 64 v104); C8 (Z_to_bv 64 v112); C8 (Z_to_bv 64 v120); C8 (Z_to_bv 64 v128); C8 (Z_to_bv 64 v136);
   C8 (Z_to_bv 64 v144); C8 (Z_to_bv 64 v152)].

(* [comment removed for export] *)
Lemma y4_idx_bound : forall tl c b sh, 1 <= tl <= 12 -> 0 <= c < 2^64 -> sh = 64 - tl ->
  0 <= (c ≪ b mod 18446744073709551616) ≫ sh < 2^tl.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4s ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h51ah61Hh71bh84__p1h91zh:1nh;2shh<2Hch=2TLh>1ch?2tlp;1p;2p;3p;4p;6p;5p;7p;8g0000j1;Tg000Nj25Tg000jj1UTg001OR0j29Tg001jj10Tg002Oj27Tg002lj22Tg003Hj2=Tg003ej3>Tg004?j2@Tg004_j2<Tg005?j2:Tg005_j2\Tg006Fj3ZTg006mj1YTg007Mj1XTg007mj1WTg008Kj1VTg008ij1STg009Tj26Tg00:7j4?Tg00:bj2QTg00;Dj2PTg00;^j2OTg00<Jj3NTg00<ij4LTg00=[j2KTg00>8j2JTg00>Vj6MTg00?:j2ITg00?]j1HTg00@?j3RTg00@bj4GTg00AJj2ATg00Agj3dTg00BJj6FTg00Bfj2cTg00CCj5bTg00Cfj5aTg00DRj3`Tg00E;j6DTg00EYj4[Tg00F4j7]Tg00FXj7^Tg00G<j8_Tf0R1#0#0p=Bg00G`R2/51p=1%01#0#0#0p=T%01#0#0#0#0#0#0#0p=4f1R3g00H>R4g00H]R5P5g00I=R6P1g00I]F]p=3g00J=R7P3g00J[P1C?p=8f2R8P4P5P5P6P3P1F^p=Cf3R9P4P5P5P6P8P3P1G_p=Eg00KBR:#;R;/59%U:#B#;R<,59'9%19%0:R=#;R>%0=#TR=#;R?'7R@,29'9f5RA,=?9>78P7f6RB,=?RC1@BA%B=#4#4#4#4#4#4#4#;R='<RD/:1RE#1f7RF,7>RG,2E'9X;7f4,@A/<=RA/:CRE#117>BRH,2EP01:31#1%18RI[%13RJ1:83#1[RK1:98#1\I1\31P1n2001000000120000000X:7X57PK^:7^57P1PD1=?FRK1221RIP01<83RL#1RM12L3RL1<98RN#1AZ831ROP3n2001000000120000000UX77X57PM\I^77^57P11@FBRPP=g00KgRQ#YRR%XQRQ%W7RS%V7RT%S7RUP71672RVg00LSRW167=C?'31QU6RXP1P8g00M:RYg00MZRZ'P1O18=>YZdAN723CLRZb1b2b3122=P1b0O3b6O3b6P717>CRY,KA121GX97PAPYPHP>PCPRPQPSPTP7PVPW167>C?,3UPXPZb1b2b3122>P1b0R2p-0RWPRPQ1J73RGPTPUPUP4P5P5P6P9EMR61I7:R:167<'8,3U5CU%H5R5167?R4=R7:R[,8V,3UCEPXPZb1b2b3X47W8151<,931=?3#1[^47^8WP115;FPFP9O3b0R\CGP71ACBR],7>12D1X97PRPQPGPTP7P4g00N:Ad7[:C?,3UPXPZb1b2b3X471=?1/A19>7?^47P1PFO1b0A>7?]P7P?1<P=17>1'2X97P0PMPL12N8POP1n2001000000120000000VIX77X57PL\I^77^57P1PPP@P>P?P2PRPQPSPT18V4,3UPXPZb1b2b3%1?P1b0CGO3b61AKFP1EFb61cYHP>PCPBP\PRPQPGPTPU167;/8:,3U=CU6P518V:,3UCEPXPZb1b2b3X47X8W15;1/93PJ[^47^8WP115F<PFP9O3b0DbEFDaPEA`AC\EDC[P9P1EDW6W<W=X;7X77X>7X?7o"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section Y4SB.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DP : 0 < dcap -> 8 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 4 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 4 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation Y4F' mm spl b4 b3 b2 b1 := (Y4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl b4 b3 b2 b1).

  (* [comment removed for export] *)
  Lemma y4s_stk : forall mm spl b4 b3 b2 b1, Y4F' mm spl b4 b3 b2 b1 -> stk usegs mm lo (SP + -104).
  Proof using All.
    intros mm spl b4 b3 b2 b1 (BUF & SRC & CBS & ST & SPC & L0 & B4 & L4 & B3 & L3 & B2 & L2 & B1 & L1 & SV & (jl & JL) & FR & MI & MU & WM).
    destruct SV as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & SV).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    release_frame SPC ST (SP + -776).
    release_frame B4 ST (SP + -736).
    release_frame B3 ST (SP + -696).
    release_frame B2 ST (SP + -656).
    release_frame B1 ST (SP + -616).
    release_frame SV ST (SP + -512).
    release_frame JL ST (SP + -104).
    exact ST.
  Qed.

  (* [comment removed for export] *)
  Lemma y4s_epi0 : forall mm (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    stk usegs mm lo (SP + -104) -> rw_cells usegs mm (SP + -104) FRS ->
    mem_inv usegs mm -> munch DW m0 mm -> wmono usegs m0 mm ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x16d70) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until xra. intros ST FR MI MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    do 14 zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  Lemma y4s_epi : forall mm spl b4 b3 b2 b1 (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    Y4F' mm spl b4 b3 b2 b1 ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -912)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x1dc54) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until xra. intros XF.
    pose proof (y4s_stk _ _ _ _ _ _ XF) as STK.
    destruct XF as (BUF & SRC & CBS & ST & SPC & L0 & B4 & L4 & B3 & L3 & B2 & L2 & B1 & L1 & SV & (jl & JL) & FR & MI & MU & WM).
    destruct SV as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & SV).
    unfold PY4_RET in SV.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    do 15 zstep.
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end).
    zto 0x16d70.
    eapply y4s_epi0; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma y4s_err : forall mm spl b4 b3 b2 b1 (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    Y4F' mm spl b4 b3 b2 b1 ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -912)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x1dc50) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until xra. intros XF.
    zstep.
    eapply y4s_epi; exact XF.
  Qed.

  (* [comment removed for export] *)
  Lemma y4s_m1 : forall mm spl b4 b3 b2 b1 (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    Y4F' mm spl b4 b3 b2 b1 ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -912)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x1dc4c) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until xra. intros XF.
    zstep. zstep.
    eapply y4s_epi; exact XF.
  Qed.

  (* [comment removed for export] *)
  Lemma y4s_end : forall mm spl c4 bc4 p4 st4 j4 c3 bc3 p3 st3 j3 c2 bc2 p2 st2 j2 c1 bc1 p1 st1 j1
      (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    Y4F' mm spl (BD4 c4 bc4 p4 st4 j4) (BD4 c3 bc3 p3 st3 j3) (BD4 c2 bc2 p2 st2 j2) (BD4 c1 bc1 p1 st1 j1) ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -912)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x1dbe0) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until xra. intros XF.
    pose proof XF as XF0.
    destruct XF as (BUF & SRC & CBS & ST & SPC & L0 & B4 & L4 & B3 & L3 & B2 & L2 & B1 & L1 & SV & JL & FR & MI & MU & WM).
    unfold BD4 in B1, B2, B3, B4.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    zto 0x1dc48.
    zstep. if_cases K.
    all: zto 0x1dc54.
    all: eapply y4s_epi; exact XF0.
  Qed.

End Y4SB.
End CANSEC1.

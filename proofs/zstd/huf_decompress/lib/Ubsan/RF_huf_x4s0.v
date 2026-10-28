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
  RF_huf_x4s RF_huf_x4s01s RF_huf_x4s02s RF_huf_x4s03s RF_huf_x4s04 RF_huf_x4s01 RF_huf_x4s02.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require RF_huf_bitinit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x4s0 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit=lor_shift_addK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8byte_litK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s04X4S0C47Corelib5Lists7ListDef3mapC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2ex00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_cell_okC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiI4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s8x4s_epi0C56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit9byte_ZnthC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_fa_iface6jt_lenC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z;div_str_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK47Corelib4Init5Logic3and01C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=bytes_at_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit=le2_two_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx16K4ELinuxProcessSemantics5Riscv5Instr5instr06C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le2C5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC47Corelib4Init9Datatypes3appC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem:zx16_shortC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_x4s08le16_lorC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_defaultK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5msize02K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Lemma le16_lor : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.lor (bv_unsigned (Z_to_bv 8 b1) ≪ 8 mod 18446744073709551616) (bv_unsigned (Z_to_bv 8 b0)) = b0 + 256 * b1.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4s0 ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51zh64__p1h74__x2h82H0h92H1h:2b0h;2b1p;2p;1p;4p;3p;6p;7p;8p10000p4p7210g000\R0p4p710p8g001:j2=Tg001Vj10Tg002;j1?Tg002Yj28Tg0035j26Tg003Pj2DTg0040j2>Tg004Pj1VTg004nj2ATg005Tj2@Tg006>j27Tg006[j2:Tg0078j2<Tg007Uj2dTg0082j1`Tg008Rj1_Tg0092j2LTg009Pj1]Tg009nj4[Tg00:Lj1ZTg00:jj1YTg00;Uj2KTg00<8j24Tg00<[j3XTg00=>j3CTg00=aj3JTg00>Dj4ETg00>oj2UTg00?Qj2TTg00?kj2STg00@Wj3ITg00A1j3RTg00APj4QTg00BBj1kTg00Bdj6jTg00CHj6iTP0j65Tg00DLj2hTg00E5j1HTg00ETj2FTg00F=j3eTg00Ffj3OTg00GOj2MTg00H;j2cTg00Hgj3NTg00IGj3aTg00Ijj3bTg00JSj2PTg00KPj7fTg00L4j7^Tg00LXj8gTf0R0#0#0p=\%00#0#0#0p=W%00#0#0#0#0#0#0#0p=1g00M<R1f1R2;I0p=3P2g00MZR3g00N9R4P4g00NYR5P0g00O9Ffp=2P1P2g00OYP0CEp=GP1P2g00P@P0CEp=Bf2R6P3P4P4P5P2P0F^p=;f3R7P3P4P4P5P6P2P0Ggp=9g00PgR8/=2R9g00QER:#0R;#\R<#0#WR=#?R>,82'6R?P1P6%?<R@,D0%1=#1#1#1#1#1#1#?R='>%V<R<f4RA,A<'@'71:>7,<ARB'3X51P1P71D7@/>=/70/3BX51P1%?;RC/d@RD,:6RE1>0=/7A/3BX51P1PE170A/3BX51P11<7E130BX51g00QjRB#`RF%_BRGP11L16P2%]1RHC[%Z1RI%Y1RJP11K1:R:1K1;R;141C=X1<RC5C15J1g00RV141>RK=C1;9J1:CE'21UJ5R;P0P6g00S=RLg00S]RM'T1S06=ILMdAR182CQRMb2b3b4X01X711:2DRL,<01:>2,<0'3^01^71P0P7PAO2b117E7P6P@P7PFPGPHPI1418RH141@'G,2JP;PMb2b3b41=8@P0b1RNPFPG1L12ROPIPJ1GH:,2JRP1B:K,2J5;JRK%k4RQ1B:C,2J9;JPC9P;PMb2b3b4X011=80RR180>'6RS182D,69[^01P0PAP6O2RAb1p-0RDPFPGPOPIPJPJP3P4P4P5P7Ej9;JPPQPPC9P;PMb2b3b4X01W616R2P9[^01^6DP0187>P7P2O3b1EiE51>E=1h1>g00T=R>#HRD,F15e11F1>R>5O1g00T\R9'M%HD#H,F19O1>/M9,c>=NBF5NBPGPOPIPJPKPQAC1:CRC,GH,2J141=,BC,2J5;JC9P;PMb2b3b4X011=8L18L='6\S^01P0P7P2O2R2b19aE=E51D6@Ab6@NE51A<7,@<PFPGPOPIPJPKPQPKC9P;PMb2b3b4X01RMP?\S^01RSPAb1,P7E51A<6,@<PMPSP2b1,P6E5X9?W8X;1X:1o"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section X4S0.
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
  Hypothesis DTA : DT mod 4 = 0.

  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation X4F' mm spl bd1 bd2 bd3 bd4 :=
    (X4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl bd1 bd2 bd3 bd4).
  Notation J1 := (Znth 0 src + 256 * Znth 1 src).
  Notation J2 := (Znth 2 src + 256 * Znth 3 src).
  Notation J3 := (Znth 4 src + 256 * Znth 5 src).
  Notation SG := ((dcap + 3) ≫ 2).
  Notation BS1 := (firstn (Z.to_nat J1) (skipn (Z.to_nat 6) src)).
  Notation BS2 := (firstn (Z.to_nat J2) (skipn (Z.to_nat (6 + J1)) src)).
  Notation BS3 := (firstn (Z.to_nat J3) (skipn (Z.to_nat (6 + J1 + J2)) src)).
  Notation BS4 := (skipn (Z.to_nat (6 + J1 + J2 + J3)) src).
  Notation BDC S d jp := [C8 (Z_to_bv 64 (bd_cont d)); C4 (Z_to_bv 64 (bd_bits d)); CB 4 jp; C8 (Z_to_bv 64 (S + bd_ptr d));
                          C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))].
  Notation XB0 l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                       TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).

  (* [comment removed for export] *)
  Definition X4S0 (mm : fmem) : Prop :=
    (exists buf, u8arr usegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at usegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at usegs mm (DT + 4) cbs
    /\ bytes_at usegs mm DT [Z_to_bv 8 mtl; Z_to_bv 8 0; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ stk usegs mm lo (SP + -104)
    /\ rw_cells usegs mm (SP + -104) FRS
    /\ mem_inv usegs mm /\ munch DW m0 mm /\ wmono usegs m0 mm.

  (* [comment removed for export] *)
  Hypothesis LOOPK : forall (L1 L2 L3 L4 SEG : Z),
    1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n ->
    0 < SEG /\ 3 * SEG <= dcap /\ 4 <= dcap ->
    forall q p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 mm j0 j96 j120 jp1 jp2 jp3 jp4
           (t2 x8 x9 a0 a2 a4 x21 x22 x27 t4 : word),
    X4F' mm (SPL3 (DST + 3 * SEG) (tl + 256 * mtl) (SS + (6 + L1 + L2 + L3) + 8) (SS + (6 + L1 + L2) + 8) (SS + (6 + L1) + 8)
                  (3 * SEG) (2 * SEG) (DST + dcap) (DST + SEG) (DST + dcap - 3) (DST + 2 * SEG) dcap DST
                  (SS + (6 + L1 + L2 + L3) + p4) j0 j96 j120)
            (BD4 c1 b1 (SS + 6 + p1) (SS + 6) jp1) (BD4 c2 b2 (SS + (6 + L1) + p2) (SS + (6 + L1)) jp2)
            (BD4 c3 b3 (SS + (6 + L1 + L2) + p3) (SS + (6 + L1 + L2)) jp3)
            (BD4 c4 b4 (SS + (6 + L1 + L2 + L3) + p4) (SS + (6 + L1 + L2 + L3)) jp4) ->
    0 <= q -> q + 3 * SEG + 4 <= dcap ->
    (0 <= p1 /\ (p1 = 0 \/ p1 + 8 <= L1) /\ 0 <= b1 <= 64 /\ (8 <= p1 -> b1 <= 8)) ->
    (0 <= p2 /\ (p2 = 0 \/ p2 + 8 <= L2) /\ 0 <= b2 <= 64 /\ (8 <= p2 -> b2 <= 8)) ->
    (0 <= p3 /\ (p3 = 0 \/ p3 + 8 <= L3) /\ 0 <= b3 <= 64 /\ (8 <= p3 -> b3 <= 8)) ->
    (0 <= p4 /\ (p4 = 0 \/ p4 + 8 <= L4) /\ 0 <= b4 <= 64 /\ (8 <= p4 -> b4 <= 8)) ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -512)) gp tp
                           (Z_to_bv 64 (SS + (6 + L1) + p2)) (Z_to_bv 64 (SS + (6 + L1 + L2) + p3)) t2 x8 x9
                           a0 (Z_to_bv 64 (Z.lxor (DT + 4) (2^64 - 1))) a2 (Z_to_bv 64 b1) a4
                           (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (2^64 - 1))
                           (Z_to_bv 64 b4) (Z_to_bv 64 b3) (Z_to_bv 64 c2) x21 x22 (Z_to_bv 64 c4)
                           (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SEG) x27
                           (Z_to_bv 64 c1) t4 (Z_to_bv 64 (SS + 6 + p1)) (Z_to_bv 64 c3))
                       F (Z_to_bv 64 0x17ad0) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Hypothesis CHK : forall (L1 L2 L3 L4 SEG Q2 Q3 : Z),
    1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n ->
    0 < SEG <= Q2 /\ Q2 <= Q3 /\ Q3 <= dcap /\ 4 <= dcap ->
    forall q1 q2 q3 q4 pt1 pt2 pt3 pt4 c1 b1 c2 b2 c3 b3 c4 b4 v8 v16 v24 v32 v40 v48 v56 v128 mm j0 j96 j120
           jp1 jp2 jp3 jp4 (xra t0 t1 x8 x9 a0 a1 a2 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word),
    X4F' mm (SPL3 v8 v16 v24 v32 v40 v48 v56 (DST + dcap) (DST + SEG) (DST + dcap - 3) (DST + Q2) dcap DST v128 j0 j96 j120)
            (BD4 c1 b1 (SS + 6 + pt1) (SS + 6) jp1) (BD4 c2 b2 (SS + (6 + L1) + pt2) (SS + (6 + L1)) jp2)
            (BD4 c3 b3 (SS + (6 + L1 + L2) + pt3) (SS + (6 + L1 + L2)) jp3)
            (BD4 c4 b4 (SS + (6 + L1 + L2 + L3) + pt4) (SS + (6 + L1 + L2 + L3)) jp4) ->
    0 <= q1 -> 0 <= q2 -> 0 <= q3 -> 0 <= q4 <= dcap ->
    DST + q1 < 2^64 -> DST + q2 < 2^64 -> DST + q3 < 2^64 ->
    0 <= pt1 -> (pt1 = 0 \/ pt1 + 8 <= L1) -> 0 <= pt2 -> (pt2 = 0 \/ pt2 + 8 <= L2) ->
    0 <= pt3 -> (pt3 = 0 \/ pt3 + 8 <= L3) -> 0 <= pt4 -> (pt4 = 0 \/ pt4 + 8 <= L4) ->
    0 <= b1 < 2^31 -> 0 <= b2 < 2^31 -> 0 <= b3 < 2^31 -> 0 <= b4 < 2^31 ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 (Z_to_bv 64 DST) x8 x9 a0 a1 a2 (Z_to_bv 64 (DST + SEG))
                           a4 a5 a6 a7 (Z_to_bv 64 (DST + q1)) (Z_to_bv 64 (tl + 256 * mtl)) x20 (Z_to_bv 64 (DST + q4))
                           (Z_to_bv 64 (DST + q3)) (Z_to_bv 64 (DST + q2)) (Z_to_bv 64 (DST + Q3)) (Z_to_bv 64 (DT + 4))
                           (Z_to_bv 64 SEG) (Z_to_bv 64 (DST + dcap)) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x18cfc) fc None mm (seg_rom usegs)).

  Notation XB1 l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                       TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47 DTA LOOPK) (only parsing).
  Notation XB2 l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                       TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47 DTA CHK) (only parsing).

  Ltac rel1 :=
    match goal with
    | STK : stk usegs ?m lo (bv_unsigned sp + ?h), FR : rw_cells usegs ?m (bv_unsigned sp + ?h) ?cs |- _ =>
        let hv := eval vm_compute in h in
        lazymatch eval vm_compute in (hv <? -104) with true => idtac end;
        let jk := fresh "jk" in let FR' := fresh "FR" in
        destruct (rw_cells_forget _ _ _ _ FR) as (jk & FR'); clear FR;
        let sz := eval vm_compute in (Z.of_nat (cells_size cs)) in
        let nh := eval vm_compute in (h + sz) in
        release_frame FR' STK (bv_unsigned sp + nh)
    end.
  Ltac err_exit :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18268) _ _ _ _) => zstep
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1826c) _ _ _ _) => idtac end;
    repeat rel1;
    eapply (XB0 x4s_epi0); eassumption.
  Ltac bytes_ok_t := lazymatch goal with
    | |- Forall _ (firstn _ _) => apply x4_bytes_sub; exact BYS
    | |- Forall _ (skipn _ _) => apply x4_bytes_tail; exact BYS end.
  Ltac bcall dd ss bb :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply RF_huf_bitinit.bit_init_proof with (D := dd) (S := ss) (bs := bb);
      [ eassumption | lia | lia
      | lazymatch goal with |- bytes_at _ _ _ (map _ (firstn _ _)) => eapply x4_src_sub_at; [eassumption|lia..]
                          | |- bytes_at _ _ _ (map _ (skipn _ _)) => eapply x4_src_tail_at; [eassumption|lia..] end
      | bytes_ok_t
      | lia | lia
      | first [ rewrite x4_sub_len by lia | rewrite x4_tail_len by lia ]; lia
      | first [ rewrite x4_sub_len by lia | rewrite x4_tail_len by lia ]; lia
      | rewrite unsigned_lit by lia; eassumption
      | rewrite unsigned_lit by lia; right; lia
      | eassumption
      | reflexivity
      | f_equal; lia
      | f_equal; first [ rewrite x4_sub_len by lia | rewrite x4_tail_len by lia ]; lia ]
    | post_call usegs mm ] end.
  Ltac post_ids :=
    lazymatch goal with PO : match init_dstream ?bs with _ => _ end |- _ =>
      let IDS := fresh "IDS" in destruct (init_dstream bs) eqn:IDS; try (exfalso; exact PO);
      [ let RET := fresh "RET" in let BZ := fresh "BZ" in let jp := fresh "jp" in let BD := fresh "BD" in
        destruct PO as (RET & BZ & jp & BD); rewrite RET; clear RET; unfold bitd_cells in BD
      | let RET := fresh "RET" in let jp := fresh "jp" in let BD := fresh "BD" in
        destruct PO as (RET & jp & BD); rewrite RET; clear RET;
        pose proof (init_dstream_err_range bs _ ltac:(bytes_ok_t) IDS) ]
    end.
  Ltac go := run; repeat (first [ err_exit | notchk; let K := fresh "K" in if_cases K; zify_cond K; try (kill K) ]; run).
  Ltac unmod := repeat match goal with
    | H : context [(DST + SG + SG + SG) mod ?M] |- _ => rewrite (Z.mod_small (DST + SG + SG + SG) M) in H by lia
    end.
  Ltac hand := lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x17ad0) _ _ _ _) => eapply (XB1 x4s01_loop)
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18cfc) _ _ _ _) => eapply (XB2 x4s02_chk)
    end.

  (* [comment removed for export] *)
  Lemma x4s0_core : forall mm (xra t0 t1 t2 x9 a0 a1 a2 a6 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    X4S0 mm ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 (Z_to_bv 64 SS) x9 a0 a1 a2 (Z_to_bv 64 n)
                           (Z_to_bv 64 DT) (Z_to_bv 64 DST) a6 (Z_to_bv 64 dcap)
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1785c) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros ((buf & BUFA & BUFL) & SRC & CBS & DTB & STK & FR & MI & MU & WM).
    pose proof (length_map (Z_to_bv 8) src) as LMAP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    carve_frame 408%nat STK.
    lazymatch goal with FRM : rw_cells _ _ (bv_unsigned sp + -512) [Cells.CB 408 ?jk] |- _ =>
      apply (rw_cells_split_CB usegs _ _ [] 408 jk [] [136; 40; 112; 40; 40; 40]%nat) in FRM; [|reflexivity];
      cbn [app mk_CB_cells] in FRM; peel FRM; peel FRM; peel FRM; peel FRM; peel FRM end.
    destruct TOK as (TL1 & _).
    unfold HUF_TABLELOG_MAX in TL1.
    go.
    all: bcall (bv_unsigned sp + -376) (SS + 6) (firstn (Z.to_nat J1) (skipn (Z.to_nat 6) src)).
    all: post_ids. all: rewrite ?x4_sub_len by lia. all: go.
    all: bcall (bv_unsigned sp + -144) (SS + 6 + J1) (firstn (Z.to_nat J2) (skipn (Z.to_nat (6 + J1)) src)).
    all: post_ids. all: rewrite ?x4_sub_len by lia. all: go.
    all: bcall (bv_unsigned sp + -184) (SS + 6 + J1 + J2) (firstn (Z.to_nat J3) (skipn (Z.to_nat (6 + J1 + J2)) src)).
    all: post_ids. all: rewrite ?x4_sub_len by lia. all: go.
    all: bcall (bv_unsigned sp + -224) (SS + 6 + J1 + J2 + J3) (skipn (Z.to_nat (6 + J1 + J2 + J3)) src).
    all: post_ids. all: rewrite ?x4_sub_len, ?x4_tail_len by lia. all: go.
    all: assert (SGE : SG = (dcap + 3) / 4) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    all: unmod.
    all: hand.
    all: first [ eassumption | lia ].
  Qed.
End X4S0.
End CANSEC1.

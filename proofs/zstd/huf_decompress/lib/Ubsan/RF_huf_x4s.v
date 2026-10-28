(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x4s () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission3Lib3Tac>rw_cells_mergeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z=shiftr_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201c5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t03C5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkK47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextI4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface=HUF_DEC_STACKc5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s7x4s_stkc5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s8x4s_epi0C5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtc5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s7x4s_epiC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litc5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3BD4C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_xorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_xorK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_xoriC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_xoriC56Stdlib6ZArith6BinInt1Z4lxorC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC56Stdlib6ZArith6BinInt1Z3lorC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_lorC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions8bv_swrapK4ELinuxProcessSemantics5Riscv5Instr5instr03C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge7zr_wordK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge7zr_lxorK4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4c5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s:x4s_end7d4K4ELinuxProcessSemantics5Riscv5Instr5msize03".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Lemma rw_cells_forget8 : forall segs m A pre v post,
  rw_cells segs m A (pre ++ C8 v :: post) -> rw_cells segs m A (pre ++ CB 8 (le8 v) :: post).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4s ()) [] "h01Ah11Hh21Mh31mh44posth53preh64segsh71vp;1p;3p;4p;6p;2p10000p4p7210p1000\p4p710p8g001:j17Tg001Zj10Tg002?j16Tg002]j15Tg003@j1=Tg003bj14Tg004Wj31Tg0057j32Tg005Tj43Tg006Jj1;Tg006jj68Tg007ej19Tg008^j1:Tg009Xj2<Tg00:M#7g00;L#0#0#0R0#0#0#0#6#5R1%60#5#=[g00<1g00<OR0#7R2f5R3f4R4f3R5f2R6f1R7#4f0R8510520C3f6R9P3P4P5%46%;0R:510R;P7E8P9P3P4A20;79205C3f7P9P3%45=10:R:#9%::'<=1069204C3[P8P7O1b2W1X42X71W5W0W3W6o"). Qed.

(* [comment removed for export] *)
Lemma x4_idx_bound : forall tl c b, 1 <= tl <= 12 -> 0 <= c < 2^64 ->
  0 <= (c ≪ (b mod 64) mod 18446744073709551616) ≫ ((64 - tl) mod 64) < 2^tl.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4s ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51ah61bh71Hh84__p1h91zh:1nh;2Hch<2TLh=1ch>2tlp;1p;2p;3p;4p;6p;5p;7p;8g00=Dj1<Tg00=bj25Tg00>>j1UTg00>cR0j26Tg001Zj10Tg00?>j29Tg00?[j21Tg00@7j2=Tg00@Tj23Tg00A4j2BTg00ATj2;Tg00B4j2dTg00B[j3\Tg006Jj1ZTg001:j1YTg00CBj1XTg00C`j1WTg00D>j1VTg00Dij28Tg00ELj2RTg00Enj2QTg00FHj2PTg00G4j3?Tg00GNj3OTg00Gmj4NTg00H_j2LTg00I<j2KTg00IZj6MTg00J>j2JTg00Jaj1ITg00KCj3STg00Kfj4HTg00LNj2DTg00Lkj3fTg00MNj4ATg00N9j6GTg00NUj2eTg00O2j5cTg00OUj5bTg00PAj3]Tg000\j6FTg00Pjj4[Tg00QEj3^Tg00Qhj7_Tg00RLj7`Tg00S0j8aTf0R1#0#0p=Eg00STR2/51p=2%01#0#0#0p=T%01#0#0#0#0#0#0#0p=7g00<1R3f1R4g00T2P1CAp=@P4g00TYR5g00U8R6P6g00UXR7P1g00V8F_p=4P3P4g00VXP1CAp=:f2R8P5P6P6P7P4P1F`p=>f3R9P5P6P6P7P8P4P1Gap=Cg00;LR:#<R;/58%U:#E#<R<,58'6%28R=%0:R>#<R?%0>#TR>#<R@'9RA,18'6P3f4RB,=@RC139@,BB%E>#7#7#7#7#7#7#7#<R>'3RD/;1RE#2f5RF,9?RG,1E'6X93138@,B9/3>RE/;CRH#219?BRI,1HP01;41#2P=[%24RJ1;84#2[RK1;98#2\=1d41P1n2001000000120000000X:3X53PK^:3^53P1PD1=@FRK1121R=P01384RL#2RM11L4RL1398RN#2A\841ROP4n2001000000120000000UX63X53PM\=^63^53P113B@,BFRPP>g00W?RQ#ZRR%YQRQ%X3RS%W3RT%V3RU1832RV183>'@'41RU7RWP1P8g00WkRXg00XKRY'Q1P18=?XYdAO324CNRYb2b3b4112>P1b1O3b7O3b7P319?CRX,LE111GX93PEPXPIP?PCPRPQPSPT183?,@V,4UPWPYb2b3b4112?P1b1R2p-0RGPRPQ1K34RZPTPUPUP5P6P6P7P9EMR91J3:R:183<':,4UR75>U%I6R6183@R5=S3:R[,:V,4UR\CCPWPYb2b3b4X03W8151<R],641=@4R^#2R_[^03^8GP115;FPFP8O3b1R`CHP31DCBRa,9?11D1X93PRPQPZPTP3P5g00XkAf3[:CA,4UPWPYb2b3b4X031=@1/D19?3@^03P1PFO1b1A?3@aP3P@13P>19?1'1X93P0PMPL11N8POP1n2001000000120000000V=X63X53PL\=^63^53P1PPPAP?P@P2PRPQPSPT1:V5,4UPWPYb2b3b4%2@P1b1CHO3b71DKFP1EGb71eXIP?PCPBP`PRPQPZPTPU183;/::,4URB=>U9P61:V:,4UCCPWPYb2b3b4X03X8G15;1R;/64PJ[^03^8GP115F<PFP8O3b1DcEGDbPHA]EC`EFC[13C@PRPQPZPTPUA>UB7P61@[5,4U9>U\CCPWPYb2b3b4X0316;]11^@,6_[^03P1PFP8O2b19^C@EFW;W<X63X=3X>3o"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section X4SB.
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

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition X4F (mm : fmem) (spl bd1 bd2 bd3 bd4 : list cell) : Prop :=
    (exists buf, u8arr usegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at usegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at usegs mm (DT + 4) cbs
    /\ stk usegs mm lo (SP + -512)
    /\ rw_cells usegs mm (SP + -512) spl /\ cells_size spl = 136%nat
    /\ rw_cells usegs mm (SP + -376) bd1 /\ cells_size bd1 = 40%nat
    /\ (exists jj, rw_cells usegs mm (SP + -336) [CB 112 jj])
    /\ rw_cells usegs mm (SP + -224) bd4 /\ cells_size bd4 = 40%nat
    /\ rw_cells usegs mm (SP + -184) bd3 /\ cells_size bd3 = 40%nat
    /\ rw_cells usegs mm (SP + -144) bd2 /\ cells_size bd2 = 40%nat
    /\ rw_cells usegs mm (SP + -104) FRS
    /\ mem_inv usegs mm /\ munch DW m0 mm /\ wmono usegs m0 mm.

  (* [comment removed for export] *)
  Lemma x4s_stk : forall mm spl bd1 bd2 bd3 bd4, X4F mm spl bd1 bd2 bd3 bd4 -> stk usegs mm lo (SP + -104).
  Proof using All.
    intros mm spl bd1 bd2 bd3 bd4 (BUF & SRC & CBS & ST & SPC & L0 & B1 & L1 & (jj & JJ) & B4 & L4 & B3 & L3 & B2 & L2 & FR & MI & MU & WM).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    release_frame SPC ST (SP + -376).
    release_frame B1 ST (SP + -336).
    release_frame JJ ST (SP + -224).
    release_frame B4 ST (SP + -184).
    release_frame B3 ST (SP + -144).
    release_frame B2 ST (SP + -104).
    exact ST.
  Qed.

  (* [comment removed for export] *)
  Lemma x4s_epi0 : forall mm (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    stk usegs mm lo (SP + -104) -> rw_cells usegs mm (SP + -104) FRS ->
    mem_inv usegs mm -> munch DW m0 mm -> wmono usegs m0 mm ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x1826c) fc None mm (seg_rom usegs)).
Proof using All.
    intros until xra. intros ST FR MI MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    do 14 zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  Lemma x4s_epi : forall mm spl bd1 bd2 bd3 bd4 (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    X4F mm spl bd1 bd2 bd3 bd4 ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x1826c) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until xra. intros XF.
    pose proof (x4s_stk _ _ _ _ _ _ XF) as STK.
    destruct XF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & MI & MU & WM).
    eapply x4s_epi0; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma x4s_err : forall mm spl bd1 bd2 bd3 bd4 (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    X4F mm spl bd1 bd2 bd3 bd4 ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x18268) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until xra. intros XF.
    zstep.
    eapply x4s_epi; exact XF.
  Qed.

  (* [comment removed for export] *)
  Definition SPL3 (v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v104 v112 v128 : Z) (j0 j96 j120 : list byte) : list cell :=
    [CB 8 j0; C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v16); C8 (Z_to_bv 64 v24); C8 (Z_to_bv 64 v32); C8 (Z_to_bv 64 v40);
     C8 (Z_to_bv 64 v48); C8 (Z_to_bv 64 v56); C8 (Z_to_bv 64 v64); C8 (Z_to_bv 64 v72); C8 (Z_to_bv 64 v80);
     C8 (Z_to_bv 64 v88); CB 8 j96; C8 (Z_to_bv 64 v104); C8 (Z_to_bv 64 v112); CB 8 j120; C8 (Z_to_bv 64 v128)].

  (* [comment removed for export] *)
  Definition BD4 (c4 bc4 ptr4 st4 : Z) (jp : list byte) : list cell :=
    [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 bc4); CB 4 jp; C8 (Z_to_bv 64 ptr4); C8 (Z_to_bv 64 st4); C8 (Z_to_bv 64 (st4 + 8))].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma x4s_end : forall mm (v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v104 v112 v128 : Z) (j0 j96 j120 : list byte)
      c1 bc1 ptr1 st1 jp1 c2 bc2 ptr2 st2 jp2 c3 bc3 ptr3 st3 jp3 c4 bc4 ptr4 st4 jp4
      (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    X4F mm (SPL3 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v104 v112 v128 j0 j96 j120)
      (BD4 c1 bc1 ptr1 st1 jp1) (BD4 c2 bc2 ptr2 st2 jp2) (BD4 c3 bc3 ptr3 st3 jp3) (BD4 c4 bc4 ptr4 st4 jp4) ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x19ca4) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until xra. intros XF.
    pose proof XF as XF0.
    destruct XF as (BUF & SRC & CBS & ST & SPC & L0 & B1 & L1 & JJ & B4 & L4 & B3 & L3 & B2 & L2 & FR & MI & MU & WM).
    unfold SPL3 in SPC. unfold BD4 in B1, B2, B3, B4.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    zto 0x19d14.
    zstep. if_cases K.
    all: zto 0x1826c.
    all: eapply x4s_epi; exact XF0.
  Qed.

End X4SB.
End CANSEC1.

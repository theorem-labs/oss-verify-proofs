(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_rs_pure.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_rs_dl () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List8map_consI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01C47Corelib5Lists7ListDef3nthC47Corelib5Lists7ListDef5skipnC47Corelib4Init5Peano2ltK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive02C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_dl;upd_app_midC46Stdlib5Lists4List:length_mapC47Corelib4Init3Nat3addC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_1_rC46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List:length_appC46Stdlib5Lists4List7map_appc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_dl>skipn_cons_nthC47Corelib5Lists7ListDef3mapI47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic3and00c5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_dl6dl_invI5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01K47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01C47Corelib4Init5Logic9False_indI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz02C5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats;direct_loopC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount6assertC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_pure;direct_stepC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z8mul_commC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit7load_okC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;Forall_ZnthC47Corelib4Init3Nat3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib5Lists4List<length_skipnC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit7src_rd2K47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbK4ELinuxProcessSemantics5Riscv7Prelude4tree01C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr06C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics5Riscv7Prelude4tree02C45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC56Stdlib6ZArith6BinInt1Z7add_0_rC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_writeC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeK46Stdlib9micromega7EnvRing5PExpr07I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writec5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_dl>u8_prefix_snocK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC56Stdlib6ZArith6BinInt1Z4landC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7eqb_neqC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_pure;direct_stopC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit>unsigned_byte'C47Corelib4Init9Datatypes7nat_indC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula05C5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z7inj_addI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqI47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStatsCHUF_SYMBOLVALUE_MAXK4ELinuxProcessSemantics5Riscv5Instr5msize01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I46Stdlib5Lists4List6Exists00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init5Logic4True01".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma upd_app_mid : forall {X} (l1 : list X) x rest y, upd (l1 ++ x :: rest) (length l1) y = l1 ++ y :: rest.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs_dl ()) [] "h04resth11xh21yh32l1h42IHh51Xh61lh71zp;1p;3p;2p;4p;6p;5p10000p4p710R0p1000Mp4p710p8P0g000iR0p4p710R1p8p200R2P1p8P2g001GR3p4p710p8P2g0027R4p4p710p8P2g002YR5p4p710p8P2g0039R6p4p710p8p1003Vp4p7210P1p8p1004Bp4p7210P1p8g004_j12Tg005?j30TP6j31TP5j23TP3j45Tg005_j34Tg0069j26Tg006Sj19TP0j68TP4j57Tf0R4#2f1R0%20f2R3f3R5#2f4R6f5R1#2R7P1A013091151315P4C5A0140911534]2]0]1W3%23R8%26R9A0640R:'6P6%96R;A0630516136;P4C5A16;:549eX25W0X10f6R;#2P;A0;3091;513;5P4C5A0;4091;534^21^09^15f7R9#2R:A0940R<9196R=f8R>#2A0>;4A0>0391>190>;34X6:A091=,6:P9A0930R=91961396P4C5P5P3P0P4O3E8P9A0916R1=19=1391P4C5A191<54:eX2;X07X16W4X38X70P4D7W3X52o"). Qed.

Lemma skipn_cons_nth : forall {X} (l : list X) n d, (n < length l)%nat -> skipn n l = nth n l d :: skipn (S n) l.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs_dl ()) [] "p'0h01Hh11ni001nh24__x1h31dh41lh52H0h67__arithh74__ffh84__p1h98__varmaph:5__with;4__x2h<4cstrh=2IHh>1Xh?5cstr0h@1xhA1zp;1p;2p;3p;4p;6p;5p;<p;7p;8p200R0g0073R1p4p710p8P0g007OR2p4p710p8P0g0027R3p4p710p8P0g002YR4p4p710p8g004_j13TP4j25Tg007mR4j24TP2j30TP1j49Tg008ER1j11Tg005?j32Tg005_j38Tg006Sj1=Tg008dR2j16Tg009DR5j27Tg0069j2:Tg009`j4JTg00:Gj1HTg00:lj2@Tg00;Hj2GTg00;fj1XTg00<Dj1WTg00<oj2FTg00=Rj2ETg00>5j4DTg00>`j1VTg00?Bj6UTg00?fj2TTg00@Hj2PTg00A4j3OTg00ASj4NTg00BEj1MTg00Bcj2;Tg00C@j1LTg00C^j4QTg00D<j3CTg00D_j1RTg00EDj4STP3j5\Tg00Eol<ITg00FTj7[Tg00G8j8ZTg00G\l<YTg00HAR3g00H`R6P4P2P5g00I>R7f3R8f2R9f1R:g00I`R;g00J?R<f0R=M<Ip=KP:g00J]R>g00K<R?P?g00K\R@P=g00L<F[p=<P6P:g00L\P=CDp=>P8P>P?P?P@P9P:P=GZp=?P3P6P4P2P5P7f5R7f4R5P8P9P:P=M<Ip=AP3P3P6P6P1P2P2P8g00MCP9P:P=M<Yp=B%3=P:%3:1559,4:%37A0798P7P9P8P:C9%19R2=07852738[^38^13W4%=8,58,4:149;%69R1/7<R4P9P11:611:6<CKP=CJP4%H8R4%68,@<R1p-0RAg00MgRB#=RC%3BRB1G6:%X6RD%W6REP61F6<RFg00NSg00O:RG,E6RHCD,<E%V?RIPE1>HF,<EPIPEP>P?P?P@P8EUC?C?1TE@R@P=P9g00O_R?g00P?R>':1P=9=8?>dAO6<:CNR>b7b9b:X26W81@<=17:<P8[[^26^8AP=f7RA#3%=AR?90A7PAP7P?P5C9%17=0A?52A38%67R?P:P9O4b6b<b5W0X39X13%391579,4:f6RF#3A0F98PFP9P8P:C9A0F2852F38[^35^13A2F58,5F,4:P3f8R2/57#1,4=f9RJ#3A2JAFRK90J:PJP:PKP8C9%1:RL=0JK52J38]0P915A5#1,4;%32P2P;A22F7RKP9C9%1;=02K522':W0%1=15JF#1'4PFP:P5f:RF/5ARJ,4:%6:RK%6JR;'7P:PK1:6KRMPJP;1:6;RNEA%1JRO,4L%MGRP,;K1;;P'7RQPL1;=PRRX@6RSPKO1PSP:PKPMCBPOPSP;O1PSPJP;PNCBEAP=CJPQf;RQ/52RN#H%6N,@<P4P1PCPBP61G69P:%L6CQPDPE1F6PRD9C6H%RG,E6RG=C6D'>,<EPI1>HG,<EC?P@P>b7b9b:X26X;61;:P,7R17:9[^26^;6P=f>/5Q#6P?P8O3b6b?b<b5CSO3%3FA2F2AR290FLPFPLP2P5C9%1L=0F252F38eW0X13P=O1n0110000020011100P=O1W0X37X13W=W4XA:P=D\W4X>0o"). Qed.

(* [comment removed for export] *)
Lemma u8_prefix_snoc : forall (acc : list Z) (jh : list byte) (v : Z), (length acc < length jh)%nat ->
  upd (map (Z_to_bv 8) acc ++ skipn (length acc) jh) (length acc) (Z_to_bv 8 v)
  = map (Z_to_bv 8) (acc ++ [v]) ++ skipn (length (acc ++ [v])) jh.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs_dl ()) [] "h01lh11nh21Eh31Hh43acch52jhh61vp;1p;2p;4p;3p;5p;6g004_j1?Tg00D_j1=Tg00P_j1HTg00Q=j1BTg002Yj2;Tg007mj2NTg00Q`j28j1@Tg0073j4<Tg008Ej16Tg007Oj33Tg005?j3:Tg0039j30Tg001Gj49Tg006Sj1OTg005_j31Tg00RFj5MTg00SIj4LTg000Mj6>Tg00Shj2GTg0069j2FTg00T?j2ETg00T_j1DTg000ij67Tg00UCj4ITg00Uaj3CTg00V@j5JTg00V\j5KTg00Wbj4ATg00H`R0f0R1';p=4P0f2R2f1R3P1CAp=2f4R4f3R5A:23130p=5%?0g00O:#=#=#=#HR6#BR7#?R8%421;73'NP8P7%45R9P2g00J?,86R:C<R;%69=372R<5:7R=P7%@6R>=274R?=071%44R@1862RAC9P0P4P0P2%O0RBD5RC927>%4C=375507518X08P7A27>5RCP;P<1863R3DMP7A07C=1;7CP3C9P7PCP7P3P<D5518g00HAR<1;7?P7P7f5R3927>RCP7P7%43R=P4P:C<%6=R;=374RDD5REP11865RFC9P7PCP7PFPDD5RD518X1<P1P@P0P7P>P4CLE>P7P7P?P7P7P@P5P:C<%6@=375RGD5P@PAC9P7P?P7PAPGD5518P8PDf6RGA:04BRA500R?927>%4?=373R?5079181X08P8A:05BRB927>R5907CR@P7A27>GRHP71864R6%4G#6=373D5RGA071?518X08P<%4B,G=R?A27>A907HA3713RA507918GX1<P8A37?4R?9075907CR4A18G1X08P<P;P7PHP7P6PAD5918GX1<1F8Dg00I`#6,E=%D=E7A18D4eA07@?P7PCP5P?CIE>A003BR?#4AC03BE7A27>?P0P7P>P3PBDJE7P7PEP=PFC9P1E7b2b2A3792P7P2P9P:P1DKE7W3X60W5W4o"). Qed.

Lemma dl_srliw : forall x k, 0 <= x < 2^31 -> 0 <= k -> bv_swrap 32 (bv_wrap 32 x ≫ k) = x ≫ k.
Proof.
  intros x k Hx Hk. rewrite wrap32_small by lia. apply swrap32_small.
  assert (0 <= x ≫ k) by (apply Z.shiftr_nonneg; lia).
  assert (x ≫ k <= x) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); Z.div_mod_to_equations; nia).
  lia.
Qed.

Lemma dl_half : forall k, 0 <= k -> (2 * k) ≫ 1 = k.
Proof.
  intros k Hk. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  rewrite Z.mul_comm. apply Z.div_mul. lia.
Qed.

Lemma dl_srliw_dbl : forall k, 0 <= k < 2^29 -> bv_swrap 32 (bv_wrap 32 (2 * k) ≫ 1) = k.
Proof. intros k Hk. rewrite dl_srliw by lia. apply dl_half. lia. Qed.

Ltac dl_ck :=
  let K := fresh "KC" in
  if_cases K; [zify_cond K; exfalso;
    repeat match type of K with context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) in K by lia end;
    first [ lia | Z.div_mod_to_equations; lia ] |].

Section DL.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Variables (x8 x12 x13 x14 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (m : fmem) (HW S oSize K : Z) (src : list Z) (jh : list byte).
  Variable POST : machine_state -> Prop.
  Hypothesis HOS : 1 <= oSize <= 255.
  Hypothesis HK : K = (oSize - 1) / 2.
  Hypothesis HJH : zlen jh = 256.
  Hypothesis HSRC : K + 2 <= zlen src.
  Hypothesis HSB : Forall (fun c => 0 <= c < 256) src.
  Hypothesis HHW : 0 < HW /\ HW + 512 <= 2^64.
  Hypothesis HS : 0 < S /\ S + zlen src <= 2^64.
  Hypothesis DHS : HW + 256 <= S \/ S + zlen src <= HW.

  (* [comment removed for export] *)
  Definition dl_inv (m1 : fmem) (acc : list Z) : Prop :=
    u8arr usegs m1 HW (map (Z_to_bv 8) acc ++ skipn (length acc) jh)
    /\ bytes_at usegs m1 S (map (Z_to_bv 8) src)
    /\ munch [(HW, HW + 256)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  Notation ST pc mm x5 x6 x7 x10 x11 x15 x16 x17 x19 :=
    (MS (mkR ra sp gp tp x5 x6 x7 x8 (Z_to_bv 64 HW) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 oSize) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma dl_loop : forall f k acc m1 fuel (x5 x6 x7 x17 x19 : word),
    Z.of_nat f = K - k + 1 -> 0 <= k <= K -> K - k + 2 <= Z.of_nat fuel ->
    zlen acc = 2 * k -> Forall (fun c => 0 <= c < 256) acc -> dl_inv m1 acc ->
    (forall m2 cells (y5 y6 y7 y10 y11 y15 y16 y17 : word),
       direct_loop src fuel (2 * k) oSize acc = Ok cells -> zlen cells = 2 * K + 2 ->
       Forall (fun c => 0 <= c < 256) cells -> dl_inv m2 cells ->
       evt usegs POST (ST 0x1eec0 m2 y5 y6 y7 y10 y11 y15 y16 y17 x12)) ->
    evt usegs POST (ST 0x1ee68 m1 x5 x6 x7 (Z_to_bv 64 (2 * k)) (Z_to_bv 64 (Z.lxor HW 18446744073709551615))
                      (Z_to_bv 64 (S + 1)) (Z_to_bv 64 (2 * k)) x17 x19).
Proof using All.
  induction f as [|f IH]; intros k acc m1 fuel x5 x6 x7 x17 x19 EF KR FU LA FA INV CONT; [lia|].
  destruct fuel as [|fuel]; [lia|].
  destruct INV as (OUT & SRCB & MU & WM & MI).
  assert (KO : 2 * K + 1 <= oSize <= 2 * K + 2)
    by (rewrite HK; pose proof (Z.div_mod (oSize - 1) 2 ltac:(lia)); pose proof (Z.mod_pos_bound (oSize - 1) 2 ltac:(lia)); lia).
  zstep.
  rewrite (dl_srliw_dbl k) by lia.
  zstep.
  zstep.
  dl_ck.
  zstep.
  dl_ck.
  assert (BR : 0 <= Znth (1 + k) src < 256) by (apply (Forall_Znth (fun c => 0 <= c < 256)); [exact HSB | lia]).
  pose proof (src_rd usegs m1 S src (1 + k) SRCB ltac:(lia)) as RX.
  zstep. cbv beta. clear RX.
  zstep.
  zstep.
  pose proof (u8arr_store_ok usegs m1 HW _ (2 * k) (wa (HW + 2 * k)) OUT
                ltac:(rewrite length_app, length_map, length_skipn; lia) eq_refl) as SOK.
  zstep.
  replace (bv_unsigned (Z_to_bv 8 (Znth (1 + k) src))) with (Znth (1 + k) src)
    by (rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; change (bv_modulus 8) with 256; lia).
  rewrite (Z.shiftr_div_pow2 _ 4) by lia. change (2^4) with 16.
  rewrite le1_lit.
  pose proof (u8arr_write usegs m1 HW _ (2 * k) (Z_to_bv 8 (Znth (1 + k) src / 16)) OUT
                ltac:(rewrite length_app, length_map, length_skipn; lia)) as OUT2.
  replace (Z.to_nat (2 * k)) with (length acc) in OUT2 by lia.
  rewrite u8_prefix_snoc in OUT2 by lia.
  clear OUT. store_done. rename OUT2 into OUT.
  zstep.
  dl_ck.
  zstep.
  zstep.
  zstep.
  try (rewrite (Z.mod_small (2 * k + 1)) by lia).
  zstep.
  dl_ck.
  pose proof (src_rd usegs _ S src (1 + k) SRCB ltac:(lia)) as RX.
  zstep. cbv beta. clear RX.
  zstep.
  zstep.
  try (rewrite (swrap32_small (2 * k + 2)) by lia).
  pose proof (u8arr_store_ok usegs _ HW _ (2 * k + 1) (wa (HW + (2 * k + 1))) OUT
                ltac:(rewrite length_app, length_map, length_skipn, length_app; cbn [length]; lia) eq_refl) as SOK.
  zstep.
  try (rewrite (swrap32_small (2 * k + 2)) by lia).
  zstep.
  try (replace (bv_unsigned (Z_to_bv 8 (Znth (1 + k) src))) with (Znth (1 + k) src)
    by (rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; change (bv_modulus 8) with 256; lia)).
  rewrite le1_lit.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [Z_to_bv 8 ?X]) _) =>
    pose proof (u8arr_write usegs _ HW _ (2 * k + 1) (Z_to_bv 8 X) OUT
                  ltac:(rewrite length_app, length_map, length_skipn, length_app; cbn [length]; lia)) as OUT2;
    replace (Z.to_nat (2 * k + 1)) with (length (acc ++ [Znth (1 + k) src / 16])) in OUT2
      by (rewrite length_app; cbn [length]; lia);
    rewrite u8_prefix_snoc in OUT2 by (rewrite length_app; cbn [length]; lia);
    clear OUT; store_done; rename OUT2 into OUT
  end.
  zstep.
  zstep.
  try (rewrite (Z.mod_small (2 * k + 2)) by lia).
  zstep.
  rewrite <- app_assoc in OUT.
  assert (FA2 : Forall (fun c => 0 <= c < 256) (acc ++ [Znth (1 + k) src / 16; Z.land (Znth (1 + k) src) 15])).
  { apply Forall_app; split; [exact FA|].
    change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2^4) with 16.
    apply Forall_cons; [cbv beta; split; Z.div_mod_to_equations; lia|].
    apply Forall_cons; [cbv beta; split; Z.div_mod_to_equations; lia|apply Forall_nil]. }
  assert (LA2 : zlen (acc ++ [Znth (1 + k) src / 16; Z.land (Znth (1 + k) src) 15]) = 2 * k + 2)
    by (rewrite length_app; cbn [length]; lia).
  assert (DS : direct_loop src (Datatypes.S fuel) (2 * k) oSize acc
               = direct_loop src fuel (2 * k + 2) oSize (acc ++ [Znth (1 + k) src / 16; Z.land (Znth (1 + k) src) 15])).
  { rewrite direct_step by lia.
    replace (1 + 2 * k / 2) with (1 + k) by (Z.div_mod_to_equations; lia).
    rewrite load_ok by lia.
    assert (A1 : (2 * k + 1 <? HUF_SYMBOLVALUE_MAX + 1) = true) by (apply Z.ltb_lt; unfold HUF_SYMBOLVALUE_MAX; lia).
    cbn [bind]. rewrite A1. reflexivity. }
  if_cases KB; zify_cond KB.
  - replace (Z_to_bv 64 (2 * k + 2)) with (Z_to_bv 64 (2 * (k + 1))) by (f_equal; lia).
    eapply (IH (k + 1) (acc ++ [Znth (1 + k) src / 16; Z.land (Znth (1 + k) src) 15]) _ fuel); try lia; try exact FA2.
    + unfold dl_inv; refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
    + intros m2 cells y5 y6 y7 y10 y11 y15 y16 y17 DL ZC FC IC.
      apply (CONT _ cells); auto. rewrite DS. replace (2 * k + 2) with (2 * (k + 1)) by lia. exact DL.
  - zstep.
    apply (CONT _ (acc ++ [Znth (1 + k) src / 16; Z.land (Znth (1 + k) src) 15])).
    + rewrite DS. destruct fuel as [|fuel]; [lia|]. apply direct_stop. lia.
    + lia.
    + exact FA2.
    + unfold dl_inv; refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
Qed.
End DL.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP FpBound FpReal FpSiteB FpSiteC ExpfModelB ExpfTablesB.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Km_setelem Km_iface Km_kit KmF_kit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface Cf_kit CfX_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit Bi_fpkit Bi_pixakit Bi_addkit Bi_relkit Bi_restore Bi_lskit Bi_kmkit Bi_bgkit Bi_fpkit2 Bi_iface2 Bi_bcreate_defs Bi_bckit BiV_defs BiV_iface BiV_iface2 Bi_bcreate_ncloop Bi_bcreate_kfrloop LeptB_guard LeptB_guard2 LeptB_guard3 D_iface D_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_bcreate_rloop_defs () := "C46Stdlib5Lists4List7map_appC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00C47Corelib5Lists7ListDef3seqC47Corelib4Init3Nat3addK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K53Lib:ExpfModelB8bil_cellC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02C46Stdlib5Lists4List5seq_Sc69OSSVerify5KrLib2K53B02EBi_bcreate_rloop_defs9bil_wordsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List:length_seqC46Stdlib5Lists4List:length_mapC47Corelib4Init5Peano2ltI47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List9nth_errorC47Corelib4Init9Datatypes:option_mapK47Corelib4Init9Datatypes6option01C56Stdlib5Arith8PeanoNat3Nat3ltbK47Corelib4Init9Datatypes6option02C56Stdlib5Arith8PeanoNat3Nat6ltb_ltC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List=nth_error_seqC46Stdlib5Lists4List=nth_error_mapI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K53Lib:ExpfModelB7bil_argC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib:ExpfModelB:expf_modelC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7nan_boxC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics5Riscv3Sem7unbox_sC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics5Riscv3Fpu9fp_of_intC4ELinuxProcessSemantics5Riscv3Fpu6fp_divC69OSSVerify5KrLib2K53Lib2FP=unbox_nan_boxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib2FP9fcvt_s_wuC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib2FP6fdiv_sC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics5Riscv3Sem8sgnj_valK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C4ELinuxProcessSemantics5Riscv3Fpu:fmt_singleK4ELinuxProcessSemantics5Riscv3Fpu5rmode01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv3Fpu6fflags00K4ELinuxProcessSemantics5Riscv5Instr6fsgnop02K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C69OSSVerify5KrLib2K53Lib;ExpfTablesB9DEN_RANGEC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify5KrLib2K53Lib:ExpfModelB2ESC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01c69OSSVerify5KrLib2K53B02EBi_bcreate_rloop_defs9FS0_RANGEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface3rtsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53B028Lept_kit?cps_ASTA_conseqC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K53B026ImageA5asegsC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition bil_words (D : Z) (n : nat) : list word := map (fun q => Z_to_bv 64 (bil_cell D (Z.of_nat q))) (seq 0 n).
Lemma bil_words_S : forall D n, bil_words D (Datatypes.S n) = bil_words D n ++ [Z_to_bv 64 (bil_cell D (Z.of_nat n))].
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_bcreate_rloop_defs ()) [] "h01lh11qh21Dh31np;1p;2p;3p;4p;5p;6g0000R0p4p7210g000LR1p4p710p8g000jj1<Tg001Jj26Tg001fj2?Tg002=j18Tg002]j35Tg003=j32Tg003Zj10Tg004?j1>Tg004]j1=Tg005@j19Tg005`j23Tg006_j24Tg007Ej41Tg007aj37Tg008;j2CTP0j5BTP1j6;Tg008Uj1ATg0094j2@Tg009Nj2:Tg00:Yg00;7R1%<1R0g00;VR2f0R3'6R41?23%81551R5521R6g00<5#0#0#0#0#0#0#>R7#=R8#<R9P1P8f3%93R:'3,47X11R;P3C1P1P8P;f1R;,62C1f2R<%9;'3,47%88R=558528R>37X00P9P1P813<:,47X11R<P4C1R0P1P8P<P5C1528A793>X0913;:,47=58=R=9280,C9P1P8P<P6C1P1P8P<P4P5DBE;%A3R5,621@32E;1:;51:;3=28=579eW3W2o"). Qed.
Lemma bil_words_length : forall D n, length (bil_words D n) = n.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_bcreate_rloop_defs ()) [] "h01nh11Dh21qp;2p;3p;6p;1p;4g001Jj2>Tg00<Zj21Tg007aj32Tg008;j24Tg00=:j2=Tg000Lj63Tg003Zj10Tg004?j15Tg004]j16Tg005@j17Tg005`j28Tg006_j29Tg007Ej4:Tg00=Yj4<Tg009Nj2;Tg00:Yg00;7R0P0g00;VR1f0R2'>R3,10R4f1R59202X00R6P0P2P61402P41=21E3g00<5#0#0#0#0#0#0#5R1#6R4P0P4f2%72'8,91X20R1P3C:'1P0P4P1P3C<E31;52,14=202eW0W1o"). Qed.
Lemma bil_words_nth : forall D n q, (q < n)%nat -> nth_error (bil_words D n) q = Some (Z_to_bv 64 (bil_cell D (Z.of_nat q))).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_bcreate_rloop_defs ()) [] "h01qh11nh22H0h31mh41oh51Dh61Hh71bp;2p;1p;3p;4p;6p;5g00>8j29Tg003Zj13Tg004?j1ATg004]j1>Tg00>Pj1<Tg005@j16Tg005`j21Tg006_j20Tg001Jj2?Tg00?2j38Tg00?Pj47Tg00@4j24Tg007aj32Tg00@Vj25Tg001fj2=Tg00A6j1ITg00AXj2HTg00B;j4GTg008;j2DTg00BWj6CTg00C3j3BTg000Lj6;Tg007Ej4@Tg00CUj5ETg009Nj2FTg00D7R0f0R1g00DWR232p=:g00:Yg00;7R3f1R4,91g00<5#3#3#3#3#3#3#AR5#>R6#<R7P3P6f4R8%61R9'1,05X03R:g00;VR;f2R<'?R==834R>C7%6<,18,05,46R89271X47%<3R?P0P?154<R@1=;4,43%I3RAn0100000020000P3P6f5RB/19,05X03P1C7=278X4?P0P@P2g00E71541#:19<4RC[194115<4#:[RDf3RE/5<#:\C1H41P1n2001000000120000000X33X13PD^33^13P1P<PEP4O3b2CGA202@P0P2P3P6f6/19,05X03P0P?P11=;E,43PAn0100000020000C7%6E,1B,05,46527X701D7815<EP1ECb2P>AB;<4E;P3P6P:P=C@=864P3P6P:P4P=DEE;1FE<=864%64,1E,05,46527eW6X03W1W5o"). Qed.
Lemma bil_cell_box : forall D i, nan_box (Z_to_bv 32 (expf_model (Z_to_bv 32 (bil_arg D i)))) = nan_box (Z_to_bv 32 (bil_cell D i)).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_bcreate_rloop_defs ()) [] "h01Dh11bh21ip;1p;2p;3p;6g003Zj11Tg004?j17Tg004]j15Tg00ERj24Tg006_j20Tg00FPj16Tg00GQj12Tg007aj33Tg008;j2<Tg00H;j2;Tg00Hej28Tg000Lj69Tg005`j2:Tg00:YR0g00<5#1#1#1#1#1R1#7R2#5R3f1R4f0R5'4,02#6,02R6%11#7#5R1f2/44,02#6,02#2%2533X13%26R3,<11;26,021826E91:45,02#29313eX20W0o"). Qed.
Lemma bil_cell_range : forall D i, 0 <= bil_cell D i < 2^32.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_bcreate_rloop_defs ()) [] "h01Dh11Rh21ip;1p;2g003Zj10Tg004?j1=Tg00ERj28Tg006_j23Tg00FPj1<Tg00IWj2:Tg00H;j29Tg00JJj22Tg00Jfj17Tg00KOj21Tg00E7j24Tg005`j26Tg00Kkj15Tg00LIj2;Tg00:YR0g00<5#0R1#0#0#0#0R2#=R3f1R4f0R5'8,33#<,33R6':g00LfR71936R6'2%73,16'4P5b11645R5,27%51%52';,15'4eX20W0o"). Qed.
(* [comment removed for export] *)
Lemma range_arg : forall i, 0 <= i <= 255 ->
  fdiv_s RNE (nan_box (sgnj_val F_SGNJN (unbox_s (fcvt_s_wu RNE (Z_to_bv 64 (i * i)))) (unbox_s (fcvt_s_wu RNE (Z_to_bv 64 (i * i))))))
         (nan_box (Z_to_bv 32 DEN_RANGE))
  = nan_box (Z_to_bv 32 (bil_arg DEN_RANGE i)).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_bcreate_rloop_defs ()) [] "h01zh11bh22Hah36__sat1h44__x1h51Eh61Hh72Hih87__arithh94__ffh:6__sat0h;8__varmaph<5__with=1ip&0p;1p;2p;3p;4p;5p;6p;7p;8g00MDj11Tg00Kkj16Tg00JJj2RTg00E7j2JTg003Zj10Tg004?j1WTg004]j1VTg00Mij2HTg006_j2;Tg00H;j23Tg00GQj1?Tg00NFj1GTg00ERj2NTg007aj32Tg00O0j2hTg00OVj2gTg00KOj2KTg00LIj2dTg00P>j3cTg00Pbj2bTg008;j2FTg008Uj1MTg00QCj2ETg00Qlj3DTg00RUj2UTg00SAj2LTg00Sjj2TTg00TKj4`Tg00Tlk203Tg002=k100Tg002]j3^Tg000jj1{Tg00UUj2zTg00V3j1wTg00VQj1vTg00W<j2OTg00A6j1tTg00W_j5sTg00XCj3rTg00Xfj2qTg00YIj3pTg00Ylj4ZTg00ZWj2oTg00[9j2nTg00[ej3kTg00\Dj4lTg00Jfj1mTg00]6j3jTg00]bj2iTg000Lj6=Tg00^Qj5XTg00_=j4QTg00BWj6uTg00_fj1STg00`bj2xTg00aZj3fTg00bOj3]Tg00blj4yTg00cWj3eTg00d@j7|Tg00ddj8}Tg00eHj7~Tg00LfR0f0R1'Rp=:%11#1p=Y%11#1#1#1p=a%01#0p=Bg00elR2g00fYR3g00gCR4f1R5P1DXp=>g00:YR6g00gcR7;]1,;5p=9f2R8g00hNP5P1Cyp=7P2P3P5P1CQp=8A]671,;5#?p=41;51#?p=PAe651p=5%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=A%11#1#1#1#1#1#1#1p=@%01#0#0#0p>02%01#0#0#0#0#0#0#0p>01%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=_P6P5g00i;P1CZp=CP5g00ibR7g00jAR9P9g00jaR:P1g00kAF|p=<f3R;P7P9P9P:P8P5P1G}p=IP8P7P9P9P:P5P1F~p=[P2P3P1g00kaR2CQp=\%:1g00<5R<#1#Y#aR=#6R>,R1'J%0<R?#0#BR@#0RA#WRB#VRC%6ARD%0ARA#WRE1H55RF,;ERG'3RH'>,9BRI#?#GRJ=7BJRK%VERL13B1RM1;B2RN#?RO#GRP,3BRQ'8,4B1N28,PBRR32X1CPCPIA7B11,3B/8Q,4B=2LRX1CPCPN1H88RQ,;E,3ERS,>D,9BRT=7BT,3B/8M,4B=2LRX1CP61hEFA261QX06%6?R?%6ARC'g1K0?RM%:C1d?CRT,K0[RU[%:?RVg00lbRWAc?C5UW2%:T\WRW^2VP5g00m>1b0?'FPMeO1PUg00mdRUg00;VRM#MRC#MRX#M,E6RY1E6XRX/5X'51E6MRM,5YRY5D6g00nPRZ'U%A=#A#6,L6R[P6%6<,T6P<1T60C`-0361E6CRC'5'5%@=#@#@#@#@#0#B$02#1#@#6,L6/5Y%BA$01#_#A#A#A#6,L615XC'515XM,5[5D65D65D6/UZ&00U5^U3^%{U1z65%w6%v6RUPU1O60RZ1O6?R?'C,<U%t9R[PUPUP7P9P9P:DsP[Ar6?ER?,CZ,<UCICIP[PU1q6<R<,CZ,<U1O6>,C<,<U5[UP[Ap6<<R<,CZ,<UP6P<g00o<P?CZ,<U5[UCICI1oU:P1P8g00D7RUg00DWR:'F1n18=2U:dAk605Clb9b;b<X46PW\V%:51R5>'J%:Q1KQT'J[[^46P1f5P8f4R8O3b8b3b:b3%:F%mE,KF'Je9jEFPH1iEFE=A26HFP6PQ1>D1,9BRH=7BH,3B13BNRH'8,4B1N2;,PB52LX06P6PQ1H;;,>D,9BR;=7B;,3BR;/8H,4Bg00ocRFP3PFP3P4PDP1DX,9BR4=7B4,3BP2CQ,4B52LX06%Y@#0#1#B#1#0#B#_#6R@,F61;B@,3B926@dA262HR@eP@P6P21H88,>D,9BR8=7B8,3BR8/81,4B%\8,4B52LX06%\;,4B,FLPHP1Eub6PSP1E=1>DQ,9BRQ=7BQ,3B/8H,4B=2LRePSP1E=b5PP%SNE=PJ%SIE=%?K#G%SKE=1x3G#GRG=7BG#?=f3O1N25,PB52LeW7X=6o"). Qed.
(* [comment removed for export] *)
Definition FS0_RANGE : Z := 18446744070543376384.
Definition FS1_SPAT : Z := 18446744070526599168.
Definition FS2_TEN : Z := 4621819117588971520.
Lemma fs0_range_box : nan_box (Z_to_bv 32 DEN_RANGE) = Z_to_bv 64 FS0_RANGE.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_bcreate_rloop_defs ()) [] "p;1p;2p;3g003Zj10Tg004?j16Tg004]j1:Tg00MDj11Tg00Kkj1<Tg010\j2;Tg011Oj39Tg008;j28Tg006_j25Tg00GQj1>Tg007aj3=Tf0R0#0#0#0#0p=3%10#1p=7%10#1#1#1p=2%00#0p=4g00<5R0#0#3R1#0#6R2#:R3%10#7#2#2#2#2#2#2#2#0#1#3#7#0#1#4#1#0#4#3#3#3#3#<R01;20592'8%61g00ka'5#>g0122,525=3do"). Qed.

Section RloopDefs.
Variable RT : rt_sig.

(* [comment removed for export] *)
Lemma rl_cps_ASTA_val : forall Σ PMc (A B C : machine_state -> Prop) (D : Prop) Q,
  cps asegs (ASTA RT Σ PMc (fun ms => (A ms /\ (B ms /\ C ms)) /\ D)) Q ->
  cps asegs (ASTA RT Σ PMc (fun ms => (A ms /\ B ms) /\ C ms /\ D)) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_bcreate_rloop_defs ()) ["RloopDefs"] "h02msh12H0h21Ah31Bh41Ch51Dh61Hh72Hah82Hbh92Hch:2Hdh;3PMch<1Qh=2Σp;1p;2p;4p;3p;8g013=j15Tg00E7R0j20Tg0145j43Tg014nj32Tg015cj41Tg016>j84Tp,2RTR1#5g017Bp-0R2[g0188R3P2[R4g019?P2[g01:4P1f6R5f5R6P6f0R7O1R8f4R9P7O1R:f3R;P7O1'0'0f2R<'0X03C3;27P1f7R1P5P5P7O1R=108:'0/0;X0310=810:;'0R:X03f1R=P7P0P1P=O1P5P=O1'0P6P=O1/09f8R8P<O1P1P<O1P5P<O1'0'0/06P7f9R<P;O1P8P;O1'0P0f:R;P9O1P<P9O1P<P6O1/08f<R9P5O1R>f;R?P5O1P;P5O1'0'0/0<[P7P9P1O1P9P8O1/0?P0f=R0P<O1P9f@R9P;O1f?R<P;O1f>P;O1'0'0/00P7P<P?O1fCP0O1R?fBP0O1R;fAP0O1R0'0R8'0P9P?P8P5P;P0P6P=C1C1P7C1X:<W9P=P7O2n2001000000120000000W1W8X7>P=P7O2n2001000000120000000W1P=P7O2n2001000000120000000X1:X03G4W6W<X52X44X34W2W;W=o"). Qed.

(* [comment removed for export] *)
Definition bc_rloop_stmt : Prop :=
  forall (PMc : Model -> Prop) (QF : config -> Prop) (F : bvmap 5 word) (x2 : rts RT) (x4 m : mem) (usp lo rng spat : Z) (gp : word) (PLR PF : Z -> Prop),
  fdfs_only PMc -> mat_stable PMc ->
  In (rng, 1024) (rt_live RT x2) -> rng mod 16 = 0 ->
  (forall a, PF a -> a < rng \/ rng + 1024 <= a) ->
  (rng + 1024 <= 65536 \/ 6746112 <= rng) -> (rng + 1024 <= 2147446784 \/ 17594333495296 <= rng) -> rng + 1024 <= rt_sp0 RT x2 - 8388608 ->
  rt_sp0 RT x2 - 8388608 <= lo -> lo + LSTK 2 <= usp -> usp mod 32 = 0 -> usp + 16 <= USTACK_TOP -> usp <= rt_sp0 RT x2 -> 0 <= usp ->
  (forall a, PLR a -> aclient (rt_live RT x2) (rt_frames RT x2) (usp - 352) a /\ outside [(rng, rng + 1024)] a) ->
  (forall a, PF a -> aclient (rt_live RT x2) (rt_frames RT x2) usp a) ->
  forall (KONT : forall (Se : rts RT) (me : mem) (rae t0e t1e t2e a0e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e : word) (Fe : bvmap 5 word) (fce : bv 32),
       fs_agree_but [8; 9; 18] F Fe -> reg_get Fe 8 = Z_to_bv 64 FS0_RANGE -> reg_get Fe 9 = Z_to_bv 64 FS1_SPAT -> reg_get Fe 18 = Z_to_bv 64 FS2_TEN ->
       frm0 fce ->
       ART RT Se me -> mem_inv asegs me -> wmono asegs x4 me -> stk asegs me lo (usp + -352) -> LIBH me -> io_ssp me ->
       agree_on PLR x4 me -> agree_on PF m me -> wr_at asegs me rng 1024 -> u32arr asegs me rng (bil_words DEN_RANGE 256) ->
       rt_live RT Se = rt_live RT x2 -> rt_frames RT Se = rt_frames RT x2 -> rt_sp0 RT Se = rt_sp0 RT x2 -> rt_credit RT Se = rt_credit RT x2 ->
       cps asegs (ASTA RT Se PMc (eq (entry_st rae (Z_to_bv 64 (usp + -352)) gp (Z_to_bv 64 TP_A) t0e t1e t2e (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -352))
                    a0e a1e a2e a3e a4e a5e a6e a7e
                    (Z_to_bv 64 rng) (Z_to_bv 64 2147450880) (Z_to_bv 64 (rng + 1024)) (Z_to_bv 64 256) (Z_to_bv 64 1) (Z_to_bv 64 256) (Z_to_bv 64 1)
                    (Z_to_bv 64 (rng + 1024)) (Z_to_bv 64 1) (Z_to_bv 64 spat) t3e t4e t5e t6e Fe fce 0xcf584 me))) QF),
  forall k i, Z.to_nat (256 - i) = k -> 0 <= i < 256 ->
  forall (Si : rts RT) (mi : mem) (rai t0i t1i t2i a0i a1i a2i a3i a4i a5i a6i a7i t3i t4i t5i t6i : word) (Fi : bvmap 5 word) (fci : bv 32),
     fs_agree_but [8; 9; 18] F Fi -> reg_get Fi 8 = Z_to_bv 64 FS0_RANGE -> reg_get Fi 9 = Z_to_bv 64 FS1_SPAT -> reg_get Fi 18 = Z_to_bv 64 FS2_TEN ->
     frm0 fci ->
     ART RT Si mi -> mem_inv asegs mi -> wmono asegs x4 mi -> stk asegs mi lo (usp + -352) -> LIBH mi -> io_ssp mi ->
     agree_on PLR x4 mi -> agree_on PF m mi -> wr_at asegs mi rng 1024 -> u32arr asegs mi rng (bil_words DEN_RANGE (Z.to_nat i)) ->
     rt_live RT Si = rt_live RT x2 -> rt_frames RT Si = rt_frames RT x2 -> rt_sp0 RT Si = rt_sp0 RT x2 -> rt_credit RT Si = rt_credit RT x2 ->
     cps asegs (ASTA RT Si PMc (eq (entry_st rai (Z_to_bv 64 (usp + -352)) gp (Z_to_bv 64 TP_A) t0i t1i t2i (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -352))
                  a0i a1i a2i a3i a4i a5i a6i a7i
                  (Z_to_bv 64 rng) (Z_to_bv 64 2147450880) (Z_to_bv 64 (rng + 4 * i)) (Z_to_bv 64 256) (Z_to_bv 64 1) (Z_to_bv 64 i) (Z_to_bv 64 1)
                  (Z_to_bv 64 (rng + 4 * i)) (Z_to_bv 64 1) (Z_to_bv 64 spat) t3i t4i t5i t6i Fi fci 0xcf520 mi))) QF.
End RloopDefs.

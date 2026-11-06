(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim FPSteps FrmKeep FrmKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_FrmKeepEs0 () := "K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType>seg_executableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3eqbC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_sizeC47Corelib4Init9Datatypes3orbC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:FrmKeepEs05FRMS03XLOC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:FrmKeepEs05FRMS03XSZC13~~~C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images5Plain1M?loaded_segmentsC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM5scan2C13~~~K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes3nat01C46Stdlib5Lists4List2InC46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic5proj1I47Corelib4Init5Logic3and00C46Stdlib4Bool4Bool=andb_true_iffC46Stdlib4Bool4Bool=negb_true_iffK47Corelib4Init9Datatypes4bool02c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:FrmKeepEs05FRMS0:segs_factsC13~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z6eqb_eqK47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRMBfetch_safe_of_scanC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:FrmKeepEs05FRMS04xsegC13~~~K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:FrmKeepEs05FRMS04SCANC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM7step_fzC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:FrmKeepEs05FRMS05no_wxC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:FrmKeepEs05FRMS0:fetch_safeC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM9msteps_fzC13~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM>msteps_fz_mkstC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.

Module FRMS0.
Definition XLO : Z := 0x34000.
Definition XSZ : Z := 0x7e000.

Lemma segs_facts :
  forallb (fun seg => negb (seg_executable seg && seg_writable seg)
                      && (negb (seg_executable seg) || ((Z.of_N (seg_base seg) =? XLO) && (Z.of_N (seg_size seg) =? XSZ)))) RSEGS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepEs0 ()) [] "h03segp;2p;1p;3g0000j2;Tg000Jj1:Tg001Nj15Tg002Pj20Tg002nj13Tg003Lj19Tg004Jj11Tg004hj22Tg005Ej16Tg006Cj27Tg006`j34Tg007<j38Tg007VR0g0086R1';g008VR2f0R3#:R4%53'0#3%34%93#1g009U'2%63#1g00:d'2'0'7'0X02g00<334=801do"). Qed.

(* [comment removed for export] *)
Lemma SCAN : FRM.scan2 RSEGS 252 1024 XLO = true.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepEs0 ()) [] "p;2p;4p;3p;1g0000j27Tg00=Aj46Tg007<j35Tg00>Mj10Tf0R0#0#0#0#0p=2%00#0#0#0#0#0#0#0p=4%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=3%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g007VR0g0086R1'7g00<3g00>l#2#4#3#1#1#1#1#1#1#1R2%22#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1g009UC6=501do"). Qed.

Lemma no_wx : forall seg, In seg RSEGS -> seg_executable seg && seg_writable seg = false.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepEs0 ()) [] "h01Hh12H0h21bh32b1h42b2h53segh62INh72_Hh81xp;3p;1p;2p;6g00?Kj3CTg000Jj14Tg001Nj15Tg002Pj21Tg002nj12Tg003Lj19Tg005Ej18Tg006Cj27Tg006`j3>Tg00?bj3=Tg00@Ej6<Tg00@`R0j2:Tg00A;j2BTg00A\j1ATg004Jj1@Tg004hj2?Tg007<j3;Tf1R1#@f0R2'?p=3g007VR3g00867;2p=0g00B=9;32p=6g008VR4g00<3R59C42R6%42R7%52'1#2%27%92g009UR7'3%82g00:dR8'3'1'7'1X54R9=>45#0R:P9P1O1#0R;\6^84R6[P:\6A=495g00B]P1P2E<P;P01112#0f2R;#0R9%01R5':[R4%02,:511;1#0R5[f3R6#0/:9\51B12P1n2001000000120000000X43X33P4^43^33P2%46R4%56'1#2R5%24%96/37%86/38'1'7R6P1O3%05%06':P0f4R6#4R5%56'1#2#0%25%96/37%86/38'1'7#0f5R6#4%56'1#6P2f6R6#4%56'1#2#0f7R6#4#2%96/37%86/38'1'7#0P0%22#0%61[R0%62%21#0R8[%6;\8%A2P1n2001000000120000000X23P0^23P2f9R3#4%53'1R3P;O2%63P2b0b1W7W0P1P2O2n2001000000120000000b0b1b0W6W5o"). Qed.
Lemma xseg : forall seg, In seg RSEGS -> seg_executable seg = true -> Z.of_N (seg_base seg) = XLO /\ Z.of_N (seg_size seg) = XSZ.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepEs0 ()) [] "h01Hh12H0h22b1h32b2h41mh51nh63segh72H1h82H2h92INh:1Xh;2_Hh<1bh=1xp;3p;1p;2p;6p;4g00?Kj3ITg000Jj16Tg001Nj1:Tg002Pj21Tg002nj12Tg006Cj28Tg006`j3DTg00?bj3CTg00@Ej6BTg00@`R0j25Tg00A;j2HTg00D3j6GTg004hj2;Tg007<j37Tg00DOj2FTg00Doj4ETg003Lj1ATg004Jj19Tg005Ej1@Tg007VR1f0R2g0086R337p=0%A2#9g009UR4';p=3%@2#9g00:dR5';p=4%A2#9p==g00EJR6?724p=?%@2#9p=<A7625p=>g008VR7g00<3R89I72R9f1R:#6#0%62R;%:2'1#2%2;%32%42'1'8'1X67R;=D78#0R<P;P:O1#0\9^=7R9[P<\9AC7;8g00B]f2R8P:EBP;P8O1#0P011:2#0%08R;%0:R7'5[R9%02,57118:#0R7[f3R<#0/5;\71H:2P:n2001000000120000000X31X21R7P9^31^21R9P2f4R;#6R=%:;'1#2R>%2=%3;%4;'1'8R;P:O3%0>%0;'5P0f5R;#6R>%:;'1#2#0%2>%3;%4;'1'8#0f6R;#=#?%<;#>'5P2f7R;#6%:;'1#2#0f8R>#6#2%3>%4>'1'8#0P1f9R>#6%22f:R=#3%4='1'8#0X<1P2P3P;EG%23%3>%4>'1'8#0P7P9P2f;R9#3R7%49R9P:O3%07%09'5P0f<R9#3#0%49#0f=R9#=#?%<9#>'5P2f>#3#0f?#4#0f@R9#=#?%<9#>P01;:2#0A768:[R0A76:21;8:#0R9[A76<8\91F:2P:n2001000000120000000X46X56R9P0^46^56R6P2fAR0#=P4P8O3b0P9P6P2%<0P5P:O3b0CEW8W7P:P2O2n2001000000120000000b0b1b0W0W;P:P2O2n2001000000121000000b0b1b0W:W9W6o"). Qed.

Theorem fetch_safe : forall a w, fetch_word RSEGS a = Some w \/ fetch_tail RSEGS a = Some w -> FRM.word_frm_safe w = true.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepEs0 ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;2p;4p;7p;3p;9g00Ehj14Tg00FMj17Tg00Fkj2CTg0000j25Tg00GKj1=Tg00Gkj1<Tg00HKj1;Tg00Hij1:Tg00IGj19Tg00J2j13Tg00JWj2HTg00K:j4GTg00Kej7FTg00LIj2ETg00Lkj2BTg007<j3@Tg00MWj3ATg00N6j4>Tg00Nhj26Tg00ODl9DTg00>Mj10Tf0R0#0#0#0#0p=8%00#0#0#0#0#0#0#0p=I%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=?%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1%40#4p=2g00<3g009UR1g00:dR2g00>l#8#I#?#1#1#1#1#1#1#1R3%83#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1g00P]g00EJR3g00QmR4#4#7,C1'5g00RRR1#=%<1%;3%:3%93R1g00S>g00S]R5P5g00T=R5P3%34#3#3#3#3#4#2#2#2#2#2#2#7R4,H3R6g00T]P6CGg00UDFF1E15P0f2R5g007VR1g0086R6'51B05=@16dg00Udf15A3C>b1b2b31644P0b01624eg00VBM9Do"). Qed.

(* [comment removed for export] *)
Theorem step_fz : forall s s', RiscvSemantics.step RSEGS s = MachineOk s' -> frm_zero (ms_fcsr s) -> frm_zero (ms_fcsr s').
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepEs0 ()) [] "p;3g00WRj30Tg00<3g00X`g00Z130o"). Qed.
Theorem msteps_fz : forall s s', msteps RSEGS s s' -> frm_zero (ms_fcsr s) -> frm_zero (ms_fcsr s').
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepEs0 ()) [] "p;3g00[Gj30Tg00<3g00X`g00Z130o"). Qed.
Theorem msteps_fz_mkst (fx fx' : FPState) R R' pc pc' M M' :
  msteps RSEGS (@mkst fx R pc M (seg_rom RSEGS)) (@mkst fx' R' pc' M' (seg_rom RSEGS)) -> frm_zero (@fp_csr fx) -> frm_zero (@fp_csr fx').
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepEs0 ()) [] "h01Mh12M'h21Rh32R'h42fxh53fx'h62pch73pc'p;1p;2p;;g00Ehj10Tg00J2j16Tg00\Wj11Tg00]5j12Tg00]Xj25Tg00^Dj14Tg00^fl;3Tg00`;R0g00Qm#0R1#6#1%01#0R1#0#0#0#1#2R2'5R3%11#2#4\2R1g00<3g00X`g00Z1f7R4f6R5f5R6f4R7f3R8f2R9f1R:f0R;M;3X11X01X72X62X33X23X50X40P4P5P6P7P8P9P:P;O8X11W0X72X62X33W2X50W4o"). Qed.
End FRMS0.

(* [comment removed for export] *)
Ltac frm_solve := FRMK.frm_solve_with FRMS0.msteps_fz_mkst.

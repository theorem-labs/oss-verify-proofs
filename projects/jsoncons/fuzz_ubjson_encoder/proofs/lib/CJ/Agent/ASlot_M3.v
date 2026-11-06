(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W10 ASlot_W11 ASlot_I ASlot_M0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require MallocFacts_inv4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ASlot_M3 () := "K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9halve_bigC13~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z8leb_specC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes7nat_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4UNITC13~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


Lemma halve_big_pos F : forall cnt sz, 1 <= cnt -> 0 <= sz < 2^18 -> 1 <= halve_big F cnt sz.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_M3 ()) ["CEIL_WRAP_1"] "p'0h06__sat1h14__x1h27__arithh34__ffh46__sat0h58__varmaph65__with71Fh84__x2h93cnth:2szh;2H1h<2Hah=2Hch>2Hsh?4__p1h@6__sat6hA4__x3hB2GThC1HhD2H0hE2H2hF2H3hG2H4hH2IHhI2LEhJ6__sat5hK1bi001bhL2b0hM1qhN1rhO1zp;1p;2p;3p;4p;5p;6p;7p;8g0000j17Tg000Nj21Tg000jj10Tg001Oj15Tg0024j2RTg002Qj22Tg002mj2<Tg003Hj3GTg004[j2^Tg005Cj3\Tg005gj2ZTg006Hj2TTg006bj1~Tg007Bj1{Tg007bj2NTg008@j1wTg008^j1qTg009Ij2ATg009lj2KTg00:Oj1gTg00;1j2dTg00;Sj2cTg00<?j3=Tg00<Yj3`Tg00=8j4_Tg00=jj28Tg00>Gj2[Tg00>ij2PTg00?FR0j3YTg00?jj2XTg00@Jj2ETg00@gj2DTg00APj2OTg00B1j4WTg00BRj3}Tg00C3j2|Tg00C\j2?Tg00DEj1>Tg00Ddj2VTg00EPj3STg00F0j1vTg00FNj4JTg00Flj5pTg00GPj1oTg00Gnj3nTg00HQj3MTg00I4j2jTg00IUj1iTg00Inj2@Tg00JNj2QTg00Jkj2hTg00KRj2kTg00L9j2lTg00L_j2mTg00MEj6fTg00Mij4FTg00NTj6eTg00O8j3rTg00O[j3sTg00PDj6tTg00Pbj4uTg00QCj7UTg00Qgj8xTg00RKj3bTg00S4j3aTg00S]j7zTg00TAR1f0R2'1p=6f2R3g00T_R4g00U>R5P5g00U^R6g00V>R7f1R8g00V\P2CFg00WCR9FUp=9f3R:P4P5P5P6P3P8P2Gxp=4%02#0p=H%02#0#0#0p=]%02#0#0#0#0#0#0#0p=BAb782p=3%52#5#5#5p=:%52#5p=yAa782p=;P7P8g00WcP2CFp=IP8P4P5P5P6P2P9FUp=CP3P4P5P5P6P8P2Fzp=Lg00XJR9g00XiR;#7R</18R=%68%0;R>#7R?%0>R@#5#0RA#7RB'RRC,28'<RDf4RE?G:3,1<[[^:7^97RFX791^?BRG121?RH%6B121C[RI[RJ%6?RKg00YNRLA\?B8UW<RB%6C\LRL^<KRMP8g00Yj1Z1?'TPHeRNO1ROPIg00ZPRP#~RQ%{PRR1N78RS%w7RT%q7RU1A7<RV1K7;RW59URX%g5RYPXC41dU6RZP2P3g00[<R[g00[\R\'T1c23==[\dA`718C_R\b3b5b6X17R]11<2R^P=[^17R_P2f7R`f5RaO2b2b0b4b0g00\<Rb?G:3,1<eX>DX==X:7X97%H@Rc#]#BRd#7Reg00\['8Rf183:Rg'[11fg12gf1Pfg3Y18:E,PfP[P018EaR0,1f120fP[P7P8f9R[1X`<R0f6Rg3GP`n0100000020000,1<P818agRh,1ff8RiP0PgP71R?<,E`P^XO7PGPJPBPMPOPI%Hd#7,D7RdP71O7<P;1O71CW9}7;,|71?7bR^'3'3%5;#0#B#B#5R;#7,D7%>bRb#>Rj#>Rk#>Rl#>,?7Rm1?7lRl'3'3%:>#:#:#:#0#5#y#:#:#:#:#7,D713m^'31?7kRk/3l,3d1?7jRj,3k,3d%H;#B#B#7,D71?7bRb,3j'3';';';';';g00]iR;'V=SPQPRP71N73P8%v7RdCJPTPUPU1A71Rl1A7?Rm59UPYPUPUP4P5P5P6DpPY%oA9n7mRA99UlC4C4PYPU1A7e%7cRc,A75M71K7>R>=M7W59UPYPUA9Ul>1I>A,CU5LUPYPUPXPYA9UmWC4C4C4C4PZP\b3b5b6X17X87PL\K18ec1838'1%6:12:C'<11<:Rc11?E[[[[^17^87P2f:Ref;RKP3PEPiP[O6b2b0b4b011?`1ji?A=7?1RL#i1E[?,8?1@[?'Q9=7[[1h[?1@e?Rn#612n?'<\H1ke?12?11@K?RH,2?11H1'<[1lK?f<RH/E?==71\L1mH?f=R1/@?==71\L1E1?P7f>/@?P7PaPNO1%62RN122?'<PGPJPBPMPOPIp-0R11D7?/3^,;b,;j,;k/V;=SPQPRP7P71N7:P3PdCJP8PdCJPTPUPUP4P5P5P6PaEf1K7@R@/Im,CU5LUPYPUPUPUP4P5P5P6P7Pmg00^UR6PlCF,CUEePYP7P>P6AM7mW=r7@CF,CUC4PYPUA9Um>PYPXC4C4C4PZP\b3b5b6X17X87XA7W?123?,<:g00_<\L18?3/QE9=7:[11?:Pc[[[^17^87^A7^?1P2%6aPafDPgPEPKPHO7b2b@bJb@b;bNbMbGbFbEb;bDbCP0PGPJPBPMPOPIPQPRPdPTA9UlVPZP\b3b5b6%6<P2b2b0b4b09s`<EtPGPJPBPMPOPIPQPRPSPTPUA9UlW1IWA,CU5LURUPYPUC4PZP\b3b5b6X17122C,<NPD[^17P2PePiO2b2b0b4b0O4WIP2O112hfPGPJPBPMPOPIP]P_P2PKP[O2b2b0b4b0WBP2O1n200210000000021100011000bLbK%>a?G:3,1<eX>DX==X:7X97XHFX79P2CuX79P2O1W7o"). Qed.
End CEIL_WRAP_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

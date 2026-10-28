(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3 BothPlanCore BothPlan BsImages BsPlanImages.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BsSmearCode () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00C7ARocqVerifyHarness?AgentSubmission3bpB5Start8BothPlan2AP7x_smearK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C6ARocqVerifyHarness?AgentSubmission3bpB5Start8BsImages6ASAN_HI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions9bv_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relC35stdpp9decidableEbool_decide_eq_true_1C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes6option01C35stdpp9decidable;bool_decideK47Corelib4Init5Logic3and01C6ARocqVerifyHarness?AgentSubmission3bpB5Start<BsPlanImages5ASEGSK47Corelib4Init5Logic4True01".
Import AX2. Import AP.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Lemma asan_smear_x : 0 <= x_smear ASAN_H /\ x_smear ASAN_H + 112 < 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_BsSmearCode ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__witp;1p;2p;3p;4p;7g0000j12Tg000Uj15Tg0013j2>Tg001[j24Tg0027j23Tg002Sj2LTg0030j3BTg003Tj1@Tg0044j1?Tg004Tj1=Tg0052j1<Tg005Pj1;Tg006;j26Tg006^j10Tg007Cj4:Tg007nj3NTg008Qj1MTg008oj3KTg009Rj7HTg00:6j2GTg00:Xj2ATg00;2j2CTg00;^j3DTg00<8j3ETg00<Wj4FTg00=Ij29Tg00=fj27Tg00>Aj1ITg00?Cj7JTf0R0#2#2p=1f1R1g00?gR2g00@FR3P3g00@fR4P0g00AFFJp=8g00AfR5#2R6#5R7%26#1#1R6#5R8'>g00BKR9/4713981L78R:,49[[1397R;g00BiR<AB781UW0139:\<^0;g00CER;#@%?;g00D1R;#=%<;%;;R<P2P3P3P4P;16;9g00DO%05#1#0#0#2#0#1#0#0#0#2#0#1#0#1#5R3,6;R2C:,8<P;%05#0#1#1#5R5,6;9N;2g00E616;7%M65K;C:,8<FH1G<4P0f2R<g00E]R4g00F=R6'A1C0<=D46dAE;91CFb2b5b613931935/4:'7P0b1b3b4g00F]#IR0,391905/4:'7eo"). Qed.

Lemma asan_smear_fwa :
  fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H)) = Some (0x00155593%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 4)) = Some (0x55555637%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 8)) = Some (0x333336b7%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 12)) = Some (0x0f0f1737%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 16)) = Some (0x010107b7%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 20)) = Some (0x00b56533%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 24)) = Some (0x5556059b%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 28)) = Some (0x3336861b%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 32)) = Some (0xf0f7069b%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 36)) = Some (0x1017871b%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 40)) = Some (0x00255793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 44)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 48)) = Some (0x02059793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 52)) = Some (0x00f585b3%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 56)) = Some (0x02061793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 60)) = Some (0x00f60633%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 64)) = Some (0x02069793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 68)) = Some (0x00f686b3%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 72)) = Some (0x02071793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 76)) = Some (0x00f70733%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 80)) = Some (0x00455793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 84)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 88)) = Some (0x00855793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 92)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 96)) = Some (0x01055793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 100)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 104)) = Some (0x02055793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 108)) = Some (0x00f56533%bv : bv 32).
Proof.
ltac2:(KReplay.run1 (kr_t_BsSmearCode ()) [] "p%0p;1p;3p;2p;6p;4g0000j10Tg008Qj1QTg00G[j1WTg00H>j1STg00>Aj1[Tg006^j11Tg00;^j32j1VTg00=fj26Tg00H`j1UTg00IHj2TTg00Iej64Tg00:Xj2RTg00J=j3OTg00Jej2KTg00KKj2JTg000Uj1BTg00LMj3LTg00M0j2NTg00=Ij2PTg00MRj2ZTg00N0j4YTg00NKR0f1R1f0R2'K'Jp=X%12#0p=8%02#1p=:%12#0#0p=?f2R3%12#0#0#1#1#Bg00OLR45L1'Np=@%B2,P1,K3,J0p=7%12#0#1#0p=C%12#1#0#0p=I%12#0#1#1p=A%12#B=L14,N3p=>%02#1#1#0p=M%12#1#0#1p=;%12#1p=H%02#0p=9%12#0#0#1p=G%02#0#1#1p=E%02#0#1#0p=D%02#0#0#0p=F%12#0#1#1#1#1#0#0#1#0#0#1#1#B=L14,N3p=<%02#B,P1,K3,J0p==g00E]R01Z12g00F=R432p=3f5f4f3?O31P2CYp=5g00AfR2#0R3#0R1#0R5#0R6#0R7#QR8#WR9#SR:%07R;#QR<g00F]#[R='XS00%13R3#0R>#8R?#1#:#:#:R@#?RA9@98S0132RBA7<=1S02%0@#8#C#I#:#A9>98S0352:R@A7<=5S04%12R2#0RC#0RD#1RE#8#MRF#M#M#;#:#A9>98S0552:RGA7<=DS06%12R2#8RH#0RI#0#:#H#8RJ#9#A#G#A9>98S0752:RKA7<=6S08%0;#8RL#9#E#;#A9>98S0952:RM%0>R>97<=S0:%13R3#0RN#8#A#D#G9@98S0;52:RO%0DRD97<=S0<%9A#D#I#;9>98S0=52:RA%92R297<=S0>%;F#9#E#F#;9>98S0?52:RFA7<=7S0@%HJ#8#F#;#9#;9>98S0A52:RJ%11R1#0RP#0RQ97<=S0B%HL#I#E#8#9#;9>98S0C52:RL%0>R>97<=S0D%CP9<98S0E52:RP%0NRN97<=S0F%1HRH#:RR#0#H#D#G9@98RS52:RT%0DRD97<=S0G%1;RU#:RV#?9<98RW52:RX%1CRC#9RY97<=S0H%?R#D#;9@98RR52:RZA=<=2S0I%1URU#0R2#0#99<98R[52:R\A7<=IRI%1HRH#0R]#0#F#I#:9@98R^52:R_A7<=;R;%?29<98R252:R`%85R59=<=Ra%1]#F#;#:9@98R]52:RbA=<=QRQ%8U#99<98RU52:Rc%?197<=R1%8H#9#E#G9@98RH52:RdA=<=>R>%C59<98R552:ReA=<=?R?=2:SRfA=<=NRN%86#C9<98R652:Rg%?397<=R3=2:SRhA=<=DS0J%87#C9<98S0K52:R7%9E97<=S0L=2:SREA=<=YS0M%0V#89<98S0N52:RV%?C97<=S0O=2:SR='6R<'6RC'6RY'6RD'6Ri'6Rj'6Rk'6Rl'6Rm'6Rn'6Ro'6Rp'6Rq'6Rr'6Rs'6Rt'6Ru'6Rv'6Rw'6Rx'6Ry'6Rz'6R{'6R|'6R}'6PBP:P:%V:R~%U8,T9R9Q00Q01E4R81R04R413B8dP@P}P@P:P:P~P9Q02Q03E4R}P413@}dPGP|PGP:P:P~P9Q04Q05E4R|P413G|dPKP{PKP:P:P~P9Q06Q07E4R{P413K{dPMPzPMP:P:P~P9Q08Q09E4RzP413MzdPOPyPOP:P:P~P9Q0:Q0;E4RyP413OydPAPxPAP:P:P~P9Q0<Q0=E4RxP413AxdPFPwPFP:P:P~P9Q0>Q0?E4RwP413FwdPJPvPJP:P:P~P9Q0@Q0AE4RvP413JvdPLPuPLP:P:P~P9Q0BQ0CE4RuP413LudPPPtPPP:P:P~P9Q0DQ0EE4RtP413PtdPTPsPTP:P:P~P9Q0FPSE4RsP413TsdPXPrPXP:P:P~P9Q0GPWE4RWP413XWdPZPqPZP:P:P~P9Q0HPRE4RRP413ZRdP\PpP\P:P:P~P9Q0IP[E4R[P413\[dP_PoP_P:P:P~P9PIP^E4R^P413_^dP`PnP`P:P:P~P9P;P2E4R2P413`2dPbPmPbP:P:P~P9PaP]E4R]P413b]dPcPlPcP:P:P~P9PQPUE4RUP413cUdPdPkPdP:P:P~P9P1PHE4RHP413dHdPePjPeP:P:P~P9P>P5E4R5P413e5dPfPiPfP:P:P~P9P?PSE4R?P413f?dPgPDPgP:P:P~P9PNP6E4R6P413g6dPhPYPhP:P:P~P9P3PSE4R3P413h3dP7PCP7P:P:P~P9Q0JQ0KE4RCP4137CdPEP<PEP:P:P~P9Q0LPSE4R<P413E<dPVP=PVP:P:P~P9Q0MQ0NE4R<P413V<dP:P:P~P9Q0OPSE4RSP413=Sd5O=E5E5E5E5E5E5E5E5E5E5E5E5E5E5E5E5E5E5E5E5E5E5E5E5E5E5E5o"). Qed.

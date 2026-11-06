(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac MState RzCPS.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA Layout RT_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_fk () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib2K53A235RT_fk7ret_stFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6ret_stC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsc69OSSVerify5KrLib2K53A235RT_fk8fs_agreeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic3and00c69OSSVerify5KrLib2K53A235RT_fk9fs_calleeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics5Riscv3Sem7reg_getK47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C47Corelib4Init5Logic3notI47Corelib4Init9Datatypes4list00C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init5Logic2or00I47Corelib7Numbers7BinNums1Z00c69OSSVerify5KrLib2K53A235RT_fk9FS_CALLEEC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic5False00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC47Corelib4Init5Logic9False_indC69OSSVerify5KrLib2K56Common8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MStateAreg_get_set_otherC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C69OSSVerify5KrLib2K53Lib6MState@reg_get_set_sameC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:in_map_iffC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes4list02C46Stdlib5Lists4List8map_consI47Corelib7Numbers7BinNums1N00".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition FS_CALLEE : list Z := [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition fs_callee (r : reg) : bool := existsb (Z.eqb (bv_unsigned r)) FS_CALLEE.

(* [comment removed for export] *)
Definition fs_agree (F F' : bvmap 5 word) : Prop :=
  forall r : reg, fs_callee r = true -> reg_get F' r = reg_get F r.

(* [comment removed for export] *)
Definition ret_stF (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (F : bvmap 5 word) (m' : mem)
    (ms : machine_state) : Prop :=
  ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms /\ fs_agree F (ms_fregs ms).

Lemma ret_stF_ret_st : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v F m' ms,
  ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v F m' ms ->
  ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_fk ()) [] "h01Fh11Hh22H0h32_Hh42gph52m'h62msh72rah82s0h92s1h:3s10h;3s11h<2s2h=2s3h>2s4h?2s5h@2s6hA2s7hB2s8hC2s9hD2sphE2tphF1vp;1p;2p;Dp;Cg0000j10Tg000Uj12Tg0013j13Tg001Vj16Tg002;j29Tg002gj18Tg003IlD7Tg004BlC1Tg005=j14Tg006=j25Tg0077#0R0#0#0R1#0#0#0#2#3R2%60#2/92%21#3#8\2g007\fCR1fBR0fAR3f@R4f?R5f>R6f=R7f<R8f;R9f:R:f9R;f8R<f7R=f6R>f5R?f4R@f3RAf2RBf1RCf0RDMD7g008cfDREP1P0P3P4P5P6P7P8P9P:P;P<P=P>P?P@PBPCMC1%4C,5AfERFPEP1P0P3P4P5P6P7P8P9P:P;P<P=P>P?PAPBMC1PDfFPFPEP1P0P3P4P5P6P7P8P9P:P;P<P=P>P@PAMC1%4@,5>PCW3W1PCPDO2n2001000000120000000W2W6W5W0XF2X;2X:2XC2XB2XA2X@2X?2X>2X=2X<2X92X82XE2X42XD2W7o"). Qed.

Lemma fs_agree_refl : forall F, fs_agree F F.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_fk ()) [] "h01Fh12_Hh21rp;1p;2p;3g0000j10Tg001Vj19Tg000Uj12Tg0013j11Tg002;j28Tg009>j17Tg00:9j34Tg00:Sj23Tg00;=j25Tg006=j26Tg0077#0R0#9#2R1%00#0#0#0#0#2#1R0'8%11g00;Wf0R1#7g00<734f2f1'3,50W1W21611eW0o"). Qed.

Lemma fs_agree_trans : forall F1 F2 F3, fs_agree F1 F2 -> fs_agree F2 F3 -> fs_agree F1 F3.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_fk ()) [] "h02F1h12F2h22F3h32H1h42H2h52Hrh61bh71rp;1p;2p;3p;6g0000j10Tg001Vj19Tg000Uj14Tg0013j12Tg002;j28Tg006=j25Tg009>j17Tg00:9j33Tg00:Sj21Tg00<Wj66Tg0077#0R0#9#4R1%00#0#0#0#0#4#2R0'8R2f2R3f1R4'5R5%21g00;Wf0R1#7g00<733P0f5/14f7/139301X60f3P4P1O2f4R0/14P3P4P1O2E6W5W71503eX45W3X22X12W0o"). Qed.

Lemma fs_agree_get : forall F F' (r : reg), fs_agree F F' -> fs_callee r = true -> reg_get F' r = reg_get F r.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_fk ()) [] "h01Fh12F'h21Hh32Hrh41rp;1p;2p;3g0000j10Tg001Vj17Tg000Uj12Tg0013j11Tg002;j26Tg006=j25Tg009>j14Tg00:9j33Tg0077#0R0#7#2R1%00#0#0#0#0#2#1'6R0%11f2R1f1R2'5g00;W%42g00<733P2P1f0O2W3W2W4X10W0o"). Qed.

(* [comment removed for export] *)
Lemma fs_agree_of_keep10 : forall F F' : bvmap 5 word,
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) -> fs_agree F F'.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_fk ()) [] "p'0h01xi001xh11Eh22H0h32Hxh41Ah52Hrh64__p1h71fh81lh91mh:1nh;1Ch<1Fh=2F'h>1Hh?7__arithh@4__ffhA8__varmaphB5__withC1khD1rhE1zp;1p;2p;3p;6p;5p;8p;4p;7g0000j11Tg001Vj16Tg000Uj1ATg0013j1@Tg002;j2^Tg00=5j24Tg00=_j12Tg00>=j1;Tg00:Sj2?Tg00:9j3:Tg009>j1GTg00>Vj1ETg00?6R0j3CTg00?Rj3=Tg008cR1j29Tg00?iR2j2>Tg00@Cj3XTg00@fj1Wj27Tg00ACj2VTg00Acj6Uj7]Tg00B?j1TTg00B_j1RTg00C=j1QTg00C[j1LTg00DFj5JTg00Djj1ITg00ELj6HTg00F0j8MTg00FTj2NTg00;=j2OTg00G6j2PTg00Gbj3FTg00HAj4STg006=j2\Tg00I3j2DTg00IVj4[Tg00JAj7ZTg00Jej7YTg00KIj2BTg00KcR3f1R4f0R53:p=5g00;WR6g00<7R77:5p=0g00LAR89=35p=<1D35p=Kf4R9g00M<R:g00M[R;P;g00N;R<f3R=P:P;P;P<P3f2R>,D3g00N[P4C[g00OBFZP5FYp=3A:39=A:3>4/B5'Bp=8g0077R?#1R@#6RA#ARB%1@R@#1RC#1#1#1#A#@RD'^RE%@BRF14B5%1ARG#2RH'5#;1?>41?=45:D[]C%G5#0P>P4P0p4p710R0P6\5RD%E4RIP1AC>45#0A=95>P=P5O1#0'9X0=,>=[RJA==54P>P5O1#0'9X0>,>>AC=>4#0RK[f5RL?=5=P9P5O1#0'9X09,>9\KAX>45P4n2001000000120000000W8W7W4PJ^8I^7D^40P5P314B>#WP8P4O4%<5R814B=/75#0'9X03,>3P2P314B9R2/75#0,98X03152H#;P5f6R2,4B/75#0,98P1%<4f7,4B/74#0f8R0,4B/5H#;P5%<=f:,4B/79#0P11745#015>4[R1154517>4#0R9[15=>\91V45P4n2001000000120000000X93X:3P1^93^:3P5f<,4BR1P2P4O31512f=,4B/5HR1P3f>,4Bf9RB,55XE3P4PHP5EU15H0P3PHg00ObR0^38X03%<Hp-0R8g00P?R2#T%E2%R3%Q3%L3R2P:P;P;P<P2P2%2CRC%KHR9P2P2%6@R@#2R=P9P2P2%1@#2RDP9P2P2%6@#2R@P9P2P2%1G#2RIP9P2P2%6G#2RGP9P2P2%6ARA#1#2RJP9P2P2%6A#2RAP9P2P2%6?#1R?#1RK#1#2RMP9P2P2%6K#2RKP9P2P2%6?R?#1#2RNP9P2P2%6?#2R?P9P2P:P;P;P<DJD3D3D3D3D3D3D3D3D3D3D3D3%I;P2P:P;P;P<P>EHGM1N2<P5P>1O671P5>#0dg00Pk=F34CSb@bAbBW6PCPHP=PHPDPHP@PHPIPHPGPHPJPHPAPHPMPHPKPHPNPHP?PHP0D8D8D8D8D8D8P4[^68P5P0P4O2b?W3PBP5PLF]b1W;%;1eb1b2W1W3P4P5O2n2001000000121000000W2X03P4P5O2n2001000000121100000b5b2O2W5XDF1\>4eW>X=EW<o"). Qed.

(* [comment removed for export] *)
Lemma fs_agree_set_other : forall F F' (k : reg) v, fs_callee k = false -> fs_agree F F' -> fs_agree F (bvmap_set k v F').
Proof.
ltac2:(KReplay.run1 (kr_t_RT_fk ()) [] "p'0h01Eh11bi001bh22H0h32Hrh42Hkh51ah61eh71kh81rh91Fh:2F'h;1Hh<1vp;1p;2p;3p;5p;6p;7p;8g0000j14Tg001Vj1FTg000Uj1:Tg0013j19Tg002;j2ETg009>j16Tg006=j2<Tg00QIj31Tg00;=j2=Tg00:9j30Tg00R6j57Tg00:Sj22Tg00Rfj3DTg00Acj68j7CTg00S[j2;Tg00T:j2BTg00<Wj8?j6>Tg00>=j1@Tg00U=j5ATg00;WR0f0R1g00VAR230p=3g00<7R39001p=5g0077#4R4#F#:R5%44#4#4#4#4#:#9R4'ER6%95R7f1R8#6#3f4R9f3R:'<%61R;#5R<f5R==158P01=01f6R>f2R?515=001P0f8R@=159=001P5P4f9RAP@f:RBD7/2=f;RC/2=RD504]0P8f7RE=15:RF#5g008cA1581#5A07?8[RGA0781A15?8#5RH[A07:?\HAD581P8n2001000000120000000X17X57PG^17^57P1PAP=P8O3A07A=P7PBP5P4f<RGPCf=RHD7/28f>RI/28504^3<X87%6B#5P0%6C%51X10P1P2PAE8A0023P0P2P0p-0RCP1g00ObRBg00VaR<n0110000020000X60g00W=RJP3P1E8PBP5P4PHPGPID7/2Hf?/2H504/;1b2b3W3P>P1P=FCb0b2W0%3FP412A9A041DX14P=P9P:O2P5P4P@PEPAD7/29PAP@P9PEA07@9R@P7P=%3;A158E#3PB]0]4X77%6=#3A15>>#3P0A15EE%31X10P1P31B5EE8A0032P0P3P0PCP1P<PBn0110000020000X60PJP2P1E8PB1;B1b2b0W0W4PAP1PEP8G?W2%@@eDAE>W0n0110000020100P1O1b0b1W3X87P5P4P:P?P9D7,<=eW;W4X<4W7X:6W9o"). Qed.

(* [comment removed for export] *)
Lemma fs_agree_set_same : forall F F' (k : reg) v, v = reg_get F k -> fs_agree F F' -> fs_agree F (bvmap_set k v F').
Proof.
ltac2:(KReplay.run1 (kr_t_RT_fk ()) [] "p'0h01Eh11bi001bh22H0h32Hrh42Hvh51ah61kh71rh81Fh92F'h:1Hh;1eh<1vp;1p;2p;3p;5p;6p;7p;8g0000j13Tg001Vj1GTg000Uj1<Tg0013j17Tg002;j2FTg00:Sj21Tg00:9j30Tg006=j2;Tg009>j19Tg00QIj32Tg00;=j2=Tg00R6j55Tg00Rfj3ETg00WYj3DTg00<Wj68j8ATg00Acj7Cj6:Tg00T:j2BTg00S[j2@Tg00>=j1?Tg00U=j5>Tg00;WR0f0R1g00<7R230p=4g00VAR39001p=6g0077#3R4#G#<R5%34#3#3#3#3#<#7R4'FR6%75R7f3R8f1R9'19041f4R:/;8%91#4R;f5R<=259P01=01f6R=f2R>525=001P0f8R?=25:=001P5P4f9R@P?f:RAD5/1<f;RB/1<RC504]0P9f7RD=258RE#4g008cA2591#4A07>9[RFA0791A25>9#4RG[A078>\GAE591P9n2001000000120000000X17X57PF^17^57P1P@P<P9O3A07@<P7PAP5P4f<RFPBf=D5/19f>RG/19504^3;X77%9A#4P4PA11GF9041X14P@P5P4PBPAPFD5/1BADFBAE8W3P=P1P<FCb0b2W0%6EP411@:A041CX14P<P:P8O2P5P4P?PDP@D5/1:P@P?P:PDA07?:REP7P<11F1904@A259D#6g00ObRF]0]4X67A04?CA25==#6P0A25DD%61X10P1P21B5DE:A0023P0P2P0p-0P1g00VaPFn0110000020000X;0g00W=P3P1E:PF1@F1b2b0W0W4P@P1PDP9GAW2%?EeD>E8W0n0110000020101P1O1b0b1W3X77P5P4P8P>P:D5,;<eW:W4X<4W6X96W8o"). Qed.

(* [comment removed for export] *)
Lemma fs_callee_cases : forall r : reg, fs_callee r = true -> In r (map (Z_to_bv 5) FS_CALLEE).
Proof.
ltac2:(KReplay.run1 (kr_t_RT_fk ()) [] "p'0h02Ekh11Hh22Hkh31kh41xi001xh51Ah61fh71lh81nh91Bh:2b1h;2b2h<1mh=1yh>2H0h?1rh@1zp;1p;3p;2p;4p;5p;6p;7g0000j1<Tg001Vj1=Tg000Uj1MTg0013j1@Tg009>j1VTg00>Vj1FTg00?6R0j3ETg00?Rj38Tg008cR1j2>Tg00?iR2j2ATg00@Cj3HTg00=5j24Tg00@fj1Uj2?Tg00X\j1Tj2BTg00YBj4CTg00ACj2RTg00:9j3;Tg00Y^j5QTg00Z=j3LTg00=_j16Tg00B?j1JTg00<Wj6ITg00Zaj4NTg00[<j4OTg00[Vj3PTg00;=j2GTg00Acj7STg00;WR3f0R4g00<73;p=5g00KcR5g00LAR6784p=Df1R7=;54p=0f2R8/47=;54p=11B74,48p=KAP574p=:A8574p=3f3R91B87'4=;54p=21G54p=9P5f5R:f4R;P9P8P7P4FSp=7g0077R<#<R=#=R>#MR?#@R@%V4#5P0p4p710R0P3\4R3%F7RAP1AE874#5A8;48P9P4O1RB#5'>X49,A9[RCA8947P8P4O1#5'>X48,A8AE987#5RD[A8:49P;P4O1RE#5'>X4;,A;\DAH874P7n2001000000120000000W7W6W5PC^7A^63^50P4P514?8#UP6P7O4%D4R014?9/?4#5'>X45,A5P2P514?;/?4#5,>0X45P5P@%T?R2P6CCR398@;P4f6RA,4?/?4#5,>0P1%D7f7,4?/?7#5f8RC=8@3P4%D9f:R3,4?/?;#5P11?74#51087[RD10741?87#5RF[1098\F1R74P7n2001000000120000000X<5X85PD^<5^85P4f<RD,4?RFPAP7O310FAg00\6RFp4p710RGPFp4p7210RFP7\7RH%F8RIP1P;P9P8P7CC9894A;:E8A8A49'>X4:,A:RE[A;;B7A8:48'>X4;,A;P:P;P9P8CC98;7[RBPAP:P;P9CC98:8\EP;P9P8P7P4DQP4n2001000000120000000X=8W7W6W9W5PB^=8^7I^6H^9F^5GP4P5P@P2P6f>R6P51B?4f?R25;@/>0X45PC1B?C=;@6%DCg00\SR@%@4R0%@7RGP1%@8?;7414979198R1[14849187%@9?;87[RF%@;?;98\1AL874P4n2001000000120000000W;W:W8PF^;G^:0^8@P4P?f9R@,B?P2P5P@AK??3R0/04X@5g00KIRG%<=R=#<#6RF/0@%==R=#6R1%<=#6R9%==#6R=%<>RH#<#6RI%=H#6RH%=>R>#<#6RB%=>#6R>%=<#<R<#<RE#<#6RJ%=E#6RE%=<R<#<#6RK%=<#6R<%J5RL':RM':RN':RO':RP':RQ':RR':RS':RT':RU':RV':RW,3@1003P:10F3PFfBR:=1?4P?P?P7P7C2R0]0X35fAR@=1?F%9FP?P?PFPFC2dW0f;RFP4P;E7W1P4O1133WPG101F13FVP?P?PDPDC2P4101DP1fDRF=1?4P0]0X35fCRW=1?1%91P?P?P1P1C2dW0f=R1P4PAE7W1P4O113DVPG1091131UP?P?P6P6C2P41096P9fFR1=1?4P0]0X35fERV=1?9%99P?P?P9P9C2dW0P2P4PCE7W1P4O1136UPG10=2132TP?P?f@RUPUC2P410=UP=fHRC=1?4P0]0X35fGR9=1?=%9=P?P?P=P=C2dW0P@P4P3E7W1P4O113UTPG10I@13@SP?P?P:P:C2P410I:PIfJR@=1?4P0]0X35fIRT=1?I%9IP?P?PIPIC2dW0PWP4PDE7W1P4O113:SPG10HW13WRP?P?PFPFC2P410HFPHfLRW=1?4P0]0X35fKRS=1?H%9HP?P?PHPHC2dW0PVP4P6E7W1P4O113FRPG10BV13VQP?P?P1P1C2P410B1PBfNRV=1?4P0]0X35fMRR=1?B%9BP?P?PBPBC2dW0P9P4PUE7W1P4O1131QPG10>9139PP?P?PCPCC2P410>CP>fPR9=1?4P0]0X35fORQ=1?>%9>P?P?P>P>C2dW0PTP4P:E7W1P4O113CPPG10JT13TOP?P?P@P@C2P410J@PJfRRT=1?4P0]0X35fQRP=1?J%9JP?P?PJPJC2dW0PSP4PFE7W1P4O113@OPG10ES13SNP?P?PWPWC2P410EWPEfT=1?4P0]0X35fS=1?E%9EP?P?PEPEC2dW0PRP4P1E7W1P4O113WNPG10KR13RMP?P?PVPVC2P410KVPKfV=1?4P0]0X35fU=1?K%9KP?P?PKPKC2dW0PQP4PCE7W1P4O113VMPG10<Q13QLP?P?P9P9C2P410<9P<fX=1?4P0]0X35fW=1?<%9<P?P?P<P<C2dW0PPP4P@E7W1P4O1139Lg00ObP?P?PTPTC2P4n010000000W2P4O1n200100000021000010000W2P4O1n200100000021000010000W2P4O1n200100000021000011000W2P4O1n200100000021000011000W2P4O1n200100000021000011000W2P4O1n200100000021000011000W2P4O1n200100000021000011000W2P4O1n200100000021000011000W2P4O1n200100000021000011000W2P4O1n200100000021000011000W2P4O1n200100000021000011000W2P4O1n20010000002100001100014?2P8EIO4b1P;CNCOO6b1b0b1W0W2P7P4O2n2001000000121000000W1X35P7P4O2n2001000000121100000b1b>W1W?o"). Qed.

(* [comment removed for export] *)
Lemma fs_reg_get_set : forall (R : bvmap 5 word) (k r : reg) v,
  reg_get (bvmap_set k v R) r = if bv_eqb k r then v else reg_get R r.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_fk ()) [] "p'0h01Eh11bi001bh21Hh31kh41ah51Rh61eh71rh81vp;1p;2p;3p;5p;6p;7g0000j12Tg001Vj1DTg000Uj18Tg0013j16Tg002;j2CTg00QIj31Tg00;=j2<Tg00:9j30Tg00R6j57Tg00:Sj24Tg00Rfj3;Tg00WYj3:Tg00<Wj6Bj7>Tg00T:j2ATg00Acj69Tg00S[j2=Tg00>=j1?Tg00U=j5@Tg00;WR0f0R1g00<7R230p=5g00VAR39001p=3g0077#2R4#D#8R5%24#2#2#2#2#8#6R4'C%65R6f2R7f1R8515R9P01<01f3R:=157=001P0f5R;f4R<515=001P5P4f6R=P<f7R>D7/4;P0P4P8P<14>;n0100000020000504]0P8A15<:R?#5g008cA1581#5A0678[R@A0681%59R9[A06:7\9A;581P8n2001000000120000000X16X46P@^16^46P1P=P;P8O3A06=;P6P=P5P4P1P=f9D7/4>=04=X36f8?:=;P>P1EBb0b2W0%3?P=P;P<P:A06;<R<P6P;A151=#3g00ObR:]0X36A15;;#3P0A15==%31X10P1P21A5=E9A0023P0P2P0p-0P1g00VaP:n0110000020000X60g00W=P3P1E9P:1=:1b2b0W0P=P1P8F>W2%?<eD@W0n0110000020000P1O1b0b1X84X76W3W5o"). Qed.

Ltac fs_eqb_simp :=
  repeat match goal with
  | |- context [bv_eqb ?a ?b] => let v := eval vm_compute in (bv_eqb a b) in change (bv_eqb a b) with v
  end; cbv iota.

Ltac fs_agree_tac :=
  first
    [ apply fs_agree_refl
    | assumption
    | let r := fresh "r" in let Hr := fresh "Hr" in
      intros r Hr; apply fs_callee_cases in Hr; cbn [map In] in Hr;
      repeat (destruct Hr as [<-|Hr]); [..| destruct Hr];
      rewrite ?fs_reg_get_set; fs_eqb_simp;
      repeat match goal with
      | H : fs_agree ?F1 ?F2 |- context [reg_get ?F2 ?r] => rewrite (fs_agree_get F1 F2 r H) by reflexivity
      end;
      reflexivity ].

(* [comment removed for export] *)
Ltac fs_reads :=
  repeat match goal with
  | H : fs_agree ?F ?F' |- context [reg_get ?F' ?r] =>
      rewrite (fs_agree_get F F' r H) by reflexivity
  end.

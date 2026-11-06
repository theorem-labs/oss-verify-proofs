(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec StepTac StoreOk StreamSim.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocImg.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Export RelocSpan CanonSpans.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_RelocRW () := "c69OSSVerify5KrLib6Common4Musl7RelocRW>rl_dwin_boundsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl7RelocRW?dwin_bounds_chkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc9rl_img_loC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC69OSSVerify5KrLib6Common5Reloc5Reloc8rl_rw_loC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC69OSSVerify5KrLib6Common5Reloc8RelocImg:rl_data_loC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common5Reloc5Reloc9rl_img_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic3and01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic6eq_indK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C46Stdlib6ZArith4Zdiv8Zmod_0_rC56Stdlib6ZArith6BinInt1Z7add_0_rK47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205".      (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition dwin_bounds_ok (img_lo rw_lo data_lo img_hi dD1 dD1b dD2 dB dBend : Z) : bool :=
  (0 <=? img_lo) && (img_lo <=? rw_lo) && (rw_lo <=? data_lo)
  && (data_lo <=? 0x1f3f8 + dD1) && (0x1f440 + dD1b <=? 0x1f440 + dD2)      (* [comment removed for export] *)
  && (data_lo <=? 0x1f440 + dD2) && (0x1f624 + dD2 <=? 0x1f630 + dB)
  && (0x300b0 + dBend <=? img_hi) && (img_hi <=? 2 ^ 32)
  && (dD1 mod 8 =? 0) && (dD2 mod 8 =? 0) && (dB mod 8 =? 0).

Definition dwin_bounds_chk {RL : Reloc} {RD : RelocData RL} : bool :=
  dwin_bounds_ok rl_img_lo rl_rw_lo rl_data_lo rl_img_hi dA_1f3f8 dA_1f430 dA_1f440 dA_1f630 dA_2fcb0.

Class RelocRW (RL : Reloc) (RD : RelocData RL) := {
  rl_dwin_bounds : dwin_bounds_chk = true;
  rl_rw_hull : hull_okb = true;
  rl_rw_spans : spans_check canon_spans = true;
  rl_rw_orders : orders_check canon_spans canon_order = true
}.

#[export] Instance RelocSpans_of_RW {RL : Reloc} {RD : RelocData RL} {RW : RelocRW RL RD} : RelocSpans RL RD :=
  {| rl_hull_ok := rl_rw_hull; rl_spans_ok := rl_rw_spans; rl_orders_ok := rl_rw_orders |}.

Section RW.
  Context {RL : Reloc} {RD : RelocData RL} {RW : RelocRW RL RD}.

  Lemma rl_dwin_facts :
    0 <= rl_img_lo /\ rl_img_lo <= rl_rw_lo /\ rl_rw_lo <= rl_data_lo
    /\ rl_data_lo <= 0x1f3f8 + dA_1f3f8 /\ 0x1f440 + dA_1f430 <= 0x1f440 + dA_1f440
    /\ rl_data_lo <= 0x1f440 + dA_1f440 /\ 0x1f624 + dA_1f440 <= 0x1f630 + dA_1f630
    /\ 0x300b0 + dA_2fcb0 <= rl_img_hi /\ rl_img_hi <= 2 ^ 32.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocRW ()) ["RW"] "h01Hh12H8h22_Hh32H0h42H1h52H2h62H3h72H4h82H5h92H6h:2H7h;1mh<1np;3p;2p;1p;4g0000j3JTg0017j2ITg002?j1BTg003@j25Tg003]j1HTg004]j26Tg005;j2ETg006@j1;Tg006ej17Tg007Jj1<Tg007hj2?Tg008hj2>Tg009Ej1GTg00:Fj2FTg00:cj2ATg00;Cj2@Tg00;`j34Tg00<CR0j21Tg00<^j23Tg00=:j2DTg00=Zj4:Tg00>5j3CTg00>Of0R1g00>o3Cp=0%;1#;p=9%;1#7p==%71#7p=2%71#;p=8p,2RLR2p,2RDR3p,2RW3J1I23#0g00?OR4%B2R5'5R6%H2R7,55R8'6R91E23R3,57R:'6R;g00?mR<#;R=#9#=R>#7#9#9#9#=#2#<%7<R<#7R?#9#=R@#8RA#8RB#8,?2RC'>RD,53RE'6RF%;>R>#2#8#2#2#2#<RG%=@R@#8#2,?2'>RH%=A#9,?2RA,>GRG'5RI'6RJ153GRK'6RL%;>#2#8R>#7#8#2#</>ARM%;>#2#2#<%9B,?2RB'>R>'5RN'6RO%2=#2#2#2#=#9#2#2#<%=@#8,?2'>R@%G2R2'5R='6RP%<<%7?R?#2#<'FR<,52RQ'6RR%<?R?,AC/@4RC'6RS1AA?/@4RA'6RT1AB?/@4R?;41%0TRT%0?R?'1P0PTP?1345RB1357RU1373RV133DRW13HGRX133GRY13M>RZ13@2R[132<R\'1R]'1R^'1R_'1R`'1Ra'1Rb'1Rc'1RdP1f1Re94SA%0SRS%0ARA'1P0PSPAPdP1A4RCe%0RRR%0CRC'1P0PRPCPdP1A4PQe%0PRP%0QRQ'1P0PPPQPdP1A4O=e%0ORO%0=R='1P0POP=PdP1A4LNe%0LRL%0NRN'1P0PLPNPdP1A4JKe%0JRJ%0KRK'1P0PJPKPdP1A4FIe%0FRF%0IRI'1P0PFPIPdP1A4;Ee%0;R;%0ERE'1P0P;PEPdP1A49:e%09R9%0:R:'1P0P9P:PdP1A468e%06R6%08R8'1P0P6P8PdP1g00@RRdP015e1#0f2R0/3e[Rf13e1150e#0Rg[f3/30\g1De1Pen2001000000120000000X;dW<RgPf^;d^<dRdP1P2P<fTO3P\PgPdP1P@P2fQO3P[PgPdP1PMP>fNO3PZPgPdP1P3PGfKO3PYPgPdP1PHPGfHO3PXPgPdP1P3PDfEO3PWPgPdP1P7P3fBR3O3PVPgPdP1P5P7f?O3PUPgPdP1P4P5P3O3PBPBPcP1PUPbP0PVPaf4PWP`f6PXP_f8PYP^f:PZP]f<P[P\f>f@C:C:C:C:C:C:C:C:b0b1b:b1b9b1b8b1b7b1b6b1b5b1b4b1b3b1X:8X06PeP1O2n2001000010121000000b0X9:X09PeP1O2n2001000010121000000b0X8EX0;PeP1O2n2001000010121000000b0X7IX0FPeP1O2n2001000010121000000b0X6KX0JPeP1O2n2001000010121000000b0X5NX0LPeP1O2n2101000010121000000b0X4=X0OPeP1O2n2101000010121000000b0X3QX0PPeP1O2n2101000010121000000b0X2CX0RPeP1O2n2101000010121000000b0X2AX0SPeP1O2n2101000010121000000b0X2?X0TPeP1O2n2101000010121000000b0b0o"). Qed.

  (* [comment removed for export] *)
  Lemma rl_dDATA1_mod8 : dA_1f3f8 mod 8 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocRW ()) ["RW"] "h01Hh12_Hh21mh31nh42H0p;3p;2p;1g0000j3ITg0017j2HTg002?j1BTg003@j2ATg003]j1GTg005;j2DTg006@j15Tg006ej11Tg007Jj17Tg007hj2<Tg008hj29Tg009Ej1FTg00:Fj2ETg00:cj2?Tg00;Cj2:Tg004]j2=Tg00;`j3>Tg00<CR0j2@Tg00>5j3;Tg00A0j2CTg00>Of0R1g00>o3;p=2f2R2f1R3/A1'=p=6%51#5p=3%51#1p=8%11#1p=0%11#5p=4p,2RLR4p,2RDR5p,2RW3I1H45#2g00?OR6%B4R7'A%G4R87671D45R5768g00?mR8#5R7#3#8R9#1#3#3#3#8#0#7%18R8#1R:#3#8R;#4R<#4R=#4,<4R>'9765%59R9#0#4#0#0#0#7R?%8;R;#4#0,<4'9%8<#3,<4R<,9?R?36?65?%59#0#4R9#1#4#0#7/9<%59#0#0#7%3=,<4R='936%07#0#0#0#8#3#0#0#7%8;#4,<4'9%F4R436%78%1:R:#0#7'E764R4%7:R:,?>R>/:6R8'=R;1?<:/:6R<'=R71?=:/:6R:;>1%27R7%2:R:'@P0P7P:g00@RR=?;>6R9P1A>;<3%2;R;%2<R<'@P0P;P<P9P1A>483%24R4%28R8'@P0P4P8P9P1P01:31#2A;=23[R0A;=311:23#2R?[f3=;=2\?1C31P3n2001000000120000000X2=X3=P0^2=^3=P1P>P6P3O3P9P1b0b4X08X14P3P1O2n2101000000121000000b0X1<X0;P3P1O2n2101000000121000000b0X1:X07P3P1O2n2101000000121000000b0b0o"). Qed.
  Lemma rl_dDATA_mod8 : dA_1f440 mod 8 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocRW ()) ["RW"] "h01Hh12_Hh21mh31nh42H0p;3p;2p;1g0000j3JTg0017j2ITg002?j1BTg003@j21Tg003]j1HTg005;j2DTg006@j14Tg006ej12Tg007Jj16Tg007hj2<Tg008hj29Tg009Ej1GTg00:Fj2ETg00:cj2?Tg00;Cj2:Tg004]j2=Tg00;`j3@Tg00<CR0j2ATg00>5j3;Tg00A0j2CTg00>Of0R1g00>o3;p=8f2R2f1R3/11'=p=F%41#4p=5%41#2p=7%21#2p=0%21#4p=31=23/=1p=>p,2RLR4p,2RDR5p,2RW3J1I45#8g00?OR6%B4R7'1%H4R87F71D45R5,18g00?mR8#4R7#5#7R9#2#5#5#5#7#0#6%28R8#2R:#5#7R;#3R<#3R=#3,<4R>'9,153>%49R9#0#3#0#0#0#6R?%7;R;#3#0,<4'9%7<#5,<4R<,9?R?'1115?3>%49#0#3R9#2#3#0#6/9<%49#0#0#6%5=,<4R='9'1%07#0#0#0#7#5#0#0#6%7;#3,<4'9%G4R4'13>%68%2:R:#0#6'E,14%6:R:,?>/:63>R>1?<:R</:6R4'=R81?=:/:6R:;@1%88R8%8:R:'AP0P8P:g00@RR=?;<6R;P1A@>43%8>R>%84R4'AP0P>P4P;P1P01:31#8A;=23[R0A;=311:23#8R7[f3=;=2\71C31P3n2001000000120000000X2=X3=P0^2=^3=P1P<P6P3O3P;P1b0b4X04X1>P3P1O2n2101000000121000000b0X1:X08P3P1O2n2101000000121000000b0b0o"). Qed.
  Lemma rl_dBSS_mod8 : dA_1f630 mod 8 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocRW ()) ["RW"] "h01Hh11mh21nh32H0h42_Hp;3p;2p;1g0000j3ITg0017j2HTg002?j1@Tg003@j22Tg003]j1GTg005;j2DTg006@j13Tg006ej11Tg007Jj16Tg007hj2=Tg008hj28Tg009Ej1FTg00:Fj2ETg00:cj2>Tg00;Cj2:Tg00;`j3CTg00<CR0j2BTg00>5j39Tg00A0j2ATg004]j2?Tg00>Of0R1g00>o39p=<f2R2f1R3'?/?1p=;%31#3p=4%31#1p=7%11#1p=0%11#3p=5p,2RLR4p,2RDR5p,2RW3I1H45#<g00?OR6%@4R7'2%G4R8,271D45R5,283;g00?mR8#3R7#4#7R9#1#4#4#4#7#0#6%18R8#1R:#4#7R;#5R<#5R=#5,=4R>'8,25%39R9#0#5#0#0#0#6R?%7;R;#5#0,=4'8%7<#4,=4R<,8?R?'23;125?%39#0#5R9#1#5#0#6/8<%39#0#0#6%4=,=4R='8'23;%07#0#0#0#7#4#0#0#6%7;#5,=4'8%F4R4'2%68%1:R:#0#6'E,243;%6:R:,>>/:61><:/:63;R<1>=:R:/:6R=;C1%<<R<%<=R='BP0P<P=g00@RR>?9:6R4P1P01:31#<A9>23[R0A9>311:23#<R8[f3=9>2\81A31P3n2001000000120000000X1>X2>P0^1>^2>P1P:P6P3O3P4P1b0b3X0=X4<P3P1O2n2101000000121000000b0b0o"). Qed.
End RW.

Lemma mod4_add8 : forall c d, c mod 4 = 0 -> d mod 8 = 0 -> (c + d) mod 4 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocRW ()) [] "p'0h01Hh12H0h22H1h32H2h42H3h57__arithh64__ffh76__sat0h88__varmaph95__with:2q0h;1rh<1zh=2Hdh>4__x1h?4__x2h@1ahA1bhB1dhC1qhD2H4hE2H5hF2H6hG2H7hH2H8hI2H9hJ2HchK6__sat1hL1chM2r0i001xp;1p;2p;3p;4p;6p;7g006ej1ETg007Jj1GTg00:cj20Tg00APj1HTg00Aij2ATg00BIj3YTg00Bmj2=Tg00C^j2:Tg00D?j27Tg00D\j26Tg008hj25Tg00E9j2;Tg00E`j22Tg00<CR0j28Tg00F<j2@Tg00<^j29Tg00Fcj2>Tg00GIj2<Tg00Goj1XTg00HOj1WTg00Hoj1VTg00IMj1UTg00Ikj1TTg00JVj2?Tg00K9j2STg00K[j2PTg00L5j2OTg00>5j3BTg00Laj3NTg00M@j4QTg00N2j2RTg00NPj4MTg00Nnj2JTg00OQj3DTg00P4j3LTg00PWj4^Tg00Q8j6KTg00QVj6]Tg00R2j4\Tg00R]j7[Tg00SAj6ZTg00@RR1f0R2g00?OR33Bp=11932p=3f1R4=B12p=4P1P4g00SeP2C\p=CP4g00TLR5g00TkR6P6g00UKR7P2g00UkF[p=FP4P5P6P6P7P2EZp=Ig00?mR6#ER5#ER8#GR9,04#1%E8#GR8,04#1%12R:#HR;P0f2R0/04#1f3R<,A0[R=1A4010<0#1R>[f4R?,A<\>AY042P4n2001000000120000000UXA1X@1P=\;^A1^@1P2P<P81=?9%3?R;%39R=f6R>/09#3[[1=?8%3810>8R?#3[\;f5R;/:8%18R@#H17>8,68/5?,4>[1;>81238f7R?/08RA#312A8'8[1@?81283f8RA/08RB,2819B3'8[1>A8f9RB/78#1\@1<B8f:RC/08/4C\@17C8P1f;RD/08P1f=RE/:9%19RF#HRGf>RH17H9RI,6910H9RJ'5'4[1;H91239RKf?RL/09RM#312M9'8[1@L91293RNf@RO/09RP,2919P3'8[1>O9fARQ/79#1\F1<Q9fBRR/09/4R\F17R9P1fC/09P1g00VKRS#XRT%WSRS%V1RU%U1RV%T1RW1?18RX1?13RY'C,FW'I1SW7R7P2P0g00>ORZg00>oR['P1O20=BZ[dAN134CQR[b6b8b9g00W7RZ\@P2b5bMb:bIbHbGbFbEb;bCbDb4b3b2b1b7bKP4O41A8<g00WTP11628R<,4;X<115>;/09#1P214?<P11648R<15C2/09#1XB11=B9%3B10D9R?#3\=[1:C917D9,69/5?,4D\G1;D9f<R?/09R;#3R>12;9'8\K1@?910E9R@,2919@3'8\N1>E9%1I\F1<H914ML\F17L9RMP1PPP1PTPSP11R10P4PUCMPV1J16R6%G5RI,?11J15R55D11?19R\5D15L1AD15X9L16'C,FWP7P[b6b8b9X>1X?116I4/69R6,52152<'4^>1^?1P2PCPRO2b5b;b:b4b3b2b1b0b715B615B<'4P116I0RI/69,5CR<1029#1X<1P110C9P:X<1PA10<9PCPIP91=C9%3CP>\=[1:D917?9,69/5;,4?\G1;?9%3@12@9'8\K1@E9129J19J3'8\N1>H9%1M\F1<L914PO\F17O9P110Q9P1PTPSPUPV1C\Y,FW,IWP7P[b6b8b9PZ\FP2b5b;b:b4b3b2b1b0b7C^EK1608,5CP2E]b0PAP2EKW0XC1P4P2O2n2001000000121100000b=b0W=WJXB1XL1o"). Qed.
Lemma mod8_add8 : forall c d, c mod 8 = 0 -> d mod 8 = 0 -> (c + d) mod 8 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocRW ()) [] "p'0h01Hh12H0h22H1h32H2h42H3h52Hdh66__sat0h71ah81bh91dh:1qh;2q0h<1rh=1zh>2H4h?2H5h@2H6hA2H7hB2H8hC2H9hD2HchE7__arithhF4__ffhG6__sat1hH8__varmaphI5__withJ1chK2r0i001xp;1p;2p;3p;4p;7p;6g006ej1>Tg007Jj1UTg00:cj20Tg00APj1ETg00Aij2:Tg00BIj3TTg00Bmj2?Tg00C^j2=Tg00D?j25Tg00D\j28Tg008hj26Tg00E9j2BTg00E`j24Tg00<CR0j27Tg00F<j2ATg00<^j29Tg00Fcj2@Tg00GIj2;Tg00Goj1STg00HOj1PTg00Hoj1OTg00IMj1NTg00Ikj1MTg00JVj2DTg00R2j4LTg00R]j7ITg00SAj6JTg00K9j2KTg00K[j2HTg00L5j2GTg00>5j3<Tg00Laj3FTg00M@j4QTg00PWj4RTg00Q8j6CTg00@RR1f0R2g00?OR33<p=11932p=2f1R4=<12p=3g00?m#>#>#>#UR5,04#1R6%12R7#ER8P0f2R0/04#1f3R9,:0[R:1:401090#1R;[f4,:9\;AT042P4n2001000000120000000UX81X71P:\8^81^71P2P9P51?95%29%25R8f5R:/05#2[[1?:5%2:f7R;/05R<#2\8[f6R=/=5%15R>#ER?15;5,85/6<,3;[1B;51435R<f8R@/05RA#214A5'7[1A@51453RAf9RB/05RC,4519C3'7[1@B5f:RD/55#1\>1;D5f;RE/05RF/3E\>15E5RGP1f<RH/05RIP11=H5f=RJ15J5,8510J5RK'6'3\?1BJ5f>RL/05RM#214M5'7\<1AL5f?RM/05RN,4519N3'7\A1@M5f@RO/55#1\>1;O5fARP/05/3P\>15P5P1fB/05P1g00VKRP#S%PP%O1%N1%M1RPg00TLRQg00TkRRPRg00UKRSPPPQPRPRPSP11D15g00Se1D13CLg00UkFIEJ1KPSP2P0g00>ORSg00>oRP'H1G20=<SPdAF134CQbFbHbIg00W7\>P2bERPbKb;bCbBbAb@b?b<b:b>b4b3b2b1b6bGP4O41:59g00WTP11825R9,3:X=116=:/05#1P213;9P11845R916D2/05#1X91P1PCP7X=1P;16B9/05PBP4P51?B5%2B%2F\8[1=D5185G/6F,3E\?1BE5%2I14I5'7\<1AH5145K19K3'7\A1@J515L5#1\>1;L513NM\>15M5P110O5P1PPb<b;b4b3b2b1b0b6CRECP@P2ECW0X:1P4P2O2n2001000000121100000b5b0X56WDX91XJ1o"). Qed.

(* [comment removed for export] *)
Lemma modk_add_al : forall k al c d, 0 < k -> al mod k = 0 -> c mod k = 0 -> d mod al = 0 -> (c + d) mod k = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocRW ()) [] "p'0h01Hh12H0h22H1h32Hdh41zh52H2h62H3h73Halh84__x1h93Hneh:7__arithh;6__sat0h<2alh=1dh>2q0h?2r0h@3H10hA2H4hB2H6hC4__ffhD8__varmaphE5__withF4__x2hG4__x3hH4__x4hI1ahJ1bhK1qhL1rhM3H11hN3H12hO3H13hP3H14hQ2H5hR2H7hS2H8hT2H9hU2HchV2HkhW6__sat1hX6__sat2hY1chZ1ei001eh[1kh\2q1h]2r1h^1si011si021ni031xp;2p;1p;6p;8p;3p;4p;7g00Wnj2ZTg00APj1=Tg00XNR0j2^Tg008hj26Tg00:cj22Tg00Xnj1YTg00QVj6OTg00YLj1XTg00Q8j6Hj8NTg00Aij2GTg00BIj3eTg00Bmj2ETg00C^j2FTg00D?j27Tg00D\j20Tg00E9j2DTg00F<j2CTg00E`j23Tg00<^j2>Tg00<CR1j2@Tg00Fcj2BTg00GIj2ATg00Goj1WTg00HOj1VTg00N2j2MTg00IMj1UTg00Ikj1TTg00JVj2STg00Nnj2ITg00R2j4KTg00Ymj1hTg00SAj6gTg00ZOj8fTg00K9j2dTg00K[j2bTg00L5j2aTg00>5j3?Tg00Laj3`Tg00M@j4_Tg00Hoj1]Tg00NPj4PTg006ej1QTg006@j1\Tg00OQj3JTg00P4j3RTg00PWj4[Tg00R]j7cTg00?OR2f0R3'3p=<g00@RR4f1R5/23;?2p=5A?432p=41>23p=1A?432#=p=;f2R616535?4p=:1353,@6p=9A?453p=8P5g00TLR7g00TkR8P8g00UKR9P3g00UkFcp=Lf3R:#<f4R;,5:f5R<,5:R=f6R>/Z2%4>R?%=?'^P0f7R0#4R?%=?160>f9R?'5P3f8R@#4RAP4P2f;RB,5315?5f:RC,6Bf=RD'5RE]3]7X<4152C15@2P412?2%43RFX44RGP3P?%Y?EO%4?P4P2f<RH/63f>RI'5X=4P4PB153IX44P016B2%XBEHPCP3EHb3W3W7P?P3P<P:GNWZP3O1%=A%=FRFP115651G6:[RA1G5615:6R0[1G:;\0Ae653P5n2001000000120000000UXJ4XI4R0PA\F^J4^I4RFP3PCPB1E@C%1@RA%1B12CH#1[[1ECH%1CRJ%1D12HI#1[[1EHD%1HRK%1If?RL,2IRM#1[[1FDI%;I17IL,0L=:IM[1DIL%<Lf@RM,2LRN#1?9NM[1CLM13M2fARN12MNRO'31>O2'@[1BMN%4NfBRO,7N#4[1ANO%4OfCRP,2O/8O[17OPP4fDRQ,2PP4fERR,FP%;RfFRS17QS'012QS5:Q[1DQS%<SfGRT,2RRU#1?9UT[1CRT13T2fHRU12SURV'31>V2'@[1BSU%4UfIRV,7T#4[1ATV%4VRWfJRX,2URY/8U[17UXRZP4fKR[,2VR\P41FV[%;[fLR]17X]'012X]R^5:X[1DX]%<]fMR_,2[R`#1?9`_[1C[_13_2fNRa12]aRb'31>b2'@[1B]a%4aRcfORd,7_Re#4[1A_d%4dfPRf,2aRg/8a[17afP4fQRh,2dP4P>PVO1fRRi/05=:f3PDPfO1fTRj99A@PRPhO1%1MfURA79MP1PJfVRJ,3CfWRk#;P5fY,3DP1%1RfZ,3Rf[Rl#;P;%1TRmf],3Ug00VKRn#WRo%VnRn1M45%U4Rp%T4RqP7P8P8P9P41S42Rrg00[3g00?mRs,I4RtCK,Lq%h8PqP7P8P8P9P4Ptg00SeR8PrCK,LqEgGf1dq9R9P3P6g00>ORrg00>oR7'b1a36=?r7dA`425C_R7bCbDbEX84Rr%<3%45Rug00W7[[^84RvP3f_PlO2b:WAW2P5P3O2n2001000000120000000W6X5KP5P3O2n2001000000120000000b2bBb@b]b\bPbObNbMb@b?b>bTbSbRbBbQbLbKbAb6b5b2b1b;bWbXP>O41GBCg00WTRKP4103D,8HX44PEP3103L,8IP4105MRE15I3%=u16NM/5P]9]3X<415DE106N#;P0PFP3PM10;PRFP5P6O41GFMPKP410>R,03,8OX4416PO/5RP310@T,03,8QP410?U,05RQ16T3/5VX=41ESU%1S%1V%1Y[[1FTV%=W10XZ=:UY[1DUX%<X%1\RY?9\[[1CV[13[213]^1>^2'@[1BX]%4]17[_#4[1A[_%4_RZ18b][17]aRbP412_dRdP4P<P]O1%13RW?93fP1%15R@135h10BP/0i,6f10Pi,0B7:fP3%1:Rf13;jPoPnP4P41M4;P6%]4CPP51M4:CPPpP4%QsRp,I4Rn%\s,I4Rs5J4%Qp,I4Rp5J49R4tP8AJ4sp9J4n9R4tCK,LqP9P7bCbDbEX84XF4XG4XH41056/0:,63106:,057:3^84^F4^G4^H4P3PJPTPLPjO4b:W2W1P5P3O2n2001000000120000000b1b?b>b6b5b2b1b0b;105?/0U,6S?:SQP4106CRQ/0V,6TRS153XX44P412TVPGPP12SVPTPQPV1ETV%1XPY[\m1FUX%;X17V[,0[=:V\[1DV[%<[%1^?9^][1CX]13]213_`1>`2'@[1B[_%4b\Z1A]a18d_\cPeP4PgP4P<P_O1A9W3hP1P@135ifSRi#;P313;APrPvP3PkPiO2b:W2X1fP5P3O2n2001000000120000000b1b?b>b6b5b2b1b0b;C[EH10CV,06,6TP3EOb0PRP3EHW0XL4P5P3O2n2001000000121103000b3b0W9W3PLP3P?P>GNW0XK4P5P3O2n2001000000121103000b7b0W9P3O1n200110100021010011102b^X3=WUW7WVX=4XY4X<4X[4o"). Qed.
Ltac rl_align_span :=
  lazymatch goal with
  | |- (?c + @rl_delta ?RL ?b) mod ?k = 0 =>
      let r := eval vm_compute in (span_find canon_spans b) in
      lazymatch r with
      | Some ?s =>
          let al := eval vm_compute in (sp_al s) in
          apply (modk_add_al k al c (@rl_delta RL b)); [ lia | reflexivity | reflexivity | exact (proj2 (rl_span b s (@eq_refl _ (Some s)))) ]
      end
  end.

(* [comment removed for export] *)
Ltac rl_dmod8 :=
  first [ exact rl_dBSS_mod8 | exact rl_dDATA_mod8 | exact rl_dDATA1_mod8
        | lazymatch goal with
          | |- (@rl_delta ?RL ?b) mod 8 = 0 =>
              let r := eval vm_compute in (span_find canon_spans b) in
              lazymatch r with Some ?s => exact (proj2 (rl_span b s (@eq_refl _ (Some s)))) end
          end ].

(* [comment removed for export] *)
Ltac rl_align :=
  first [ reflexivity
        | apply mod4_add8; [ reflexivity | rl_dmod8 ]
        | apply mod8_add8; [ reflexivity | rl_dmod8 ]
        | rl_align_span ].

(* [comment removed for export] *)
Ltac rl_dwin_bounds :=
  lazymatch goal with
  | _ : rl_img_hi <= 2 ^ 32 |- _ => idtac
  | _ => let F := fresh "RWF" in
         let a := fresh "RWa" in let b := fresh "RWb" in let c := fresh "RWc" in let d := fresh "RWd" in
         let e := fresh "RWe" in let f := fresh "RWf" in let g := fresh "RWg" in let h := fresh "RWh" in let i := fresh "RWi" in
         let x := fresh "RWx" in let y := fresh "RWy" in let z := fresh "RWz" in
         pose proof rl_dwin_facts as F; destruct F as (a & b & c & d & e & f & g & h & i);
         pose proof (rl_delta_bd B_A_1f3f8) as x; pose proof (rl_delta_bd B_A_1f440) as y; pose proof (rl_delta_bd B_A_1f630) as z;
         rl_spans_data;     (* [comment removed for export] *)
         rl_data_chain      (* [comment removed for export] *)
  end.

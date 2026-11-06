(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocKit_A2.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocKit_B MallocModel_B MallocKit_B2 MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_F_am_K2 () := "C35stdpp4base6lookupC69OSSVerify5KrLib2CJ4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC69OSSVerify5KrLib2CJ4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2CJ1A9MallocRep5lr_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib2CJ1A:MallocTree>In_live_rangesC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2CJ4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib2CJ4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2CJ1A:MallocTree>ranges_free_InC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic3notc69OSSVerify5KrLib2CJ1A7F_am_K2;clear_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I69OSSVerify5KrLib2CJ4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1N00I69OSSVerify5KrLib2CJ4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI69OSSVerify5KrLib2CJ4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes:comparison00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module A2 := MallocKit_A2.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition clear_range (st : mstate) (lo n : Z) : Prop :=
  forall rid r x, (s_regions st) !! rid = Some r -> lr_lo r <= x < r_base r + round_up_pg (r_len r) -> ~ (lo <= x < lo + n).

Lemma clear_range_of_ranges_free st lo n : ranges_free (live_ranges st) lo n = true -> clear_range st lo n.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_K2 ()) ["AC_1"] "p'0h02HIh12Hxh24__p1h34__x1h44__x2h54__x3h64__x4h74__x5h81Hh97__arithh:4__ffh;8__varmaph<5__with=3Hinh>2Hrh?2RFh@2lohA1nhB1ri001rhC2r0hD3ridhE2sthF1xi011xp;1p;3p;4p;6p;2p;7p;8p-1R0g0000R1p4p710p8P0P1p4p7210p8g000Dj1DTg001Cj3rTg002Bj3GTg002\j1STg003>j4qTg003Rj4bTg003kj1\TP1j6XTg004hj2VTg005Jj1UTg006Cj1<Tg007=j17Tg0086j1;Tg0095j20Tg009Rj26Tg009nj4aTg00;1j2^Tg00;Qj1]Tg00<Vj3ATg00<mj1ZTg00=gj1@Tg00>Lj1WTg00>jj2FTg00?Gj7MTg00@Jj21Tg00@fj2=Tg00A@j1>Tg00A_j29Tg00BHj3BTg00C1j2LTg00C]j1RTg00D=j3JTg00D]j1QTg00E=j2KTg00E[j1PTg00F9j4ETg00FWj1TTg00G5j1pTg00G`j28Tg00HCj1OTg00Hhj3CTg00IKj2oTg00Inj3lTg00JQj1`Tg00K3j4HTg00K^j6_Tg00LBj2cTg00Ldj2dTg00M>j2eTg00Mjj3fTg00NIj4[Tg00O;j1gTg00OTj3hTg00PQj2iTg00Plj4jTg00QLj7kTg00R0j7YTg00RTj7mTg00S8j8nTf2R1f1R0'1f0R2'ip=3%@2#@p=:g00S\R3P3P0P2Cjp=?P3P0g00T:P2CHp=4P0g00TaR4g00U@R5P5g00U`R6P2g00V@Fkp=2P1P4P5P5P6P0P2FYp=NP1P4P5P5P6P0P2Fmp=If3R7P4P5P5P6P1P0P2Gnp=5g00V`g00W\R8%D1?r02g00X<R93Gg00X\R:g00Y:R;%S;P:P;P:g00Z6R<g00ZOR=P;CqP:P<P=P;CbP1f6R=#\EX1V;03G%U1%<1%71#;'0,60730f7R;10;=,61731R<f9R:f5R>f4R?P1Ca1^33R@%]?%D:3A%Z>g00ZmRAPAPAP3P2%<;RBg00[hRC#@RD#@RE#:#:#:#:#:#WRF'0RGPBPBn011010003000000%7;#;RH,0B,6=73=PAP@P0f8RA#<RI/0FRJ%7A#;RK/FFRL'?1?IKRMPMn011010003000000f=RM#DRN5A@g00\MRO]0]1P2%<=RP/0F%7=#;,0P,6>RQ73>1FHF,?Gf<RG#DRR5A@PNPGf;RSPJPLf:RTP2FM10GSRU/1J10JL/1G'=p-0RLg00\jRJg00]VRV#>RW#>RX#>RY#>,93RZ193Y193V5B35B3g00^5RV'L193X193W5B39B3Z/LV%RJ5JJ3JRV%QJRJP3P31K3?P1%P3RZCEP0P31K3>P7PZCECERZ%T3RW%p3RX183ERE%OD,835C3RY183CR[1o3FR\5C3R]'4,2X%OC,83RC=l3\9C3]/4E,2X5NX%`5R\PX183DRD,4E,2XP3PDg00^aR^PYCH,2X5IXR_P\PX14]D,2XP3PDP^AC3[CRCCH,2XR^5IXP\PXP4P5P5P6P;E_R;C5C5C51cX6R6P2P11d891e21=G89dg00_H=f30C[R9b:b;b<X33X43X53X63X73W2107?R8102FR5'11F1F,05/17'=10?>,6193?1R5101F101?,67R?737PA[[[^33^43^53^63^73^2LP2POPMf>%7T#;P:%<TP0P=P7O9R=b9b8W0W1A3P>Q1?BH=A@RPNPGPSPIPKPTP2FM11UI10IK/1G'=PVPJPZPWPX14Y[,2X14CE,2X5NXP\PXP_P\PX14[D,2X=IX^P\P;C5C5C5P6P9b:b;b<X33X43X53X63X73X2L11821021/17'=A317?PA[\5[^33^43^53^63^73^2LP=b9b8W0W1R=P=n011000003010101P7P0O2bCb0W=%g<eW1W>XF3WBWDAh710eW?XA3X@3WEo"). Qed.

Lemma round_up_pg_aligned x : x mod 4096 = 0 -> round_up_pg x = x.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_K2 ()) ["AC_1"] "h02H1h12H6h27__arithh34__ffh48__varmaph55__with64__x1h74__x2h84__x3h94__x4h:4__x5h;1Hh<2H0h=2H2h>2H3h?2H4h@2H5hA2H7hB2H8hC2H9hD6__sat0hE1qhF2q0hG1rhH2r0hI1xhJ1zp;1p;2p;3p;4p;6p;7p;8g00=gj1CTg00>Lj1GTg00_fj20Tg00`Fj17Tg00HCj1QTg00`cj2`Tg0095j29Tg00a@j2MTg00O;j1ZTg00aaj2=Tg00b>j2BTg00b[j2UTg009Rj22Tg00PQj26Tg00cBj2PTg00@Jj2HTg00cij2RTg00dOj2TTg00e5j2_Tg00Ldj2OTg00eVj1^Tg00f4j2]Tg00A@j1<Tg00fUj3ETg00A_j2NTg00C1j2\Tg00g>j2LTg00C]j1[Tg00D=j3YTg00D]j1XTg00E=j2KTg00E[j1WTg00F9j4DTg00FWj1VTg00G5j1rTg00IKj2JTg00gjj6qTg00JQj1pTg00G`j2?Tg00hNj3STg00Hhj3FTg00K3j4ATg00RTj7mTg00i1j2lTg00LBj2kTg00M>j2hTg002Bj3ITg00Mjj3fTg00NIj4eTg00iTj1dTg00j2j2cTg00jPj2gTg00kAj3bTg00kdj6iTg0086j1jTg00BHj3aTg00QLj7nTg00S8j8oTf0R0#C#Cp=8g00S\R1g00_HR27I0p=>f1R3=I10p=11H20p=31N10p=;Aa130p=5P1P3g00lBP0CAp=@P3g00TaR4g00U@R5P5g00U`R6P0g00V@Fnp=4f3R7P4P5P5P6f2R8P3P0Gop=:g00[hR9#CR:#CR;#8#8#8#8#8#GR<,00#>P1%73R=%G:%Q9R>#8#GR?'`'01980/18XJ11M=<%><R@#ZRA%78RB1=B<,B<10B<'9'1[1UB<122<RB%77RC/0<RD#312D<'6[1PC<12<2RDf4RE#7RF/0<RG,2<1HG2'6[1RF<f5RF#7RG/=<#>\@1TG<f6RG#7RH/0</1H\@1=H<P1f7#7/0<P1f8RH/M<f9RI1=I<,B<10I<'9'1\A1UI<f:RA/0<RJ#312J<'6\B1PA<f;RJ/0<RK,2<1HK2'6\D1RJ<f<RD/=<#>\@1TD<f=RD/0</1D\@1=D<P1f>/0<P1PFg00li1_2<'OPBeRBO1%30120<'6PDPBO1%3H12H<'6g00\jRH%^9,]1RBg00]VRD#<RK#<RL#<RM#<RN#<RO#;5E1%;LRL9E1B%;KRK9E1B1N1DRD'5'5'5%<O#;%;N%;M/5L'5'515KDg00^5'\'L'L%[HRD3Y%XHRHP1P11K1EP8%W1RKCDP3P11K1FP7PKCDCD%V1RL%r1RMPMPMP4P5P5P61J1<RN1J12RO'@,4MEqRB%p5RP1?19R9%Q:,?19S1N1?1>R>5F1'@,4MC:PPPMPMP4P5P5P6P1POg00T:R51?1:R:CA,4MP1P:g00^aPNCA,4MFmPPPMPMPBPP1l191?1;9S1N=F1:'@,4MC:PPPM1@>O,4MPPAF19:/@9,4MC:C:C:C:1kM6R6P0P8g00W\R9g00X<R:'O1h08=I9:dAf123CeR2b3b4b5X61X71X81X91X:1g00\M\@R@1B<F/97,13[%38128<'61B<G/9E,1C\@%>F19EF/1E[[[[^61^71^81^91^:1P0PEPJP7PAfBPIP3f@fAO9b2b0b1bHbFbCbBbAb1b@bGbEb?b>b=b0b<%d?,c=1g3<%33%3<107<#3[[PDPHPKPLP1POP51J1?CA,4MP6P2b3b4b5%3?P0b2bD9b=?Ei%j3/13eW;XI1o"). Qed.

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis MR : mrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= alloc_ceiling.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.

End GROW.

End AC_1.

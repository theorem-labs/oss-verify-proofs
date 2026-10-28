(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import List.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3 BothPlanCore BothPlan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BsHSTab () := "C46Stdlib5Lists4List:fold_rightI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00c6ARocqVerifyHarness?AgentSubmission3bpB5Start7BsHSTab9hs_lookupI47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2InK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes4list01C47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4list02C47Corelib4Init3Nat3eqbK47Corelib4Init5Logic2eq01C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic2or01C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01I7ARocqVerifyHarness?AgentSubmission3bpB5Start8BothPlan2AP3acs00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4bool02c6ARocqVerifyHarness?AgentSubmission3bpB5Start7BsHSTab<hs_lookup_InC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init5Logic3and01I47Corelib4Init5Logic2or00".
Import ListNotations. Import AP.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Fixpoint hs_lookup (h : nat) (l : list (nat * acs)) : option acs :=
  match l with
  | [] => None
  | (k, c) :: r => if Nat.eqb h k then Some c else hs_lookup h r
  end.

Lemma hs_lookup_In : forall h l c, hs_lookup h l = Some c -> In (h, c) l.
Proof.
ltac2:(KReplay.run1 (kr_t_BsHSTab ()) [] "p'0h01Hh11Eh22H0h31lh42c'h51eh61kh71mh81ni001nh92IHh:1ai011ah;1bi021bh<1ch=1hh>1ri031oi041pp;2p;1p;3p;6p;5p;4p-1p10000p4p710p9g000OR0j2ITg000oj1HTg001OR1j1ATg0021j22Tg0031j30Tg003Kj36Tg003bj1?Tg004Dj69Tg004`j1>Tg005@j2=Tg005_j35Tg006?j27Tg006Vj2<Tg0070j2;Tg007Pj2GTg0083j6FTg008Pj3ETg008jj6BTg009Hj3@Tg009bj5CTg00:Dj2DTg00:fj4:Tg00;FR2f0R3'Dp=1g00<FR4P2f1R5P3C:p=3f3R6P4P2f2R7P5C:;63p=4g00<eR8g00=E703p=81I42R9#HR:P9%A2R;1263%15R<30f4R=/37R>=695[X3:%?2R?%13R@50;P;P?P1P2p-0P3g00=eR?g00>Bn10110300021000000X5;g00>^P<P3E9P?%>9R?969>/=3b2W0127?=0;@P9P6P5P?C4[eP0P4P2f5R0/23%1650;P9f6R?P=P5C4[A5975,2?%1=50;P9f7R@P0A5967C4[[^3:P3f8R>/23%1?R<50;P9f9RAP@P5C4[P8P;17A6%1712A5n0100000020000%1@RB50;f:RC/7=P81<83f;RD/70=083P8f=RE/7@=083P8P;P5PBf>RF/2?n0100000020000f<RG#150;P9f?RHPE13A>=59@C4]0]1P517G?RI#8%1DRJ90;<g00?:1;53#8A0475[R<A04531;75#8RK[A0467\K1G53P5n2001000000120000000X74X84P<^74^84P3PHPAP7O3A04HAP4f@R<P9fARKPH133C=59AC4X64P;P2P1P2P2P3P3PCn10110300021010100X5;%1A%1FP7EFA02AFA02CHP2P<P9fCRHPK13H3=59DC4X42fB/3<R<=09<A69<C1<9<3EPDP3EBW0P3O1b2PCP3E9b1b2W0W1g00?U908I12E0=0;J13>@13FGRG509A69G?P0P3O13@W0W1n0110200020000P3P7O2b1b;W01367=595,2A=0;BP9PCP>13=6=597C4[eW9X>:X42X64P5P3O2n2001104000121100101X:9P5DCX<2W3X=4o"). Qed.

Lemma hs_lookup_cases : forall h l c, hs_lookup h l = Some c ->
  fold_right (fun kc (P : Prop) => (h = fst kc /\ c = snd kc) \/ P) False l.
Proof.
ltac2:(KReplay.run1 (kr_t_BsHSTab ()) [] "p'0h01Hh11Ph22kch31lh42H0h52c'h61eh71kh82IHh91ai001ah:1ch;1hh<1ri011ni021pp;2p;1p;3p;4p;6p;5g000OR0j2LTg000oj1KTg001Oj1BTg0021j2>Tg00:Dj2JTg0031j33Tg00@5j4FTg003Kj31Tg00A8j3?Tg00AUj3=Tg004`j1ITg005_j36Tg0083j6;Tg006Vj2:Tg00B2j4ETg008jj69Tg008Pj3ATg009Hj3CTg009bj6DTg00:fj4@Tg00?:j2<Tg00BMR1j2GTg0000j5HTg00<FR2g00;FR3f1R4f0R5C@p=0f4R6f3R7532f2R8=334'</G5p=2p-0R9P8P4g00=eP5DHp=4A3345p=5A3284/<5p=8A3245p=71L23R:#KR;%B31>841J3533P7P8P4P5CF1074=1:8P:f5R</07=1:5f8R=A?234R>f6R?A=234R@P5D2X19X2:=4:4]0X3;1068%I:RA51:P5f7RBP>P<P@P5D2X19X2:=4:AeW0P0P2P310B<=1:5f:RAP>P=P@P5D2X19X2:=4:4]010=?A6:8451:f;RCP>f9RDP@P5D2X19X2:A6:7854:]0[^3;P510A==1:5f=REP>PCP@P5D2X19X2:=4:4]010CD1078=6:451:P11067R1f<RF/0ARG53:A1:G8PEP<PCP6f?RGP>PEP@P5D2X19X2:=4:7D2P510<610ECRC53:f>RH15F<78?RIf@RJP>PHP@P5D2X19X2:=4:6R6P:P3P0P2P3P3P5P5n2001102000120101100X6:10?<10HFP5E;15<FP:P2P0P2P3P2P5P4n2001102000120101100X6:10B?10GEP4E;17BG17=JP2fARB15DJfCRE15BA784[X7215=GP3PJ15B598EEX53fBRE/7E15JJ1:2E1:3JCEPDP5E9W0PDP5E9W0P5O1b4P5O1b43AW0P5O1A1:C7P7P5O19CI6W0P5O1n200100000021000010000PHP>PFP@P5D2X19X2:A6:1854:eW0W8X<;X53X72P4P5O2n2001102000121101100X9:P7P5EDb0W0X:3W3X;2o"). Qed.

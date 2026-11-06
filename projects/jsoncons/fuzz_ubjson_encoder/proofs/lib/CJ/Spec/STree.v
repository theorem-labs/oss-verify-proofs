(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import List.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_STree () := "C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5sbindC13~~~i99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5stree00C13~~~K47Corelib4Init5Logic2eq01k99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5stree02C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree9stree_indC13~~~i99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree4steq00C13~~~k99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree4steq01C13~~~k99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree4steq02C13~~~k99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5stree01C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree9steq_reflC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree4smapC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree8steq_indC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree9strel_indC13~~~I47Corelib4Init5Logic2eq00i99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5strel00C13~~~k99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5strel01C13~~~k99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5strel02C13~~~K47Corelib4Init5Logic3and01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree;strel_sbindC13~~~C47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C47Corelib4Init9Datatypes3fstc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5erunsC13~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes3snd".
Set Implicit Arguments.

Section STREE.
Variable E : Type.   (* [comment removed for export] *)
Variable A : Type.   (* [comment removed for export] *)

Inductive stree (R : Type) : Type :=
| SRet (r : R)
| SVis (e : E) (k : A -> stree R).

Arguments SRet {R} r.
Arguments SVis {R} e k.

Fixpoint sbind (R S : Type) (t : stree R) (f : R -> stree S) {struct t} : stree S :=
  match t with
  | SRet r => f r
  | SVis e k => SVis e (fun a => sbind (k a) f)
  end.

Lemma sbind_ret_l : forall R S (r : R) (f : R -> stree S), sbind (SRet r) f = f r.
Proof.
ltac2:(KReplay.run1 (kr_t_STree ()) ["STREE"] "h01Rh11Sh21fh31rp;1p;2p,1Ep4p300R0p10000p4p710R1p8P0p1000Lp4p710R2p8P0p1000jp4p7210R3p8P0p1001Gp4p710R0p8p,1Ap4p300R4P1p8P4P2p8P4P3p8P4P0p8p200R0p1001eR4p609311001p8p201R3P4p6094111000p8g0033j11Tg004Cj20Tf1R4f2R2%12R2[f0P4O1,02W2W3X13X00o"). Qed.

Lemma sbind_vis : forall R S e (k : A -> stree R) (f : R -> stree S),
  sbind (SVis e k) f = SVis e (fun a => sbind (k a) f).
Proof.
ltac2:(KReplay.run1 (kr_t_STree ()) ["STREE"] "h01Rh11Sh21ah31eh41fh51kp;1p;4p;3p;2p200R0g001eR1p609311001p8p201R2P1p6094111000p8g0033j13TP1j42Tg004]j30Tg004Cj21Tp,1Ep,1AR1f3R3#3R4[P4\3f2R5f5f4P5f0O1f1C2X21503,14W4W5W3X12X00o"). Qed.

(* [comment removed for export] *)
Inductive steq (R : Type) : stree R -> stree R -> Prop :=
| steq_ret : forall r, steq (SRet r) (SRet r)
| steq_vis : forall e k1 k2, (forall a, steq (k1 a) (k2 a)) -> steq (SVis e k1) (SVis e k2).

Lemma steq_refl : forall R (t : stree R), steq t t.
Proof.
ltac2:(KReplay.run1 (kr_t_STree ()) ["STREE"] "h01th11Hh21Rh31eh41kh51rp;1p;3p;2p;5p200R0g005mR1p609311001p8g0033j10Tg007?j31Tg008Nj23Tg009]j52TP1j54Tf0R1#0f1R2%02f2R3?111W01331X52p,1Ep,1AR4f3#0[f4R5P2P1O1R6;16\4P5P3P2P2P1D2W1W4W3P1D4W0X20o"). Qed.

Lemma sbind_ret_r : forall R (t : stree R), steq (sbind t (fun r => SRet r)) t.
Proof.
ltac2:(KReplay.run1 (kr_t_STree ()) ["STREE"] "h01rh11th21Hh31Rh41ah51eh61kp;1p;2p;4p;3p;5p200R0g005mR1p609311001p8P0g001eR2p609311001p8P0P2p6094111000p8g0033j13Tg00:lj22TP2j40Tg007?j31Tg008Nj27Tg009]j56Tg004]j35TP1j54Tf0R1#3f1R2%32f2R3P3P3P1f3R4/21X03R5C0;11W11731P3P31231R6P5C0=136eX02p,1Ep,1AR6%34[f4R4P4P4P2P1O1R5f5R7/21X04R8C0;15\6P4P3P7P7P3P1O1f6/21X07C0X46P2P1D6P4P4A5432R3P8C0=143eW2W6W5P1D4W1X30o"). Qed.

Lemma sbind_assoc : forall R S T (t : stree R) (f : R -> stree S) (g : S -> stree T),
  steq (sbind (sbind t f) g) (sbind t (fun r => sbind (f r) g)).
Proof.
ltac2:(KReplay.run1 (kr_t_STree ()) ["STREE"] "h01fh11gh21rh31ah41th51Hh61Rh71Sh81Th91eh:1kp;1p;4p;3p;2p;5p200R0g005mR1p609311001p8P0g001eR2p609311001R3p8p201R4P3p8P4P2p6094111000R3p8p202R5P3p8P5g00<<R3p609311000p8g0033j11TP2j40Tg007?j32TP3j23Tg00:lj27Tg009]j56Tg004]j35TP1j54Tf2R1#1f3R3%13f4R2%12[R6f5R7P2f6R8P7P1f1R9C0f0R:C0P8P2P1P8P7P1P:O1R;P9C0X28R<C0522^16]0W4P7P2P9P1O1P:C0,32P7P2P8P71781R=P9C0P:C0P8P2P=P<C0522eX16X06X23p,1Ep,1AR6%17[%18\8R7f7R<P8f8R=P<P3P1O1R>P9C0P:C0P=P8P>P=P<P;P9C0X2=R;C0528^17]0\6P8P2P=P<f9R>P=P2P:O1R?P1C0P9C0X36P>P<P?P>P=P3P:O1P1C0X2>C0X36P3P:P1P9O3X36D6P<P8P=P<A5=23R2P9C0P:C0P=P8P2P;C0528eX17X07W5W:W9P:D4W4X85X74X60o"). Qed.

(* [comment removed for export] *)
Definition smap (R S : Type) (f : R -> S) (t : stree R) : stree S := sbind t (fun r => SRet (f r)).

(* [comment removed for export] *)
Inductive strel (R1 R2 : Type) (RR : R1 -> R2 -> Prop) : stree R1 -> stree R2 -> Prop :=
| strel_ret : forall r1 r2, RR r1 r2 -> strel RR (SRet r1) (SRet r2)
| strel_vis : forall e k1 k2, (forall a, strel RR (k1 a) (k2 a)) -> strel RR (SVis e k1) (SVis e k2).

Lemma strel_eq_steq : forall R (t1 t2 : stree R), strel eq t1 t2 <-> steq t1 t2.
Proof.
ltac2:(KReplay.run1 (kr_t_STree ()) ["STREE"] "h01Hh11ah22t1h32t2h42H0h51eh62k1h72k2h82r1h91xh:1Rh;1rh<2r2p;1p;5p;3p;2p;6p;9p;7p;4p100=NR0p609311001p1001eR1p609311001p8P0p6094111000P1p6094111000p8p200R1g001GR0p4p710p8P1g00>[R2p609311001p8P1g00?lR3p609311003p8P1P3p6094111002p8g0033j11Tg00A>j12j3>Tg00AXj53Tg007?j30Tg00:lj24Tg008Nj2;TP0j68Tg009]j57TP3l96Tg004Cj25Tg00Bhj69Tg00D8j7:TP2j7=Tg00EHj4<Tf0R2#1f1R3#1f2R0P0%20P3P2D3R4f3R5?003[A0032R6P5P5%25R7P0P3D3[P5P5P7%15R7f4R8#1R9f5R:?032W3W2A>:32f6R;P3f7R<14<214<030X8;1;;3P0P2E8W0X<8X85p,1ER=p,1AR>%1:]9R?%1;^9>R;P<P<%2<P0P2O1R@P3P2O1RAD3^1>f8RBP5P2O1RC;0@^1>PBP8P5P0P2D7W4W0W7W6W5P0P3P2M96X04P5P:P:%2:P3P2D3X39X27P8P8%28P2P21582E9X;5A0<@A^1>PBPB%2BRAPCP@D3^1>PBPBPAP8P5P0P2F:W4W0X7;X6?X5=P0P3P2F=X06C<W3W2X:1o"). Qed.

Lemma strel_mono : forall R1 R2 (RR RR' : R1 -> R2 -> Prop) t1 t2,
  (forall a b, RR a b -> RR' a b) -> strel RR t1 t2 -> strel RR' t1 t2.
Proof.
ltac2:(KReplay.run1 (kr_t_STree ()) ["STREE"] "h02H0h11ah22t1h32t2h41Hh52H1h62R1h72R2h82RRh93RR'h:1bh;1eh<2k1h=2k2h>2r1h?2r2h@1xp;1p;5p;6p;7p;9p200R0g00?lR1p609311003p8p201R2P1p6094111002p8g0033j11Tg00AXj50Tg00Bhj63Tg00D8j72TP1l94Tf1R1p-0R3\1[f2R4P3\4[f3R3#1R5f5R6P6P1f0R7O2P6P4P1O2[^:6]1f6R8P6f4R9P4P1D0f7R:P8P6%1:R6f9R;f8P8P1P7D0X36W2P:P1P7O2f:R6P;P:P4P1P9P4P1P7O3E3W0X?:X>:p,1Ep,1AR:%1;]@R8f;R<P6P;P4P7O1R6P1P7O1D0^1:f<R1P<P;P3P7O1P6D0^1:P1P<P;P9P3P4P7F2W5W0X=8W<W;P3P4P7M94W0W4X35W2W9W8X72X60o"). Qed.

Lemma strel_sbind : forall R1 R2 S1 S2 (RR : R1 -> R2 -> Prop) (SS : S1 -> S2 -> Prop)
  t1 t2 (f1 : R1 -> stree S1) (f2 : R2 -> stree S2),
  strel RR t1 t2 -> (forall r1 r2, RR r1 r2 -> strel SS (f1 r1) (f2 r2)) ->
  strel SS (sbind t1 f1) (sbind t2 f2).
Proof.
ltac2:(KReplay.run1 (kr_t_STree ()) ["STREE"] "h01ah12r1h22r2h31Hh42t1h52t2h62H0h72R1h82R2h92RRh:2S1h;2S2h<2SSh=1eh>2f1h?2f2h@2k1hA2k2hB1xp;1p;5p;4p;2p;7p;3p;9p200R0g001eR1p609311001R2p8P0g00?lR3p609311003p8p201R4P2p8P4P3p6094111002p8p202R2P1p6094111000R5p8p203R6P5p8g0033j12Tg00AXj51TP1j40Tg00:lj23Tg00D8j76Tg004]j34TP3l95Tf3R3p-0R1\3[f2R5P1\5[f5R1#2R7f7R8f6R9#2[R:f9R;f8R<P1P3P5D1f:R=P;P9%2=R>f<R?P=f1R@f0RAO2f=RBP?P=P8P5O1P9P@O1D1[^2?]1f;RCP=P<PBPCP5P1C0P?P=P@f4RDC0D1[X5>W4P<P@PAO2PCP@PAO2f>R>PBPCP<P5O1P8P@O1D1[^2B^1BPAP3P5P@O3P?PCP;P>P?13>3P9C0PBPC13B5P1C0D1eUW3X2=X1=p,1Ep,1AR9%2?]BR?P>PBP=P5PAO1P@PAO1D1^09f?REPBP@PAO2f@RFPEPBP=P5O1P;P@O1D1[^2E]1R=P>PBPCPFP>PDP@O1P<C0PEPBP3P@O1P8C0D1[^09P>PBPCP1fAPEP1PAO1P;C0X09PFP>PDPAO1P<C0X09P5PAP@O2X09F6P>PBPCPFP>A4F1DP<C0PEPBA4E13P8C0D1eV=W6W3XA?W@W=PDP3PAM95W3X?:W>X57W4W<W9X;6X:2X84X70o"). Qed.

Lemma strel_smap : forall R1 R2 S1 S2 (RR : R1 -> R2 -> Prop) (SS : S1 -> S2 -> Prop)
  t1 t2 (f1 : R1 -> S1) (f2 : R2 -> S2),
  strel RR t1 t2 -> (forall r1 r2, RR r1 r2 -> SS (f1 r1) (f2 r2)) ->
  strel SS (smap f1 t1) (smap f2 t2).
Proof.
ltac2:(KReplay.run1 (kr_t_STree ()) ["STREE"] "h01rh12r1h22r2h32R1h42R2h52RRh62S1h72S2h82SSh92f1h:2f2h;2t1h<2t2p;1p;5p;2p;6p;<p;4p200R0g00=NR1p609311001R2p8P0g00EcR3p609311005p8p201R4P2p8P4P3p6094111004p8p202R2P1p6094111000R5p8P2P3p60951111003p8p203R6P5p8P6P3p609611111002p8g0033j15Tg00AXj52Tg00:lj20Tg00Bhj63TP3l<4TP1j41Tf3R1p-0R3\1[f2R5P3\5[f5R3#5R7f7R8f6R9[R:f9R;f8R<P3P1P5D2f:R=P<f1R>f0R?O2P<P3P5O1f4R@P>O1O2[^2=]1f;RAP=P;P<P8P9P3P@P@P?O1,0=X0AP1P?O1,0;X0=P>P;P>P?O2f<PAP;P9P5O1P3P>O1P1P5P>P?O3E3UX2AX1AM<4P;P<P9PAP;P1P3C1P=P<P5P@C1D2eUUX::W9X<7W;W8W5X76X62X44X30o"). Qed.

Lemma strel_trans_eq : forall R1 R2 (RR : R1 -> R2 -> Prop) t1 t2 t3,
  strel RR t1 t2 -> strel eq t2 t3 -> strel RR t1 t3.
Proof.
ltac2:(KReplay.run1 (kr_t_STree ()) ["STREE"] "p'0h02H1h12H0h22H2h31ah42Hth52H3h61si001sh72t3h81xh91Hh:1ei011eh;2H4h<2e0h=2r2i022r2h>2e1h?2k1i032k1h@2k2i042k2hA2r1i052r1hB2t1hC2t2hD2R1hE2R2hF2RRhG2k0hH2k3hI1ri061rhJ2r0hK2r3i071ki082s0p;1p;5p;2p;3p;6p;7p;9p;:p200R0g00?lR1p609311003p8p201R2g0000R3p4p710p8P2g000jR4p4p710p8P2P4p4p7210p8P2g001GR5p4p710p8P2P1p6094111002p8g0033R6j11Tg00AXR7j54Tg00:lj22Tg00A>j1:j30TP4j6=Tg00Bhj6BTP3j7?j6;TP5l9Aj6>Tg004]j33Tg00G7j2@Tg004Cj2<Tg00D8j7DTP1l:CTf4R1f3R5f2R3#:f1R4f0R8D4p=71234=058p=8f5R9P1P51234P8D4p=9A3534=018p=6f6R:P9P1A3534P8D4p=5p-0R;\4\4%13R<%15P9P1P5P3P4D4P:P9P1%1:R=f7R>#1f8R?P?P?P4P8D7f:R@f9RAP?P5P4D4[]7XC=WBP:P4P8O2%1?R=PAPAPA12A3P8D7P7P@P@%:@f=RB#1RC12B:703f>RD#1RE?039f@RFf?RGPD12FARHP:D4[[P8A0G48%1FRIPFP3PHC8fARH#1RJPHP3P?C8fBRK#1RLPKP1f;RM,2KRNC8fCRO#1RPPOP6fDRQfERRP8P8P?n10110000021010620101107X:P12O9f<RS,2OP8E=A0O9SA0Q:BP8A0R>DfFRTPGfGRU#1RVPUP?PDC8RWfHRX?04AfJRYfIRZPXPYPOPFE9]1]2XIT%1TR[PTP>PBC8P8PW%1XRW12XAA0ZK@fKR\PYPZP\PQP4E9]1X6WA0XHAPZP@PZPQP8O2P\P\P\12\4PKD7fLR]?0D3fNR^fMR_P]P^PU12_DR`E9]1]4]9X=ZPXPOP@O2PYPYPY12YMPHD7A0\BS%1]Ra12]BRbP_P_P_P`P8D7fOR`P^P_P`PX12^GE9]4X7aP]P]P]PbPbD7P^P_P]PUPDP5EBW4POP9P4F?W1W4W9PKP8PHPGP1M9AW0PGP8E;b0W2P?P8E>b2W1P8O1b1W0P4P8P3O3W2W0W1XKDXJBP3P4P8O3p,1ERbp,1ARcPI]8PJ^8cPKPKPKP3P8O1RJP4P8O1RdD7^3cPLPKP5P3PND6PPPOP1P3P@D6%1QRNPQP9P112QBD6%1RReA3R:9P6PTP;P8g00GVRfg00H3Rgn10110000021010620101107X<eg00HORh12RDP8E;PfP[PTP>P9PBD6PXPXPXP?P8O1P>P8O1D7^3cPZPXPUPZPKPGE9]1]2/@8b1W0P4P8P3O3W2W0W1W@W?W:P5P3P4P8O4n3000310010800000023110510200040101103104000%1@Ri%1MRj%1SRk12S9704A0C41PGPDPBPGP?P9E9[[W6W612@5P4O2P812M1,<j1<j3O2b1W4W7W9X=:XA:P=^8cR=P@PAP?PJPdD4^3cPMPM%:MRjP5P4O1P8D4PBPSPMP9P3O1P4D4[^7i^3cPMPMPjPMP9P5P8F5P7PSPS%:S%1GR7A3GA>703A0I39PKPHPFPKPMP@P:F5[[P8A0H48PLPKP3A3KS@C8PPPOP3P?C8PNPQP1A3QDSRIC8Pe12R9P6PTP;P8PgPfn10110000021010620101107X<ePhA3RGBP8E;PfP[PTP9PMC8A0U>:PZPXPUPZPKPHPBF5]0]5/@8b0W2P4P8P3O3W5W2W0X=FXAGP3P4P8O3PL^8cPP^8cPQPQPQPJPdD7^3cPNPQP5P3PID6PePRP1P3P@D6P[PTP9P1A3TFDD6PVPW\cRTP6PX%1Y\cP8P>P8n10110000021010620101107X>VA3U:9A3UHGP8E=A0T9GPWPbP6PZPbP8PAP4n10110000021010620101107X>WA3X>:A3XKFP4E=A0b>KA0b?OP8A0bAQPbPR%1_RW\c?0@QR6PWP_P4P@PKD6P`P`P`PBP8O1RTPSP8O1D7^3cfPRVP`P^PVPZPXPQF5]0]5[X:bPa\c?0AOP8P6%1^R6\cPRP6^8cP6P^PXPMPOD6ROPVPV%:VR^PJPTD4^3cfQR6PVP`P6PYPZPRF5]0]5W6PWP_PUP@PKD6P8PO%1`ROA3`ZSP6P6%:6R`PZP8O1PDP8O1D4^3cfRRKP6PVPKP\PYP4F5]0X6OPVPVP^PXP8O1PTD4^3c%1VRTA3VYBROP6P6P`P6P\PZP8F5fSRZPKP6PZP]P\A3K]GF5]4X7TPVPVP^PVPYPXPOF5PKP6PVP\PYPDPXP8PGP8O1PJO3X3cFDW4PRP3PQF?W;PQP8E;b;W2PMP8E>b;W5P@P8E>b5W0P8O1b0P8O1b0W2P4P8P3O3W5W2W0WHWGX<bP5P3P4P8O4n3000310010800000023010510200041101103104000A3D?:90E4A0741PHPFPGPHP@PAP9F5[[X6CX6kA3S:1P4O2P8A3B>9,<C1<C3O2b0W4X7iW1W9X@=W?X:bP5P3P8P4M:CW9W7XC<WBWFXE2XD0o"). Qed.

(* [comment removed for export] *)
Section ERUNS.
Variable O : Type.
Variable sel : O -> E -> option A.
Variable upd : O -> E -> A -> O.

Fixpoint eruns (R : Type) (o : O) (t : stree R) {struct t} : stree (O * R) :=
  match t with
  | SRet r => SRet (o, r)
  | SVis e k =>
      match sel o e with
      | Some a => eruns (upd o e a) (k a)
      | None => SVis e (fun a => eruns (upd o e a) (k a))
      end
  end.

Lemma eruns_ret : forall R o (r : R), eruns o (SRet r) = SRet (o, r).
Proof.
ltac2:(KReplay.run1 (kr_t_STree ()) ["STREE"; "ERUNS"] "h01Rh11oh21rp;2p;1p;4p,1OR0p4p300R1p1001eR2p609311001p8P1P2p6094111000p8P1p100<<p609311000p8P1p100Hkp4p710p8p200R1p100IHp609611111000p8g00JVj24Tg0033j13Tg00K6j40Tg00:lj21Tg004Cj22Tf1R2f2R3,40R4#3P0P3P2f0C0,14'2W2X10X01o"). Qed.

Lemma eruns_vis_keep : forall R o e (k : A -> stree R),
  sel o e = None -> eruns o (SVis e k) = SVis e (fun a => eruns (upd o e a) (k a)).
Proof.
ltac2:(KReplay.run1 (kr_t_STree ()) ["STREE"; "ERUNS"] "p'0h01ai001ah11oh21Rh31eh41ki011xp;1p;3p;2p;6p200R0g00IHR1p609611111000p8g0033j10Tg00KVR2j18Tg00L8j17Tg00A>j31Tg00JVj24TP1j33Tg004]j32Tg004Cj26Tg001Gj65Tp,1OR1p,1Ep,1AR3f3R4#0[%83R5p,3selR6f2R7f1R8O2%73R931P5P9f5R9,41R:#0P2P3f6R2,41#0f0R;p,3updR<P9f4R=P;O3P4P;O1532R2P2X0392:4R:n10110100021010000;1:X15141=R1#0R5P<P=P4P;O3P7P;O1539X039217R1'6P6P4P7O2P;E5A2=7893=4=151eUW4W3W1X20o"). Qed.

Lemma eruns_vis_sel : forall R o e a (k : A -> stree R),
  sel o e = Some a -> eruns o (SVis e k) = eruns (upd o e a) (k a).
Proof.
ltac2:(KReplay.run1 (kr_t_STree ()) ["STREE"; "ERUNS"] "p'0h01ai001ah11oh21Rh31eh41ki011xp;1p;2p;3p;6p200R0g00IHR1p609611111000p8g0033j11Tg00KVR2j18Tg00LZj24Tg00A>j32Tg00JVj23TP1j30Tg004]j35Tg004Cj27Tg001Gj66Tp,1OR1p,1Ep,1AR3f4R4#1\3%83R5p,3selR6f3R7f2R8O2f1R9,4332P51438f6R:,31R;#1P2P3f7R2,31#1f0R<p,3updR=P:f5R>P<O3P7P<O1502R2P2X0395;4n10110100021010000P=P>P4P7O3P8P7O150:32X15131>#1R1P=P4P7P8O3P9P8O150>R8'7P6P4P7O2P<E6A5>7990>4=218eUW4W0W3W1X20o"). Qed.

Lemma eruns_sbind : forall R S o (t : stree R) (g : R -> stree S),
  steq (eruns o (sbind t g)) (sbind (eruns o t) (fun x => eruns (fst x) (g (snd x)))).
Proof.
ltac2:(KReplay.run1 (kr_t_STree ()) ["STREE"; "ERUNS"] "p'0h01ai001ah11oi011oh21xi021xh31gh41th51Hh61Rh71Sh81eh91kh:2o0h;1rp;1p;2p;4p;3p;5p;6p200R0g005mR1p609311001p8P0g001eR2p609311001p8P0g00HkR3p4p7210p8P0g00IHR4p609611111000R5p8p201R6P2p6094111000p8P6g00<<R7p609311000p8P6P5p8g0033j14Tg00JVj23TP2j41TP4j30TP3j37Tg00M<j36Tg007?j32TP7j2<Tg00:lj2;Tg00KVR7j1:Tg004]j35Tg009]j58TP1j69Tp,1OR1f2R3#4f3R4%44f5R2%42R5[R81312R9f1R:f6R;P2P3f0R<C1502131;R=P9A0;:3f7R>=71<P:A61><O150;X2=R?C132]3^11W4P<P3O1902:,<9P;P21;;3R@P<C1902:P=P9A0;:@P?C1529eX38X11X;4p,1Ep,1AR8P5[%4>\>R5131>R9f8R?P>P4P3O1R@P<C190>:131?R=P9A0?:@f9R@=71<P:A61@<O150?X2=RAC132]3^11\8p,3selP:f4RBO2%:8P7P8131@RCP7P8f:RD,31RE#4P<p,3updRFPBP>P<O3RGf;RHPDP;P<O1RIP4C150DRJPJX0895C;n10110200021010000PEPCP7P8131HR7#4P<A0HGIRIPIX0895E;n10110200021010000A71H<P4A61H<O150DX2ERKC132P<P2P<PGP4O3P7PEPIf<RI=71<PBA61I<O150HX27C192EJeX08P<O1P=P2PFP4P;P<O3R;PDP@P2P<O1RFP3C150@X08RJPEPCA0D;FRFPKC1X08PBP<P;P3O3X08D8A5=2JPCP=PFX0895C2A71D<P3A61D<O150@X2CC152=en10110100021010000b:P?P>A5?B4RBP<C190>:P=P9A0?:BPAC1529eX35X11W5W9W8P<P:E9W4W1X76X60o"). Qed.
End ERUNS.

(* [comment removed for export] *)
Section RUN.
Variable O : Type.
Variable oracle : O -> E -> A * O.

Fixpoint srun (R : Type) (o : O) (t : stree R) {struct t} : list (E * A) * O * R :=
  match t with
  | SRet r => (nil, o, r)
  | SVis e k =>
      let (a, o1) := oracle o e in
      let '(tr, o2, r) := srun o1 (k a) in
      ((e, a) :: tr, o2, r)
  end.
End RUN.

(* [comment removed for export] *)
Definition srun0 (f : E -> A) (R : Type) (t : stree R) : list (E * A) * R :=
  let '(tr, _, r) := srun (fun (_ : unit) e => (f e, tt)) tt t in (tr, r).

End STREE.

Arguments SRet {E A R} r.
Arguments SVis {E A R} e k.
Arguments sbind {E A R S} t f.
Arguments smap {E A R S} f t.
Arguments steq {E A R} _ _.
Arguments strel {E A R1 R2} RR _ _.
Arguments eruns {E A O} sel upd {R} o t.
Arguments srun {E A O} oracle {R} o t.
Arguments srun0 {E A} f {R} t.

Declare Scope stree_scope.
Notation "x <-- c1 ;; c2" := (sbind c1 (fun x => c2))
  (at level 65, c1 at next level, right associativity) : stree_scope.
Notation "' pat <-- c1 ;; c2" := (sbind c1 (fun x__ => match x__ with pat => c2 end))
  (at level 65, pat pattern, c1 at next level, right associativity) : stree_scope.

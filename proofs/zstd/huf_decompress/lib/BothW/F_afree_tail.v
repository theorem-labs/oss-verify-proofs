(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase AQConst ABytes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AKit AKit2 AKitQ F_apoison F_aenqueue F_adrain F_aput.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_afree_tail () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideI47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7and_indK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00C47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes4prod01I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlI47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00I47Corelib5Lists7ListDef6Forall00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List=Exists_existsc5ARocqVerifyHarness?AgentSubmission5BothW<F_afree_tail;outside_In8K46Stdlib9micromega6VarMap1t01C47Corelib5Lists7ListDef:Forall_indC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4sclrC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4iclrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPK46Stdlib9micromega5Tauto8GFormula03I5ARocqVerifyHarness?AgentSubmission3Lib8RunConst9runConstT00".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_F_afree_tail ()) [] "p'0h01Hh12H0h22hih32loh41xh51Eh62H1h72H2h82HIh91Wh:1ah;1bh<1eh=2H3h>2H4h?2IHh@2a0hA1li001pi011zp;1p;2p;3p;5p;6p;4p;8p10000p4p7210g000\R0p4p710p8g001:j1ETg001Zj22Tg002PR1j2ATg0030j35Tg003Gj20Tg003cj1:Tg004<j23Tg004Xj2<Tg0057j58Tg005Tj1@Tg0064j39Tg006Tj27Tg006oj34Tg007IR2j2DTg007cj6?Tg008@j4>TP0j8=Tg008[j5CTg009=j4BTg009]R0P0f1R3f0R4CBp=1f2R5/33/74p=;1734#:p=6g00:;R6#ER7P6f3R8/251A00R91153R:f4R;3510;59;8;R<#:R=[[^20^30^40R>X97g00:mg00;IR?f5R@,3;RA10@8RBP?f6RC/0;1<?8W7X6AP4D8X1<P=eW8W0X20X30X40%@6R</25A59:<P=[[^20^30^40eP1P0P0A96@;/25A96C@959:P=[[^20^30^40\>^A7P413C5105@'612;5'7f7R</1CRD=49:A59:@'DP2f8R2/1<1185RE549A59EC16ABP4f9RB/1211;8RA549P9P0P1P0P0P0P4P3n2001100000120101101X<9f:RE/1BRF11@;RGP4E?A40E@RHP9P0P1P0P0P0P4P4n2001100000120101101X<9f;R1/1ERI11C@RJP3E?PHA401Cf=RH=402P0P2f?RK/311014'612H1'7f@RL/13=49If<RM/3H10H1'6RN]5]0X;0f>RO/3ERP10E2'612ME'711KB=49FP0P1114111M1549133O10OMR1'612LO'713OK10KH'6RF]0]5X:0A49II12KH,7NA;HO1R1PFfARO/2KP?fBRN/2L13LORI10OKP?10NLfCRO,3NRKfDRQ/0NRNP@fERR,3Q10ROP3P4C>O1W>W1P?\NRN\KP4P5O1RKPNPKP?1<?4b1b6b1W=X0IP5D8W7X6FP3D8W1%:1eW0W5PLP5P4P3G=W5W0PHP3P<P;G=UUP4O1b1P4O1b1W5P4O1A59A<P<PCP@P;13EC10CB'6RA122CRCPC12B<R<13M2RL10BMRMP8PP10EHP3P4C>O1W7W0RHP?\M\LRLP3b0W6X1AP8D8PAPCA59G2PHPLP8b0X6<X1AP8D8O5W8P4O1n200100000021100010000W8W0X20X30X40A96J;/25A96D@959:P=[[^20^30^40eX?>X97X;0X:0P3P4O2n2001100000121101101X@6P4DCW9o"). Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
ltac2:(KReplay.run1 (kr_t_F_afree_tail ()) [] "p'0h02jvh11xi001xh21Hh34__x1h44__x2h54__x3h62ivh72HPh81Wh91lh:1Ah;2HFh<1Ph=7__arithh>4__ffh?8__varmaph@5__withA4__x4hB4__x5hC2x0hD2H1hE2H2hF2HEhG2HIhH2HOhI2IHhJ2W'hK2hihL3hi'hM2lohN3lo'i011pi021zp;1p;2p;3p;4p;6p;7p;8p10000p4p7210p1000\p4p710p8g001:j1LTg004<j20Tg007IR0j2;Tg00;fj3JTg001Zj27Tg005Tj1OTg0064j3>Tg003cj1:Tg00<Gj1FTg00<fj2@Tg00=Oj2KTg00>;j2ETg00>Yj4DTg00?7j1ZTg00?Uj1YTg00@@j1QTg00@ej2?Tg00AHj1XTg00Ajj1PTg00BOj4ITg00C:j2WTg00C\j2VTg00D6j2UTg006oj3TTg00Dbj3STg00EAj4RTg00F3R1j3HTg0030j3BTg006TR2j25Tg00FPR3j2GTg00Fjj3iTg00GLj6hTg00HOj1gTg008@j4fTg00Hmj7eTg00IPj2bTg00JEj3^Tg00Jbj3]Tg009=j4_Tg003Gj2\Tg00K?j3`Tg00Khj7aTg00LLj7[Tg00M0j6cTg00MTj8dTg009]R4f0R57^4p=3A]445p=4f3R6f2R7'0f1R8/05'5p=1g00:;R9?H85p=8P4P4P8P5C_p=610671\85'5p=2A`485p==P4P8g00N8P5CIp=AP8g00N_R:g00O>R;P;g00O^R<P5g00P>Fap=9P7P:P;P;P<P8P5F[p=NP8P:P;P;P<P5Ecp=MP6P:P;P;P<P7P8P5Gdp=CAB985p=<%L9R:%35R=%45R>'0R?P>%48R@%38RAP=C1X09RB/88';X69=J981775P9f4RC,8B,;?X691757X8:g00P^%O9/78eg002PRDP4P410A@P>%47%37P=C1X09f6RA'8';f8R@,8B,;?X69=J98177AA>9C6f7RE'7[[[^9:P51678RF#3RG%4FRH'0P>1667RI#4%3IP=C1X09f9RI'8';f;RJ,8B,;?X69=J98177If5R?f:RBPBPCC2#:176BP010C?P>PAP?P=C1X09f<R0'8PAPJPJP?C2#:P710?Ag00Q:RKg00QfRL#FRM#FRN,@4RO1@4MRM1@4LRL'='=g00RERP'K%OKRQ3>%LKRRP41E47P81E46CD%Z4RS%Y4RTg00S1RU#Q,?4RV1?4URW'A,9T%X;R;%PURU,?4RX,AW,9TP4PXg00SVRYPVCI,9T5NT,MTRZCC1WT<R<P5P7g00T=R[g00T]R\'V1U57=T[\dg00U==S48CRR\b>b?b@X34X44X541075P8P7P7P6C2g00;IR[[[^34^44^54P5PEf=R]P@P8O4b=WFP5O1P>PEPAP=C1X09/8]P1p4p710R1p-0\5R^%L8R_P2AH785ABC57P6P5O1'5X16,G6[R`AB658P7P5O1'5X17,G7AH678Ra[AB?56PCP5O1'5X1C,GC\aAi785P8n2001000000120000000W9W<W:P`^9_^<^^:1P5P9P>PIP@P=C1R1X09f?R^P8O4f@R_,<5/51X19,G9P3P9fAR3,<5P>PBPIP=C1'5X19PBP^P^PIC2#:P5PDP4P4fDRD,<5P>P]P0P=C1'5f>fCR=P=P]C2#:[P51685R]fGR>'<%4]P_P^%3]C1'5P2fH,<FPHP3P_PGC1fBP>P>P3C2#:P516C6fJR3'<16?CRG#4PDP=%3GC1P216A?RA#4fER2'0%3A,0DfFfKRDPDP2C2#:P516@E#4/0>16I@#3,0>fPR>fNR@PBPIfMP?EhPBP@P@PIC2#:%FNRN#F,@4RI1@4N/=L'=/KP1=OM,=I/KP=>KQ5>KPRP4P41E4CP7%g4RRCDP8P41E4?P6PRCDCDPSPT%PU,?4RS/AX,9TP4PXPY%QU,?4RUCI,9T5NT,MTP;PT1AVU,9TP;PT1ASW,9TP;PZCCCCCCP<P\b>b?b@X34X44X54XA4XB4P6P8P8PCC2P[[106?10?7P6PCPCP?C2P[[[[[^34^44^54^A4^B4P5PJP0P3P>PDP8P7P6O8b=b2WEWDP8P5O2n2001000000121000000W2WGP8P5O2n2001000000121000000W2XL4XN4P8P5O2n2001101000121102102XC9P8P5O2n2001000000121100000b7b2W7P5O1n200100000021000011000P5CfA>9G6/7BeWIW;W7X8:XK4XM4P8P5O2n2001101000121102102XC9PCP7FeWHX141b78eW;XJ:W8o"). Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Ltac with_sclr tac := idtac; match goal with H : sclr ?a ?n |- _ => with_band H tac | _ => tac end.  (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac iclr_of H := clear -H; unfold iclr, AIMG_LO, AIMG_HI in *; lia.
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_F_afree_tail ()) [] "h04__x1h14__x2h21Hh37__arithh44__ffh58__varmaph65__with71kh82G1h92G2h:1ah;1np;2p;1p;4p;3p;7p;8p10000p4p7210p1000\p4p710p8g00U[j2WTg004<j20Tg00VPj22Tg00Ajj11Tg00Vmj1;Tg00@@j16Tg006Tj23Tg00WKj29Tg00FPj2VTg005Tj1UTg001:j1TTg00>;j2PTg00HOj1OTg00>Yj4NTg00?7j1LTg00?Uj1KTg00Whj2:Tg00@ej2ATg00AHj1ITg00XKj3>Tg00Xnj3=Tg00C:j2HTg00C\j2JTg00D6j2GTg006oj3FTg00Dbj3MTg00EAj4ETg00YQj4CTg00BOj4QTg00Khj7DTg00LLj7RTg00MTj8STf0R0#1#1#1#1p=?%10#1#1#1#1#1#1#1p=5%10#1p=B%60#6p=@%60#6#6#6p=7f2R1g00N_R2g00O>R3P3g00O^R4g009]R5f1R6g00N8P0CQg00P>FDp=4P1P2P3P3P4P6P0FRp=8f3R7P2P3P3P4P1P6P0GSp=<1W60g00U=R2/011271g00S1R8#1R9#?#5R:#1#B#5#5#5#5#5#5#;R;'0g007If4R</27%@8#7#7#7#1#6#@#?#5#;R='0%7:#7#7#7#1#B#?#5#;R:/0<1020R>%;8R?,00'3R@f6RAf5RB'2190;,2=RC'019:0RD/0A'3'3X75,V5P112B</0=P5f7RE/2A/0C10DE'3,3@X75R@P2g00Q:RD#URC%TDRDP51P51P6%O5CNRF%L5RG%K5RH1:52RI1A58R854H%I3R3PH1A599>58R91:5=RJ54HP3A4HII1:5?RK94HIRL58H1:5;RM9=5I9>5J94H91:5:RN==5I=4H858H58HC<C<1HH4R4P0P1g00T=RIg00T]RO'J1G01=FIOdAM526CEROb4b5b6X05X151261/0=1022102?RI'31217RP192;,2='019:2/01'3'3[\>^05^15P0PAPEP<P6O4b3CCW2P0O110:BP5P@P?PCPDPFPGPHA4H9MP3PHA4HN8P3A4HKK98HLA=5KM9>5J94H9A=5NK=4H858H58HC<C<P4POb4b5b6X05X151206/0;10:610??,3I19?;,2=,0P19:?/01'3'3[[^05^15P0PAPEP7P6O4b3CCW2P0O1n200100001021100011000W9W8W2X;5X:5o"). Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6352896 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_F_afree_tail ()) [] "h04__x1h14__x2h22H0h31kh41Hh57__arithh64__ffh78__varmaph85__with92G2h:1ah;1np;2p;1p;4p;3p;7p;8p10000p4p7210p1000\p4p710p8g00Ykj2YTg00Ajj11Tg00Vmj1<Tg004<j20Tg00@@j1:Tg007IR0j2DTg00VPj23Tg00WKj27Tg00FPj2ETg005Tj1VTg001:j1UTg00>;j2TTg00HOj1RTg00>Yj4QTg00?7j1PTg00?Uj1NTg00@ej2BTg00XKj3@Tg00Whj28Tg00AHj1KTg00Xnj3>Tg00C:j2JTg00C\j2ITg00D6j2HTg006oj3MTg00Dbj3GTg00EAj4OTg00YQj4CTg006TR1j2?Tg00BOj4FTg00Khj7STg00LLj7XTg00MTj8WTf0R2#1#1p=L%12#1#1#1#1#1#1#1p=5%12#1#1#1p=Af2R3f1R4'3/02p=;1034/?2p=61?42,?3p==P3g00N_R5g00O>R6P6g00O^R7g009]R8P4g00N8P2CFg00P>FSp=2P3P5P6P6P7P4P2FXp=4f3R9P5P6P6P7P3P4P2GWp=91Y42g00S1R5#1R:#1#L#5R;#AR<#5#5#5#5#5#5#<R=9;34P1%<;R;/09R1%<<R<9;93%:5#1#A#:#:#:#:#A#5#<R>/09'Dg00U=R?%<5R@,02762RAf5RB,0;RCf4RD,3B172=,3<RE17>2RF/0B363=X38,E8P4f6RG?;B<10>G'DP0f7R0?;G<10>0f9RG,0;f8RB,3G10FG76E5=AX38,E8P2A;B0<P8f:RH,0;13HG10FH76E5=AX38RAP?g00Q:RE#VRF%UEREP81T83P4%R8CQRI%P8RJ%N8RK1B85R51B8:5@8R:188<RL52K%K6R6PK188;=2K5RMP6188?RN=2KN188@RO92KNRP54K188=RQ9>8N9@8L92K:188>RR=>8N=2K554K94KM54KC9C91JK7R7P2P3g00T=RNg00T]RS'I1H23=MNSdAG8?4CORSb6b7b8X08X181324RN/0<10;410?@RT96??10;3R;133917?=,3<17>?/03363=[[^08^18P2PGPHP4PDO4b5CCW2P2O110>BP8PAP@PFPEPIPJPKA2K:QP6PKA2KR5P6PKPMP6A2KOO94KPA>8OQ9@8L92K:A>8RO=2K554K94KM54KC9C9C9P7PSb6b7b8X08X1810N=10>410@@,?T139D17@=,3<17>@/09367=1\;[[^08^18P2PGPHP0P4PDO5b5CCW2P2O1n200100000021100011000W2X4CP4P2O2n2001000000121000000W9W4X;8X:8o"). Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6352896 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof.
ltac2:(KReplay.run1 (kr_t_F_afree_tail ()) [] "h01Hh14__p1h24__x1h34__x2h44__x3h51kh62rch72H1h87__arithh94__ffh:8__varmaph;5__with<2H0h=2hih>2lop;3p;1p;2p;4p;6p;7p;8p10000p4p7210p1000\p4p710p8g00Z`j3bTg00[Uj1aTg00@@j15Tg00Ajj11Tg00Vmj19Tg00\Sj18Tg004<j20Tg006TR0j2>Tg00WKj2=Tg00VPj2ETg00FPj2JTg00<Gj1DTg00<fj2CTg00K?j3ITg00=Oj2VTg005Tj1UTg0064j3TTg001:j1STg00>;j2GTg00>Yj4RTg00?7j1QTg00?Uj1PTg00@ej2BTg00]Ij6OTg00AHj1NTg00Whj2FTg00Xnj3ATg00XKj3HTg00C:j2MTg00C\j2`Tg00D6j2_Tg006oj3^Tg00Dbj3[Tg00EAj4ZTg00YQj4KTg00BOj4YTg00Khj7\Tg00LLj7WTg00MTj8]Tf0R1#5#5#5#5p=7%51#5p=X%11#1p=@%11#1#1#1p=:%11#1#1#1#1#1#1#1p=3f2R2f1R3'0/>1p=21>31,>2p=?g009]R4/F1p=;P2g00N_R5g00O>R6P6g00O^R7P4P3g00N8P1CYg00P>F\p=4P2P5P6P6P7P3P1FWp=6f3R8P5P6P6P7P2P3P1G]p=<1031,>2p=Lg00]mR9Ab231%a8g00S1R:#5R;#5#7#7#7R<#1#5#XR=#5#7#1#@#:#3#3#9R>%88R?%5<#7#7#1#@#:#3#3#9R<,0?32g007I%5:#1#:#7#:#3#9R?/08R@%:=#3#9R=,02RA'>%1:RB#:#3RC#7#7#7#7#1#@#:#3#9RDf4RE#8,02728g00U=RF%9:RG,01721RHf5RI,0?RJ1=D1RK%1C#@#3#3#3#3#3#3#9RC,=1,E=RLf6RM#8,0ERN52E72I3?X54,J4P3108=92?EP0PJ10E=f7RJ,0?ROf8#8,0M92ML92KJ5?HX54,J4RMP110J=P4f:RP,0?f9RQf;#8RR,0Q72L92KP5?HX54RHPFp-0RKg00Q:RLg00QfRS#D#DRT#D,C41C4T1C4S5I45I4g00RE'V%UL3TRS%SLRLP41G42P31G48CRRT%Q4RU%P4RV%;>1B4;R;54VPVP5P6P6P7PIEOR556V%N6R6PV1B4BRB%;=RW54VP6PV%;?1B4:R:54VRXP61F4FRY=4VY%;GRZ94VYR[56V%;DR\=A4Y=4V:%;CR]9A4Y9H4W94VBA4VB;RY56V56V96VX56VC<C<C<1MV7R7P1P2g00T=R^g00T]R_'`1_12=^^_dA[4F3CZR_b9b:b;X24X34X44W1A2>2810?210FGR?92FF1=DF1=FC,E=10EIRF52E7287?@[\A[^24^34^44^1KP110R<PRPQPPPJP3P2O7b8CKW7X0OP3P1O2n2001000010121000000W0P1O1%8I,0892DEP010DIPNPMP110DJ%8Q,0JP4PHPGPSPLPTPUPV%;<94V;96V5P6PVPYP6PVA4V\:P6A4VZZ96V[AA4\Z=4V:AA4Z]9H4W94VB=6VY56V96VX56VC<C<C<P7P_b9b:b;X24X34X44X1KAL82<102810D2AL?GG1=DG1=GC,E==2EF7287?@[[[^24^34^44^1KP110>RPRPQPPPJP3P2O7b8CKW7W0P3P1O2n2001000010121000000W0P1O1n200100001021100011000b<W0X=4X>4X69P1O1X69P1O1W6o"). Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Inductive enq_kind :=
| EkAppend (nx bsz cnt : Z) (hs : list word) (cnt24 : Z) (maxc csz stj : word)
| EkNew (full : bool) (nx bsz cnt24 : Z) (maxc csz stj idxw : word) (chunks : list word) (spacebeg b : Z) (hs : list word).

(* [comment removed for export] *)
Record gqd := mkGQ { g_drain : bool; g_full : bool; g_nb : Z; g_fst : Z; g_lst : Z; g_qb : Z; g_nx : Z }.

Definition ek_nb (ek : enq_kind) (nb : Z) : Z := match ek with EkAppend _ _ _ _ _ _ _ _ => nb | EkNew _ _ _ _ _ _ _ _ _ _ _ _ => nb + 1 end.
Definition ek_fst (ek : enq_kind) (fst0 : Z) : Z :=
  match ek with EkAppend _ _ _ _ _ _ _ _ => fst0 | EkNew full _ _ _ _ _ _ _ _ _ b _ => if full then fst0 else b end.
Definition ek_lst (ek : enq_kind) (lst : Z) : Z := match ek with EkAppend _ _ _ _ _ _ _ _ => lst | EkNew _ _ _ _ _ _ _ _ _ _ b _ => b end.
Definition ek_delta (ek : enq_kind) (n : Z) : Z := match ek with EkAppend _ _ _ _ _ _ _ _ => n | EkNew _ _ _ _ _ _ _ _ _ _ _ _ => n + 8192 end.
Definition ek_b (ek : enq_kind) (lst : Z) : Z := match ek with EkAppend _ _ _ _ _ _ _ _ => lst | EkNew _ _ _ _ _ _ _ _ _ _ b _ => b end.
Definition dk_glst (g : gqd) (lst : Z) : Z := if g_drain g then g_lst g else lst.

(* [comment removed for export] *)
Definition ek_pre (ek : enq_kind) (RNG : footprint) (t nb lst n hm : Z) (m : amem) : Prop :=
  match ek with
  | EkAppend nx bsz cnt hs cnt24 maxc csz stj =>
         0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 cnt)]
      /\ 0 <= cnt < 1021 /\ 0 <= bsz /\ bsz + n < 2^63 /\ 0 <= nx < 2^64
      /\ u64arr bsegs m (lst + 24) hs /\ length hs = Z.to_nat cnt
      /\ (exists bs, rw_cells bsegs m (lst + 24 + 8 * cnt) [CB (Z.to_nat (8192 - 24 - 8 * cnt)) bs])
      /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP /\ (t + 4096 <= lst \/ lst + 8192 <= t) /\ (hm + 16 <= lst \/ lst + 8192 <= hm)
      /\ rw_cells bsegs m (t + 2128) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 csz] /\ rw_cells bsegs m (t + 2784) [C8 stj]   (* [comment removed for export] *)
      /\ rng RNG lst 8192
  | EkNew full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs =>
         (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
                    /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
                    /\ u64arr bsegs m (lst + 24) hs /\ length hs = 1021%nat    (* [comment removed for export] *)
                    /\ rng RNG lst 8192
          else nb = 0 /\ lst = 0)
      /\ rw_cells bsegs m 0xb6cb8 [C8 (Z_to_bv 64 spacebeg)]
      /\ rw_cells bsegs m (t + 2128) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 csz]
      /\ u32arr bsegs m (t + 2128 + 16) chunks /\ length chunks = 16%nat
      /\ 0 < cnt24 <= 16 /\ nth_error chunks (Z.to_nat (cnt24 - 1)) = Some idxw /\ bv_unsigned idxw < 2^32
      /\ rw_cells bsegs m (t + 2784) [C8 stj]
      /\ b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw
      /\ (exists bs, rw_cells bsegs m b [CB (Z.to_nat 8192) bs])
      /\ 0 < spacebeg /\ 0x10007fff8000 <= b /\ b + 8192 <= ATOP
      /\ (t + 4096 <= b \/ b + 8192 <= t) /\ (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) /\ (b + 8192 <= lst \/ lst + 8192 <= b)
      /\ (hm + 16 <= b \/ b + 8192 <= hm) /\ (hm + 16 <= lst \/ lst + 8192 <= hm)
      /\ rng RNG b 8192
  end.

(* [comment removed for export] *)
Definition ek_post (ek : enq_kind) (t lst hm n : Z) (m' : amem) : Prop :=
  match ek with
  | EkAppend nx bsz cnt hs cnt24 maxc csz stj =>
         rw_cells bsegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 (bsz + n)); C8 (Z_to_bv 64 (cnt + 1))]
      /\ u64arr bsegs m' (lst + 24) (hs ++ [Z_to_bv 64 hm])
      /\ (exists bs, rw_cells bsegs m' (lst + 24 + 8 * (cnt + 1)) [CB (Z.to_nat (8192 - 24 - 8 * (cnt + 1))) bs])
      /\ rw_cells bsegs m' (t + 2128) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 csz] /\ rw_cells bsegs m' (t + 2784) [C8 stj]
  | EkNew full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs =>
         rw_cells bsegs m' (t + 2128) [C4 (Z_to_bv 64 (cnt24 - 1)); C4 maxc; C8 csz]
      /\ (exists stj' : word, rw_cells bsegs m' (t + 2784) [C8 stj'])
      /\ rw_cells bsegs m' b [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1)]
      /\ u64arr bsegs m' (b + 24) [Z_to_bv 64 hm]
      /\ (exists bs, rw_cells bsegs m' (b + 24 + 8 * 1) [CB (Z.to_nat (8192 - 24 - 8 * 1)) bs])
      /\ (if full then rw_cells bsegs m' lst [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] /\ u64arr bsegs m' (lst + 24) hs else True)
  end.

(* [comment removed for export] *)
Definition dk_pre (ek : enq_kind) (g : gqd) (RNG : footprint) (t lst hm qb' : Z) (m : amem) : Prop :=
     rw_cells bsegs m 0xb7008 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0xb7010 [C8 (Z_to_bv 64 (g_nb g)); C8 (Z_to_bv 64 (g_fst g)); C8 (Z_to_bv 64 (g_lst g)); C8 (Z_to_bv 64 (g_qb g))]
  /\ 0 <= g_nb g < 2^62 /\ 0 <= g_qb g /\ 0 <= g_fst g < 2^64 /\ 0 <= g_lst g < 2^64
  /\ if g_drain g then
          Q_CACHE < qb' /\ g_qb g + qb' <= Q_MAX
       /\ (if g_full g then 0 < g_nb g /\ rw_cells bsegs m (g_lst g) [C8 (Z_to_bv 64 (g_nx g))] /\ 0x10007fff8000 <= g_lst g /\ g_lst g + 8192 <= ATOP
                          /\ (t + 4096 <= g_lst g \/ g_lst g + 8192 <= t) /\ (hm + 16 <= g_lst g \/ g_lst g + 8 <= hm)
                          /\ (lst + 8192 <= g_lst g \/ g_lst g + 8192 <= lst) /\ (ek_b ek lst + 8192 <= g_lst g \/ g_lst g + 8192 <= ek_b ek lst)
                          /\ rng RNG (g_lst g) 8192
           else g_nb g = 0 /\ g_lst g = 0)
     else qb' <= Q_CACHE.

Definition dk_post (g : gqd) (nb' fst' lst' qb' : Z) (m' : amem) : Prop :=
     rw_cells bsegs m' 0xb7008 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ if g_drain g then
          rw_cells bsegs m' 0xb7010 [C8 (Z_to_bv 64 (g_nb g + nb')); C8 (Z_to_bv 64 (if g_full g then g_fst g else fst'));
                                C8 (Z_to_bv 64 lst'); C8 (Z_to_bv 64 (g_qb g + qb'))]
       /\ (if g_full g then rw_cells bsegs m' (g_lst g) [C8 (Z_to_bv 64 fst')] else True)
     else rw_cells bsegs m' 0xb7010 [C8 (Z_to_bv 64 (g_nb g)); C8 (Z_to_bv 64 (g_fst g)); C8 (Z_to_bv 64 (g_lst g)); C8 (Z_to_bv 64 (g_qb g))].
(* [comment removed for export] *)
Definition tcache_post (g : gqd) (nb' fst' lst' qb' : Z) : list cell :=
  if g_drain g then [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  else [C8 (Z_to_bv 64 nb'); C8 (Z_to_bv 64 fst'); C8 (Z_to_bv 64 lst'); C8 (Z_to_bv 64 qb')].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put_tail_post (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);      (* [comment removed for export] *)
              (0xb7008, 0xb7008 + 4); (0xb7010, 0xb7010 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells bsegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells bsegs m' (t + 80) (tcache_post g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n))
    /\ ek_post ek t lst hm n m'
    /\ dk_post g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'.

Lemma put_tail_spec : forall (ek : enq_kind) (g : gqd) (t hm lst : Z) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo : Z) (sjunk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 0xb6f70 -> a1 = Z_to_bv 64 (t + 80) -> a2 = Z_to_bv 64 (t + 208) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0xb6fb0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells bsegs m 0xb2120 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells bsegs m 0xb7b24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  poison_cells m ->
  (* [comment removed for export] *)
  rw_cells bsegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> 0 <= b1 < 256 -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (* [comment removed for export] *)
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  ek_pre ek RNG t nb lst n hm m ->
  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->                                            (* [comment removed for export] *)
  evtF bsegs RNG (put_tail_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x359b4) fc None m (seg_rom bsegs)).
Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Proof.
  intros until sjunk. intros ST CEIL LO MI -> -> -> -> -> QK GF FLG PC HD N B1 AL HLO HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT EK DK RIMG RSTK RT RH RSH TI.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.   (* [comment removed for export] *)
  assert (SHB : 2148243968 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (unfold rup; Z.div_mod_to_equations; lia).
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);      (* [comment removed for export] *)
              (0xb7008, 0xb7008 + 4); (0xb7010, 0xb7010 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof QK as QK0. rw_split QK0 1%nat QMX QK2. clear QK2.
  box DHT.
  (* [comment removed for export] *)
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0];
  [ destruct EK as (NB1 & LB & CNT & BSZ & BSZN & NX & LA & LEN & [junkt LJ] & L0 & L1 & DTL & DHL & CR' & STS' & RL); box DTL; box DHL
  | destruct EK as (FULL & SB & CR & CH & LCH & CNT & NTH & IXS & STS & HB & [junkb BJ] & SBP & B0 & BL1 & DTB & DTL & DBL & DHB & DHL & RB);
    box DTB; box DTL; box DBL; box DHB; box DHL;
    destruct full; [destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1 & LA0 & LEN0 & RL) | destruct FULL as [NB0 LST0]] ];
  unfold dk_glst in *; cbn [ek_pre dk_pre ek_b ek_nb ek_fst ek_lst ek_delta] in *;
  destruct DK as (MX & GC & GNB & GQB & GFST & GLST & DK');
  (destruct (g_drain g) eqn:EGD;
   [ destruct DK' as (QB1 & GQ & GFULL);
     destruct (g_full g) eqn:EGF;
     [destruct GFULL as (G1 & GLB & G3 & G4 & G5 & G6 & G7 & G8 & G9); box G5; box G6; box G7; box G8 | destruct GFULL as [GNB0 GLST0]]
   | rename DK' into QB1 ]);
  rewrite ?EGD in *; cbn [ek_pre dk_pre ek_b ek_nb ek_fst ek_lst ek_delta dk_glst] in *; unfold AIMG_HI in *.
  all: first [assert (QZE : qsz lst = 8192) by (apply qsz_pos; generalize L0; clear; intros; lia) | assert (QZE : qsz lst = 8) by (apply qsz_eq0; exact LST0)]; rewrite QZE in *.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box SH'. box GLB. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80 + 24, t + 80 + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z MUe WMe.
    box LJ. box LB. box QC. box LA.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_append_spec (t + 80) lst cnt RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo hs);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_MAX in *; lia| lia| lia| lia
      | unboxed LB| exact CNT| lia| unfold Q_MAX in *; lia| lia| unboxed LA| exact LEN| exists junkt; unboxed LJ
      | iclr_of TI| atop_facts; lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear LJ LB QC LA.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; lia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; lia). carry CR' MUe WMe ltac:(ub DTL; lia). carry STS' MUe WMe ltac:(ub DTL; lia). clear MUe WMe.
    rename POST into LJ'. rename PC1 into LB'. rename PC2 into LA'. rename PC0 into QC'. destruct LJ' as [junkt' LJ'].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box LB'. box LA'. box LJ'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xb7008, 0xb7008 + 4); (0xb7010, 0xb7010 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 lst (qb + n) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry LB' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry LA' MUd WMd ltac:(rewrite length_app, LEN; cbn [length]; ub DTL; first [ub G7 | pose proof GLST0]; lia). carry LJ' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry CR' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box SH'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80 + 24, t + 80 + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z MUe WMe.
    box LJ. box LB. box QC. box LA.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_append_spec (t + 80) lst cnt RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo hs);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_MAX in *; lia| lia| lia| lia
      | unboxed LB| exact CNT| lia| unfold Q_MAX in *; lia| lia| unboxed LA| exact LEN| exists junkt; unboxed LJ
      | iclr_of TI| atop_facts; lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear LJ LB QC LA.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; lia). carry SH' MUe WMe ltac:(lia). carry CR' MUe WMe ltac:(ub DTL; lia). carry STS' MUe WMe ltac:(ub DTL; lia). clear MUe WMe.
    rename POST into LJ'. rename PC1 into LB'. rename PC2 into LA'. rename PC0 into QC'. destruct LJ' as [junkt' LJ'].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box LB'. box LA'. box LJ'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xb7008, 0xb7008 + 4); (0xb7010, 0xb7010 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 lst (qb + n) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry LB' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry LA' MUd WMd ltac:(rewrite length_app, LEN; cbn [length]; ub DTL; first [ub G7 | pose proof GLST0]; lia). carry LJ' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry CR' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box SH'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80 + 24, t + 80 + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z MUe WMe.
    box LJ. box LB. box QC. box LA.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_append_spec (t + 80) lst cnt RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo hs);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_MAX in *; lia| lia| lia| lia
      | unboxed LB| exact CNT| lia| unfold Q_MAX in *; lia| lia| unboxed LA| exact LEN| exists junkt; unboxed LJ
      | iclr_of TI| atop_facts; lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear LJ LB QC LA.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; lia). carry SH' MUe WMe ltac:(lia). carry CR' MUe WMe ltac:(ub DTL; lia). carry STS' MUe WMe ltac:(ub DTL; lia). clear MUe WMe.
    rename POST into LJ'. rename PC1 into LB'. rename PC2 into LA'. rename PC0 into QC'. destruct LJ' as [junkt' LJ'].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [exfalso; unfold Q_CACHE in *; lia|].   (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box CH. box SH'. box GLB. box LA0.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec true t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xb7008, 0xb7008 + 4); (0xb7010, 0xb7010 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box CH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX CH.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box CH. box SH'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec true t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xb7008, 0xb7008 + 4); (0xb7010, 0xb7010 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box CH. box SH'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec true t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [exfalso; unfold Q_CACHE in *; lia|].   (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box CH. box SH'. box GLB.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec false t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear ST.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xb7008, 0xb7008 + 4); (0xb7010, 0xb7010 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box CH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX CH.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box CH. box SH'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec false t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear ST.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xb7008, 0xb7008 + 4); (0xb7010, 0xb7010 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box CH. box SH'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec false t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear ST.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [exfalso; unfold Q_CACHE in *; lia|].   (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
Qed.
End CANSEC1.

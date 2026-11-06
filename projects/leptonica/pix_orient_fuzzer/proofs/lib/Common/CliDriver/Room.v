(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Room () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6of_natc69OSSVerify5KrLib6Common9CliDriver4Room7room_k0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver4Room6need_kC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver4Room7room_b0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver4Room6need_bC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith4Znat5Nat2Z8inj_succC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega:ZMicromega;ZArithProof01c69OSSVerify5KrLib6Common9CliDriver4Room6fuzz_kC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver4Room6fuzz_bC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_r".
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition DRV_CALLS : Z := 12.
Definition DRV_BYTES : Z := (2^16 + 2^22) + (2^27 - 2^17 + 10 * 2^22) + (2^26 + 2^22).

(* [comment removed for export] *)
Definition room_k0 (FC : Z) : Z := DRV_CALLS + 4 * FC.
Definition room_b0 (FB : Z) : Z := DRV_BYTES + 4 * FB.

(* [comment removed for export] *)
Definition need_k (FC : Z) (j : nat) : Z := (10 - Z.of_nat j) + 1 + 4 * FC.
Definition need_b (FB : Z) (j : nat) (cap : Z) : Z :=
  (2^27 - 2 * cap) + (10 - Z.of_nat j) * 2^22 + (2^26 + 2^22) + 4 * FB.

(* [comment removed for export] *)
Definition fuzz_k (FC : Z) (rem : Z) : Z := rem * FC.
Definition fuzz_b (FB : Z) (rem : Z) : Z := rem * FB.

Lemma need0 : forall FC FB, room_k0 FC - 1 = need_k FC 0 /\ room_b0 FB - (65536 + 2^22) = need_b FB 0 65536.
Proof.
ltac2:(KReplay.run1 (kr_t_Room ()) [] "h02Hah14__x1h24__x2h32FBh42FCh57__arithh64__ffh76__sat0h86__sat1h96__sat2h:6__sat3h;6__sat4h<6__sat5h=6__sat6h>6__sat7h?6__sat8h@6__sat9hA8__varmaphB5__witp;1p;2p;3p;4p;7g0000j14Tg000Uj12Tg0013j19Tg001Xj2>Tg002@j2ATg002]j3?Tg003Aj1TTg003aj1QTg004Aj2MTg004_j1KTg005=j4JTg005[j1_Tg0069j1ZTg006dj2ITg007Gj3CTg007jj3@Tg008Mj2HTg0090j4GTg009[j1<Tg00:9j3BTg00:\j7STg00;@j2RTg00;bj2PTg00<<j2OTg00<hj3ETg00=Bj3LTg00=aj4NTg00>Sj26Tg00?0j21Tg00?Mj25Tg00?jj2DTg00@Ej1UTg00@ej1^Tg00Agj2]Tg00Bhj1\Tg00Cjj3YTg00Dkj2WTg00EGj2XTg00Ecj3VTg00FFj7[Tg00FjR0f0R1'Wp=;1X01p=3g00GHR2/H1p=:f1R3=V21p=0P3g00GfR4g00HER5P5g00HeR6P1g00IEF[p=F%41#4p=7f2R7/13/11p==AE231p=8g00IeR8#4R9#2R:%49R;#4R<#9R=#2R>'>%;:R?%3>1A:>R@#;[[%3:RAg00JJRBA?:>3UW0%3@\B^0A%4<R<#2R>,>:%3>1A:>RC#;[\?A?:>3VBX0A%3C\B^0A%99R>#9#4RD#2RE,>:%3E1A:ERF#;[\?A?:E3VBX0A%3F\B^0A%98#4RE#9RG#9RH#2RI,>:%3I1A:IRJ#;[\?A?:I3VBX0A%3J\B^0A%4GRG#2RI,>:%3I1A:IRK#;[\?A?:I3VBX0A%3K\B^0Ag00JfRA#T%QAP21M27P3%K2CJ%_2%Z2RAP4P5P5P6P2%4E#2RE#:%2;R;#:R51I285C2R4'0%28R8#:RB5@2g00KRRI%4>#2R>#:R?1H205@2RL/0B/04CG,FAP2%::R4%<<5B2%<D9B24RD'0%<H9B24RH%<=9B245@2AC2?D'0'0%<G9B24/0DRG'01I299C25R5'0%7<#7#7#7#7#7#2R<#:R9/0D5@2PIAC2499@2HAC2LD'0/0G/05CG,FAFS1RA6P1P7g00L9RAg00LYR6'P1O17=EA6dAL203CNb6bAbBX12X2216;1R6,1E/5815>0R0?=86'811CF15J@16>F'111KFRK3=R@16;3R;'111<FRC'516:<,5JRJ160F'1?=K;'8'D^12^22P1f;f<O2b5b7b8b9b:b;b<b=b>b?b@11E;/58g00M9RE#U,5>R>?=8;'811@6/5C16>F,1J?=K6'8'De%^3/581]3E'8%\1/5CAY1E<'8'DeX32X42o"). Qed.

(* [comment removed for export] *)
Lemma need_grow : forall FC FB j cap,
  need_k FC (S j) = need_k FC j - 1 /\ need_b FB (S j) (2 * cap) = need_b FB j cap - (2 * cap + 2^22).
Proof.
ltac2:(KReplay.run1 (kr_t_Room ()) [] "h02Hah14__x1h24__x2h34__x3h44__x4h52FBh62FCh77__arithh84__ffh96__sat0h:6__sat1h;6__sat2h<6__sat3h=6__sat4h>6__sat5h?8__varmaph@5__withA3caphB4cstrhC1jhD1zp;1p;2p;3p;4p;7p;6g00@Ej1?Tg00MXj1aTg0000j16Tg0013j1;Tg000Uj15Tg00?Mj22Tg00?0j20Tg00>Sj23Tg002@j2ATg00?jj2CTg00N6j1MTg001Xj2ETg00Dkj2>Tg002]j3DTg003Aj1XTg003aj1WTg004Aj2ITg004_j1VTg005=j4HTg005[j1STg0069j1RTg008Mj2<Tg006dj2=Tg0090j4GTg009[j1BTg00:9j3@Tg00:\j7OTg00;@j2NTg00;bj2PTg00<<j2QTg00<hj3JTg00=Bj3TTg00=aj4UTg00N[j1`Tg00O:j1_Tg00O^j6^Tg00Agj2LTg00Cjj3KTg00EGj2]Tg00Ecj3ZTg007jj3[Tg007Gj3\Tg00FFj7YTf2R0f1R1'0f0R2'0p=:g00GHR3?J12p=9g00FjR4/]2p=4AZ312p=1A[312p=8A\312p=7P1g00GfR5g00HER6P6g00HeR7P2g00IEFYp=Fg00P<P3%?1R8#ag00IeR9#6R:#;R;#6#5R</22R=%59R>'0R?%6:R@#5RAf4RB'3RC'0%?0,2<RD?:>C/2>'9%5:RC%;9RE#6#;RF#;RG#5RH'ARI13C1RJ,3C'2%;;#6R;#5RK,ACRL,3=R='0%6FRF#5RM,ACRN/0LROf3RP,3ARQ3:12IJ13DL'0?:OQ10JL'2'9'CXD3%M1%481ECK1>4CR8%4K1>4L[[%4CRJg00JJRDADCK1UW0%4L\D^0J1ECH%4H1>4I[\8ADCH1VDX0J%4I\D^0J1ECM%4M1>4N[\8ADCM1VDX0J%4N\D^0Jg00JfRJ#X%WJP3P31I3BP0%V3CHP11I3PCH%S3%R3RBP5P6P6P7P31<3<R61=39R91<3>R5'1'8RJ/151<3ARD1=3:'7R:'1g00KRRN1869R9/15/1:/85CG,FBP31<3CR5%BG5@3RG1=3E,75RE,75'8%B;9@35R;,7J'1%BF9@35/1;R5'11=3@,7DRD'1PN18GE179;'1/15/1D11E;'8CG,FBFO1NB7P2P0g00L9RBg00LYR7'P1Q20=JB7dAT341CUb8b?b@X13X23X33X43102>,2<R<13A1RA7:>10?A/2>'913C0RA,3C,2I13<L'0?:OQ12IA/0=?:OQ10AL'2'9'C^13^23^33^43P2f:f8f;f9#?O4b7b9b:b;b<b=b>bB%`1RA#?%_1E^1LPA1LP1/2>'913C2RC9K0AAK01210CL'2'9'CeXA3WCX53X63o"). Qed.

(* [comment removed for export] *)
Lemma need_lo : forall FC FB j cap, 0 <= FC -> 0 <= FB -> Z.of_nat j <= 10 -> 0 <= cap <= 2^26 ->
  1 + 4 * FC <= need_k FC j /\ (2^26 + 2^22) + 4 * FB <= need_b FB j cap.
Proof.
ltac2:(KReplay.run1 (kr_t_Room ()) [] "h02Hah14__p1h24__x1h34__x2h44__x3h54__x4h62FBh72FCh87__arithh94__ffh:6__sat3h;6__sat4h<6__sat5h=6__sat6h>6__sat7h?6__sat8h@8__varmaphA5__withB3caphC4cstrhD1jp;1p;2p;3p;4p;6p;7p;8g00@Ej1FTg0000j10Tg0013j17Tg000Uj13Tg00EGj25Tg002@j2GTg00?jj2:Tg00N6j1TTg001Xj2BTg00Dkj29Tg002]j3CTg00P[j2@Tg00N[j1ETg00QDj2]Tg00Qmj3[Tg00RVj3LTg00S?j2YTg00Skj2XTg003Aj1WTg00TWj3VTg003aj1UTg004Aj2JTg004_j1STg005=j4ITg005[j1RTg0069j1QTg00U7j6PTg006dj2=Tg008Mj2?Tg009[j1ATg00:9j3DTg00U[j1OTg007Gj38Tg007jj3NTg00;@j2iTg00;bj2gTg00<<j2fTg00<hj3eTg00=Bj3_Tg00=aj4^Tg00>Sj26Tg00?0j22Tg00?Mj2KTg00Agj2\Tg00Cjj3`Tg0090j4aTg00FFj7bTg00:\j7ZTg00Ecj3cTg00V=j8dTg00FjR0f0R1'5p=1%01#0p=h%01#0#0#0p=<g00GHR2f1R3g00VaP1Cap=;P3g00GfR4g00HER5P5g00HeR6P1g00IEFbp=>f2R7P4P5P5P6P3P1FZp=HAc231p=4f3R8P4P5P5P6P7P3P1Gdp=Mg00P<%18R9%F8g00IeR:#0R;#7R<#0#3R='5%3;R>%7:R?#0#7R@#0RA#3RB'GRC,58RD,:9f5RE#T%FE#1%7<#0R<#3RF,B>190>RG%1F1G>FRH,90[[%1>RIg00JJRJAC>F3UW0%1H\J^0I%7@R@#3RF,B>%1F1G>FRK,90[\GAC>F3VJX0I%1K\J^0I1B>B%1B190C[\GAC>B3VJX0I%1C\J^0Ip-0RIg00JfRJg00M9RB,@2RG%EB#ERB#E,@2%0;RF#0#h#<#<#<#<#3,]21@2B5[25L29L2Gg00WH'Y'X%WJ3V%UJP2P2f4RJ,J2P7%S2CIP31J28CI%R2%Q2RGPGP4P5P5P6f6R4EP1=2FRB1?2>RL%AA5D2RA';,>G5HG%O5R5PG1=2;R;1?2=RM';,>GP5%3:R5,?2RN%3FRF,?2RO1=2:582R:'4AN2M;RM/4N/4:';,>G%A<9D2LR<,4ARA1=2?982ORO'4%A@9D2LA82LB5N2A82M<'4/4A/4O';,>G5HGCMCM1iG6P1P7g00L9RGg00LYR6'g1f17=eG6dA_203C^b9b@bAX22X32X42X52W11:JD157=16F7R7,251K=8R=/25/27'512CHRC16FJR7'216>E,KK16=H'2/2C/27'5':[[^22^32^42^52^1IP1f<R1#1P1f>f=#Ff?f8f9O7b8b:b;b<b=b>b?bCf7R1,6F,251\1E'516F4,2CA`4EJ'5':eUUV9UXB2WDX62X72o"). Qed.

(* [comment removed for export] *)
Lemma fuzz_step : forall FC FB rem,
  fuzz_k FC rem = FC + fuzz_k FC (rem - 1) /\ fuzz_b FB rem = FB + fuzz_b FB (rem - 1).
Proof.
ltac2:(KReplay.run1 (kr_t_Room ()) [] "h04__x1h14__x2h24__x3h32FBh42FCh57__arithh64__ffh78__varmaph85__with93remp;1p;2p;4p;3p;7g003Aj1MTg003aj1LTg004Aj27Tg005=j4>Tg005[j1KTg0069j1HTg006dj24Tg0000j1ATg007Gj31Tg000Uj1?Tg008Mj2=Tg007jj3<Tg00Ecj39Tg0090j4;Tg0013j1JTg00:\j7GTg00;@j2FTg00;bj2ETg00<<j2CTg00<hj30Tg00=Bj3BTg00=aj4@Tg00>Sj22Tg00?Mj2DTg00?0j23Tg00?jj26Tg00X4j2:Tg00Y5j25Tg00FFj7ITf1R0g00GfR1g00HER2P2g00HeR3f0R4g00IEFIp=8g00GHR5g00JfR6#M%L6P5f2R6,75P0f3R7,75C>%K5%H5R8P1P2P2P3P5g00IeR2,45R1%A2,45R9515g00KRR:%?2R;,=59<51R<=1599959C;,88P5%J2,45R29151P:A15<29952C;,88FG1F83P4P6g00L9R8g00LYR3'E1C46=083dg00Fj=B50C@b6b7b8X05X15X2512401D4;R;/20,30505124612;6,36505'6^05^15^25P4P6P7P0O3b51:641:6;,365051504150;,30505'6eX95X35W4o"). Qed.

Lemma fuzz_nonneg : forall FC FB rem, 0 <= FC -> 0 <= FB -> 0 <= rem -> 0 <= fuzz_k FC rem /\ 0 <= fuzz_b FB rem.
Proof.
ltac2:(KReplay.run1 (kr_t_Room ()) [] "h02FBh12FCh23remp;2p;4g00EGj20Tg00>Sj22Tg00Z6j41Tg00Zaj43Tg00X4j26Tg00Y5j25Tg00?jj24Tg00GHR0g00FjR1f2R2'0R3f3R4f5R5'2,01f4R6,24,01P4P5f0R7P2C1P4P6P7f1C1C31654,011564,01'4eV3V3UX20X00W1o"). Qed.

Lemma fuzz_le4 : forall FC FB rem, 0 <= FC -> 0 <= FB -> 0 <= rem <= 4 ->
  fuzz_k FC rem <= 4 * FC /\ fuzz_b FB rem <= 4 * FB.
Proof.
ltac2:(KReplay.run1 (kr_t_Room ()) [] "h04__x1h17__arithh24__ffh34__p1h48__varmaph55__with62FBh72FCh82H1h92H2h:2H3h;3remp;2p;1p;4p;3p;6p;7p;5p;8g00EGj20Tg0000j18Tg000Uj1=Tg00?jj22Tg00>Sj21Tg003Aj1LTg003aj1>Tg004Aj2<Tg005[j1;Tg0069j1:Tg008Mj23Tg006dj29Tg0090j46Tg00U[j1MTg00;@j2KTg00;bj2JTg00<<j2DTg00<hj3?Tg00=Bj3@Tg00=aj4ATg00U7j6BTg00:\j7CTg00[<j55Tg00Zaj4ETg00X4j2FTg00Y5j2GTg00FFj7HTg00V=j8ITf1R0g00GfR1g00HER2P2g00HeR3f0R4g00IEFHp=7f3R5P1P2P2P3f2R6P0P4GIp=4g00GHR7g00FjR8/06R9g00IeR:#8#8#=R;,06,29f5R<,1511;<R='0f4R>,1511;>R?'0P5P;P<g00JfR@#LRA%>@R@1<70RB%;7RC%:7RDP71378g00VaRE197:R:C6,7DRF%M2RGPFC41KD3RFP4P6g00L9RHg00LYRI'J1D46=?HIdA@780CARIb2b4b5X07RH10841080[^07RJP4f6P5O2b1p-0RKPAP@PBPCPDPDP1P2P2P3PDP1P2P2P3P5EBP7P:PE137;C6,7DRDFCPGPDC4PFPIb2b4b5X07W3104;,20100;[^07^3KP4108>P>P0O3b1R0D5P5P;P>PHPJP4P<P6O2b1P0D5CE1F<5/0=1G>5/0?'2eW:X99W8X;7X67W7o"). Qed.

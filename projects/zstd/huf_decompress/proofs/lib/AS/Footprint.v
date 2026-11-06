(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Footprint () := "c59OSSVerify5KrLib2AS9Footprint7rg_disjC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9Footprint5rg_hiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9Footprint5rg_loC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01i59OSSVerify5KrLib2AS9Footprint6region00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00c59OSSVerify5KrLib2AS9Footprint6coversC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib2AS9Footprint5rg_wfC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07I47Corelib4Init5Logic4True00c59OSSVerify5KrLib2AS9Footprint7heap_rgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9Footprint;covers_monoC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record region : Type := Rg { rg_lo : Z; rg_hi : Z }.

Definition rg_wf (r : region) : Prop :=
  0 <= rg_lo r /\ rg_lo r <= rg_hi r /\ rg_hi r <= 2 ^ 64.

(* [comment removed for export] *)
Definition covers (r : region) (a : word) (n : nat) : Prop :=
  rg_lo r <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= rg_hi r.

Definition rg_disj (r1 r2 : region) : Prop :=
  rg_hi r1 <= rg_lo r2 \/ rg_hi r2 <= rg_lo r1.

Lemma rg_disj_sym : forall r1 r2, rg_disj r1 r2 -> rg_disj r2 r1.
Proof.
ltac2:(KReplay.run1 (kr_t_Footprint ()) [] "h01Hh12H0h22r1h32r2p;2p;1p;3g0000j23Tg000ij12Tg001`j11Tg002Wj20Tg0033j35Tg003Mj34Tg003gR0f1R1f0R2'3g004af2R3#2R4%11'0%21%13R1'0f3R5,33P2%25R3/01f4R1#1,03R3%21%15R5'0R1;52W0P2O11045A4312W0P2O1n200100000021000010000W1X30W2o"). Qed.

(* [comment removed for export] *)
Lemma covers_mono : forall r r' a n,
  covers r a n -> rg_lo r' <= rg_lo r -> rg_hi r <= rg_hi r' -> covers r' a n.
Proof.
ltac2:(KReplay.run1 (kr_t_Footprint ()) [] "h04__x1h14__x2h24__x3h37__arithh44__ffh58__varmaph65__with74__x4h84cstrh91Hh:2H1h;2H2h<2Hhh=2Hlh>1ah?1nh@1rhA2r'p;1p;3p;2p;4p;7p;8g005;j14Tg005`j1WTg006>j1HTg006aj3?Tg001`j12Tg007Yj26Tg002Wj20Tg008Cj19Tg008cj27Tg000ij11Tg009@j1ETg009ej1@Tg00:Dj2=Tg00:mj3ATg00;Vj2VTg00<Bj1UTg00<bj3RTg00=Bj1QTg00=bj2<Tg00>@j4;Tg00>^j1LTg00?<j1KTg00?gj2:Tg00@Jj1>Tg00@oj1GTg00AQj2FTg00B3j2ITg00BMj2JTg00C9j3DTg00CSj3MTg00D2j4NTg00Ddj1CTg00EBj3OTg00Eej4PTg00F@j4BTg00Fkj7STg00GOj8TTg00H3R0f1R1g00HQf0R2CBp=3P1g00I8R3g00IWR4P4g00J7R5P2g00JWFSp=5f3R6P3P4P4P5f2R3P1P2GTp=8g003gR7g00K7R8#4R9#4#4#4#4#4#WR:#Hg00K\A?612g00L;f4R;#2R<16:3R='0%91,7=%1;'0f5R=#2,0<f6R<#1%1='0A?<=;[[P2%2<16:;'016:=%9;'7f7R<#1'0%2<f8R>#2'0f9R?#1R@%1>'0%2?16:>R>'0%9<RA,7>/0@%E<R<g00LVR@/0ARAg00M4R>g00M`RB#@RC#@,=01=0C1=0B5A05A0g00N?'V%U>3RRB%Q>R>P01<03RCP11<06C;%L0RD%K0RE1:08RF%>8,:0R8'3,5E%G4R4PE1:09RG,38,5EP413FG,5EC8C81FE5R5P2P3g00NkRHg00OKRI'I1J23=DHIdAM0@1CNR@b4b5b6X00X10X2010231063RI1036[[^00^10^20P2f<RH#2f:,6:R:f;RJ#2P6P=O5b3b8P<PAPBP>P0PCP1P01<0;P6%C0C;C;PDPE%>9,:0R9/38,5EP4PEAO0FGRG/39,5EP413G8,5EC8C8P5P@b4b5b6X00X10X20X701713/0;1736/0;[\I^00^10^20^70P2%1H%1J%9?P:P3P;O6b3b8CPW<W=W;W:P1P2O2n2001000000121000000W9W?W>XA7W@o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma covers_nowrap : forall r a n,
  rg_wf r -> covers r a n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_Footprint ()) [] "h01Hh12H0h22Hah34__x1h44__x2h54__x3h63Hhih72_Hh83_H0h93_H1h:7__arithh;4__ffh<6__sat0h=6__sat1h>8__varmaph?5__with@1ahA4cstrhB1nhC1rp;1p;2p;3p;4p;7p;8g005;j17Tg005`j1_Tg006>j1QTg00Okj1GTg001`j13Tg000ij11Tg002Wj20Tg00Pbj1?Tg00Q@j2HTg00L;R0j2@Tg006aj3<Tg007Yj24Tg008Cj15Tg008cj22Tg009@j1VTg00Q]j2UTg00REj2CTg00Raj3TTg009ej1ATg00:Dj2;Tg00:mj3=Tg00;Vj2PTg00<Bj1OTg00<bj3NTg00=Bj1LTg00=bj2>Tg00>@j4KTg00>^j1ITg00?<j1JTg00?gj29Tg00EBj3FTg00@Jj1MTg00@oj1ETg00SEj2RTg00Shj3DTg00AQj2STg00B3j2^Tg00BMj2]Tg00C9j3\Tg00CSj3WTg00D2j4XTg00F@j4YTg00Fkj7ZTg00GOj8[Tg00LVR1f0R2'0p=6g00H3R3f1R4g00HQP2CYp=8P4g00I8R5g00IWR6P6g00J7R7P2g00JWFZp=:f3R8P5P6P6P7f2R5P4P2G[p=Bg003gg00K7R9#7R:#7#7#7#7#7R;#_R<#Qg00K\%G5P0%38R=#6%18R>,0=%?:R=%?;R;'HR?,0>'@f4R>?<8514<>%58'2/0?[P2f5#3#6f6R@#3%1@RA'010A?'@P0f7RA#3%1ARB'010B?f8RB?<A@14<B%5A'2/0?[P2f9RA#3%1A'0f:RB#1/0?f;R@?<BAP0f<R0#314<@RC'0%5B,2C%10'014<0%5@'2/0?P2f>R@#3f=R0,4<'014<@%50'2f?#1'0%V@%5@#61U=;1C1=%6;1C1?[[%6=R@g00TKR0AT=;4UW2%6?\0^2@g00M4R@g00M`R0#AR;#A,;31;3;1;305=35=3g00N?'P%O@3N%L@P31>35P41>38CK%I3%J3R@1939193:5F3R:%M9,93R9'8,:@%E6R6P@1R3==D3<R=,89,:@P618:=,:@CBCB1S@7P2P5g00NkR@g00OKR7'^1]25=\@7dAW314CXb;b>b?X33X43X531224/05108?1258/0?[[^33^43^53P2fD#1fB#5fC,4<P>PAO5b:b<b=bAW0W9P4P2O2n2001000000121000000W1W6W8P4P2O2n2001000000121000000W0W7P4P2O2n2001000000121000000W1WBW@WCo"). Qed.

(* [comment removed for export] *)
Lemma covers_disj : forall r1 r2 a1 n1 a2 n2,
  rg_disj r1 r2 -> covers r1 a1 n1 -> covers r2 a2 n2 ->
  bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
  \/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1.
Proof.
ltac2:(KReplay.run1 (kr_t_Footprint ()) [] "h02H0h14__x1h24__x2h34__x3h44__x4h54__x5h61Hh72H1h82H2h92H3h:2H4h;7__arithh<4__ffh=8__varmaph>5__with?4cstrh@5cstr0hA2a1hB2a2hC2n1hD2n2hE2r1hF2r2p;1p;2p;3p;4p;7p;8g005;j16Tg005`j1[Tg006>j1MTg0000j2HTg000ij14Tg001`j13Tg002Wj20Tg006aj37Tg007Yj21Tg008Cj12Tg008cj2=Tg004aR0j2?Tg009@j1DTg009ej1ATg00:Dj2<Tg00:mj3@Tg00;Vj2VTg00<Bj1UTg00<bj3RTg00=Bj1QTg00=bj2CTg00Ddj1LTg00>@j4>Tg00>^j1KTg00?<j1JTg00@Jj1BTg00?gj28Tg00@oj1ITg00EBj3GTg00AQj2NTg00B3j2FTg00BMj2OTg00C9j3PTg00CSj3ETg00D2j4STg003Mj3TTg0033j3ZTg00F@j4YTg00Fkj7XTg00GOj8WTf2R1f1R2'=f0R3'0p=5g00H3R4P2g00HQP3CYp=;P2g00I8R5g00IWR6P6g00J7R7P3g00JWFXp=:f3R8P5P6P6P7P1P2P3GWp=9g003gR5g00K7R9#6R:#6R;#6#6#6#6#[R<#MR=g00K\R>f5R?f4R@'HP0f6R0#4RA%3?'0%4?%30RB'0f7RC?7?@A7C@811<CRD%20'=RE11<?RF'0%2@=5FD'?[[P3%4C/0Bf8RB?70?RFg00L;RGf9RH#3/0DRI%4H,0ERJA7H0?11<HRK%2B;5D10EK'?[REP3f;RD#3/0KRKf:RL,1<RM%2H'=RNf<RO#4'0RPA7OHBRQPGf=RR#3/0MRM%4R,0NRN11<RRS%2O'=RT11<DRD'0%2L=5DS'?RDP3f?RS#311<O'0ROf@RL#4,0TRT11<LRU%2SRVf>RW,1<RX35RY%2R=5XURX%DSRSg00LVRU/0VRV%DWRZ%2W,0URWg00M4R[g00M`R\#AR]#AR^#A,<41<4^1<4]1<4\5@45@45@4g00N?'V%U[3RR\%Q[R[P4P41C4@P1%L4R]C>P2P41C4?P8P]C>C>R]%K4R^%J4R_%B:,84R`%B9,84Ra';,:_Rb%I6R6P_1849184:5G4R:184;R;';,:_R9P6P_1;;`,:_P61;:a,:_C9R:C9C91N_7R7P3P1g00NkRag00OKR;'F1O31=Pa;dAE4U2CSRUb<b=b>X14X24X34X44X5410@1A521@10?0A58@?[R0[[^14^24^34^44^54P3fDR1#3fER;#4fA,1<RafB#2fC,1<R<P@PBPRO8b;b@b?3TW:W9P2P3O2n2001000000121000000W0W8W7P2P3O2n2001000000121000000W0W6P3O1%3C,0APGPIPJPEP3PGPMPNPDP3PSPVPZPWP\P[P]P^P_P9P6P_PbP6P:C9C9P7PUb<b=b>X14X24X34X44X54A532810?8P0[[^14^24^34^44^54P3%3;%41P<%2LPaP8PHPRO8b;b@b?9ZYXX:TX9OP2P3O2n2001000000121000000X0QX8PX7KP2P3O2n2001000000121000000X0FW6P3O1n200100000021100011000W0XD>XB=WCWAXF5WEo"). Qed.

(* [comment removed for export] *)
Lemma covers_same_disj : forall r a1 n1 a2 n2,
  covers r a1 n1 -> covers r a2 n2 ->
  bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
  \/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1 ->
  bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
  \/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1.
Proof.
ltac2:(KReplay.run1 (kr_t_Footprint ()) [] "h01Hh12H0h22H1h32a1h42a2h52n1h62n2h71rp;1p;3p;2g005;j10Tg005`j18Tg006>j17Tg006aj31Tg007Yj25Tg008Cj14Tg008cj23Tg002Wj22Tg004aj26Tg003gg00K7#0#0#0#0#0#0#8R0#7R1g00K\R2f4R3f3R4f2R531f5R6f17151506R6%43'31504R4'2%45,34/26'6f0W2W1W0X62X41W5W3W7o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stack_rg (sp : word) (below above : Z) : region :=
  Rg (bv_unsigned sp - below) (bv_unsigned sp + above).

(* [comment removed for export] *)
Definition seg_rg (lo hi : Z) : region := Rg lo hi.

(* [comment removed for export] *)
Definition heap_rg (base : word) (cur : Z) : region :=
  Rg (bv_unsigned base) (bv_unsigned base + cur).

Lemma heap_rg_bump : forall base cur cur' a n,
  cur <= cur' -> covers (heap_rg base cur) a n -> covers (heap_rg base cur') a n.
Proof.
ltac2:(KReplay.run1 (kr_t_Footprint ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with54__x2h64__x3h71Hh83Hleh91ah:4baseh;3curh<4cur'h=1np;1p;2p;3p;4p;8p;7g005;j11Tg005`j1OTg006>j1@Tg002Wj20Tg00Tgj23Tg006aj3LTg00<Bj1FTg00=Bj1?Tg00=bj24Tg00>^j1=Tg00?<j1<Tg00?gj22Tg00AQj2NTg00B3j2MTg00BMj2KTg00C9j3HTg00CSj3GTg00D2j4ETg007Yj2ATg001`j18Tg00>@j4BTg00@Jj1CTg00@oj1DTg00EBj39Tg00GOj8>Tg008cj27Tg000ij1:Tg00U`j7ITg00F@j4JTg00Fkj7;Tg00H3R0f1R1g00HQf0R2CJp=5P1g00I8R3g00IWR4P4g00J7R5P2g00JWF;p=6g00K7R6#1R7#1#1#1#1#1#OR8#@R9g00K\f3R:f2R;'0f5R<f4R='3?L;1f6R>/3<R?13>=R=P:P;P2g00M4R@#FRA%?@R@1401%=0RB%<0RC1206RD/5D'61NC5REP2P;g00NkRFg00OKRG'M1K2;=HFGdg00LV=G01CERGb2b3b4X001022^00P2f7,A8R8O1b1%8=%8?'0ePAP@P0140;P1140:CBPBPCP3P4P4P51207R7%C6,20R6'5,6C%D4A90D7A90D6'5,6CG>PEPGb2b3b4X00X50X60101;171;171:'0[^00^50^60P2P<P>P8P;O4b1%:?%:='0eFIW7W8W=X99X<0X;0W:o"). Qed.

(* [comment removed for export] *)
Definition layout_wf (rs : list region) : Prop :=
  Forall rg_wf rs /\
  forall i j, (i < j)%nat -> (j < length rs)%nat ->
              rg_disj (nth i rs (Rg 0 0)) (nth j rs (Rg 0 0)).

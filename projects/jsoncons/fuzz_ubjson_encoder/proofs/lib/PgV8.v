(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core
     PmLayout PmModel PmStatics PmSpecs PmParSpecs PmTxtSpecs PgSrc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PgV8 () := "C46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z2lec89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4PgV84PGV87v8_roomC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulK47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init5Logic3and01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic2ex01k89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4PgV84PGV82v802C13~~~I47Corelib4Init5Logic2ex00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01i89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4PgV84PGV82v800C13~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01k89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4PgV84PGV82v801C13~~~K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4PgV84PGV88v8_clearC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4PgV84PGV86v8_capC13~~~C47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init5Logic5False00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4PgV84PGV85v8_okC13~~~C47Corelib4Init5Logic3iffK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init5Logic6eq_indC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface?hl_k_per_mallocC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface=hl_b_overheadC13~~~C56Stdlib6ZArith6BinInt1Z2geK47Corelib4Init9Datatypes4prod01c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4PgV84PGV86pot_v8C13~~~K46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init9Datatypes3sndI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface;heap_layout00C13~~~K46Stdlib9micromega=RingMicromega3Op204C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z7pow_1_rC56Stdlib6ZArith6BinInt1Z9pow_add_rK47Corelib7Numbers7BinNums1N01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op206".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGV8.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive v8 : Type := V8Null | V8Blk (b n c : Z).
Definition v8_size (x : v8) : Z := match x with V8Null => 0 | V8Blk _ n _ => n end.
Definition v8_cap (x : v8) : Z := match x with V8Null => 0 | V8Blk _ _ c => c end.
Definition v8_data (x : v8) : Z := match x with V8Null => 0 | V8Blk b _ _ => b end.
Definition v8_own (x : v8) : list (Z * Z) := match x with V8Null => [] | V8Blk b _ c => [(b, c)] end.
(* [comment removed for export] *)
Definition v8_clear (x : v8) : v8 := match x with V8Null => V8Null | V8Blk b _ c => V8Blk b 0 c end.

Section Model.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable acc : (word -> option byte) -> Z -> Z -> Prop.
Variable ann : (word -> option byte) -> Z -> Z -> Z -> Prop.
(* [comment removed for export] *)
Definition v8_at (M : word -> option byte) (v : Z) (x : v8) : Prop :=
  L5.defined M v 24 /\ acc M v 24 /\
  match x with
  | V8Null => L5.u64_at segs M v 0 /\ L5.u64_at segs M (v + 8) 0 /\ L5.u64_at segs M (v + 16) 0
  | V8Blk b n c => L5.u64_at segs M v b /\ L5.u64_at segs M (v + 8) (b + n) /\ L5.u64_at segs M (v + 16) (b + c)
                   /\ 0 <= n <= c /\ 1 <= c <= 2 ^ 27 /\ 4096 <= b /\ b mod 16 = 0
                   /\ L5.defined M b c /\ acc M b n /\ ann M b n c
  end.
End Model.

(* [comment removed for export] *)
Definition v8_ok (x : v8) (g : Z) : Prop :=
  match x with V8Null => g = 0 | V8Blk _ _ c => 1 <= g <= 28 /\ 2 ^ (g - 1) <= c end.
(* [comment removed for export] *)
Definition pot_v8 (L : heap_layout) (x : v8) (g : Z) : credit :=
  (hl_k_per_malloc L * (28 - g), (2 ^ 28 - 2 * v8_cap x) + (28 - g) * hl_b_overhead L).
(* [comment removed for export] *)
Definition v8_grow_ok (x : v8) (n : Z) : Prop := n <= v8_cap x \/ (v8_cap x <= 2 ^ 26 /\ n <= 2 ^ 27).

(* [comment removed for export] *)
Definition v8_room (x : v8) (u : Z) : Prop :=
  match x with
  | V8Null => True
  | V8Blk _ _ c => exists a0 j, 0 <= j /\ c = a0 * 2 ^ j /\ 1 <= a0 <= 2 ^ 14 /\ a0 + u <= 2 ^ 26
  end.
Lemma v8_room_mono x u u' : u' <= u -> v8_room x u -> v8_room x u'.
Proof.
ltac2:(KReplay.run1 (kr_t_PgV8 ()) [] "p'0h01jh16__sat6h24__x1h32a0h41Hh52Hah67__arithh74__ffh87__sat10h96__sat5h:6__sat7h;6__sat8h<6__sat9h=8__varmaph>5__with?4__p1h@4__x2hA4__x3hB1ahC1uhD2u'hE1xi001xhF2H0hG2H1hH2H2hI2H3hJ2H4hK2HuhL1bi011bhM1ci021chN1ni031ni041vp;2p;1p;3p;4p;6p;7p;8p-1R0p10000p4p710p8P0p1000Gp4p710p8P0p1000hR1p4p710p8P0P1p4p7210p8g001Ej20Tg001aj2>Tg002mj1@Tg003Rj1DTg0040j24Tg004Mj2ATg004jj1JTg005OR1j22Tg005jj2?Tg006Gj2KTg006oj2<Tg007Kj3LTg007oj1dTg008Oj1cTg008oj2ITg009Mj1bTg009kj1aTg00:Vj2GTg00;9j2HTg00;\j1`Tg00<>j2_Tg00<`j2^Tg00=:j2]Tg00=fj3CTg00>@j3\Tg00>_j4[Tg00?Qj1ZTg00?oj2YTg00@Pj1XTg00@oj2MTg00AXj3nTg00BAj3ETg00Bjj2WTg00CVj3VTg00D6j4mTg00DTj3lTg00E7j4UTg00Ebj6jTg00FFj1RTg00Fdj3NTg00GGj4BTg00Gbj3QTg00HEj4PTg00H_j3OTg00IhR0j2gTg00JBj7fTg00Jfj8eTg00KJj7kTg00KnR2f0R3'0p=5f3R4f2R5f1R6'?/03'2p=3g00LLR7?C56/23,24p=61g73p=11A639C75p=810451063'2p=7f4R81063,25,24'2p=FAC756/23p=T1?56/03p==P7P6g00LjP3CUp=;P6g00MQR9g00N0R:P:g00NPR;P3g00O0Ffp=9P4P9P:P:P;P5P6P3Gep=:P5P9P:P:P;P6P3Fkp=S1056/23p=i1063,25p=hg00OPR<P<10651>641>54[[P51036R=g00PYR>g00Q5WFW4g00QQ/>5R?P?[\=ef6R=f7R?'0R@%53RAP4g00RZRB#@RC#DRD/43RE,A6RF%DBRG/06RH%JBRI#J#@RJ#DRK,4DRL,06RM'2RNP6f:RO%@I#J#@RP#DRQ,4DRRC3C6X07#1X37#1P0P7PAP8PFPNP6f;RSPRC3RTC6X07#1X37PAf5RUPFPTC6X07#1X37#1P3PAP=PFPNP6f=R=PRC3C6X07#1P0P7PAA8?5EPGP5P5PLC7f>R0,?5PRDFX07PAf9RTPFPNP6f?RVPRC3C6X07#1X37#1P3PAA8T8EPGP8P8PLC7f@RW,?8PRDFP1%56RX14D6,AUPGPUPUPLC7PUfARYPRC35TOPAP=PFPNP6fCROPRC3C6X07#1X37#1P3%54f8RZ14D8'APGPZPZPLC7PZfDR[PRC35T=P114DU980TPGPTPTPLC7PTfER0PRC3PAPYPFPNP6fGRUPRC3C6X07#1X37#1P314D?98WSPGf<RSPSPLC7PSfHRSPRC3P1PGP=P=PLC7fIR1===RPAP0PFPNP6fKPRC3C6X07#1X37#1P3PGPVPVPLC7fLRV==WRP7PAPSPFPNP6fNRNPRC3C6X07#1X37PYP7PAfBRF=8UEPGPFPFPLC7fMRU,?FPRDFX07P=%5=fF14D=78YRE10GYRS10YLR?'2R\A=YVRRV'2R]'21KDKR^1<2DR_%5K1<2L[[R`%5DRaALDK6V>W5RK%5L\>^5aRb1KDQRc%5Q1<2R[\_RdALDQ6V>X5aRQ%5R\>^5aRe1KDYRf%5F14DO,<2[\_ROALD[6V>X5aRF14D[R[#5\>^5aRaP5P3PWO2XB_RW1<2[^B_R_g00S?R[#dR>%c[Rg1I76Rh%b7Ri%a7Rj1G721H7BRk';,9jRl%`:RmPlC:1_j;RlP3P5g00SkRng00TKRo'^1]35=CnodA\726C[R2b7b=b>X27PX\A^27P3P0PYO2b6b1b9b1b:b;b<b8PEP]P^P`PKPbPcPdPQPePfPOPFPaPWP_%ZB,Y7g00TkRB#XR],M7RE5n71M7BRB5E7g00UJRY'W=V[>PgP71I75P61I74CmRAPiPjP7Pkg00V61H7CRC1H7IRI5l7CU,9jRXPmPXC:PlP2b7b=b>X27X@7XA7A8365A8654[^27^@7^A7P314D0P1PNP=O4b6b1b9b1b:b;b<b8P\PVPSP?P^P`PKPbPcPdPQPePfPOPFPaPWP_p-0R?P>PgPhPiPj1G7G/;k,9jRSPjP9P:P:P;P4EjR;5SjPmPSC:PlP2b7b=b>X27W?AiG36PH[^27^??P3101LP1PTO3b6b1b9b1b:b;b<b8P^P`PKPbPcPdPQPePfPOPFPaPWP_P>PgPhPiPj1G7DRD%RJ5N7,;k,9jRJ9Sj;PmPJC:PlP2b7b=b>X27X??Ah63LPM[^27^??P310G1P1PTO3b6b1b9b1b:b;b<b8CBP^P`PKPbPcPdPQPePfPOPFPaPWP_%X],M7AE7EB5E7/WY=V[>PgPAPiPjAQ7kI%RP9N7DRD';,9jPmPj1;CI,9jPmAQ7kC/;D,9jC:C:PlP2b7b=b>X27X@7XA7A=35R1054A=54R[[^27^@7^A7P3fUfTP1PZPUO5b6b1b9b1b:b;b<b8CBCBCBCPCPWJWIP6P3O2n2001000000121000000W4WHP6P3O2n2001000000121000000W4WGP6P3O2n2001000000121000000W4X07P6P3O2n2001000000121100000W4X37P6P3O2n2001000000121100000W4WKAO456/>ZAO845/>Z[\@eXM7XN7XL7P5P6P3O3n0110400020031101103102XD7XC7XE<P5P6P3O3XD7XC7WEo"). Qed.
Lemma v8_room_clear x u : v8_room x u -> v8_room (v8_clear x) u.
Proof.
ltac2:(KReplay.run1 (kr_t_PgV8 ()) [] "p'0h01Hh11uh21xh32a0h41bi001bh51ci011ch61jh71ni021ni031vp;2p;1p;3g001aj20Tg00V]j16Tg001Ej23Tg002mj12Tg003Rj14Tg0040j27Tg004Mj2<Tg00=fj3;Tg004jj15Tg005Oj21Tg005jj2:Tg00Ihj28Tg00H_j39Tg00OPR0g00LLR1P0f0R2f1R3'0%63f2R4'0[P3g00PYg00Q5W0g00QQR5/02%65/03[eg00Kn/32g00RZR5#2#4R6/72,<39;14%45/33%55R5#5#2#4,76,33'1f8,:3%25#5#2#4,76'3'1'1'1X61,81X31,81P2W0A9432f6'0f3?943#6f7'0[eX51X71X41P4P3P2O3n0110300020030100102101X11X20P3P2O2W1W2o"). Qed.
Lemma v8_room_cap x x' u : v8_cap x' = v8_cap x -> x' <> V8Null -> x <> V8Null -> v8_room x u -> v8_room x' u.
Proof.
ltac2:(KReplay.run1 (kr_t_PgV8 ()) [] "p'0h02N1h11Eh21Hh32N2h42a0h51jh62H0h72H1h81bi001bh91ci011ch:2c0h;1ni021nh<1uh=1xh>2x'h?2b0h@2n0i031vp;1p;2p;3p;7g00Wjj17Tg001aj21Tg00=fj38Tg00Y5j1@Tg00<`j2DTg00H_j32Tg001Ej26Tg002mj1:Tg003Rj19Tg0040j2=Tg004Mj2ATg004jj1>Tg005Oj25Tg005jj2<Tg00YNj2?Tg00Ymj7CTg00Ihj2BTg00LLR0f1R1f0R238p=0g00OPR3g00QQR4782#@p=3f2R51512'5p=;1B02p=4P3%75%72R6'0f3R7#3%35f4R8,17f6R9f5R:'1[[[[P5P3%74R;,06%31R<A8344R=#@R>1148R?118:[[[[P1g00KnR@=80@g00PYRA1D34RBP=P7P2O1b6g00ZKRCPBP=P8P2O1b7PCg00Q5X7CP2O1b7X6CP2O1b6W2X3>X0>W110;;1147P?[\>\>[eA802@A2751R?#3RC16@2R=g00RZRD#:#9RE/=2,A1RF,09%9D/61%>DRD#>#:#9,=E,61'5RGf<,<1%:D#>#:#9,=ERE'6'53;X50#4X40#4P1PBO1'?X2AX3>W0W1A2512#7RD/0;f9RH,14A29:8RIf:RJ'1RK[\>\C[eX90X;0X80P5P1P2O3n0110300020030100102101P3%7?,06A2:87R6#3f;R?,18\K[\<[f7R<A80@2A2875#3R@10:F1<1?/6E,5G5;=X50#4X40#4P5PBO1,?AW2W3X0>W110;D116H114J[\@\>[e1029f8R>92JH#3R@10?FfA,<1/6E,5G5;=X50#4X40#4P0PJA2<92#3107FfD,<1/6E,5G5;=X50#4X40#4]0X:0A29:J#3P1W0P8P7P5FCW2W3X0CW1A2><9#7,0DA2?JHf?'1f@,1I[\@\C[eX:0X@0X?0P5P1P2O3n0110300020031100102101X90X;0X80P5P1P2O3n0110300020131100102101X<0X>3X=3P5P1P2O3X<0X>3X=3o"). Qed.

Lemma v8_ok_cap x g : v8_ok x g -> 0 <= g <= 28 /\ (g = 0 <-> x = V8Null).
Proof.
ltac2:(KReplay.run1 (kr_t_PgV8 ()) [] "p'0h01Hh12Hah24__x1h37__arithh44__ffh58__varmaph65__with71gh84__p1h94__p2h:6__sat3h;6__sat4h<1xh=2H0h>2H1h?2H2h@1bi001bhA1ci011chB1ehC1ni021ni031vp;2p;1p;3p;4p;6p;7p;8g00Zhj2BTg004jj1GTg002mj1?Tg003Rj1DTg001Ej20Tg005OR0j21Tg00\2j25Tg00=fj3:Tg007oj1KTg008Oj1JTg00\Kj1\Tg009Mj1VTg009kj1UTg00:Vj2ATg00<>j2STg00<`j2@Tg00=:j2RTg00>@j3QTg00>_j4PTg00GGj4=Tg00Ymj6MTg00\ij24Tg0040j28Tg00H_j36Tg006Gj2FTg006oj2>Tg007Kj3ETg008oj2LTg00;9j2NTg00;\j1OTg00E7j4HTg00]Fj6TTg00YNj2[Tg00JBj7ZTg00KJj7YTg00Jfj8WTg00Ebj6XTg00KnR1f0R2'0p=2g00LLR3?:21p=3g00OPR4g00QQR57:2p=7P3f1R6g00LjP2CHp=;P6g00MQR7g00N0R8P8g00NPR9P2g00O0FZp=9f2R:P7P8P8P9P6P2FYp=<f3R;P7P8P8P9P:P6P2GWp=CP6P7P8P8P9P2EXp=IP41B26%2:g00RZR7#G#G#?#?#DR<,0:'1%3:%76'5'1[P6%32R=P3P1%22102<R>'1A:455R?,5='1X731011%2<'1R@A:311RA/5?g00S?RB#KRC%JBRB%\3%V3RD%U3RE1A31RF/;F,9E1A3<RG,;F,9E3<1SE9R9P2P:g00SkRHg00TKRI'@1R2:=:HIdAQ316CPRIb4b5b6P@P2b3P?\APA\?1@45X0A1@31X0?C=C=P6P2EMW01B52%26106<'1RA%36/5?'1[e%D7R?f6R@'010@<'1%?7#DRH14@?'8/02'1P0f7R0,0?100<RJ'1140?,8H/06f8RK#210K<'1%3Kf4RL?6;:#7'5'1P2f9RM,0?10M<'1f:RN/4?,8H/0Lf;RO#210O<'1%3ORPf5RQ960@#7RR'514O?,FH1>1HRSf<RT/4?RU#2f=RV/4?RW,8H,>1[[%2HRXg00PYRYf>RZ/4?R[=EH6UW118H[R[#2\Y^1XPCPB1L36R\PDPE1A3?1N37R7';,9ER]1;7G,9ERG5<E%O8R81;F7,9E=<EGCCP9PIb4b5b6X2310?2/1>PA[^23P2PZPLO2b3b:b;A6K0@RK#7\P%3T\R1FHU%2W1>1[[\Sf?RS/4?R[=EH6VYX1X18H[#2\Y^1Xp-0RXPCPBP\PDPEP3P7g00V6PFCH,9EP8PE1IE;9<E]P81IELCCCCP9PIb4b5b6X23X8XW910?6/1:PL[\=^23^8X^9XP2A6ONM#710S<PSP;PQO5b3b:b;VPP4PKP4PXP2g00ZKRXPYn0110300020030100102101XB4g00Q5P5P2ETPX%3V/[2b=X0RC=C=W?W>P6P2O2n2001000000121000000W0A6:62/B@%20/1J%30A6;:6#7'5'1[eXA3XC3X@3P:P6P2O3n0110300020031100102101X73X<4P6P2O2X73X<4o"). Qed.

Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

Abbreviation iss_at := (PM.iss_at segs A PMSP.T3).
Abbreviation nullis_at := (PM.nullis_at segs A PMSP.T3).
Abbreviation src_fields_at := (PM.src_fields_at segs PMSP.T3).
Abbreviation v8_atP := (v8_at segs PMSP.T3 PMSP.T4).
Abbreviation entry := (PMSP.entry A L).
Abbreviation pm_scr := PMSP.pm_scr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vu8_grow_spec (pc : Z) (is_append : bool) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (v a sp r g : Z) (x : v8),
    hi_heap HI (v8_own x ++ LB) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 1 ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 a -> sp <= v -> v + 24 <= hl_sptop L -> v mod 8 = 0 ->
    v8_atP M v x -> v8_ok x g ->
    (* [comment removed for export] *)
    (if is_append then 1 <= a /\ v8_size x + a < 2 ^ 64 else 0 <= a < 2 ^ 64) ->
    v8_grow_ok x (if is_append then v8_size x + a else a) ->
    PMSP.credit_le (pot_v8 L x g) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : v8) (g' : Z) (cr' : credit),
        regs_preserved R R' -> v8_atP M' v x' -> v8_size x' = (if is_append then v8_size x + a else a) -> v8_ok x' g' ->
        v8_cap x <= v8_cap x' ->
        (v8_size x' <= v8_cap x -> v8_own x' = v8_own x /\ v8_cap x' = v8_cap x /\ g' = g) ->
        (v8_cap x' = v8_cap x \/ v8_cap x' = Z.max (2 * v8_cap x) (if is_append then v8_size x + a else a)) ->   (* [comment removed for export] *)
        L5C.hpres L LB sp (pm_scr 1) [(v, 24)] M M' ->
        PMSP.credit_keep cr cr' (pot_v8 L x g) (pot_v8 L x' g') ->
        model_but_vm model model' -> hi_heap HI (v8_own x' ++ LB) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.
Definition vu8_resize_spec (pc : Z) : Prop := vu8_grow_spec pc false.
Definition vu8_append_spec (pc : Z) : Prop := vu8_grow_spec pc true.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record vowner : Type := VOWN {
  vw_at  : (word -> option byte) -> PM.srcst -> v8 -> Z -> list (Z * Z) -> Prop;
  vw_os  : Z; vw_ois : Z; vw_ov : Z; vw_lo : Z; vw_hi : Z
}.
Record vowner_ok (V : vowner) : Prop := {
  vo_src : forall M src x g OB, vw_at V M src x g OB ->
             src_fields_at M (vw_os V) (vw_ois V) (vw_ois V + 16) src /\ nullis_at M (vw_os V + 8) /\ L5.defined M (vw_os V) 296
             /\ v8_atP M (vw_ov V) x /\ v8_ok x g;
  vo_lay : vw_lo V <= vw_os V /\ vw_os V + 296 <= vw_hi V /\ vw_lo V <= vw_ois V /\ vw_ois V + 272 <= vw_hi V
           /\ vw_lo V <= vw_ov V /\ vw_ov V + 24 <= vw_hi V /\ vw_hi V <= hl_sptop L /\ vw_hi V <= 2 ^ 47
           /\ vw_os V mod 8 = 0 /\ vw_ois V mod 8 = 0 /\ vw_ov V mod 8 = 0 /\ 4096 <= vw_lo V
           /\ (vw_os V + 296 <= vw_ois V \/ vw_ois V + 272 <= vw_os V)
           /\ (vw_ov V + 24 <= vw_os V \/ vw_os V + 296 <= vw_ov V) /\ (vw_ov V + 24 <= vw_ois V \/ vw_ois V + 272 <= vw_ov V);
  (* [comment removed for export] *)
  vo_upd : forall (LBX : list (Z * Z)) (sp scr : Z) (Wx : list L5.range) (M M' : word -> option byte) (src src' : PM.srcst)
             (x x' : v8) (g g' : Z) (OB : list (Z * Z)) (cr : credit) (VM : VmMaps),
             sp <= vw_lo V -> vw_at V M src x g OB ->
             hi_heap HI (PM.src_own src ++ v8_own x ++ OB ++ LBX) cr M VM ->
             (* [comment removed for export] *)
             Forall (fun b => fst b + snd b <= vw_lo V \/ vw_hi V <= fst b) (PM.src_own src ++ v8_own x ++ OB) ->
             (forall b, In b OB -> (fst b + snd b <= PM.sr_qc src \/ PM.sr_qc src + PM.CHUNK <= fst b)
                                   /\ (forall B' m', In (B', m') (v8_own x) -> fst b + snd b <= B' \/ B' + m' <= fst b)) ->
             (* [comment removed for export] *)
             Forall (fun r => (fst r + snd r <= vw_lo V \/ vw_hi V <= fst r) /\ (forall B m, In (B, m) OB -> fst r + snd r <= B \/ B + m <= fst r)) Wx ->
             L5C.hpres L (OB ++ LBX) sp scr (PGS.W_srcfG (vw_os V) (vw_ois V) ++ [(vw_ov V, 24)] ++ Wx) M M' ->
             src_fields_at M' (vw_os V) (vw_ois V) (vw_ois V + 16) src' -> PM.sr_qc src' = PM.sr_qc src ->
             v8_atP M' (vw_ov V) x' -> v8_ok x' g' ->
             vw_at V M' src' x' g' OB
}.
(* [comment removed for export] *)
Definition src_of_vw (V : vowner) (x : v8) (g : Z) : PGS.owner :=
  {| PGS.ow_at := fun M src OB' => exists OB, OB' = v8_own x ++ OB /\ vw_at V M src x g OB;
     PGS.ow_os := vw_os V; PGS.ow_ois := vw_ois V; PGS.ow_lo := vw_lo V; PGS.ow_hi := vw_hi V;
     PGS.ow_win := fun M src OB' p k => 0 <= k /\ exists b n c, x = V8Blk b n c /\ b <= p /\ p + k <= b + c |}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition read_span_v_specG (pc : Z) : Prop :=
  forall (V : vowner), vowner_ok V ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (OB LBX : list (Z * Z)) (cr : credit) (sp r len : Z) (src : PM.srcst) (x : v8) (g : Z) (str : PM.vstr) (sm : PM.strm),
    hi_heap HI (PM.src_own src ++ v8_own x ++ OB ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 6 ->
    sp <= vw_lo V ->
    getr R 10%bv = Z_to_bv 64 (vw_os V) -> getr R 11%bv = Z_to_bv 64 len -> getr R 12%bv = Z_to_bv 64 (vw_ov V) -> 0 <= len < 2 ^ 64 ->
    vw_at V M src x g OB -> iss_at M (vw_ois V) str sm -> PMST.base_ok segs A M ->
    incl (PM.vs_own str) LBX -> PM.unread src sm < 2 ^ 26 -> v8_room x (PM.unread src sm) ->
    PMSP.credit_le (pot_v8 L x g) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (x' : v8) (g' : Z)
            (sm' : PM.strm) (cr' : credit) (ptr n : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
        PMSP.consumed src src' sm sm' = n ->
        ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PM.src_own src' ++ v8_own x' ++ OB) ptr n) ->
        L5.defined M' ptr n ->
        (n = len -> v8_room x' (PM.unread src' sm')) ->
        vw_at V M' src' x' g' OB -> iss_at M' (vw_ois V) str sm' ->
        PMSP.src_step src src' sm sm' ->
        L5C.hpres L LBX sp (pm_scr 6) (PGS.W_srcfG (vw_os V) (vw_ois V) ++ [(vw_ov V, 24)]) M M' ->
        PMSP.credit_keep cr cr' (pot_v8 L x g) (pot_v8 L x' g') ->
        model_but_vm model model' -> hi_heap HI (PM.src_own src' ++ v8_own x' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
Definition srd_read_v_specG (pc : Z) : Prop :=
  forall (V : vowner), vowner_ok V ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (OB LBX : list (Z * Z)) (cr : credit) (sp r len : Z) (src : PM.srcst) (x : v8) (g : Z) (str : PM.vstr) (sm : PM.strm),
    hi_heap HI (PM.src_own src ++ v8_own x ++ OB ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 5 ->
    sp <= vw_lo V ->
    getr R 10%bv = Z_to_bv 64 (vw_os V) -> getr R 11%bv = Z_to_bv 64 (vw_ov V) -> getr R 12%bv = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 ->
    vw_at V M src x g OB -> iss_at M (vw_ois V) str sm -> PMST.base_ok segs A M ->
    incl (PM.vs_own str) LBX -> PM.unread src sm < 2 ^ 26 -> v8_size x = 0 -> v8_room x (PM.unread src sm) ->
    PMSP.credit_le (pot_v8 L x g) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (x' : v8) (g' : Z)
            (sm' : PM.strm) (cr' : credit) (d : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
        PMSP.consumed src src' sm sm' = d -> v8_size x' = d ->
        (d = len -> v8_room x' (PM.unread src' sm')) ->
        vw_at V M' src' x' g' OB -> iss_at M' (vw_ois V) str sm' ->
        PMSP.src_step src src' sm sm' ->
        L5C.hpres L LBX sp (pm_scr 5) (PGS.W_srcfG (vw_os V) (vw_ois V) ++ [(vw_ov V, 24)]) M M' ->
        PMSP.credit_keep cr cr' (pot_v8 L x g) (pot_v8 L x' g') ->
        model_but_vm model model' -> hi_heap HI (PM.src_own src' ++ v8_own x' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

End Specs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pot_v8_grow L x g c' :
  0 <= hl_k_per_malloc L -> v8_ok x g -> 2 * v8_cap x <= c' ->
  forall b' n', v8_ok (V8Blk b' n' c') (g + 1) ->
  fst (pot_v8 L x g) - hl_k_per_malloc L = fst (pot_v8 L (V8Blk b' n' c') (g + 1))
  /\ snd (pot_v8 L x g) - (c' + hl_b_overhead L) >= snd (pot_v8 L (V8Blk b' n' c') (g + 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PgV8 ()) [] "h04__x1h14__x2h22Hah31Lh47__arithh54__ffh68__varmaph75__with84__x3h94__x4h:2c'h;1gh<1xh=2Hch>1Kh?2OKh@3OK'hA6__sat0hB6__sat1hC2b'hD2n'p;1p;2p;3p;4p;8p;7g00]bj1@Tg001Ej25Tg00Zhj2ETg002mj17Tg003Rj1DTg00Wjj1;Tg004Mj21Tg00H_j3HTg005jj22Tg004jj1FTg00\ij20Tg00=fj36Tg0040j2MTg00_6j1LTg00`Hj2:Tg007oj1aTg008Oj1\Tg008oj2BTg00\Kj1ZTg00D6j4ATg009Mj1YTg009kj1XTg00;9j29Tg00:Vj2?Tg00Gbj3=Tg00E7j4>Tg00<>j2WTg00<`j2VTg00=:j2QTg00>@j3PTg00>_j4OTg006Gj2NTg006oj2GTg007Kj3RTg00;\j1STg00FFj1TTg00Fdj3UTg00Jfj8cTg00GGj4bTg00`dj4KTg005Oj2JTg00aDj3ITg00bOj3`Tg00DTj3_Tg00JBj7[Tg000hj3]Tg00c2j3^Tg00LLR0f1R1f0R23`p=4A_012p=3P1g00MQR3g00N0R4P4g00NPR5P2g00O0F[p=CA]002p=<A^002p=8g00cOR6g00OPR7g00KnR8f3R9#@'5f2R:,E9g00RZR;#7R<#DR=f4R>#;'1/5:f59H12f6R?%D;R@'2'Ef9RA#@RB%F;RC#F#7#7RD#DREf7RF'0RG'1RH/0B12F@RI,0ERJ,1BRK5601M=ERLf8RM#;,1='0%LARN,1G'2RG12?NRO'011=?,0L11JNRN'2':g00S?RJ#aRP%\JRJP01B0:P1%Z0RQCA%Y0RR%X0RSP0190;R;1?0ERT190<RU'4RV'3/4;g00V61?0@9=0U,4TRT,3;C>'C1WS5RUP2P:g00SkRWg00TKRX'V1Q2:=6WXdAP081CORXb5b6b7X00X1010E1,12/02121@,0E,12560^00^10P2PMf:RW#@O2b41N=E1G8=158E1G8L[[158=RYg00PYRZAR=E1UW2158L\Z^2YPPPJP0P01B0>P:PQCAP11B09CAPRPSP3P4P4P5P01?0=R5/3;R;g00Lj%7<,90R<C>,CS%S4P0%TD9U05RD/4;190CRC,3V5=0A=0<C'4g00da135<,4D13TC5=0C>,CSGcPUPXb5b6b7X00X10X80X9011=2/5911=1,0L10E:/19'212>9'011=>,0L12:@,0E/19'2':[^00^10^80^90P2PAf<#LPWf;#;P?O5b4bAbBCbP0P0PHPGCKRG#</0BP0P0PKAH:1?R?#;,1=,0L/2NCKRN#<560%8G/0O%8N':'JeAIAMFRM#</0BAIA?IR?#<560%8M/0O%8?':'JeW@XD0XC0W=W?W>X:0X;0X<7X36P9P:P1P2O4X:0X;0W<W3o"). Qed.

(* [comment removed for export] *)
Lemma v8_ok_grow x g b' n' c' :
  v8_ok x g -> 2 * v8_cap x <= c' -> 1 <= c' <= 2 ^ 27 -> v8_ok (V8Blk b' n' c') (g + 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PgV8 ()) [] "p'0h04__x1h12Hah27__arithh34__ffh44__p1h56__sat3h66__sat4h78__varmaph85__with96__sat5h:6__sat6h;2H2h<2OKh=4__x2h>4__x3h?4__x4h@1HhA1gi001ghB1zhC4__p2hD4__p3hE2b'hF2c'hG2n'hH1xhI2H0hJ2HchK2HghL2HphM1bi011bhN1ci021chO1ni031nhP1si041si051li061vp%0p;2p;1p;3p;4p;6p;5p;7p;8g00Zhj2;Tg002mj1ETg003Rj1HTg00Wjj1GTg004jj1LTg0040j22Tg00H_j3ATg005jj24Tg001Ej20Tg00\ij21Tg006Gj2>Tg007Kj3<Tg007oj1pTg008Oj1nTg00\Kj1gTg009Mj1fTg009kj1eTg00:Vj2BTg00Gbj3PTg00<>j2bTg00<`j2aTg00=:j2`Tg00=fj3OTg00>@j3_Tg00>_j4^Tg008oj2NTg00;9j2FTg00;\j1]Tg00Fdj3WTg00GGj4VTg005OR0j2@Tg00Ymj6UTg00bOj3\Tg00E7j4KTg004Mj2RTg00eHj2tTg00eoj2MTg00fKR1j2sTg00fkj5rTg00gRj2qTg00@Pj1ITg00@oj2DTg00h;j3STg00BAj3CTg00Bjj2[Tg00CVj3ZTg00D6j4YTg00FFj1mTg00DTj3QTg00YNj2lTg00hdj1hTg00iEj5iTg00]Fj6jTg006oj2kTg00JBj7XTg00KJj7oTg00Ebj6dTg00Jfj8cTf2R2f1R3'Rf0R4'0p=8f3R5/021034'@p=71023/@4p=?1034,@2p=:g00KnR6/k4p=91064p=5P2g00MQR7g00N0R8P8g00NPR9g00LLR:P3g00LjP4CKg00O0R;FXp=3P2P7P8P8P9P3P4Fop==P3P7P8P8P9P4Edp=JP5P7P8P8P9P2P3P4Gcp=6P3P7P8P8P9P4P;FXp=Tg00OPR;f4R7/;5g00RZR<#ER=#HR>f5R?#G;83%H<R@P2P2%L<RA#E#L#LRB#HRC,2>RDC7P;f7RE,;4%G3=8>?f8RFf6RG7AEf9RH/4@';];]<PEg00QQRI/;G%GI=8>7P:P6144@RI%LA#E#E#HRJ,0IRK5?@11I@RL,2>;:GXA:P@146@RMPMPJC7RN11M@RM,2>RO/0?RP1>>CRQ%9>RR%5C%9D[[RS%5>RTg00PYRUA<>C3UW1RV%5D\U^1TRWg00S?RX#pRY%nXRZ%g:R[%f:R\%e:R]1B:@R^1B:6R_=P:^R`53]1B:JRa93]`3=1b]9R9P4P2g00SkR`g00TKRb'a1`42=O`bdA_:63C^Rbb3b7b8PNP4b2b5b61>>M%5M%9O[\RA<>M3VUX1T%5O\U^1TPQPSPVPWp-0ROPYPZ1N:3RMP\P]1F:<R<93]^R`1J]55=]S00%]8R81B:>Rcg00ih5W:=3]<C6P9Pbb3b7b8X0:W4A?@43Rd12>6/03[^0:^4OP4f:R6/0DP6PEO3b2b5b6b9b:CV1@NPePFP3EUAAEG?14F@';eW;W<AA234f<RP';AA523#G=8>6P0P@f>R0P0PJC7110@,2>/02P@f?RN/4@RePePJC711e@,2>;:PP3P@f@RePePJC7fARf/1@,2>/0?PQPSPVPWfDRg/1@Rh,>>fERi/1@Rj#5fFRk/1@Rl,2>Rm#9[\RfGRn/1@Ro=<>3VUX1T12>oRo#5\U^1TPYPZPMP\P:A\:<^Rp=P:^g00V6AP:<^Rq=\:^CK,T]P9Pbb3b7b8X0:114@/4@=O:L^0:P4PnO1b2b5b6b9b:fBRn/1@/4@14n@Rn/1@RL5O:P:fCRr/1@Rs/4@Rt14g@Rg10gJRu5?@Rv12>4;:fXB:P:12>sRw12>@S01'RA:v4fXB:P:P>12>h/R4=:vfXB:14r@Rr10rJRv5?@A8w>e1trJ1MrJ,svP1Pu1MgJ14i@Rg10gJRu5?@P4PQPSPVPWfHR1/1@Rv,>>RwfIRf/1@Rh#5fJ/1@Rx,2>#9[\RRyfKRz/1@R{=<>3VUX1TR|12>{R{#5\U^1TR}PYPZPMP\P]A3]qaR~P8P]Q00P8A3]^q==]~C6C6P9Pbb3b7b8X0:X4OA?@32P@142@R~P~PJC7[\K^0:^4OP410zJPzP?P6O4b2b5b6b9b:X@uP4O11MgJP@14k@RgPgPJC7P>PCPlPQPSPVPWPwPyP|P}PYPZP[P\P:P_g00jFPcCK,T]P9Pbb3b7b8PRP4b2b5b6b9b:PQPSPVPWPwPyP|P}PYPZPMP\P]P:Pqg00jmPaCK,T]P81B:C=3]pC6P9Pbb3b7b8X0:1MIJ113@RI,0C[^0:P4PzP?O2b2b5b6b9b:Dr10DmPQPSPVPW1>>h%5x%9{[\RfLR{/1@Rx=<>3VUX1T12>xRx#5\U^1T1q:>Rhg00TkRm#IRz#IRC#IRa#I,D:5S:1D:aRa1D:CRC1D:z9S:h5C:5C:5C:g00UJRz'[=ZXYPZP:P:1N:7P2P[CYP31N:5CYRqP\P]%mB9W:cRB1F:=R}53]P8P]1J]GR|%E=,F:R==3]B5=]P8P]1F:ARA9Q:c=3]=P8P]A3]}AP8P]1J]E9=]`P81J]FC6C6C6C6C6P9Pbb3b7b8X0:X=:X>:X?:X4OXCOXDO10D3A:?7DA8>7?107?10@7RD/@Hf;RH[[[[[^0:^=:^>:^?:^4O^CO^DOP4g00ZK10{J10@fPfPePxP{P?PkP0P6PHO<b2b5b6b9b:bI'lW@P4O1n200110400021110511100bPPQPSPVPW1>>jRj%5l%9o[\RRRA<>v3VUX1TRo12>vRv#5\U^1TRTAS:hC1D:m5C:9C:a/[z=ZXYPZPqP\P]AQ:c==3]}P8P]A3]<=P8P]A3]^A==]|P8AQ:<c=3]}C6C6C6P9Pbb3b7b8X0:X=:X>:X?:X4OA8>5310371@DGA85>7[[[^0:^=:^>:^?:^4OP4101JRDPPP1PiPvP6PGPEO8b2b5b6b9b:CVQ01%h>EU12>tP>PsP@PQPSPVPWPjPRPoPTPYPZPMP\P]Q00P8A3]_pC6P9Pbb3b7b8X0:X4O%5I\d^0:^4OP4PDP1PEO3b2b5b6b9b:PQPSPVPWPjPRPoPTPYPZP[P\A3]_^P9Pbb3b7b8%5@P4b2b5b6b9b:DiEU11r@P4Ejb@P@PnPnPJC712>L;:NeWLWKP3P4O2n2001000000121000000f=?APH140@';eW;W<XN:XO:XM:P2P3P4O3n0110600020131101103102P2P3O2WJW;W<XF:XG:XE:XA:XH;P7P5P2P3P4O5XF:XG:XE:XA:WHo"). Qed.

End PGV8.

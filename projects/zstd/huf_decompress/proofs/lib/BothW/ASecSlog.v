(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (1 recorded proof replaced by written proofs (slog_ok_sound)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import ABase AModelFacts APrimFacts F_acache3 ASecFacts.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASecSlog () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Classes9Morphisms:forall_defK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib5BothW:APrimFacts=forallb_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib5BothW8ASecSlog7slog_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properC59OSSVerify5KrLib5BothW9F_acache36cb_clzC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init5Logic3iffI47Corelib4Init5Logic3and00C47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib5BothW9F_acache35cb_smC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyK47Corelib7Numbers7BinNums1Z01C47Corelib7Program6Basics4implK47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00C47Corelib7Classes?RelationClasses=iff_ReflexiveC59OSSVerify5KrLib5BothW:APrimFacts@range_by_computeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ASecSlog=slog_ok_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ASecSlog;slog_ok_allC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega6VarMap1t01c59OSSVerify5KrLib5BothW8ASecSlog:slog_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition slog_ok (j : Z) : bool :=
  let y := cb_sm (4096 * j) in let k := cb_clz y in (34 <=? k) && (k <=? 47) && (0 <=? y) && (y <? 18446744073709551616).
Lemma slog_ok_all : forallb_range slog_ok 18 (Z.to_nat (131077 - 18 + 1)) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ASecSlog ()) ["CANSEC1"] "p;2p;1p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?p4p710p9g001fj29Tg002@j12Tg002ej11Tg003Jj13Tg003hj28Tg004Ej27Tg004bj14Tg005Bj35Tg006Ej36Tf0#1#1p=0g006_R0g007?R1'9g007_g008ZR2#0R3#2#1#3R4%03#0#0#0#0#0#2#1#2#3/84%32'7#435=601do"). Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Opaque cb_sm cb_clz.
Local Strategy expand [slog_ok].
Lemma slog_ok_sound : forall z, slog_ok z = true -> 0 <= cb_sm (4096 * z) < 2^64 /\ 34 <= cb_clz (cb_sm (4096 * z)) <= 47.
Proof.
  intros z Hz. unfold slog_ok in Hz. cbv zeta in Hz.
  rewrite !Bool.andb_true_iff in Hz. destruct Hz as [[[H1 H2] H3] H4].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
  change (2^64) with 18446744073709551616. repeat split; assumption.
Qed.

Lemma slog_range : forall z, 18 <= z <= 131077 ->
  0 <= cb_sm (4096 * z) < 2^64 /\ 34 <= cb_clz (cb_sm (4096 * z)) <= 47.
Proof.
ltac2:(KReplay.run1 (kr_t_ASecSlog ()) ["CANSEC1"] "h01jp;1p;2p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?p4p710p9g002ej10Tg003Jj12Tg00Dfj26Tg00ECj1;Tg00B6j25Tg00BRj2:Tg00Boj27Tg00=Aj24Tg002@j11Tg00:Uj18Tg00IZj69Tf0R0#0#0p=3g00HLg00G0g008Z#0R1#0R2#0R3#0#3R4#3#3#3R5#2/60#;R0'5%21%24':,70'4%13#0#2%80R0'5%11#1#1#1#2,50'4'4W0g007_%12#0#2%35#1#0#1#2g00J`g00KaE9o"). Qed.

Lemma slog_facts : forall ms, 73728 <= ms <= 536891392 -> ms mod 4096 = 0 ->
  0 <= cb_sm ms < 2^64 /\ 34 <= cb_clz (cb_sm ms) <= 47.
Proof.
ltac2:(KReplay.run1 (kr_t_ASecSlog ()) ["CANSEC1"] "h04__x1h14__x2h21Hh32H0h42H1h52H2h62H3h77__arithh84__ffh98__varmaph:5__with;4__x3h<2msh=1qh>1rh?1Eh@1MhA1Rp;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?p4p710p9g002ej10Tg002@j13Tg003Jj15Tg00B6j21Tg00=Aj22Tg00L`j28Tg00M@j2MTg00Maj1YTg00N:j2=Tg00Dfj2<Tg004Ej2JTg00NWj2QTg00Boj2:Tg00O>j2OTg00Oej2STg00PKj2NTg00Q1j1]Tg00QOj2\Tg00R0j1GTg00ROj2CTg00S8j3FTg00Saj2BTg00TMj1[Tg00Tmj3ATg00UMj1ZTg00Umj2LTg00VKj4KTg00Vij1XTg00WGj1WTg00X2j2;Tg00XUj6VTg00Y9j1UTg00Y[j2ETg00Z>j3TTg00Zaj3oTg00[Dj2nTg001fj2mTg00[fj2lTg006Ej3HTg00\Rj3hTg00]1j4gTg00ECj1fTg00BRj2eTg00:Uj1dTg00]cj2cTg00^Lj3bTg00_5j1aTg00_Sj2`Tg00`Qj6_Tg00`oj3^Tg00aXj4RTg00bCj7iTg00bgj8jTg00cKj7kTf0R0#0#0#0#0p=9%00#0p=Ig00HLR1g00G0R27H0p=@f1R3=H10p=6A^130p=7P1P3g00coP0CRp=>P3g00dVR4g00e5R5P5g00eUR6P0g00GlFip=4f3R7P4P5P5P6f2R8P3P0Gjp=?P1P3g00f5P0CRp=DP8P4P5P5P6P3P0Fkp=Pg008ZR9#0R:#0R;#3#0R<#9#9#9#5R=/10%0;R;#0#IR>#I#9R?#I#3#0#3R@#9#9#9#5RA,10'2%5?R?,83#@1M8?%@?RB#YRC1=7?RD,<?RE187?'J,67[1Q7?1:2?RFf4RG/8?RH,121:H?'2[1OG?1:?2RIf5RJ/8?RK,:?11K2'2[1SJ?f6RL/=?#@\B1NL?f7RM/8?/6M\B1=M?RNP1f8RO/8?RPP1g00f\RQ%]9,\1RRg00gHRS#GRT#GRU,C1RV5F11C1TRT9F1R1C1SRS'7'7g00ggRW'B17TS,7V/BW%[QRX5AQ3A%ZQRYP11L18RZP31L17CK%X1R[%W1R\P\P\P4P5P5P61;1?R41;12R]'>,4\EV%U5R51E19R^1E1:R_9T14R`%39,E1R95o1'>,4\C?P5P\1>9],4\P51>^`,4\C?C?1n\6R6P0P8g006_R`g007?R9'm1l08=H`9dAh123CgR9b8b9b:X01X11X;1g00hS\B1<?8/J7,63[%@71<?7,68[[^01^11^;1P0P3P8f:R`PMPOO5b7b>b=b6b5b4b3b21=8?,<?,68P1PE%f0RE,12%5:%5>'e,:E'2%3;#0#5%dERE'1%3:#3#3#3#5,1E'2'2X<11M7?1=G?,<?/JH,6G\C1QG?112K1:K?'2\F1OJ?18L?RJ,:?11J2'2\I1SL?%@N\B1NM?16PO\B1=O?P1f9/8?P1%GU,C1RU1c1?=b1SRS,7V'7/BWAF1RU17TS'7/BW=AQX5AQPYP1PZP3%a1CKP[P\AT14^,>_,4\P5P\1;1=/D_,4\1;1A,D_,4\5P\P5%5<R<,;1/D^,4\%5@R@,;1,D^,4\5P\C?C?P6P9b8b9b:X01X111<?0,6311=8118A'211<8118@'2[[^01^11P0f;P8POP`O4b7b>b=b6b5b4b3b2,`DP7P0E_b?W@WAX<1o"). Qed.
End CANSEC1.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Bytes.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_A3.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ASlot_W16 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr06K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op203C45stdpp9bitvector;definitions7bv_wrapK47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega6VarMap1t03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;round_up_pgC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9ASlot_W16?land_4095_rangeC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mm_usage1 (st1 : mstate) (sc usage0 : Z) : Z :=
  if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0.

Definition mm_cnt_red (sc size cnt usage1 : Z) (nosmall : bool) : Z :=
  if (usage1 <? 4 * cnt) && negb nosmall then
    if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
    else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
    else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
    else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
    else cnt
  else cnt.

Definition mm_small (size req usage1 cnt needed : Z) : Z * Z :=
  let req := round_up_pg (req + IB + UNIT) in
  if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed).

Definition mm_final (size req usage1 cnt : Z) (nosmall : bool) : Z * Z :=
  let needed := round_up_pg (size * cnt + UNIT) in
  if negb nosmall && (cnt <=? 7) then mm_small size req usage1 cnt needed else (cnt, needed).

(* [comment removed for export] *)
Lemma land_4095_wrap x : 0 <= x -> x + 16 <= 2^64 ->
  Z.land (18446744073709551600 - x) 4095 = Z.land (- (x + 16)) 4095.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W16 ()) ["CEIL_WRAP_1"] "h02Hah11zh27__arithh34__ffh46__sat2h56__sat3h68__varmaph75__with86__sat4h96__sat5h:4__x1h;1xh<1Hh=2H0h>2H1h?6__sat6h@6__sat7p;1p;2p;3p;4p;6p;7g0000j10Tg000Uj16Tg0013j23Tg001Pj2>Tg001mj2HTg002Ij11Tg002nj2;Tg003Kj24Tg003kj19Tg004Hj1JTg004fj2CTg005Dj2@Tg005lj2:Tg006Hj3?Tg006lj1YTg007Lj1XTg007lj2WTg008Jj1VTg008hj1QTg009Sj2PTg00:6j28Tg00:Yj3FTg00;<j2OTg00;_j1DTg00<=j3ETg00<`j3NTg00=Cj3MTg00=fj4<Tg00>Qj2LTg00?3j2GTg00?Mj2KTg00@9j3BTg00@Sj3STg00A2j4TTg00Adj2UTg00BAj1^Tg00B_j6]Tg00CCj4\Tg00Cdj6ATg00DBj6[Tg00D^j3ITg00EAj7ZTg00EeR0f0R1'Hp=2%11#1p=R%11#1#1#1#1#1#1#1p=5g00FCR2f1R3;B1p=7P3g00FaR4g00G@R5P5g00G`R6P1g00H@FZp==%21g00H`R7#0R8#0#0#0R9#6R:,33%68R8%09#0#6R9'>R;'HP2%17R<#R#5#5#5#5#5#5#5#0#0#0#0#6R=f2R>';R?%0<R<#0R@#6RA,>8RB'4f3RC/3:#9RD%JARE'C,71X12P213>:#9RF/4B1;=CRC/4B/71X12%1<#0#0R<#6RG,@81:08RH%2G1>8GRI,:0[[%28RJg00IERKA?8G3UW0%2I\K^0J1@8ARG%2ARL1:0B[\HRMA?8A3VKX0JRN%2B\K^0JRO1@89RP%291:0;[\HRHA?893VKX0JR9%2;\K^0JRJg00IaRK#YR;%XKRK1W23%V2RQ%Q2RRP21P27R7182:5F2,O21828R8%D<5E2%D@9E28R85N25F2g00JMR@182==M27C<'=1LR6R7P1P>g00K4R<g00KTRS'G1K1>=B<SdAS203CTR3b3b6b7X:2131:#91UIBRS'31;=1'7^:2P1f9O1b2b4b5b8b9b?b@13FS/7?P213DSRS141Bf4/3:#9/4BR:'7X12P214DBR=171:X121G2=14SBPDPIPBPGPMPNPOPPPHP9PJP;PK%^2ROPQPRP4P5P5P6P2P8P@1820R@C<,=RE]P7P3b3b6b7AB2B0g00L4[P1b2b4b5b8b9C\EAPCP1E[b<1CFEPPPHP9PJP;PKPOPQP2P@g00LQ182AC<,=RP7P3b3b6b7PLP1b2b4b5RL9IFAEA1C?EAI?ALEAW>W=X;2P1O1X;2o"). Qed.

Lemma land_4095_wrap20 x : 0 <= x -> x + 20 <= 2^64 ->
  Z.land (18446744073709551596 - x) 4095 = Z.land (- (x + 20)) 4095.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W16 ()) ["CEIL_WRAP_1"] "h02Hah11zh27__arithh34__ffh46__sat2h56__sat3h68__varmaph75__with86__sat4h96__sat5h:4__x1h;1xh<1Hh=2H0h>2H1h?6__sat6h@6__sat7p;1p;2p;3p;4p;6p;7g0000j10Tg002Ij11Tg000Uj16Tg0013j23Tg001Pj2?Tg001mj2HTg002nj2;Tg003Kj25Tg003kj19Tg004Hj1JTg004fj2CTg005Dj2@Tg005lj2:Tg006Hj3>Tg006lj1YTg007Lj1XTg007lj2WTg008Jj1VTg008hj1RTg009Sj2QTg00:6j28Tg00:Yj3GTg00;<j2OTg00;_j1DTg00<=j3ETg00<`j3NTg00=Cj3MTg00=fj4<Tg00>Qj2LTg00?3j2FTg00?Mj2KTg00@9j3BTg00@Sj3STg00A2j4TTg00Adj2UTg00BAj1^Tg00B_j6]Tg00CCj4\Tg00Cdj6ATg00DBj6[Tg00D^j3ITg00EAj7ZTg00EeR0f0R1'Hp=2%11#1#1#1#1#1#1#1p=4%11#1p=Pg00FCR2f1R3;B1p=7P3g00FaR4g00G@R5P5g00G`R6P1g00H@FZp==%21g00H`R7#0R8#1#0#0#6R9,33%68R:%08#0#0#0#0#6R8'?R;'HP2%17R<#1#4#4#4#4#4#4#4#0#P#0#0#6R=f2R>';R?%0<R<#0R@#6RA,?:RB'5f3RC/39#9RD%JARE'C,71X12P213>9#9RF/5B1;=CRC/5B/71X12%1<#0#0R<#6RG,@:1:0:RH%2G1?:GRI,:0[[%2:RJg00IERKA>:G3UW0%2I\K^0J1@:ARG%2ARL1:0B[\HRMA>:A3VKX0JRN%2B\K^0JRO1@:8RP%281:0;[\HRHA>:83VKX0JR8%2;\K^0JRJg00IaRK#YR;%XKRK1W23%V2RQ%R2RRP21Q27R718295G2,O2182:R:%D<5E2%D@9E2:R:5N25G2g00JMR@182==M27C<'=1LR6R7P1P>g00K4R<g00KTRS'F1K1>=B<SdAS203CTR3b3b6b7X:21319#91UIBRS'31;=1'7^:2P1f9O1b2b4b5b8b9b?b@13FS/7?P213DSRS151Bf4/39#9/5BR9'7X12P215DBR=1719X121F2=15SBPDPIPBPGPMPNPOPPPHP8PJP;PK%^2ROPQPRP4P5P5P6P2P:P@1820R@C<,=RE]P7P3b3b6b7AB2B0g00L4[P1b2b4b5b8b9C\EAPCP1E[b<1CFEPPPHP8PJP;PKPOPQP2P@g00LQ182AC<,=RP7P3b3b6b7PLP1b2b4b5RL9IFAEA1C?EAI?ALEAW>W=X;2P1O1X;2o"). Qed.

Lemma land_4095_word z : Z.land (bv_unsigned (Z_to_bv 64 z)) 4095 = Z.land z 4095.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W16 ()) ["CEIL_WRAP_1"] "h01zh17__arithh24__ffh38__varmaph45__witp;1p;2p;3p;4p;7p;6g0000j10Tg00;_j1PTg00M8j2CTg002Ij16Tg000Uj15Tg004fj22Tg00@9j31Tg001Pj29Tg00Adj2<Tg003Kj24Tg004Hj1=Tg00?3j28Tg00M^j4OTg00N8j4NTg006lj1MTg007Lj1LTg00BAj1KTg008Jj1JTg008hj1ITg00:6j2:Tg00=fj4HTg00EAj7BTg00>Qj2DTg00?Mj2ETg00@Sj3ATg00A2j4FTg001mj2GTg00D^j3;Tg00Cdj67Tg00N^j2@Tg00ODj2?Tg00Onj2>Tf0R0#6#6p=3g00FCR1P1g00H`R2#0R3#0#0#0#0#0#PR4/C0R5%62R2#3#3#3#3#3#5R6,20R7f1R8/26511X01P1%53R3%02R2#6#0#0#5'9R9%02#5R2,93R3'<R:,40R;/43%=2R<,289110X01P11403148:/43=110X01P0P:P3P11<03911:X01P9181:COCN120<g00IaR:#M%L:%K1%J1%I1R:g00Fag00G@R9P9g00G`R9P1g00EeR3,:1g00LQ1:12CHg00H@FB1D:9P0f2R9g00K4R:g00KTR='81E09=1:=dAA138CFb2b3b41G32P0b1R39;02E712;<A;;23E71256=117e1@40,?41>40E7X01P0O1W0o"). Qed.

Lemma land3_range x : 0 <= Z.land x 3 <= 3.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W16 ()) ["CEIL_WRAP_1"] "h07__arithh14__ffh28__varmaph35__with42Hah56__sat0h66__sat1h74__x1h81xh91Hh:6__sat2h;1zp;1p;2p;3p;4p;8p;6p;7g0000j1XTg000Uj1:Tg001Pj2BTg003Kj28Tg002Ij1MTg001mj25Tg00P]j22Tg005Dj2@Tg005lj23Tg006Hj3>Tg006lj1<Tg007Lj1;Tg00BAj1WTg008Jj1UTg008hj1TTg00:6j27Tg00;_j1LTg00<=j3KTg00=fj46Tg00>Qj2CTg00?3j2ATg00?Mj2DTg00@9j3ETg00@Sj3FTg00A2j4GTg00Q8j3HTg00Q_j2?Tg007lj2ITg009Sj2JTg00RPj1=Tg00S2j8NTg004Hj1OTg004fj2PTg00D^j3QTg00Cdj6RTg00EAj7STg00SVj7VTg00EeR0f0R1'5p=0f1R2g00FaR3g00G@R4P4g00G`R5P1g00H@FSp=1g00FCR6P2g00LQP1C6p=4f2R7P3P4P4P5P2P1FVp=9P6g00H`R8#XR9#:R:/B:R;,81R<%01R=%M8#:R>,51'2X;61@::R?130:%0:R@130;RA[[RBg00IERCA>::2UX4@RD%0;RE\C^4@RCg00IaRF#<RG%;FRF%W6RH%U6RI%T6RJP61760RKg00T:RL176:RM%L95K6R9C6'11CJ5RNP1P7g00K4ROg00KTRP'A1D17=EOPdAF602CGR0b1b2b3PAP1b0b5b69H1;%0<13<;'2P?PBPDPCf3RC/?;%0Cf5/8;RC#0\E[PGPF1I62PIPJP3P4P4P51J68R8,4K,1JR5P6P8PLP9C6,1J59J%=4176>,48,1J99J5GNPNP0b1b2b3X76131;,2=%02152>'2[^76P1PCf4O2b0b5b6b:b9%O:,P1PGPFPHPI14KM,1JPNP0b1b2b3P@P1b09Q1:ERX86P1O1X86o"). Qed.

Lemma land_4095_range y : 0 <= Z.land y 4095 < 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W16 ()) ["CEIL_WRAP_1"] "h07__arithh14__ffh28__varmaph35__with41yh51zp;1p;2p;4p;3p;6p;7g0000j11Tg000Uj12Tg002Ij1>Tg001Pj2LTg003Kj2JTg001mj26Tg005lj24Tg00P]j2<Tg006lj1;Tg007Lj18Tg00BAj19Tg008Jj1:Tg008hj1KTg00:6j23Tg00=fj47Tg00>Qj2ITg00?3j2BTg00?Mj2?Tg00@9j3@Tg00@Sj3ATg00A2j4=Tg00Q8j3CTg004Hj1DTg004fj2ETg00D^j3FTg00Cdj6GTg00EAj7HTf0R0#1#1p=0f1R1g00Fag00G@R2P2g00G`R2P0g00H@FHp=5g00FCR3P3g00H`R4#1R5#2%>4#0#2R4'L,J0g00EeR6/60%15#0#0#0#0#0#2R5,40'<X53g00IaR7#;R8%87R7%93R9%:3R:%K3R;P31336R<g00T:1335C7'51I;2R2P0f2R=g00K4R>g00KTR?'B1?0==@>?dAA361C=R1b1b2b31465P0b09C05%D4,E0P8P7P9P:P3P<g00LQ1334C7,5;P2P1b1b2b31664P0b09F04EGX43P0O1W4o"). Qed.

Lemma round_up_pg_alt x : Z.land (- x) 4095 + x = round_up_pg x.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W16 ()) ["CEIL_WRAP_1"] "h04__x1h14__x2h21xh37__arithh44__ffh58__varmaph65__witp;1p;2p;4p;3p;7g006lj1HTg007Lj1GTg007lj2>Tg00BAj1;Tg00Taj4FTg008Jj1BTg008hj1?Tg009Sj26Tg0000j1<Tg00:Yj34Tg00=fj4:Tg00EAj78Tg00>Qj29Tg00?3j2ETg00?Mj2CTg00@9j31Tg00@Sj3ATg00A2j4@Tg0013j22Tg003kj15Tg002Ij13Tg000Uj1=Tg004fj27Tg00U?j1DTf0R0#3#3p=0g00FCR1g00IaR2#H%G2P1f2R2,>1f1R3%;1CF%B1%?1R4g00Fag00G@R5P5g00G`R5P1g00H`R6,61R7%<6,61R8541g00JMA4187C:g00H@F81945P0P2g00K4R5g00KTR4'E1C02=154dg00Ee=A13C@b4b5b6X01X1112031230511^01^11P0P3%53%36#0#0#0#0#0#=R6'7O2b3%50/76/20%D0511eX21P0O1W2o"). Qed.

Lemma round_up_pg_range x : 0 <= x -> x <= round_up_pg x < x + 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W16 ()) ["CEIL_WRAP_1"] "h04__x1h14__x2h21xh32H0h47__arithh54__ffh68__varmaph75__witp;2p;1p;4p;3p;8p;7g001mj21Tg003kj1@Tg00VTj1JTg002Ij18Tg000Uj1?Tg004fj2=Tg0000j14Tg005lj27Tg00P]j25Tg006lj1BTg007Lj1ATg007lj2STg00BAj1RTg00Taj4QTg008Jj1NTg008hj1MTg00:6j2:Tg009Sj29Tg00=fj46Tg00RPj1ITg00:Yj3;Tg00S2j8FTg00>Qj2GTg00?3j2HTg00?Mj2ETg00@9j3KTg00@Sj3LTg00A2j4DTg0013j2>Tg00U?j1CTg00EAj7OTg00SVj7PTf0R0#8#8p=2%40#4p=0f1R1g00FaR2g00G@R3P3g00G`R4P0g00H@FOp=3f2R5P2P3P3P4P1P0FPp=<g00FCR6g00EeR7/10%@1R8#Jg00H`R9#8#2#2#2#2#2#?R:,=8R8,17%49R;#4#0#0#0#0#0#?R<,78'5g00IaR8#B%A8P61S65P1%R6CQ%N6%M6R8P2P3P3P4P61:67g00LQR2196;R;C6,38P6P;g00T:R=1:6<R>C6,385<8%I3P61969R9P2A;69;R;C6,38P6P;P=A;69>C6,385<8GF1G84P0P5g00K4R8g00KTR4'H1E05=K84dAL671CDb5b6b7X06X161171171<'51>15R5,111>1<R<,75'5[^06^16P0f3R5#@/=:P5P1O3b4b3%C1R5,11175<'5eUX26P0O1W2o"). Qed.
End CEIL_WRAP_1.


(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac bool_hyp b K := destruct b; cbn in K; first [reflexivity | discriminate | congruence | (exfalso; apply K; reflexivity)].
Section CEIL_WRAP_2.
Context {RUNp : RunP}.


Section MMC.
Variables (sc size req : Z) (nos : bool).
Hypothesis SC : 0 <= sc < 48.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis RQ : 0 <= req < 2^32.

Definition mmc_post (ra sp gp tp t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (res : Z * Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t4' a0' a1' a2' a3' a4' a5' a6' t5' : word),
    ms' = MS (mkR ra sp gp tp t0' (wz size) t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4' t5' t6)
             F (Z_to_bv 64 0x1675c) fc None m (seg_rom asegs)
    /\ a1' = wz (snd res) /\ a6' = wz (fst res).
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End MMC.
End CEIL_WRAP_2.


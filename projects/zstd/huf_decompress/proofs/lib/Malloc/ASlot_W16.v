(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W16 () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr06K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op203C45stdpp9bitvector;definitions7bv_wrapK47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega6VarMap1t03C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W16?land_4095_rangeC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
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
ltac2:(KReplay.run1 (kr_t_ASlot_W16 ()) ["CANSEC1"] "h01zh17__arithh24__ffh38__varmaph45__with54__x1h61xh71Hh82H0h92H1p;2p;1p;3p;4p;6p;7g0000j2@Tg000Lj10Tg0011j15Tg001Oj22Tg001lj2?Tg002Ij11Tg002nj29Tg003Kj23Tg003kj18Tg004Hj1GTg004fj2;Tg005Dj1XTg005dj1WTg006Dj2VTg006bj1UTg007@j1TTg007kj2QTg008Nj27Tg0091j3DTg009Tj2MTg00:7j1CTg00:Uj3BTg00;8j3LTg00;[j3KTg00<>j4:Tg00<ij2JTg00=Kj2ATg00=ej2ITg00>Qj3=Tg00>kj3HTg00?Jj4NTg00@<j2OTg00@Yj1PTg00A7j6FTg00A[j4STg00B<j6>Tg00BZj6ZTg00C6j3ETg00CYj7YTf0R0#1#1p=R%10#1#1#1#1#1#1#1p=4g00D=R1f1R2;=0p=6P2g00D[R3g00E:R4P4g00EZR5P0g00F:FYp=<g00FZR6/@0g00G8R7#0R8#0#0#0R9#5R:,22%58R8%09#0#5'?'@P1%17R9#R#4#4#4#4#4#4#4#0#0#0#0#5R;f2R<'9R=%09R9#0R>#5R?,?8R@'3f3RA/2:#8RB%G?RC';,60X01P112<:#8RD/3@19;ARE/3@/60X01g00G]RF#XRG%WFRF1V12%U1RH%T1RIP11Q17R7171:5D1,M11718RJ%19#0#0R9#C5B1%C>9B1JRJ5L15D1g00HIR>171;=K17C:'<1JI5R7P0P<g00I0RKg00IPRL'A1I0<==KLdAH162CNR2b2b3b4X51120:#8%59,?8R8/O@R9'219;0'6^51P0PAO1b112D9/6=P112B9R9130@f4/2:#8/3@R:'6X01P113B@RA160:X011A1A139@PBP8P@PGPF%P1R8PHPIP3P4P4P5P1PJP>1716R>C:,<IEFP7P2b2b3b4A=1@6g00J0[P0b1CSE>PEP0EZb71;DCPGPFP8PHP1P>g00JM171?C:,<IP7P2b2b3b41@6?P0b1R69ED?E>1;=CAE=?6E>W9W8X61P0O1X61o"). Qed.

Lemma land_4095_wrap20 x : 0 <= x -> x + 20 <= 2^64 ->
  Z.land (18446744073709551596 - x) 4095 = Z.land (- (x + 20)) 4095.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W16 ()) ["CANSEC1"] "h01zh17__arithh24__ffh38__varmaph45__with54__x1h61xh71Hh82H0h92H1p;2p;1p;3p;4p;6p;7g0000j2@Tg000Lj10Tg002Ij11Tg0011j15Tg001Oj22Tg001lj2>Tg002nj29Tg003Kj23Tg003kj18Tg004Hj1GTg004fj2=Tg005Dj1XTg005dj1WTg006Dj2VTg006bj1UTg007@j1TTg007kj2RTg008Nj27Tg0091j3DTg009Tj2MTg00:7j1CTg00:Uj3BTg00;8j3LTg00;[j3KTg00<>j4:Tg00<ij2JTg00=Kj2ATg00=ej2ITg00>Qj3?Tg00>kj3HTg00?Jj4OTg00@<j2PTg00@Yj1QTg00A7j6FTg00A[j4STg00B<j6;Tg00BZj6ZTg00C6j3ETg00CYj7YTf0R0#1#1#1#1#1#1#1#1p=4%10#1p=Ng00D=R1f1R2;?0p=6P2g00D[R3g00E:R4P4g00EZR5P0g00F:FYp=<g00FZR6/@0g00G8R7#0R8#1#0#0#5R9,22%58R:%08#0#0#0#0#5'>'@P1%17R8#1#4#4#4#4#4#4#4#0#N#0#0#5R;f2R<'9R=%08R8#0R>#5R?,>:R@'3f3RA/29#8RB%G?RC'=,60X01P112<9#8RD/3@19;ARE/3@/60X01g00G]RF#XRG%WFRF1V12%U1RH%T1RIP11R17R717195D1,M1171:RJ%18#0#0R8#C5B1%C>9B1JRJ5L15D1g00HIR>171;=K17C:'<1JI5R7P0P<g00I0RKg00IPRL'A1I0<=?KLdAH162COR2b2b3b4X511209#8%58,>:R:/P@R8'219;0'6^51P0PAO1b112D8/6=P112B8R8130@f4/29#8/3@R9'6X01P113B@RA1609X011A1A138@PBP:P@PGPF%Q1R:PHPIP3P4P4P5P1PJP>1716R>C:,<IEFP7P2b2b3b4A?1@6g00J0[P0b1CSE;PEP0EZb71=DCPGPFP:PHP1P>g00JM171?C:,<IP7P2b2b3b41@6?P0b1R69ED?E;1==CAE=?6E;W9W8X61P0O1X61o"). Qed.

Lemma land_4095_word z : Z.land (bv_unsigned (Z_to_bv 64 z)) 4095 = Z.land z 4095.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W16 ()) ["CANSEC1"] "h01zh17__arithh24__ffh38__varmaph45__witp;1p;2p;3p;4p;7p;6g000Lj10Tg00:7j1PTg00K4j2CTg002Ij16Tg0011j15Tg004fj22Tg00>Qj31Tg001lj29Tg00@<j2<Tg003Kj24Tg004Hj1=Tg00=Kj28Tg00KZj4OTg00L4j4NTg005Dj1MTg005dj1LTg00@Yj1KTg006bj1JTg007@j1ITg008Nj2:Tg00<>j4HTg00CYj7BTg00<ij2DTg00=ej2ETg00>kj3ATg00?Jj4FTg0000j2GTg00C6j3;Tg00B<j67Tg00LZj2@Tg00M@j2?Tg00Mjj2>Tf0R0#6#6p=3g00D=R1P1g00G8R2#0R3#0#0#0#0#0#PR4/C0R5%62R2#3#3#3#3#3#5R6,20R7f1R8/26511X01P1%53R3%02R2#6#0#0#5'9R9%02#5R2,93R3'<R:,40R;/43%=2R<,289110X01P11403148:/43=110X01P0P:P3P11<03911:X01P9181:COCN120<g00G]R:#M%L:%K1%J1%I1R:g00D[g00E:R9P9g00EZR9P1g00FZR3,:1g00JM1:12CHg00F:FB1D:9P0f2R9g00I0R:g00IPR='81E09=1:=dAA138CFb2b3b41G32P0b1R39;02E712;<A;;23E71256=117e1@40,?41>40E7X01P0O1W0o"). Qed.

Lemma land3_range x : 0 <= Z.land x 3 <= 3.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W16 ()) ["CANSEC1"] "h07__arithh14__ffh28__varmaph35__with44__x1h51xh61Hh71zp;1p;2p;3p;4p;8p;6p;7g000Lj1TTg0011j19Tg001lj2@Tg003Kj28Tg0000j20Tg002Ij1LTg00NYj22Tg005Dj1?Tg005dj1>Tg00@Yj1=Tg006bj1<Tg007@j1:Tg008Nj23Tg00:7j1STg00:Uj3RTg00<>j46Tg00<ij2KTg00=Kj2HTg00=ej2DTg00>Qj3CTg00>kj3ATg00?Jj4BTg00O4j24Tg00OPj3ETg006Dj2FTg007kj2GTg00P7j1ITg00PYj8JTg004Hj1;Tg004fj2MTg00C6j3NTg00B<j6OTg00CYj7PTg00Q=j7QTf1R0g00D[R1g00E:R2P2g00EZR3f0R4g00F:FPp=1g00D=R5P0g00JMP4C6p=5f2R6P1P2P2P3P0P4FQp=7P5g00G8R7#TR8#9R9/@9R:,84R;g00FZR</04R=%L7#9R>,04'2X75g00G]R?#?R@%>?R?%=5RA%<5RB%:5RCP5135<RDg00QaRE1359RF%S85R5R8C6'11KC3RGP4P6g00I0RHg00IPRI'H1D46=CHIdAA5<0CBRIb1b2b314<:P4b09E4:10<;14;:'2P@P?1F50PBPCP1P2P2P31G57R7,5D,1CR3P5P7PEP8C6,1C57C%I2135>,57,1C97C3GJPGPIb1b2b3X45144:,2=10<0100>'2[^45P4186:P0O2b0b6%;9,M4P@P?PAPB15DF,1CPGPIb1b2b310<9P4b09N49EOX55P4O1X55o"). Qed.

Lemma land_4095_range y : 0 <= Z.land y 4095 < 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W16 ()) ["CANSEC1"] "h07__arithh14__ffh28__varmaph35__with41yh51zp;1p;2p;4p;3p;6p;7g000Lj11Tg0011j12Tg002Ij1>Tg001lj2LTg003Kj2JTg0000j26Tg00O4j24Tg00NYj2<Tg005Dj1;Tg005dj18Tg00@Yj19Tg006bj1:Tg007@j1KTg008Nj23Tg00<>j47Tg00<ij2ITg00=Kj2BTg00=ej2?Tg00>Qj3@Tg00>kj3ATg00?Jj4=Tg00OPj3CTg004Hj1DTg004fj2ETg00C6j3FTg00B<j6GTg00CYj7HTf0R0#1#1p=0f1R1g00D[g00E:R2P2g00EZR2P0g00F:FHp=5g00D=R3P3g00G8R4#1R5#2%>4#0#2R4'L,J0g00FZR6/60%15#0#0#0#0#0#2R5,40'<X53g00G]R7#;R8%87R7%93R9%:3R:%K3R;P31336R<g00Qa1335C7'51I;2R2P0f2R=g00I0R>g00IPR?'B1?0==@>?dAA361C=R1b1b2b31465P0b09C05%D4,E0P8P7P9P:P3P<g00JM1334C7,5;P2P1b1b2b31664P0b09F04EGX43P0O1W4o"). Qed.

Lemma round_up_pg_alt x : Z.land (- x) 4095 + x = round_up_pg x.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W16 ()) ["CANSEC1"] "h04__x1h14__x2h21xh37__arithh44__ffh58__varmaph65__witp;1p;2p;4p;3p;7g005Dj1HTg005dj1GTg006Dj2>Tg00@Yj1;Tg00RHj4FTg006bj1BTg007@j1?Tg007kj26Tg000Lj1<Tg0091j34Tg00<>j4:Tg00CYj78Tg00<ij29Tg00=Kj2ETg00=ej2CTg00>Qj31Tg00>kj3ATg00?Jj4@Tg001Oj22Tg003kj15Tg002Ij13Tg0011j1=Tg004fj27Tg00Rfj1DTf0R0#3#3p=0g00D=R1g00G]R2#H%G2P1f2R2,>1f1R3%;1CF%B1%?1R4g00D[g00E:R5P5g00EZR5P1g00G8R6,61R7%<6,61R8541g00HIA4187C:g00F:F81945P0P2g00I0R5g00IPR4'E1C02=154dg00FZ=A13C@b4b5b6X01X1112031230511^01^11P0P3%53%36#0#0#0#0#0#=R6'7O2b3%50/76/20%D0511eX21P0O1W2o"). Qed.

Lemma round_up_pg_range x : 0 <= x -> x <= round_up_pg x < x + 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W16 ()) ["CANSEC1"] "h04__x1h14__x2h21xh32H0h47__arithh54__ffh68__varmaph75__witp;2p;1p;4p;3p;8p;7g0000j21Tg003kj1@Tg00Sbj1JTg002Ij18Tg0011j1?Tg004fj2=Tg000Lj14Tg00O4j27Tg00NYj25Tg005Dj1BTg005dj1ATg006Dj2STg00@Yj1RTg00RHj4QTg006bj1NTg007@j1MTg008Nj2:Tg007kj29Tg00<>j46Tg00P7j1ITg0091j3;Tg00PYj8FTg00<ij2GTg00=Kj2HTg00=ej2ETg00>Qj3KTg00>kj3LTg00?Jj4DTg001Oj2>Tg00Rfj1CTg00CYj7OTg00Q=j7PTf0R0#8#8p=2%40#4p=0f1R1g00D[R2g00E:R3P3g00EZR4P0g00F:FOp=3f2R5P2P3P3P4P1P0FPp=<g00D=R6g00FZR7/10%@1R8#Jg00G8R9#8#2#2#2#2#2#?R:,=8R8,17%49R;#4#0#0#0#0#0#?R<,78'5g00G]R8#B%A8P61S65P1%R6CQ%N6%M6R8P2P3P3P4P61:67g00JMR2196;R;C6,38P6P;g00QaR=1:6<R>C6,385<8%I3P61969R9P2A;69;R;C6,38P6P;P=A;69>C6,385<8GF1G84P0P5g00I0R8g00IPR4'H1E05=K84dAL671CDb5b6b7X06X161171171<'51>15R5,111>1<R<,75'5[^06^16P0f3R5#@/=:P5P1O3b4b3%C1R5,11175<'5eUX26P0O1W2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Ltac bool_hyp b K := destruct b; cbn in K; first [reflexivity | discriminate | congruence | (exfalso; apply K; reflexivity)].

Section CANSEC2. Context {rc : runConstT}.
Section MMC.
Variables (sc size req : Z) (nos : bool).
Hypothesis SC : 0 <= sc < 48.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis RQ : 0 <= req < 2^32.
End MMC.


End CANSEC2.

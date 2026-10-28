(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ABase () := "C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3appc5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00c5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIc5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC47Corelib4Init5Logic7and_indC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC45stdpp;list_basics4list;list_filterC35stdpp4base6FilterC46Stdlib5Lists4List8flat_mapC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KENDK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subc5ARocqVerifyHarness?AgentSubmission5BothW5ABase4sclrc5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSc5ARocqVerifyHarness?AgentSubmission5BothW5ABase4iclrC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow7app_blkK46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic3notK46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3divC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow6HSH_LOC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow6HSH_HIK47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndc5ARocqVerifyHarness?AgentSubmission5BothW5ABase4wclrI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indI47Corelib5Lists7ListDef6Forall00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00i5ARocqVerifyHarness?AgentSubmission5BothW5ABase6uchain00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2wak5ARocqVerifyHarness?AgentSubmission5BothW5ABase6uchain01C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib5Lists4List9nth_errorC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8K47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegk5ARocqVerifyHarness?AgentSubmission5BothW5ABase6uchain02C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib5Arith8PeanoNat3Nat4predC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegk5ARocqVerifyHarness?AgentSubmission5BothW5ABase6uchain03c5ARocqVerifyHarness?AgentSubmission5BothW5ABase:uchain_indC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC46Stdlib9micromega;ZifyClasses5mkrelC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_lt".
Import ListNotations.
Open Scope Z_scope.

Notation amem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AMALLOC_SYM : Z := 0x5242c.    (* [comment removed for export] *)
Definition AFREE_SYM : Z := 0x52428.      (* [comment removed for export] *)
Definition AMALLOC_PC : Z := 0x526c8.     (* [comment removed for export] *)
Definition AFREE_PC : Z := 0x52568.       (* [comment removed for export] *)
Definition AMALLOC_STACK : Z := 4096.     (* [comment removed for export] *)
Definition AFREE_STACK : Z := 4096.
Definition ATP : Z := 0x5ed290.           (* [comment removed for export] *)
Definition AERRNO : Z := ATP - 164.       (* [comment removed for export] *)
Definition AREQMAX : Z := 2^29 + 2^10.    (* [comment removed for export] *)
Definition UDEPTH : nat := 28%nat.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AIMG_LO : Z := 0x10000.
Definition AIMG_HI : Z := 0x60f000.
Definition ARELRO_LO : Z := 0xb1000.
Definition ARELRO_HI : Z := 0xb3000.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition KLS : Z := 0x7fff7000.
Definition sclr (a n : Z) : Prop := a + n <= KLS \/ 0x10007fff8000 <= a.
Definition iclr (a n : Z) : Prop := 4096 <= a /\ (a + n <= AIMG_LO \/ AIMG_HI <= a).
Section ABLK. Context {rc : runConstT}.
Definition ablk (lo hi : Z) : Prop := (AIMG_HI <= lo /\ hi <= KLS) \/ (0x10007fff8000 <= lo /\ hi <= ATOP).

Lemma ablk_sub : forall lo hi lo' hi', ablk lo hi -> lo <= lo' -> hi' <= hi -> ablk lo' hi'.
Proof. intros lo hi lo' hi' H A B. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
(* [comment removed for export] *)
Lemma ablk_lin : forall lo hi, ablk lo hi -> AIMG_HI <= lo /\ 0 <= lo /\ hi <= ATOP /\ hi + 8 <= 2^47.
Proof. intros lo hi H. atop_facts. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
Lemma ablk_img : forall lo hi, ablk lo hi -> AIMG_HI <= lo.
Proof.
ltac2:(KReplay.run1 (kr_t_ABase ()) ["ABLK"] "h01Hh12H1h22H0h32H2h42H3h52hih62lop;2p;3p;1p;5g000dj2;Tg00R_j3:Tg004[j19Tg003Xj15Tg004=j16Tg00PHj22Tg0033j13Tg00MBj28Tg001Yj20Tg00SXj54Tg005Qj27Tf2R0f1R1'0f0R2'7p=1g00E@R31;12A:012g00QgR4g00K`R5p,2rc#9R6g00I0#5R7#5#5#6R8,21%67%37#3#3#3#6'8R7'0511710710f3R1,04R91208/0791069151P9f4R01218/079116515f5R1,05R51208/07910610411218/079116f6R0/06R61208/07f7R0,041208/07P1W4X16P2D4W3X05P2D4W1X29P2D4b0W0X53W6o"). Qed.
Lemma ablk_top : forall lo hi, ablk lo hi -> hi <= ATOP.
Proof.
ltac2:(KReplay.run1 (kr_t_ABase ()) ["ABLK"] "h01Hh12H1h22H0h32H2h42H3h52hih62lop;2p;3p;1p;5g000dj2:Tg00R_j39Tg001Yj20Tg004[j17Tg003Xj16Tg004=j14Tg00PHj22Tg0033j13Tg00MBj28Tg005Qj21Tg00SXj55Tg00E@R0f1R1f0R2':f2R3?912g00QgR4/03g00K`R5/03p,2rc#7R6,01g00I0#6R7#6#6#4R8,21%47%37#3#3#3#4'8R7'0'1'1'1f3R9,04R410591036R:1238/07'1'1P:f4R:,0510961298/07'1'1f5R9,05R510:6R312:8/07'1P310961298/07'1f6R9/06R61298/07P6f7/28/07P1W4X16P2D5W3X05P2D5W1X24P2D5b0W0X50W6o"). Qed.
Lemma ablk_kend : forall lo hi, ablk lo hi -> hi + 8 <= KEND.
Proof.
ltac2:(KReplay.run1 (kr_t_ABase ()) ["ABLK"] "h01Hh12H1h22H0h32H2h42H3h52hih62lop;2p;3p;1p;5p100T5p4p70R0p10000p4p710p8P0p100Tlp4p710p8P0p100UQR1p4p710p8P0P1p4p7210p8P0p100UeR1p4p710p8P0P1p4p7210p8g000dj2>Tg00R_j3=Tg004[j1:Tg003Xj10Tg004=j16Tg00PHj23Tg0033j15Tg00MBj29Tg001Yj21Tg00SXj57Tg005Qj2;Tf0R1#0#0p=<f2R0f1R2'1/;1p=2%01#0#0#0p=8%01#0#0#0#0#0#0#0p=4g00E@R31>21A=021g00QgR4g00K`R5p,2rc#:R6g00I0#0R7#<R8#6R9,32%67%57#5#5#5#6'9R7'1522720720f3R2,14R41309R:/1792069252%88#4#4#4#4#4#6R8,1:f4R01329/179226525f5R2,15R51309R;/17920611;81329/179226f6R2/16R61329R2/171128f7/39/17P1W4X16P1D7W3X05P1D7W1X24P1D7g00VB,1:eb0W0X53W6o"). Qed.
Lemma ablk_sclr : forall lo hi, ablk lo hi -> sclr lo (hi - lo).
Proof.
ltac2:(KReplay.run1 (kr_t_ABase ()) ["ABLK"] "h04__p1h14__p2h24__x1h34__x2h44__x3h51Hh62H0h77__arithh84__ffh98__varmaph:5__with;2hih<2lop;2p;1p;4p;3p;8p;6p;7g000dj2[Tg0025j1ZTg0033j13Tg003Xj10Tg004=j17Tg004[j1FTg001Yj22Tg005Qj2;Tg007`j1BTg008@j1YTg008`j2ATg009\j4TTg00::j1PTg00:Xj1OTg00;fj28Tg00;Cj2MTg00<mj1LTg00W7j3KTg00Ndj3GTg00D\j8HTg00=Oj2ITg00>1j2JTg00>Kj2ETg00?7j3DTg00?Qj3NTg00@0j4CTg00@bj2@Tg00WZj2?Tg00PHj2QTg00X7j2RTg00<Ij6STg00BEj4XTg00C0j7WTg00CTj7VTg00D8j7UTf0R0#3#3#3#3p=1%00#0p=:%00#0#0#0p=5%00#0#0#0#0#0#0#0p=4f1R1g00FJR2g00FiR3P3g00GIR4P0ESp=>g00E@R5P1g00GiP0CXp=9P1P2P3P3P4P0g00HPFWp=6f2R6P2P3P3P4P1P0FVp==P6P2P3P3P4P1P0FUp=<1[10p,2rcR7#Zg00I0R8#3R9#3#1#1#1R:#0#1#1#0#:#5#4#4#7%F7R7'2%3:#1#1#0#:#5#4#4#7,27';p-0R:g00E^R;#B%Y;P51A56P1f3R;,A5CT%P5%O5R<P2P3P3P4f5,><%08R2,85R=1859R9'9,6<5=<%52#4#1#1#1#1#0#:#5#4#7R2,M51858R8'9,6<R>f6,><5=<5<<%L3AK5=89G58/99,6<=<<>GH1I<4P0P6g00J`R<g00K@R4'J1E06=D<4dg00K`=N51CCb8b9b:X25X35X45X0:W11216,;;1220f4R4';'@1?61,Q1/2;1221'@[^25^35^45^0:^1:P012;7g00Qg/24g00XlP;P4P6O6b7b61?16,R6eW5X;5X<5o"). Qed.
Lemma ablk_iclr : forall lo hi, ablk lo hi -> iclr lo (hi - lo).
Proof. intros lo hi H. unfold ablk, iclr, AIMG_HI, AIMG_LO in *. lia. Qed.
(* [comment removed for export] *)
Lemma ablk_app_blk : forall lo hi, ablk lo hi -> lo <= hi -> app_blk lo hi.
Proof. intros lo hi H LE. atop_facts. unfold ablk, app_blk, AIMG_HI, KLS, KLOW, KHIGH, KEND in *. lia. Qed.
(* [comment removed for export] *)
Lemma ablk_clear_band : forall lo hi a, ablk lo hi -> KLS <= a < 0x10007fff8000 -> ~ (lo <= a < hi).
Proof. intros lo hi a H B. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
Lemma ablk_disj_band : forall lo hi, ablk lo hi -> hi <= KLS \/ 0x10007fff8000 <= lo.
Proof.
ltac2:(KReplay.run1 (kr_t_ABase ()) ["ABLK"] "h04__p1h14__p2h24__x1h34__x2h44__x3h51Hh62H0h77__arithh84__ffh98__varmaph:5__with;2hih<2lop;2p;1p;4p;8p;3p;6p;7g000dj2UTg0025j1TTg0033j13Tg003Xj10Tg004=j19Tg004[j1ETg001Yj22Tg005Qj27Tg007`j1ATg008@j1STg008`j2@Tg009\j4RTg00::j1NTg00:Xj1MTg00;fj26Tg00BEj4=Tg00;Cj2GTg00<mj1FTg00D\j8HTg00=Oj2ITg00>1j2JTg00>Kj2KTg00?7j3LTg00?Qj3DTg00@0j4CTg00@bj2?Tg00<Ij6BTg00C0j7OTg00CTj7PTg00D8j7QTf0R0#3#3#3#3p=1%00#0p=8%00#0#0#0p=5%00#0#0#0#0#0#0#0p=4f1R1g00FJR2g00FiR3P3g00GIR4P0EBp=>P1P2P3P3P4P0g00HPFOp=:f2R5P2P3P3P4P1P0FPp=<P5P2P3P3P4P1P0FQp=;g00E@R61U10p,2rcR7#Tg00I0R8#3R9#3#1#1#1R:#0#1#1#0#8#5#4#4#9%E7R7'2%3:#1#1#0#8#5#4#4#9,27'7p-0R:g00E^R;#A%S;P61@65P1f3R;,@6CR%N6%M6R<P2P3P3P4f5,><P61668g00GiR2%08R8,66C=,:<R=5<<P6%58#4#1#1#1#1#0#8#5#4#9R8,G6P21669C=,:<R9f6,><5<<5;<%F3A;<=9GH1I<4P0P5g00J`R<g00K@R4'J1K05=L<4dg00K`=D61CCb8b9b:X26X36X46X0:W11201,7;1285f4R4'7'?1215128;'?[^26^36^46^0:^1:P012;7g00Qg/24P4g00XlP;P5O6b7b6W5X;6W<o"). Qed.
(* [comment removed for export] *)
Lemma ablk_shad : forall lo hi, ablk lo hi -> lo <= hi ->
  (shad AIMG_HI <= shad lo /\ shad hi <= shad KLS) \/ (HSH_LO <= shad lo /\ shad hi < HSH_HI).
Proof.
  intros lo hi H LE. atop_facts. rewrite !shad_div. unfold ablk, AIMG_HI, KLS, ASHOFF, HSH_LO, HSH_HI in *.
  Z.div_mod_to_equations; lia.
Qed.
Lemma ablk_shad_lin : forall lo hi, ablk lo hi -> lo <= hi -> shad AIMG_HI <= shad lo /\ shad hi < HSH_HI.
Proof.
  intros lo hi H LE. atop_facts. rewrite !shad_div. unfold ablk, AIMG_HI, KLS, ASHOFF, HSH_HI in *.
  Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Lemma ablk_shad_disj : forall lo hi, ablk lo hi -> lo <= hi -> hi <= shad lo \/ shad (hi + 7) + 1 <= lo.
Proof.
  intros lo hi H LE. atop_facts. rewrite !shad_div. unfold ablk, AIMG_HI, KLS, ASHOFF in *.
  Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Definition wclr (iv : Z * Z) : Prop := AIMG_HI <= fst iv /\ sclr (fst iv) (snd iv - fst iv).
Lemma wclr_high : forall lo hi, 0x10007fff8000 <= lo -> wclr (lo, hi).
Proof. intros lo hi H. unfold wclr, sclr, AIMG_HI. cbn [fst snd]. lia. Qed.
Lemma wclr_ablk : forall lo hi a b, ablk lo hi -> lo <= a -> b <= hi -> wclr (a, b).
Proof. intros lo hi a b H A B. unfold wclr, sclr, ablk, AIMG_HI, KLS in *. cbn [fst snd]. lia. Qed.
Lemma wclr_outside_band : forall W x, Forall wclr W -> KLS <= x < 0x10007fff8000 -> outside W x.
Proof.
ltac2:(KReplay.run1 (kr_t_ABase ()) ["ABLK"] "p'0h02FWh11Hh22H0h32H1h42H2h51li001lh61Wh71eh82IHh94__p1h:4__x1h;4__x2h<4__x3h=4__x4h>2Hxh?7__arithh@4__ffhA8__varmaphB5__withC1ahD2hihE2lohF1pi011phG1xi021xhH1yi031zp;2p;1p;3p;6p;4p;7p;8g00mYR0j2lTg008@R1j1OTg001Yj27Tg003Xj11Tg004=j1YTg00Lfj2ATg005Qj2<Tg00n9j23Tg007`j1GTg00Aej34Tg00?7j30Tg00noj6dTg00oKj2^Tg00ldR2j1DTg00ojj6KTg00\1j1ZTg005lj1@Tg0077j2:Tg00A<j3?Tg006Kj2ITg008`j2HTg009>j1XTg009\j4FTg00::j1WTg00:Xj1VTg00<Ij6TTg00;fj2>Tg0033j1BTg00W7j3STg00Ndj3RTg00;Cj2QTg00D8j7UTg00<mj1kTg00BEj4CTg00[Mj6jTg00=Oj2iTg00>1j2NTg00>Kj2gTg00?Qj3fTg00@0j4cTg00WZj2bTg00PHj2aTg00@bj2_Tg010Gj4`Tg00g@j6LTg010bj6]Tg011DR3j3eTg00kJj4JTg00C0j7\Tg00CTj7[Tg00D\j8hTf1R4f0R57e2p=6%15#1p=M%15#1#1#1p=;%B5#Bp=5f3R6g00E@R7P7f2R8P4CJ;45p=2P7P7P4P5CJp=9P7P4g00GiP5CCp==P4g00FJR9g00FiR:P:g00GIR;P5g00HPF\p=8P8P9P:P:P;P4P5F[p=EP6P9P:P:P;P8P4P5Ghp=P1l77R<#OR=16<4R>g00XlR?/74g00I0R@#1RA#1RB#1#M#;#;#5#5#5#5#5#5#5#5#1#M#;#;#;#YRC,A4'<P<16<5RDf4RE,34]0X6=%G<RF,6<g011eRGW0P0P7P7f6R0,34^0DA4<84,6<A4<68RHf7RI'3]0[^5=P5f9RJ,34^0DP<P6P8P4C2,6<P3P<P2P<P0f5R2PEC2R390=4P<PIP0P2C2f=RD'3RK[P5P<PEP6P8C2RL90=FP<P2PEP6C2RM90=FP=PFP1P<p-0RFP5g00Peg00]1RNn10110000020020000000X7=PGP3P5EdPN1^K5b2W1P5O1W1%D4RKP<f<RGf;ROf:RPC290=HA4<E6P<PDPGPOC250=P=P=P1P<P=P5P2P5n10110000020020101100X7=A4<2EP<f>RHPDPGC2P5EKA0=EGP=P<P1P<P<P5PIP4n10110000020020101100X7=A4<02f?R2/9HRH=4<DP4EKA0<0Hf@RH/9290<IP5f8RIfAR2/9H50<P<fBRD/92A0=J2R216<OP<fFROfER1fDRQC2fLRR'3RS]4^3K[XF<A0=IHP5P2P=PD191Q#DP<fGRDPOP1C2fM'3^4>]3X5=fCR2,9Q#D16<217OR1AR1'<#Z13QRRQP2P5O1R2PQg00E^RQg00IUR1#@RO#@RI#@RH#@,:7RK1:7I1:7O5?75?7g00J4RO'I1:7H1:715?79?7K/IO%GQ54Q34%OQP7P71H7EP8%X7CFP41H76CF%W7%V7RQPQP9P:P:P;P0ETPQP9P:P:P;1>7@R0%B@,>7R@=S705R71>7BRB'=,8Q1Q7CRO/=0,8QFU5EQ%k:RKPQ1>7ARA,=B,8QP7PAg00\JRBPOCC,8Q5EQPKPQP9P:P:P;1=0A,8QP7PAPBP@CC,8Q5EQEjCPCP1iQ;P5P8g00J`RQg00K@R;'N1g58=0Q;dg00K`=f74Ccb@bAbBX:7X;7X<7X=7X9F1b85,a5/7617C5'_,<E17E81A8C'<17861A6E'<PN[[[^:7^;7^<7^=7^9FP5g00QgfHRF'7P?PDfNPFP6PRO7b?b8P2C`PSeW4W3PPP5ELb3W2PJP5ELb2W1P5O1b2P5O1b2W1P5P8P4O3W1X4>W3X5=XH<P6P8P4P5O4n200210000000020041102100000000A0=5M133G[X5=PLO1P51N=MO1b1W0W8X6=XD7XE7P4P5O2n2001101000121103103XC<P6P4E]W>W0XG7W6o"). Qed.
Lemma wclr_outside_img : forall W x, Forall wclr W -> x < AIMG_HI -> outside W x.
Proof.
ltac2:(KReplay.run1 (kr_t_ABase ()) ["ABLK"] "p'0h02FWh11Hh22H0h32H1h42H2h51li001lh61Wh71eh82IHh94__p1h:4__p2h;4__x1h<4__x2h=4__x3h>2Hxh?7__arithh@4__ffhA8__varmaphB5__withC1ahD2hihE2lohF1pi011phG1xi021xhH1yi031zp;2p;1p;3p;6p;4p;7p;8g00mYR0j2bTg008@R1j1JTg00Lfj26Tg00n9j22Tg007`j1ITg00Aej33Tg00?7j30Tg00noj6PTg00oKj2NTg00ldR2j1<Tg00ojj6HTg001Yj2;Tg005Qj28Tg00\1j1YTg005lj1ETg0077j29Tg00A<j3DTg006Kj2WTg008`j2VTg009>j1STg009\j4CTg00::j1RTg00:Xj1QTg003Xj1ATg00;fj2=Tg00BEj47Tg00<mj1MTg00[Mj6OTg00=Oj2LTg00>1j2BTg00>Kj2KTg00?Qj3TTg00@0j4UTg00WZj2aTg00X7j2`Tg010Gj4_Tg00g@j6GTg010bj6]Tg011DR3j3\Tg00kJj4FTg00C0j7ZTg00<Ij6[Tg00CTj7XTg00D\j8^Tf1R4f0R57\2p=4f3R6g00E@R7P7f2R8P4CF;35p=1P7P7P4P5CFp=5P4g00FJR9g00FiR:P:g00GIR;P5g00HPFZp=:P4P9P:P:P;P5E[p=@P8P9P:P:P;P4P5FXp=?P6P9P:P:P;P8P4P5G^p=>1b77R<#JR=14<4R>g00QgR?,64P<14<5R@f4RA,24]0X6=%I<RB,4<g011eRCW0P0P7P7f6R0,24^0@A3<84,4<A3<68RDf7RE'2]0[^5=P5f9RF,24^0@P<P6P8P4C1,4<P3P<P2P<P0f5R2PAC1R390=4P<PEP0P2C1f=R@'2RG[P5P<PAP6P8C1RH90=BP<P2PAP6C1RI90=BP=PBP1P<p-0RBP5g00Peg00]1RJn10110000020020000000X7=PCP3P5EPPJ1NG5b2W1P5O1W1%<4RGP<f<RCf;RKf:RLC190=DA3<A6P<P@PCPKC150=P=P=P1P<P=P5P2P5n10110000020020101100X7=A3<2AP<f>RDP@PCC1P5EHA0=ACP=P<P1P<P<P5PEP4n10110000020020101100X7=A3<02f?R1/5DRD=3<@P4EHA0<0Df@RD/5190<EP5f8REfAR1/5D50<P<fBR@/51A0=F1R114<KP<fFRKfERAfDRMC1fLRN'2RO]4^3G[XF<A0=EDP5P1P=P@15AM#<P<fGR@PKPAC1fM'2^4>]3X5=fCR1,5M#<14<11;KN16NA'8#Y12MNRMP1P5O1R1PMg00E^RMg00IURA#ERK#E,97197K197A5D75D7g00J4'W%IM33%JMP7P71V76P8%S7RMCCP4PMCC%R7%Q7RMP7g00I0RA#ARK#A,=7REg00GiRD1=7ARAC7,:M1@M25?M%M:R2PMP71=7KRKg00\JPEC7,:MP2PMP9P:P:P;P7PAPDPKC7,:M1@M05?MEOC>C>1LM;P5P8g00J`RMg00K@R;'B1K58=0M;dg00K`=T74CUb@bAbBX;7X<7X=7X9BX:B1;85/8616861;86/80PJ[[[^;7^<7^=7^9B^:BP5fNRB/6@fHRJ1a@J'`P?PBPJP6PNO7b?b8P1C_POeW4W3PLP5EGb3W2PFP5EGb2W1P5O1b2P5O1b2W1P5P8P4O3W1X4>W3X5=XH<P6P8P4P5O4n200210000000020041102100000000A0=5I123C[X5=PHO1P51B=IO1b1W0W8X6=XD7XE7P4P5O2n2001101000121103103XC<P6P4E]W>W0XG7W6o"). Qed.
Lemma wclr_disjoint_band : forall W a n, Forall wclr W -> KLS <= a -> a + n <= 0x10007fff8000 -> disjoint_from W a n.
Proof.
ltac2:(KReplay.run1 (kr_t_ABase ()) ["ABLK"] "p'0h02FWh11Hh22H0h32F1h42F2h51li001lh61Wh71eh82IHh94__p1h:4__x1h;4__x2h<4__x3h=4__x4h>4__x5h?2H1h@2H2hA2H3hB7__arithhC4__ffhD8__varmaphE5__withF1ahG2a0hH2hihI2lohJ1nhK1pi011phL1yi021xi031zp;2p;1p;3p;6p;4p;7p;8g00mYR0j2iTg008@R1j1PTg001Yj21Tg00PHj2=Tg003Xj13Tg004=j1WTg012Aj35Tg007`j1GTg00Aej34Tg00?7j30Tg00noj6aTg00oKj2\Tg00ldR2j1DTg00ojj6MTg00@bj2CTg005lj1ATg0077j2<Tg00A<j3@Tg006Kj2JTg008`j2ITg009>j1XTg009\j4BTg00::j1VTg00:Xj1UTg00<Ij6TTg0033j1?Tg00;fj2>Tg00W7j3RTg00Ndj3FTg00;Cj2QTg00CTj7STg00<mj1hTg00=Oj2gTg00>1j2OTg00>Kj2fTg00?Qj3eTg00@0j4`Tg00WZj2_Tg005Qj2]Tg010Gj4[Tg00g@j6NTg010bj6^Tg011DR3j3ZTg00kJj4LTg00BEj4bTg00C0j7YTg00D8j7cTg00D\j8dTf1R4f0R57Z2p=7%35#3p=K%35#3#3#3p=;%?5#?p=6f3R6g00E@R7P7f2R8P4CL;45p=2P7P7P4P5CLp=:P7P4g00GiP5Cbp=8P4g00FJR9g00FiR:P:g00GIR;P5g00HPFYp=9P8P9P:P:P;P4P5Fcp=HP6P9P:P:P;P8P4P5Gdp=E1i77R<#PR=17<8g00XlR>/181=68g00I0R?#3R@#3RA#3#K#;#;#6#6#6#6#6#6#6#6#3#K#;#;#;#WRB'1P<17<5RCf6RDf5RE554]0X6=%G<RF,7<g011eRGW0P0P7P7f8R0f7RH554^0CA4<84,7<A4<68RIf9RJ;50]0[^5=P5f;RKf:RL554^0CP<P6P8P4C2,7<P3P<P2P<PDPEf4R2C2R390=4P<PHPDPEC2f?RCf>RM35RN[P5P<P2P6P8C2RO90=FP<PEP2P6C2RP90=FP=PFP1P<p-0RFP5g00Peg00]1RQn10110000020020000000X7=PGP3P5EaPQ1\N5b2W1P5O1W1%D4RN17<4RQP<f<RGPKPLC290=IA4<26P<f=RIPGPKC250=P=P=P1P<P=P5PEP5n10110000020020101100X7=A4<E2P<PMPIPGC2P5EMA0=2GP=P<P1P<P<P5PHP4n10110000020020101100X7=A4<DE1:CMR1=4<IP4EMA0<D1f@R1/:C90<HP5fARC/:190<0P<fBRG/:CA0=JCRC17<KP<fFRKfERRfDRSC2fNRTfMRU35RV]4^3N[XK<A0=01P5PCP=PG1:RS#DP<fGRGPKPRC2fORC;5T^4Q]3X5=fCRQ,:S#D17<Q1=TU/1K11RT'CA5STURTPQP5O1RQPTg00E^RTg00IURS#ARR#ARK#AR1#A,<7R01<711<7R5@75@7g00J4RR'J1<7K1<7S5@79@70/JR%GT54T34%PTP7P71I72P8%X7RTCBP4P71I7EP6PTCBCB%V7%U7RTPTP9P:P:P;PTP9P:P:P;PHET%??,>7RH1>7ARA=R7H5F7%?@,>7R9'8,9T1Q7BRR/8H,9T5HTFS%h:R:PT1>7?R?1>7@5F7R@/8R,9TP:PT189?,9TP:18@H,9T18A?,9T5HTCECECE1gT;P5P8g00J`RTg00K@R;'O1f58=0T;dg00K`=e74C`bCbDbEX:7X;7X<7X=7X>7X9F1_68,=8/1211B8'C,]E1=48/1B11D81=62/1E11D6'C[[[^:7^;7^<7^=7^>7^9FP5g00QgfHRF'1P>PGPFPCfPP6fLPUO9bBb8PQC[PVeW4W3PLP5ENbAW2PJP5ENb2W1P5O1b2P5O1b2W1P5P8P4O3W1W4W3X5=XL<P6P8P4P5O4n200210000000020041102100000000A0=5PA53MI[X5=POO1P51O=PO1b1W0W8X6=XH7XI7P4P5O2n2001101000121103103XG<PEP8E^W@W?W0XJ7XF7W6o"). Qed.
Lemma wclr_disjoint_img : forall W a n, Forall wclr W -> a + n <= AIMG_HI -> disjoint_from W a n.
Proof.
ltac2:(KReplay.run1 (kr_t_ABase ()) ["ABLK"] "p'0h02FWh12H0h22H1h32F1h42F2h51li001lh61Wh71eh82IHh94__p1h:4__p2h;4__x1h<4__x2h=4__x3h>4__x4h?1Hh@2H2hA7__arithhB4__ffhC8__varmaphD5__withE1ahF2a0hG2hihH2lohI1nhJ1pi011phK1yi021xi031zp;2p;1p;3p;6p;4p;7p;8g00mYR0j2dTg008@R1j1ITg00PHj27Tg001Yj25Tg012Aj32Tg007`j1CTg00Aej33Tg00?7j30Tg00noj6QTg00oKj2LTg00ldR2j1;Tg00ojj6JTg00@bj2GTg005lj1ETg0077j2<Tg00A<j3DTg006Kj2XTg008`j2BTg009>j1WTg009\j4@Tg00::j1VTg00:Xj1UTg003Xj1STg0033j1>Tg00;fj28Tg00CTj7PTg00<mj1OTg00Ndj3MTg00D8j7NTg00=Oj2RTg00>1j2FTg00>Kj2KTg00?Qj3TTg00@0j4cTg005Qj2bTg00WZj2aTg00X7j2`Tg010Gj4_Tg00g@j6HTg010bj6]Tg011DR3j3\Tg00kJj4ATg00BEj4[Tg00C0j7ZTg00<Ij6^Tg00D\j8YTf1R4f0R57\2p=4f3R6g00E@R7P7f2R8P4CA;35p=1P7P7P4P5CAp=6P7P4g00GiP5C[p=:P4g00FJR9g00FiR:P:g00GIR;P5g00HPFZp=9P4P9P:P:P;P5E^p==P6P9P:P:P;P8P4P5GYp=?1d77R<#IR=14<81784g00QgR>'5P<14<5R?f5R@f4RA524]0X6=%C<RB,4<g011eRCW0P0P7P7f7R0f6RD524^0?A3<84,4<A3<68REf8RF;20]0[^5=P5f:RGf9RH524^0?P<P6P8P4C1,4<P3P<P2P<PDP@PAC1R290=4P<P0PDP@C1f>R3f=R?32RI[P5P<PAP6P8C1RJ90=BP<P@PAP6C1RK90=BP=PBP1P<p-0RBP5g00Peg00]1RLn10110000020020000000X7=PCP2P5EQPL1LI5b2W1P5O1W1%;4RI14<4RLP<f<RCf;RMPGC190=EA3<A6P<P?PCPMC150=P=P=P1P<P=P5P@P5n10110000020020101100X7=A3<@AP<P3P?PCC1P5EJA0=ACP=P<P1P<P<P5P0P4n10110000020020101100X7=A3<D@f?R@/63R3=3<?P4EJA0<D3f@R3/6@90<0P5fAR@/6390<FP<fBR1/6@A0=H@R@14<MP<fFRMfEREfDRNC1fMROfLRP32RQ]4^3I[XJ<A0=F3P5P@P=P116EN#;P<fGR1PMPEC1fNR@;2O^4L]3X5=fCRL,6N#;14<L17OP/5M15EO'GA2NOPROPLP5O1RLPOg00E^ROg00IURN#ERE#E,<71<7E1<7N5D75D7g00J4'X%CO33%IOP71B78P4P71B7AP6%W7C@C@%V7%U7ROPOP9P:P:P;g00I0RN#SRE#>,87RM%>N,87R3':,9O1=ODFP%O:RDPO187N187E5M7RE/:M,9OPDPOP9P:P:P;1:E3,9O1=O0FNC?C?1RO;P5P8g00J`ROg00K@R;'F1K58=0O;dg00K`=T74CcbBbCbDX;7X<7X=7X>7X9BX:B1568/bA1748/5A1786/5A/G0[[^;7^<7^=7^>7^9B^:BP5fORB,51fHR01a10'`P>P0P@PBP6PPO8bAb8PLC_PQeW4W3PGP5EHb@W2PHP5EHb2W1P5O1b2P5O1b2W1P5P8P4O3W1W4W3X5=XK<P6P8P4P5O4n200210000000020041102100000000A0=5KA22?C[X5=PJO1P51F=KO1b1W0W8X6=XG7XH7P4P5O2n2001101000121103103XF<PAP4E]W?W0XI7XE7W6o"). Qed.
(* [comment removed for export] *)
Lemma shad_in_band : forall a, 0 <= a < 2^47 -> KLS + 4096 <= shad a < 0x10007fff8000.
Proof.
ltac2:(KReplay.run1 (kr_t_ABase ()) ["ABLK"] "h02H1h12Hah26__sat6h34__x1h44__x2h54__x3h61Hh72H0h82H2h92H3h:2H4h;7__arithh<4__ffh=6__sat5h>8__varmaph?5__with@1ahA1qhB1rhC1zp;1p;2p;3p;4p;6p;7p;8g003Xj10Tg004=j16Tg00MBj2uTg00]Nj2CTg00PHj28Tg001Yj2>Tg00^cj2UTg00?7j3:Tg00\1j1tTg00g^j2PTg00_Dj2?Tg00_dj2qTg00Lfj2;Tg00`Kj2fTg005Qj2NTg00a2j2aTg00aXj2`Tg00NCj2OTg00>1j2FTg00L>j2\Tg00M_j3[Tg005lj1@Tg0077j2=Tg00cPj1ZTg00cnj2YTg00dOj3XTg00b>j2WTg00bgj3VTg006Kj2MTg007`j1TTg00Aej3KTg008@j1RTg008`j2LTg009\j4STg00::j1sTg00:Xj1rTg00;Cj2QTg0033j12Tg00;fj2JTg00<mj1pTg00BEj4ATg00[Mj6oTg00edj3nTg00Ndj3DTg00OGj1eTg00Oej3dTg00=Oj2bTg00>Kj2gTg00?Qj3hTg00@0j4iTg00]kj1jTg00fGj1kTg00g@j6lTg00A<j3mTg00C0j7_Tg00CTj7^Tg00D\j8]Tg00K`R0f0R1'>p=7%21#2#2#2p=4f2R2f1R3/;1'Np=5%01#0p=G%01#0#0#0p=1g00E@R4?m31p=9P4P3g00GiP1CAp=EP3g00FJR5g00FiR6P6g00GIR7P1g00HPF_p=31Q41p=<P4P3g00\JP1CAp=IP2P5P6P6P7P3P1F^p=Hf3R8P5P6P6P7P2P3P1G]p=B%21#2p=c%71R9g00I0R:#0R;#6R<%4;R=#6R>'uR?751P4g00hb%G;R@#6RA,C3'8RBg00Xl%0@#1#1R@#6RC'8RD/>1%0@#4#4#4#4#0#G#1#1#1#6R@751XC41U3AA:4A0RE#t1C2A,PA1?2A'89:42[1q2A1;0ARF1?8ARG#7?5GA[1f8A1;A0f4RG/?ARH,;A1>H0'N[1aGAf5RH/CA=:40\E1`HAf6RI/?A=:4I\E1CIAP4f7/?AP4PHg00QARJ1O0A'FPFeO1A591A1\<>1;0<R9%7>1;0?[RF[%7<RKg00PeRLA[<>3UW1%7?\L^1KP31O0<,FJP9eO1PFg00E^RFg00IUR9#@RJ#@RK#@RL#@R>#@,=4%Z:,Y41=4LRL5X41=4J1W4A1=495V4R9'9'9'9g00J4RJ'M1=4>1=4K/99,9L'9/MJ%TF5KF3K%RFP41L42P31L48CS%s4%r4RF1Q40RJ%2:RL,J4R9'E,3F%<ARK,I9,3F5HF%p6R>PFPFPFP5P6P6P7P4PKg00h;R6PJCA,3FEoP>P41J4;R;P61J4:R:9n4K=D49CA,3FCBP>PF1EJ;,3F%<<%e=5d4,I;,3F5HFP>%2L#4#4#4RL#0#2#c#1#1#1#6R>#<%<C5D4%2L#0#G#1#1#1#6RL#<=D4:R:'E,3F%<@,I:,3F5HFCBCBCB1bF7P1P2g00J`RFg00K@R7'F1g12=:F7dAh403Cib<b>b?X34X44X54%72?52Ag00]1\E1PA2/8G9:48[%78?58?18>C18L8RL'>?5L@[[[^34^44^54P1PHf=PIPGf;f<O6b;b2b=b2b0bBbAb:b9b8b0b71>DB?5B@e%j3%k3ElW6X@4o"). Qed.
End ABLK.

(* [comment removed for export] *)
Definition artcells (m : amem) : Prop :=
     rw_cells bsegs m 0xb2108 [C8 (Z_to_bv 64 0x149da0)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb2118 [C8 (Z_to_bv 64 0x14be28); C8 (Z_to_bv 64 0xb7af8); C8 (Z_to_bv 64 0xba2f8);
                                C8 (Z_to_bv 64 0xbafe8); C8 (Z_to_bv 64 0xbaff0); C8 (Z_to_bv 64 0xbafe0)]   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb2c90 [C8 (Z_to_bv 64 0xbafd9)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb3fa0 [C8 (Z_to_bv 64 0xab458); C8 (Z_to_bv 64 0xab85c)]         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xba2f8 [C8 (Z_to_bv 64 0x7fff8000)]                                 (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xba300 [C4 (Z_to_bv 64 1)]                                          (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbafd8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbafe0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb9b5c [C1 (Z_to_bv 8 1)]                                           (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbaffc [C4 (Z_to_bv 64 30)]                                         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x149da0 [C8 (Z_to_bv 64 4096)]                                       (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x14be48 [C8 (Z_to_bv 64 0x1e00010000)]                               (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x14bea0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb3e98 [C8 (Z_to_bv 64 0xaada8); C8 (Z_to_bv 64 0xa7c98)]         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb3f50 [C8 (Z_to_bv 64 0xabce4)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb3e78 [C8 (Z_to_bv 64 0xb0b5c)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb3e80 [C8 (Z_to_bv 64 0xa7a10)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb3f50 [C8 (Z_to_bv 64 0xabce4)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb3e68 [C8 (Z_to_bv 64 0xab35c)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x14be78 [C8 (Z_to_bv 64 4294967296)]                                 (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x14bf20 [C8 (Z_to_bv 64 0x101010101010101)]                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb7b58 [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x149d98 [C4 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Definition in_ranges (l : list (Z * Z)) (a : Z) : Prop := exists iv, In iv l /\ fst iv <= a < snd iv.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AINSTANCE : Z := 0xb6c98.     (* [comment removed for export] *)
Definition AFLAGS : Z := 0xb7af8.        (* [comment removed for export] *)
Definition ACFLAGS : Z := 0x14be28.       (* [comment removed for export] *)
Definition AINITED : Z := 0xbafd8.       (* [comment removed for export] *)
Definition ACANPOISON : Z := 0xb9b5c.    (* [comment removed for export] *)
Definition AMCTXSZ : Z := 0xbaffc.       (* [comment removed for export] *)
Definition ASHBASE : Z := 0xba2f8.       (* [comment removed for export] *)
Definition AMIDBEG : Z := 0xbafe8.       (* [comment removed for export] *)
Definition AMIDEND : Z := 0xbaff0.       (* [comment removed for export] *)
Definition AHIGHEND : Z := 0xbafe0.      (* [comment removed for export] *)
Definition AREALMEMSET : Z := 0xb3fa8.   (* [comment removed for export] *)
Definition AMEMSET : Z := 0xab85c.
Definition APGSZ : Z := 0x149da0.         (* [comment removed for export] *)
Definition ATSDI : Z := 0xb9b60.         (* [comment removed for export] *)
Definition ATSDK : Z := 0xb9b64.         (* [comment removed for export] *)
Definition ATP88 : Z := 0x5ed238.         (* [comment removed for export] *)
Definition ATSD : Z := 0x60e638.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition GOT_PGSZ : Z := 0xb2108.      (* [comment removed for export] *)
Definition GOT_CFLAGS : Z := 0xb2118.    (* [comment removed for export] *)
Definition GOT_FLAGS : Z := 0xb2120.     (* [comment removed for export] *)
Definition GOT_SHBASE : Z := 0xb2128.    (* [comment removed for export] *)
Definition GOT_MIDBEG : Z := 0xb2130.    (* [comment removed for export] *)
Definition GOT_MIDEND : Z := 0xb2138.    (* [comment removed for export] *)
Definition GOT_HIGHEND : Z := 0xb2140.   (* [comment removed for export] *)
Definition GOT_REALMEMSET : Z := 0xb2148. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Record alayout := mkALayout {
  al_V : nat -> Z;            (* [comment removed for export] *)
  al_w : bool;                (* [comment removed for export] *)
  al_U : list (list Z)        (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition al_sp0 (L : alayout) : Z := 32768 * al_V L 0%nat + 16 * al_V L 6%nat.       (* [comment removed for export] *)
Definition al_top (L : alayout) : Z := page_round_up_Z (al_sp0 L - 0xa0).              (* [comment removed for export] *)
Definition al_bot (L : alayout) : Z := al_top L - 0x800000.                             (* [comment removed for export] *)
Definition al_t (L : alayout) : Z := 4096 * al_V L 240%nat.                             (* [comment removed for export] *)
Definition al_ctx (L : alayout) : Z := 4096 * al_V L 241%nat.                           (* [comment removed for export] *)
Definition al_space_beg (L : alayout) : Z := 4096 * (al_V L 221%nat - al_V L 222%nat) + 0x10000.
Definition al_ptr_array (L : alayout) : Z := 4096 * al_V L 239%nat.
Definition al_nodes (L : alayout) : Z := 4096 * al_V L 485%nat.                         (* [comment removed for export] *)
Definition al_store (L : alayout) : Z := 4096 * al_V L 486%nat.                         (* [comment removed for export] *)
Definition al_fake (L : alayout) : Z := 4096 * al_V L 406%nat.                          (* [comment removed for export] *)
Definition AUMAX : Z := 4096.                                                           (* [comment removed for export] *)

Inductive abkind := ABHeap (p : aptr) | ABFake (cls : Z).
Record ablock := mkABlock { ab_kind : abkind; ab_addr : Z; ab_size : Z }.
Notation HB p A n := (mkABlock (ABHeap p) A n).

Definition in_block (LB : list ablock) (a : Z) : Prop :=
  exists b, In b LB /\ ab_addr b <= a < ab_addr b + ab_size b.
Definition in_fake (LB : list ablock) (a : Z) : Prop :=
  exists cls A n, In (mkABlock (ABFake cls) A n) LB /\ A <= a < A + n.

Definition abkind_eqb (k k' : abkind) : bool :=
  match k, k' with
  | ABHeap p, ABHeap p' => (p =? p')%N
  | ABFake c, ABFake c' => c =? c'
  | _, _ => false
  end.
Definition lb_remove (p : aptr) (LB : list ablock) : list ablock :=
  filter (fun b => negb (abkind_eqb (ab_kind b) (ABHeap p))) LB.
(* [comment removed for export] *)
Definition hb_ids (LB : list ablock) : list aptr :=
  flat_map (fun b => match ab_kind b with ABHeap p => [p] | ABFake _ => [] end) LB.

(* [comment removed for export] *)
Definition ablock_range {rc : runConstT} (A n : Z) : Prop :=
  ablk A (A + n) /\ 0 <= n /\ A + n <= ATOP /\ A mod 16 = 0.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ablock_shadow (m : amem) (A n : Z) : Prop :=
  forall g, 0 <= g -> 8 * g < n ->
    m (wa (shad A + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? n then 0 else n - 8 * g)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive uchain (m : amem) (top pc : Z) : Z -> Z -> nat -> list Z -> Prop :=
| uc_stop : forall prev frame k,
    ~ (prev < frame /\ frame < top - 16 /\ frame mod 8 = 0 /\ (0 < k)%nat) ->
    uchain m top pc prev frame k []
| uc_lowpc : forall prev frame k fp ra,
    prev < frame -> frame < top - 16 -> frame mod 8 = 0 -> (0 < k)%nat ->
    bytes_at bsegs m (frame - 16) (le8 (Z_to_bv 64 fp)) ->
    bytes_at bsegs m (frame - 8) (le8 (Z_to_bv 64 ra)) ->
    0 <= ra < 4096 ->
    uchain m top pc prev frame k []
| uc_step : forall prev frame k fp ra tr,
    prev < frame -> frame < top - 16 -> frame mod 8 = 0 -> (0 < k)%nat ->
    bytes_at bsegs m (frame - 16) (le8 (Z_to_bv 64 fp)) ->
    bytes_at bsegs m (frame - 8) (le8 (Z_to_bv 64 ra)) ->
    4096 <= ra < 2^64 -> 0 <= fp < 2^64 ->
    uchain m top pc frame fp (if ra =? pc then k else Nat.pred k) tr ->
    uchain m top pc prev frame k ((if ra =? pc then [] else [ra]) ++ tr).

(* [comment removed for export] *)
Lemma uchain_frame : forall m m' top pc prev frame k tr,
  uchain m top pc prev frame k tr ->
  (forall a, frame - 16 <= a < top -> m' (wa a) = m (wa a)) ->
  uchain m' top pc prev frame k tr.
Proof.
ltac2:(KReplay.run1 (kr_t_ABase ()) [] "p'0h01Hh12H7h21ih32H6h42H5h52H0h62H8h72H9h81ai001ah93H11h:3H10h;3H13h<2Hih=4__x1h>4__x2h?1oh@1zi011zhA2HChB2IHhC7__arithhD3H12hE4__x3hF4cstrhG5cstr0hH2tri022trhI3H15hJ5framei035framehK1ki041khL1ni051nhM4previ064prevhN1BhO3H14hP3Hi0hQ1XhR1YhS4__ffhT8__varmaphU5__withV1li071lhW2HMhX2HahY7__sat12hZ7__sat13h[6frame0h\2k0h]5prev0h^2B1h_2B2h`2H1ha2H2hb2H3hc2H4hd3Hrahe4__p1hf7__sat11hg4__x4hh2fpi082fphi3fp0hj2rai092rahk3ra0hl2GEhm3Hfphn2Hnho2LThp7__sat10hq7__sat14hr1mhs2m'ht2pchu1si0:1shv3tophw3tr0hx1xi0;1xi0<1bi0=1ei0>2z0p%0p&0p;1p;7p;2p;3p;6p;4p;?p;8p;Bp;<g003Xj1ATg00OGk105Tg013=j1|Tg013`R0k10=Tg008@k104Tg014BS00j74Tg004=j1eTg00WZj21Tg015;j1ZTg00?7j33Tg00LfR1j25Tg005QR2j2;Tg00\1j1\Tg015jk700Tg016cj2>Tg00MBk20ETg017CR3j2?Tg017[R4j1:Tg018;j3FTg018Yj2cTg019?j1dTg00PHj2LTg019ok206Tg00>1j2JTg005lj1XTg01:Qj1qTg00noj6Ej8rTg01;Hj4gTg01;oj1MTg0077j2pTg00A<j3wTg006Kk202Tg007`k101Tg00Aej3vTg008`j2uTg009\j4fTg00::k10OTg00:Xk10NTg00;Cj2tTg00;fj2nTg00<mk10MTg0033k10JTg00W7j3mTg00Ndj3}Tg00=Ok20ITg00>Kk20HTg00?Qk30GTg00@0k40FTg00g@j6RTg010Gj4STg01<Tm?0DTg01=Mj20Tg01=jj12Tg01>Kk20BTg001Yj2DTg01?2S01k20ATg009>k10@Tg01?Rj2jTg00_Dj2bTg00L>k20?Tg00M_k30<Tg00NCk20;Tg00<Ik60>Tg00oKj2yTg01@CmB0:Tg01A<m<0CTg01B7j4xTg01Blj3sTg01C\k209Tg01DUm<03Tg00BEj4~Tg00C0k708Tg00CTk707Tg00D\k80KTg000Gk30LTf3R5f2R6'Df1R7f0R8'5';p==1178,56p=Ng00E@R91b78g00K`R:33p=@g00IUR;/?8p=91;78,;6p=o1c78#dp=<g01E:R<P6P7P8Cxp=81D:61578';p=T1D:8p=6%:8,L7p={f4R=1L67#Z9s<5;38p=G1D67/;8p=O1167/L8p=a1L67/D8p=HAs<78p=P1L78#Zp=iAs<67=358p=h209<8p=Y1J98p=Wg01EoR>P9P3P4P1g01FNR?f5R@P=P5P6P7P8N<03p>0P%:8,D:p=VP9P7g00GiP8C~p=`P7g00FJS02g00FiRAPAg00GIS03P8g00HPK08p=BP9P7g00\JP8C~p=[P6Q02PAPAQ03P7P8K07p=lP5Q02PAPAQ03P6P7P8L0Kp=IP<P51167P8Cxp=KA3978p=7A3>78p=C1567/;8p=_P9P=P5P6P7P8ERp=^15:8p=]P>P9P3P4P1P?P;P:P5P6P7P8N<03p=kAv978p=UB0L978p=Q1D:7/;8p=zg00I0R?#AR1#A#AR4#AR3#A#AR<$05RB#|RC&054#|RD$0=RE[PE^xC&049RCf7RFP@P=P5P6P7P8F4f8RGf6RHP@%e3R3,15RIP8P8f;RJC=f=RK%Z7RLO1f>RMPLO153E[^89RNf<ROPJf:RPP=P5P6P7F4[XHCXK>XJ9XM91567S04f9RQ=N73%e4R4,@7%98';S053o#\POPJPPP=P5P6P7K00XWNWnXK>XJ9XM915=5S0611O3S07,5=1@@4S08%9@S09fARN11F3S0:1<B@RR38fBRS11G4S0;;8R%A<#A#A#A#A#A#eRT9THHS0<11J3RUP8P8fCRVC=fERWPLO1fFRXPLO153E[^89fDRYPVPSPOPJPPPQPGPFPHP@P=P2%6U1<BQS0=,>DS0>,{U%e1RU%e<S0?+0ER<1<BPRZ,>D,?8PEfGR[11K3R\%:7R]1<BJS0@=FD7DG[^2>3OQ07=8WZP5%6\1<BO,>DS0A#:S0B9aM31<BKR^,>DR_,?8S0CPEfJR`f@Ra/13RbP]1<BMRc=FD7S0DDG[^2>7O<P2f?Rd/13Re%:_;H<S0E1>DcR_,?8PEfKRf11N3RgP]1<BdRh=FD7DG[^2>S0FfIRi?8bcS0GP81>Dh#:S0H=Hg<1<BNRh,>DRc,?8RbPEfNRj11Y3S0IP]1cBSS0J#dRk=FD7RlDG[^2>S0K11V3Rm#6%:c=Hm<S0L1>DkS0M,?8Rm11W3S0N/L]Rc#ZRn,PjRo1cBVRp#dRq=FD7Rr53E[^2>Rs';P@Q0LPsP7PEfORs/PnRtPEPs11X3%:6Ru'iRvP8ChX?EPEPsPnO1RwP0PDPEP8206D8Rx%YvRyn10110;00021010<00P0PDPEfPRzPvO1PxPyn10110;00021010<0053EX?EP0PDPEPwPx%Ynn10110;00021010<00,JEPjPnO1PPPcP>1>DqS0O1?68XL>S0PP8%X;Rq#XRc#XS0Q#X#X#X#X#XRn%qpEE1?7nS0R1?6n15u4RpP6Pu%WuPnP4%W4J0PP8CgS0SPp%M5S0T%V5S0U1cBXS0V#dRw,>DRy#M%Vyg00E^Rv1p9c1p9q1p9;5w9S0W5w9g00J4S0X+02&01vS0Y3vS0Z&04vS0[P91u96S0\P71u95S0]CfS0^&0O9S0_&0N9R;1t9:1n91R1'`,B;S0`&0MARqP;1t94S0a,[1,B;S0bPqP;1n9?Rc&0J?S0c,n9R?1t93R{5m9'[,B;S0dPqAm9c{R|A}9|1R}'`,B;1[}?,B;5l;CICICIQ03-0I;S0eP8P6g00J`R}g00K@R~'J20H86=3}~dB0G9:7H0FS0fbSbTbUX=9X>9XE9S0g%67S0h1564S0iAN6=3S0jPI1LI=R~P~P@C=[[[^=9^>9^E9S0kP8fRR~%:HS0lP`P6P5PWO6S0mbCbGbFbPb<O2ERA3EotePrP6P7P8O2S0nEEX<mX2>CSCSWNWRP7P8O2n200110000012110710=W8WQP7P8O2n2001100000121107100P211J4Ro#61<BG,>D,{oQ0>,?8PEP[11K4RoP]AFDZ7DG[^2>7O<PWPOP4Q0=CKP6%6oQ0@,>D#:9aM4Q0A,?8PEP`11a4RoP]AFD^7DG[^2>7O<P211d4S0AQ0B;H<S0BQ0CPEPf11N4RZP]Q0DDG[^2>S0CA8io^S0DP8%:_=HZ<1<Ba,>DR_,?8PEPj11Y4S0@P]AFDh7DG[^2>S0=11V4Ro#6%:_S0>=Ho<S0o11W4S0p/L]S0q#ZRo,PjS0r=3El\b^2>R_';P@Q0oP_P7PE1PsoR_PEPs11X4/iuR^P8ChX?EPEPsPoO1S0sP0PDPEP8Px%Y^S0tn10110;00021010<00P0PDPEPzP^O1PxQ0tn10110;00021010<0053EX?EP0PDPEQ0sPx%Yon10110;00021010<00,JEPjPoO1PPQ0qP>Q0MQ0PP8PnQ0J#qEEQ0RQ0SPpQ0TQ0U1<BWS0J,>DRo#M%:oS0q#6Q0ZQ0[Q0^Q0_P;Q0`PqP;Q0bPqP;Q0dPqQ0a9m9c=}91R^,`|,B;1[^?,B;5l;CICICIQ0eQ0fbSbTbUX=9X>9XE9S0aQ0hQ0iQ0jPIAa54=R^P^P@C=[[[^=9^>9^E9S0hQ0mbCbGbFbPb<O2ERQ0r=3E_ePlQ0nEEX<bX2>CSCSWNWRP7P8O2n2001000000121000000W0WQP7P8O2n2001000000121000000P7N?0DWWWdW_W^WcWbWaW`Xj9Xh9XK>XJ9XM915@=S0r15@\1@H4S0m%9HS0i11G3S0j1<BHS0d58S11Q4S0bQ0d58VPTPFPFP<C=S0`ATQQ<S0^PXPYPVPOPPP}P>10QVPJ%2JS0Zn0100000020000PGF4Q07P8P8PXC=fHR\PLO1PiPLO1R^53E[^89P[PXPWPMPOP}P>10JWPK%2Kn0100000020000PPF4[PeP8P8P[C=P`PLO193E^[^89P\P[PXPaPdPMPKPOPJPPPQPGPFP2%6eQ0EQ0F';Q0GPH%6gQ0>9aS3Q0K7O<P2Q0LA3Etr\m^2>fMRmQ0I;8kP8Q0NQ0O#:;H<1?8oRoPEP~11\3S0NP]AFDw7S0ODG[^2>11[3Rk#6Q0q=Hk<Rk1?8yS0qAai3]S0I#ZRt,P~S0L1cB[S0K#dRr=FD7S0>53E[^2>Re';P@PkPeP7Q0qPEfSRe/PtS0GPEPe11`3/iuRkP8ChX?EPEPePtO1S0FP0PDPEP8Px%YkS0En10110;00021010<00P0PDPEfTR^PkO1PxQ0En10110;00021010<0053EX?EP0PDPEQ0FPx%Ytn10110;00021010<00,JEP~PtO1PPQ0IP>1>DrQ0PP8PnQ0K#qEEQ0RQ0SPpQ0TQ0U1<B`S0K,>DRt#M%VtQ0gQ0kP8fVRtQ0lPjP6P5P\O6RkbCbGbFbPb<O2ERQ0LQ0G53EeQ0>Q0nEEW<X2>CSCSWNWRP7P8O2n2001000000121000000W0WQP7P8O2n2001000000121000000P2Q0A#6Q0BQ0C';Q0DP@%6ZQ0H9aS4Q0=7O<P2Q0oA3E_l\b^2>Q0@=8mhP8Q0pQ0M#:;H<1<BY,>DRh,?8PEP~11\4P]Q0J=FD7DG[^2>11[4Rb#6%:h=Hb<Rb11i4Rh/L]R]#ZR_,P~RlQ0O53E\o^2>R2';P@PbP2P7PE1Pe_R2PEPe11`4/iuRuP8ChX?EPEPeP_O1RbP0PDPEP8Px%YuRZn10110;00021010<00P0PDPEP^PuO1PxPZn10110;00021010<0053EX?EP0PDPEPbPx%Y_n10110;00021010<00,JEP~P_O1PPP]P>PyQ0PP8PnQ0V#qEEQ0RQ0SPpQ0TQ0U1<BiS0U,>DRD#M%VDQ0aQ0hPkbCbGbFbPb<O2ERA3El2eQ0OQ0nEEX<oX2>CSCSWNWRP7P8O2n2001000000121000000W0WQP7P8O2n2001000000121000000P=P520BdK15dK1DKd+0AQ0115aM1DMaP`PiP\PNPdP}P>10M\Pa%2an0100000020000PKF4P815NdP=PgP8P8PfC=P@P7Q0Q,p9Q0W5w9Q0X+02Q0Y5vvQ0[P9P9&0@9S0XP61u9=CfP7Q0]CfQ0_P;Q0c#A,n9S0c=m9{/`1,B;1[1?,B;R?5l;PqP;Q0c,[c,B;Pq1`|1,B;=l;?CICIQ0eQ0fbSbTbUX=9X>9XE9Xg9PIP7P7P6C=157=1163P5P5P=C=[[^=9^>9^E9^g9P8PVPmP6PWP7P5O6bCO2WXX89O1WoP8O11DdNQ00fLRIP`Pi17=[17=XP}P>10XzP\%2\n0100000020000,C=A3C=XP^PeP~PfPiP}P>10\~P`%2`n0100000020000P[F4[[[[P@Q04fQR?=N73Q053o#\175`175iP}P>10iePf%2fn0100000020000,C5&019R|=3Ci17FjP817GsPz17QsRcP}P>fYR{,0sP?%2?n0100000020000,CQRvA3C|sf\Rg/13Ro1@O4%9J';5_O9_5O#\f^R2f]RlPgfURkPeP}P>10~gP^%2^n0100000020000P?F4]0]1]3]4X@917GjP8PcPzP}P>fZRc,0zP~%2~n0100000020000,CPRgA3C|zRD11l31@64%9O';5_69_k6#\f_RpP2PlPtP^P}P>10elPk%2kn0100000020000RlP~F4]0]1]3X@9P8PgP>P}P>f[Rg,0?Pe%2en0100000020000A3C|?Rn15t^RyAN^23R]1@^4R_%97';3o#\f`RxPpP2fWRbPkP}P>10^2Pt%2tn0100000020000R^PeF4]0]1XL>P8PnPCP|11p31@k4%9^';5_k9_bk#\faRnPxPpfXR0PtP}P>10kpPb%2bn0100000020000RZP7F4]0XVC%9l,;_9oy]#\PCP|fbR]PxPpP0PtPZP8F41103P8P8P]C=fdS05PLO1RZfeRyPLO153E[^89fcR_P]PnPcP0P}P>10bnP{%2{n0100000020000RlP6F4[P_P]PnPcP0PlP|F4]B]AXHCPnPpP2PbPkP^P|F411b3P8P8PnC=P_PLO1=3EZ[^89P]PnPxP{PbP}P>10txP0%20n0100000020000R0P|F4[P]PnPxP{PbP0P6K00WBWAPeP6P`PiGrW0P~P8EEb0X1DPJP8ERb0X3vPPP8D^b0W4PQP8D^b0W5P5P6P7P8P=O5W1W3W4W5W0X\>X[9X]9P5P6P7P8O4Q0615=oQ08Q09Q0:=8nRQ0;=8]RQ0<17Jc17J{P}P>10{_Pg%2gn0100000020000,CJA3C|{17d2P817apPx17NpR{P}P>fiRg,0pPn%2nn0100000020000S0;,CNS0:A3C|p155YfmRc/13S04,5W1@X4%9XfrRRQ0N;8wfsRo?8hwAT[[TftRhPoPRfkRwPgP}P>fhRv/0RfjRD%2Dn0100000020000fgR0F4]7]6]1]3]4]5]0];]D]9X@917a2P8P{PxP}P>10xDP]%2]n0100000020000,CSR{A3C|xS0N15y6fnS00/13S0],551@=4S0W%9[11H3S0Q=8or11F4S01=8hrAT\\TfuRrPhPoflR2PDP}P>10goPw%2wn0100000020000PvF4]7]6]1]3]4]5]0];]DX@9Q0:P8P{P>P}P>10nwP_%2_n0100000020000A3C|nRnffR_Q05'5S0nfoR{/13S0O,5yS0h1@_4S0a%9=S0TPhPvP31<B\RbCKS0SPrPgP4PbCKS0RATiiTS0VfvRbPrPhPcPwP}P>10DhP2%22n0100000020000S0PPgF4]7]6]1]3]4]5]0];XL>Q0NP8PnPCP|150yfpRn=N_31@04P}P>fqRt,00Pg%2gn0100000020000S0J#9PrPgP3Q0UCKPbPDP4Q0UCKAT``TfwRZPbPrQ00P2P}P>10wrPc%2cn0100000020000R^PFF4]7]6]1]3]4]5]0XVCQ0nQ0hQ0aP}P>10_nPv%2vn0100000020000S0p#9Q0SQ0RQ0VPCP|fxRkPbPrQ00P2P^P8F4Q0]P8P8PkC=fzR^PLO1S0Mf{RlPLO153E[^89fyRuPkPZPnQ00P}P>10cZP{%2{n0100000020000S0@P6F4[PuPkPZPnQ00Q0@P|F4]B]AXHCPZPrPhPcPwQ0PP|F4Q04P8P8PZC=PuPLO1Q0M53E[^89PkPZPbP{PcP}P>102bQ00Q00#2n0100000020000S00P|F4S0M[Q0MQ00#9S04Q00#:S0P#]S0o1J9:S0=Q00Q0PQ0P#WCkP@CgQ0o%9{%:{S0o#]S0PQ0=P{Q0oQ0o#WCkPvCgQ0P%Mn%VnP}P>10{uPt%2tn0100000020000S0P#MQ0P#V1jo4%6o%64S0P1br4#6[[Q0?-0?US0o%]US00Q0?#6%]<[S0H[S0D%6US0Cg00PeS0BQ0?>0<U7UWXS0?Q0CQ0B%6<[]XS0C1jh4%6hQ0P1bb4#6[[P6g00QA20;:U'JQ00eO1S00Q0Hp-0RUQ0YQ0[P9P9Q0XP7Q0\CfP6Q0XCfQ0_P;Q0c,[1,B;PqP;Q0c/`1,B;PqP;Q02PAPAQ03P=J0>CICIQ0eQ0fbSbTbUX=9X>9WeS0f15871D67P=[[^=9^>9^eUS0eP8g00]1S03PZPuPSP0O5bCbYbpbfbYbZbGbFb1b1'yWBWAPgPGPxPpGrW7W6W1W3W4W5W0P]P8EEb0W;PVP8ERb0WDPSP8D^b0W9PNP8D^b0W:P5P6P7P8PPPQPGPFPHP@P=O;W;WDW9W:W7W6W1W3W4W5W0Xk9Xi9X\>X[9X]9PJPPPQPGPFPHP@P=P5P6P7P8O<Q0rAN@x3Q0mQ0iQ0jQ0d58yQ0bQ0d58_Q0`Q0^PgP0P_POPPP}P>10Q_PJQ0Zn0100000020000PGF417Mx17MpQ0;,CMP}PC10KDP|1UK|n0100000020000/QO=3CpQ05,7SP817VyP_17YyRpP}P>10y{P0%20n0100000020000,CYRxP}PC10VnP|1UV|n0100000020000/QS=3Cy155[AN\o31@i4%9iPkPfP3Q0UCKPuPIP4Q0UCKPTP`P`P<C=15I<Ry,zIf|RgP^PuPsPmP}P>10IuPj%2jn0100000020000PfF4PgPlP^PoPtP}P>10n^PR%2Rn0100000020000P{F4]9]:]7]6]1]3]4]5]0]I]O];X@9Q05,7VP8PpP_Q0p,CWRpP}PC10YtP|1UY|n0100000020000/QV=3C_R_15w6AN5h3Q0W%9`Q0QQ0K58uQ01Q0K58^PTPfPfP<C=15m<R],zmf}RUPlP^PPPjP}P>10m^Ps%2sn0100000020000PIF4PUPgPlPhPRP}P>10tlPo%2on0100000020000RAPnF4]9]:]7]6]1]3]4]5]0]I]OX@9P8PpP>Q0JP}PC10WRP|1UW|n0100000020000/QY=3C0S0J152DRD11r3S0W,5wRp1@24R;Q0TQ0]1<BfRf58^R^PlP{P4PfCKRfAOTIyRyATjj<Rqf~R1PgPlPRPsP}P>10jlS0]PQ%2Qn0100000020000PmF4P1PUPgPrPoP}P>10RgPh%2hn0100000020000R:PtF4]9]:]7]6]1]3]4]5]0]IXL>P8Q0JPCP}PC10XoP|1UX|n0100000020000/QW15cw11b3R3,521@c4Q0@#9Q0O1<BIRI58lPgPnP4PICKAOTm]ATss<p+01@R<PUPgPoPzP}P>10sgR]P:%2:n0100000020000PjF4P<P1PUPbPhP}P>10oUPr%2rn0100000020000RTPQF4]9]:]7]6]1]3]4]5]0XVCQ04P1PgPlPRPsP}P>Q0]PA%2An0100000020000PmF4PCP}PCP]P|1Us|n0100000020000/QjRjp+01AR]P1PUPbPhPTP8F4P3P8P8P]C=p+01CPLO1R3p+01DPLO153E[^89p+01BRTP]P<PkPbP}P>10r<PZ%2Zn0100000020000RmP6F4[PTP]P<PkPbPmP}PC10~<P|1U~|n0100000020000/Q?F4]B]AXHCP<PUPgPrPoP:PjF4Q0WP8P8P<C=PTPLO1=3E3[^89P]P<P1PZPrP}P>10h1Pb%2bn0100000020000RbP}PC10?1P|1U?|n0100000020000/QzF4Rz[%9b%:bR|#]RhQ0=PbP|%W|CkPFCgPh%9Z%:ZRh#]R|Q0=PZPh%WhCkPnCgP|%Mk%VkP}P>10ZTPu%2un0100000020000Ru#M%Vu1jl4%6lQ0P1bU4#6[[Q0oQ0DQ0?Q0C1jg4%6gQ0P1b14#6[[Q00Q0HQ0fQ0eP8Q03P<PTPYP{O5bCbZbfbYbZbqbGbFb1b1,yzWBWAPtPPPvP0GrW9X:qX7yX6fX1^W3X4;X5pX0DPvP8EEb0XI_PXP8ERb0XOxPWP8D^b0W;PYP8D^b0WDP5P6P7P8POPJPPPQPGPFPHP@P=O=WIWOW;WDW9W:W7W6W1W3W4W5W0XwCXk9Xi9X\>X[9X]9PMPKPOPJPPPQPGPFPHP@P=P5P6P7P8O?n3000510110>105107000000341106103104000<1106103104108109000000000000000000000?1106103104108109102000000000000000000000000000175X175WP}P>10WsP[%2[n0100000020000,C5A3C5WPeP~P?P`P\P}P>10[?Pi%2in0100000020000PXF4[[[[XVCXL>X@9X@9PSPaP}P>10diPN%2Nn0100000020000PMO4P8%WV%WNP}P>10a`PS%2Sn0100000020000,J>1JCdO4b0WlP8O1n200110:00021110711107buNB0:WWWBWAWmWdW_W^WcWbWaW`XHCXj9Xh9XK>XJ9XM9P=P5P6P7P8N<0CW0WHXK>XJ9XM9Xt9Xv9WsWro"). Qed.


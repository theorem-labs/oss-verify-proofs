(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_fa_iface AF_huf_w4s_iface AF_huf_w4e.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4m.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_dec4x1A () := "I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6to_natK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C5ARocqVerifyHarness?AgentSubmission5Plain<RF_huf_iface8x1_bytesC47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3minK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3minC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z8min_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit29x1_bytes'C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2@x1_bytes'_lengthC47Corelib4Init5Logic8eq_ind_rC47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List=length_firstnK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula06I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2InI5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<AMallocIface00C5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_w4s_iface=w4_slow_stmtAC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fa_iface?fast_args_stmtAC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02C47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface7x1_tabAC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface7src_inAC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<harness_invAC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_cell_okC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangec5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_dec4x1A:w4_tab_lenC46Stdlib6ZArith:ZArith_dec8Z_lt_decI47Corelib4Init6Specif7sumbool00K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic3and01C47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_w4s_iface<w4_slow_goalC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4e8w4_entryC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface>dec4_int_stmtAC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00I5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface?HUF_DEC_STACK_AC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface;AHUF_DX1_4XC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1:x1_defaultI47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Lemma w4_tab_len : forall (cells : list deltX1) tl mtl, zlen cells = 2^(mtl+1) -> 0 <= tl <= mtl + 1 -> 0 <= mtl ->
  zlen (firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells)) = 2 * 2^tl.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_dec4x1A ()) [] "h04__p1h14__x1h24cstrh37__arithh44__ffh58__varmaph65__with74__x2h81xh94__p2h:4__x3h;4__x4h<4__x5h=1nh>1Hh?2H0h@2H1hA2H2hB2LChC1MhD1ThE5cellshF3mtlhG2tlhH1yhI2z1hJ2z2p&0p;1p;2p;4p;3p;5p;<p;6p;7p;8p;Bg0000j1aTg000PR0j16Tg0010j1RTg001Uj1bTg0023j2ATg002Pj27Tg002mj25Tg003Ij24Tg003dR1j23Tg004AR2j1PTg004ak109Tg005?k107Tg005bk102Tg006bj2NTg007Bj2QTg007Yj1:Tg0088j2\Tg008Oj1TTg0094j1rTg009Tj1pTg00:2j1oTg00:Pj1nTg00;;j2UTg00;^j4MTg00<Ij2iTg00<kj2GTg00=Ej2fTg00>1j3Ik101Tg00>Kj3eTg00>jj4dTg00?\j2<Tg00@8j2HTg00@Vj4JTg00A4j2FTg00AWj3cTg00B:k108Tg00B\k506Tg00CCk405Tg00Ckj2OTg00DHR3j2VTg00Dek100Tg00ECl<xTg00Ehj2tTg00FJj2LTg00Fdj2sTg00GFj1[Tg00Gdj2WTg00HEj3DTg00Hnj2ZTg00IWj2qTg00J@j3ETg00Jij2STg00KUj1YTg00L:j3XTg00L]j4uTg00MHj1vTg00NIj1wTg00OQj6^Tg00Ooj3mTg00PNj3lTg00Q0j7kTg00QTj6{Tg00R8j7|Tg00R\j8jTg00S@l<_Tg00SelB`Tg00TKj3hTg00U4k203Tg00U`k304Tg00V@j7gTg00VdR4f0R5'Np=>g00WdR6f1R7;I5p=2g00XBR8/55p=9P7g00X`R9g00Y?R:P:g00Y_R;P5g00Z?Fkp=1P7P9P:P:P;P5E{p=KP6P7g00Z_P5CMp=Cf2R<P9P:P:P;P7P5F|p=Bf3R=P9P:P:P;P<P7P5Gjp=8P6g00[FR>P6P6P2f4R2P0P=g00[eP<P7P5M<_p=~P>P>P>P6P6P6g00\RP0P0P0P1g00]2f5R1P2P=P<P7P5MB`p=}P>P>P>P6P6P6g00]UP0P0P0P3g00^5P1P2P=P<P7P5MB`p=zP>P6P6P6P0P0P1P2P=P<P7P5M<_p=y1Z65p==Ah675p=0g00^X-035p=@g00_DR0@0475p=;P6P7g00`0P5CMp=?P<P9P:P:P;P7P5Fgp=]%a4%><#6g00`WR4#RR9#bR3%b4R?,A5'7'2%9<R@1A7?RA,5<'4P>1732RB,33#PRC%R9RD#R$09$07RE&021RF'N'Q%65RG1731RH,33RI'2X=>P>g00a<RJ#:RK#:RL%>1RM'\%PI/Q5#6/2IX=>P3P21A=?RI%TMRN%6M#9RM%r0RO%a0R0%p6RP%o6RQ%n6RRP61U68RSg00a[RT1U63RUCM'11iR;R;P5P<g00bBRVg00bbRW'G1f5<=IVWdAe687CdRWb4b5b61<83P5b3RVb2PNPMp-0RMPOP0P61H6<P7PPCJPQPR1KR21F64RN1F69RX1U6?5c6'C,1RRY5BR&08:R:PYC8P;PWb4b5b6X16X76W0155A,4<1A<?,57[^16^76^0MP5f6RA#9P1PAP=O4b3b2I06173I,5BP3P1%>ARB#TRI%6B#9RBPVb2PIPBPOP01H67PQPR1CSN,1RRB1KR=5BRP:PBC8P;PWb4b5b6X16X0M%95/47%97[^16^0MP5f7RB1AA?'5PBP2O3b3b2H051<8H173A,33RH#PRI%>BRV,\LRY'QRZ#6R[/2H1O8HR\%6VR],33R^'VR_/2HP6P6&016R`P5X86RaP`1275$00XH6X86P[P_PaPa1G6GX8>PZP_PIP\Pa1O85X86PHPH1G6HRaD~PYP^PLP31G63PVP]1G6]E}EzEyPHPHPaM<x%TV%9]173B,33R],t81<8]1O8]RV/2]'415]8AI6V8'4'Lf8RV,73,33,O8P6f:R]#>#6,33Ra,s51<5a1V5aRH/25'415a512Ha'4'Lf;RH#>#6,33,V7P6%[4,W6Ra%:LR^#:#:RY#:R\#:RI#=R_5D6%[9,W6R9%=KRK5D61Z6JRJ'0RZ'01q63R>=E6JRG%=YRY9E6>%=LRL9E6>'0,0_'0#@'S%=\R\%=^R^9E6>'0#@R_AE6>K/0J,0\%:I#=AD69L,0\'0,0G#@'SAD6a\RG/0Z10J^#@'SAD6aY/0J,0G#@10YJ,0\#@1;_O,;_';';';';';';P0P6P61H62P<PPCJP7P6PPP=1H61CJCJPQPR1KRB%Y4R4#Y,F6RQ,?N,1R5BR1F64R49X6URP/CQ,1R1?NP,1R5BR5]RP:PR1KRVAX6UXRU,?Q,1R5BR1CUS,1R1?QS,1R5BR5]RP:PR1CS4,1RP:PRP6PSPTPXCM,1RP:PR1F6DRD,CX,1RP:PR1?4D,1RP:1?NU,1RC8C8C8C8C8C8P;PWb4b5b6X16X76X:6X;6X<6X0MX9M1252,41133<RW/52125W'4'L121W,4B15W8AI618'4'L%921<82151B12BV133B,2A[[[[[[^16^76^:6^;6^<6^0M^9MP5f<,73R5,33,<8f=#>#6R8,33,<=P=1AH?,73P8P5P7P<P2P1PAPBP]O=b3bJbAbIb@b2Cub?b>%v1,NE%w1E^AmECF,NEAlECFE^XC@WDWBXF6XG6WEo"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Definition w4_fast_stmtA : Prop :=
  forall (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region),
  AHEAP AI L RNG st LB m0 ->
  (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  1 <= mtl <= 12 -> tl <= mtl + 1 -> In (HB pdt DT (DTABLE_BYTES mtl)) LB ->
  x1_table_ok cells tl -> cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells) -> zlen cbs = 2 * 2^tl ->
  ((DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB)) -> 0 <= dcap < 2^32 ->
  Forall (fun c => 0 <= c < 256) src -> zlen src < 2^26 -> 16 <= SS ->
  (0 < zlen src -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= SS /\ SS + zlen src <= SBH) ->
  (DT + DTABLE_BYTES mtl <= SS \/ SS + zlen src <= DT) -> (DST + dcap <= SS \/ SS + zlen src <= DST) ->
  (DT + DTABLE_BYTES mtl <= DST \/ DST + dcap <= DT) ->
  ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HUF_DEC_STACK_A -> bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP -> harness_invA m0 ->
  rclean m0 rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk -> rrng RNG rstk ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
  w4fa_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs.

Theorem dec_4x1_proofA : forall (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop),
  w4_slow_stmtA -> fast_args_stmtA -> w4_fast_stmtA -> dec4_int_stmtA AI rng_fs x1_tabA AHUF_DX1_4X.
Proof.
  intros AI rng_fs SLW FAP FST. unfold dec4_int_stmtA.
  intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB
    DST dcap S DT mtl flags pdt src lo rstk AH NFK ABL MTL HDT TAB DSTF DC SRC BYS NSM S16 SIN DJ1 DJ2 DJ3 STK LOA LOS
    RCL RLO RHI RRL SPT SP16 MI TPA FL HINV WSK WIM WIS WFS RRS E0 E1 E2 E3 E4 E5.
  subst a0 a1 a2 a3 a4 a5.
  destruct TAB as (tl & cells & DTH & CL & TOK & TLM & CBS).
  pose proof TOK as (TL1 & _).
  pose proof (w4_tab_len cells tl mtl CL ltac:(lia) ltac:(lia)) as LCB.
  assert (SB : exists SBL SBH, 0 < zlen src -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= S /\ S + zlen src <= SBH).
  { destruct (Z_lt_le_dec 0 (zlen src)) as [P|P].
    - destruct (SIN P) as (p & A & nn & HB1 & A1 & A2). exists A, (A + nn). intros _. exists p.
      replace (A + nn - A) with nn by lia. auto.
    - exists 0, 0. intros P'. lia. }
  destruct SB as (SBL & SBH & SRCB).
  eapply (w4_entry AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m DST dcap S DT mtl tl lo src cells
            (firstn (Z.to_nat (2 * 2 ^ tl)) (x1_bytes cells)) pdt SBL SBH rstk).
  all: first [ eassumption | reflexivity
             | eapply SLW; first [eassumption | reflexivity]
             | eapply FST; first [eassumption | reflexivity]
             | unfold KXGoM.apart; lia ].
Qed.
End CANSEC1.

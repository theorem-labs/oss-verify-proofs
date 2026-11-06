(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W2 ASlot_W8 ASlot_W9 ASlot_W10 ASlot_W12 ASlot_I ASlot_M0 ASlot_M1.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv4.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_M2 () := "I35stdpp9countable9Countable00C35stdpp4base;RelDecisionK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp4base7is_SomeI35stdpp4gmap4gmap00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp;grp_hdr_covC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idI47Corelib4Init9Datatypes4prod00I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic5proj2K47Corelib4Init5Logic3and01C59OSSVerify5KrLib6Malloc9Malloc_fp9unk_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition epi_frame (jj : list byte) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [CB 48 jj; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Section EPI2.
Variables (lo : Z).
Hypothesis CLO : ATOP <= lo.
End EPI2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Let F0 : ISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Variable am_pre : mstate -> Prop.
Hypothesis AMP : AMP_AS am_pre.

Lemma errno_lit2 : errno_addr tp = 107900.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_M2 ()) ["CANSEC1"; "LEVEL"] "h02Hah17__sat13h27__sat15h31ah41Hh52H0h62H1h72H2h82H3h97__arithh:4__ffh;7__sat12h<7__sat14h=8__varmaph>5__with?2tph@1zp;1p;2p;3p;4p;7p;6p10000p4p710R0p1000NR1p4p710p8P0P1p4p7210p8g000gj10Tg001Lj1STg001jj1JTg002Mj11Tg0032j14Tg003Pj2RTg0046j2BTg004`j1ITg005>j2@Tg005[j3>Tg0065j2=Tg006Oj1XTg007Mj1VTg008Cj2<Tg008_R1j29Tg009:j2ETg009bj26Tg00:>j2DTg00:[j3CTg00;?j2QTg00;`j1OTg00<@j1NTg00<`j1MTg00=>j1LTg00=\j1KTg00>Gj2;Tg00>jj4?Tg00?Uj3HTg00@8j7PTg00@\j2GTg00A>j2TTg00Ajj3UTg00BIj4[Tg00C;j2ZTg00D7j6FTg00DUj7YTf0R0#0#0#0#0p=8%00#0p=2%10#0p=7%10#1#1#1p=5%10#1p=W%00#0#0#0#0#0#0#0p=:g00E9R2/<0p=3f1R3g00EWR4g00F6R5P5g00FVR6P0g00G6FYp=Ag00GVR7#0R8#8R9#0R:#SR;#JR<%17R7#0R=#1#2#1R>#7#2#7#8#4R?,R;R@g00H;RA1B;0%18#2#1#2#IRB'@%0>#7#1#5#2#4R>3>X?<PAP?1@0B=>A>X@A1=A>1B;@p,2rcR@#X%17#5#5#5R7#0#1#W#5#7#2#8#:#:#4%V@R@'<%57#5#7#2#8#:#:#4,<@'9%48R8%49R9'E1628R@%391D89R7,62[R>[%38RBg00HYR<AC893UW0%37\<^0B%4:R:,E8%3:1D8:R9,62[RC\@AC8:3V<X0B%39\<^0Bp,2SCp,2scRB#3R<%0=#2#4,6BRB'9P1P<PB%3?16?9'9R9P0p,2RQp,3reqR=#3R:16=7R='9P1P:P=P9P0f;g00I51Q28'=P@eR@O1PCf>P@O1P>g00I[R>#O%N>%MA%LA%KAR>P4P5P5P6PA1;A2g00JG1;A?R5C?,A>PAP5g00Jn1;A8=HA;C?,A>FP1G>6P0f2R>g00KUR6g00L5R;'=1T0>=>6;dAUA23C[b:b=b>P9P0b9b2b1X8=X7:P3P0O2n2001000000121000000b3X6BX5<P3P0O2n2001000000121000000b3b;b1b<b2b4,Z?EFp,2tpp,2TPEFo"). Qed.

(* [comment removed for export] *)
Lemma unk_agree_keep stE mE :
  s_shadow stE = s_shadow st ->
  (forall rid r, r_kind r = RKGroup -> (s_regions stE) !! rid = Some r -> (s_regions st) !! rid = Some r) ->
  (forall b, is_Some ((s_groups stE) !! b) <-> is_Some ((s_groups st) !! b)) ->
  (forall rid r off h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
      cell_read (get_shadow st rid) off = Unknown h -> ~ grp_hdr_cov st rid off -> mE (wa (r_base r + off)) = m (wa (r_base r + off))) ->
  unk_agree stE o mE.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_M2 ()) ["CANSEC1"; "LEVEL"] "p'0h02ghh11Hh21xi001xh32Hch41bh51rh63ridh71hh82mEh93offh:3stEh;2AGh<2EGh=3ERGh>2ESh?3Hbqh@4Hbq1hA3Hc0hB2HfhC2HkhD2HohE4HoffhF2HrhG3Hr0hH2NGhI3NG0hJ1XhK2bqhL1ghM3gh1hN1ihO1op;1p;4p;3p;2p;6p;5g00LUR0p4p70R1p10000p4p710R2p8P1p1000NR3p4p710R4p8P1P3p4p7210R3p8P1g00MJR5p4p710p8P1p100Mcp4p73110R6p8P1g00N5R1p4p710p8p100NIp4p70R7P5p4p741110p8P7g00O>R8p4p710p8P7P1p4p7210p8P7P1p4p73110p8g00OSR7p4p710R9P2p8P9P4p8P9P3p8P9P6p8g000gj15Tg001Lj1ZTg001jj1TTg00Ogj1GTP7j4RTg00PIj1PTg005[j30Tg00QBj1UTP5j4OTg00R9j1KTg00S3j28Tg00SUj4\Tg00T3j6iTg00TTj11Tg00UMj2dTg00Ufj1`Tg00V\j1_Tg009bj2?Tg00WXj2>Tg00XSj1ATg00YMj3@Tg00ZNj1NTg00Zgj1MTg005>j2=Tg00[^j1JTg00\Mj1^Tg00D7j6STg00\ij2]Tg002Mj1[Tg0032j1hTg00]IR5j2ETg00]cj4QTg00^=j4gTg008_R7j2:Tg00^Xj4WTg00_3j3eTP1j6CTP8j2cTg008Cj2VTg00`2j2aTg00`lj5bTg00aGj3YTg00adj3fTg00bAR8g00b_R1f3R6f2R9f1R3f0R4ECp=DP0g00cXR2P6P9P3P4ECp=61c24p=;1V93/:4p=Bg00dO1a93;04p=3P8g00eIR:P6P9P3P4ECp=IP:P:P3g00fBP4Dbp=Hf6R;f5R<P2f4R=P6P9P3EC;04p=7g00H;R>=Y84p=LA0834p=FAf8>4p=21:34,:9p=9AY8>3=084p=<1V=61=34,?9':p=4A0893/:4p=Xg00g:R?g00GVR@#5#5#5RA#5#5#5#Z#T%ZA#T#GRA]2RBP8g00h3RCg00hLRDP:CRRE%P3p,2stRF#PRG30g00hjRH%U4g00ibRI30%G1RJP8PCPDP1CRRKP8PCPDP1CORLP9%K<CD181330PKPLP6%KFRMCD1819RN50JRO[[^51^68P0P8PCP>g00jZRPC\RQP8PCPDP>PPg00k3EiRPP2CRRRP0PQPPP2CORPP4%1=C6#;PRPPP4%1FRQC6#;'d^40%U6=0HIRIg00E9%`=#_,?67B6RH1>F;%A6R073=f7RS=@F<#Nf<RT%MS/=;#JRUO1p,1mRVPUO150A[[[[\O^7>^9>^51^68PKPLP6f9RO#KCD=0JN1>T;?3=0f=R0?@S<#Nf;RNf8RUPSP6P=O4PKPLPUPMCD181S50JPEPG%^:RJPEP8PCPDP:COR:f:RDP4CI'H%ASRC73UPEP:PNPGCI,HJ%AU73O]3XLEPEP:POPGCI,HJ%A;RJ73SP4WJf?RG#PP0ES1>GO?3SJ1>FD?3UC]3eP9O11>FO?3SJA@FDURFP51]8>RJ%G2RCPJPRPPP3PQ1824R:F7RE%L3RM/F0%23RL%[@#5#5#hR@,=LRK,?N7BN39X02,E2X4Jg00kQRWP41FMG1?0K9BL059EX02,E2P5P2PCPJPRPPP9PQP:F7f@RE,<9%29RXf>RYPYPXP@D439X02PWP4PCPJPRPPP=PQP:F7fBRX,<=%2=RZPEPEPZP@D439P7PCPJPRPPP<PQ1823RZF7%L<fCR[%2<R\fAR]P]P\P@D43XPWP4PCPJPRPPPSPQ1826F7%LUfF%2UR6fDRSPSP6P@D43XP7fG,<O%2OR7fER6P6P7P@D4PWP4fI,<N%2TRWfHR7P7PWP@D4P[PRPPP0fQRW#1C6#;PRPPPYPQC6R7#;[PRPPP0PQC6#;PRPPPYfRRY#1C6RQ#;[fMR6P0O1P2A0C7:X22POP<CQCgA0CQ:X22,E2P5P2PRPPPGfSRG#1C6=0C:X22fK9@G6P4PRPPP]fU#1C6=0C:PJPCPJPRPPP3fX#1P:F71FMYfPRY1?YK5BL39X02,E2X4JPXP2PCPJPRPPP[fW#1P:F71<[W%2[R[fORWPWP[P@D439X02P3PCPJPRPPPXfV#1PZF71<XYRY%2XRXfNRZPZPXP@D4R@':P4PYP@P;P<CWCWCQCQW@XM2P3P4O2n2001000000121100000bNO1WEWBP3P4O2n2001000000121000000W1W?P3P4O2n2001000000121000000W1X02P3P4O2n2001000000121100000W1XKJP3P4O2n2001000000121100000W1%NFRFePFPAPV%MD/=O#JRVO1p,1oRF%MN/=D#JO190A4XOAp,2UAPNPDPOPUP9P;P<P3P4O9PEPVO1PTPNPDPOPUP9P;P<P3P4O9ESbIbAbGWHW3XDHXCIWFX7>X9>X51X68Ae<F=eW;W<W=W>X8BX:?P3P4O2W8W:o"). Qed.
End LEVEL.


End CANSEC1.

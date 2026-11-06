(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require MallocKit_A2.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_syscalls F_mm_syscalls MallocRep F_malloc_free MallocTree MallocFacts_B MallocFacts_Bpres.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocKit_B MallocModel_B MallocKit_B2 MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_am_A F_am_K F_am_K2 F_am_C F_am_D F_am_E F_am_F F_am_G F_am_H F_am_P.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_F_alloc_meta () := "c69OSSVerify5KrLib2CJ1A<F_alloc_meta6magreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2CJ3Lib3Mem2waC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8eq_ind_rI47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2CJ1A:MallocTree3memC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2CJ3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A;MallocKit_B;ivs_coveredC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes8list_indC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2CJ3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C69OSSVerify5KrLib2CJ3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module A2 := MallocKit_A2.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition magree (C : Z -> Prop) (m m' : mem) : Prop := forall a, 0 <= a < 2^64 -> ~ C a -> m' (wa a) = m (wa a).

Lemma magree_trans (C1 C2 C3 : Z -> Prop) m1 m2 m3 :
  magree C1 m1 m2 -> magree C2 m2 m3 -> (forall a, C1 a -> C3 a) -> (forall a, C2 a -> C3 a) -> magree C3 m1 m3.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["AC_1"] "h01ah11Xh21Ah31Bh42C1h52C2h62C3h72Hah82Hch92I1h:2I2h;2m1h<2m2h=2m3h>1op;3p;2p;1p;6g0000j34Tg000mj2=Tg001Ij10Tg001nj12Tg002Lj2<Tg002ij2:Tg003Ej28Tg003`j11Tg0049j16Tg004Wj17Tg005:j15Tg005\j13Tg006Nj39Tg006hj6;Tg007FR0p-0[R1g007dR2f5R3f2R4f1R534R6f8R7f0R8O1R9f7R:P5O1[^00P7P5O1\9^00g008\/=8g009:#0R9#2%09#0R9#0#0#0#2'<,:8'8f9P5O1#1%69#7#5R9P7%34R7O1f:f3R;#3O19998X>9f6R9P4P5f<P4O1R<P5P3P;P8O2O1W1%1<eO3P:P7O1P3P4P5f;P4O1R4P5f4R5P;P8O2O1W1%14eO3E;W8W7X00A4:95eW:W9X36W2X=2X<2W;X61X51W4o"). Qed.

Lemma magree_of_munch C W m m' : munch W m m' -> ivs_covered C W -> magree C m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["AC_1"] "p'0h03COVh12Hch22Hah31Wh41xh56__sat1h64__x1h71Ch82C1h93Hinh:2IHh;2MUh<7__arithh=4__ffh>6__sat0h?8__varmaph@5__withA1ahB2a0hC2hihD1lhE2lohF1mhG2m'hH1zi001zi011pp;1p;3p;2p;4p;7p;8p;6g009_j1ATg001Ij16Tg0049j1<Tg004Wj1=Tg005:j1\Tg00:?j3UTg00;6j21Tg000mj20Tg001nj1:Tg002Lj2FTg002ij22Tg003ER0j24Tg003`j13Tg005\j1[Tg00<7j25Tg00=0j1@Tg00=Pj37Tg00>0j4TTg00>Kj4>Tg00>kj7OTg00?Mj2NTg00@7j2MTg00@_j3LTg00ACj2KTg00Adj29Tg00B>j2ITg00B\j1HTg00C:j1GTg00Cej2;Tg00DHj2JTg00Dkj4?Tg00EVj3ETg00F9j7DTg00F]j1CTg00G?j8PTg00Gcj2QTg00HEj2BTg006Nj3RTg00I1j3STg00IPj4ZTg00JBj2YTg006hj6XTg0000j3VTg00K=j7WTf1R1g00KaR2g00L@R3P3g00L`R4f0R5g00M@FWp=8g007FR6p-0[g00M`R7#AR8g009:R9#6R:#6#6R;#6#6#6R<#<R=#=%<;#=#\[R;f2R>?U15f4R?f3R@'1g008\RA/05%::R:%:<R<'FRB,25'4RCf7RDP1O1#3P?%[>REP6P>f8RF/55XH6P7f9RG/15f:RHP?O1#3f5RI,5>]1]0X38g00NURJPGP@O1#3RKg00O1W1W0%@7RL,1F15L?^1K]0eg00OMP6P6f;RK/15f<RLf6RMO1#315>D]1]0A77>1,1Lf=PDO1#3A77?@/5F]1]0[^D8P5f>/15f?RNPGO1#315>H]1]010?5125@'4fAROP1O1[^4611N1'4f@RPPHO1#3RHP010M5125I'4fCP1O1[^4611O@10ML12LI'4#315?L'4P110F5125D'4fEP1O1[^46fD/1M10GN12NF'4RF#3RG15DNPIP>PPP5O2O1X9FPGePMP5P?O2CTW0W8P1P5O2n2001000000120000000W1W0P6P6P@P>C>=771,1NP6P6PIP?C>=77@/5K^1H]0eW:X38XC6XE6P1P5O2n2001101000120100100XB7PDP@P5FO1N=E1M:<12A:RE10A<12AB[RD[10A:R7AL:<1VJW210AB\J^27P1g00Om1KA:'9PEeO1PDg00PSRD#@%AD1I61%H6%G6RDP2P3P3P4PDP2P3P3P4P61;6Ag00Q?1J69R9C?,8DP6P9g00Qf1;6:=E6=C?,8DFDR=%C3P=GP1QD4P5P>g00RMRDg00RmR4'91B5>=RD4dAS6A1CZb=b?b@X6610A1121B'4\C^66P5PMPIO2b<b5b>b5,Y>EXO2W1W2XA6AVI@>eW0W;XG;WFW3W7o"). Qed.

Section ASM.
Variables (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : AMpre st.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - AM_STACK.
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis KH : forall st1 mo s' ms',
     am_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     implT o (k st1 mo) s' Q ms'.

Definition FP (stX : mstate) (a : Z) : Prop := alloc_fp (fun k => k <> RKGroup) stX lo (bv_unsigned sp) a \/ fresh_addr st a.

End ASM.

End AC_1.

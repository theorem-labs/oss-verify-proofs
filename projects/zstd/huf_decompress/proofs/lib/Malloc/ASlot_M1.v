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
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_I ASlot_M0.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv4.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_M1 () := "C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframeEget_meta_rec_upd_sameC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section TASLOT.
Variables (st0 st stX : mstate) (LB : list block) (sc req : Z) (g : aptr) (k : Z).
Let mr := get_meta_rec stX g.
Let msk := m_avail mr.
Let st' := upd_meta g (m_set_avail (msk - lowbit msk)) stX.
Hypothesis F : ISTF st LB.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TR : ta_rel sc st stX.
Hypothesis HA : active stX sc = Some g.
Hypothesis GM : gmf st sc g.
Hypothesis MSK : 0 < msk < 2^32.
Hypothesis K0 : 0 <= k < 32.
Hypothesis LBK : lowbit msk = 2 ^ k.

Lemma rec_st' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_M1 ()) ["CANSEC1"; "TASLOT"] "h01mh11zp;1p;2p;3p;6p10000p4p70g000eR0p4p710p8g001Cj1<Tg002:j23Tg002Wj21Tg003Tj22j15Tg004Pj1;Tg0055j1:Tg005Sj27Tg0060j30Tg006Jj26TP0j64Tg006dj38Tg007]j39Tg008oR0p,3mskR1%<1R2'3R3p,3stXR4p,1gR5'1R6'2f0R7g009f#;#:p,1k'7R8,31p,2mr'2R9500X00g00:KR:P81317/26=009X1:1609P2p,3LBKE4%53R3=854/15A9453E4p,3st'/15=009eo"). Qed.
End TASLOT.

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

Lemma errno_lit : errno_addr tp = 107900.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_M1 ()) ["CANSEC1"; "LEVEL"] "h02Hah17__sat13h27__sat15h31ah41Hh52H0h62H1h72H2h82H3h97__arithh:4__ffh;7__sat12h<7__sat14h=8__varmaph>5__with?2tph@1zp;1p;2p;3p;4p;7p;6g004Pj10Tg00:ij1STg00;Gj1JTg00;jj11Tg0055j14Tg00<Oj2RTg00=5j2BTg00=_j1ITg00>=j2@Tg0060j3>Tg006Jj2=Tg00>Zj1XTg00?Xj1VTg00@Nj2<Tg00@jR0j29Tg00AEj2ETg00Amj26Tg005Sj2DTg00BIj3CTg00Bmj2QTg00CNj1OTg00Cnj1NTg00DNj1MTg00Dlj1LTg00EJj1KTg00F5j2;Tg00FXj4?Tg00GCj3HTg00Gfj7PTg00HJj2GTg00Hlj2TTg00IXj3UTg00J7j4[Tg00Jij2ZTg000ej6FTg00Kej7YTf0R1#0#0#0#0p=8%01#0p=2%11#0p=7%11#1#1#1p=5%11#1p=W%01#0#0#0#0#0#0#0p=:g00LIR2/<1p=3f1R3g00LgR4g00MFR5P5g00MfR6P1g00NFFYp=Ag009fR7#0R8#8R9#0R:#SR;#JR<%17R7#0R=#1#2#1R>#7#2#7#8#4R?,R;R@g00:KRA1B;1%18#2#1#2#IRB'@%0>#7#1#5#2#4R>3>X?<PAP?1@1B=>A>X@A1=A>1B;@p,2rcR@#X%17#5#5#5R7#0#1#W#5#7#2#8#:#:#4%V@R@'<%57#5#7#2#8#:#:#4,<@'9%48R8%49R9'E1628R@%391D89R7,62[R>[%38RBg00NfR<AC893UW0%37\<^0B%4:R:,E8%3:1D8:R9,62[RC\@AC8:3V<X0B%39\<^0Bp,2SCp,2scRB#3R<%0=#2#4,6BRB'9P0P<PB%3?16?9'9R9P1p,2RQp,3reqR=#3R:16=7R='9P0P:P=P9P1f;g00OB1Q28'=P@eR@O1PCf>P@O1P>g00OhR>#O%N>%MA%LA%KAR>P4P5P5P6PA1;A2g00PT1;A?R5C?,A>PAP5g00Q;1;A8=HA;C?,A>FP1G>6P1f2R>g00QbR6g00RBR;'=1T1>=>6;dAUA23C[b:b=b>P9P1b9b2b1X8=X7:P3P1O2n2001000000121000000b3X6BX5<P3P1O2n2001000000121000000b3b;b1b<b2b4,Z?EFp,2tpp,2TPEFo"). Qed.
End LEVEL.


End CANSEC1.

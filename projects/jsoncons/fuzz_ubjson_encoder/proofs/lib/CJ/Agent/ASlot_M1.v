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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_I ASlot_M0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require MallocFacts_inv4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ASlot_M1 () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6lowbitC13~~~C56Stdlib6ZArith6BinInt1Z3subC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;m_set_availC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8eq_ind_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8upd_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent@F_malloc_enframeEget_meta_rec_upd_sameC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z7compareI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:F_syscalls5asegsC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section TASLOT.
Variables (st0 st stX : mstate) (LB : list block) (sc req : Z) (g : aptr) (k : Z).
Let mr := get_meta_rec stX g.
Let msk := m_avail mr.
Let st' := upd_meta g (m_set_avail (msk - lowbit msk)) stX.
(* [comment removed for export] *)
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
ltac2:(KReplay.run1 (kr_t_ASlot_M1 ()) ["CEIL_WRAP_1"; "TASLOT"] "h01mh11zp;1p;2p;3p;6g0000j1<Tg001@j23Tg001]j21Tg0033j22j15Tg004Hj1;Tg004mj1:Tg005Kj27Tg005hj30Tg006Bj26Tg006\j64Tg007:j38Tg008Lj39Tg00:6R0p,3mskR1%<1R2'3R3p,3stXR4p,1gR5'1R6'2f0R7g00;F#;#:p,1k'7R8,31p,2mr'2R9500X00g00;kR:P81317/26=009X1:1609P2p,3LBKE4%53R3=854/15A9453E4p,3st'/15=009eo"). Qed.
(* [comment removed for export] *)
End TASLOT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
(* [comment removed for export] *)
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
(* [comment removed for export] *)
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
(* [comment removed for export] *)
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma errno_lit : errno_addr tp = 107900.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_M1 ()) ["CEIL_WRAP_1"; "LEVEL"] "h02Hah13ERRh27__sat13h37__sat15h41ah51Hh62H0h72H1h82H2h97__arithh:4__ffh;7__sat12h<7__sat14h=8__varmaph>5__with?2tph@1zp;1p;2p;3p;4p;7p;6g004Hj13Tg00<Ij1VTg00<gj1GTg00=Jj10Tg004mj14Tg00=oj2UTg00>Uj28Tg00??j1HTg00?]j26Tg00@:j1ETg00AHj1@Tg00Ahj3YTg00BHj4CTg005hj3<Tg006Bj2;Tg00CWj2BTg00D?j25Tg005Kj2ATg00D[j3=Tg00E?R0j2:Tg00EZj2TTg00F;j1QTg00F[j1KTg00G9j1JTg00GWj1ITg00HBj29Tg00Hej4>Tg00IPj3FTg00J3j7LTg00JWj2MTg00K9j2NTg00Kej3OTg00LDj4PTg00M6j2DTg006\j6Rj7STg00NKj2XTg00Ngj7WTf0R1#3#3p=1%01#3p=7g00OKR2/X1p=2f1R3g00OiR4g00PHR5P5g00PhR6P1g00QHFWp=?g00;FR7#3R8#1#1R9#3R:#VR;#GR<%77R7#0#1#0R=#7#1#7#1#1#4R>,U;R?g00QhR@p,1mRA18;1%08#1#0#1#HRB'6g00S<RCp,4errv#E%@C3YRCCCg00;kRD18;3/6B%3=#7#0#0#0#0#0#1#4R=3<]1X?<P@PA18;?R?/6BPCCCPDP>161B=<D=X@D1;D=P?%48R8%49R9'B1528R?%291A89R=,52[RB[%28RCg00TJRAA=893UW0%2=\A^0C%4:R:,B8%2:1A8:R9,52[R@\?A=8:3VAX0C%29\A^0Cp,2SCp,2scRC#2RA%37#1#4,5CRC':P0PAPC%2>15>9':R9P1p,2RQp,3reqR7#2R:157=R7':P0P:P7P9P1f;g00Tf1T28';P?eR?O1P@f>P?O1PBg00ULRB#@%QB%KD%JD%IDRBP4P5P5P6PD19D2g00V819D>R5C>,?BPDP5g00V_19D8=FD;C>,?BFL1MB6P1f2RBg00WFR6g00WfR;';1N1B=<6;dAOD23CPb:b=b>P9P1b9b3b2X87X7:P3P1O2n2001000000121000000b4X6CX5AP3P1O2n2001000000121000000b4b;b2b<b3,D>ERW1p,2tpp,2TPp,3ERRFSo"). Qed.
(* [comment removed for export] *)
End LEVEL.
End CEIL_WRAP_1.


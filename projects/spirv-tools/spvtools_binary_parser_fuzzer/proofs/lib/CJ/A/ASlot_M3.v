(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocKit_AB.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W10 ASlot_W11 ASlot_I ASlot_M0.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require MallocFacts_inv4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_ASlot_M3 () := "C69OSSVerify5KrLib2CJ4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C69OSSVerify5KrLib2CJ4Spec6Malloc9halve_bigC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z8leb_specC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes7nat_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib2CJ4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma halve_big_pos F : forall cnt sz, 1 <= cnt -> 0 <= sz < 2^18 -> 1 <= halve_big F cnt sz.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_M3 ()) ["AC_1"] "p'0h06__sat1h14__x1h27__arithh34__ffh46__sat0h58__varmaph65__with74__x2h81Fh93cnth:2szh;2H1h<2Hah=2Hch>2Hsh?4__p1h@6__sat6hA4__x3hB2GThC1HhD2H0hE2H2hF2H3hG2H4hH2IHhI2LEhJ6__sat5hK1bi001bhL2b0hM1qhN1rhO1zp;1p;2p;3p;4p;5p;6p;7p;8p10000p4p70p1000hp4p7210R0p8p1001fp4p70P0p8g002^j17Tg003<j21Tg003Xj10Tg004=j15Tg004bj2RTg005?j22Tg005[j2<Tg0066j3GTg0073j2^Tg007[j3\Tg008?j2ZTg008`j2TTg009:j1~Tg009Zj1{Tg00::j2NTg00:Xj1wTg00;6j1qTg00;aj2ATg00<Dj2KTg00<gj1gTg00=Ij2dTg00=kj2cTg00>Wj3=Tg00?1j3`Tg00?Pj4_Tg00@Bj28Tg00@_j2[Tg00AAj2PTg00A^R0j3YTg00BBj2XTg00Bbj2ETg00C?j2DTg00Chj2OTg00DIj4WTg00Djj3}Tg00EKj2|Tg00F4j2?Tg00F]j1>Tg00G<j2VTg00Ghj3STg00HHj1vTg00Hfj4JTg00IDj5pTg00Ihj1oTg00JFj3nTg00Jij3MTg00KLj2jTg00Kmj1iTg00LFj2@Tg00Lfj2QTg00MCj2hTg00Mjj2kTg00NQj2lTg00O7j2mTg00O]j6fTg00PAj4FTg00Plj6eTg00QPj3rTg00R3j3sTg00R\j6tTg00S:j4uTg00S[j7UTg00T?j8xTg00Tcj3bTg00ULj3aTg00V5j7zTg00VYR1f0R2'1p=6f2R3g00W7R4g00WVR5P5g00X6R6g00XVR7f1R8g00Y4P2CFg00Y[R9FUp=9f3R:P4P5P5P6P3P8P2Gxp=4%02#0p=H%02#0#0#0p=]%02#0#0#0#0#0#0#0p=BAb782p=3%52#5#5#5p=:%52#5p=yAa782p=;P7P8g00Z;P2CFp=IP8P4P5P5P6P2P9FUp=CP3P4P5P5P6P8P2Fzp=Lg00ZbR9g00[AR;#7R</18R=%68%0;R>#7R?%0>R@#5#0RA#7RB'RRC,28'<RDf4RE?G:3,1<[[^:7^97RFX891^?BRG121?RH%6B121C[RI[RJ%6?RKg00[fRLA\?B8UW<RB%6C\LRL^<KRMP8g00\B1Z1?'TPHeRNO1ROPIg00\hRP#~RQ%{PRR1N78RS%w7RT%q7RU1A7<RV1K7;RW59URX%g5RYPXC41dU6RZP2P3g00]TR[g00^4R\'T1c23==[\dA`718C_R\b3b5b6X17R]11<2R^P=[^17R_P2f7R`f5RaO2b2b0b4b0g00^TRb?G:3,1<eX>DX==X:7X97%H@Rc#]#BRd#7Reg00_3'8Rf183:Rg'[11fg12gf1Pfg3Y18:E,PfP[P018EaR0,1f120fP[P7P8f9R[1X`<R0f6Rg3GP`n0100000020000,1<P818agRh,1ff8RiP0PgP71R?<,E`P^XO7PGPJPBPMPOPI%Hd#7,D7RdP71O7<P;1O71CW9}7;,|71?7bR^'3'3%5;#0#B#B#5R;#7,D7%>bRb#>Rj#>Rk#>Rl#>,?7Rm1?7lRl'3'3%:>#:#:#:#0#5#y#:#:#:#:#7,D713m^'31?7kRk/3l,3d1?7jRj,3k,3d%H;#B#B#7,D71?7bRb,3j'3';';';';';g00_kR;'V=SPQPRP71N73P8%v7RdCJPTPUPU1A71Rl1A7?Rm59UPYPUPUP4P5P5P6DpPY%oA9n7mRA99UlC4C4PYPU1A7e%7cRc,A75M71K7>R>=M7W59UPYPUA9Ul>1I>A,CU5LUPYPUPXPYA9UmWC4C4C4C4PZP\b3b5b6X17X77PL\K18ec1838'1%6:12:C'<11<:Rc11?E[[[[^17^77P2f:Ref;RKP3PEPiP[O6b2b0b4b011?`1ji?A=7?1RL#i1E[?,8?1@[?'Q9=7[[1h[?1@e?Rn#612n?'<\H1ke?12?11@K?RH,2?11H1'<[1lK?f<RH/E?==71\L1mH?f=R1/@?==71\L1E1?P7f>/@?P7PaPNO1%62RN122?'<PGPJPBPMPOPIp-0R11D7?/3^,;b,;j,;k/V;=SPQPRP7P71N7:P3PdCJP8PdCJPTPUPUP4P5P5P6PaEf1K7@R@/Im,CU5LUPYPUPUPUP4P5P5P6P7Pmg00`WR6PlCF,CUEePYP7P>P6AM7mW=r7@CF,CUC4PYPUA9Um>PYPXC4C4C4PZP\b3b5b6X17X77XA7W?123?,<:g00a>\L18?3/QE9=7:[11?:Pc[[[^17^77^A7^?1P2%6aPafDPgPEPKPHO7b2b@bJb@b;bNbMbGbFbEb;bDbCP0PGPJPBPMPOPIPQPRPdPTA9UlVPZP\b3b5b6%6<P2b2b0b4b09s`<EtPGPJPBPMPOPIPQPRPSPTPUA9UlW1IWA,CU5LURUPYPUC4PZP\b3b5b6X17122C,<NPD[^17P2PePiO2b2b0b4b0O4WIP2O112hfPGPJPBPMPOPIP]P_P2PKP[O2b2b0b4b0WBP2O1n200210000000021100011000bLbK%>a?G:3,1<eX>DX==X:7X97XHFX89P2CuW8o"). Qed.

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
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis MED : rw_cells asegs m MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  implT o (k st1 idx) s' Q ms'.
Let F0 : ISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Definition ag_ctx (st1 st2 : mstate) (mm : aptr) (m3 : mem) (s' : PState) (errv' : word) (j : list byte) (oo : mem) : Prop :=
  ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
  leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
  IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
  am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
  mrep st2 m3 /\ ticks_ok st2 /\ unk_agree st2 o m3 /\ mem_inv asegs m3 /\ stk asegs m3 lo (bv_unsigned sp + -96) /\
  rw_cells asegs m3 (bv_unsigned sp + -96) (ag_frame sc j s4 s3 s2 s1 s0 ra) /\
  rw_cells asegs m3 (errno_addr tp) [C4 errv'] /\ auxv_ok m3 (bv_unsigned sp) /\ rw_cells asegs m3 MEDTAB medtab_cells /\
  pres_except (malloc_fp st0 st2 lo (bv_unsigned sp)) m m3 /\
  brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s.

Definition HMM_stmt : Prop :=
  forall st1 st2 mm m3 s' errv' j oo (cnt1 : Z) (t0' t2' a3' t4' t6' : word),
  ag_ctx st1 st2 mm m3 s' errv' j oo ->
  1 <= cnt1 <= 32 -> 2048 < size_class sc * UNIT * cnt1 + UNIT ->
  implT o (ag_mmap sc req k bail st2 mm cnt1) s' Q
    (MS (mkR (Z_to_bv 64 0x163fc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' (wz (size_class sc * UNIT)) t2' (Z_to_bv 64 sc) (Z_to_bv 64 CTX)
             (wz 4096) (wz (size_class sc * UNIT * cnt1)) (wz (usage st2 sc)) a3' (Z_to_bv 64 SIZE_CLASSES) (wz 2048) (wz cnt1) (Z_to_bv 64 (conc st2 mm))
             (Z_to_bv 64 (sc + 10)) (wz (size_class sc)) a1 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (sc + 58)) t4' (wz (4 * cnt1)) t6')
        F (Z_to_bv 64 0x16640) fc None m3 (seg_rom asegs)).

Definition HNEST_stmt : Prop :=
  forall st1 st2 mm m3 s' errv' j oo (cnt1 : Z) (t0' t2' a3' t5' t6' : word),
  ag_ctx st1 st2 mm m3 s' errv' j oo ->
  1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
  implT o (ag_nest f sc k bail st2 mm cnt1) s' Q
    (MS (mkR (Z_to_bv 64 0x163fc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' (wz (size_class sc * UNIT)) t2' (Z_to_bv 64 sc) (Z_to_bv 64 CTX)
             (wz 4096) (wz (size_class sc * UNIT * cnt1)) (wz (usage st2 sc)) a3' (Z_to_bv 64 SIZE_CLASSES) (wz 2048) (wz cnt1) (Z_to_bv 64 (conc st2 mm))
             (Z_to_bv 64 (sc + 10)) (wz (size_class sc)) a1 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (sc + 58)) (wz cnt1) t5' t6')
        F (Z_to_bv 64 0x16954) fc None m3 (seg_rom asegs)).

Hypothesis HMM : HMM_stmt.
Hypothesis HNEST : HNEST_stmt.

End LEVEL.

End AC_1.

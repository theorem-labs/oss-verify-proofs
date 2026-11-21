(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (1 recorded proof replaced by written proofs (ralloc_slot_ok)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_I ASlot_M0.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W2 RASlot_W4 RASlot_W9 RASlot_M0 RASlot_M1 RASlot_M2 RASlot_M3 RASlot_M4 RASlot_M5D RASlot_M5F RASlot_M5S RASlot_M5.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv4.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RASlot_M6 () := "I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan8RASlot_IAralloc_slot_stmt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RASlot_M29rag_phaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RASlot_M37rhag_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RASlot_M47rhmm_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RASlot_M59rhnest_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RASlot_M5S9rnsucc_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RASlot_M17rhk1_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree<rimplT_undefC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RASlot_W99rta_phaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RASlot_M5F9rnfail_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W14as_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree@ralloc_meta_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS8AMP_AS_gC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib5Ubsan8RASlot_I8ras_pre2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp9unk_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree;brk_link_psC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib5Ubsan;RMallocTree8rauxv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib5Ubsan@RAllocSlot_iface9RAS_STACKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib5Ubsan8RASlot_I9ras_post2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree6rimplTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes4list00I59OSSVerify5KrLib6Malloc>MallocFacts_AS3IST00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00I59OSSVerify5KrLib6Malloc7ASlot_I9ENTRY_REL00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc7ASlot_I4ALLCC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib6Malloc@MallocFacts_inv4?ist_facts_proofC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc>MallocFacts_AS6ISTF_g00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan@RAllocSlot_iface<RAS_STACK_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9try_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RASlot_M0=rtaf_of_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init9Datatypes6option00I59OSSVerify5KrLib6Malloc8ASlot_W06ta_rel00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I59OSSVerify5KrLib6Malloc8ASlot_W93gmf00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RASlot_W96rta_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree<rpres_exceptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS7ta_failC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RASlot_W29rta_frameC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W16as_grpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RASlot_W48rt1_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W1<alloc_slot_SC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indI59OSSVerify5KrLib6Malloc<MallocBlocks;AREACH_from00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib5Ubsan:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep4RATPC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRepAralloc_slot_entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Theorem ralloc_slot_ok (ram_pre : mstate -> Prop) :
  ralloc_meta_stmt ram_pre -> RAMP_AS ram_pre -> forall f, ralloc_slot_stmt2 f.
Proof.
  intros AM AMP f. induction f as [|f IHf].
  - intros R k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st lo sc req errv
           PRE MR TK UA BL AUX ST CLO LO ERR MI TP A0 A1 HK.
    cbn [alloc_slot]. apply rimplT_undef.
  - intros R k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st lo sc req errv
           PRE MR TK UA BL AUX ST CLO LO ERR MI TP A0 A1 HK.
    destruct PRE as ((LB & AR & IS) & ER & AC & SC & RQ & FIT).
    pose proof (MallocFacts_inv4.ist_facts_proof st0 LB st AR IS) as F0.
    pose proof (RAS_STACK_ge sc) as ASG.
    rewrite (alloc_slot_S full_lay f sc req k bail st). subst a0.
    eapply (rta_phase (as_k full_lay f sc req k bail) bail o s Q st m sc lo ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
              (rtaf_of_facts st LB sc F0 SC) SC CLO ltac:(lia)).
    + (* [comment removed for export] *)
      intros stX g3 msk kk m' t0' t1' a1' a2' a3' a4' a5' a6' a7' TR HA GM MSK MR0 LBK KK MR' MI' ST' PE.
      exact (rhk1_ok f k bail o s Q ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st LB lo sc req errv
                AR IS ER AC SC RQ FIT MR TK UA BL AUX CLO LO ERR TP HK stX g3 msk kk m' t0' t1' a1' a2' a3' a4' a5' a6' a7' TR HA GM MSK MR0 LBK KK MR' MI' ST' PE).
    + reflexivity.
    + exact MR.
    + exact MI.
    + exact ST.
    + (* [comment removed for export] *)
      intros st1 m' t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' junk TF TR ACT0 MR1 MI1 FR1 ST1 PE1.
      unfold as_k. cbn [Z.eqb negb].
      eapply (rag_phase f k bail o s Q ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st LB lo sc req errv
                AR IS ER AC SC MR TK UA BL AUX CLO LO ERR TP HK ram_pre AM AMP); [| exact TF| exact TR| exact ACT0| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1].
      (* [comment removed for export] *)
      refine (rhag_ok f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req AR SC RQ FIT _ _).
      * (* [comment removed for export] *)
        exact (rhmm_ok k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req
                 AR ER SC RQ FIT MR AUX CLO LO TP A1 HK).
      * (* [comment removed for export] *)
        refine (rhnest_ok f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc AR ER SC MR CLO LO TP IHf _ _).
        -- exact (rnfail_ok f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req errv
                   AR IS ER SC RQ MR AUX CLO LO ERR TP HK).
        -- exact (rnsucc_ok f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req errv
                   AR IS ER SC RQ FIT MR AUX CLO LO ERR TP HK).
Qed.
End CANSEC1.

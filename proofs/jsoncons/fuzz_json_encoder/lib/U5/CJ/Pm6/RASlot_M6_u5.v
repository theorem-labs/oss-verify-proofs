(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import F_malloc_free_u5 F_malloc_fast_u5 F_malloc_entry_u5 F_malloc_enframe_u5 MallocTree_u5 MallocFacts_A_u5 MallocHINV_u5 MallocKit_A_u5 MallocKit_AB_u5 MallocKit_A2_u5 MallocKit_A3_u5 MallocKit_B_u5 MallocKit_B3_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import Malloc_fp_u5 MallocNat_u5 MallocFacts_AS_u5 ASlot_W0_u5 ASlot_W1_u5 ASlot_W9_u5 ASlot_I_u5 ASlot_M0_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Pm6 Require Import RMallocRep_u5 RMallocTree_u5 RF_get_meta_u5 RMallocKit_B_u5 RMallocKit_B2_u5 RMallocKit_B3_u5 RMallocKit_A_u5 RMallocKit_A2_u5 RMalloc_fp_u5 RAllocSlot_iface_u5 RASlot_I_u5 RASlot_W2_u5 RASlot_W4_u5 RASlot_W9_u5 RASlot_M0_u5 RASlot_M1_u5 RASlot_M2_u5 RASlot_M3_u5 RASlot_M4_u5 RASlot_M5D_u5 RASlot_M5F_u5 RASlot_M5S_u5 RASlot_M5_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require MallocFacts_inv4_u5.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


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
    pose proof (MallocFacts_inv4_u5.ist_facts_proof st0 LB st AR IS) as F0.
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
End CEIL_WRAP_1.


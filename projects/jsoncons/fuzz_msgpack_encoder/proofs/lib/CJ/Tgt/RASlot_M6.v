(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require SysStep SFModel ITree Nodes Decode. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045.Tac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Image OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.ZBridge OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.SysStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.SFModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.ITree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Decode OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Arr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Ubsan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0072. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0082. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0061. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0072.F_malloc_free OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0082.F_malloc_fast OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0082.F_malloc_entry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0082.F_malloc_enframe OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0061.MallocTree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0061.MallocFacts_A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0061.MallocHINV OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0082.MallocKit_A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0072.MallocKit_AB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0082.MallocKit_A2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0082.MallocKit_A3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0072.MallocKit_B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0072.MallocKit_B3.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec Require Monad. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004.STree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029.Malloc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029.MallocCtrl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Monad OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046.Prog.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0082. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0061. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0082.Malloc_fp OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0061.MallocNat OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0061.MallocFacts_AS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0082.ASlot_W0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0082.ASlot_W1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0082.ASlot_W9 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0082.ASlot_I OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0082.ASlot_M0.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0074. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0096. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0098. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0122. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt Require RASlot_M4 RASlot_M5S. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0074.RMallocRep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0074.RMallocTree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0096.RF_get_meta OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0098.RMallocKit_B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0096.RMallocKit_B2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0098.RMallocKit_B3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0096.RMallocKit_A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0096.RMallocKit_A2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0096.RMalloc_fp OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0096.RAllocSlot_iface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0096.RASlot_I OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0122.RASlot_W2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0122.RASlot_W4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0122.RASlot_W9 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0096.RASlot_M0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0122.RASlot_M1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0122.RASlot_M2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0122.RASlot_M3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.RASlot_M4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0122.RASlot_M5D OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0122.RASlot_M5F OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.RASlot_M5S OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Tgt.Mh_0122.RASlot_M5.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0131. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0131.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Import RunP. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
End CEIL_WRAP_1.


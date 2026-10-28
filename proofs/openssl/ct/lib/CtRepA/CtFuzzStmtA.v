(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse ApPrim.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import CtSizes CtWire CtTime CtModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs D_libiface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA UnwindA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface W_get_objectA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition CT_FUZZ_ENTRY_A : Z := 0x1f40f0.
Definition FUZZER_TEST_ONE_INPUT_A : Z := 0x1f4160.

(* [comment removed for export] *)
Definition CT_FUZZ_STACK_A : Z := FUZZ_STACK - 16.            (* [comment removed for export] *)
Definition CT_FUZZ_COST_A (len : Z) : Z := FUZZ_COST.         (* [comment removed for export] *)
Definition CT_FUZZ_FRAMES_A : Z := Z.of_nat FRAMES_MAX - 1.   (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).

(* [comment removed for export] *)
Definition ct_top_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ0 : rts RT) (LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z)
    (m0 : mem) (D : Z) (d : list Z) (r : Z * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (OW' : list block) (bo' : Z * Z),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' (snd r) m' OW' LB E bo' sp lo 0 0 0
    /\ snd r = st_of_ls (ls_of_st (snd r))
    /\ ax_pres LB (bv_unsigned sp) LIBW_A m0 m'
    /\ rt_credit RT Σ0 - CT_FUZZ_COST_A (zlength d) <= rt_credit RT Σ'
    /\ payload_okA m' LB D d
    /\ fst r = 0.

(* [comment removed for export] *)
Definition ct_fuzz_stmtA : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : ap_ls bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (D : Z) (d : list Z),
    ap_preA Σ (st_of_ls ls) m OW LB E bo sp lo CT_FUZZ_STACK_A (CT_FUZZ_COST_A (zlength d)) CT_FUZZ_FRAMES_A -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) nil ->            (* [comment removed for export] *)
    uk_ctx CT_FUZZ_ENTRY_A [bv_unsigned ra] ->                                (* [comment removed for export] *)
    payload_okA m LB D d -> a0 = wz D -> a1 = wz (zlength d) ->
    implAp (ct_call d (st_of_ls ls)) Σ
           (ct_top_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ LB E bo lo m D d)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz CT_FUZZ_ENTRY_A) fc None m (seg_rom ctasegs)).

End WithRT.

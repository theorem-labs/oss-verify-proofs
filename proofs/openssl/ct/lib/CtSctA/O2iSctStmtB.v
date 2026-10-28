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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApLogic ApInv ApErr ApParse ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA UnwindA EdgesA UnwindX W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface W_get_objectA ApErrKitA2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctRep O2iKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import W_sk_leavesA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA W_o2i_sigA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

(* [comment removed for export] *)
Definition O2I_SCT_STACK_A : Z := 176 + O2I_SIG_STACK_A.
Definition O2I_SCT_COST_A (len : Z) : Z := 1 + 2 * GETOBJ_ERR_COST_A + 2 * mcost len.
Definition O2I_SCT_FRAMES_A : Z := 1 + O2I_SIG_FRAMES_A.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition o2i_sct_postA2 (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (m : mem) (K : list block) (CST : Z)
    (adr : bptr -> Z) (c : list Z) (D p len PIN : Z)
    (r : option (sctr bptr) * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' bo' (adr' : bptr -> Z) (NEW : list block),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz match fst r with Some x => adr' (sc_blk x) | None => 0 end) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' (snd r) m' OW' (NEW ++ LB) E bo' sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(PIN, PIN + 8)] ++ LIBW_A) m m'
    /\ rt_credit RT Σ - CST <= rt_credit RT Σ'
    /\ blocks_kept K (snd r) OW' m m'
    /\ (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b))
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OW' ++ LB)))
    /\ Forall lbokA NEW
    /\ match fst r with
       | None => NEW = [] /\ rw_cells ctasegs m' PIN [C8 (wz (D + p))]
       | Some x => NEW = sct_blocks adr' x /\ sct_repA m' (OW' ++ NEW ++ LB) adr' x /\ rw_cells ctasegs m' PIN [C8 (wz (D + p + len))]
                   /\ sc_version x = CtWire.byte c p /\ i2o_sct_len x <= len
       end.

Definition o2i_sct_specA2 (STK : Z) (CST : Z -> Z) (FRM : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z)
         (adr : bptr -> Z) (c : list Z) (D p len PIN : Z),
    ap_preA Σ st m OW LB E bo sp lo STK (CST len) FRM -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx O2I_SCT_A (bv_unsigned ra :: ras) -> ras <> nil ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_okA m LB D c -> 0 <= p -> 1 <= len <= MAX_SCT_SIZE -> p + len <= zlength c ->
    (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    cellA_in LB PIN 8 -> PIN mod 8 = 0 -> (PIN + 8 <= D \/ D + zlength c <= PIN) -> rw_cells ctasegs m PIN [C8 (wz (D + p))] ->
    a0 = wz 0 -> a1 = wz PIN -> a2 = wz len ->
    implAp (o2i_sct c p len st) Σ
           (o2i_sct_postA2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST len) adr c D p len PIN)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz O2I_SCT_A) fc None m (seg_rom ctasegs)).

End WithRT.

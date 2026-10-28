(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA UnwindA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ASN1_GET_OBJECT_A : Z := 0x223b30.
(* [comment removed for export] *)
Definition GETOBJ_STACK_A : Z := 64 + ERR_SET_ERROR_STACK.
(* [comment removed for export] *)
Definition GETOBJ_ERR_COST_A : Z := ERR_NEW_COST + ERR_SET_DEBUG_COST + ERR_SET_ERROR_COST.
(* [comment removed for export] *)
Definition GETOBJ_FRAMES_A : Z := ERR_SET_ERROR_FRAMES.
(* [comment removed for export] *)
Definition A_ASN1_LIB_C_A : Z := 0x713c0.
Definition A_ASN1_GET_OBJECT_FN_A : Z := 0x71400.

Notation go_eff := CtRepP.W_get_object.go_eff.

Definition go_costA (g : go_res) : Z := match go_err g with None => 0 | Some _ => GETOBJ_ERR_COST_A end.

(* [comment removed for export] *)
Definition cellA_in (LB : list block) (A n : Z) : Prop :=
  exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b.

(* [comment removed for export] *)
Definition go_cellsA_ok (LB : list block) (PP PL PT PC : Z) : Prop :=
  cellA_in LB PP 8 /\ cellA_in LB PL 8 /\ cellA_in LB PT 4 /\ cellA_in LB PC 4
  /\ PP mod 8 = 0 /\ PL mod 8 = 0 /\ PT mod 4 = 0 /\ PC mod 4 = 0
  /\ (PP + 8 <= PL \/ PL + 8 <= PP) /\ (PP + 8 <= PT \/ PT + 4 <= PP) /\ (PP + 8 <= PC \/ PC + 4 <= PP)
  /\ (PL + 8 <= PT \/ PT + 4 <= PL) /\ (PL + 8 <= PC \/ PC + 4 <= PL) /\ (PT + 4 <= PC \/ PC + 4 <= PT).

(* [comment removed for export] *)
Definition go_cells_offA (D n PP PL PT PC : Z) : Prop :=
  (PP + 8 <= D \/ D + n <= PP) /\ (PL + 8 <= D \/ D + n <= PL) /\ (PT + 4 <= D \/ D + n <= PT) /\ (PC + 4 <= D \/ D + n <= PC).

(* [comment removed for export] *)
Definition payload_okA (m : mem) (LB : list block) (D : Z) (d : list Z) : Prop :=
  bytes_at ctasegs m D (to_bytes d) /\ Forall (fun c => 0 <= c < 256) d
  /\ 0 < D /\ D + zlength d < 2^63 /\ zlength d < 2^26
  /\ (d = [] \/ exists b, In b LB /\ blk_addr b <= D /\ D + zlength d <= blk_addr b + blk_size b).

Section WithRT.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition ERR_new_specA_bo : Prop := forall bo0 : Z * Z,
  ap_stmtA ERR_NEW ERR_NEW_STACK ERR_NEW_COST ERR_NEW_FRAMES (fun st OW m a0 a1 a2 a3 a4 a5 bo => bo = bo0) (err_new)
           (fun r OW' m' a0' bo' => bo' = bo0).
Definition ERR_set_debug_specA_bo (rs : rsite) (file func : Z) : Prop := forall bo0 : Z * Z,
  ap_stmtA ERR_SET_DEBUG ERR_SET_DEBUG_STACK ERR_SET_DEBUG_COST ERR_SET_DEBUG_FRAMES
           (fun st OW m a0 a1 a2 a3 a4 a5 bo => a0 = wz file /\ a1 = wz (rs_line rs) /\ a2 = wz func /\ bo = bo0) (err_set_debug rs)
           (fun r OW' m' a0' bo' => bo' = bo0).

(* [comment removed for export] *)
Definition getobj_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (m : mem) (K : list block)
    (D PP PL PT PC : Z) (g : go_res) (r : unit * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' (jl j2 j3 : list byte),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' (snd r) m' OW' LB E bo sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(PP, PP + 8); (PL, PL + 8); (PT, PT + 4); (PC, PC + 4)] ++ LIBW_A) m m'
    /\ rt_credit RT Σ - go_costA g <= rt_credit RT Σ'
    /\ blocks_kept K (snd r) OW' m m'
    /\ rw_cells ctasegs m' PP [C8 (wz (D + go_p g))]
    /\ match go_err g with
       | None => a0 = wz (go_ret g)
                 /\ rw_cells ctasegs m' PL [C8 (wz (go_len g))] /\ rw_cells ctasegs m' PT [C4 (wz (go_tag g))] /\ rw_cells ctasegs m' PC [C4 (wz (go_cls g))]
       | Some GeTooLong => a0 = wz (Z.lor (go_ret g) 128)
                 /\ rw_cells ctasegs m' PL [C8 (wz (go_len g))] /\ rw_cells ctasegs m' PT [C4 (wz (go_tag g))] /\ rw_cells ctasegs m' PC [C4 (wz (go_cls g))]
       | Some _ => a0 = wz 128
                 /\ rw_cells ctasegs m' PL [CB 8 jl] /\ rw_cells ctasegs m' PT [CB 4 j2] /\ rw_cells ctasegs m' PC [CB 4 j3]
       end.
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ASN1_get_object_specA : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z)
         (D : Z) (d : list Z) (op omax PP PL PT PC : Z) (jl j2 j3 : list byte),
    ap_preA Σ st m OW LB E bo sp lo GETOBJ_STACK_A GETOBJ_ERR_COST_A GETOBJ_FRAMES_A -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ASN1_GET_OBJECT_A (bv_unsigned ra :: ras) -> ras <> nil ->   (* [comment removed for export] *)
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_okA m LB D d -> 0 <= op -> 0 < omax -> op + omax <= zlength d ->
    go_cellsA_ok LB PP PL PT PC -> go_cells_offA D (zlength d) PP PL PT PC ->
    rw_cells ctasegs m PP [C8 (wz (D + op))] -> rw_cells ctasegs m PL [CB 8 jl] -> rw_cells ctasegs m PT [CB 4 j2] -> rw_cells ctasegs m PC [CB 4 j3] ->
    a0 = wz PP -> a1 = wz PL -> a2 = wz PT -> a3 = wz PC -> a4 = wz omax ->
    implAp (go_eff (get_object d op omax) st) Σ
           (getobj_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E bo lo m K D PP PL PT PC (get_object d op omax))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz ASN1_GET_OBJECT_A) fc None m (seg_rom ctasegs)).

End WithRT.

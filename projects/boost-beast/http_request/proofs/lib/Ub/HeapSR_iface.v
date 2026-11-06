(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr SysStep Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import USegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ROPNEW   : Z := 0x7d324.   (* [comment removed for export] *)
Definition ROPDEL   : Z := 0x5d2d8.   (* [comment removed for export] *)
Definition ROPDEL2  : Z := 0x5d2dc.   (* [comment removed for export] *)
Definition ROPNEW_STACK : Z := 16 + RMALLOC_STACK.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition lb_bytes (LB : list block) : Z := fold_right (fun b acc => blk_size b + acc) 0 LB.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record hsr := {
  hs_SR       : (config -> Prop) -> config -> Prop ;
  hs_KREL     : PState -> Model -> Prop ;
  hs_MPRES    : Model -> Model -> Prop ;
  hs_RHEAP    : PState -> list block -> mem -> Prop ;
  hs_rauxv_ok : mem -> Z -> Prop ;
  hs_lb_remove : bptr -> list block -> list block ;
  hs_alloc_ok : PState -> list block -> Z -> Prop ;
  hs_LIVE_MAX : Z ;          (* [comment removed for export] *)
  hs_LIVE_CNT_MAX : Z       (* [comment removed for export] *)
}.

Section Iface.
  Context {HCEIL : HeapCeil}.   (* [comment removed for export] *)
  Variable H : hsr.
  Notation SR := (hs_SR H).  Notation KREL := (hs_KREL H).  Notation MPRES := (hs_MPRES H).
  Notation RHEAP := (hs_RHEAP H).  Notation rauxv_ok := (hs_rauxv_ok H).  Notation lb_remove := (hs_lb_remove H).
  Notation alloc_ok := (hs_alloc_ok H).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition SR_laws : Prop :=
       (forall (Q : config -> Prop) c, Q c -> SR Q c)                                                   (* [comment removed for export] *)
    /\ (forall (Q Q' : config -> Prop) c, SR Q c -> (forall c', Q c' -> Q' c') -> SR Q' c)            (* [comment removed for export] *)
    /\ (forall (Q1 Q2 : config -> Prop) c, SR Q1 c -> (forall c', Q1 c' -> SR Q2 c') -> SR Q2 c)      (* [comment removed for export] *)
    /\ (forall (P : machine_state -> Prop) ms mo,                                                      (* [comment removed for export] *)
          m_halted mo = None -> m_vm_lazy mo = [] -> evt usegs P ms ->
          SR (fun c => P (cfg_ms c) /\ cfg_model c = mo) (mkCfg ms mo)).

  Definition KREL_laws : Prop :=
       (forall s mo, KREL s mo -> m_halted mo = None /\ m_vm_lazy mo = []).

  Definition MPRES_laws : Prop :=
       (forall mo, MPRES mo mo)
    /\ (forall mo1 mo2 mo3, MPRES mo1 mo2 -> MPRES mo2 mo3 -> MPRES mo1 mo3).

  (* [comment removed for export] *)
  Definition alloc_ok_of_live : Prop :=
    forall s LB m n, RHEAP s LB m -> 0 <= n -> lb_bytes LB + n <= hs_LIVE_MAX H ->
      Z.of_nat (length LB) + 1 <= hs_LIVE_CNT_MAX H -> alloc_ok s LB n.

  (* [comment removed for export] *)
  Definition RHEAP_frame : Prop := RHEAP_frame_stmt RHEAP.
  Definition RHEAP_block_range : Prop := RHEAP_block_range_stmt RHEAP.
  Definition RHEAP_blocks_disjoint : Prop := RHEAP_blocks_disjoint_stmt RHEAP.
  Definition RHEAP_blocks_nodup : Prop := RHEAP_blocks_nodup_stmt RHEAP.
  Definition rauxv_frame : Prop := rauxv_ok_frame_stmt rauxv_ok.
  (* [comment removed for export] *)
  Definition lb_remove_laws : Prop :=
       (forall p A n LB, ~ In p (map blk_id LB) -> lb_remove p ((p, A, n) :: LB) = LB)
    /\ (forall p b LB, blk_id b <> p -> lb_remove p (b :: LB) = b :: lb_remove p LB)
    /\ (forall p LB b, In b (lb_remove p LB) -> In b LB).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition malloc_sr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (n lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) junk (p : bptr) (s' : PState),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ KREL s' (cfg_model c) /\ MPRES mo (cfg_model c)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
      /\ rheap_pres LB (bv_unsigned sp) m m'
      /\ rblock_range A n /\ RHEAP s' ((p, A, n) :: LB) m'
      /\ rw_cells usegs m' A [CB (Z.to_nat n) junk].

  Definition malloc_sr_stmt_at (entry stack : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (n lo B : Z) (errv : word) (mo : Model),
      RHEAP s LB m -> KREL s mo -> alloc_ok s LB n ->
      rauxv_ok m B -> bv_unsigned sp <= B ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - stack ->
      rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
      a0 = Z_to_bv 64 n -> 1 <= n < 2^32 ->
      SR (malloc_sr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo)
         (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 entry) fc None m (seg_rom usegs)) mo).

  Definition malloc_sr_stmt : Prop := malloc_sr_stmt_at RMALLOC_SYM RMALLOC_STACK.
  (* [comment removed for export] *)
  Definition opnew_sr_stmt : Prop := malloc_sr_stmt_at ROPNEW ROPNEW_STACK.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition free_sr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : PState),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ KREL s' (cfg_model c) /\ MPRES mo (cfg_model c)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' (errno_addr tp) [C4 errv]          (* [comment removed for export] *)
      /\ rauxv_ok m' B
      /\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
      /\ RHEAP s' (lb_remove p LB) m'.

  Definition free_sr_stmt_at (entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word) (mo : Model),
      RHEAP s LB m -> KREL s mo -> In (p, A, n) LB ->
      rauxv_ok m B -> bv_unsigned sp <= B ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
      rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
      a0 = Z_to_bv 64 A ->
      SR (free_sr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m mo)
         (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 entry) fc None m (seg_rom usegs)) mo).

  Definition free_sr_stmt : Prop := free_sr_stmt_at RFREE_SYM.
  Definition opdel_sr_stmt : Prop := free_sr_stmt_at ROPDEL.       (* [comment removed for export] *)
  Definition opdel2_sr_stmt : Prop := free_sr_stmt_at ROPDEL2.     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition opdel_null_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) : config -> Prop :=
    fun c => cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (ret_pc ra) fc None m (seg_rom usegs)
             /\ cfg_model c = mo.
  Definition opdel_null_sr_stmt_at (entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model),
      m_halted mo = None -> m_vm_lazy mo = [] ->
      SR (opdel_null_post ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo)
         (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 entry) fc None m (seg_rom usegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition heap_sr_hyps : Prop :=
    SR_laws /\ KREL_laws /\ MPRES_laws /\ alloc_ok_of_live
    /\ RHEAP_frame /\ RHEAP_block_range /\ RHEAP_blocks_disjoint /\ RHEAP_blocks_nodup /\ rauxv_frame /\ lb_remove_laws
    /\ malloc_sr_stmt /\ opnew_sr_stmt /\ free_sr_stmt /\ opdel_sr_stmt /\ opdel2_sr_stmt
    /\ opdel_null_sr_stmt_at ROPDEL /\ opdel_null_sr_stmt_at ROPDEL2.
End Iface.

(* [comment removed for export] *)

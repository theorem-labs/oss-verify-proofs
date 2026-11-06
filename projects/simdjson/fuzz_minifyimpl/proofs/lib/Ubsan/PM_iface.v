(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessM ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PM_model.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RunDraw PU_iface PM_kit UM_minify.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Export PM_strlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Notation Popnew := (HarnessM.opnew raw_malloc ProgP.new_handler).
Notation Popdelete := (HarnessM.opdelete raw_free).
Notation Podelete := (HarnessM.odelete raw_free).
Notation Pvctor := (vctor_model raw_malloc ProgP.new_handler).
Notation Passign := (assign_model raw_malloc raw_free ProgP.new_handler).
Notation Plam := (lam_model raw_malloc raw_free ProgP.new_handler).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition PLAM : Z := 0x3c3f0.          (* [comment removed for export] *)
Definition PVCTOR : Z := 0x3c7c4.        (* [comment removed for export] *)
Definition PVALLOC : Z := 0x3c954.       (* [comment removed for export] *)
Definition PRESIZE : Z := 0x3c8fc.       (* [comment removed for export] *)
Definition PSTRCTOR : Z := 0x3c82c.      (* [comment removed for export] *)
Definition PASSIGN : Z := 0x3ca5c.       (* [comment removed for export] *)
Definition PMEMMOVE : Z := 0xcefd0.      (* [comment removed for export] *)
Definition PERRCODES : Z := 0xd4c48.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition VCTOR_STACK : Z := 48 + 32 + OPNEW_STACK.      (* [comment removed for export] *)
Definition STRCTOR_STACK : Z := 48 + OPNEW_STACK.         (* [comment removed for export] *)
Definition ASSIGN_STACK : Z := 48 + 32 + OPNEW_STACK.     (* [comment removed for export] *)
Definition LAM_STACK : Z := 64 + ASSIGN_STACK.

(* [comment removed for export] *)
Definition vec_cells (b e c : Z) : list cell := [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 c)].
(* [comment removed for export] *)
Definition lstr_cells (capw sz p : Z) : list cell := [C8 (Z_to_bv 64 capw); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 p)].

(* [comment removed for export] *)
Definition helper_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (lo B X xn : Z) (m : mem)
    (K : word -> PState -> mem -> Prop) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres_x LB (bv_unsigned sp) X xn m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ K a0 s' m'.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vctor_K (LB : list block) (n V : Z) (b : option bptr) : word -> PState -> mem -> Prop :=
  fun _ s' m' =>
    match b with
    | None => n = 0 /\ RHEAP s' LB m' /\ rw_cells usegs m' V (vec_cells 0 0 0)
    | Some p => exists A, 0 < n /\ rblock_range A n /\ RHEAP s' ((p, A, n) :: LB) m'
                /\ rw_cells usegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
                /\ rw_cells usegs m' V (vec_cells A (A + n) (A + n))
    end.
Definition vctor_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B V : Z) (errv : word) (vj : list byte),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - VCTOR_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  rw_cells usegs m V [CB 24 vj] -> bv_unsigned sp <= V -> V + 24 <= B ->
  0 <= n < 2^26 ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 n ->
  implM usegs (Pvctor n) s
        (fun b => helper_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B V 24 m (vctor_K LB n V b))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PVCTOR) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition strctor_K (LB : list block) (T : Z) (t : bptr) : word -> PState -> mem -> Prop :=
  fun _ s' m' => exists A (jr : list byte), rblock_range A ERRSTR_BYTES /\ RHEAP s' ((t, A, ERRSTR_BYTES) :: LB) m'
                 /\ rw_cells usegs m' A [CB 54 MSG; C1 (Z_to_bv 8 0); CB 1 jr]
                 /\ rw_cells usegs m' T (lstr_cells (ERRSTR_BYTES + 1) ERRMSG_LEN A).
Definition strctor_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (lo B T : Z) (errv : word) (tj : list byte),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - STRCTOR_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  rw_cells usegs m T [CB 24 tj] -> bv_unsigned sp <= T -> T + 24 <= B ->
  a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 PMSG ->
  implM usegs (Popnew ERRSTR_BYTES) s
        (fun t => helper_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B T 24 m (strctor_K LB T t))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PSTRCTOR) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vbuf (b : option bptr) (A n : Z) (LB : list block) : Prop :=
  match b with None => A = 0 /\ n = 0 | Some p => In (p, A, n) LB /\ 0 < n end.
Definition lbx (b : option bptr) (LB : list block) : list block :=
  match b with None => LB | Some p => lb_remove p LB end.
Definition assign_K (LB : list block) (n V : Z) (b : option bptr) (A : Z) (b' : option bptr) : word -> PState -> mem -> Prop :=
  fun _ s' m' =>
    match b' with
    | None => False
    | Some p' => exists A' LB', rblock_range A' (Z.max n ERRMSG_LEN)
        /\ RHEAP s' LB' m'
        /\ (if ERRMSG_LEN <=? n then b' = b /\ A' = A /\ LB' = LB else LB' = (p', A', ERRMSG_LEN) :: lbx b LB)
        /\ rw_cells usegs m' V (vec_cells A' (A' + ERRMSG_LEN) (A' + Z.max n ERRMSG_LEN))
    end.
Definition assign_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B V A S : Z) (b : option bptr) (t : bptr) (errv : word) (old sj : list byte),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ASSIGN_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  rw_cells usegs m V (vec_cells A (A + n) (A + n)) -> bv_unsigned sp <= V -> V + 24 <= B ->
  vbuf b A n LB -> (0 < n -> rw_cells usegs m A [CB (Z.to_nat n) old]) -> 0 <= n < 2^26 ->
  In (t, S, ERRSTR_BYTES) LB -> rw_cells usegs m S [CB 54 MSG; C1 (Z_to_bv 8 0); CB 1 sj] -> (S + ERRSTR_BYTES <= A \/ A + n <= S) ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (S + ERRMSG_LEN) -> a3 = Z_to_bv 64 ERRMSG_LEN ->
  implM usegs (Passign n b) s
        (fun b' => helper_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lbx b LB) lo B V 24 m (assign_K LB n V b A b'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PASSIGN) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lam_K (LB : list block) (pl : list Z) (R : Z) (b' : option bptr) : word -> PState -> mem -> Prop :=
  fun _ s' m' => let n := zlength pl in
    match b' with
    | None => n = 0 /\ unclosed pl = false /\ RHEAP s' LB m' /\ rw_cells usegs m' R (vec_cells 0 0 0)
    | Some p' => exists A' n' e', RHEAP s' ((p', A', n') :: LB) m'
        /\ 0 < n' /\ rblock_range A' n' /\ 0 <= e' <= n'
        /\ rw_cells usegs m' R (vec_cells A' (A' + e') (A' + n'))
    end.
Definition lam_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (lo B R C D : Z) (pl : list Z) (errv : word) (rj : list byte),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - LAM_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  client_img m -> rw_cells usegs m PFALLBACK [C8 (Z_to_bv 64 PFALLBACK_VT)] ->
  rw_cells usegs m R [CB 24 rj] -> bv_unsigned sp <= R -> R + 24 <= B ->
  rw_cells usegs m C [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (zlength pl))] -> bv_unsigned sp <= C -> C + 16 <= B ->
  (R + 24 <= C \/ C + 16 <= R) ->
  bytes_at usegs m D (map (Z_to_bv 8) pl) -> Forall (fun c => 0 <= c < 256) pl ->
  rclient_range LB (bv_unsigned sp) D (zlength pl) -> (R + 24 <= D \/ D + zlength pl <= R) ->
  0 < D -> D + zlength pl <= ATOP -> zlength pl < 2^26 ->
  a0 = Z_to_bv 64 R -> a1 = Z_to_bv 64 C -> a2 = Z_to_bv 64 PFALLBACK ->
  implM usegs (Plam pl) s
        (fun b' => helper_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B R 24 m (lam_K LB pl R b'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PLAM) fc None m (seg_rom usegs)).
End CANSEC1.

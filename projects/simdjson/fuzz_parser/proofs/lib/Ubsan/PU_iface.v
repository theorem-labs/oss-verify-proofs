(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg StdioFiles.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Malloc Monad Stdio PState HarnessP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PFUZZ_ENTRY : Z := 0x26af8.     (* [comment removed for export] *)
Definition PTRUN_RET : Z := 0x269f4.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition PHARNESS_STACK : Z := 16384.
(* [comment removed for export] *)
Definition PACTIVE : Z := 0x911f8.         (* [comment removed for export] *)
Definition PACTIVE_GUARD : Z := 0x91200.   (* [comment removed for export] *)
Definition PFALLBACK : Z := 0x91270.       (* [comment removed for export] *)
Definition PFALLBACK_GUARD : Z := 0x91228. (* [comment removed for export] *)
Definition PFALLBACK_VT : Z := 0x7c7c8.    (* [comment removed for export] *)
Definition PFALLBACK_NAME : Z := 0x12b20.  (* [comment removed for export] *)
Definition PFALLBACK_DESC : Z := 0x10bce.  (* [comment removed for export] *)
Definition PVTAB_IMPL : Z := 0x7c7c8.      (* [comment removed for export] *)
Definition PVTAB_DOM : Z := 0x7c830.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition client_wr : list (Z * Z) := [(0x911f8, 0x91202); (0x91228, 0x9122a); (0x91270, 0x9129c)].

Definition harness_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside client_wr a ->
    m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None).
Lemma harness_pres_of_rheap_pres : forall LB SP m m', rheap_pres LB SP m m' -> harness_pres LB SP m m'.
Proof. intros LB SP m m' H a Ha Hc _. exact (H a Ha Hc). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vtab_impl_cells : list cell :=
  [C8 (Z_to_bv 64 0x41388); C8 (Z_to_bv 64 0x41458); C8 (Z_to_bv 64 0x41528); C8 (Z_to_bv 64 0x27ca8); C8 (Z_to_bv 64 0x29730); C8 (Z_to_bv 64 0x29814)].
Definition vtab_dom_cells : list cell :=
  [C8 (Z_to_bv 64 0x41334); C8 (Z_to_bv 64 0x27ddc); C8 (Z_to_bv 64 0x29abc); C8 (Z_to_bv 64 0x352ac); C8 (Z_to_bv 64 0x40bf8);
   C8 (Z_to_bv 64 0x40fb0); C8 (Z_to_bv 64 0x41530); C8 (Z_to_bv 64 0x41600); C8 (Z_to_bv 64 0x416c8); C8 (Z_to_bv 64 0x41730)].
(* [comment removed for export] *)
Definition PGOT_NOTHROW : Z := 0x7fb20.    (* [comment removed for export] *)
Definition PNOTHROW : Z := 0x1b8d0.        (* [comment removed for export] *)
Definition PFMIN : Z := 0x80f30.           (* [comment removed for export] *)
Definition got_nothrow_cells : list cell := [C8 (Z_to_bv 64 PNOTHROW)].
Definition fmin_cells : list cell := [C4 (Z_to_bv 64 8388608)].    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition client_img (m : mem) : Prop :=
  rw_cells usegs m PVTAB_IMPL vtab_impl_cells /\ rw_cells usegs m PVTAB_DOM vtab_dom_cells
  /\ rw_cells usegs m PGOT_NOTHROW got_nothrow_cells /\ rw_cells usegs m PFMIN fmin_cells.

Definition w0 : word := Z_to_bv 64 0.
Definition guard1 : list cell := [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
Definition fallback_cells : list cell :=
  [C8 (Z_to_bv 64 PFALLBACK_VT); C8 (Z_to_bv 64 PFALLBACK_NAME); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 PFALLBACK_DESC); C8 (Z_to_bv 64 0x1f); C4 w0].
(* [comment removed for export] *)
Definition cstat_image (m : mem) : Prop :=
  forall a : word, (0x911f8 <= bv_unsigned a < 0x91202 \/ 0x91228 <= bv_unsigned a < 0x9122a \/ 0x91270 <= bv_unsigned a < 0x9129c) -> m a = None.
(* [comment removed for export] *)
Definition cstat_built (m : mem) : Prop :=
  rw_cells usegs m PACTIVE [C8 (Z_to_bv 64 PFALLBACK)] /\ rw_cells usegs m PACTIVE_GUARD guard1
  /\ rw_cells usegs m PFALLBACK fallback_cells /\ rw_cells usegs m PFALLBACK_GUARD guard1.

Definition client_static (s : PState) (LB : list block) (m : mem) : Prop :=
  client_img m /\ ps_fa s = None /\ (cstat_image m \/ cstat_built m).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FuzzOneU.
  Variable fuzz_model : list Z -> M PState Z.      (* [comment removed for export] *)

  Definition fuzz_oneU_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : PState) (LB : list block) (AB lo : Z) (m : mem)
      (r : Z) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word) (LB' : list block),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ r = 0
      /\ mem_inv usegs m' /\ frm0 fc'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
      /\ rauxv_ok m' AB
      /\ harness_pres LB (bv_unsigned sp) m m'
      /\ RHEAP s' LB' m'
      /\ client_static s' LB' m'
      /\ ps_so s' = ps_so s
      /\ LB' = LB /\ ps_fa s' = ps_fa s.      (* [comment removed for export] *)

  Definition fuzz_oneU_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (s : PState) (LB : list block) (D : Z) (payload : list Z) (AB lo : Z) (errv : word),
      RHEAP s LB m ->
      bytes_at usegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
      rclient_range LB (bv_unsigned sp) D (zlength payload) ->
      (forall a, D <= a < D + zlength payload -> outside client_wr a) ->      (* [comment removed for export] *)
      0 < D -> D + zlength payload <= ATOP -> zlength payload < 2^26 ->
      client_static s LB m ->
      rauxv_ok m AB -> bv_unsigned sp <= AB -> bv_unsigned sp <= 2^47 ->      (* [comment removed for export] *)
      stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PHARNESS_STACK ->
      rw_cells usegs m (errno_addr tp) [C4 errv] ->
      mem_inv usegs m -> frm0 fc ->
      tp = Z_to_bv 64 RATP -> bv_unsigned sp mod 16 = 0 ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength payload) ->
      ra = Z_to_bv 64 PTRUN_RET ->
      implM usegs (fuzz_model payload) s
            (fuzz_oneU_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 PFUZZ_ENTRY) fc None m (seg_rom usegs)).
End FuzzOneU.
End CANSEC1.

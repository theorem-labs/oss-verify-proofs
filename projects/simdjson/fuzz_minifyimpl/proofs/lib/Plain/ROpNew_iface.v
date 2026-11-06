(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessM ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Definition POPNEW : Z := 0xc92d0.        (* [comment removed for export] *)
Definition POPDEL : Z := 0x6dc24.        (* [comment removed for export] *)
Definition POPDEL_SZ : Z := 0x6dc28.     (* [comment removed for export] *)
Definition POPDEL_AL : Z := 0x6dc2c.     (* [comment removed for export] *)

Definition OPNEW_STACK : Z := 16 + RMALLOC_STACK.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rheap_pres_of_munch : forall LB SP W m m',
  munch W m m' -> wmono psegs m m' ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a) ->
  rheap_pres LB SP m m'.
Proof.
  intros LB SP W m m' MU WM OUT a Ha Hc. split.
  - apply MU. unfold wa. rewrite unsigned_lit by lia. apply OUT; assumption.
  - intros Hv. apply WM. exact Hv.
Qed.

Lemma RHEAP_stack_frame : forall s LB m m' W,
  RHEAP s LB m -> munch W m m' -> wmono psegs m m' ->
  Forall (fun iv => ATOP <= fst iv) W -> RHEAP s LB m'.
Proof.
  intros s LB m m' W HP MU WM FW. eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
  eapply Forall_impl; [| exact FW]. intros iv H. left. exact H.
Qed.

Lemma rauxv_ok_stack_frame : forall m m' B W,
  rauxv_ok m B -> munch W m m' -> wmono psegs m m' ->
  Forall (fun iv => ATOP <= fst iv /\ snd iv <= B) W -> rauxv_ok m' B.
Proof.
  intros m m' B W AUX MU WM FW. eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
  eapply Forall_impl; [| exact FW]. intros [lo hi] [H1 H2]. cbn [fst snd] in *. unfold RAUXV_CELL in *. lia.
Qed.

Lemma errno_lit : bv_unsigned (Z_to_bv 64 RATP) + -164 = RERRNO.
Proof. unfold RATP, RERRNO. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma RHEAP_need_locks : forall s LB m, RHEAP s LB m -> rw_cells psegs m RNEED_LOCKS [C1 (b8 0)].
Proof. intros s LB m (st & LB0 & _ & _ & (_ & _ & (_ & NL & _) & _) & _). exact NL. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition opnew_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (p : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ exists A junk,
         a0 = Z_to_bv 64 A /\ rblock_range A n
         /\ RHEAP s' ((p, A, n) :: LB) m'
         /\ rw_cells psegs m' A [CB (Z.to_nat n) junk]
         /\ (raddr_exposed s n -> A = ptr_addr s' p).

Definition opnew_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - OPNEW_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 < n < 2^32 ->
  implM psegs (HarnessM.opnew raw_malloc ProgP.new_handler n) s
        (opnew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 POPNEW) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition opdelete_stmt_at (entry : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
  RHEAP s LB m -> In (p, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 A ->
  implM psegs (HarnessM.opdelete raw_free p) s
        (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom psegs)).

Definition opdelete_stmt : Prop := opdelete_stmt_at POPDEL /\ opdelete_stmt_at POPDEL_SZ /\ opdelete_stmt_at POPDEL_AL.
End CANSEC1.

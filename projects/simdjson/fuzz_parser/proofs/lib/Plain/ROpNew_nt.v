(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import Stdio_pure Printf_pieces.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface ROpNew.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessP ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Definition POPNEW_NT : Z := 0x57530.        (* [comment removed for export] *)
Definition POPNEW_ARR_NT : Z := 0x57564.    (* [comment removed for export] *)
Definition POPDEL_ARR : Z := 0x575a0.       (* [comment removed for export] *)
Definition OPNEW_NT_STACK : Z := 16 + OPNEW_STACK.

(* [comment removed for export] *)
Definition opnew_at_stmt (entry : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - OPNEW_NT_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 < n < 2^32 ->
  implM psegs (HarnessP.opnew raw_malloc ProgP.new_handler n) s
        (opnew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom psegs)).

Definition opnew_nt_stmt : Prop := opnew_at_stmt POPNEW_NT /\ opnew_at_stmt POPNEW_ARR_NT.
Definition opdelete_arr_stmt : Prop := opdelete_stmt_at POPDEL_ARR.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Local Ltac at_pcZ p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Local Ltac zsteps_to p := repeat (tryif at_pcZ p then fail else zstep).

Section Proofs.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.

  Theorem opdelete_arr_proof : opdelete_arr_stmt.
  Proof. exact (proj2 (proj2 (opdelete_proof FREE))). Qed.

  Theorem opnew_nt_proof : opnew_nt_stmt.
  Proof.
    pose proof (opnew_proof MALLOC) as ON. unfold opnew_stmt in ON.
    split; unfold opnew_at_stmt; intros until errv; intros HP AUX SPB ST LOA LOS ERR MI TP A0 Hn.
    all: subst tp; rewrite errno_lit in ERR; unfold RERRNO in ERR.
    all: pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    all: unfold OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK in LOS; atop_facts.
    all: apply implM_from_evt.
    all: pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU; pose proof (wmono_refl psegs m) as WM.
    all: carve_frame 16%nat ST.
    all: unfold POPNEW_NT, POPNEW_ARR_NT; zsteps_to 0x71918%Z.
    all: apply evt_done.
    all: lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP1 : RHEAP s LB mx) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]);
      assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]])
    end.
    all: clear HP AUX.
    all: eapply implM_post_evt;
      [ eapply ON with (lo := lo) (B := B); try reflexivity; rewrite ?unsigned_lit by lia;
          first [ exact HP1 | exact AUX1 | exact ST | exact MI | exact A0 | (rewrite errno_lit; unfold RERRNO; exact ERR) | exact Hn
                | (unfold OPNEW_STACK, RMALLOC_STACK; rewrite ?unsigned_lit by lia; lia)
                | (rewrite ?unsigned_lit by lia; lia) ]
      | ].
    all: cbv beta; intros p s' ms1 PO.
    all: destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
    all: rewrite ?unsigned_lit in ST2 by lia; rewrite ?unsigned_lit in HPR by lia.
    all: assert (FR2 : rw_cells psegs m2 (bv_unsigned sp + -16) [CB 8 (take 8 junk); C8 ra])
           by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
    all: lazymatch goal with |- evt _ _ (MS (mkR ?rr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
           replace (ret_pc rr) with rr by (symmetry; rpc) end.
    all: zstep; zstep; zstep.
    all: release_frame FR2 ST2 (bv_unsigned sp).
    all: apply evt_done; unfold opnew_post.
    all: do 15 eexists; exists m2, errv1; split; [reflexivity|].
    all: split; [exact MI2|]; split; [exact ST2|]; split; [exact ERR2|]; split; [exact AUX2|].
    all: split; [ eapply rheap_pres_trans; [eapply rheap_pres_of_munch; [exact MU| exact WM| intros a Ha Hc; cbn; destruct Hc as [Hc|[Hc|(bb & Hb & Hr)]]; [lia| lia|]]
                                          | eapply rheap_pres_weaken; [exact HPR| lia| intros bb Hb; exact Hb]] |].
    all: try (pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP1 Hb) as (_ & _ & _ & R4 & _); atop_facts; lia).
    all: split; [exact FAE|]; split; [exact SOE| exact RR].
  Qed.
End Proofs.
End CANSEC1.

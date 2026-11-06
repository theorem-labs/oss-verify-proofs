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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import Stdio_pure.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessP ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT}.
Section OpNew.
  Hypothesis MALLOC : rmalloc_stmt.

  Theorem opnew_proof : opnew_stmt.
  Proof.
    unfold opnew_stmt. intros until errv. intros HP AUX SPB ST LOA LOS ERR MI TP A0 Hn.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold OPNEW_STACK, RMALLOC_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    unfold HarnessP.opnew. replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    subst a0. unfold POPNEW. do 3 zstep. zstep. zstep.
    replace (n + Z.b2z (n <? 1)) with n by (destruct (Z.ltb_spec n 1); cbn; lia).
    zstep. zstep. apply evt_done.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP1 : RHEAP s LB mx) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]);
      assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]])
    end.
    clear HP AUX.
    eapply implM_bind.
    { unfold rmalloc_stmt in MALLOC.
      eapply MALLOC with (lo := lo) (B := B); try reflexivity; unfold RATP, RMALLOC_STACK; rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact AUX1 | exact ST | exact MI | lia | change (597472 + -164) with 597308; exact ERR]. }
    cbv beta. intros r s' ms1 PO.
    destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    replace (ret_pc (Z_to_bv 64 0x7b694)) with (Z_to_bv 64 0x7b694) by (symmetry; rpc).
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra])
      by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
    clear FR ST MI ERR AUX1.
    destruct r as [p|].
    - (* [comment removed for export] *)
      destruct RR as (A & junk2 & -> & BR & HP2 & BLK & HEXP). pose proof BR as (BR1 & _).
      assert (RA : 0 <= A < 2^64) by (unfold rblock_range in BR; lia).
      apply implM_ret. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      do 3 zstep. zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. unfold opnew_post.
      do 15 eexists. exists m2, errv1. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST2|]. split; [rewrite errno_lit; exact ERR2|]. split; [exact AUX2|].
      split; [eapply rheap_pres_trans; [eapply rheap_pres_of_munch; [exact MU| exact WM| intros a Ha Hc; cbn; destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|]] | eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]] |].
      { pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP1 Hb) as (_ & _ & _ & R4 & _). atop_facts. lia. }
      split; [exact FAE|]. split; [exact SOE|]. exists A, junk2. split; [reflexivity|]. split; [exact BR|]. split; [exact HP2|]. split; [exact BLK| exact HEXP].
    - (* [comment removed for export] *)
      unfold new_handler. apply implM_unr.
  Qed.

  Hypothesis FREE : rfree_stmt.

  Theorem opdelete_proof : opdelete_stmt.
  Proof.
    split; [| split]; unfold opdelete_stmt_at; intros until errv; intros HP IN AUX SPB ST LOA LOS ERR MI TP A0;
      unfold HarnessP.opdelete, POPDEL_SZ, POPDEL_AL, POPDEL; apply implM_from_evt.
    - zstep. apply evt_done. unfold rfree_stmt in FREE. eapply FREE; eassumption || reflexivity.
    - zstep. zstep. apply evt_done. unfold rfree_stmt in FREE. eapply FREE; eassumption || reflexivity.
    - zstep. zstep. apply evt_done. unfold rfree_stmt in FREE. eapply FREE; eassumption || reflexivity.
  Qed.
End OpNew.
End CANSEC1.

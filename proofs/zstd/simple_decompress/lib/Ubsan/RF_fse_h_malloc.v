(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg StdioFiles.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RF_fse_iface_m RF_fse_h_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio Malloc Harness Prog.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import frame_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT}.
Section FuzzMalloc.
  Hypothesis MALLOC : rmalloc_stmt.

  Theorem fuzz_malloc_proof : fuzz_malloc_stmt.
  Proof.
    unfold fuzz_malloc_stmt. intros until errv. intros HP AUX SPB ST LOA LOS ERR MI TP A0 Hn.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold FUZZ_MALLOC_STACK, RMALLOC_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    unfold Harness.fuzz_malloc.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    subst a0. unfold PFUZZ_MALLOC. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (n = 0) by lia. subst n. cbn [Z.ltb Z.compare].
      zstep. zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. apply implM_ret. apply evt_done.
      unfold fuzz_malloc_post.
      do 15 eexists. exists m0, errv. split; [reflexivity|].
      split; [exact MI|]. split; [exact ST|]. split; [rewrite errno_lit; exact ERR|].
      split; [eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]|].
      split; [eapply rheap_pres_of_munch; [exact MU| exact WM|]; intros a Ha Hc; cbn; destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|];
              pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb) as (_ & _ & _ & R4 & _); destruct Hr; atop_facts; lia|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]].
    - (* [comment removed for export] *)
      replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
      zstep. apply evt_done.
      assert (HP1 : RHEAP s LB m0) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
      assert (AUX1 : rauxv_ok m0 B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
      eapply implM_bind.
      { unfold rmalloc_stmt in MALLOC.
        eapply MALLOC with (lo := lo) (B := B); try reflexivity; unfold RATP, RMALLOC_STACK; rewrite ?unsigned_lit by lia;
          first [exact HP1 | exact AUX1 | exact ST | exact MI | lia | change (295416 + -164) with 295252; exact ERR]. }
      cbv beta. intros r s' ms1 PO.
      destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
      rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
      replace (ret_pc (Z_to_bv 64 186424)) with (Z_to_bv 64 186424) by (symmetry; rpc).
      assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -16) [CB 8 (take 8 junk); C8 ra])
        by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
      clear FR ST MI ERR AUX1.
      destruct r as [p|].
      + (* [comment removed for export] *)
        destruct RR as (A & junk2 & -> & BR & HP2 & BLK & HEXP). pose proof BR as (BR1 & _).
        assert (RA : 0 <= A < 2^64) by (unfold rblock_range in BR; lia).
        apply implM_ret. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
        zstep. zstep. zstep.
        release_frame FR2 ST2 (bv_unsigned sp).
        apply evt_done. unfold fuzz_malloc_post.
        do 15 eexists. exists m2, errv1. split; [reflexivity|].
        split; [exact MI2|]. split; [exact ST2|]. split; [rewrite errno_lit; exact ERR2|]. split; [exact AUX2|].
        split; [eapply rheap_pres_trans; [eapply rheap_pres_of_munch; [exact MU| exact WM| intros a Ha Hc; cbn; destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|]] | eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]]|].
        { pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb) as (_ & _ & _ & R4 & _). destruct Hr. atop_facts. lia. }
        split; [exact FAE|]. split; [exact SOE|]. exists A, junk2. split; [reflexivity|]. split; [exact BR|]. split; [exact HP2|]. split; [exact BLK| exact HEXP].
      + (* [comment removed for export] *)
        unfold new_handler. apply implM_unr.
  Qed.
End FuzzMalloc.

Section Create.
  Hypothesis FMALLOC : fuzz_malloc_stmt.

  Theorem prod_create_proof : prod_create_stmt.
  Proof.
    unfold prod_create_stmt. intros until errv. intros HP AUX SPB ST LOA LOS ERR MI TP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold PROD_CREATE_STACK, FUZZ_MALLOC_STACK, RMALLOC_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 32%nat ST.
    unfold PPROD_CREATE. do 4 zstep. zstep. zstep. zstep. zstep. apply evt_done.
    assert (HP1 : RHEAP s LB m0) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
    assert (AUX1 : rauxv_ok m0 B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
    eapply implM_post_evt.
    { unfold fuzz_malloc_stmt in FMALLOC.
      eapply FMALLOC with (lo := lo) (B := B) (n := PRODUCER_SIZE); try reflexivity; unfold RATP, FUZZ_MALLOC_STACK, RMALLOC_STACK, PRODUCER_SIZE; rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact AUX1 | exact ST | exact MI | lia | change (295416 + -164) with 295252; exact ERR]. }
    cbv beta. intros r s' ms1 PO.
    destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    replace (ret_pc (Z_to_bv 64 186004)) with (Z_to_bv 64 186004) by (symmetry; rpc).
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -32) [CB 8 (take 8 (take 16 (take 24 junk))); C8 s1; C8 s0; C8 ra])
      by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
    clear FR ST MI ERR AUX1.
    destruct r as [p|]; [| destruct RR as (RR & _); unfold PRODUCER_SIZE in RR; lia].
    destruct RR as (A & junk2 & -> & BR & HP2 & BLK & HEXP). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    assert (RA : 0 <= A < 2^64) by (atop_facts; lia).
    unfold PRODUCER_SIZE in BLK. change (Z.to_nat 16) with 16%nat in BLK.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8]%nat) in BLK; [| reflexivity]. cbn [mk_CB_cells app] in BLK.
    pose proof (munch_refl [(A, A + 16)] m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
    assert (A8 : A mod 8 = 0) by (Z.div_mod_to_equations; lia).
    zstep. fck. zstep. zstep. fck.
    zstep. zstep.
    destruct (fh_transport s' [(p, A, PRODUCER_SIZE)] LB m2 m3 _ B (bv_unsigned sp + -32) HP2 MU2 WM2
                ltac:(constructor; [right; exists (p, A, PRODUCER_SIZE); split; [left; reflexivity| unfold PRODUCER_SIZE; cbn; lia] | constructor]) ltac:(atop_facts; lia))
      as (HP3 & AUX3 & _ & HPR23).
    specialize (AUX3 AUX2).
    zstep. zstep. zstep. zstep. zstep.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evt_done. unfold prod_create_post.
    do 15 eexists. exists m3, errv1. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|]. split; [rewrite errno_lit; exact ERR2|]. split; [exact AUX3|].
    split.
    { eapply rheap_pres_trans; [eapply rheap_pres_of_munch; [exact MU| exact WM| intros a Ha Hc; cbn; destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|]]|].
      { pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb) as (_ & _ & _ & R4 & _). destruct Hr. atop_facts. lia. }
      eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]|].
      eapply rheap_pres_weaken; [exact HPR23| lia| intros b Hb; exact Hb]. }
    split; [exact FAE|]. split; [exact SOE|]. exists p, A. split; [reflexivity|]. split; [reflexivity|]. split; [exact BR|].
    split; [exact HP3|]. split; [exact BLK| exact HEXP].
  Qed.
End Create.

Section Free.
  Hypothesis FREE : rfree_stmt.

  (* [comment removed for export] *)
  Theorem prod_free_proof : prod_free_stmt.
  Proof.
    unfold prod_free_stmt. intros until errv. intros HP IN AUX SPB ST LOA LOS ERR MI TP A0.
    unfold PPROD_FREE. apply implM_from_evt. zstep. apply evt_done.
    unfold rfree_stmt in FREE. eapply FREE; eassumption || reflexivity.
  Qed.
End Free.
End CANSEC1.

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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_facts RF_fse_h_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio Malloc Harness Prog.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import ZdDctxRep ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_frame_iface RZ_dframe_iface RZ_dctx_iface_m.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import frame_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT}.
Section Free.
  Hypothesis FREE : rfree_stmt.

  Theorem zd_freedctx_proof : zd_freedctx_stmt.
  Proof.
    unfold zd_freedctx_stmt. intros until errv. intros HP DA AUX SPB ST LOA LOS ERR MI TP A0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold FREEDCTX_STACK, RFREE_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP ltac:(left; reflexivity)) as BR.
    cbn [blk_addr blk_size fst snd] in BR. pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold DCTX_SIZE in BR3, BR4, BR5.
    destruct DA as (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                    _ & _ & _ & _ & _ & [H5C H5L] & H5OK & _).
    destruct H5OK as (_ & _ & _ & _ & _ & K_CF & K_CO & K_SS & K_DL & _ & _ & K_DS & K_IB).
    h5_open ws H5L. unfold wz0 in *. subst b6 b7 b10 b13 b19 b24.
    apply implM_from_evt.
    pose proof (munch_refl [(A, A + 95992); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    subst a0. unfold PZD_FREEDCTX.
    carve_frame 48%nat ST.
    do 7 zstep.
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
    zstep. zstep. fck.
    zstep. zstep. zstep. zstep. zstep. if_true.
    zstep. zstep. zstep. zstep. zstep.
    carve_frame 32%nat ST.
    do 5 zstep. zstep. if_true.
    do 7 zstep.
    release_frame FR0 ST (bv_unsigned sp + -48).
    zstep. zstep. zstep. zstep. zstep. if_true.
    zstep. zstep. zstep. if_true. zstep. if_true.
    zstep. zstep.
    apply evt_done.
    lazymatch type of MU with munch _ _ ?mk =>
      destruct (fh_transport s [(p, A, DCTX_SIZE)] LB m mk _ B (bv_unsigned sp) HP MU WM
                  ltac:(constructor; [right; exists (p, A, DCTX_SIZE); split; [left; reflexivity| unfold DCTX_SIZE; cbn; lia]
                        | constructor; [left; cbn; atop_facts; lia| constructor]]) ltac:(atop_facts; lia))
        as (HP1 & AUX1 & _ & HPR01)
    end.
    specialize (AUX1 AUX). cbn [app] in HP1.
    pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP1) as ND1.
    pose proof (lb_remove_hd p (p, A, DCTX_SIZE) _ eq_refl ND1) as LBR1.
    eapply implM_post_evt.
    { unfold rfree_stmt, RFREE_SYM in FREE.
      eapply FREE with (lo := lo) (B := B) (A := A) (n := DCTX_SIZE); try reflexivity; unfold RATP, RFREE_STACK; rewrite ?unsigned_lit by lia;
        first [exact HP1 | left; reflexivity | exact AUX1 | exact ST | exact MI | lia | change (295416 + -164) with 295252; exact ERR]. }
    cbv beta. intros [] s' ms1 PO.
    destruct PO as (u0 & u1 & u2 & ra0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m5 & -> & MI5 & ST5 & ERR5 & AUX5 & HPR5 & FAE5 & SOE5 & HP5).
    rewrite LBR1 in HPR5, HP5.
    rewrite ?unsigned_lit in ST5 by lia. rewrite ?unsigned_lit in HPR5 by lia. rewrite errno_lit in ERR5.
    replace (ret_pc (Z_to_bv 64 84840)) with (Z_to_bv 64 84840) by (symmetry; rpc).
    assert (FR5 : rw_cells usegs m5 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rheap_pres_rw_cells; [exact HPR5| exact FR| left; cbn; lia]).
    zstep. do 6 zstep. zstep. zstep.
    release_frame FR5 ST5 (bv_unsigned sp).
    apply evt_done. unfold zd_freedctx_post.
    do 14 eexists. exists m5. split; [reflexivity|].
    split; [exact MI5|]. split; [exact ST5|]. split; [rewrite errno_lit; exact ERR5|]. split; [exact AUX5|].
    split.
    { eapply rheap_pres_trans; [exact HPR01|]. eapply rheap_pres_weaken; [exact HPR5| lia| intros bq Hb; exact Hb]. }
    split; [exact FAE5|]. split; [exact SOE5| exact HP5].
  Qed.
End Free.
End CANSEC1.

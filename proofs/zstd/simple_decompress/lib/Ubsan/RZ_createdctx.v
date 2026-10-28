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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RF_fse_h_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio Malloc Harness Prog.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Bytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import frame_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun ZdDctxRep ZdWalkKit ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_frame_iface RZ_dframe_iface RZ_dctx_iface_m.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)
Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR.
  change (256 ^ Z.of_nat 4) with 4294967296 in HR. rewrite <- bytes_le_to_Z_le_val in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma cb4_as_c4 : forall segs m A pre j post,
  rw_cells segs m A (pre ++ CB 4 j :: post) -> exists w, rw_cells segs m A (pre ++ C4 w :: post).
Proof.
  intros segs m A pre j post H. exists (le_bytes_to_word j).
  pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [WF1 [WFJ WF2]]. cbn in WFJ.
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact WF1|]. split; [exact I| exact WF2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite le4_of_bytes by exact WFJ. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac wordify_go H segs m A pre rest :=
  lazymatch rest with
  | CB 8 ?j :: ?post =>
      let w := fresh "w" in let H' := fresh "WH" in
      destruct (cb8_as_c8 segs m A pre j post H) as [w H']; clear H; rename H' into H;
      let pre' := eval cbn [app] in (pre ++ [C8 w]) in wordify_go H segs m A pre' post
  | CB 4 ?j :: ?post =>
      let w := fresh "w" in let H' := fresh "WH" in
      destruct (cb4_as_c4 segs m A pre j post H) as [w H']; clear H; rename H' into H;
      let pre' := eval cbn [app] in (pre ++ [C4 w]) in wordify_go H segs m A pre' post
  | ?c :: ?post => let pre' := eval cbn [app] in (pre ++ [c]) in wordify_go H segs m A pre' post
  | nil => cbn [app] in H
  end.
Ltac wordify H := lazymatch type of H with rw_cells ?segs ?m ?A ?cs => wordify_go H segs m A (@nil cell) cs end.

Section CANSEC1. Context {rc : runConstT}.
Section Create.
  Hypothesis MALLOC : rmalloc_stmt.

  Theorem zd_createdctx_proof : zd_createdctx_stmt.
  Proof.
    unfold zd_createdctx_stmt. intros until errv. intros HP AUX SPB ST LOA LOS ERR MI TP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold CREATEDCTX_STACK, RMALLOC_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    unfold PZD_CREATEDCTX. do 6 zstep. apply evt_done.
    assert (HP1 : RHEAP s LB m1) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
    assert (AUX1 : rauxv_ok m1 B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
    eapply implM_post_evt.
    { unfold rmalloc_stmt in MALLOC.
      eapply MALLOC with (lo := lo) (B := B) (n := DCTX_SIZE); try reflexivity; unfold RATP, RMALLOC_STACK, DCTX_SIZE; rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact AUX1 | exact ST | exact MI | lia | change (295416 + -164) with 295252; exact ERR]. }
    cbv beta. intros r s' ms1 PO.
    destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    replace (ret_pc (Z_to_bv 64 84412)) with (Z_to_bv 64 84412) by (symmetry; rpc).
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra])
      by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
    clear FR ST MI ERR AUX1.
    assert (HPR02 : rheap_pres LB (bv_unsigned sp) m m2).
    { eapply rheap_pres_trans; [eapply rheap_pres_of_munch; [exact MU| exact WM| intros a Ha Hc; cbn; destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|]] | eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]].
      pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb) as (_ & _ & _ & R4 & _). destruct Hr. atop_facts. lia. }
    destruct r as [p|].
    - (* [comment removed for export] *)
      destruct RR as (A & junk2 & -> & BR & HP2 & BLK & HEXP). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
      unfold DCTX_SIZE in BLK, BR3, BR4, BR5. change (Z.to_nat 95992) with 95992%nat in BLK.
      assert (RA : 0 <= A < 2^64) by (atop_facts; lia).
      (* [comment removed for export] *)
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [32; 29856; 484; 65568; 52]%nat) in BLK; [| reflexivity].
      cbn [mk_CB_cells app] in BLK.
      apply (proj1 (rw_cells_app _ _ _ [CB 32 _] _)) in BLK. destruct BLK as [BK0 BLK]. cbn [cells_size csize Nat.add] in BLK.
      apply (proj1 (rw_cells_app _ _ _ [CB 29856 _] _)) in BLK. destruct BLK as [BKE BLK]. cbn [cells_size csize Nat.add] in BLK.
      apply (proj1 (rw_cells_app _ _ _ [CB 484 _] _)) in BLK. destruct BLK as [BK1 BLK]. cbn [cells_size csize Nat.add] in BLK.
      apply (proj1 (rw_cells_app _ _ _ [CB 65568 _] _)) in BLK. destruct BLK as [BKX BK3]. cbn [cells_size csize Nat.add] in BK3.
      replace (Z.of_nat 29856) with 29856 in * by (vm_compute; reflexivity).
      replace (Z.of_nat 65568) with 65568 in * by (vm_compute; reflexivity).
      replace (A + Z.of_nat 32) with (A + 32) in * by lia.
      replace (A + 32 + 29856) with (A + 29888) in * by lia.
      replace (A + 29888 + Z.of_nat 484) with (A + 30372) in * by lia.
      replace (A + 30372 + 65568) with (A + 95940) in * by lia.
      apply stk_of_rw_cells in BKE. cbn [cells_size csize Nat.add] in BKE. replace (Z.of_nat 29856) with 29856 in BKE by (vm_compute; reflexivity).
      replace (A + 32 + 29856) with (A + 29888) in BKE by lia.
      apply stk_of_rw_cells in BKX. cbn [cells_size csize Nat.add] in BKX. replace (Z.of_nat 65568) with 65568 in BKX by (vm_compute; reflexivity).
      replace (A + 30372 + 65568) with (A + 95940) in BKX by lia.
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8]%nat) in BK0; [| reflexivity]. cbn [mk_CB_cells app] in BK0.
      apply (rw_cells_split_CB _ _ _ [] _ _ _
               [8;8;8;8;8; 48; 8;8;4;4;4;4; 88;
               8; 4;4; 4;4; 8;8;8;8;8;8;8; 4;4; 8;8; 4;4;4;4; 8; 8; 4;4; 8;8; 8;8;8;8;8;8;8; 4;4;4;4; 8;8;8; 8;8; 4]%nat) in BK1; [| reflexivity].
      cbn [mk_CB_cells app] in BK1.
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [20; 8;8;8;8]%nat) in BK3; [| reflexivity].
      cbn [mk_CB_cells app] in BK3.
      pose proof (munch_refl [(A, A + 95992)] m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
      zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
      zstep. zstep. fck.
      do 37 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => try rename mm into m0 end.
      wordify BK0.
      wordify BK3.
      wordify BK1.
      apply (proj1 (rw_cells_app _ _ _ [C8 _; C8 _; C8 _; C8 _; C8 _] _)) in BK1. destruct BK1 as [H1 BK1]. cbn [cells_size csize Nat.add] in BK1.
      apply (proj1 (rw_cells_app _ _ _ [CB 48 _] _)) in BK1. destruct BK1 as [FPC BK1]. cbn [cells_size csize Nat.add] in BK1.
      apply (proj1 (rw_cells_app _ _ _ [C8 _; C8 _; C4 _; C4 _; C4 _; C4 _] _)) in BK1. destruct BK1 as [H3 BK1]. cbn [cells_size csize Nat.add] in BK1.
      apply (proj1 (rw_cells_app _ _ _ [CB 88 _] _)) in BK1. destruct BK1 as [XSC H5S]. cbn [cells_size csize Nat.add] in H5S.
      replace (A + 29888 + Z.of_nat 40) with (A + 29928) in * by lia.
      replace (A + 29928 + Z.of_nat 48) with (A + 29976) in * by lia.
      replace (A + 29976 + Z.of_nat 32) with (A + 30008) in * by lia.
      replace (A + 30008 + Z.of_nat 88) with (A + 30096) in * by lia.
      set (WS := [w15; Z_to_bv 64 0; Z_to_bv 64 0; w16; w17; w18; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; w19; w20; Z_to_bv 64 0; Z_to_bv 64 1; w21;
                  Z_to_bv 64 0; Z_to_bv 64 0; w22; Z_to_bv 64 0; Z_to_bv 64 0; w23; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                  Z_to_bv 64 0; Z_to_bv 64 0; w24; Z_to_bv 64 134217729; w25; Z_to_bv 64 0; w26; w27; w28; w29; Z_to_bv 64 0; Z_to_bv 64 0; w30;
                  w31; w32; w33; w34; w35; w36]).
      assert (H5C : rw_cells usegs m0 (A + 30096) (h5_cells WS)).
      { eapply rw_cells_recell; [exact H5S | unfold WS; cbn; tauto | unfold WS; reflexivity]. }
      assert (H5OK : h5_frame_ok WS).
      { unfold h5_frame_ok, WS, wz0. cbv beta iota delta [wnth nth H5_format H5_forceIgnoreChecksum H5_refMultipleDDicts H5_maxBlockSizeParam H5_customAlloc
          H5_customFree H5_customOpaque H5_staticSize H5_ddictLocal H5_ddict H5_dictUses H5_ddictSet H5_inBuff]. repeat split; reflexivity. }
      assert (DA : dctx_any m0 A).
      { eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, WS, _, _, _, _, _.
        split; [exact BK0|]. split; [exact H1|]. split; [split; [exact FPC| reflexivity]|]. split; [exact H3|]. split; [split; [exact XSC| reflexivity]|].
        split; [split; [exact H5C| reflexivity]|]. split; [exact H5OK|]. split; [exact BK3|]. split; [exact BKE| exact BKX]. }
      clear H5S H5C BK0 H1 FPC H3 XSC BK3 BKE BKX.
      destruct (fh_transport s' [(p, A, DCTX_SIZE)] LB m2 m0 _ B (bv_unsigned sp + -16) HP2 MU2 WM2
                  ltac:(constructor; [right; exists (p, A, DCTX_SIZE); split; [left; reflexivity| unfold DCTX_SIZE; cbn; lia] | constructor]) ltac:(atop_facts; lia))
        as (HP3 & AUX3 & _ & HPR23).
      specialize (AUX3 AUX2).
      zstep. zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. unfold zd_createdctx_post.
      do 15 eexists. exists m0, errv1. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST2|]. split; [rewrite errno_lit; exact ERR2|]. split; [exact AUX3|].
      split.
      { eapply rheap_pres_trans; [exact HPR02|]. eapply rheap_pres_weaken; [exact HPR23| lia| intros b Hb; exact Hb]. }
      split; [exact FAE|]. split; [exact SOE|]. exists A. split; [reflexivity|]. split; [exact BR|]. split; [exact HP3|]. split; [exact DA| exact HEXP].
    - (* [comment removed for export] *)
      destruct RR as (-> & HP2).
      zstep. if_true. zstep. zstep. zstep. zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. unfold zd_createdctx_post.
      do 15 eexists. exists m2, errv1. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST2|]. split; [rewrite errno_lit; exact ERR2|]. split; [exact AUX2|].
      split; [exact HPR02|]. split; [exact FAE|]. split; [exact SOE|]. split; [reflexivity| exact HP2].
  Qed.
End Create.
End CANSEC1.

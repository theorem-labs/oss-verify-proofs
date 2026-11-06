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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMalloc_iface RYajlRep RYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlParser YajlFactsBuf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : RawAlloc.PState -> list MallocBlocks.block -> (word -> option byte) -> Model -> Prop.

(* [comment removed for export] *)
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

Lemma ybuf_err_spec : ybuf_err_stmt.
Proof.
  unfold ybuf_err_stmt. intros until m. intros BC STR B0 MI A0.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ BC) as BCB. cbn [cells_size csize] in BCB.
  subst a0. unfold RY_BUF_ERR, wz in *.
  step. if_cases K0; zify_cond K0. 1:{ kill K0. }
  step. rewrite ysx32_small by lia. step.
  unfold ybuf_err_rpost. finish. all: reflexivity.
Qed.

Lemma ybuf_len_spec : ybuf_len_stmt.
Proof.
  unfold ybuf_len_stmt. intros until m. intros BS ST B0 STK LO BLO MI A0.
  destruct BS as (BC & DZ & RL & RU). unfold buf_cells in BC. rewrite ST in BC. cbn [buf_state_code] in BC.
  pose proof (rw_cells_bound _ _ _ _ BC) as BCB. cbn [cells_size csize Nat.add] in BCB.
  subst a0. unfold RY_BUF_LEN, RY_BUF_SMALL_STACK, SIZEOF_BUF, wz in *.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  step. carve_frame 16%nat STK.
  step.
  step. if_cases K0; zify_cond K0. 1:{ kill K0. }
  step. step. if_cases K1; zify_cond K1. 1:{ kill K1. }
  step. rewrite !ysx32_small by lia.
  step. step. step.
  release_frame FR STK (bv_unsigned sp).
  unfold ybuf_len_rpost. finish.
  - reflexivity.
  - split; [| split; [exact DZ| lia]]. unfold buf_cells. rewrite ST. cbn [buf_state_code]. assumption.
Qed.

Lemma ybuf_data_spec : ybuf_data_stmt.
Proof.
  unfold ybuf_data_stmt. intros until m. intros BS ST B0 STK LO BLO MI A0.
  destruct BS as (BC & DZ & RL & RU). unfold buf_cells in BC. rewrite ST in BC. cbn [buf_state_code] in BC.
  pose proof (rw_cells_bound _ _ _ _ BC) as BCB. cbn [cells_size csize Nat.add] in BCB.
  subst a0. unfold RY_BUF_DATA, RY_BUF_SMALL_STACK, SIZEOF_BUF, wz in *.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  step. carve_frame 16%nat STK.
  step.
  step. if_cases K0; zify_cond K0. 1:{ kill K0. }
  step. step. if_cases K1; zify_cond K1. 1:{ kill K1. }
  step.
  step. step. step.
  release_frame FR STK (bv_unsigned sp).
  unfold ybuf_data_rpost. finish.
  - reflexivity.
  - split; [| split; [exact DZ| lia]]. unfold buf_cells. rewrite ST. cbn [buf_state_code]. assumption.
Qed.
(* [comment removed for export] *)
Lemma ybuf_clear_spec : ybuf_clear_stmt.
Proof.
  unfold ybuf_clear_stmt. intros until m. intros BS BD ST BI B0 STK LO BLO DSEP MI A0.
  destruct BS as (BC & DZ & RL & RU). unfold buf_cells in BC. rewrite ST in BC. cbn [buf_state_code] in BC.
  pose proof (rw_cells_bound _ _ _ _ BC) as BCB. cbn [cells_size csize Nat.add] in BCB.
  subst a0. unfold RY_BUF_CLEAR, RY_BUF_SMALL_STACK, SIZEOF_BUF, wz in *.
  pose proof (wmono_refl rsegs m) as WM.
  destruct BI as (I1 & I2 & I3 & I4 & I5 & I6).
  destruct (yb_data b) as [dp|] eqn:HD; cbn [app];
    [pose proof (munch_refl [(lo, bv_unsigned sp); (B + 8, B + 12); (D, D + 1)] m) as MU
    |pose proof (munch_refl [(lo, bv_unsigned sp); (B + 8, B + 12)] m) as MU].
  - (* [comment removed for export] *)
    assert (D0 : D <> 0) by (intros E; apply DZ in E; congruence).
    specialize (DSEP ltac:(congruence)). destruct DSEP as [DLO DSB].
    specialize (I5 ltac:(congruence)).
    unfold buf_data in BD. rewrite HD in BD. destruct BD as (UL0 & junk0 & DC).
    pose proof (rw_cells_bound _ _ _ _ DC) as DCB. cbn [cells_size csize Nat.add] in DCB.
    pose proof (rw_cells_merge rsegs _ D [] _ [] ltac:(rewrite app_nil_r; exact DC)) as DM. cbn [app] in DM.
    assert (DM' : rw_cells rsegs m D [CB (Z.to_nat (yb_len b))
              (cells_bytes [CB (Z.to_nat (yb_used b)) (zbytes (yb_bytes b)); C1 (Z_to_bv 8 0);
                           CB (Z.to_nat (yb_len b - yb_used b - 1)) junk0])]).
    { destruct DC as [[Hwf _] _].
      eapply rw_cells_recast; [exact DM| | reflexivity|].
      - cbn [cells_wf cell_wf]. split; [|exact I]. rewrite (cells_bytes_length _ Hwf). cbn [cells_size csize]. lia.
      - cbn [cells_size csize]. lia. }
    clear DM DC.
    step. carve_frame 16%nat STK.
    step.
    step. if_cases K0; zify_cond K0. 1:{ kill K0. }
    step. step. if_cases K1; zify_cond K1. 1:{ kill K1. }
    step. step.
    step. if_cases K2; zify_cond K2. 1:{ kill K2. }
    (* [comment removed for export] *)
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (rw_cells_CB_store_ok rsegs mx D _ _ 1%nat DM' ltac:(lia)) as SOK end.
    step.
    match type of DM' with rw_cells _ ?mx _ _ =>
      pose proof (rw_cells_CB_prefix_write rsegs mx D _ _ (le1 (Z_to_bv 64 0)) DM' ltac:(cbn; lia)) as DC' end.
    clear DM'. store_done.
    step. step. step.
    release_frame FR STK (bv_unsigned sp).
    unfold ybuf_clear_rpost. rewrite HD. cbn [app]. finish.
    + split; [| split; [cbn [yb_data buf_cleared]; rewrite HD; exact DZ| cbn; lia]]. unfold buf_cells, buf_cleared. cbn. exact BC.
    + unfold buf_data, buf_cleared. cbn [yb_data yb_used yb_len yb_bytes]. rewrite HD. split; [lia|].
      destruct DC' as [[Hwf' HB'] HW']. cbn [cells_wf cell_wf] in Hwf'. destruct Hwf' as (_ & Hl2 & _).
      eexists. split; [split|].
      * cbn [cells_wf cell_wf]. split; [reflexivity|]. split; [exact I|]. split; [|exact I].
        rewrite Hl2, length_le1. lia.
      * revert HB'. rewrite !length_le1. cbn [cells_bytes cbytes zbytes map app]. intros HB'.
        replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] in HB' by reflexivity. exact HB'.
      * revert HW'. rewrite !length_le1. cbn [cells_size csize]. intros HW'.
        replace (Z.to_nat 0 + (1 + (Z.to_nat (yb_len b - 0 - 1) + 0)))%nat with (1 + (Z.to_nat (yb_len b) - 1 + 0))%nat by lia.
        exact HW'.
  - (* [comment removed for export] *)
    assert (D0 : D = 0) by (apply DZ; reflexivity). subst D.
    step. carve_frame 16%nat STK.
    step.
    step. if_cases K0; zify_cond K0. 1:{ kill K0. }
    step. step. if_cases K1; zify_cond K1. 1:{ kill K1. }
    step. step.
    step. if_cases K2; zify_cond K2. 2:{ kill K2. }
    step. step. step.
    release_frame FR STK (bv_unsigned sp).
    unfold ybuf_clear_rpost. rewrite HD. cbn [app]. finish.
    + split; [| split; [cbn [yb_data buf_cleared]; rewrite HD; exact DZ| cbn; lia]]. unfold buf_cells, buf_cleared. cbn. exact BC.
    + unfold buf_data, buf_cleared. cbn [yb_data]. rewrite HD. exact I.
Qed.
End S.
End RC__1.

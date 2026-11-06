(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Cells Step RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_Pahif U_PKit U_Pahbe V_PH51p U_vevaj RU_ssdc U_Leaves U_PDhsq ImgU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_La7nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Cov8m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahbe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_vevaj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RU_ssdc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Leaves OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PDhsq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.

Module U_PHaq6.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_Pahif U_PKit V_PH51p ImgU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_La7nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Cov8m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Hypothesis HVE : vep_error_stmt.

  #[using="HVE"] Lemma PH_SkipAttribute : handler_stmt S_SkipAttribute.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    (* [comment removed for export] *)
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312); (pe_sp E, pe_sp E + 16); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312); (pe_sp E, pe_sp E + 16); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
    assert (EVSC : h_vsc (pe_H E) = h_sp (pe_H E) + 2240) by reflexivity.
    assert (EVS : VEPERR_STACK = 48) by reflexivity.
    assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
    (* [comment removed for export] *)
    assert (EXIT_E : forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E, pe_sp E + 16); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m mc ->
      wmono rsegs m mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (x_v x) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E) (pframe E j0 j8 j16 j24) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) ->
      henv_ok LayoutPU VIU (pe_H E) mc -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      realizes rsegs (mkCfg (loop_ms E 0x1a950 (pe_e E) ra' t0' t1' t2' (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) md) T).
    { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc HENVc STKc. unfold loop_ms, lms.
      clear VEPC FR DBY STK HENV MI.
      unfold vep_cells in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
      apply rz_go; [exact MDH| exact MDL|].
      zstep. zstep.
      apply rz_stop.
      eapply (KL (PST (pe_e E) S_SkipAttribute (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
      2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MUc WMc WZ). }
      2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
      2:{ eapply hstep_stores; [exact MUc | | eapply parse_window_mapped; [exact PE0| exact STKc| exact FRc]
                               | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
          w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
      2:{ psimp. intros H. exfalso. clear - H. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV MUc WMc WZ.
      - (* [comment removed for export] *) clear - VERP PLE. unfold pe_e, pe_N in *. lia.
      - (* [comment removed for export] *) revert OUT PLE. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. unfold pe_e, pe_N in *. intros; lia. }
    (* [comment removed for export] *)
    assert (INTAG : forall (q' : Z) (b : byte) (ra' t0' t1' t2' a0' a1' a2' a3' s8' a5' a6' a7' t3' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E, pe_sp E + 16); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m mc ->
      wmono rsegs m mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (x_v x) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E) (pframe E j0 j8 j16 j24) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) ->
      henv_ok LayoutPU VIU (pe_H E) mc -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      x_p x <= q' -> q' < pe_e E -> nth_error (pe_inp E) (Z.to_nat (q' - pe_DATA E)) = Some b ->
      vct_xmlname (bv_unsigned b) = false ->
      realizes rsegs (mkCfg (loop_ms E 0x1ad64 q' ra' t0' t1' t2' a0' a1' a2' a3' (Z_to_bv 64 (stU S_InTag)) a5' a6' a7' s8' t3' t4' t5' t6' mc) md) T).
    { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc HENVc STKc LQ QE Hnth NX. unfold loop_ms, lms.
      clear VEPC FR DBY STK HENV MI.
      unfold vep_cells in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
      pose proof (ainv_stores E A m mc md _ _ PE0 AINV MUc WMc WZ) as AINVc.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU2. pose proof (wmono_refl rsegs mc) as WM2.
      assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                            [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH| exact MDL|].
      zstep. zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
          by (eapply (henv_stores E A _ _ md _ _ PE0 AINVc MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENVc])
      end.
      eapply (KL (PST q' S_InTag (fupd (x_v x) Fstate (stU S_InTag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
      2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MUc WMc WZ). }
      2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
      2:{ eapply hstep_stores; [exact MUc | | eapply parse_window_mapped; [exact PE0| exact STKc| exact FRc]
                               | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
          w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
      2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST.
          destruct (Z.eq_dec q' (x_p x)) as [EQ|NE].
          - (* [comment removed for export] *)
            unfold look. rewrite <- EQ, Hnth, NX. clear - EQ. lia.
          - destruct (vct_xmlname (look E x)); clear - NE LQ QE; lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV MUc WMc WZ.
      - (* [comment removed for export] *) clear - VERP LQ. lia.
      - (* [comment removed for export] *) clear - QE. unfold pe_e, pe_N in *. lia.
      - (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia. }
    (* [comment removed for export] *)
    assert (EXIT_T : forall (q' : Z) (b : byte) (ra' t0' t1' t2' a0' a3' a5' a6' a7' t3' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E, pe_sp E + 16); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m mc ->
      wmono rsegs m mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (x_v x) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E) (pframe E j0 j8 j16 j24) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) ->
      henv_ok LayoutPU VIU (pe_H E) mc -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      x_p x <= q' -> q' < pe_e E -> nth_error (pe_inp E) (Z.to_nat (q' - pe_DATA E)) = Some b ->
      vct_xmlname (bv_unsigned b) = false ->
      realizes rsegs (mkCfg (loop_ms E 0x1aacc q' ra' t0' t1' t2' a0' (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 (vct (bv_unsigned b))) a3' (Z_to_bv 64 (stU S_InTag)) a5' a6' a7'
                                     (Z_to_bv 64 (stU S_TagError)) t3' t4' t5' t6' mc) md) T).
    { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc HENVc STKc LQ QE Hnth NX. unfold loop_ms, lms.
      clear VEPC FR DBY STK HENV MI.
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      pose proof (vct_range (bv_unsigned b)) as VR.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1.
      { apply rz_stop. eapply INTAG; [exact MUc| exact WMc| exact MIc| exact VEPCc| exact FRc| exact DBYc| exact HENVc| exact STKc| exact LQ| exact QE| exact Hnth| exact NX]. }
      (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2.
      { apply rz_stop. eapply INTAG; [exact MUc| exact WMc| exact MIc| exact VEPCc| exact FRc| exact DBYc| exact HENVc| exact STKc| exact LQ| exact QE| exact Hnth| exact NX]. }
      (* [comment removed for export] *)
      zstep. zstep. if_cases K3; zify_cond K3.
      - (* [comment removed for export] *)
        zstep. zstep. if_cases K4; zify_cond K4.
        { apply rz_stop. eapply INTAG; [exact MUc| exact WMc| exact MIc| exact VEPCc| exact FRc| exact DBYc| exact HENVc| exact STKc| exact LQ| exact QE| exact Hnth| exact NX]. }
        (* [comment removed for export] *)
        unfold vep_cells in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
        zstep. zstep. zstep. zstep.
        hide STKc. hide_slow.
        call_fr (HVE (pe_VEP E) (x_v x) (x_tag x) (x_q x) (pe_H E) (pe_lo E)) by idtac.
        1:{ reflexivity. }
        1:{ unfold vep_cells. rewrite STATE. exact VEPCc. }
        1:{ exact TAG. }
        1:{ exact PADS. }
        1:{ exact (proj1 BASE). }
        1:{ exact HENVc. }
        1:{ exact (proj1 PE0). }
        1:{ eapply (img_stores E A m mc md _ _ PE0 AINV MUc WZ). exact IMG. }
        1:{ exact VEPlo. }
        1:{ apply mod8_of_mod16. exact VEP16. }
        1:{ clear - VEPhi. lia. }
        1:{ unhide STKc. rewrite unsigned_lit by exact SPR. exact STKc. }
        1:{ rewrite unsigned_lit by exact SPR. rewrite EVS, PSP. clear - LOP. lia. }
        1:{ exact CEIL. }
        1:{ rewrite unsigned_lit by exact SPR. rewrite PSP. clear. lia. }
        1:{ exact MIc. }
        clear STKc. unhide_slow.
        try match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
        rename PC into HENV1. rename POST into STK1.
        match goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          pose proof (ainv_stores E A m m1 md _ _ PE0 AINV MUc WMc WZ) as AINV1;
          pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m1) as MU3; pose proof (wmono_refl rsegs m1) as WM3 end.
        assert (WZ3 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                              [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        apply rz_stop.
        match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
          assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
            by (eapply (henv_stores E A _ _ md _ _ PE0 AINV1 MU3 WM3 WZ3); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENV1])
        end.
        eapply (KL (PST q' S_TagError (fupd (x_v x) Fstate (stU S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
        2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MUc WMc WZ). }
        2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
        2:{ eapply hstep_stores; [exact MUc | | eapply parse_window_mapped; [exact PE0| exact STK1| exact FRc]
                                 | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
            w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
        2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST.
            destruct (Z.eq_dec q' (x_p x)) as [EQ|NE].
            - unfold look. rewrite <- EQ, Hnth, NX. clear - EQ. lia.
            - destruct (vct_xmlname (look E x)); clear - NE LQ QE; lia. }
        apply Build_pinv; psimp; pinv_close PE0 AINV MUc WMc WZ.
        + (* [comment removed for export] *) clear - VERP LQ. lia.
        + (* [comment removed for export] *) clear - QE. unfold pe_e, pe_N in *. lia.
        + (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
      - (* [comment removed for export] *)
        clear K1 K2.
        unfold vep_cells in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
        pose proof (ainv_stores E A m mc md _ _ PE0 AINV MUc WMc WZ) as AINVc.
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU2. pose proof (wmono_refl rsegs mc) as WM2.
        assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                              [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
        zstep. zstep. if_cases KT; zify_cond KT.
        { exfalso. revert KT QE Dhi CV. clear. unfold pe_e, pe_N. intros. lia. }
        clear KT.
        zstep. zstep. zstep. zstep. zstep. zstep.
        apply rz_stop.
        match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
          assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
            by (eapply (henv_stores E A _ _ md _ _ PE0 AINVc MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENVc])
        end.
        eapply (KL (PST (q' + 1) S_AttrDelim (fupd (x_v x) Fstate (stU S_AttrDelim)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
        2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MUc WMc WZ). }
        2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
        2:{ eapply hstep_stores; [exact MUc | | eapply parse_window_mapped; [exact PE0| exact STKc| exact FRc]
                                 | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
            w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
        2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST.
            destruct (vct_xmlname (look E x)); clear - LQ QE; lia. }
        apply Build_pinv; psimp; pinv_close PE0 AINV MUc WMc WZ.
        + (* [comment removed for export] *) clear - VERP LQ. lia.
        + (* [comment removed for export] *) clear - QE. unfold pe_e, pe_N in *. lia.
        + (* [comment removed for export] *)
          intros _ [X|X]; [discriminate X|]. exfalso; apply X. revert VA AVSB; clear; destruct (x_va x); [| reflexivity].
          intros VA AVSB. exfalso. exact (AVSB (proj1 VA)).
        + (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia. }
    (* [comment removed for export] *)
    assert (LOOP : forall (k : nat) (q : Z) (ra' t0' t1' t2' a1' a2' a3' a5' a6' a7' t3' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E, pe_sp E + 16); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m mc ->
      wmono rsegs m mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (x_v x) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E) (pframe E j0 j8 j16 j24) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) ->
      henv_ok LayoutPU VIU (pe_H E) mc -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      q + Z.of_nat k = pe_e E -> x_p x <= q -> q < pe_e E ->
      evt rsegs (rz_at rsegs md T)
          (loop_ms E 0x1a928 q ra' t0' t1' t2' (Z_to_bv 64 (pe_e E - q)) a1' a2' a3' (Z_to_bv 64 (stU S_InTag)) a5' a6' a7' (Z_to_bv 64 (stU S_TagError)) t3' t4' t5' t6' mc)).
    { induction k as [|k IH]; intros until mc; intros MUc WMc MIc VEPCc FRc DBYc HENVc STKc Hk LQ QE.
      { exfalso. clear - Hk QE. lia. }
      unfold loop_ms, lms.
      pose proof VEPCc as VEPCk. pose proof FRc as FRk.
      clear VEPC FR DBY STK HENV MI.
      unfold vep_cells in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
      (* [comment removed for export] *)
      zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT LQ VERP Dlo. lia. } clear KT.
      (* [comment removed for export] *)
      destruct (payload_read rsegs E mc q DBYc ltac:(clear - LQ VERP; lia) QE) as (b & Hnth & RDP).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta.
      (* [comment removed for export] *)
      zstep. zstep.
      replace (Z.shiftl (bv_unsigned b) 1) with (2 * bv_unsigned b) by (rewrite Z.shiftl_mul_pow2; clear; lia).
      pose proof (vct_readU mc (bv_unsigned b) _ MIc BR eq_refl) as RDV. unfold wa in RDV.
      zstep. clear RDV. cbv beta. rewrite zx16_vct.
      pose proof (vct_range (bv_unsigned b)) as VR.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *)
        apply rz_stop. eapply (EXIT_T q b); [exact MUc| exact WMc| exact MIc| exact VEPCk| exact FRk| exact DBYc| exact HENVc| exact STKc
                                            | exact LQ| exact QE| exact Hnth| unfold vct_xmlname; rewrite K1; reflexivity]. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      - (* [comment removed for export] *)
        replace (pe_e E - q + -1) with (pe_e E - (q + 1)) by (clear; lia).
        eapply (IH (q + 1)); [exact MUc| exact WMc| exact MIc| exact VEPCk| exact FRk| exact DBYc| exact HENVc| exact STKc
                             | clear - Hk; lia| clear - LQ; lia| clear - K2 Hk QE; lia].
      - (* [comment removed for export] *)
        apply rz_stop. replace (pe_e E - q + -1) with 0 by (clear - K2; lia). replace (q + 1) with (pe_e E) by (clear - K2; lia).
        eapply EXIT_E; [exact MUc| exact WMc| exact MIc| exact VEPCk| exact FRk| exact DBYc| exact HENVc| exact STKc]. }
    (* [comment removed for export] *)
    apply rz_go; [exact MDH| exact MDL|].
    zstep. if_cases K0; zify_cond K0. { dead K0. } clear K0.
    zstep. zstep.
    eapply (LOOP (Z.to_nat (pe_e E - x_p x)) (x_p x));
      [exact MU| exact WM| exact MI| unfold vep_cells; rewrite STATE; exact VEPC| unfold pframe; exact FR| exact DBY| exact HENV| exact STK
      | clear - PLT; rewrite Z2Nat.id by lia; lia| clear; lia| exact PLT].
  Qed.
End S.
End U_PHaq6.

Module U_PHbhj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_Pahif U_PKit V_PH51p ImgU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_La7nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Cov8m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)



Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Hypothesis HVE : vep_error_stmt.

  #[using="HVE"] Lemma PH_AttrDelim : handler_stmt S_AttrDelim.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
    assert (EVSC : h_vsc (pe_H E) = h_sp (pe_H E) + 2240) by reflexivity.
    assert (EVS : VEPERR_STACK = 48) by reflexivity.
    assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
    pose proof (DELIM1 ltac:(discriminate)) as DL0.
    (* [comment removed for export] *)
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU2. pose proof (wmono_refl rsegs m) as WM2.
    assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                          [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    (* [comment removed for export] *)
    assert (QUOTE : forall (d : Z) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      (d = 34 \/ d = 39) ->
      realizes rsegs (mkCfg (loop_ms E 0x1aa70 (x_p x) ra' t0' t1' t2' (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' m) md) T).
    { intros until t6'. intros HD. unfold loop_ms, lms.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. zstep. if_cases KT; zify_cond KT.
      { exfalso. revert KT PLT Dhi CV. clear. unfold pe_e, pe_N. intros. lia. }
      clear KT.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
          by (eapply (henv_stores E A _ _ md _ _ PE0 AINV MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENV])
      end.
      eapply (KL (PST (x_p x + 1) S_AttrValue (fupd (fupd (x_v x) Fattr_delim d) Fstate (stU S_AttrValue))
                      (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
      2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
      2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
      2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
          w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
      2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. clear - PLT. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
      + (* [comment removed for export] *) clear - VERP. lia.
      + (* [comment removed for export] *) clear - PLT. unfold pe_e in *. lia.
      + (* [comment removed for export] *) split; [intros X; exfalso; exact (X eq_refl)| intros _; right; destruct HD as [-> | ->]; [left|right]; reflexivity].
      + (* [comment removed for export] *) intros _ [X|X]; [discriminate X| exact (ATTRST I (or_intror X))]. }
    (* [comment removed for export] *)
    apply rz_go; [exact MDH| exact MDL|].
    (* [comment removed for export] *)
    zstep. rewrite DL0, sx32_zero. zstep. if_cases K1; zify_cond K1. { dead K1. } clear K1.
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT VERP Dlo. lia. } clear KT.
    (* [comment removed for export] *)
    destruct (look_read rsegs E x m DBY ltac:(clear - VERP; lia) PLT) as (b & Hnth & Hlook & RDP).
    pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
    zstep. clear RDP. cbv beta.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K2; zify_cond K2.
    { apply rz_stop. rewrite K2. apply QUOTE. right; reflexivity. }
    (* [comment removed for export] *)
    zstep. zstep. if_cases K3; zify_cond K3.
    2:{ apply rz_stop. rewrite K3. apply QUOTE. left; reflexivity. }
    (* [comment removed for export] *)
    zstep.
    replace (Z.shiftl (bv_unsigned b) 1) with (2 * bv_unsigned b) by (rewrite Z.shiftl_mul_pow2; clear; lia).
    (* [comment removed for export] *)
    assert (VCR1 : 0 <= VCT_ADDR < 2^64) by (unfold VCT_ADDR; clear; lia).
    zstep. zstep. if_cases KT; zify_cond KT.
    { exfalso. revert KT BR. clear. intros. rewrite zb_lxor_ones in KT by (unfold VCT_ADDR; lia). unfold VCT_ADDR in KT.
      first [rewrite !Z.mod_small in KT by lia | idtac]. lia. }
    clear KT VCR1. zstep.
    pose proof (vct_readU m (bv_unsigned b) _ MI BR eq_refl) as RDV. unfold wa in RDV.
    zstep. clear RDV. cbv beta. rewrite zx16_vct.
    (* [comment removed for export] *)
    pose proof (vct_range (bv_unsigned b)) as VR.
    zstep. zstep. if_cases K4; zify_cond K4.
    { (* [comment removed for export] *)
      clear MU2 WM2 WZ2 QUOTE.
      zstep. zstep. zstep. zstep. zstep.
      hide STK. hide_slow.
      call_fr (HVE (pe_VEP E) (x_v x) (x_tag x) (x_q x) (pe_H E) (pe_lo E)) by idtac.
      1:{ reflexivity. }
      1:{ unfold vep_cells. rewrite STATE. exact VEPC. }
      1:{ exact TAG. }
      1:{ exact PADS. }
      1:{ exact (proj1 BASE). }
      1:{ exact HENV. }
      1:{ exact (proj1 PE0). }
      1:{ exact IMG. }
      1:{ exact VEPlo. }
      1:{ apply mod8_of_mod16. exact VEP16. }
      1:{ clear - VEPhi. lia. }
      1:{ unhide STK. rewrite unsigned_lit by exact SPR. exact STK. }
      1:{ rewrite unsigned_lit by exact SPR. rewrite EVS, PSP. clear - LOP. lia. }
      1:{ exact CEIL. }
      1:{ rewrite unsigned_lit by exact SPR. rewrite PSP. clear. lia. }
      1:{ exact MI. }
      clear STK. unhide_slow.
      try match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
      rename PC into HENVc. rename POST into STKc.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        pose proof (ainv_stores E A m mc md _ _ PE0 AINV MU WM WZ) as AINVc;
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU3; pose proof (wmono_refl rsegs mc) as WM3 end.
      assert (WZ3 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                            [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      (* [comment removed for export] *)
      zstep. zstep. zstep. apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
          by (eapply (henv_stores E A _ _ md _ _ PE0 AINVc MU3 WM3 WZ3); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENVc])
      end.
      eapply (KL (PST (x_p x) S_TagError (fupd (x_v x) Fstate (stU S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
      2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
      2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
      2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STKc| exact FR]
                               | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
          w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
      2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
    }
    (* [comment removed for export] *)
    clear K4. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
      assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
        by (eapply (henv_stores E A _ _ md _ _ PE0 AINV MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENV])
    end.
    eapply (KL (PST (x_p x) S_AttrValue (fupd (fupd (x_v x) Fattr_delim 32) Fstate (stU S_AttrValue))
                    (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
    2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
    2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
    2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
    (* [comment removed for export] *)
    2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
    apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
    + (* [comment removed for export] *) split; [intros X; exfalso; exact (X eq_refl)| intros _; left; reflexivity].
    + (* [comment removed for export] *) intros _ [X|X]; [discriminate X| exact (ATTRST I (or_intror X))].
    all: fail "stop".
  Qed.
End S.
End U_PHbhj.

Module U_PHej2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_Pahif U_PKit V_PH51p ImgU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_La7nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Cov8m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Hypothesis HVE : vep_error_stmt.

  #[using="HVE"] Lemma PH_ESI_Include : handler_stmt S_ESI_Include.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
    assert (EVSC : h_vsc (pe_H E) = h_sp (pe_H E) + 2240) by reflexivity.
    assert (EVS : VEPERR_STACK = 48) by reflexivity.
    assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
    (* [comment removed for export] *)
    assert (TAIL : forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m mc ->
      wmono rsegs m mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (x_v x) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E) (pframe E j0 j8 j16 j24) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) ->
      henv_ok LayoutPU VIU (pe_H E) mc -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      realizes rsegs (mkCfg (loop_ms E 0x1a358 (x_p x) ra' t0' t1' t2' (Z_to_bv 64 (stU S_TagError)) a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) md) T).
    { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc HENVc STKc. unfold loop_ms, lms.
      clear VEPC FR DBY STK HENV MI.
      unfold vep_cells in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
      pose proof (ainv_stores E A m mc md _ _ PE0 AINV MUc WMc WZ) as AINVc.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU2. pose proof (wmono_refl rsegs mc) as WM2.
      assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                            [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH| exact MDL|].
      zstep. zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
          by (eapply (henv_stores E A _ _ md _ _ PE0 AINVc MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENVc])
      end.
      eapply (KL (PST (x_p x) S_TagError (fupd (x_v x) Fstate (stU S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
      2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MUc WMc WZ). }
      2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
      2:{ eapply hstep_stores; [exact MUc | | eapply parse_window_mapped; [exact PE0| exact STKc| exact FRc]
                               | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
          w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
      2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV MUc WMc WZ. }
    (* [comment removed for export] *)
    assert (ERRC : forall (ret : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      (ret = 0x1a784 \/ ret = 0x1a7e4) ->
      realizes rsegs (mkCfg (loop_ms E vep_error_entry (x_p x) (Z_to_bv 64 ret) t0' t1' t2' (Z_to_bv 64 (pe_VEP E)) a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' m) md) T).
    { intros until t6'. intros RET. unfold loop_ms, lms, vep_error_entry.
      apply rz_go; [exact MDH| exact MDL|].
      hide STK. hide_slow.
      call_fr (HVE (pe_VEP E) (x_v x) (x_tag x) (x_q x) (pe_H E) (pe_lo E)) by idtac.
      1:{ reflexivity. }
      1:{ unfold vep_cells. rewrite STATE. exact VEPC. }
      1:{ exact TAG. }
      1:{ exact PADS. }
      1:{ exact (proj1 BASE). }
      1:{ exact HENV. }
      1:{ exact (proj1 PE0). }
      1:{ exact IMG. }
      1:{ exact VEPlo. }
      1:{ apply mod8_of_mod16. exact VEP16. }
      1:{ clear - VEPhi. lia. }
      1:{ unhide STK. rewrite unsigned_lit by exact SPR. exact STK. }
      1:{ rewrite unsigned_lit by exact SPR. rewrite EVS, PSP. clear - LOP. lia. }
      1:{ exact CEIL. }
      1:{ rewrite unsigned_lit by exact SPR. rewrite PSP. clear. lia. }
      1:{ exact MI. }
      clear STK. unhide_slow.
      (* [comment removed for export] *)
      destruct RET as [-> | ->];
        match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end;
        zstep; zstep; zstep; apply rz_stop;
        (eapply TAIL; [exact MU| exact WM| exact MI0| unfold vep_cells; rewrite STATE; exact VEPC| unfold pframe; exact FR| exact DBY| exact PC| exact POST]). }
    (* [comment removed for export] *)
    apply rz_go; [exact MDH| exact MDL|].
    (* [comment removed for export] *)
    zstep. destruct B_rm as [RM|RM]; rewrite RM, ?sx32_zero, ?sx32_one.
    2:{ (* [comment removed for export] *)
        zstep. if_cases K1; zify_cond K1. { dead K1. } clear K1.
        zstep. zstep. zstep. zstep. apply rz_stop. apply ERRC. left. reflexivity. }
    zstep. if_cases K1; zify_cond K1. 2:{ dead K1. } clear K1.
    (* [comment removed for export] *)
    zstep. destruct B_et as [ET|ET]; rewrite ET, ?sx32_zero, ?sx32_one.
    2:{ (* [comment removed for export] *)
        zstep. if_cases K2; zify_cond K2. { dead K2. } clear K2.
        zstep. zstep. zstep. zstep. apply rz_stop. apply ERRC. right. reflexivity. }
    zstep. if_cases K2; zify_cond K2. 2:{ dead K2. } clear K2.
    (* [comment removed for export] *)
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU2. pose proof (wmono_refl rsegs m) as WM2.
    assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                          [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (TBL_bom + 32) with TBL_attr_include by reflexivity.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
      assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
        by (eapply (henv_stores E A _ _ md _ _ PE0 AINV MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENV])
    end.
    eapply (KL (PST (x_p x) S_InTag (fupd (fupd (fupd (x_v x) Fattr TBL_attr_include) Fdostuff (vi_do_include VIU)) Fstate (stU S_InTag))
                    (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
    2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
    2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
    2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
    (* [comment removed for export] *)
    2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
    apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
    (* [comment removed for export] *) { right; left; reflexivity. }
    (* [comment removed for export] *) right. split; [reflexivity| split; [reflexivity| left; exact I]].
  Qed.
End S.
End U_PHej2.

Module U_PHj88.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m U_Pahif U_PKit ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  Lemma PH_CDATA : handler_stmt S_CDATA.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    apply rz_go; [exact MDH| exact MDL|].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    eapply (KL (PST (x_p x) S_Until
                    (fupd (fupd (fupd (fupd (x_v x) Funtil LIT_cdata_end) Funtil_p LIT_cdata_end) Funtil_s (stU S_NxtTag)) Fstate (stU S_Until))
                    (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
    2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
    2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
    2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
    (* [comment removed for export] *)
    2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
    apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
    - (* [comment removed for export] *) intros _. split; [right; reflexivity|]. split; [unfold LIT_cdata_end; lia| reflexivity].
  Qed.
End S.
End U_PHj88.

Module U_PHjur.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_Pahif U_PKit ImgU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_La7nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Cov8m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Hypothesis HVE : vep_error_stmt.

  #[using="HVE"] Lemma PH_ESI_Bogon : handler_stmt S_ESI_Bogon.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    (* [comment removed for export] *)
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
    apply rz_go; [exact MDH| exact MDL|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    assert (EVSC : h_vsc (pe_H E) = h_sp (pe_H E) + 2240) by reflexivity.
    assert (EVS : VEPERR_STACK = 48) by reflexivity.
    assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
    hide STK. hide_slow.
    call_fr (HVE (pe_VEP E) (x_v x) (x_tag x) (x_q x) (pe_H E) (pe_lo E)) by idtac.
    1:{ reflexivity. }
    1:{ unfold vep_cells. rewrite STATE. exact VEPC. }
    1:{ exact TAG. }
    1:{ exact PADS. }
    1:{ exact (proj1 BASE). }
    1:{ exact HENV. }
    1:{ exact (proj1 PE0). }
    1:{ exact IMG. }
    1:{ exact VEPlo. }
    1:{ apply mod8_of_mod16. exact VEP16. }
    1:{ clear - VEPhi. lia. }
    1:{ unhide STK. rewrite unsigned_lit by exact SPR. exact STK. }
    1:{ rewrite unsigned_lit by exact SPR. rewrite EVS, PSP. clear - LOP. lia. }
    1:{ exact CEIL. }
    1:{ rewrite unsigned_lit by exact SPR. rewrite PSP. clear. lia. }
    1:{ exact MI. }
    clear STK. unhide_slow. rename POST into STK. rename PC into HENV1. clear HENV.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (ainv_stores E A m mc md _ _ PE0 AINV MU WM WZ) as AINV1;
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU2; pose proof (wmono_refl rsegs mc) as WM2;
      assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                            [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac
    end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    (* [comment removed for export] *)
    match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
      assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
        by (eapply (henv_stores E A _ _ md _ _ PE0 AINV1 MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENV1])
    end.
    eapply (KL (PST (x_p x) S_TagError (fupd (x_v x) Fstate (stU S_TagError))
                    (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
    2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
    2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
    2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
    (* [comment removed for export] *)
    2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
    apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
  Qed.
End S.
End U_PHjur.

Module U_PHnex.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m U_Pahif U_PKit ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  Lemma PH_ESI_Remove : handler_stmt S_ESI_Remove.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    apply rz_go; [exact MDH| exact MDL|].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    eapply (KL (PST (x_p x) S_InTag (fupd (fupd (x_v x) Fdostuff (vi_do_remove VIU)) Fstate (stU S_InTag))
                    (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
    2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
    2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
    2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
    (* [comment removed for export] *)
    2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
    apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
    - (* [comment removed for export] *) right; right; left. reflexivity.
  Qed.
End S.
End U_PHnex.

Module U_PHow2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_Pahif U_PKit V_PH51p ImgU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_La7nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Cov8m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Hypothesis HVE : vep_error_stmt.

  #[using="HVE"] Lemma PH_ESI_Comment : handler_stmt S_ESI_Comment.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
    assert (EVSC : h_vsc (pe_H E) = h_sp (pe_H E) + 2240) by reflexivity.
    assert (EVS : VEPERR_STACK = 48) by reflexivity.
    assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
    (* [comment removed for export] *)
    assert (TAIL : forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m mc ->
      wmono rsegs m mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (x_v x) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E) (pframe E j0 j8 j16 j24) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) ->
      henv_ok LayoutPU VIU (pe_H E) mc -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      realizes rsegs (mkCfg (loop_ms E 0x1a358 (x_p x) ra' t0' t1' t2' (Z_to_bv 64 (stU S_TagError)) a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) md) T).
    { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc HENVc STKc. unfold loop_ms, lms.
      clear VEPC FR DBY STK HENV MI.
      unfold vep_cells in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
      pose proof (ainv_stores E A m mc md _ _ PE0 AINV MUc WMc WZ) as AINVc.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU2. pose proof (wmono_refl rsegs mc) as WM2.
      assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                            [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH| exact MDL|].
      zstep. zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
          by (eapply (henv_stores E A _ _ md _ _ PE0 AINVc MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENVc])
      end.
      eapply (KL (PST (x_p x) S_TagError (fupd (x_v x) Fstate (stU S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
      2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MUc WMc WZ). }
      2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
      2:{ eapply hstep_stores; [exact MUc | | eapply parse_window_mapped; [exact PE0| exact STKc| exact FRc]
                               | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
          w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
      2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV MUc WMc WZ. }
    (* [comment removed for export] *)
    assert (ERRC : forall (ret : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      (ret = 0x1a7c0 \/ ret = 0x1a874) ->
      realizes rsegs (mkCfg (loop_ms E vep_error_entry (x_p x) (Z_to_bv 64 ret) t0' t1' t2' (Z_to_bv 64 (pe_VEP E)) a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' m) md) T).
    { intros until t6'. intros RET. unfold loop_ms, lms, vep_error_entry.
      apply rz_go; [exact MDH| exact MDL|].
      hide STK. hide_slow.
      call_fr (HVE (pe_VEP E) (x_v x) (x_tag x) (x_q x) (pe_H E) (pe_lo E)) by idtac.
      1:{ reflexivity. }
      1:{ unfold vep_cells. rewrite STATE. exact VEPC. }
      1:{ exact TAG. }
      1:{ exact PADS. }
      1:{ exact (proj1 BASE). }
      1:{ exact HENV. }
      1:{ exact (proj1 PE0). }
      1:{ exact IMG. }
      1:{ exact VEPlo. }
      1:{ apply mod8_of_mod16. exact VEP16. }
      1:{ clear - VEPhi. lia. }
      1:{ unhide STK. rewrite unsigned_lit by exact SPR. exact STK. }
      1:{ rewrite unsigned_lit by exact SPR. rewrite EVS, PSP. clear - LOP. lia. }
      1:{ exact CEIL. }
      1:{ rewrite unsigned_lit by exact SPR. rewrite PSP. clear. lia. }
      1:{ exact MI. }
      clear STK. unhide_slow.
      (* [comment removed for export] *)
      destruct RET as [-> | ->];
        match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end;
        zstep; zstep; zstep; apply rz_stop;
        (eapply TAIL; [exact MU| exact WM| exact MI0| unfold vep_cells; rewrite STATE; exact VEPC| unfold pframe; exact FR| exact DBY| exact PC| exact POST]). }
    (* [comment removed for export] *)
    apply rz_go; [exact MDH| exact MDL|].
    (* [comment removed for export] *)
    zstep. destruct B_rm as [RM|RM]; rewrite RM, ?sx32_zero, ?sx32_one.
    2:{ (* [comment removed for export] *)
        zstep. if_cases K1; zify_cond K1. { dead K1. } clear K1.
        zstep. zstep. zstep. zstep. apply rz_stop. apply ERRC. left. reflexivity. }
    zstep. if_cases K1; zify_cond K1. 2:{ dead K1. } clear K1.
    (* [comment removed for export] *)
    zstep. destruct B_et as [ET|ET]; rewrite ET, ?sx32_zero, ?sx32_one.
    2:{ (* [comment removed for export] *)
        zstep. if_cases K2; zify_cond K2. { dead K2. } clear K2.
        zstep. zstep. zstep. zstep. apply rz_stop. apply ERRC. right. reflexivity. }
    zstep. if_cases K2; zify_cond K2. 2:{ dead K2. } clear K2.
    (* [comment removed for export] *)
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU2. pose proof (wmono_refl rsegs m) as WM2.
    assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                          [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
      assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
        by (eapply (henv_stores E A _ _ md _ _ PE0 AINV MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENV])
    end.
    eapply (KL (PST (x_p x) S_InTag (fupd (fupd (x_v x) Fdostuff (vi_do_comment VIU)) Fstate (stU S_InTag))
                    (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
    2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
    2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
    2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
    (* [comment removed for export] *)
    2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
    apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
    (* [comment removed for export] *) right; right; right. reflexivity.
  Qed.
End S.
End U_PHow2.

Module U_PHwzj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m U_Pahif U_PKit ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  Lemma PH_Comment : handler_stmt S_Comment.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    apply rz_go; [exact MDH| exact MDL|].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    eapply (KL (PST (x_p x) S_Until
                    (fupd (fupd (fupd (fupd (fupd (fupd (x_v x) Fesicmt_p 0) Funtil LIT_arrow) Funtil_p LIT_arrow)
                                      Funtil_s (stU S_NxtTag)) Fesicmt 0) Fstate (stU S_Until))
                    (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
    2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
    2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
    2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
    (* [comment removed for export] *)
    2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
    apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
    - (* [comment removed for export] *) left. split; reflexivity.
    - (* [comment removed for export] *) intros _. split; [left; reflexivity|]. split; [unfold LIT_arrow; lia| reflexivity].
  Qed.
End S.
End U_PHwzj.

Module U_PHy8z.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m U_Pahif U_PKit V_PH51p ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  Lemma PH_Attr : handler_stmt S_Attr.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    (* [comment removed for export] *)
    pose proof (DELIM1 ltac:(discriminate)) as DL0.
    assert (AV0 : x_v x Fattr_vsb = 0).
    { destruct (Z.eq_dec (x_v x Fattr_vsb) 0) as [X|X]; [exact X| exfalso; exact (AVSB X)]. }
    apply rz_go; [exact MDH| exact MDL|].
    (* [comment removed for export] *)
    zstep. rewrite DL0, sx32_zero. zstep. if_cases K1; zify_cond K1. { dead K1. } clear K1.
    (* [comment removed for export] *)
    destruct ATTR as [AT0|(ATI & DOI & _)].
    - (* [comment removed for export] *)
      zstep. rewrite AT0. zstep. if_cases K2; zify_cond K2. { dead K2. } clear K2.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KT; zify_cond KT.
      { exfalso. revert KT VERP Dlo PLT Dhi CV. clear. intros. first [rewrite Z.mod_small in KT by lia | idtac]. lia. }
      clear KT.
      (* [comment removed for export] *)
      zstep. zstep. rewrite AV0. zstep. if_cases K3; zify_cond K3. { dead K3. } clear K3.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (KL (PST (x_p x + 1) S_SkipAttribute (fupd (x_v x) Fstate (stU S_SkipAttribute))
                      (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
      2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
      2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
      2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      (* [comment removed for export] *)
      2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST.
          destruct (vct_xmlname _); clear - PLT; lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
      + (* [comment removed for export] *) clear - VERP. lia.
      + (* [comment removed for export] *) clear - PLT. unfold pe_e in *. lia.
      + (* [comment removed for export] *) left. exact AT0.
    - (* [comment removed for export] *)
      zstep. rewrite ATI. unfold TBL_attr_include. (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2. 2:{ dead K2. } clear K2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (KL (PST (x_p x) S_Match (fupd (fupd (x_v x) Fmatch TBL_attr_include) Fstate (stU S_Match))
                      (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
      2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
      2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
      2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      (* [comment removed for export] *)
      2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST.
          unfold TBL_bom, TBL_starttag, TBL_esi, TBL_attr_include. cbn [Z.eqb Pos.eqb]. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
      + (* [comment removed for export] *) intros _. exact (ARMED I).
      + (* [comment removed for export] *) right. split; [exact ATI|]. split; [exact DOI|]. left. reflexivity.
      + (* [comment removed for export] *) intros _ _. exact ATI.
      + (* [comment removed for export] *) intros _ _ HLT. refine (LOOKA eq_refl _ HLT). rewrite ATI. unfold TBL_attr_include. clear. lia.
  Qed.
End S.
End U_PHy8z.


Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vm_find_some : forall es inp i, mtab_wf es -> vm_find es inp = Some i ->
  exists e, nth_error es i = Some e /\
            ((me_ptr e = 0 /\ me_str e = []) \/ (me_ptr e <> 0 /\ is_prefixb (me_str e) inp = true /\ (1 <= length (me_str e) <= 8)%nat)).
Proof.
  induction es as [|e es IH]; intros inp i WF H; cbn in H; [cbn in WF; contradiction|].
  destruct es as [|e2 es2].
  - destruct WF as [E0 Es]. rewrite E0 in H. cbn in H. injection H as <-. exists e. split; [reflexivity| left; auto].
  - (first [ dand4 WF as Hp Hl Hn WF' | destruct WF as (Hp & Hl & Hn & WF') ]).
    destruct (me_ptr e =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|]. apply Z.eqb_neq in E0.
    destruct (is_prefixb (me_str e) inp) eqn:EP.
    + injection H as <-. exists e. split; [reflexivity| right; auto].
    + destruct (runs_outb (me_str e) inp); [discriminate|].
      destruct (vm_find (e2 :: es2) inp) as [j|] eqn:EJ; [|discriminate]. cbn in H. injection H as <-.
      (first [ pose proof ((IH inp j WF' EJ)) as dR_2; dex1 dR_2 as e'; destruct dR_2 as [Hn' F] | pose proof ((IH inp j WF' EJ)) as dR_2; dand3 dR_2 as e' Hn' F | destruct (IH inp j WF' EJ) as (e' & Hn' & F) ]). exists e'. split; [exact Hn'| exact F].
Qed.

Lemma vm_find_none : forall es inp, mtab_wf es -> vm_find es inp = None -> (length inp <= 7)%nat.
Proof.
  induction es as [|e es IH]; intros inp WF H; cbn in H; [discriminate|].
  destruct es as [|e2 es2].
  - destruct WF as [E0 _]. rewrite E0 in H. cbn in H. discriminate.
  - (first [ dand4 WF as Hp Hl Hn WF' | destruct WF as (Hp & Hl & Hn & WF') ]).
    destruct (me_ptr e =? 0); [discriminate|]. destruct (is_prefixb (me_str e) inp); [discriminate|].
    destruct (runs_outb (me_str e) inp) eqn:ER.
    + apply runs_outb_length in ER. lia.
    + destruct (vm_find (e2 :: es2) inp) eqn:EJ; [discriminate|]. eapply IH; eauto.
Qed.

Lemma vm_find_lt : forall es inp i, mtab_wf es -> vm_find es inp = Some i -> (i < length es)%nat.
Proof. intros. eapply vm_find_bound; eauto. Qed.

(* [comment removed for export] *)
Definition tgt_ok (es : list mentry) (ts : list (nat * vstate)) : Prop :=
  forall i e, nth_error es i = Some e ->
    exists k S', nth_error ts i = Some (k, S') /\ me_svar e = VEPVARSU + Z.of_nat k /\
                 cell_at vepvarsU k = Some (C8 (Z_to_bv 64 (stU S'))) /\ me_sval e = stU S' /\ (VEPVARSU + Z.of_nat k) mod 8 = 0.

Definition tgts_bom : list (nat * vstate) := [(0%nat, S_Start); (8%nat, S_BOM)].
Definition tgts_attr_include : list (nat * vstate) := [(104%nat, S_AttrGetValue); (104%nat, S_AttrGetValue); (112%nat, S_SkipAttribute)].
Definition tgts_esi : list (nat * vstate) := [(72%nat, S_ESI_Include); (80%nat, S_ESI_Remove); (88%nat, S_ESI_Comment); (96%nat, S_ESI_Bogon)].
Definition tgts_starttag : list (nat * vstate) :=
  [(16%nat, S_CommentESI); (24%nat, S_NxtTag); (32%nat, S_Comment); (40%nat, S_end_ESITag); (48%nat, S_ESITag); (56%nat, S_CDATA); (64%nat, S_NotMyTag)].

Ltac tgt_ok_tac :=
  intros [|[|[|[|[|[|[|[|i]]]]]]]] e H; cbn in H; try discriminate; injection H as <-;
  eexists _, _; (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]); split; reflexivity.

Lemma tgt_bom : tgt_ok tbl_bom tgts_bom. Proof. tgt_ok_tac. Qed.
Lemma tgt_attr_include : tgt_ok tbl_attr_include tgts_attr_include. Proof. tgt_ok_tac. Qed.
Lemma tgt_esi : tgt_ok tbl_esi tgts_esi. Proof. tgt_ok_tac. Qed.
Lemma tgt_starttag : tgt_ok tbl_starttag tgts_starttag. Proof. tgt_ok_tac. Qed.

(* [comment removed for export] *)
Definition tab4 (Tb : Z) (es : list mentry) (ts : list (nat * vstate)) : Prop :=
  (Tb = TBL_bom /\ es = tbl_bom /\ ts = tgts_bom) \/ (Tb = TBL_attr_include /\ es = tbl_attr_include /\ ts = tgts_attr_include) \/
  (Tb = TBL_esi /\ es = tbl_esi /\ ts = tgts_esi) \/ (Tb = TBL_starttag /\ es = tbl_starttag /\ ts = tgts_starttag).

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  Lemma PH_Match : handler_stmt S_Match.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 80, pe_sp E); (pe_sp E + 24, pe_sp E + 32)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 80, pe_sp E); (pe_sp E + 24, pe_sp E + 32)]) by wzone_tac.
    assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
    assert (EVM : VM_FRAME = 80) by reflexivity.
    assert (PHI : phi E x = 16 * (pe_e E - x_p x) + rank E x) by reflexivity.
    (* [comment removed for export] *)
    assert (TBL : exists Tb es ts, x_v x Fmatch = Tb /\ ro_cells rsegs m Tb (mtab_cells es) /\ mtab_wf es /\ mtab_strings m es /\
                  tgt_ok es ts /\ IMGU_LO <= Tb /\ Tb + Z.of_nat (cells_size (mtab_cells es)) <= IMGU_HI /\
                  (forall i e, nth_error es i = Some e -> me_ptr e <> 0 -> 0 <= me_ptr e /\ me_ptr e + 16 <= IMGU_LO) /\ Tb mod 8 = 0 /\ tab4 Tb es ts).
    { (first [ pose proof (IMG) as dR_4; dand10 dR_4 as _ _ _ _ _ _ ITb ITa ITe ITs | pose proof IMG as (_ & _ & _ & _ & _ & _ & ITb & ITa & ITe & ITs) ]).
      destruct (MTCH eq_refl) as [TM|[TM|[TM|TM]]].
      - exists TBL_bom, tbl_bom, tgts_bom. split; [exact TM|]. split; [exact ITb|]. split; [exact tbl_bom_wf|]. split; [exact (tbl_bom_strings m MI)|].
        split; [exact tgt_bom|]. split; [unfold IMGU_LO, TBL_bom; clear; lia|]. split; [unfold IMGU_HI, TBL_bom; cbn; clear; lia|].
        split; [| split; [reflexivity| left; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity]].
        intros [|[|[|i]]] e H; cbn in H; try discriminate; injection H as <-; cbn; unfold IMGU_LO; clear; intros; lia.
      - exists TBL_starttag, tbl_starttag, tgts_starttag. split; [exact TM|]. split; [exact ITs|]. split; [exact tbl_starttag_wf|].
        split; [exact (tbl_starttag_strings m MI)|].
        split; [exact tgt_starttag|]. split; [unfold IMGU_LO, TBL_starttag; clear; lia|]. split; [unfold IMGU_HI, TBL_starttag; cbn; clear; lia|].
        split; [| split; [reflexivity| right; right; right; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity]].
        intros [|[|[|[|[|[|[|[|i]]]]]]]] e H; cbn in H; try discriminate; injection H as <-; cbn; unfold IMGU_LO; clear; intros; lia.
      - exists TBL_esi, tbl_esi, tgts_esi. split; [exact TM|]. split; [exact ITe|]. split; [exact tbl_esi_wf|]. split; [exact (tbl_esi_strings m MI)|].
        split; [exact tgt_esi|]. split; [unfold IMGU_LO, TBL_esi; clear; lia|]. split; [unfold IMGU_HI, TBL_esi; cbn; clear; lia|].
        split; [| split; [reflexivity| right; right; left; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity]].
        intros [|[|[|[|[|i]]]]] e H; cbn in H; try discriminate; injection H as <-; cbn; unfold IMGU_LO; clear; intros; lia.
      - exists TBL_attr_include, tbl_attr_include, tgts_attr_include. split; [exact TM|]. split; [exact ITa|]. split; [exact tbl_attr_include_wf|].
        split; [exact (tbl_attr_include_strings m MI)|].
        split; [exact tgt_attr_include|]. split; [unfold IMGU_LO, TBL_attr_include; clear; lia|]. split; [unfold IMGU_HI, TBL_attr_include; cbn; clear; lia|].
        split; [| split; [reflexivity| right; left; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity]].
        intros [|[|[|[|i]]]] e H; cbn in H; try discriminate; injection H as <-; cbn; unfold IMGU_LO; clear; intros; lia. }
    (first [ dand13 TBL as Tb es ts TM ITB WF STRS TGT TLO THI STRB T8 TAB4 | destruct TBL as (Tb & es & ts & TM & ITB & WF & STRS & TGT & TLO & THI & STRB & T8 & TAB4) ]).
    (* [comment removed for export] *)
    (first [ pose proof ((pd_split3 rsegs m (pe_VEP E) _ 39 (C8 (Z_to_bv 64 (x_v x Fmatch))) VEPC eq_refl)) as dR_6; dand3 dR_6 as _ VPM _ | pose proof (pd_split3 rsegs m (pe_VEP E) _ 39 (C8 (Z_to_bv 64 (x_v x Fmatch))) VEPC eq_refl) as (_ & VPM & _) ]).
    cbn [firstn cells_size csize Nat.add length] in VPM. change (Z.of_nat 240) with 240 in VPM. rewrite TM in VPM.
    (* [comment removed for export] *)
    apply rz_go; [exact MDH| exact MDL|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    hide STK. hide_slow. pose proof VEPimg as VEPimg'. unfold off_image in VEPimg'. cbn [al_image_lo al_image_hi LayoutPU] in VEPimg'. unfold IMGU_LO in TLO. unfold IMGU_HI in THI.
    call_fr (vep_match_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               bvmap_empty (Z_to_bv 32 0) m (pe_VEP E) Tb es (pslice E (x_p x) (pe_e E)) (pe_lo E)) by idtac.
    1:{ exact MI. }
    1:{ unhide STK. rewrite unsigned_lit by exact SPR. exact STK. }
    1:{ rewrite unsigned_lit by exact SPR. unfold VM_FRAME. rewrite PSP. clear - LOP. lia. }
    1:{ reflexivity. }
    1:{ exact (proj1 VPM). }
    1:{ clear - TLO. lia. }
    1:{ exact ITB. }
    1:{ exact WF. }
    1:{ exact STRS. }
    1:{ rewrite unsigned_lit by (clear - VERP Dlo Dhi CV PLT; unfold pe_e, pe_N in *; lia). apply pslice_bytes; [exact DBY| clear - VERP; lia| exact PLE| clear; unfold pe_e, pe_N; lia]. }
    1:{ rewrite unsigned_lit by (clear - VERP Dlo Dhi CV PLT; unfold pe_e, pe_N in *; lia). rewrite pslice_length; [f_equal; clear; unfold pe_e, pe_N; lia| clear - VERP; lia| exact PLE| clear; unfold pe_e, pe_N; lia]. }
    1:{ left. rewrite unsigned_lit by exact SPR. unfold VM_FRAME. rewrite PSP. clear - VEPhi CEIL LOP. lia. }
    1:{ left. rewrite unsigned_lit by exact SPR. unfold VM_FRAME. rewrite PSP. clear - THI CEIL LOP CV. lia. }
    1:{ left. rewrite (unsigned_lit (x_p x)) by (clear - VERP Dlo Dhi CV PLT; unfold pe_e, pe_N in *; lia). rewrite (unsigned_lit (pe_sp E)) by exact SPR.
        unfold VM_FRAME. rewrite PSP. rewrite pslice_length; [| clear - VERP; lia| exact PLE| clear; unfold pe_e, pe_N; lia].
        clear - Dhi CEIL LOP PLE. unfold pe_e, pe_N in *. lia. }
    1:{ intros i e Hn Hp. left. rewrite unsigned_lit by exact SPR. unfold VM_FRAME. rewrite PSP. destruct (STRB i e Hn Hp) as [_ B]. revert B CEIL LOP CV. clear. unfold IMGU_LO. intros; lia. }
    1:{ split; [clear - VEPlo; lia|]. split; [clear - VEPhi CV; lia| apply mod8_of_mod16; exact VEP16]. }
    1:{ unhide T8. split; [exact T8| clear - THI CV; unfold IMGU_HI in THI; lia]. }
    1:{ rewrite unsigned_lit by (clear - VERP Dlo Dhi CV PLT; unfold pe_e, pe_N in *; lia).
        rewrite pslice_length; [| clear - VERP; lia| exact PLE| clear; unfold pe_e, pe_N; lia]. clear - VERP Dlo Dhi CV PLE. unfold pe_e, pe_N in *. lia. }
    clear STK. unhide_slow. rename POST into STK. rename MI0 into MI.
    (* [comment removed for export] *)
    clear ITB VPM.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (ainv_stores E A m mc md _ _ PE0 AINV MU WM WZ) as AINVc;
      assert (STRS1 : mtab_strings mc es)
        by (destruct TAB4 as [(_ & X & _)|[(_ & X & _)|[(_ & X & _)|(_ & X & _)]]]; rewrite X;
            [apply tbl_bom_strings| apply tbl_attr_include_strings| apply tbl_esi_strings| apply tbl_starttag_strings]; exact MI)
    end.
    set (inp' := pslice E (x_p x) (pe_e E)) in *.
    assert (LINP : Z.of_nat (length inp') = pe_e E - x_p x) by (subst inp'; apply pslice_length; [clear - VERP; lia| exact PLE| clear; unfold pe_e, pe_N; lia]).
    destruct (vm_find es inp') as [i|] eqn:VF; unfold vm_result; rewrite VF.
    - (* [comment removed for export] *)
      (first [ pose proof ((vm_find_some es inp' i WF VF)) as dR_7; dex1 dR_7 as e; destruct dR_7 as [Hnth CASES] | pose proof ((vm_find_some es inp' i WF VF)) as dR_7; dand3 dR_7 as e Hnth CASES | destruct (vm_find_some es inp' i WF VF) as (e & Hnth & CASES) ]).
      (first [ pose proof ((TGT i e Hnth)) as dR_8; dex1 dR_8 as k; dand6 dR_8 as S' Hts Esv Hcell Esval SV8 | pose proof ((TGT i e Hnth)) as dR_8; dand7 dR_8 as k S' Hts Esv Hcell Esval SV8 | destruct (TGT i e Hnth) as (k & S' & Hts & Esv & Hcell & Esval & SV8) ]).
      pose proof (vm_find_lt es inp' i WF VF) as IL. rewrite mtab_cells_size in THI.
      assert (IR : 0 <= Tb + 16 * Z.of_nat i < 2^64) by (revert IL TLO THI; clear; intros; lia).
      (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 TLO. lia. } clear K1.
      zstep. zstep. zstep. if_cases KT; zify_cond KT.
      { exfalso. apply KT. apply land7_of_mod8; [clear - IR; lia|]. revert T8. clear. intros. Z.div_mod_to_equations. lia. }
      clear KT.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (ITB : ro_cells rsegs mc Tb (mtab_cells es))
          by (pose proof (img_stores E A m mc md _ _ PE0 AINV MU WZ IMG) as X; (first [ dand10 X as _ _ _ _ _ _ X1 X2 X3 X4 | destruct X as (_ & _ & _ & _ & _ & _ & X1 & X2 & X3 & X4) ]);
              destruct TAB4 as [(Y & X & _)|[(Y & X & _)|[(Y & X & _)|(Y & X & _)]]]; rewrite X, Y; assumption) end.
      pose proof (mtab_read_ptr rsegs _ Tb es i e _ ITB Hnth eq_refl) as RD1. unfold wa in RD1.
      zstep. clear RD1 ITB. cbv beta.
      (* [comment removed for export] *)
      assert (P804 : forall (p' : Z) (j24' ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc : mem),
        munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 80, pe_sp E); (pe_sp E + 24, pe_sp E + 32)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
        rw_cells rsegs mc (pe_VEP E) (vep_cells (fupd (x_v x) Fmatch_hit (Tb + 16 * Z.of_nat i)) (x_tag x) (x_q x)) ->
        rw_cells rsegs mc (pe_sp E) (pframe E j0 j8 j16 j24') ->
        bytes_at rsegs mc (pe_DATA E) (pe_inp E) -> stk rsegs mc (pe_lo E) (pe_sp E) ->
        ((me_ptr e = 0 /\ me_str e = [] /\ p' = x_p x) \/
         (me_ptr e <> 0 /\ is_prefixb (me_str e) inp' = true /\ p' = x_p x + Z.of_nat (length (me_str e)) /\ (1 <= length (me_str e) <= 8)%nat)) ->
        realizes rsegs (mkCfg (lms E 0x1ad70 (Z_to_bv 64 (x_p x)) (Z_to_bv 64 p') ra' t0' t1' t2' a0' (Z_to_bv 64 (Tb + 16 * Z.of_nat i)) a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mc) md) T).
      { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc STKc HP. unfold lms.
        clear VEPC FR DBY STK MI STRS1.
        unfold vep_cells in VEPCc. psimp_in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
        assert (LP : x_p x <= p' <= pe_e E).
        { destruct HP as [(_ & _ & ->)|(_ & PF & -> & _)]; [clear - PLE; unfold pe_e, pe_N; lia|].
          apply is_prefixb_length in PF. revert PF LINP PLE. clear. unfold pe_e, pe_N. intros. lia. }
        apply rz_go; [exact MDH| exact MDL|].
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          assert (ITB : ro_cells rsegs mc Tb (mtab_cells es))
            by (pose proof (img_stores E A m mc md _ _ PE0 AINV MUc WZ IMG) as X; (first [ dand10 X as _ _ _ _ _ _ X1 X2 X3 X4 | destruct X as (_ & _ & _ & _ & _ & _ & X1 & X2 & X3 & X4) ]);
                destruct TAB4 as [(Y & X & _)|[(Y & X & _)|[(Y & X & _)|(Y & X & _)]]]; rewrite X, Y; assumption) end.
        pose proof (mtab_read_svar rsegs _ Tb es i e _ ITB Hnth eq_refl) as RD2. unfold wa in RD2.
        zstep. clear RD2 ITB. cbv beta. rewrite Esv.
        assert (SVR : 0 <= VEPVARSU + Z.of_nat k < 2^64)
          by (pose proof (cell_at_bound _ _ _ Hcell) as KB; revert KB; clear; cbn [cells_size vepvarsU csize List.fold_right]; unfold VEPVARSU; intros; lia).
        zstep. if_cases KT; zify_cond KT. { exfalso. revert KT. clear. unfold VEPVARSU. lia. } clear KT.
        zstep. zstep. if_cases KT; zify_cond KT. { exfalso. apply KT. apply land7_of_mod8; [clear; unfold VEPVARSU; lia| exact SV8]. } clear KT.
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          assert (IVV : ro_cells rsegs mc VEPVARSU vepvarsU)
            by (pose proof (img_stores E A m mc md _ _ PE0 AINV MUc WZ IMG) as X; (first [ dand7 X as _ _ _ _ _ X1 _ | destruct X as (_ & _ & _ & _ & _ & X1 & _) ]); exact X1) end.
        pose proof (ro_cells_read_at rsegs _ VEPVARSU vepvarsU k _ 8 _ IVV Hcell eq_refl eq_refl) as RD3. unfold wa in RD3. cbn [cbytes] in RD3.
        zstep. clear RD3 IVV. cbv beta.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        apply rz_stop.
        match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
          assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
            by (eapply (henv_stores E A _ _ md _ _ PE0 AINV MUc WMc WZ); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2 PSP; lia| exact HENV])
        end.
        (* [comment removed for export] *)
        assert (LKM : Tb = TBL_attr_include -> vct_xmlname (look E x) = true).
        { intros ETB. (first [ pose proof ((look_read rsegs E x _ DBYc ltac:(clear - VERP; lia) PLT)) as dR_12; dex1 dR_12 as b; dand3 dR_12 as Hb Hlk _ | pose proof ((look_read rsegs E x _ DBYc ltac:(clear - VERP; lia) PLT)) as dR_12; dand4 dR_12 as b Hb Hlk _ | destruct (look_read rsegs E x _ DBYc ltac:(clear - VERP; lia) PLT) as (b & Hb & Hlk & _) ]).
          pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR. rewrite <- Hlk.
          apply (proj1 (vct_namestart_facts _ BR ltac:(rewrite Hlk; apply (LOOKM eq_refl); [rewrite TM; exact ETB| exact PLT]))). }
        eapply (KL (PST p' S' (fupd (fupd (fupd (fupd (x_v x) Fmatch_hit (Tb + 16 * Z.of_nat i)) Fstate (stU S')) Fmatch 0) Ftag_i 0)
                        (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
        2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MUc WMc WZ). }
        2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
        2:{ eapply hstep_stores; [exact MUc | | eapply parse_window_mapped; [exact PE0| exact STKc| exact FRc]
                                 | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
            w_in_zone_tac. left. unfold blk. lia. }
        (* [comment removed for export] *)
        all: destruct TAB4 as [(ETb & Ees & Ets)|[(ETb & Ees & Ets)|[(ETb & Ees & Ets)|(ETb & Ees & Ets)]]]; subst ts es;
          (destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn in Hts; try discriminate Hts);
          injection Hts as EK ES'; subst k S'; cbn in Hnth; injection Hnth as Ee; subst e; cbn [me_ptr me_str length] in HP;
          rewrite ETb in TM, LKM, VEPCc |- *.
        (* [comment removed for export] *)
        17-32: psimp; intros _; split; [| discriminate]; unfold phi, rank; psimp; rewrite ST, TM;
          unfold TBL_bom, TBL_starttag, TBL_esi, TBL_attr_include; cbn [Z.eqb Pos.eqb];
          destruct HP as [(Z0 & _ & EP)|(NZ & PF & EP & LEN)]; subst p'; try (exfalso; clear - Z0; lia); try (exfalso; clear - NZ; lia);
          try (unfold look; cbn [x_p]; unfold look in LKM; rewrite (LKM eq_refl)); clear - PLT; lia.
        (* [comment removed for export] *)
        all: apply Build_pinv; psimp; pinv_close PE0 AINV MUc WMc WZ.
        all: lazymatch goal with
          | |- _ <= _ Fver_p <= _ => clear - VERP LP; lia
          | |- _ <= pe_e _ => clear - LP; lia
          | |- 0 <= 0 <= 7 => clear; lia
          | |- _ = 0 \/ _ =>
              destruct ATTR as [A0|(A1 & A2 & A3)]; [left; exact A0| exfalso; destruct A3 as [A3|[A3|[A3|A3]]];
                [rewrite TM in A3; revert A3; clear; unfold TBL_bom, TBL_starttag, TBL_esi, TBL_attr_include; intros; lia
                | discriminate A3| discriminate A3| discriminate A3]]
          | |- _ + _ + _ + _ <= _ => revert OUT LP HP; unfold oacost, oicost; cbn [x_va x_vi x_st x_p x_vv]; clear; intros; lia
          | |- True -> _ <> 0 => intros _; apply ARMED; exact TM
          | |- True -> _ -> _ /\ _ => intros _ _; split; [exact (MATTR eq_refl TM)| cbn [Z.of_nat Pos.of_succ_nat]; first [left; clear; lia | right; clear; lia]]
          end. }
      (* [comment removed for export] *)
      pose proof (wf_ptr_nonneg _ _ _ WF Hnth) as PR.
      zstep. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        zstep. apply rz_stop. destruct CASES as [[Z0 ZS]|(NZ & _)]; [| exfalso; exact (NZ K2)].
        eapply (P804 (x_p x)); [exact MU| exact WM| exact MI| unfold vep_cells; psimp; rewrite STATE; exact VEPC| unfold pframe; exact FR| exact DBY| exact STK
                              | left; split; [exact Z0| split; [exact ZS| reflexivity]]]. }
      destruct CASES as [[Z0 _]|(NZ & PF & LEN)]; [exfalso; exact (K2 Z0)|].
      (first [ pose proof ((wf_entry _ _ _ WF Hnth NZ)) as dR_13; dand3 dR_13 as _ NONUL _ | pose proof (wf_entry _ _ _ WF Hnth NZ) as (_ & NONUL & _) ]).
      (* [comment removed for export] *)
      zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (STRS2 : mtab_strings mc es)
          by (destruct TAB4 as [(_ & X & _)|[(_ & X & _)|[(_ & X & _)|(_ & X & _)]]]; rewrite X;
              [apply tbl_bom_strings| apply tbl_attr_include_strings| apply tbl_esi_strings| apply tbl_starttag_strings]; assumption) end.
      (first [ pose proof ((STRS2 i e Hnth NZ)) as dR_14; dex1 dR_14 as slack; dand3 dR_14 as SB SPAD SLEN | pose proof ((STRS2 i e Hnth NZ)) as dR_14; dand4 dR_14 as slack SB SPAD SLEN | destruct (STRS2 i e Hnth NZ) as (slack & SB & SPAD & SLEN) ]). clear STRS2.
      hide_slow.
      call_fr (strlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bvmap_empty (Z_to_bv 32 0) _ (me_str e) slack) by idtac.
      1:{ rewrite unsigned_lit by exact PR. exact SB. }
      1:{ exact NONUL. }
      1:{ rewrite unsigned_lit by exact PR. exact SPAD. }
      1:{ assumption. }
      unhide_slow. rename POST into SB2.
      try match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
      (* [comment removed for export] *)
      assert (PR2 : 0 <= Z.of_nat (length (me_str e)) + x_p x < 2^64) by (revert LEN VERP Dlo PLT Dhi CV; clear; unfold pe_e, pe_N; intros; lia).
      assert (PR3 : 0 <= x_p x < 2^64) by (revert VERP Dlo PLT Dhi CV; clear; unfold pe_e, pe_N; intros; lia).
      zstep. zstep. if_cases KT; zify_cond KT. { exfalso. revert KT LEN. clear. intros. first [rewrite !Z.mod_small in KT by lia | idtac]. lia. } clear KT.
      zstep. zstep. zstep.
      replace (0 <? x_p x) with true by (symmetry; apply Z.ltb_lt; revert VERP Dlo; clear; intros; lia).
      replace (Z.of_nat (length (me_str e)) + x_p x <? 1) with false by (symmetry; apply Z.ltb_ge; revert VERP Dlo; clear; intros; lia).
      change (Z.lxor (Z.b2z true) (Z.b2z false)) with 1.
      zstep. if_cases KT; zify_cond KT. { exfalso. revert KT. clear. intros. lia. } clear KT.
      zstep. zstep.
      apply rz_stop.
      replace (Z.of_nat (length (me_str e)) + x_p x) with (x_p x + Z.of_nat (length (me_str e))) by (clear; lia).
      eapply (P804 (x_p x + Z.of_nat (length (me_str e))));
        [exact MU| exact WM| assumption| unfold vep_cells; psimp; rewrite STATE; exact VEPC| unfold pframe; exact FR| exact DBY| exact STK
        | right; split; [exact NZ| split; [exact PF| split; [reflexivity| exact LEN]]]].
    - (* [comment removed for export] *)
      pose proof (vm_find_none es inp' WF VF) as LIN.
      assert (NR : 0 <= pe_e E - x_p x <= 7) by (revert LIN LINP PLT; clear; intros; lia).
      (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. } clear K1.
      (* [comment removed for export] *)
      assert (PR8 : 0 <= x_p x + 8 < 2^64) by (revert VERP Dlo PLT Dhi CV; clear; unfold pe_e, pe_N; intros; lia).
      zstep. zstep. zstep. if_cases K3; zify_cond K3.
      { exfalso. revert K3 VERP Dlo. clear. intros. first [rewrite Z.mod_small in K3 by lia | idtac]. lia. }
      clear K3.
      zstep. if_cases K3; zify_cond K3.
      { exfalso. revert K3 NR VERP Dlo PLT Dhi CV. clear. unfold pe_e, pe_N. intros. first [rewrite Z.mod_small in K3 by lia | idtac]. lia. }
      clear K3.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      set (n := Z.to_nat (pe_e E - x_p x)).
      assert (LN : length inp' = n) by (subst n; revert LINP; clear; intros; lia).
      assert (LT8 : (n <= 8)%nat) by (subst n; revert NR; clear; intros; lia).
      (first [ pose proof ((pd_split3 rsegs _ (pe_VEP E) _ 41 (CB 8 (x_tag x)) VEPC eq_refl)) as dR_15; dand3 dR_15 as VXA VXT VXB | pose proof (pd_split3 rsegs _ (pe_VEP E) _ 41 (CB 8 (x_tag x)) VEPC eq_refl) as (VXA & VXT & VXB) ]).
      cbn [firstn skipn cells_size csize Nat.add length] in VXA, VXT, VXB.
      change (Z.of_nat 256) with 256 in VXT. change (Z.of_nat 256) with 256 in VXB. change (Z.of_nat 8) with 8 in VXB.
      replace (pe_VEP E + 256 + 8) with (pe_VEP E + 264) in VXB by (clear; lia).
      apply (rw_cells_recast rsegs _ (pe_VEP E + 256) _ [CB n (firstn n (x_tag x)); CB (8 - n) (skipn n (x_tag x))]) in VXT;
        [| cbn; rewrite firstn_length, skipn_length; revert TAG LT8; clear; intros; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia
         | cbn [cells_bytes cbytes]; rewrite !app_nil_r; rewrite firstn_skipn; reflexivity].
      apply (proj1 (rw_cells_app rsegs _ _ [CB n (firstn n (x_tag x))] [CB (8 - n) (skipn n (x_tag x))])) in VXT.
      destruct VXT as [VXT1 VXT2]. cbn [cells_size csize Nat.add] in VXT2.
      clear VEPC. hide_slow.
      call_fr (memcpy_spec_z _ _ _ _ _ _ _ _ _ (pe_VEP E + 256) (x_p x) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 bvmap_empty (Z_to_bv 32 0) _ inp' (firstn n (x_tag x))) by idtac.
      1:{ rewrite LINP. unfold pe_e, pe_N. reflexivity. }
      1:{ subst inp'. apply pslice_bytes; [exact DBY| clear - VERP; lia| exact PLE| clear; unfold pe_e, pe_N; lia]. }
      1:{ rewrite LN. exact VXT1. }
      1:{ revert DJ_VD VERP PLE NR. clear. unfold pe_e, pe_N. intros. lia. }
      1:{ clear - VEPhi CV. lia. }
      1:{ clear - PLT Dhi CV. unfold pe_e, pe_N in *. lia. }
      1:{ exact MI. }
      unhide_slow.
      lazymatch goal with H : rw_cells rsegs ?mc (pe_VEP E + 256) [CB (length inp') inp'] |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into DST end.
      try match goal with |- context [ret_pc (Z_to_bv 64 ?n0)] =>
        replace (ret_pc (Z_to_bv 64 n0)) with (Z_to_bv 64 n0) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
      (* [comment removed for export] *)
      set (tag' := inp' ++ skipn n (x_tag x)).
      assert (TAG' : length tag' = 8%nat) by (subst tag'; rewrite length_app, skipn_length, LN; revert TAG LT8; clear; intros; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        assert (VEPC : rw_cells rsegs mf (pe_VEP E) (vep_cells (fupd (x_v x) Fmatch_hit 0) tag' (x_q x))) end.
      { subst tag'. unfold vep_cells. psimp. rewrite STATE.
        lazymatch type of VXA with rw_cells _ _ _ ?pre =>
          apply (pd_join3 rsegs _ (pe_VEP E) pre (CB 8 (inp' ++ skipn n (x_tag x)))); [exact VXA| |] end.
        - cbn [cells_size csize Nat.add length]. change (Z.of_nat 256) with 256.
          apply (rw_cells_recast rsegs _ (pe_VEP E + 256) [CB n inp'; CB (8 - n) (skipn n (x_tag x))]).
          + apply (proj2 (rw_cells_app rsegs _ _ [CB n inp'] [CB (8 - n) (skipn n (x_tag x))])).
            split; [rewrite <- LN; exact DST|]. cbn [cells_size csize Nat.add]. exact VXT2.
          + cbn. rewrite length_app, skipn_length, LN. revert TAG LT8. clear. intros. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
          + cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
        - cbn [cells_size csize Nat.add length]. change (Z.of_nat 256) with 256. change (Z.of_nat 8) with 8.
          replace (pe_VEP E + 256 + 8) with (pe_VEP E + 264) by (clear; lia). exact VXB. }
      clear VXA VXB VXT2 DST POST. unfold vep_cells in VEPC. psimp_in VEPC. rewrite STATE in VEPC.
      (* [comment removed for export] *)
      assert (NR64 : 0 <= pe_e E - x_p x < 2^64) by (revert NR; clear; intros; lia).
      assert (NR32 : 0 <= pe_e E - x_p x < 2^32) by (revert NR; clear; intros; lia).
      zstep. zstep. zstep. zstep. zstep. zstep.
      apply rz_stop.
      set (v' := fupd (fupd (fupd (x_v x) Fmatch_hit 0) Ftag_i (pe_e E - x_p x)) Fstate (stU S_MatchBuf)).
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
          by (eapply (henv_stores E A _ _ md _ _ PE0 AINV MU WM WZ); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2 PSP; lia| exact HENV])
      end.
      eapply (KX (PST (pe_e E) S_MatchBuf v' tag' (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
      2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
      2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
      2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; subst v'; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; subst v'; refine (parse_new_same E x _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      2:{ reflexivity. }
      subst v'. apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
      + (* [comment removed for export] *) clear - VERP PLE. unfold pe_e, pe_N. lia.
      + (* [comment removed for export] *) revert OUT PLE. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. unfold pe_e, pe_N. intros; lia.
  Qed.
End S.

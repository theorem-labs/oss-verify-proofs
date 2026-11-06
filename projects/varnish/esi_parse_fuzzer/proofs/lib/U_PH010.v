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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_Pahif U_PKit U_PMark U_Pahbe V_PH51p ImgU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_La7nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Cov8m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahbe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.

Module U_PH1yj.
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

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  Lemma PH_end_ESITag : handler_stmt S_end_ESITag.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    apply rz_go; [exact MDH| exact MDL|].
    zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    eapply (KL (PST (x_p x) S_ESITag (fupd (fupd (x_v x) Fstate (stU S_ESITag)) Fendtag 1)
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
  Qed.
End S.
End U_PH1yj.

Module U_PH_BOM.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_Pahif U_PKit U_PMark U_Pahbe ImgU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_La7nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Cov8m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahbe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU.
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

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_BOM : handler_stmt S_BOM.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    pose proof PI as PI0.
    handler_prologue PE PI AINV ST.
    apply rz_go; [exact MDH| exact MDL|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    apply rz_stop.
    (* [comment removed for export] *)
    eapply (mark_call HMC E x A m md T (x_p x) 1 0x1a378);
      [ exact PE | exact PI0 | exact AINV | clear; lia | exact PLE | right; reflexivity | clear; lia | reflexivity
      | rewrite ST; intros [X|X]; discriminate X | ].
    intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1.
    assert (ST1 : x_st x1 = S_BOM) by (rewrite EX1, <- ST; reflexivity).
    assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
    assert (EP1 : x_p x1 = x_p x) by (rewrite EX1; reflexivity).
    assert (EQ1 : x_tag x1 = x_tag x /\ x_q x1 = x_q x /\ x_va x1 = x_va x /\ x_vi x1 = x_vi x) by (rewrite EX1; repeat split; reflexivity).
    clear - HMC PE ST PLT KL KX PI1 AINV' MDF HS VK VERP1 LM1 OP1 ST1 EV1 EP1 EQ1.
    pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
    world_open PE PI1 AINV'. rewrite <- EP1.
    (* [comment removed for export] *)
    unfold loop_ms, lms.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
    assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    apply rz_go; [exact MDH'| exact MDL'|].
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    pose proof (rw_cells_read_sub rsegs _ _ _ 4 1 VEPC ltac:(clear; lia) ltac:(cbn; clear; lia)) as RDF.
    match type of RDF with _ = Some ?r => change r with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x1 Fflags)))] in RDF end.
    remember (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x1 Fflags)))) as fb eqn:Efb in RDF.
    set (RWv := rw_cells rsegs m2 (pe_VEP E)) in VEPC.
    zstep. subst RWv. clear RDF. cbv beta.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. apply rz_stop.
      eapply (KL (PST (x_p x1) S_NxtTag
                      (fupd (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) Fstate (stU S_NxtTag))
                      (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ md1).
      2:{ eapply (ainv_stores E A1 m2 _ md1 _ _ PE0 AINV' MU WM WZ). }
      2:{ exact MDF. }
      2:{ eapply hstep_trans; [exact HS|].
          eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      (* [comment removed for export] *)
      2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST, EP1. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. apply rz_stop.
      eapply (KL (PST (x_p x1) S_TestXml
                      (fupd (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) Fstate (stU S_TestXml))
                      (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ md1).
      2:{ eapply (ainv_stores E A1 m2 _ md1 _ _ PE0 AINV' MU WM WZ). }
      2:{ exact MDF. }
      2:{ eapply hstep_trans; [exact HS|].
          eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      (* [comment removed for export] *)
      2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST, EP1. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ.
  Qed.
End S.
End U_PH_BOM.

Module U_PHrp1.
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

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  Lemma PH_Start : handler_stmt S_Start.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    (* [comment removed for export] *)
    pose proof (rw_cells_read_sub rsegs _ _ _ 4 1 VEPC ltac:(clear; lia) ltac:(cbn; clear; lia)) as RDF.
    match type of RDF with _ = Some ?r => change r with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x Fflags)))] in RDF end.
    (* [comment removed for export] *)
    remember (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x Fflags)))) as fb eqn:Efb in RDF.
    (* [comment removed for export] *)
    assert (GOBOM : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      realizes rsegs (mkCfg (loop_ms E 0x1a360 (x_p x) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' m) md) T).
    { intros. unfold loop_ms, lms. apply rz_go; [exact MDH| exact MDL|].
      zstep. zstep. zstep.
      apply rz_stop.
      eapply (KL (PST (x_p x) S_BOM (fupd (x_v x) Fstate (stU S_BOM)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
      2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
      2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
      2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ. }
    apply rz_go; [exact MDH| exact MDL|].
    (* [comment removed for export] *)
    set (RWv := rw_cells rsegs m (pe_VEP E)) in VEPC.   (* [comment removed for export] *)
    zstep. subst RWv. clear RDF. cbv beta. zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *) apply rz_stop. apply GOBOM. }
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT VERP Dlo. lia. }
    clear KT.
    (* [comment removed for export] *)
    destruct (look_read rsegs E x m DBY ltac:(clear - VERP; lia) PLT) as (b & Hnth & Hlook & RDP).
    pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
    zstep. clear RDP. cbv beta. zstep. zstep. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *) apply rz_stop. apply GOBOM. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    eapply (KL (PST (x_p x) S_Match (fupd (fupd (x_v x) Fmatch TBL_bom) Fstate (stU S_Match))
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
  Qed.
End S.
End U_PHrp1.

Module U_PHxiy.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_Pahif U_PKit U_PMark U_Pahbe V_PH51p ImgU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_La7nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Cov8m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahbe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU.
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

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_NotMyTag : handler_stmt S_NotMyTag.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    pose proof PI as PI0.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (PHI : phi E x = 16 * (pe_e E - x_p x) + 1) by (unfold phi, rank; rewrite ST; reflexivity).
    (* [comment removed for export] *)
    assert (TAIL_E : forall (xc : pst) (mc : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc -> x_p xc = pe_e E ->
      realizes rsegs (mkCfg (lms E 0x1a5a0 s7' (Z_to_bv 64 (x_p xc)) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mc) md) T).
    { intros until t6'. intros PIc AINVc HSc EPc.
      clear - HMC PE ST PLT KL PIc AINVc HSc EPc MDL MDH.
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold lms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU. pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E A [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. destruct B_rm as [RM|RM]; rewrite RM, ?sx32_zero, ?sx32_one.
      2:{ (* [comment removed for export] *)
          zstep. if_cases K1; zify_cond K1. 2:{ dead K1. } clear K1.
          apply rz_stop.
          eapply (KL xc A mc md); [exact PIc0| exact AINVc| apply md_frame_refl; [exact MDL| exact MDH]| exact HSc|].
          rewrite EPc. intros H. exfalso. clear - H. lia. }
      zstep. if_cases K1; zify_cond K1. { dead K1. } clear K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (mark_call HMC E xc A mc md T (x_p xc) 0 0x1a5b8);
        [ exact PE | exact PIc0 | exact AINVc | clear; lia | rewrite EPc; clear; lia | left; reflexivity | clear; lia | reflexivity
        | intros _; reflexivity | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (HS2 : hstep E x x1 A A1 m m2) by (eapply hstep_trans; [exact HSc| exact HS]).
      assert (ST1 : x_st x1 = x_st xc) by (rewrite EX1; reflexivity).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
      clear - HMC PE KL PI1 AINV' MDF HS2 VK VERP1 LM1 OP1 ST1 EV1 EP1 EPc.
      pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
      world_open PE PI1 AINV'. rewrite <- EP1. rewrite <- EP1 in EPc.
      unfold loop_ms, lms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH'| exact MDL'|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (KL (PST (x_p x1) (x_st x1)
                      (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1))
                      (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ md1).
      2:{ eapply (ainv_stores E A1 m2 _ md1 _ _ PE0 AINV' MU WM WZ). }
      2:{ exact MDF. }
      2:{ eapply hstep_trans; [exact HS2|].
          eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      2:{ psimp. rewrite EPc. intros H. exfalso. clear - H. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ.
      (* [comment removed for export] *)
      all: rewrite ?ST1; try assumption.
      exact (conj DELIM1 DELIM2). }

    (* [comment removed for export] *)
    assert (G3F0 : forall (xc : pst) (mc : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc -> x_st xc = S_NotMyTag -> x_p x < x_p xc -> x_p xc <= pe_e E ->
      realizes rsegs (mkCfg (lms E 0x1a528 s7' (Z_to_bv 64 (x_p xc)) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mc) md) T).
    { intros until t6'. intros PIc AINVc HSc STc LTc LEc.
      clear - HMC PE PHI KL TAIL_E PIc AINVc HSc STc LTc LEc MDL MDH.
      world_open PE PIc AINVc. unfold lms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU. pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E A [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep.
      set (x2 := PST (x_p xc) S_NxtTag (fupd (x_v xc) Fstate (stU S_NxtTag)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)).
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        pose proof (ainv_stores E A mc mf md _ _ PE0 AINVc MU WM WZ) as AINV2;
        assert (PI2 : pinv E x2 A mf); [| assert (HS2 : hstep E x x2 A A m mf)] end.
      { subst x2. apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ. }
      { eapply hstep_trans; [exact HSc|].
        eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
        subst x2. w_in_zone_tac. left. unfold blk. lia. }
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      { apply rz_stop. eapply (TAIL_E x2); [exact PI2| exact AINV2| exact HS2| subst x2; cbn [x_p]; exact K1]. }
      (* [comment removed for export] *)
      zstep. apply rz_stop.
      eapply (KL x2 A _ md); [exact PI2| exact AINV2| apply md_frame_refl; [exact MDL| exact MDH]| exact HS2|].
      subst x2. psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LTc. lia. }
    (* [comment removed for export] *)
    pose proof (rw_cells_read_sub rsegs _ _ _ 4 1 VEPC ltac:(clear; lia) ltac:(cbn; clear; lia)) as RDF.
    match type of RDF with _ = Some ?r => change r with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x Fflags)))] in RDF end.
    remember (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x Fflags)))) as fb eqn:Efb in RDF.
    apply rz_go; [exact MDH| exact MDL|].
    set (RWv := rw_cells rsegs m (pe_VEP E)) in VEPC.
    zstep. subst RWv. clear RDF. cbv beta. zstep. zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases KT; zify_cond KT.
      { exfalso. revert KT VERP Dlo PLT Dhi CV. clear. intros. first [rewrite Z.mod_small in KT by lia | idtac]. lia. }
      clear KT.
      apply rz_stop.
      set (xa := PST (x_p x + 1) S_NotMyTag (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
      assert (PIa : pinv E xa A m); [| assert (HSa : hstep E x xa A A m m)].
      { subst xa. apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
        + (* [comment removed for export] *) clear - VERP. lia.
        + (* [comment removed for export] *) clear - PLT. unfold pe_e, pe_N in *. lia. }
      { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
      eapply (G3F0 xa); [exact PIa| exact AINV| exact HSa| reflexivity| subst xa; cbn [x_p]; clear; lia| subst xa; cbn [x_p]; clear - PLT; unfold pe_e, pe_N in *; lia].
    - (* [comment removed for export] *)
      zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (CK : forall q, x_p x <= q -> q <= pe_e E ->
        pinv E (PST q S_NotMyTag (fupd (x_v x) Ftag_i 0) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A mc
        /\ hstep E x (PST q S_NotMyTag (fupd (x_v x) Ftag_i 0) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A A m mc);
      [| pose proof (ainv_stores E A m mc md _ _ PE0 AINV MU WM WZ) as AINV1;
         assert (LOOP : forall (k : nat) (q : Z) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' t3' t4' t5' t6' : word),
                q + Z.of_nat k = pe_e E -> x_p x <= q -> q <= pe_e E ->
                evt rsegs (rz_at rsegs md T)
                    (loop_ms E 0x1a408 q ra' t0' t1' t2' (Z_to_bv 64 q) a1' a2' a3' a4' a5' a6' a7' s8' t3' t4' t5' t6' mc)) ]
      end.
      { intros q LQ QE. split.
        - apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
          + (* [comment removed for export] *) clear - VERP LQ. lia.
          + (* [comment removed for export] *) clear. lia.
          + (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
        - eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      { (* [comment removed for export] *)
        induction k as [|k IH]; intros until t6'; intros Hk LQ QE; unfold loop_ms, lms.
        - (* [comment removed for export] *)
          zstep. if_cases Kb; zify_cond Kb. 2:{ exfalso. clear - Kb Hk. lia. }
          zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. apply Kc. clear - Hk. lia. }
          apply rz_stop. destruct (CK q LQ QE) as [PIc HSc].
          eapply (TAIL_E (PST q S_NotMyTag (fupd (x_v x) Ftag_i 0) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)));
            [exact PIc| exact AINV1| exact HSc| cbn [x_p]; clear - Hk; lia].
        - zstep. if_cases Kb; zify_cond Kb. { exfalso. clear - Kb Hk. lia. } clear Kb.
          (* [comment removed for export] *)
          assert (QR : 0 <= q + 1 < 2^64) by (revert LQ QE VERP Dlo Dhi CV; clear; unfold pe_e, pe_N; intros; lia).
          zstep. zstep. if_cases KT; zify_cond KT.
          { exfalso. revert KT QR LQ VERP Dlo. clear. intros. first [rewrite Z.mod_small in KT by lia | idtac]. lia. }
          clear KT.
          (* [comment removed for export] *)
          destruct (payload_read rsegs E _ q DBY ltac:(clear - LQ VERP; lia) ltac:(clear - Hk; unfold pe_e, pe_N in *; lia)) as (b & Hnth & RDP).
          pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
          zstep. clear RDP. cbv beta.
          zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
          + (* [comment removed for export] *)
            eapply (IH (q + 1)); [clear - Hk; lia| clear - LQ; lia| clear - Hk; lia].
          + (* [comment removed for export] *)
            zstep. apply rz_stop. destruct (CK (q + 1) ltac:(clear - LQ; lia) ltac:(clear - Hk; lia)) as [PIc HSc].
            eapply (G3F0 (PST (q + 1) S_NotMyTag (fupd (x_v x) Ftag_i 0) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)));
              [exact PIc| exact AINV1| exact HSc| reflexivity| cbn [x_p]; clear - LQ; lia| cbn [x_p]; clear - Hk; lia]. }
      eapply (LOOP (Z.to_nat (pe_e E - x_p x)) (x_p x)); [clear - PLT; rewrite Z2Nat.id by lia; lia| clear; lia| clear - PLT; lia].
  Qed.
End S.
End U_PHxiy.

Module U_PHyeb.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_Pahif U_PKit U_PMark U_Pahbe V_PH51p ImgU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_La7nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Cov8m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahbe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU.
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

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_NotXml : handler_stmt S_NotXml.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    pose proof PI as PI0.
    handler_prologue PE PI AINV ST.
    apply rz_go; [exact MDH| exact MDL|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    apply rz_stop.
    (* [comment removed for export] *)
    eapply (mark_call HMC E x A m md T (pe_e E) 0 0x1ae74);
      [ exact PE | exact PI0 | exact AINV | clear - PLT; lia | clear; lia | left; reflexivity | clear; lia | reflexivity
      | rewrite ST; intros [X|X]; discriminate X | ].
    intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1.
    assert (ST1 : x_st x1 = S_NotXml) by (rewrite EX1, <- ST; reflexivity).
    assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
    assert (EP1 : x_p x1 = pe_e E) by (rewrite EX1; reflexivity).
    assert (EQ1 : x_tag x1 = x_tag x /\ x_q x1 = x_q x /\ x_va x1 = x_va x /\ x_vi x1 = x_vi x) by (rewrite EX1; repeat split; reflexivity).
    clear - HMC PE ST PLT KL KX PI1 AINV' MDF HS VK VERP1 LM1 OP1 ST1 EV1 EP1 EQ1.
    pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
    world_open PE PI1 AINV'.
    (* [comment removed for export] *)
    unfold loop_ms, lms.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
    assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    apply rz_go; [exact MDH'| exact MDL'|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    apply rz_stop.
    eapply (KX (PST (pe_e E) S_NotXml
                    (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1))
                    (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ md1).
    2:{ eapply (ainv_stores E A1 m2 _ md1 _ _ PE0 AINV' MU WM WZ). }
    2:{ exact MDF. }
    2:{ eapply hstep_trans; [exact HS|].
        eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
    2:{ reflexivity. }
    apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ.
    - (* [comment removed for export] *) rewrite <- EP1. exact VERP.
    - (* [comment removed for export] *) revert OUT. rewrite ?ST1, EP1. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
  Qed.
End S.
End U_PHyeb.


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
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
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

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Hypothesis HMC : vep_mark_common_stmt.
  Hypothesis HVE : vep_error_stmt.
  Hypothesis HDC : vep_do_comment_stmt.
  Hypothesis HDR : vep_do_remove_stmt.
  Hypothesis HDIT : vep_do_include_tag_stmt.

  Section X.
    Variables (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet).
    Hypothesis PE : penv_ok E.
    Hypothesis PHI : phi E x = 16 * (pe_e E - x_p x) + 5.
    Hypothesis KL : latch_K E x A m md T.

    (* [comment removed for export] *)
    #[using="KL PHI PE HDC"] Lemma intag_do_comment : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
        (s7 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      pinv E xc Ac mc -> ainv Ac mc mdc -> md_frame md mdc -> hstep E x xc A Ac m mc ->
      x_st xc = S_InTag -> x_p x < x_p xc ->
      realizes rsegs (mkCfg (lms E vep_do_comment_entry s7 (Z_to_bv 64 (x_p xc)) (Z_to_bv 64 0x1a9bc) t0 t1 t2
                               (Z_to_bv 64 (pe_VEP E)) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc AINVc MDFc HSc STc LT.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      world_open PE PIc AINVc. unfold lms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] mc) as MU.
      pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
      assert (EVS : VEPERR_STACK = 48) by reflexivity.
      assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
      apply rz_go; [exact MDH| exact MDL|].
      hide STK. hide_slow.
      call_fr (HDC (pe_VEP E) (x_v xc) (x_tag xc) (x_q xc) (pe_H E) (pe_lo E)) by idtac.
      1:{ reflexivity. }
      1:{ reflexivity. }
      1:{ unfold vep_cells. rewrite STATE. exact VEPC. }
      1:{ exact TAG. }
      1:{ exact PADS. }
      1:{ exact B_em. }
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
      rename PC into HENV1. rename POST into STK.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
        pose proof (ainv_stores E Ac mc m1 mdc _ _ PE0 AINVc MU WM WZ) as AINV1;
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m1) as MU2; pose proof (wmono_refl rsegs m1) as WM2 end.
      assert (WZ2 : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                            [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
          by (eapply (henv_stores E Ac _ _ mdc _ _ PE0 AINV1 MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV1])
      end.
      eapply (KL (PST (x_p xc) S_NxtTag (fupd (fupd (x_v xc) Fin_esi_tag 0) Fstate (stU S_NxtTag))
                      (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) Ac _ mdc).
      2:{ eapply (ainv_stores E Ac mc _ mdc _ _ PE0 AINVc MU WM WZ). }
      2:{ exact MDFc. }
      2:{ eapply hstep_trans; [exact HSc|].
          eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
          w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
      2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LT. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ.
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HDR"] Lemma intag_do_remove : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
        (s7 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      pinv E xc Ac mc -> ainv Ac mc mdc -> md_frame md mdc -> hstep E x xc A Ac m mc ->
      x_st xc = S_InTag -> x_p x < x_p xc ->
      realizes rsegs (mkCfg (lms E vep_do_remove_entry s7 (Z_to_bv 64 (x_p xc)) (Z_to_bv 64 0x1a9bc) t0 t1 t2
                               (Z_to_bv 64 (pe_VEP E)) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc AINVc MDFc HSc STc LT.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      world_open PE PIc AINVc. unfold lms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] mc) as MU.
      pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
      assert (EVS : VEPERR_STACK = 48) by reflexivity.
      assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
      apply rz_go; [exact MDH| exact MDL|].
      hide STK. hide_slow.
      try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_VEPC); call_fr (HDR (pe_VEP E) (x_v xc) (x_tag xc) (x_q xc) (pe_H E) (pe_lo E)) by idtac.
      1:{ reflexivity. }
      1:{ reflexivity. }
      1:{ unfold vep_cells. rewrite STATE. exact VEPC. }
      1:{ exact TAG. }
      1:{ exact PADS. }
      1:{ exact B_em. }
      1:{ exact B_et. }
      1:{ exact B_rm. }
      1:{ exact (proj1 BASE). }
      1:{ exact HENV. }
      1:{ exact (proj1 PE0). }
      1:{ exact IMG. }
      1:{ exact VEPlo. }
      1:{ apply mod8_of_mod16. exact VEP16. }
      1:{ clear - VEPhi. lia. }
      1:{ exact VEPimg. }
      1:{ unhide STK. rewrite unsigned_lit by exact SPR. exact STK. }
      1:{ rewrite unsigned_lit by exact SPR. rewrite EVS, PSP. clear - LOP. lia. }
      1:{ exact CEIL. }
      1:{ rewrite unsigned_lit by exact SPR. rewrite PSP. clear. lia. }
      1:{ exact MI. }
      clear STK. unhide_slow.
      try match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
      rename PC into HENV1. rename PC0 into STK. rename PC1 into RM. rename POST into VEPC.
      lazymatch type of RM with bool01 ?r => rename r into rm end.
      unfold vep_cells in VEPC. psimp_in VEPC. rewrite STATE in VEPC.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
        pose proof (ainv_stores E Ac mc m1 mdc _ _ PE0 AINVc MU WM WZ) as AINV1;
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m1) as MU2; pose proof (wmono_refl rsegs m1) as WM2 end.
      assert (WZ2 : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                            [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
          by (eapply (henv_stores E Ac _ _ mdc _ _ PE0 AINV1 MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV1])
      end.
      eapply (KL (PST (x_p xc) S_NxtTag (fupd (fupd (fupd (x_v xc) Fremove rm) Fin_esi_tag 0) Fstate (stU S_NxtTag))
                      (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) Ac _ mdc).
      2:{ eapply (ainv_stores E Ac mc _ mdc _ _ PE0 AINVc MU WM WZ). }
      2:{ exact MDFc. }
      2:{ eapply hstep_trans; [exact HSc|].
          eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
          w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
      2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LT. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ.
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HDIT"] Lemma intag_do_include : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
        (s7 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      pinv E xc Ac mc -> ainv Ac mc mdc -> md_frame md mdc -> hstep E x xc A Ac m mc ->
      x_st xc = S_InTag -> x_p x < x_p xc -> x_v xc Flast_mark = 1 ->
      realizes rsegs (mkCfg (lms E vep_do_include_entry s7 (Z_to_bv 64 (x_p xc)) (Z_to_bv 64 0x1a9bc) t0 t1 t2
                               (Z_to_bv 64 (pe_VEP E)) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc AINVc MDFc HSc STc LT LM.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      (* [comment removed for export] *)
      pose proof (pinv_sizes _ _ _ _ PIc) as (OUT7 & WBB & LEN0 & SZ0).
      pose proof (pw_nlive_range (x_va xc) (x_vi xc)) as WNL.
      world_open PE PIc AINVc. unfold lms.
      assert (AV0 : x_v xc Fattr_vsb = 0).
      { destruct (Z.eq_dec (x_v xc Fattr_vsb) 0) as [X|X]; [exact X| exfalso; exact (AVSB X)]. }
      assert (EVA : x_va xc = None).
      { revert VA AV0. clear. destruct (x_va xc); [| reflexivity]. intros VA AV0. exfalso. exact (proj1 VA AV0). }
      assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
      unfold oibuf in D_IBV, D_IBS, D_IBB, D_IBD, D_IBW, D_II.
      eapply (HDIT (pe_VEP E) (x_v xc) (x_tag xc) (x_q xc) (x_vv xc) (x_vi xc) (pe_H E) (pe_lo E)
                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc mdc Ac T).
      1:{ exact AINVc. }
      1:{ exact MI. }
      1:{ reflexivity. }
      1:{ reflexivity. }
      1:{ split; [exact LVEP|]; split; [unfold vep_cells; rewrite STATE; exact VEPC|]; split; [exact TAG| exact PADS]. }
      1:{ exact BASE. }
      1:{ exact HENV. }
      1:{ exact HG. }
      1:{ exact IMG. }
      1:{ rewrite FLG; exact FL. }
      1:{ exact B_em. }
      1:{ exact B_ic. }
      1:{ exact LM. }
      1:{ exact AV0. }
      1:{ rewrite VSBF; exact VSBO. }
      1:{ rewrite VSBF; exact NE1. }
      1:{ exact D_VB. }
      1:{ exact ROOM. }
      1:{ revert OUT OA0 OI0 CNT VERP PLE NN DLEN; unfold oacost, oicost, vep_cnt; clear; destruct (x_vi xc); intros; lia. }
      1:{ (* [comment removed for export] *)
          revert LB BUDL WBB ROOM OUT7 OA0 OI0 LEN0 NN; unfold PARSE_LIVE, pe_N, oicost; clear; destruct (x_vi xc); intros; lia. }
      1:{ revert NL BUDN WNL; unfold PARSE_NLIVE; clear; intros; lia. }
      1:{ clear - VI D_IV D_IBV D_IS D_IBS D_IB D_IBB VSBF. rewrite ?VSBF.
          destruct (x_vi xc) as [yi|]; [| exact VI]. destruct VI as (Q1 & Q2 & Q3 & Q3b & Q4 & Q5).
          exact (conj Q1 (conj Q2 (conj Q3 (conj D_IV (conj D_IBV (conj D_IS (conj D_IB (conj D_IBS D_IBB)))))))). }
      1:{ reflexivity. }
      1:{ rewrite unsigned_lit by exact SPR; rewrite PSP, Zminus_mod, G1; reflexivity. }
      1:{ rewrite unsigned_lit by (clear; lia); reflexivity. }
      1:{ rewrite unsigned_lit by exact SPR; exact STK. }
      1:{ exact CEIL. }
      1:{ rewrite unsigned_lit by exact SPR; revert LOP PSP; clear; unfold_stacks_g; intros; lia. }
      1:{ rewrite unsigned_lit by exact SPR; rewrite PSP; clear; lia. }
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' v' vv' AINV1 MI1 MDF1 ST1 HENV1 VEPO1 VK VST IC1 IS1 VSBO1 LEN1 SZ1 REL LIVE1 CF1.
      rewrite unsigned_lit in ST1, CF1 by exact SPR.
      replace (ret_pc (Z_to_bv 64 0x1a9bc)) with (Z_to_bv 64 0x1a9bc) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof (as_lazy_nil _ _ _ AINV1) as [MDL1 MDH1].
      rewrite VSBF in VSBO1.
      (* [comment removed for export] *)
      set (v3 := fupd (fupd (fupd (x_v xc) Fstate (v' Fstate)) Finclude_src 0) Finclude_continue (v' Finclude_continue)).
      assert (EQF : forall f, v' f = v3 f).
      { intros f. subst v3. destruct f; cbn [fupd vf_beq vf_index N.eqb Pos.eqb];
          first [ reflexivity | exact IS1 | (apply VK; clear; cbv; intros [X|[X|[X|[]]]]; discriminate X) ]. }
      destruct VEPO1 as (LVEP1 & VEPC1 & _). cbn [al_segs LayoutPU] in VEPC1. clear VEPC.
      unfold vep_cells in VEPC1. rewrite !EQF in VEPC1. subst v3. psimp_in VEPC1.
      (* [comment removed for export] *)
      set (Vi := fun a : Z => blk (pe_VEP E) 312 a \/ blk (vb_buf (x_vv xc)) (vb_size (x_vv xc)) a \/ (x_v xc Fvsb <= a < x_v xc Fvsb + 40)
                           \/ match x_vi xc with Some yi => vsb_blocks (x_v xc Finclude_src) yi a | None => False end
                           \/ (h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320)) in CF1.
      assert (CV1 : vcover (pe_H E) Ac [pe_DATA E] Vi).
      { intros a [X|[X|[X|[X|X]]]].
        - eapply cover_blk; [exact LVEP| wz_not_in| exact X].
        - eapply cover_blk; [exact LVB| wz_not_in| exact X].
        - rewrite VSBF in X. eapply cover_rng; [exact LVS| wz_not_in| exact X].
        - clear - X VI D_ID D_IBD. destruct (x_vi xc) as [yi|]; [| destruct X].
          destruct VI as (_ & IO & _). pose proof IO as (_ & _ & LIS & LIB & _).
          destruct X as [X|X]; [eapply cover_blk; [exact LIS| wz_not_in| exact X] | eapply cover_blk; [exact LIB| wz_not_in| exact X]].
        - apply cover_vsc. exact X. }
      assert (WIN : alloc_ceiling <= pe_sp E - DOINCL_STACK) by (revert CEIL LOP PSP; clear; unfold_stacks_g; intros; lia).
      assert (WPOS : 0 <= DOINCL_STACK) by (clear; unfold_stacks_g; lia).
      (* [comment removed for export] *)
      assert (LK : forall p k, a_live Ac p = Some k -> p <> vb_buf (x_vv xc) ->
                   ~ (match x_vi xc with Some yi => p = x_v xc Finclude_src \/ p = vb_buf yi | None => False end) ->
                   a_live A' p = Some k).
      { intros p k Hp NB NI. clear - Hp NB NI LIVE1 REL.
        assert (NB' : p <> vb_buf vv') by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact Hp| exact NB]).
        destruct (x_vi xc) as [yi|].
        - destruct LIVE1 as (_ & _ & LQ & _). rewrite (LQ p NB NB'); [exact Hp| |]; intros ->; apply NI; [left| right]; reflexivity.
        - rewrite (proj1 LIVE1 p). exact Hp. }
      (* [comment removed for export] *)
      assert (SZQ : match x_vi xc with None => vb_size vv' = vb_size (x_vv xc) | Some _ => True end).
      { clear - LIVE1 REL VSBO1 LVB. destruct (x_vi xc) as [yi|]; [exact I|]. destruct LIVE1 as (LQ & _).
        pose proof (proj1 (proj2 (proj2 (proj2 VSBO1)))) as LVB1. rewrite LQ in LVB1.
        destruct REL as [EB|[F1 F2]]; [rewrite EB in LVB1; rewrite LVB in LVB1; injection LVB1; lia| rewrite F1 in LVB1; discriminate LVB1]. }
      assert (LDATA1 : a_live A' (pe_DATA E) = Some (Z.of_nat (length (pe_inp E)))).
      { apply LK; [exact LDATA| exact (not_eq_sym D_BD)|]. clear - D_ID D_IBD. destruct (x_vi xc); [| intros X; exact X].
        intros [X|X]; [exact (D_ID (eq_sym X))| exact (D_IBD (eq_sym X))]. }
      assert (WAL1 : a_live A' (pe_wa E) = Some 40).
      { apply LK; [exact WAL| exact D_WB|]. clear - D_IW D_IBW. destruct (x_vi xc); [| intros X; exact X].
        intros [X|X]; [exact (D_IW (eq_sym X))| exact (D_IBW (eq_sym X))]. }
      assert (NB_V : pe_VEP E <> vb_buf vv') by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LVEP| exact D_VB]).
      assert (NB_W : pe_wa E <> vb_buf vv') by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact WAL| exact D_WB]).
      assert (NB_D : pe_DATA E <> vb_buf vv') by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LDATA| exact (not_eq_sym D_BD)]).
      assert (NB_S : pe_S E <> vb_buf vv') by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LVS| exact D_SB]).
      (* [comment removed for export] *)
      assert (FR1 : rw_cells rsegs m' (pe_sp E) (pframe E j0 j8 j16 j24)).
      { eapply (pframe_call E Ac A' mc m' mdc (pe_sp E) DOINCL_STACK Vi _ [pe_DATA E]);
          [exact PE| exact AINVc| exact CF1| exact WIN| exact WPOS| clear; lia| exact CV1| unfold pframe; exact FR]. }
      assert (IMG1 : img_okU m').
      { eapply (img_call (pe_H E) Ac A' mc m' mdc (pe_sp E) DOINCL_STACK Vi _ [pe_DATA E] AINVc CF1 HG WIN); [exact CV1| exact IMG]. }
      assert (DATA1 : data_obj LayoutPU A' m' (pe_DATA E) (pe_inp E)).
      { eapply (data_obj_call (pe_H E) Ac A' mc m' mdc (pe_sp E) DOINCL_STACK Vi _ [pe_DATA E] AINVc CF1 HG WIN);
          [exact CV1| in_list| exact LDATA1| exact DATA]. }
      unfold pframe in FR1.
      (* [comment removed for export] *)
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m') as MU3. pose proof (wmono_refl rsegs m') as WM3.
      assert (WZ3 : wzone E A' [pe_S E; vb_buf vv'; pe_DATA E] [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      set (xI := PST (x_p xc) S_InTag (fupd (fupd (fupd (x_v xc) Fstate (v' Fstate)) Finclude_src 0) Finclude_continue (v' Finclude_continue))
                     (x_tag xc) (x_q xc) vv' None None).
      assert (HScall : hstep E xc xI Ac A' mc m').
      { eapply (hstep_intro E xc xI Ac A' mc m' PARSE_STACK Vi (blk (vb_buf vv') (vb_size vv'))).
        - eapply cframe_rebase; [exact CF1| clear; unfold_stacks_g; lia| eapply parse_window_mapped; [exact PE| exact ST1| unfold pframe; exact FR1]].
        - clear; lia.
        - eapply parse_window_mapped; [exact PE| exact ST1| unfold pframe; exact FR1].
        - intros a [X|[X|[X|[X|X]]]]; unfold pzone;
            [ left; exact X | right; right; left; exact X | right; left; rewrite VSBF in X; exact X
            | right; right; right; right; left; exact X | do 5 right; exact X ].
        - subst xI. unfold parse_new. cbn [x_v x_vv x_va x_vi option_map]. intros a [X|[X|X]]; [left; exact X| destruct X| destruct X].
        - intros p k Hp NB. apply LK; [exact Hp| |].
          + intros ->. apply NB. unfold pst_blocks. left. reflexivity.
          + clear - NB. intros X. apply NB. unfold pst_blocks. right. right. exact X.
        - subst xI. unfold pst_blocks. cbn [x_v x_vv x_va x_vi]. intros p [X|[X|X]]; [| destruct X| destruct X].
          destruct REL as [EB|[F1 F2]]; [left; left; rewrite X; exact EB| right; rewrite X; exact F1]. }
      apply rz_go; [exact MDH1| exact MDL1|].
      zstep. zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
          by (eapply (henv_stores E A' _ _ md' _ _ PE0 AINV1 MU3 WM3 WZ3); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV1])
      end.
      eapply (KL (PST (x_p xc) S_NxtTag
                      (fupd (fupd (fupd (fupd (fupd (x_v xc) Fstate (v' Fstate)) Finclude_src 0) Finclude_continue (v' Finclude_continue)) Fin_esi_tag 0) Fstate (stU S_NxtTag))
                      (x_tag xc) (x_q xc) vv' None None) A' _ md').
      2:{ eapply (ainv_stores E A' m' _ md' _ _ PE0 AINV1 MU3 WM3 WZ3). }
      2:{ eapply md_frame_trans; [exact MDFc| exact MDF1]. }
      2:{ eapply hstep_trans; [exact HSc|]. eapply hstep_trans; [exact HScall|].
          eapply hstep_stores; [exact MU3 | | eapply parse_window_mapped; [exact PE0| exact ST1| exact FR1]
                               | intros p0 X; refine (pst_blocks_same xI _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E xI _ a _ _ X); reflexivity ].
          subst xI. w_in_zone_tac. left. unfold blk. lia. }
      2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LT. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV1 MU3 WM3 WZ3.
      - (* [comment removed for export] *) clear - SZ1 LEN1 ROOM. lia.
      - (* [comment removed for export] *) clear - OUT LEN1 EVA. unfold oacost, oicost in *. rewrite EVA in OUT. cbn [x_va x_vi x_st x_p x_vv x_v] in *.
        destruct (x_vi xc); lia.
      - (* [comment removed for export] *) intros y Hy. split; [apply (proj1 (APART y Hy))|].
        cbn in Hy. destruct Hy as [<-|[<-|[<-|[]]]]; apply not_eq_sym; [exact NB_V| exact NB_W| exact NB_D].
      - (* [comment removed for export] *) revert LB LIVE1 SZQ. rewrite EVA. clear. unfold pw_bytes. destruct (x_vi xc); intros; lia.
      - (* [comment removed for export] *) revert NL LIVE1. rewrite EVA. clear. unfold pw_nlive. destruct (x_vi xc); intros; lia.
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HDIT HDR HDC HMC"] Lemma intag_gt : forall (xc : pst) (mc : mem)
        (s7 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc ->
      x_st xc = S_InTag -> x_p x < x_p xc ->
      realizes rsegs (mkCfg (lms E 0x1a990 s7 (Z_to_bv 64 (x_p xc)) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mc) md) T.
    Proof.
      intros until t6. intros PIc AINVc HSc STc LT.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold lms.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (mark_call HMC E xc A mc md T (x_p xc) 1 0x1a9a0);
        [ exact PE | exact PIc0 | exact AINVc | clear; lia | exact PLE | right; reflexivity | clear; lia | reflexivity
        | rewrite STc; intros [X|X]; discriminate X | ].
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (HS2 : hstep E x x1 A A1 m m2) by (eapply hstep_trans; [exact HSc| exact HS]).
      assert (ST1 : x_st x1 = S_InTag) by (rewrite EX1; exact STc).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
      clear - HMC HVE HDC HDR HDIT PE PHI KL PI1 AINV' MDF HS2 VK LM1 ST1 EV1 EP1 LT.
      rewrite <- EP1 in LT. rewrite <- EV1 in LM1.
      pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
      world_open PE PI1 AINV'. unfold lms. rewrite <- EP1.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH'| exact MDL'|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      set (x2 := PST (x_p x1) S_InTag (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1))
                     (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        pose proof (ainv_stores E A1 m2 mf md1 _ _ PE0 AINV' MU WM WZ) as AINV2;
        assert (PI2 : pinv E x2 A1 mf); [| assert (HS3 : hstep E x x2 A A1 m mf)] end.
      { subst x2. apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ. }
      { eapply hstep_trans; [exact HS2|].
        eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
      (* [comment removed for export] *)
      destruct DOST as [D0|[DI|[DR|DC]]]; [exfalso; exact (ARMED I D0)| | |].
      - rewrite DI. cbn [vi_do_include VIU]. zstep. apply rz_stop.
        eapply (intag_do_include x2 A1 _ md1); [exact PI2| exact AINV2| exact MDF| exact HS3| reflexivity| exact LT| subst x2; psimp; exact LM1].
      - rewrite DR. cbn [vi_do_remove VIU]. zstep. apply rz_stop.
        eapply (intag_do_remove x2 A1 _ md1); [exact PI2| exact AINV2| exact MDF| exact HS3| reflexivity| exact LT].
      - rewrite DC. cbn [vi_do_comment VIU]. zstep. apply rz_stop.
        eapply (intag_do_comment x2 A1 _ md1); [exact PI2| exact AINV2| exact MDF| exact HS3| reflexivity| exact LT].
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HVE"] Lemma intag_err : forall (site : Z) (xc : pst) (mc : mem)
        (s7 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      (site = 0x1a9d0 \/ site = 0x1aab0) ->
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc ->
      x_st xc = S_InTag -> x_p x <= x_p xc -> x_p xc < pe_e E ->
      realizes rsegs (mkCfg (lms E site s7 (Z_to_bv 64 (x_p xc)) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mc) md) T.
    Proof.
      intros until t6. intros SITE PIc AINVc HSc STc LQ QE.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      world_open PE PIc AINVc. unfold lms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] mc) as MU.
      pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E A [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
      assert (EVS : VEPERR_STACK = 48) by reflexivity.
      assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
      apply rz_go; [exact MDH| exact MDL|].
      destruct SITE as [-> | ->].
      -   (* [comment removed for export] *)
          zstep. zstep. zstep. zstep.
          hide STK. hide_slow.
          call_fr (HVE (pe_VEP E) (x_v xc) (x_tag xc) (x_q xc) (pe_H E) (pe_lo E)) by idtac.
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
          rename PC into HENV1. rename POST into STK.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            pose proof (ainv_stores E A mc m1 md _ _ PE0 AINVc MU WM WZ) as AINV1;
            pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m1) as MU2; pose proof (wmono_refl rsegs m1) as WM2 end.
          assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                                [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
          (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. zstep.
          apply rz_stop.
          match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
            assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
              by (eapply (henv_stores E A _ _ md _ _ PE0 AINV1 MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV1])
          end.
          eapply (KL (PST (x_p xc) S_TagError (fupd (x_v xc) Fstate (stU S_TagError)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) A _ md).
          2:{ eapply (ainv_stores E A mc _ md _ _ PE0 AINVc MU WM WZ). }
          2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
          2:{ eapply hstep_trans; [exact HSc|].
              eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                                   | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                                   | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
              w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
          2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LQ. lia. }
          apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ.
      -   (* [comment removed for export] *)
          zstep. zstep. zstep. zstep.
          hide STK. hide_slow.
          call_fr (HVE (pe_VEP E) (x_v xc) (x_tag xc) (x_q xc) (pe_H E) (pe_lo E)) by idtac.
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
          rename PC into HENV1. rename POST into STK.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            pose proof (ainv_stores E A mc m1 md _ _ PE0 AINVc MU WM WZ) as AINV1;
            pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m1) as MU2; pose proof (wmono_refl rsegs m1) as WM2 end.
          assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                                [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
          (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. zstep.
          apply rz_stop.
          match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
            assert (HENV2 : henv_ok LayoutPU VIU (pe_H E) mf)
              by (eapply (henv_stores E A _ _ md _ _ PE0 AINV1 MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV1])
          end.
          eapply (KL (PST (x_p xc) S_TagError (fupd (x_v xc) Fstate (stU S_TagError)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) A _ md).
          2:{ eapply (ainv_stores E A mc _ md _ _ PE0 AINVc MU WM WZ). }
          2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
          2:{ eapply hstep_trans; [exact HSc|].
              eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                                   | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                                   | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
              w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
          2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LQ. lia. }
          apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ.
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HDIT HDR HDC HVE HMC"] Lemma intag_exit2 : forall (xc : pst) (mc : mem)
        (s7 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc ->
      x_st xc = S_InTag -> x_p x <= x_p xc -> x_p xc < pe_e E ->
      realizes rsegs (mkCfg (lms E 0x1a970 s7 (Z_to_bv 64 (x_p xc)) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mc) md) T.
    Proof.
      intros until t6. intros PIc AINVc HSc STc LQ QE.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold lms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU. pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E A [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      (* [comment removed for export] *)
      assert (DSR : 0 <= x_v xc Fdostuff < 2^64 /\ x_v xc Fdostuff <> 0).
      { split; [| exact (ARMED I)]. clear - DOST. destruct DOST as [-> |[-> |[-> | ->]]]; cbn; lia. }
      destruct DSR as [DSR DNZ].
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT VERP Dlo. lia. } clear KT.
      (* [comment removed for export] *)
      destruct (look_read rsegs E xc mc DBY ltac:(clear - VERP; lia) QE) as (b & Hnth & Hlook & RDP).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      2:{ (* [comment removed for export] *)
          zstep. zstep. if_cases KT; zify_cond KT.
          { exfalso. revert KT QE Dhi CV. clear. unfold pe_e, pe_N. intros. lia. }
          clear KT.
          zstep. zstep. if_cases K2; zify_cond K2. { exfalso. exact (DNZ K2). } clear K2.
          zstep. apply rz_stop.
          set (xg := PST (x_p xc + 1) S_InTag (x_v xc) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)).
          assert (PIg : pinv E xg A mc); [| assert (HSg : hstep E x xg A A m mc)].
          { subst xg. apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ.
            - (* [comment removed for export] *) clear - VERP. lia.
            - (* [comment removed for export] *) clear - QE. lia. }
          { eapply hstep_trans; [exact HSc|].
            eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                                 | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
            w_in_zone_tac. left. unfold blk. lia. }
          eapply (intag_gt xg mc); [exact PIg| exact AINVc| exact HSg| reflexivity| subst xg; cbn [x_p]; clear - LQ; lia]. }
      (* [comment removed for export] *)
      zstep. pose proof B_em as EM; destruct EM as [EM|EM]; rewrite EM, ?sx32_zero, ?sx32_one.
      2:{ (* [comment removed for export] *)
          zstep. if_cases K2; zify_cond K2. { exfalso. clear - K2. lia. } clear K2.
          apply rz_stop. eapply (intag_err 0x1a9d0 xc mc); [left; reflexivity| exact PIc0| exact AINVc| exact HSc| exact STc| exact LQ| exact QE]. }
      zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. } clear K2.
      (* [comment removed for export] *)
      zstep. pose proof B_ca as CA; destruct CA as [CA|CA]; rewrite CA, ?sx32_zero, ?sx32_one.
      { (* [comment removed for export] *)
        zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear - K3. lia. } clear K3.
        apply rz_stop. eapply (intag_err 0x1aab0 xc mc); [right; reflexivity| exact PIc0| exact AINVc| exact HSc| exact STc| exact LQ| exact QE]. }
      zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3. lia. } clear K3.
      (* [comment removed for export] *)
      zstep.
      replace (Z.shiftl (bv_unsigned b) 1) with (2 * bv_unsigned b) by (rewrite Z.shiftl_mul_pow2; clear; lia).
      assert (VCR1 : 0 <= VCT_ADDR < 2^64) by (unfold VCT_ADDR; clear; lia).
      zstep. zstep. if_cases KT; zify_cond KT.
      { exfalso. revert KT BR. clear. intros. rewrite zb_lxor_ones in KT by (unfold VCT_ADDR; lia). unfold VCT_ADDR in KT.
        first [rewrite !Z.mod_small in KT by lia | idtac]. lia. }
      clear KT VCR1. zstep.
      pose proof (vct_readU mc (bv_unsigned b) _ MI BR eq_refl) as RDV. unfold wa in RDV.
      zstep. clear RDV. cbv beta. rewrite zx16_vct.
      pose proof (vct_range (bv_unsigned b)) as VR.
      zstep. zstep. if_cases K4; zify_cond K4.
      2:{ (* [comment removed for export] *)
          apply rz_stop. eapply (intag_err 0x1aab0 xc mc); [right; reflexivity| exact PIc0| exact AINVc| exact HSc| exact STc| exact LQ| exact QE]. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (KL (PST (x_p xc) S_Attr (fupd (x_v xc) Fstate (stU S_Attr)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) A _ md).
      2:{ eapply (ainv_stores E A mc _ md _ _ PE0 AINVc MU WM WZ). }
      2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
      2:{ eapply hstep_trans; [exact HSc|].
          eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LQ. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ.
      - (* [comment removed for export] *)
        intros _ _ _. unfold look. cbn [x_p]. rewrite Hnth. unfold vct_namestart. apply Bool.negb_true_iff. apply Z.eqb_neq. exact K4.
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HDIT HDR HDC HVE HMC"] Lemma intag_exit2s : forall (xc : pst) (mc : mem)
        (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word),
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc ->
      x_st xc = S_InTag -> x_p x <= x_p xc ->
      realizes rsegs (mkCfg (loop_ms E 0x1a968 (x_p xc) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 mc) md) T.
    Proof.
      intros until t6. intros PIc AINVc HSc STc LQ.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms, lms.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. zstep. if_cases K0; zify_cond K0.
      { (* [comment removed for export] *)
        apply rz_stop.
        eapply (KL xc A mc md); [exact PIc0| exact AINVc| apply md_frame_refl; [exact MDL| exact MDH]| exact HSc|].
        intros H. exfalso. clear - H K0. unfold pe_e, pe_N in *. lia. }
      apply rz_stop. eapply (intag_exit2 xc mc); [exact PIc0| exact AINVc| exact HSc| exact STc| exact LQ| clear - K0; unfold pe_e, pe_N in *; lia].
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HDIT HDR HDC HVE HMC"] Lemma intag_exit1 : forall (xc : pst) (mc : mem) (b : byte)
        (ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word),
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc ->
      x_st xc = S_InTag -> x_p x <= x_p xc -> x_p xc < pe_e E ->
      nth_error (pe_inp E) (Z.to_nat (x_p xc - pe_DATA E)) = Some b ->
      realizes rsegs (mkCfg (loop_ms E 0x1a958 (x_p xc) ra t0 t1 t2 a0 (Z_to_bv 64 (bv_unsigned b)) a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 mc) md) T.
    Proof.
      intros until t6. intros PIc AINVc HSc STc LQ QE Hnth.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms, lms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU. pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E A [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1.
      { apply rz_stop. eapply (intag_exit2s xc mc); [exact PIc0| exact AINVc| exact HSc| exact STc| exact LQ]. }
      (* [comment removed for export] *)
      zstep. pose proof B_em as EM; destruct EM as [EM|EM]; rewrite EM, ?sx32_zero, ?sx32_one.
      2:{ (* [comment removed for export] *)
          zstep. if_cases K2; zify_cond K2. { exfalso. clear - K2. lia. }
          apply rz_stop. eapply (intag_exit2s xc mc); [exact PIc0| exact AINVc| exact HSc| exact STc| exact LQ]. }
      zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. } clear K2.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KT; zify_cond KT.
      { exfalso. revert KT QE Dhi CV. clear. unfold pe_e, pe_N. intros. lia. }
      clear KT.
      zstep. zstep. zstep. zstep.
      set (xe := PST (x_p xc + 1) S_InTag (fupd (fupd (x_v xc) Femptytag 1) Fcanattr 0) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        pose proof (ainv_stores E A mc mf md _ _ PE0 AINVc MU WM WZ) as AINVe;
        assert (PIe : pinv E xe A mf); [| assert (HSe : hstep E x xe A A m mf)] end.
      { subst xe. apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ.
        - (* [comment removed for export] *) clear - VERP. lia.
        - (* [comment removed for export] *) clear - QE. lia. }
      { eapply hstep_trans; [exact HSc|].
        eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
      (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3.
      { (* [comment removed for export] *)
        apply rz_stop.
        eapply (KL xe A _ md); [exact PIe| exact AINVe| apply md_frame_refl; [exact MDL| exact MDH]| exact HSe|].
        subst xe. cbn [x_p]. intros H. exfalso. clear - H K3. unfold pe_e, pe_N in *. lia. }
      zstep. apply rz_stop.
      eapply (intag_exit2 xe _); [exact PIe| exact AINVe| exact HSe| reflexivity| subst xe; cbn [x_p]; clear - LQ; lia
                                 | subst xe; cbn [x_p]; clear - K3; unfold pe_e, pe_N in *; lia].
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HDIT HDR HDC HVE HMC"] Lemma intag_loop : forall (k : nat) (xc : pst) (mc : mem)
        (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word),
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc ->
      x_st xc = S_InTag -> x_p x <= x_p xc -> x_p xc + Z.of_nat k = pe_e E -> x_p xc < pe_e E ->
      evt rsegs (rz_at rsegs md T)
          (loop_ms E 0x1a818 (x_p xc) ra t0 t1 t2 (Z_to_bv 64 (pe_e E - x_p xc)) a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 mc).
    Proof.
      induction k as [|k IH]; intros until t6; intros PIc AINVc HSc STc LQ Hk QE.
      { exfalso. clear - Hk QE. lia. }
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms, lms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU. pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E A [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      (* [comment removed for export] *)
      zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT VERP Dlo. lia. } clear KT.
      (* [comment removed for export] *)
      destruct (look_read rsegs E xc mc DBY ltac:(clear - VERP; lia) QE) as (b & Hnth & Hlook & RDP).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta.
      (* [comment removed for export] *)
      zstep. zstep.
      replace (Z.shiftl (bv_unsigned b) 1) with (2 * bv_unsigned b) by (rewrite Z.shiftl_mul_pow2; clear; lia).
      pose proof (vct_readU mc (bv_unsigned b) _ MI BR eq_refl) as RDV. unfold wa in RDV.
      zstep. clear RDV. cbv beta. rewrite zx16_vct.
      pose proof (vct_range (bv_unsigned b)) as VR.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1.
      { apply rz_stop. eapply (intag_exit1 xc mc b); [exact PIc0| exact AINVc| exact HSc| exact STc| exact LQ| exact QE| exact Hnth]. }
      (* [comment removed for export] *)
      zstep. pose proof B_em as EM; destruct EM as [EM|EM]; rewrite EM, ?sx32_zero, ?sx32_one.
      2:{ zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. }
          apply rz_stop. eapply (intag_exit2s xc mc); [exact PIc0| exact AINVc| exact HSc| exact STc| exact LQ]. }
      zstep. if_cases K2; zify_cond K2. { exfalso. clear - K2. lia. } clear K2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        pose proof (ainv_stores E A mc mf md _ _ PE0 AINVc MU WM WZ) as AINVl;
        assert (CKl : forall q, x_p xc + 1 <= q -> q <= pe_e E ->
          pinv E (PST q S_InTag (fupd (x_v xc) Fcanattr 1) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) A mf
          /\ hstep E x (PST q S_InTag (fupd (x_v xc) Fcanattr 1) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) A A m mf) end.
      { intros q LQ' QE'. split.
        - apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ.
          + (* [comment removed for export] *) clear - VERP LQ'. lia.
          + (* [comment removed for export] *) revert OUT LQ'. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
        - eapply hstep_trans; [exact HSc|].
          eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3.
      - (* [comment removed for export] *)
        destruct (CKl (x_p xc + 1) ltac:(clear; lia) ltac:(clear - K3 Hk QE; lia)) as [PIl HSl].
        replace (pe_e E - x_p xc + -1) with (pe_e E - (x_p xc + 1)) by (clear; lia).
        eapply (IH (PST (x_p xc + 1) S_InTag (fupd (x_v xc) Fcanattr 1) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)));
          [exact PIl| exact AINVl| exact HSl| reflexivity| cbn [x_p]; clear - LQ; lia| cbn [x_p]; clear - Hk; lia| cbn [x_p]; clear - K3 Hk QE; lia].
      - (* [comment removed for export] *)
        zstep. zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear - K4. lia. }
        apply rz_stop.
        destruct (CKl (pe_e E) ltac:(clear - QE; lia) ltac:(clear; lia)) as [PIl HSl].
        eapply (KL (PST (pe_e E) S_InTag (fupd (x_v xc) Fcanattr 1) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) A _ md);
          [exact PIl| exact AINVl| apply md_frame_refl; [exact MDL| exact MDH]| exact HSl|].
        cbn [x_p]. intros H. exfalso. clear - H. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HDIT HDR HDC HVE HMC"] Lemma intag_body : forall (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word),
      pinv E x A m -> ainv A m md -> x_st x = S_InTag -> x_p x < pe_e E ->
      realizes rsegs (mkCfg (disp_ms E x ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 m) md) T.
    Proof.
      intros until t6. intros PI AINV ST PLT.
      handler_prologue PE PI AINV ST.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
      assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep.
      set (x0 := PST (x_p x) S_InTag (fupd (x_v x) Ftag_i 0) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        pose proof (ainv_stores E A m mf md _ _ PE0 AINV MU WM WZ) as AINV0;
        assert (PIx : pinv E x0 A mf); [| assert (HSx : hstep E x x0 A A m mf)] end.
      { subst x0. apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ. clear. lia. }
      { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0 PLT. unfold pe_e, pe_N in *. lia. } clear K0.
      zstep.
      eapply (intag_loop (Z.to_nat (pe_e E - x_p x)) x0);
        [exact PIx| exact AINV0| exact HSx| reflexivity| subst x0; cbn [x_p]; clear; lia
        | subst x0; cbn [x_p]; clear - PLT; rewrite Z2Nat.id by lia; lia| exact PLT].
    Qed.
  End X.

  #[using="HDIT HDR HDC HVE HMC"] Lemma PH_InTag : handler_stmt S_InTag.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    apply (intag_body E x A m md T PE); [unfold phi, rank; rewrite ST; reflexivity| exact KL| exact PI| exact AINV| exact ST| exact PLT].
  Qed.
End S.

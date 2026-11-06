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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit V_PMark V_Pa4g6 V_PH51p Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Pa4g6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.

Module V_PH1oh.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit V_PMark V_Pa4g6 V_PH51p Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Pa4g6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
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
  Context {AI : AllocSpec LayoutP0}.
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
    assert (TAIL : forall (xc : pst) (mc : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc ->
      (x_st xc = S_NotMyTag \/ x_st xc = S_NxtTag) -> (x_p xc < pe_e E -> phi E xc < phi E x) ->
      realizes rsegs (mkCfg (loop_ms E 0x1a308 (x_p xc) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) md) T).
    { intros until t6'. intros PIc AINVc HSc STc PHIc.
      clear - HMC PE KL PIc AINVc HSc STc PHIc MDL MDH.
      assert (NMB : x_st xc <> S_MatchBuf) by (destruct STc as [X|X]; rewrite X; discriminate).
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0.
      { (* [comment removed for export] *)
        apply rz_stop.
        eapply (KL xc A mc md); [exact PIc0| exact AINVc| apply md_frame_refl; [exact MDL| exact MDH]| exact HSc|].
        intros H. split; [exact (PHIc H)| exact NMB]. }
      (* [comment removed for export] *)
      zstep. destruct B_rm as [RM|RM]; rewrite RM, ?sx32_zero, ?sx32_one.
      2:{ (* [comment removed for export] *)
          zstep. if_cases K1; zify_cond K1. 2:{ dead K1. } clear K1.
          apply rz_stop.
          eapply (KL xc A mc md); [exact PIc0| exact AINVc| apply md_frame_refl; [exact MDL| exact MDH]| exact HSc|].
          intros H. exfalso. clear - H K0. unfold pe_e, pe_N in *. lia. }
      zstep. if_cases K1; zify_cond K1. { dead K1. } clear K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (mark_call HMC E xc A mc md T (x_p xc) (x_p xc) 0 0x1a324);
        [ exact PE | exact PIc0 | exact AINVc | clear; lia | exact PLE | left; reflexivity | clear; lia | reflexivity
        | intros [X|X]; destruct STc as [Y|Y]; rewrite Y in X; discriminate X | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (HS2 : hstep E x x1 A A1 m m2) by (eapply hstep_trans; [exact HSc| exact HS]).
      assert (ST1 : x_st x1 = x_st xc) by (rewrite EX1; reflexivity).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
      assert (EPc : x_p x1 = pe_e E) by (rewrite EP1; exact K0).
      clear - HMC PE KL PI1 AINV' MDF HS2 VK VERP1 LM1 OP1 ST1 EV1 EP1 EPc.
      pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
      world_open PE PI1 AINV'. rewrite <- EP1.
      unfold loop_ms.
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
      all: rewrite ?ST1; try assumption.
      exact (conj DELIM1 DELIM2). }
    (* [comment removed for export] *)
    pose proof (rw_cells_read_sub rsegs _ _ _ 4 1 VEPC ltac:(clear; lia) ltac:(cbn; clear; lia)) as RDF.
    match type of RDF with _ = Some ?r => change r with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x Fflags)))] in RDF end.
    remember (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x Fflags)))) as fb eqn:Efb in RDF.
    apply rz_go; [exact MDH| exact MDL|].
    set (RWv := rw_cells rsegs m (pe_VEP E)) in VEPC.
    zstep. subst RWv. clear RDF. cbv beta. zstep. zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      apply rz_stop.
      set (xa := PST (x_p x + 1) S_NxtTag (fupd (x_v x) Fstate (st0 S_NxtTag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        pose proof (ainv_stores E A m mf md _ _ PE0 AINV MU WM WZ) as AINVa;
        assert (PIa : pinv E xa A mf); [| assert (HSa : hstep E x xa A A m mf)] end.
      { subst xa. apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
        + (* [comment removed for export] *) clear - VERP. lia.
        + (* [comment removed for export] *) clear - PLT. unfold pe_e, pe_N in *. lia. }
      { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
      eapply (TAIL xa); [exact PIa| exact AINVa| exact HSa| right; reflexivity|].
      subst xa. intros _. rewrite PHI. unfold phi, rank; psimp. clear. lia.
    - (* [comment removed for export] *)
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      (* [comment removed for export] *)
      assert (CK : forall q, x_p x <= q -> q <= pe_e E ->
        pinv E (PST q S_NotMyTag (fupd (x_v x) Ftag_i 0) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A mc
        /\ hstep E x (PST q S_NotMyTag (fupd (x_v x) Ftag_i 0) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A A m mc);
      [| assert (EXIT : forall (q : Z) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
             x_p x <= q -> q = pe_e E ->
             realizes rsegs (mkCfg (loop_ms E 0x1a308 q ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) md) T);
         [| assert (LOOP : forall (k : nat) (q : Z) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
                q + Z.of_nat k = pe_e E -> x_p x <= q -> q <= pe_e E ->
                evt rsegs (rz_at rsegs md T)
                    (loop_ms E 0x1a22c q ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc)) ]]
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
        intros until t6'. intros LQ QE.
        destruct (CK q LQ ltac:(clear - QE; lia)) as [PIc HSc].
        eapply (TAIL (PST q S_NotMyTag (fupd (x_v x) Ftag_i 0) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)));
          [exact PIc| eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ)| exact HSc| left; reflexivity|].
        cbn [x_p]. intros H. exfalso. clear - H QE. lia. }
      { (* [comment removed for export] *)
        induction k as [|k IH]; intros until t6'; intros Hk LQ QE; unfold loop_ms.
        - (* [comment removed for export] *)
          zstep. if_cases Kb; zify_cond Kb. 2:{ dead Kb. }
          apply rz_stop. eapply EXIT; [exact LQ| clear - Hk; lia].
        - zstep. if_cases Kb; zify_cond Kb. { dead Kb. } clear Kb.
          (* [comment removed for export] *)
          destruct (payload_read rsegs E _ q DBY ltac:(clear - LQ VERP; lia) ltac:(clear - Hk; unfold pe_e, pe_N in *; lia)) as (b & Hnth & RDP).
          pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
          zstep. clear RDP. cbv beta.
          zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
          + (* [comment removed for export] *)
            eapply (IH (q + 1)); [clear - Hk; lia| clear - LQ; lia| clear - Hk; lia].
          + (* [comment removed for export] *)
            zstep. zstep. zstep.
            apply rz_stop.
            set (xg := PST (q + 1) S_NxtTag (fupd (fupd (x_v x) Ftag_i 0) Fstate (st0 S_NxtTag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
            match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
              pose proof (ainv_stores E A m mf md _ _ PE0 AINV MU WM WZ) as AINVg;
              assert (PIg : pinv E xg A mf); [| assert (HSg : hstep E x xg A A m mf)] end.
            { subst xg. apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
              * (* [comment removed for export] *) clear - VERP LQ. lia.
              * (* [comment removed for export] *) clear - Hk. lia.
              * (* [comment removed for export] *) clear. lia.
              * (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia. }
            { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                                   | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                                   | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
              w_in_zone_tac. left. unfold blk. lia. }
            eapply (TAIL xg); [exact PIg| exact AINVg| exact HSg| right; reflexivity|].
            subst xg. intros _. rewrite PHI. unfold phi, rank; psimp. clear - LQ. lia. }
      eapply (LOOP (Z.to_nat (pe_e E - x_p x)) (x_p x)); [clear - PLT; rewrite Z2Nat.id by lia; lia| clear; lia| clear - PLT; lia].
  Qed.
End S.
End V_PH1oh.

Module V_PH88s.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c V_Paq9r V_PKit Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
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
  Context {AI : AllocSpec LayoutP0}.

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
      realizes rsegs (mkCfg (loop_ms E 0x1a1b0 (x_p x) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' m) md) T).
    { intros. unfold loop_ms. apply rz_go; [exact MDH| exact MDL|].
      zstep. zstep.
      apply rz_stop.
      eapply (KL (PST (x_p x) S_BOM (fupd (x_v x) Fstate (st0 S_BOM)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
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
    destruct (look_read rsegs E x m DBY ltac:(clear - VERP; lia) PLT) as (b & Hnth & Hlook & RDP).
    pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
    zstep. clear RDP. cbv beta. zstep. zstep. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *) apply rz_stop. apply GOBOM. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    eapply (KL (PST (x_p x) S_Match (fupd (fupd (x_v x) Fmatch TBL_bom) Fstate (st0 S_Match))
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
End V_PH88s.

Module V_PH9xg.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit V_PH51p Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
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
  Context {AI : AllocSpec LayoutP0}.
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
      rw_cells rsegs mc (pe_sp E) (pframe E j0 j8) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) ->
      henv_ok LayoutP0 VI0 (pe_H E) mc -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      realizes rsegs (mkCfg (loop_ms E 0x1a434 (x_p x) ra' t0' t1' t2' (Z_to_bv 64 (st0 S_TagError)) a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) md) T).
    { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc HENVc STKc. unfold loop_ms.
      clear VEPC FR DBY STK HENV MI.
      unfold vep_cells in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
      pose proof (ainv_stores E A m mc md _ _ PE0 AINV MUc WMc WZ) as AINVc.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU2. pose proof (wmono_refl rsegs mc) as WM2.
      assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                            [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH| exact MDL|].
      zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
          by (eapply (henv_stores E A _ _ md _ _ PE0 AINVc MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENVc])
      end.
      eapply (KL (PST (x_p x) S_TagError (fupd (x_v x) Fstate (st0 S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
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
      (ret = 0x1a5c8 \/ ret = 0x1a674) ->
      realizes rsegs (mkCfg (loop_ms E vep_error_entry (x_p x) (Z_to_bv 64 ret) t0' t1' t2' (Z_to_bv 64 (pe_VEP E)) a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' m) md) T).
    { intros until t6'. intros RET. unfold loop_ms, vep_error_entry.
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
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
      assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
        by (eapply (henv_stores E A _ _ md _ _ PE0 AINV MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENV])
    end.
    eapply (KL (PST (x_p x) S_InTag (fupd (fupd (x_v x) Fdostuff (vi_do_comment VI0)) Fstate (st0 S_InTag))
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
End V_PH9xg.

Module V_PHayj.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c V_Paq9r V_PKit Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  Lemma PH_end_ESITag : handler_stmt S_end_ESITag.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    apply rz_go; [exact MDH| exact MDL|].
    zstep. zstep. zstep. zstep.
    apply rz_stop.
    eapply (KL (PST (x_p x) S_ESITag (fupd (fupd (x_v x) Fstate (st0 S_ESITag)) Fendtag 1)
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
End V_PHayj.

Module V_PHbir.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
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
  Context {AI : AllocSpec LayoutP0}.
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
    zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    (* [comment removed for export] *)
    match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
      assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
        by (eapply (henv_stores E A _ _ md _ _ PE0 AINV1 MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENV1])
    end.
    eapply (KL (PST (x_p x) S_TagError (fupd (x_v x) Fstate (st0 S_TagError))
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
End V_PHbir.

Module V_PHc39.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c V_Paq9r V_PKit V_PMark V_Pa4g6 Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
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
  Context {AI : AllocSpec LayoutP0}.
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_ESITag : handler_stmt S_ESITag.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    (* [comment removed for export] *)
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    apply rz_go; [exact MDH| exact MDL|].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    (* [comment removed for export] *)
    set (xc := PST (x_p x) S_ESITag (fupd (fupd (x_v x) Fin_esi_tag 1) Fesi_found 1) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
    assert (PIc : pinv E xc A m1).
    { subst xc. apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ. }
    pose proof (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ) as AINVc.
    assert (HS1 : hstep E x xc A A m m1).
    { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                           | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                           | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
      w_in_zone_tac. left. unfold blk. lia. }
    (* [comment removed for export] *)
    eapply (mark_call HMC E xc A m1 md T (x_p x) (x_p x) 1 0x1a528);
      [ exact PE | exact PIc | exact AINVc | subst xc; cbn [x_p]; lia | exact PLE | right; reflexivity | lia | reflexivity
      | subst xc; cbn [x_st]; intros [X|X]; discriminate X | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1.
    (* [comment removed for export] *)
    assert (HS2 : hstep E x x1 A A1 m m2) by (eapply hstep_trans; [exact HS1| exact HS]).
    assert (ST1 : x_st x1 = S_ESITag) by (rewrite EX1; reflexivity).
    assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
    assert (EP1 : x_p x1 = x_p x) by (rewrite EX1; reflexivity).
    assert (EQ1 : x_tag x1 = x_tag x /\ x_q x1 = x_q x /\ x_va x1 = x_va x /\ x_vi x1 = x_vi x) by (rewrite EX1; subst xc; repeat split; reflexivity).
    clear - HMC PE ST PLT KL KX PI1 AINV' MDF HS2 VK VERP1 LM1 OP1 ST1 EV1 EP1 EQ1.
    pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
    world_open PE PI1 AINV'. rewrite <- EP1.
    (* [comment removed for export] *)
    unfold loop_ms.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
    assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    apply rz_go; [exact MDH'| exact MDL'|].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    (* [comment removed for export] *)
    eapply (KL (PST (x_p x1) S_Match
                    (fupd (fupd (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) Fmatch TBL_esi) Fstate (st0 S_Match))
                    (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ md1).
    2:{ eapply (ainv_stores E A1 m2 _ md1 _ _ PE0 AINV' MU WM WZ). }
    2:{ exact MDF. }
    2:{ eapply hstep_trans; [exact HS2|].
        eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
    2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST, EP1.
        unfold TBL_bom, TBL_starttag, TBL_esi, TBL_attr_include. cbn [Z.eqb Pos.eqb]. lia. }
    apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ.
  Qed.
End S.
End V_PHc39.

Module V_PHgbh.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit V_PH51p Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
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
  Context {AI : AllocSpec LayoutP0}.
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
      realizes rsegs (mkCfg (loop_ms E 0x1a854 (x_p x) ra' t0' t1' t2' (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' m) md) T).
    { intros until t6'. intros HD. unfold loop_ms.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
          by (eapply (henv_stores E A _ _ md _ _ PE0 AINV MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENV])
      end.
      eapply (KL (PST (x_p x + 1) S_AttrValue (fupd (fupd (x_v x) Fattr_delim d) Fstate (st0 S_AttrValue))
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
    zstep. zstep.
    replace (Z.shiftl (bv_unsigned b) 1) with (2 * bv_unsigned b) by (rewrite Z.shiftl_mul_pow2; clear; lia).
    pose proof (vct_read0 m (bv_unsigned b) _ MI BR eq_refl) as RDV. unfold wa in RDV.
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
        assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
          by (eapply (henv_stores E A _ _ md _ _ PE0 AINVc MU3 WM3 WZ3); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENVc])
      end.
      eapply (KL (PST (x_p x) S_TagError (fupd (x_v x) Fstate (st0 S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
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
    clear K4. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
      assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
        by (eapply (henv_stores E A _ _ md _ _ PE0 AINV MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENV])
    end.
    eapply (KL (PST (x_p x) S_AttrValue (fupd (fupd (x_v x) Fattr_delim 32) Fstate (st0 S_AttrValue))
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
End V_PHgbh.

Module V_PHham.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c V_Paq9r V_PKit Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
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
  Context {AI : AllocSpec LayoutP0}.

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
                    (fupd (fupd (fupd (fupd (x_v x) Funtil LIT_cdata_end) Funtil_p LIT_cdata_end) Funtil_s (st0 S_NxtTag)) Fstate (st0 S_Until))
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
End V_PHham.

Module V_PHlrw.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit V_PMark V_Pa4g6 V_PH51p Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Pa4g6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
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
  Context {AI : AllocSpec LayoutP0}.
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
    eapply (mark_call HMC E x A m md T (x_p x) (pe_e E) 0 0x1ab18);
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
    unfold loop_ms.
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
End V_PHlrw.

Module V_PHo3d.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit V_PH51p Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
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
  Context {AI : AllocSpec LayoutP0}.
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
      rw_cells rsegs mc (pe_sp E) (pframe E (Z_to_bv 64 (st0 S_TagError)) j8) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) ->
      henv_ok LayoutP0 VI0 (pe_H E) mc -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      realizes rsegs (mkCfg (loop_ms E 0x1a7d8 (pe_e E) ra' t0' t1' t2' (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) md) T).
    { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc HENVc STKc. unfold loop_ms.
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
    assert (INTAG : forall (q' : Z) (b : byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E, pe_sp E + 16); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m mc ->
      wmono rsegs m mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (x_v x) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E) (pframe E (Z_to_bv 64 (st0 S_TagError)) j8) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) ->
      henv_ok LayoutP0 VI0 (pe_H E) mc -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      x_p x <= q' -> q' < pe_e E -> nth_error (pe_inp E) (Z.to_nat (q' - pe_DATA E)) = Some b ->
      vct_xmlname (bv_unsigned b) = false ->
      realizes rsegs (mkCfg (loop_ms E 0x1aa68 q' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (st0 S_InTag)) t3' t4' t5' t6' mc) md) T).
    { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc HENVc STKc LQ QE Hnth NX. unfold loop_ms.
      clear VEPC FR DBY STK HENV MI.
      unfold vep_cells in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
      pose proof (ainv_stores E A m mc md _ _ PE0 AINV MUc WMc WZ) as AINVc.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU2. pose proof (wmono_refl rsegs mc) as WM2.
      assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                            [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH| exact MDL|].
      zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
          by (eapply (henv_stores E A _ _ md _ _ PE0 AINVc MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENVc])
      end.
      eapply (KL (PST q' S_InTag (fupd (x_v x) Fstate (st0 S_InTag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
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
    assert (EXIT_T : forall (q' : Z) (b : byte) (ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E, pe_sp E + 16); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m mc ->
      wmono rsegs m mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (x_v x) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E) (pframe E (Z_to_bv 64 (st0 S_TagError)) j8) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) ->
      henv_ok LayoutP0 VI0 (pe_H E) mc -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      x_p x <= q' -> q' < pe_e E -> nth_error (pe_inp E) (Z.to_nat (q' - pe_DATA E)) = Some b ->
      vct_xmlname (bv_unsigned b) = false ->
      realizes rsegs (mkCfg (loop_ms E 0x1a8a0 q' ra' t0' t1' t2' a0' (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 (vct (bv_unsigned b))) a3' a4' a5' a6' a7'
                                     (Z_to_bv 64 (st0 S_InTag)) t3' t4' t5' t6' mc) md) T).
    { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc HENVc STKc LQ QE Hnth NX. unfold loop_ms.
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
        zstep. zstep. zstep. zstep.
        apply rz_stop.
        match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
          assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
            by (eapply (henv_stores E A _ _ md _ _ PE0 AINV1 MU3 WM3 WZ3); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENV1])
        end.
        eapply (KL (PST q' S_TagError (fupd (x_v x) Fstate (st0 S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
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
        zstep. zstep. zstep. zstep. zstep. zstep.
        apply rz_stop.
        match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
          assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
            by (eapply (henv_stores E A _ _ md _ _ PE0 AINVc MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENVc])
        end.
        eapply (KL (PST (q' + 1) S_AttrDelim (fupd (x_v x) Fstate (st0 S_AttrDelim)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
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
    assert (LOOP : forall (k : nat) (q : Z) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E, pe_sp E + 16); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m mc ->
      wmono rsegs m mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (x_v x) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E) (pframe E (Z_to_bv 64 (st0 S_TagError)) j8) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) ->
      henv_ok LayoutP0 VI0 (pe_H E) mc -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      q + Z.of_nat k = pe_e E -> x_p x <= q -> q < pe_e E ->
      evt rsegs (rz_at rsegs md T)
          (loop_ms E 0x1a7b4 q ra' t0' t1' t2' (Z_to_bv 64 (pe_e E - q)) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (st0 S_InTag)) t3' t4' t5' t6' mc)).
    { induction k as [|k IH]; intros until mc; intros MUc WMc MIc VEPCc FRc DBYc HENVc STKc Hk LQ QE.
      { exfalso. clear - Hk QE. lia. }
      unfold loop_ms.
      pose proof VEPCc as VEPCk. pose proof FRc as FRk.
      clear VEPC FR DBY STK HENV MI.
      unfold vep_cells in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
      (* [comment removed for export] *)
      destruct (payload_read rsegs E mc q DBYc ltac:(clear - LQ VERP; lia) QE) as (b & Hnth & RDP).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta.
      (* [comment removed for export] *)
      zstep. zstep.
      replace (Z.shiftl (bv_unsigned b) 1) with (2 * bv_unsigned b) by (rewrite Z.shiftl_mul_pow2; clear; lia).
      pose proof (vct_read0 mc (bv_unsigned b) _ MIc BR eq_refl) as RDV. unfold wa in RDV.
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
    pose proof (munch_refl [(pe_sp E, pe_sp E + 16)] m) as MU2. pose proof (wmono_refl rsegs m) as WM2.
    assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                          [(pe_sp E, pe_sp E + 16)]) by wzone_tac.
    apply rz_go; [exact MDH| exact MDL|].
    zstep. if_cases K0; zify_cond K0. { dead K0. } clear K0.
    zstep. zstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (HENV1 : henv_ok LayoutP0 VI0 (pe_H E) m1)
        by (eapply (henv_stores E A _ _ md _ _ PE0 AINV MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha PSP CV EVSC G2; lia| exact HENV])
    end.
    clear MU2 WM2 WZ2.
    eapply (LOOP (Z.to_nat (pe_e E - x_p x)) (x_p x));
      [exact MU| exact WM| exact MI| unfold vep_cells; rewrite STATE; exact VEPC| unfold pframe; exact FR| exact DBY| exact HENV1| exact STK
      | clear - PLT; rewrite Z2Nat.id by lia; lia| clear; lia| exact PLT].
  Qed.
End S.
End V_PHo3d.

Module V_PHoxm.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c V_Paq9r V_PKit Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
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
  Context {AI : AllocSpec LayoutP0}.

  Lemma PH_ESI_Remove : handler_stmt S_ESI_Remove.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    apply rz_go; [exact MDH| exact MDL|].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    eapply (KL (PST (x_p x) S_InTag (fupd (fupd (x_v x) Fdostuff (vi_do_remove VI0)) Fstate (st0 S_InTag))
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
End V_PHoxm.

Module V_vec2f.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Img0 Img0 V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
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


Lemma sx32_small : forall z, (0 <= z < 2^31)%Z -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite bv_swrap_small; [reflexivity|].
  unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 `div` 2)%Z with 2147483648%Z. lia.
Qed.


(* [comment removed for export] *)
Local Ltac err_tail :=
  zstep; zstep; zstep; zstep;
  lazymatch goal with ST : stk _ _ ?lo (bv_unsigned ?sp) |- _ =>
    carve_frame 48%nat ST;
    do 8 zstep;
    try replace (bv_unsigned sp + -48 + 48)%Z with (bv_unsigned sp) by lia; try rewrite (Z_to_bv_bv_unsigned sp);
    lazymatch goal with FR : rw_cells _ _ (bv_unsigned sp + -48)%Z _, ST2 : stk _ _ lo _ |- _ =>
      release_frame FR ST2 (bv_unsigned sp) end
  end;
  lazymatch goal with CNT : rw_cells _ _ (h_vsc ?H + 1304)%Z _, MU : munch _ _ _, WM : wmono _ _ _, ST : stk _ _ _ _,
                      VEPC : rw_cells _ _ ?VEP (C4 (Z_to_bv 64 VEP_MAGIC) :: _), HRM : bool01 (?v Fremove), HOBJ : hobj_ok _ _ _ _ |- _ =>
    let c := fresh "cnt'" in let C := fresh "CNT'" in
    destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C; clear CNT;
    lazymatch goal with E : v Fvc = h_vc H |- _ => rewrite <- E in VEPC end;
    apply evt_done; unfold vep_do_remove_post;
    do 16 eexists; exists (v Fremove);
    split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [|split; [exact ST| split; [exact HRM|
      unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact VEPC]]];
    split;
    [ eapply (glob_ok_intro LayoutP0); [eassumption| cbn [vi_bss VI0 al_segs LayoutP0]; lazymatch goal with E : h_bss H = _ |- _ => rewrite E end; eassumption | eassumption | exact C]
    | eapply (hobj_ok_munch LayoutP0); [exact HOBJ| exact MU| exact WM|];
      intros a Ha; unfold h_req, h_resp, h_hd in Ha; cbn [outside]; lia ]
  end.

(* [comment removed for export] *)
Local Ltac store_tail :=
  zstep; zstep; zstep;
  lazymatch goal with MU : munch _ _ _, WM : wmono _ _ _, ST : stk _ _ _ _,
                      VEPC : rw_cells _ _ ?VEP (C4 (Z_to_bv 64 VEP_MAGIC) :: _), GLOB : glob_ok _ _ _ _, HOBJ : hobj_ok _ _ _ _ |- _ =>
    lazymatch type of VEPC with context [C4 (Z_to_bv 64 ?rm) :: C8 (Z_to_bv 64 (?v Fo_wait)) :: _] =>
    lazymatch goal with E : v Fvc = h_vc _ |- _ => rewrite <- E in VEPC end;
    apply evt_done; unfold vep_do_remove_post;
    do 16 eexists; exists rm;
    split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|];
    split; [| split; [exact ST| split; [| unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact VEPC]]];
    [ split;
      [ lazymatch goal with CNT : rw_cells _ _ (h_vsc ?H + 1304)%Z _ |- _ =>
          eapply (glob_ok_intro LayoutP0); [eassumption| cbn [vi_bss VI0 al_segs LayoutP0]; lazymatch goal with E : h_bss H = _ |- _ => rewrite E end; eassumption | eassumption | exact CNT] end
      | eapply (hobj_ok_munch LayoutP0); [exact HOBJ| exact MU| exact WM|];
        intros a Ha; unfold h_req, h_resp, h_hd, h_cp, h_vsc in Ha; cbn [outside]; lia ]
    | unfold bool01;
      match goal with
      | |- context [Z.b2z (?x <? ?y)] => destruct (Z.ltb_spec x y); cbn; lia
      | |- context [Z.b2z (?x =? ?y)] => destruct (Z.eqb_spec x y); cbn; lia
      end ]
    end
  end.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma vep_do_remove_ok : vep_do_remove_stmt.
Proof.
  unfold vep_do_remove_stmt.
  intros VEP v tag q H lo. intros until m.
  intros A0 A1 VEPC TAG PADS HET HEN HRM EVC HENV HG IMG VLO V8 VHI VIMG ST LO CEIL SPH MI.
  unfold off_image in VIMG. cbn [al_image_lo al_image_hi LayoutP0] in VIMG.
  rewrite A0, A1. unfold vep_do_remove_entry. unfold VEPERR_STACK in *.
  pose proof alloc_ceiling_val as ACV.
  (first [ dand3 HG as G16 GCE GHI | destruct HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
  assert (Evc : h_vc H = h_sp H + 1304) by reflexivity.
  assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity.
  assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
  assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
  destruct HENV as [GLOB HOBJ].
  (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as EBSS BSS CP [cnt CNT] | pose proof GLOB as (EBSS & BSS & CP & [cnt CNT]) ]). rewrite EBSS in BSS. cbn [vi_bss VI0 al_segs LayoutP0] in BSS.
  cbn [al_segs LayoutP0] in CP, CNT.
  (first [ pose proof (HOBJ) as dR_3; dand3 dR_3 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
  cbn [al_segs LayoutP0] in VC, WK. unfold vc_cells in VC. unfold wrk_cells in WK.
  (first [ dand4 IMG as _ _ GVSC _ | destruct IMG as (_ & _ & GVSC & _) ]). unfold GOT_vsc in GVSC.
  pose proof (rw_cells_bound _ _ _ _ VEPC) as VEPB. rewrite (vep_cells_size v tag q TAG PADS) in VEPB.
  (first [ pose proof (PADS) as dR_7; dand7 dR_7 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
  unfold vep_cells in VEPC. rewrite EVC in VEPC.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP + 92, VEP + 96)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  zstep. zstep. if_cases KW; zify_cond KW. { exfalso. klia KW. } clear KW.
  zstep. rewrite (sx32_small (v Femptytag)) by (destruct HET; lia).
  zstep. if_cases KE; zify_cond KE.
  all: cycle 1.
  - (* [comment removed for export] *)
    do 12 zstep.
    err_tail.
  - (* [comment removed for export] *)
    zstep. rewrite (sx32_small (v Fremove)) by (destruct HRM; lia).
    zstep. rewrite (sx32_small (v Fendtag)) by (destruct HEN; lia).
    zstep. if_cases KR; zify_cond KR.
    + (* [comment removed for export] *)
      zstep. if_cases KN; zify_cond KN.
      * (* [comment removed for export] *) store_tail.
      * (* [comment removed for export] *) do 13 zstep. err_tail.
    + (* [comment removed for export] *)
      zstep. if_cases KN; zify_cond KN.
      * (* [comment removed for export] *) store_tail.
      * (* [comment removed for export] *) do 13 zstep. err_tail.
Qed.

End CEIL.
End V_vec2f.


Import ListNotations.
(* [comment removed for export] *)
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
  Context {AI : AllocSpec LayoutP0}.
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
        (t0 t1 t2 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      pinv E xc Ac mc -> ainv Ac mc mdc -> md_frame md mdc -> hstep E x xc A Ac m mc ->
      x_st xc = S_InTag -> x_p x < x_p xc ->
      realizes rsegs (mkCfg (loop_ms E vep_do_comment_entry (x_p xc) (Z_to_bv 64 0x1a774) t0 t1 t2
                               (Z_to_bv 64 (pe_VEP E)) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc AINVc MDFc HSc STc LT.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      world_open PE PIc AINVc. unfold loop_ms.
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
      zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
          by (eapply (henv_stores E Ac _ _ mdc _ _ PE0 AINV1 MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV1])
      end.
      eapply (KL (PST (x_p xc) S_NxtTag (fupd (fupd (x_v xc) Fin_esi_tag 0) Fstate (st0 S_NxtTag))
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
        (t0 t1 t2 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      pinv E xc Ac mc -> ainv Ac mc mdc -> md_frame md mdc -> hstep E x xc A Ac m mc ->
      x_st xc = S_InTag -> x_p x < x_p xc ->
      realizes rsegs (mkCfg (loop_ms E vep_do_remove_entry (x_p xc) (Z_to_bv 64 0x1a774) t0 t1 t2
                               (Z_to_bv 64 (pe_VEP E)) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc AINVc MDFc HSc STc LT.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      world_open PE PIc AINVc. unfold loop_ms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] mc) as MU.
      pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
      assert (EVS : VEPERR_STACK = 48) by reflexivity.
      assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
      apply rz_go; [exact MDH| exact MDL|].
      hide STK. hide_slow.
      call_fr (HDR (pe_VEP E) (x_v xc) (x_tag xc) (x_q xc) (pe_H E) (pe_lo E)) by idtac.
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
      zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
          by (eapply (henv_stores E Ac _ _ mdc _ _ PE0 AINV1 MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV1])
      end.
      eapply (KL (PST (x_p xc) S_NxtTag (fupd (fupd (fupd (x_v xc) Fremove rm) Fin_esi_tag 0) Fstate (st0 S_NxtTag))
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
        (t0 t1 t2 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      pinv E xc Ac mc -> ainv Ac mc mdc -> md_frame md mdc -> hstep E x xc A Ac m mc ->
      x_st xc = S_InTag -> x_p x < x_p xc -> x_v xc Flast_mark = 1 ->
      realizes rsegs (mkCfg (loop_ms E vep_do_include_entry (x_p xc) (Z_to_bv 64 0x1a774) t0 t1 t2
                               (Z_to_bv 64 (pe_VEP E)) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc AINVc MDFc HSc STc LT LM.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      (* [comment removed for export] *)
      pose proof (pinv_sizes _ _ _ _ PIc) as (OUT7 & WBB & LEN0 & SZ0).
      pose proof (pw_nlive_range (x_va xc) (x_vi xc)) as WNL.
      world_open PE PIc AINVc. unfold loop_ms.
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
      replace (ret_pc (Z_to_bv 64 0x1a774)) with (Z_to_bv 64 0x1a774) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof (as_lazy_nil _ _ _ AINV1) as [MDL1 MDH1].
      rewrite VSBF in VSBO1.
      (* [comment removed for export] *)
      set (v3 := fupd (fupd (fupd (x_v xc) Fstate (v' Fstate)) Finclude_src 0) Finclude_continue (v' Finclude_continue)).
      assert (EQF : forall f, v' f = v3 f).
      { intros f. subst v3. destruct f; cbn [fupd vf_beq vf_index N.eqb Pos.eqb];
          first [ reflexivity | exact IS1 | (apply VK; clear; cbv; intros [X|[X|[X|[]]]]; discriminate X) ]. }
      destruct VEPO1 as (LVEP1 & VEPC1 & _). cbn [al_segs LayoutP0] in VEPC1. clear VEPC.
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
      assert (FR1 : rw_cells rsegs m' (pe_sp E) (pframe E j0 j8)).
      { eapply (pframe_call E Ac A' mc m' mdc (pe_sp E) DOINCL_STACK Vi _ [pe_DATA E]);
          [exact PE| exact AINVc| exact CF1| exact WIN| exact WPOS| clear; lia| exact CV1| unfold pframe; exact FR]. }
      assert (IMG1 : img_ok0 m').
      { eapply (img_call (pe_H E) Ac A' mc m' mdc (pe_sp E) DOINCL_STACK Vi _ [pe_DATA E] AINVc CF1 HG WIN); [exact CV1| exact IMG]. }
      assert (DATA1 : data_obj LayoutP0 A' m' (pe_DATA E) (pe_inp E)).
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
      zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
          by (eapply (henv_stores E A' _ _ md' _ _ PE0 AINV1 MU3 WM3 WZ3); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV1])
      end.
      eapply (KL (PST (x_p xc) S_NxtTag
                      (fupd (fupd (fupd (fupd (fupd (x_v xc) Fstate (v' Fstate)) Finclude_src 0) Finclude_continue (v' Finclude_continue)) Fin_esi_tag 0) Fstate (st0 S_NxtTag))
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
        (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc ->
      x_st xc = S_InTag -> x_p x < x_p xc ->
      realizes rsegs (mkCfg (loop_ms E 0x1a748 (x_p xc) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 mc) md) T.
    Proof.
      intros until t6. intros PIc AINVc HSc STc LT.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (mark_call HMC E xc A mc md T (x_p xc) (x_p xc) 1 0x1a758);
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
      world_open PE PI1 AINV'. unfold loop_ms. rewrite <- EP1.
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
      - rewrite DI. cbn [vi_do_include VI0]. zstep. apply rz_stop.
        eapply (intag_do_include x2 A1 _ md1); [exact PI2| exact AINV2| exact MDF| exact HS3| reflexivity| exact LT| subst x2; psimp; exact LM1].
      - rewrite DR. cbn [vi_do_remove VI0]. zstep. apply rz_stop.
        eapply (intag_do_remove x2 A1 _ md1); [exact PI2| exact AINV2| exact MDF| exact HS3| reflexivity| exact LT].
      - rewrite DC. cbn [vi_do_comment VI0]. zstep. apply rz_stop.
        eapply (intag_do_comment x2 A1 _ md1); [exact PI2| exact AINV2| exact MDF| exact HS3| reflexivity| exact LT].
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HVE"] Lemma intag_err : forall (site : Z) (xc : pst) (mc : mem)
        (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      (site = 0x1a78c \/ site = 0x1a884) ->
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc ->
      x_st xc = S_InTag -> x_p x <= x_p xc -> x_p xc < pe_e E ->
      realizes rsegs (mkCfg (loop_ms E site (x_p xc) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 mc) md) T.
    Proof.
      intros until t6. intros SITE PIc AINVc HSc STc LQ QE.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      world_open PE PIc AINVc. unfold loop_ms.
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
            assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
              by (eapply (henv_stores E A _ _ md _ _ PE0 AINV1 MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV1])
          end.
          eapply (KL (PST (x_p xc) S_TagError (fupd (x_v xc) Fstate (st0 S_TagError)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) A _ md).
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
            assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
              by (eapply (henv_stores E A _ _ md _ _ PE0 AINV1 MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV1])
          end.
          eapply (KL (PST (x_p xc) S_TagError (fupd (x_v xc) Fstate (st0 S_TagError)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) A _ md).
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
        (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc ->
      x_st xc = S_InTag -> x_p x <= x_p xc ->
      realizes rsegs (mkCfg (loop_ms E 0x1a730 (x_p xc) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 mc) md) T.
    Proof.
      intros until t6. intros PIc AINVc HSc STc LQ.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU. pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E A [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      (* [comment removed for export] *)
      assert (DSR : 0 <= x_v xc Fdostuff < 2^64 /\ x_v xc Fdostuff <> 0).
      { split; [| exact (ARMED I)]. clear - DOST. destruct DOST as [-> |[-> |[-> | ->]]]; cbn; lia. }
      destruct DSR as [DSR DNZ].
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0.
      { (* [comment removed for export] *)
        apply rz_stop.
        eapply (KL xc A mc md); [exact PIc0| exact AINVc| apply md_frame_refl; [exact MDL| exact MDH]| exact HSc|].
        intros H. exfalso. clear - H K0. unfold pe_e, pe_N in *. lia. }
      (* [comment removed for export] *)
      destruct (look_read rsegs E xc mc DBY ltac:(clear - VERP; lia) ltac:(clear - K0; unfold pe_e, pe_N in *; lia)) as (b & Hnth & Hlook & RDP).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      2:{ (* [comment removed for export] *)
          zstep. zstep. if_cases K2; zify_cond K2. { exfalso. exact (DNZ K2). } clear K2.
          zstep. apply rz_stop.
          set (xg := PST (x_p xc + 1) S_InTag (x_v xc) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)).
          assert (PIg : pinv E xg A mc); [| assert (HSg : hstep E x xg A A m mc)].
          { subst xg. apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ.
            - (* [comment removed for export] *) clear - VERP. lia.
            - (* [comment removed for export] *) clear - K0. lia. }
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
          apply rz_stop. eapply (intag_err 0x1a78c xc mc); [left; reflexivity| exact PIc0| exact AINVc| exact HSc| exact STc| exact LQ| exact K0]. }
      zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. } clear K2.
      (* [comment removed for export] *)
      zstep. pose proof B_ca as CA; destruct CA as [CA|CA]; rewrite CA, ?sx32_zero, ?sx32_one.
      { (* [comment removed for export] *)
        zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear - K3. lia. } clear K3.
        apply rz_stop. eapply (intag_err 0x1a884 xc mc); [right; reflexivity| exact PIc0| exact AINVc| exact HSc| exact STc| exact LQ| exact K0]. }
      zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3. lia. } clear K3.
      (* [comment removed for export] *)
      zstep. zstep.
      replace (Z.shiftl (bv_unsigned b) 1) with (2 * bv_unsigned b) by (rewrite Z.shiftl_mul_pow2; clear; lia).
      pose proof (vct_read0 mc (bv_unsigned b) _ MI BR eq_refl) as RDV. unfold wa in RDV.
      zstep. clear RDV. cbv beta. rewrite zx16_vct.
      pose proof (vct_range (bv_unsigned b)) as VR.
      zstep. zstep. if_cases K4; zify_cond K4.
      2:{ (* [comment removed for export] *)
          apply rz_stop. eapply (intag_err 0x1a884 xc mc); [right; reflexivity| exact PIc0| exact AINVc| exact HSc| exact STc| exact LQ| exact K0]. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (KL (PST (x_p xc) S_Attr (fupd (x_v xc) Fstate (st0 S_Attr)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) A _ md).
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
    #[using="KL PHI PE HDIT HDR HDC HVE HMC"] Lemma intag_exit1 : forall (xc : pst) (mc : mem) (b : byte)
        (ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc ->
      x_st xc = S_InTag -> x_p x <= x_p xc -> x_p xc < pe_e E ->
      nth_error (pe_inp E) (Z.to_nat (x_p xc - pe_DATA E)) = Some b ->
      realizes rsegs (mkCfg (loop_ms E 0x1a710 (x_p xc) ra t0 t1 t2 a0 (Z_to_bv 64 (bv_unsigned b)) a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 mc) md) T.
    Proof.
      intros until t6. intros PIc AINVc HSc STc LQ QE Hnth.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU. pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E A [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1.
      { apply rz_stop. eapply (intag_exit2 xc mc); [exact PIc0| exact AINVc| exact HSc| exact STc| exact LQ]. }
      (* [comment removed for export] *)
      zstep. pose proof B_em as EM; destruct EM as [EM|EM]; rewrite EM, ?sx32_zero, ?sx32_one.
      2:{ zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. }
          apply rz_stop. eapply (intag_exit2 xc mc); [exact PIc0| exact AINVc| exact HSc| exact STc| exact LQ]. }
      zstep. if_cases K2; zify_cond K2. { exfalso. clear - K2. lia. } clear K2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      apply rz_stop.
      set (xe := PST (x_p xc + 1) S_InTag (fupd (fupd (x_v xc) Femptytag 1) Fcanattr 0) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)).
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
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
      eapply (intag_exit2 xe _); [exact PIe| exact AINVe| exact HSe| reflexivity| subst xe; cbn [x_p]; clear - LQ; lia].
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HDIT HDR HDC HVE HMC"] Lemma intag_loop : forall (k : nat) (xc : pst) (mc : mem)
        (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc ->
      x_st xc = S_InTag -> x_p x <= x_p xc -> x_p xc + Z.of_nat k = pe_e E -> x_p xc < pe_e E ->
      evt rsegs (rz_at rsegs md T)
          (loop_ms E 0x1a620 (x_p xc) ra t0 t1 t2 (Z_to_bv 64 (pe_e E - x_p xc)) a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 mc).
    Proof.
      induction k as [|k IH]; intros until t6; intros PIc AINVc HSc STc LQ Hk QE.
      { exfalso. clear - Hk QE. lia. }
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU. pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E A [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      (* [comment removed for export] *)
      destruct (look_read rsegs E xc mc DBY ltac:(clear - VERP; lia) QE) as (b & Hnth & Hlook & RDP).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta.
      (* [comment removed for export] *)
      zstep. zstep.
      replace (Z.shiftl (bv_unsigned b) 1) with (2 * bv_unsigned b) by (rewrite Z.shiftl_mul_pow2; clear; lia).
      pose proof (vct_read0 mc (bv_unsigned b) _ MI BR eq_refl) as RDV. unfold wa in RDV.
      zstep. clear RDV. cbv beta. rewrite zx16_vct.
      pose proof (vct_range (bv_unsigned b)) as VR.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1.
      { apply rz_stop. eapply (intag_exit1 xc mc b); [exact PIc0| exact AINVc| exact HSc| exact STc| exact LQ| exact QE| exact Hnth]. }
      (* [comment removed for export] *)
      zstep. pose proof B_em as EM; destruct EM as [EM|EM]; rewrite EM, ?sx32_zero, ?sx32_one.
      2:{ zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. }
          apply rz_stop. eapply (intag_exit1 xc mc b); [exact PIc0| exact AINVc| exact HSc| exact STc| exact LQ| exact QE| exact Hnth]. }
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
        zstep. zstep. apply rz_stop.
        destruct (CKl (pe_e E) ltac:(clear - QE; lia) ltac:(clear; lia)) as [PIl HSl].
        eapply (intag_exit2 (PST (pe_e E) S_InTag (fupd (x_v xc) Fcanattr 1) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)));
          [exact PIl| exact AINVl| exact HSl| reflexivity| cbn [x_p]; clear - LQ QE; lia].
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HDIT HDR HDC HVE HMC"] Lemma intag_body : forall (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      pinv E x A m -> ainv A m md -> x_st x = S_InTag -> x_p x < pe_e E ->
      realizes rsegs (mkCfg (disp_ms E x ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 m) md) T.
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

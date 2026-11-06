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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m U_Pahif U_PKit U_PMark.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_Pahbe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_Pahbe.

Module U_Packp.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m U_Pahif U_PKit U_PMark U_Pahbe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ImgU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_La7nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Cov8m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahbe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32.U_cromo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU.
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
Ltac call_consts_in H ::= unfold CRC_FRAME_U, VEPERR_STACK in H.
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
Definition ret_ms (E : penv) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) : machine_state :=
  MS (mkR (pe_ra E) (Z_to_bv 64 (h_sp (pe_H E))) (pe_gp E) (al_tp LayoutPU) t0 t1 t2 (pe_s0 E) (pe_s1 E)
          a0 a1 a2 a3 a4 a5 a6 a7 (pe_s2 E) (pe_s3 E) (pe_s4 E) (pe_s5 E) (pe_s6 E) (pe_s7 E) (pe_s8 E) (pe_s9 E)
          (pe_s10 E) (pe_s11 E) t3 t4 t5 t6)
     bvmap_empty (ret_pc (pe_ra E)) (Z_to_bv 32 0) None m (seg_rom rsegs).

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Hypothesis HMC : vep_mark_common_stmt.

  (* [comment removed for export] *)
  Definition ret_K (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet) : Prop :=
    forall (x2 : pst) (A2 : AS) (m2 : mem) (md2 : Model)
           (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      pinv E x2 A2 m2 -> ainv A2 m2 md2 -> md_frame md md2 -> hstep E x x2 A A2 m m2 ->
      x_p x2 = pe_e E -> x_v x2 Fver_p = pe_e E -> stk rsegs m2 (pe_lo E) (h_sp (pe_H E)) ->
      realizes rsegs (mkCfg (ret_ms E t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2) md2) T.

  #[using="HMC"] Lemma parse_exit : forall (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s7 t3 t4 t5 t6 : word),
    penv_ok E -> pinv E x A m -> ainv A m md -> x_p x = pe_e E ->
    ret_K E x A m md T ->
    realizes rsegs (mkCfg (exit_ms E x ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s7 t3 t4 t5 t6 m) md) T.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV PEQ KR. pose proof PI as PI0.
    pose proof (as_lazy_nil _ _ _ AINV) as [MDL MDH].
    world_open PE PI AINV.
    unfold exit_ms, lmsx, PC_EXIT.
    pose proof (munch_refl [(pe_sp E - 112, pe_sp E); (pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_sp E - 112, pe_sp E); (pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (R1 : 0 <= x_p x < 2^64) by lia. assert (R2 : 0 <= x_v x Fver_p < 2^64) by lia.
    apply rz_go; [exact MDH| exact MDL|].
    (* [comment removed for export] *)
    zstep. zstep. if_cases KP; zify_cond KP.
    - (* [comment removed for export] *)
      do 13 zstep. zstep. zstep.
      release_frame FR STK (h_sp (pe_H E)). cps_done.
      replace (pe_sp E + 208) with (h_sp (pe_H E)) by (rewrite PSP; lia).
      eapply (KR x A m md); [exact PI0 | exact AINV | apply md_frame_refl; [exact MDL| exact MDH] | | exact PEQ | lia | exact STK].
      apply hstep_refl. eapply (stk_mapped (L:=LayoutPU)); [exact STK| exact CEIL| stk_lia| stk_lia].
    - (* [comment removed for export] *)
      assert (SKIP : forall a0v,
        evt rsegs (rz_at rsegs md T)
          (lmsx E 0x1ae9c s1 s7 (Z_to_bv 64 (x_p x)) ra t0 t1 t2 a0v (Z_to_bv 64 (x_v x Fver_p)) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m)).
      { intros a0v. unfold lmsx.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. apply rz_stop.
        eapply (mark_call_x HMC E x A m md T (x_p x) 1 0x1aeac s1 s7 (Z_to_bv 64 (x_p x)));
          [ exact PE | exact PI0 | exact AINV | lia | unfold pe_e, pe_N; exact PLE | right; reflexivity | lia | reflexivity
          | intros _; reflexivity | ].
        intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1.
        assert (EP1 : x_p x1 = x_p x) by (rewrite EX1; reflexivity).
        assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
        clear - HMC PE PEQ KR PI1 AINV' MDF HS VK VERP1 LM1 OP1 EP1 EV1.
        pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
        world_open PE PI1 AINV'. unfold lmsx.
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
        assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                             [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
        apply rz_go; [exact MDH'| exact MDL'|].
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        do 13 zstep. zstep. zstep.
        pose proof FR as FRc. pose proof STK as STKc.
        release_frame FR STK (h_sp (pe_H E)). cps_done.
        replace (pe_sp E + 208) with (h_sp (pe_H E)) by (rewrite PSP; lia).
        lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
          eapply (KR (PST (x_p x1) (x_st x1)
                        (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1))
                        (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 mx md1) end.
        2:{ eapply (ainv_stores E A1 m2 _ md1 _ _ PE0 AINV' MU WM WZ). }
        2:{ exact MDF. }
        2:{ eapply hstep_trans; [exact HS|].
            eapply hstep_stores; [exact MU | | eapply (stk_mapped (L:=LayoutPU)); [exact STK| exact CEIL| stk_lia| stk_lia]
                                 | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
            w_in_zone_tac. left. unfold blk. lia. }
        2:{ psimp. rewrite EP1. exact PEQ. }
        2:{ psimp. rewrite EV1, VERP1. exact PEQ. }
        2:{ exact STK. }
        apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ.
        split; [exact DELIM1| exact DELIM2]. }
      destruct B_ie as [IE|IE].
      + (* [comment removed for export] *)
        zstep. rewrite IE, (sx32_small 0) by lia. zstep. if_lit.
        destruct B_rm as [RM|RM].
        * (* [comment removed for export] *)
          zstep. rewrite RM, (sx32_small 0) by lia. zstep. if_lit.
          (* [comment removed for export] *)
          assert (LTP : x_v x Fver_p < x_p x) by (clear - KP VERP; lia).
          zstep. if_cases K0; zify_cond K0. { exfalso. klia K0. } clear K0.
          zstep. zstep. if_cases KL0; zify_cond KL0.
          { exfalso. rewrite (proj2 (Z.ltb_lt 0 _)) in KL0 by lia. rewrite (proj2 (Z.ltb_lt _ _)) in KL0 by lia. discriminate KL0. }
          clear KL1 KL2.
          (* [comment removed for export] *)
          zstep. zstep. rewrite Z.add_0_r, (swrap32_small (x_p x - x_v x Fver_p)) by lia. zstep.
          (* [comment removed for export] *)
          hide STK.
          call_fr (crc32_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pe_lo E) (pslice E (x_v x Fver_p) (x_p x))) by idtac.
          1:{ exact MI. }
          1:{ unhide STK. rewrite unsigned_lit by lia. exact STK. }
          1:{ rewrite unsigned_lit by lia. lia. }
          1:{ rewrite unsigned_lit by lia. apply pslice_bytes; [exact DBY| lia| lia| lia]. }
          1:{ rewrite !unsigned_lit by lia. left. rewrite pslice_length by lia. lia. }
          1:{ rewrite unsigned_lit by lia. rewrite pslice_length by lia. lia. }
          1:{ rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. rewrite pslice_length by lia. lia. }
          clear STK. rename POST into STK. rename MI0 into MI.
          (* [comment removed for export] *)
          assert (OPB : 0 <= x_v x Fo_pending /\ x_v x Fo_pending + (x_p x - x_v x Fver_p) < 2^40).
          { revert CNT VERP LTP PLE NN. clear. unfold vep_cnt, NMAX, pe_e, pe_N. intros; lia. }
          zstep. zstep. zstep. zstep. zstep. zstep.
          zstep. if_cases K0; zify_cond K0.
          { exfalso. unsign K0. apply K0. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
          clear K0.
          (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. zstep. zstep. zstep.
          do 13 zstep. zstep. zstep.
          pose proof FR as FRc. pose proof STK as STKc.
          release_frame FR STK (h_sp (pe_H E)). cps_done.
          replace (pe_sp E + 208) with (h_sp (pe_H E)) by (rewrite PSP; lia).
          match goal with VEPC : rw_cells _ ?mx (pe_VEP E) _ |- _ =>
            match type of VEPC with context [C4 ?w :: CB 4 (p140 _) :: _] =>
              rewrite <- (Z_to_bv_bv_unsigned w) in VEPC;
              eapply (KR (PST (x_p x) (x_st x)
                            (fupd (fupd (fupd (fupd (x_v x) Fo_pending (x_v x Fo_pending + (x_p x - x_v x Fver_p)))
                                  Fcrcp (bv_unsigned w)) Fver_p (x_p x))
                                  Fnm_pending (bv_unsigned (sx32 (Z_to_bv 64 (x_v x Fnm_pending))) + 1))
                            (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A mx md)
            end end.
          2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
          2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
          2:{ eapply hstep_stores; [exact MU | | eapply (stk_mapped (L:=LayoutPU)); [exact STK| exact CEIL| stk_lia| stk_lia]
                                   | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                                   | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
              w_in_zone_tac. left. unfold blk. lia. }
          2:{ psimp. exact PEQ. }
          2:{ psimp. exact PEQ. }
          2:{ exact STK. }
          apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
          -- revert CNT VERP LTP. clear. unfold vep_cnt. cbn [fupd vf_beq vf_index N.eqb Pos.eqb]. intros; lia.
          -- lia.
          -- split; [exact DELIM1| exact DELIM2].
        * (* [comment removed for export] *)
          zstep. rewrite RM, (sx32_small 1) by lia. zstep. if_lit. apply SKIP.
      + (* [comment removed for export] *)
        zstep. rewrite IE, (sx32_small 1) by lia. zstep. if_lit. apply SKIP.
  Qed.
End S.
End U_Packp.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_HKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ImgU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_La7nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Cov8m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahbe.U_Paczw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahbe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Parse.U_Packp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_HKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.RL.sec := Ltac2.Init.true.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
Ltac unhide_all := repeat match goal with H : kept _ |- _ => unhide H end.
Tactic Notation "olia" ne_hyp_list(hs) := clear - hs; unhide_all; lia.

(* [comment removed for export] *)
Lemma CB32_four_C8 : forall segs m a (junk : list byte) cs,
  rw_cells segs m a (CB 32 junk :: cs) ->
  exists j0 j8 j16 j24, rw_cells segs m a (C8 j0 :: C8 j8 :: C8 j16 :: C8 j24 :: cs).
Proof.
  intros segs m a junk cs RC.
  pose proof (rw_cells_peel _ _ _ _ _ RC) as [H1 _]. pose proof (rw_CB_length _ _ _ _ _ H1) as LEN.
  exists (le_bytes_to_word (firstn 8 junk)), (le_bytes_to_word (firstn 8 (skipn 8 junk))),
         (le_bytes_to_word (firstn 8 (skipn 16 junk))), (le_bytes_to_word (skipn 24 junk)).
  eapply rw_cells_recast; [exact RC| |].
  - cbn. destruct RC as [[WF _] _]. cbn in WF. tauto.
  - cbn [cells_bytes cbytes app]. rewrite !le8_of_bytes by (rewrite ?length_firstn, ?length_skipn; lia).
    set (rest := cells_bytes cs). clearbody rest.
    replace (skipn 24 junk) with (skipn 8 (skipn 16 junk)) by (rewrite skipn_skipn; reflexivity).
    rewrite (app_assoc (firstn 8 (skipn 16 junk)) (skipn 8 (skipn 16 junk)) rest), (firstn_skipn 8 (skipn 16 junk)).
    replace (skipn 16 junk) with (skipn 8 (skipn 8 junk)) by (rewrite skipn_skipn; reflexivity).
    rewrite (app_assoc (firstn 8 (skipn 8 junk)) (skipn 8 (skipn 8 junk)) rest), (firstn_skipn 8 (skipn 8 junk)).
    rewrite (app_assoc (firstn 8 junk) (skipn 8 junk) rest), (firstn_skipn 8 junk). reflexivity.
Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Hypothesis HMC : vep_mark_common_stmt.
  Hypothesis HND : forall st, st <> S_MatchBuf -> handler_stmt st.

  (* [comment removed for export] *)
  #[using="HND HMC"] Lemma parse_from_head : forall (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word),
    penv_ok E -> pinv E x A m -> ainv A m md -> x_st x <> S_MatchBuf -> x_p x < pe_e E ->
    ret_K E x A m md T ->
    realizes rsegs (mkCfg (head_ms E x ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 m) md) T.
  Proof.
    intros until t6. intros PE PI AINV NMB PLT KR.
    eapply (loop_ok HND (S (Z.to_nat (phi E x)))); [lia| exact PE| exact PI| exact AINV| exact NMB| exact PLT|].
    intros x' A' m' md' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s1' s7' t3' t4' t5' t6' PI' AINV' MDF HS PEQ.
    eapply (parse_exit HMC E x' A' m' md' T); [exact PE| exact PI'| exact AINV'| exact PEQ|].
    intros x2 A2 m2 md2 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 PI2 AINV2 MDF2 HS2 PEQ2 VEQ2 STK2.
    eapply (KR x2 A2 m2 md2); [exact PI2| exact AINV2| eapply md_frame_trans; [exact MDF| exact MDF2]
      | eapply hstep_trans; [exact HS| exact HS2]| exact PEQ2| exact VEQ2| exact STK2].
  Qed.

  #[using="HND HMC"] Theorem VEP_Parse_ok : VEP_Parse_stmt.
  Proof.
    intros H VEP S b flags wa DATA inp tag q lo.
    intros until T. intros AINV MI Ha0 Ha1 Ha2 FL VEPO NS0 VSO WS1 DATA0 HENV HG IMG
           NE_VS NE_Vb NE_wS NE_wb NE_DV NE_DS NE_Db NE_Dw LBUD NBUD TP SP16 RA2 STK CEIL LOP HSP K.
    pose proof (as_lazy_nil _ _ _ AINV) as [MDL MDH].
    set (E := PENV H VEP S b flags wa DATA inp lo gp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (a_livebytes A) (a_nlive A)).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). pose proof alloc_ceiling_val as CV.
    (first [ pose proof (VEPO) as dR_2; dand4 dR_2 as LVEP VEPC TAG PADS | pose proof VEPO as (LVEP & VEPC & TAG & PADS) ]). cbn [al_segs LayoutPU] in VEPC.
    (first [ pose proof (DATA0) as dR_3; dand3 dR_3 as LDATA DBY DLEN | pose proof DATA0 as (LDATA & DBY & DLEN) ]).
    pose proof VSO as VSOx. (first [ dand6 VSOx as VSC VINV LVS LVB SNB (bs0 & U8 & LBS & NUL0) | destruct VSOx as (VSC & VINV & LVS & LVB & SNB & (bs0 & U8 & LBS & NUL0)) ]). cbn [al_segs LayoutPU] in VSC, U8.
    cbn [vb_buf vb_size vb_len vsb_fresh] in LVB, SNB, U8, LBS.
    pose proof WS1 as WS1x. (first [ dex2 WS1x as wid wpad; dand7 WS1x as _ _ _ _ LWA _ _ | dand9 WS1x as wid wpad _ _ _ _ LWA _ _ | destruct WS1x as (wid & wpad & _ & _ & _ & _ & LWA & _ & _) ]).
    (first [ pose proof ((live_geom LayoutPU _ _ _ _ _ AINV LVEP)) as dR_6; dand7 dR_6 as _ VEP16 VEPlo VEPhi VEPimg _ _ | pose proof (live_geom LayoutPU _ _ _ _ _ AINV LVEP) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & _ & _) ]).
    (first [ pose proof ((live_geom LayoutPU _ _ _ _ _ AINV LDATA)) as dR_7; dand7 dR_7 as _ _ Dlo Dhi Dimg _ _ | pose proof (live_geom LayoutPU _ _ _ _ _ AINV LDATA) as (_ & _ & Dlo & Dhi & Dimg & _ & _) ]).
    (first [ pose proof ((live_geom LayoutPU _ _ _ _ _ AINV LVS)) as dR_8; dand7 dR_8 as _ S16 Slo Shi Simg _ _ | pose proof (live_geom LayoutPU _ _ _ _ _ AINV LVS) as (_ & S16 & Slo & Shi & Simg & _ & _) ]).
    (first [ pose proof ((live_geom LayoutPU _ _ _ _ _ AINV LVB)) as dR_9; dand7 dR_9 as _ _ Blo Bhi Bimg _ _ | pose proof (live_geom LayoutPU _ _ _ _ _ AINV LVB) as (_ & _ & Blo & Bhi & Bimg & _ & _) ]).
    (first [ pose proof ((live_geom LayoutPU _ _ _ _ _ AINV LWA)) as dR_10; dand7 dR_10 as _ _ Wlo Whi Wimg _ _ | pose proof (live_geom LayoutPU _ _ _ _ _ AINV LWA) as (_ & _ & Wlo & Whi & Wimg & _ & _) ]).
    unfold off_image in VEPimg, Dimg, Simg, Bimg, Wimg. cbn [al_image_lo al_image_hi LayoutPU] in VEPimg, Dimg, Simg, Bimg, Wimg.
    assert (NE_Vw : VEP <> wa) by (intros X; rewrite X, LWA in LVEP; discriminate LVEP).
    pose proof (as_live_disjoint _ _ _ _ _ _ _ AINV LVEP LVS NE_VS) as DJ_VS.
    pose proof (as_live_disjoint _ _ _ _ _ _ _ AINV LVEP LVB NE_Vb) as DJ_VB.
    pose proof (as_live_disjoint _ _ _ _ _ _ _ AINV LVEP LDATA (not_eq_sym NE_DV)) as DJ_VD.
    pose proof (as_live_disjoint _ _ _ _ _ _ _ AINV LVEP LWA NE_Vw) as DJ_VW.
    pose proof (as_live_disjoint _ _ _ _ _ _ _ AINV LVS LWA (not_eq_sym NE_wS)) as DJ_SW.
    pose proof (as_live_disjoint _ _ _ _ _ _ _ AINV LVB LWA (not_eq_sym NE_wb)) as DJ_BW.
    assert (PE : penv_ok E).
    { unfold penv_ok; cbn [pe_H pe_flags pe_lo pe_VEP pe_S pe_wa pe_DATA pe_ra pe_inp pe_N pe_LB0 pe_NL0 E].
      split; [exact HG|]. split; [exact FL|]. split; [unfold pe_N; cbn [pe_inp E]; unfold NMAX; lia|].
      split; [exact CEIL|]. split; [lia|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto. }
    assert (PSP : pe_sp E = h_sp H - 208) by reflexivity.
    assert (EE : pe_e E = DATA + Z.of_nat (length inp)) by reflexivity.
    (* [comment removed for export] *)
    assert (Esp : sp = Z_to_bv 64 (h_sp H)) by (rewrite <- HSP; symmetry; apply Z_to_bv_bv_unsigned).
    unfold HFRAME in G3. unfold PARSE_STACK, DOINCL_STACK, REALLOC_STACK in LOP.
    rewrite Ha0, Ha1, Ha2, TP. rewrite Esp in K |- *. rewrite TP in K. rewrite HSP in STK, SP16, LOP. clear HSP. rewrite unsigned_lit in K by lia.
    pose proof (bv_unsigned_in_range _ ra) as Rra.
    unfold VEP_Parse_entry. unfold vep_cells in VEPC. cbn [vep_init_map] in VEPC.
    pose proof (munch_refl [(h_sp H - 208, h_sp H); (VEP, VEP + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutPU A [(h_sp H - 208, h_sp H); (VEP, VEP + 312)]).
    { cbn. split; [left; lia|]. split; [right; left; exists VEP, 312; split; [exact LVEP| lia]| exact I]. }
    hide U8. hide VSC. hide DBY.
    hide VEPimg. hide Dimg. hide Simg. hide Bimg. hide Wimg. hide DJ_VS. hide DJ_VB. hide DJ_VD. hide DJ_VW. hide DJ_SW. hide DJ_BW.
    apply rz_go; [exact MDH | exact MDL |].
    (* [comment removed for export] *)
    carve_frame 208%nat STK.
    do 14 zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { exfalso. unsign K0. lia. } clear K0.
    zstep. zstep. zstep. if_cases K0; zify_cond K0. { exfalso; apply K0; apply land7_of_mod8; [lia| apply mod8_of_mod16; exact VEP16]. } clear K0.
    zstep. zstep. zstep. zstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. revert K0. clear. unfold VEP_MAGIC. vm_compute. congruence. } clear K0.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { exfalso. unsign K0. lia. } clear K0.
    (* [comment removed for export] *)
    zstep. zstep. if_lit.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m1 end.
    assert (AINV0 : ainv A m1 md) by (eapply (ainv_munch LayoutPU); [exact AINV| exact MU| exact WM| exact CFP]).
    assert (MAP1 : mapped m1 (h_sp H - PARSE_STACK) PARSE_STACK).
    { eapply (window_mapped LayoutPU m1 lo (h_sp H + -208) (h_sp H) PARSE_STACK); [exact STK| exact FR| cbn; lia| exact CEIL| unfold PARSE_STACK, DOINCL_STACK, REALLOC_STACK; olia LOP| unfold PARSE_STACK, DOINCL_STACK, REALLOC_STACK; olia LOP]. }
    rename MU into MU0. rename WM into WM0.
    set (v0 := fupd (fupd (vep_init_map H VEP S flags) Fver_p LIT_empty) Flast_mark 1).
    eapply (HMC VEP v0 tag q (vsb_fresh b) H LIT_empty 0 0 [] lo);
      [ exact AINV0
      | exact MI
      | reflexivity | reflexivity | reflexivity | left; reflexivity
      | split; [exact LVEP|]; split; [subst v0; unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map al_segs LayoutPU]; exact VEPC
                             | split; [exact TAG| exact PADS]]
      | subst v0; unfold vep_base; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity
      | eapply (henv_ok_munch LayoutPU); [exact HENV| exact MU0| exact WM0|];
        intros a Ha; pose proof HENV as ((Ebss & _) & _); rewrite Ebss in Ha; cbn [vi_bss VIU] in Ha;
        unfold h_hd, h_wrk, h_req, h_vsc in Ha; cbn [outside]; olia Ha VEPhi VEPimg G2 CV
      | exact HG
      | eapply (img_okU_munch _ m); [exact MU0| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; olia Ha VEPhi VEPimg G2 CV| exact IMG]
      | subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; right; reflexivity
      | subst v0; unfold vep_cnt; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map]; lia
      | lia
      | subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; unfold NMAX; lia
      | subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map];
        eapply (vsb_obj_munch LayoutPU); [exact VSO| exact MU0| exact WM0| cbn; olia Shi DJ_VS G2 CV| cbn; olia Bhi DJ_VB G2 CV]
      | subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map]; exact NE_VS
      | cbn [vb_buf vsb_fresh]; exact NE_Vb
      | cbn [vb_size vsb_fresh]; unfold EXT_MAX; lia
      | cbn [vb_size vsb_fresh]; pose proof (vsb_extendsize_tight (16 + 9)) as EXT0; revert LBUD EXT0; unfold PARSE_LIVE; clear; intros; lia
      | revert NBUD; unfold PARSE_NLIVE; clear; intros; lia
      | subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; apply bytes_at_nil; unfold LIT_empty; lia
      | subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb length Z.of_nat]; lia
      | subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; unfold LIT_empty; lia
      | unfold LIT_empty; lia
      | left; subst v0; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; split; reflexivity
      | reflexivity
      | rewrite unsigned_lit by lia; replace (h_sp H + -208) with (h_sp H - 208) by lia; rewrite Zminus_mod, G1; reflexivity
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; exact STK
      | exact CEIL
      | rewrite unsigned_lit by lia; unfold MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK; lia
      | rewrite unsigned_lit by lia; lia
      | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m2 md1 v1 vv1
           AINV1 MI2 MDF ST2 VO1 VK VERP1 LM1 OP1 CNT1 CRC1 CRCP1 VSO1 LEN1 SZ1 REL LIVE1 LB1 NL1 HENV1 DBY1 CF1.
    rewrite unsigned_lit in ST2, CF1 by lia.
    subst v0. cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map vb_buf vb_size vb_len vsb_fresh] in CNT1, VSO1, LEN1, SZ1, REL, LIVE1, LB1, DBY1, CF1.
    replace (ret_pc (Z_to_bv 64 106760)) with (Z_to_bv 64 106760) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (as_lazy_nil _ _ _ AINV1) as [MDL1 MDH1].
    clear CFP. try clear MI.
    (* [comment removed for export] *)
    (first [ pose proof (VO1) as dR_11; dand4 dR_11 as LVEP1 VEPC1 _ _ | pose proof VO1 as (LVEP1 & VEPC1 & _ & _) ]). cbn [al_segs LayoutPU] in VEPC1.
    assert (LDATA1 : a_live A1 DATA = Some (Z.of_nat (length inp))) by (eapply (live_keep A A1 b (vb_buf vv1)); [exact LIVE1| exact REL| exact LDATA| exact NE_Db]).
    assert (LWA1 : a_live A1 wa = Some 40) by (eapply (live_keep A A1 b (vb_buf vv1)); [exact LIVE1| exact REL| exact LWA| exact NE_wb]).
    (first [ pose proof (VSO1) as dR_12; dand6 dR_12 as _ VINV1 LVS1 LVB1 SNB1 _ | pose proof VSO1 as (_ & VINV1 & LVS1 & LVB1 & SNB1 & _) ]).
    assert (NB_D : DATA <> vb_buf vv1) by (eapply (fresh_ne A A1 b); [exact REL| exact LDATA| exact NE_Db]).
    assert (NB_W : wa <> vb_buf vv1) by (eapply (fresh_ne A A1 b); [exact REL| exact LWA| exact NE_wb]).
    assert (NB_V : VEP <> vb_buf vv1) by (eapply (fresh_ne A A1 b); [exact REL| exact LVEP| exact NE_Vb]).
    (* [comment removed for export] *)
    assert (CV1 : vcover H A [DATA; wa] (fun a => blk VEP 312 a \/ blk b 16 a \/ S <= a < S + 40)).
    { intros a [Ha|[Ha|Ha]].
      - eapply cover_blk; [exact LVEP| cbn [In]; intros [X|[X|[]]]; [exact (NE_DV X)| exact (NE_Vw (eq_sym X))]| exact Ha].
      - eapply cover_blk; [exact LVB| cbn [In]; intros [X|[X|[]]]; [exact (NE_Db X)| exact (NE_wb X)]| exact Ha].
      - eapply cover_rng; [exact LVS| cbn [In]; intros [X|[X|[]]]; [exact (NE_DS X)| exact (NE_wS X)]| exact Ha]. }
    assert (WIN1 : alloc_ceiling <= h_sp H + -208 - MARK_STACK) by (unfold MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK; lia).
    lazymatch type of FR with rw_cells _ _ _ (CB 104 ?j :: _) => set (junk104 := j) in FR; clearbody junk104 end.
    assert (FR2 : rw_cells rsegs m2 (h_sp H + -208)
              [CB 104 junk104; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_call_stack H A A1 m1 m2 md (h_sp H + -208) MARK_STACK _ _ [DATA; wa] AINV0 CF1 WIN1);
        [unfold MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK; lia| exact CV1| exact FR| lia| cbn; unfold h_vsc; lia]. }
    assert (DATA2 : data_obj LayoutPU A1 m2 DATA inp).
    { unhide DBY. eapply (data_obj_call H A A1 m1 m2 md (h_sp H + -208) MARK_STACK _ _ [DATA; wa] AINV0 CF1 HG WIN1);
        [exact CV1| cbn; left; reflexivity| exact LDATA1|].
      split; [exact LDATA|]. split; [| exact DLEN]. eapply bytes_at_transport; [exact DBY| exact MU0| cbn; olia Dhi DJ_VD G2 CV DLEN]. }
    assert (IMG2 : img_okU m2).
    { eapply (img_call H A A1 m1 m2 md (h_sp H + -208) MARK_STACK _ _ [DATA; wa] AINV0 CF1 HG WIN1); [exact CV1|].
      eapply (img_okU_munch _ m); [exact MU0| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; olia Ha VEPhi VEPimg G2 CV| exact IMG]. }
    assert (WS1_2 : ws1_obj LayoutPU H A1 m2 wa VEP).
    { eapply (ws1_obj_ccall LayoutPU H A A1 m1 md m2 (h_sp H + -208) MARK_STACK); [exact AINV0| exact CF1| exact HG| | lia| exact WIN1| exact LWA1| exact LVEP1|].
      - eapply (ws1_obj_munch LayoutPU); [exact WS1| exact MU0| exact WM0|]. intros a Ha. unfold h_ws, h_wsbuf in Ha. cbn [outside]. olia Ha VEPhi Whi G2 CV DJ_VW.
      - intros a Ha [X|[X|X]]; unfold blk in X; unfold h_ws, h_wsbuf in Ha; olia Ha X VEPhi Bhi Shi Whi G2 CV DJ_VW DJ_BW DJ_SW. }
    assert (MAP2 : mapped m2 (h_sp H - PARSE_STACK) PARSE_STACK).
    { eapply (window_mapped LayoutPU m2 lo (h_sp H + -208) (h_sp H) PARSE_STACK); [exact ST2| exact FR2| cbn; lia| exact CEIL| unfold PARSE_STACK, DOINCL_STACK, REALLOC_STACK; olia LOP| unfold PARSE_STACK, DOINCL_STACK, REALLOC_STACK; olia LOP]. }
    rename FR into FRm1. hide FRm1. hide CF1. clear CV1.
    (* [comment removed for export] *)
    pose proof (munch_refl [(h_sp H + -176, h_sp H + -104); (VEP, VEP + 312)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
    assert (CFP : client_fp LayoutPU A1 [(h_sp H + -176, h_sp H + -104); (VEP, VEP + 312)]).
    { cbn. split; [left; lia|]. split; [right; left; exists VEP, 312; split; [exact LVEP1| lia]| exact I]. }
    unfold vep_cells in VEPC1. vk_norm_in VK VEPC1. cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map] in VEPC1.
    rewrite VERP1, LM1, OP1 in VEPC1.
    hide ST2. clear DBY1.
    hide VEPimg. hide Dimg. hide Simg. hide Bimg. hide Wimg. hide DJ_VS. hide DJ_VB. hide DJ_VD. hide DJ_VW. hide DJ_SW. hide DJ_BW. hide REL. hide SZ1. hide LIVE1.
    apply rz_go; [exact MDH1 | exact MDL1 |].
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { exfalso. unsign K0. olia K0 Dlo Dhi DLEN CV. } clear K0.
    zstep. if_cases K0; zify_cond K0. { exfalso. unsign K0. olia K0 Dlo. } clear K0.
    zstep. if_cases K0; zify_cond K0. { exfalso. unsign K0. olia K0 Dlo Dhi DLEN CV. } clear K0.
    (* [comment removed for export] *)
    do 33 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (IMGc : img_okU mc) by (eapply (img_okU_munch _ m2); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; olia Ha VEPhi VEPimg G2 CV| exact IMG2]) end.
    pose proof IMGc as (ROvct & _). unfold GOT_vct in ROvct.
    zstep. clear ROvct.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    apply rz_stop. clear IMGc.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m3 end.
    (* [comment removed for export] *)
    (first [ pose proof ((CB32_four_C8 _ _ _ _ _ FR2)) as dR_13; dex4 dR_13 as j0 j8 j16 j24; rename dR_13 into FR3 | pose proof ((CB32_four_C8 _ _ _ _ _ FR2)) as dR_13; dand5 dR_13 as j0 j8 j16 j24 FR3 | destruct (CB32_four_C8 _ _ _ _ _ FR2) as (j0 & j8 & j16 & j24 & FR3) ]). clear FR2.
    assert (AINV3 : ainv A1 m3 md1) by (eapply (ainv_munch LayoutPU); [exact AINV1| exact MU| exact WM| exact CFP]).
    unhide ST2.
    assert (ST3 : stk rsegs m3 lo (h_sp H + -208)).
    { eapply stk_transport_disjoint; [exact ST2| exact MU| exact WM| cbn; olia CEIL LOP VEPhi]. }
    assert (IMG3 : img_okU m3).
    { eapply (img_okU_munch _ m2); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; olia Ha VEPhi VEPimg G2 CV| exact IMG2]. }
    assert (HENV3 : henv_ok LayoutPU VIU H m3).
    { eapply (henv_ok_munch LayoutPU); [exact HENV1| exact MU| exact WM|].
      intros a Ha; pose proof HENV1 as ((Ebss & _) & _); rewrite Ebss in Ha; cbn [vi_bss VIU] in Ha;
      unfold h_hd, h_wrk, h_req, h_vsc in Ha; cbn [outside]; olia Ha VEPhi VEPimg G2 CV. }
    assert (VSO3 : vsb_obj LayoutPU A1 m3 S vv1 false).
    { (first [ pose proof ((live_geom LayoutPU _ _ _ _ _ AINV1 LVS1)) as dR_14; dand5 dR_14 as _ _ _ Shi1 _ | pose proof (live_geom LayoutPU _ _ _ _ _ AINV1 LVS1) as (_ & _ & _ & Shi1 & _) ]).
      (first [ pose proof ((live_geom LayoutPU _ _ _ _ _ AINV1 LVB1)) as dR_15; dand5 dR_15 as _ _ _ Bhi1 _ | pose proof (live_geom LayoutPU _ _ _ _ _ AINV1 LVB1) as (_ & _ & _ & Bhi1 & _) ]).
      pose proof (as_live_disjoint _ _ _ _ _ _ _ AINV1 LVEP1 LVS1 NE_VS) as DJ1.
      pose proof (as_live_disjoint _ _ _ _ _ _ _ AINV1 LVEP1 LVB1 NB_V) as DJ2.
      eapply (vsb_obj_munch LayoutPU); [exact VSO1| exact MU| exact WM| cbn; olia Shi1 DJ1 G2 CV| cbn; olia Bhi1 DJ2 G2 CV]. }
    assert (DATA3 : data_obj LayoutPU A1 m3 DATA inp).
    { (first [ dand3 DATA2 as LD2 DBY2 _ | destruct DATA2 as (LD2 & DBY2 & _) ]). split; [exact LD2|]. split; [| exact DLEN].
      pose proof (as_live_disjoint _ _ _ _ _ _ _ AINV1 LVEP1 LDATA1 (not_eq_sym NE_DV)) as DJ3.
      eapply bytes_at_transport; [exact DBY2| exact MU| cbn; olia Dhi DJ3 G2 CV DLEN]. }
    clear ST2 IMG2 HENV1 VSO1 DATA2 CFP.
    set (v2 := fupd (fupd (fupd v1 Fstartup 0) Fhack_p DATA) Fver_p DATA).
    set (x0 := PST DATA S_Start v2 tag q vv1 None None).
    pose proof CNT1 as CNT1'. unfold vep_cnt, LIT_empty in CNT1'.
    assert (PI0 : pinv E x0 A1 m3).
    { subst x0 v2. apply Build_pinv; cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi pe_VEP pe_S pe_H pe_DATA pe_flags pe_wa pe_lo pe_inp E];
        unfold va_world, vi_world, in_tag_cluster, attr_states, avsb_states, oacost, oicost;
        cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi fupd vf_beq vf_index N.eqb Pos.eqb pe_VEP pe_S pe_H pe_DATA pe_flags pe_wa pe_lo pe_inp E].
      all: try (vk_norm VK; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map]).
      - split; [exact LVEP1|]. split; [| split; [exact TAG| exact PADS]].
        unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb al_segs LayoutPU]. vk_norm VK. cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map].
        rewrite ?LM1, ?OP1. exact VEPC1.
      - unfold vep_base; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]. vk_norm VK. cbn [fupd vf_beq vf_index N.eqb Pos.eqb vep_init_map]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold vep_cnt; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]. olia CNT1'.
      - lia.
      - unfold pe_e, pe_N; cbn [pe_DATA pe_inp E]. olia DLEN.
      - rewrite LM1. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; left; reflexivity.
      - lia.
      - split; [intros _; reflexivity| intros X; discriminate X].
      - left; split; reflexivity.
      - intros X; discriminate X.
      - intros X; discriminate X.
      - left; reflexivity.
      - intros X; destruct X.
      - left; reflexivity.
      - intros X; destruct X.
      - intros X; discriminate X.
      - intros X; discriminate X.
      - intros X; discriminate X.
      - exact VSO3.
      - unhide SZ1. olia SZ1 LEN1.
      - olia LEN1.
      - intros y Hy. destruct Hy as [<-|[<-|[<-|[]]]]; split.
        + exact (not_eq_sym NE_VS). + exact (not_eq_sym NB_V).
        + exact (not_eq_sym NE_wS). + exact (not_eq_sym NB_W).
        + exact (not_eq_sym NE_DS). + exact (not_eq_sym NB_D).
      - exact LWA1.
      - intros X; apply X; reflexivity.
      - reflexivity.
      - reflexivity.
      - exact DATA3.
      - exact HENV3.
      - exact IMG3.
      - unfold pe_sp; cbn [pe_H E]. replace (h_sp H - 208) with (h_sp H + -208) by lia. exact ST3.
      - exists j0, j8, j16, j24. unfold pframe, pe_sp, pe_e, pe_N; cbn [pe_VEP pe_H pe_DATA pe_inp pe_s0 pe_s1 pe_s2 pe_s3 pe_s4 pe_s5 pe_s6 pe_s7 pe_s8 pe_s9 pe_s10 pe_s11 pe_ra E].
        replace (h_sp H - 208) with (h_sp H + -208) by lia.
        rewrite (lxor_ones (VEP + 256)) in FR3 by olia VEPlo VEPhi CV.
        rewrite (Z_to_bv_eqm (0 - (DATA + Z.of_nat (length inp))) (2 ^ 64 - (DATA + Z.of_nat (length inp)))) in FR3
          by (rewrite <- (Z_mod_plus_full (0 - (DATA + Z.of_nat (length inp))) 1 (2^64)); f_equal; lia).
        replace (2 ^ 64 - 1 - (VEP + 256)) with (18446744073709551615 - (VEP + 256)) by lia.
        exact FR3.
      - exact MI2.
      - (* [comment removed for export] *)
        cbn [pe_LB0 E]. unfold pw_bytes. olia LB1.
      - (* [comment removed for export] *) cbn [pe_NL0 E]. unfold pw_nlive. olia NL1. }
    assert (MAP3 : mapped m3 (h_sp H - PARSE_STACK) PARSE_STACK).
    { eapply (window_mapped LayoutPU m3 lo (h_sp H + -208) (h_sp H) PARSE_STACK); [exact ST3| exact FR3| cbn; lia| exact CEIL| unfold PARSE_STACK, DOINCL_STACK, REALLOC_STACK; olia LOP| unfold PARSE_STACK, DOINCL_STACK, REALLOC_STACK; olia LOP]. }
    (* [comment removed for export] *)
    eapply (parse_from_head E x0 A1 m3 md1 T); [exact PE| exact PI0| exact AINV3| subst x0; cbn [x_st]; discriminate
      | subst x0; unfold pe_e, pe_N; cbn [x_p pe_DATA pe_inp E]; olia DLEN|].
    (* [comment removed for export] *)
    unfold ret_K. intros x2 A2 m4 md2 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 PI2 AINV2 MDF2 HS2 PEQ2 VEQ2 STK4.
    unfold ret_ms. cbn [pe_ra pe_H pe_gp pe_s0 pe_s1 pe_s2 pe_s3 pe_s4 pe_s5 pe_s6 pe_s7 pe_s8 pe_s9 pe_s10 pe_s11 E].
    unfold pe_e, pe_N in PEQ2, VEQ2. cbn [pe_DATA pe_inp pe_lo pe_H E] in PEQ2, VEQ2, STK4.
    pose proof (ocosts_nonneg _ _ _ _ PI2) as [OA2 OI2].
    pose proof PI2 as PI2c.
    destruct PI2c as [VEPO2 BASE2 FLG2 VSBF2 STUP2 STATE2 CNT2 VERP2 PLE2 B012 TAGI2 DELIM2 ESIC2 UNTL2 MTCH2 DOST2 ARMED2 ATTR2 ATTRST2
                      MATTR2 LOOKA2 LOOKM2 VSBO2 ROOM2 OUT2 APART2 WAL2 AVSB2 VA2 VI2 DATA4 HENV4 IMG4 STK4' FRAME4 MI4 LB2 NL2].
    cbn [pe_VEP pe_S pe_H pe_DATA pe_flags pe_wa pe_lo pe_inp E] in VEPO2, BASE2, FLG2, VSBF2, CNT2, VERP2, PLE2, VSBO2, OUT2, APART2, WAL2, VA2, VI2, DATA4, HENV4.
    unfold va_world in VA2. unfold vi_world in VI2. cbn [pe_VEP pe_S pe_H pe_DATA pe_flags pe_wa pe_lo pe_inp E] in VA2, VI2.
    rewrite VEQ2 in CNT2. replace (DATA + Z.of_nat (length inp) - DATA) with (Z.of_nat (length inp)) in CNT2 by lia.
    (first [ dand3 HS2 as HL2 HN2 HC2 | destruct HS2 as (HL2 & HN2 & HC2) ]).
    assert (LVV : 0 <= vb_len (x_vv x2)) by ((first [ dand3 VSBO2 as _ VIx _ | destruct VSBO2 as (_ & VIx & _) ]); unfold vsb_inv in VIx; olia VIx).
    eapply (K u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 A2 m4 md2 (x_v x2) (x_tag x2) (x_q x2) (x_vv x2) (x_va x2)
              (option_map (fun y => (y, true)) (x_vi x2)) (Z.of_nat (length inp))).
    - exact AINV2.
    - exact MI4.
    - eapply md_frame_trans; [exact MDF| exact MDF2].
    - exact STK4.
    - exact HENV4.
    - exact IMG4.
    - (* [comment removed for export] *)
      unfold parsed_world. pose proof CNT2 as CNT2'. unfold vep_cnt in CNT2'.
      split; [exact VEPO2|]. split; [exact BASE2|]. split; [exists (x_st x2); exact STATE2|].
      split; [exact (proj1 B012)|]. split; [exact (proj1 (proj2 B012))|].
      split; [exact CNT2|]. split; [olia DLEN|]. split; [unfold NMAX; olia DLEN|]. split; [rewrite VEQ2; olia Dlo Dhi DLEN|].
      split; [rewrite VSBF2; exact VSBO2|].
      split; [split; [exact ROOM2| unfold world_len; revert OUT2 OA2 OI2 CNT2' PEQ2; clear; unfold oacost, oicost;
                                   destruct (x_va x2); destruct (x_vi x2); cbn [option_map]; intros; destruct (x_st x2); lia]|].
      split; [rewrite VSBF2; intros y Hy; apply APART2; revert Hy; clear; cbn [In]; tauto|].
      split.
      + destruct (x_va x2) as [ya|] eqn:EVA; [|exact VA2]. (first [ dand4 VA2 as ANZ AO ASZ AAP | destruct VA2 as (ANZ & AO & ASZ & AAP) ]).
        unfold oacost, oicost in OUT2. rewrite EVA in OUT2.
        split; [exact AO|]. split; [unfold EXT_MAX; revert ASZ OUT2 OI2 CNT2' PEQ2 DLEN LVV; clear; unfold oicost; intros; destruct (x_vi x2); destruct (x_st x2); lia|].
        split; [exact ASZ|].
        rewrite VSBF2. intros y Hy; apply AAP; revert Hy; clear; cbn [In]; tauto.
      + destruct (x_vi x2) as [yi|] eqn:EVI; cbn [option_map]; [|exact VI2]. (first [ dand6 VI2 as INZ IO IERR ISZ IAP IAP2 | destruct VI2 as (INZ & IO & IERR & ISZ & IAP & IAP2) ]).
        split; [exact IO|]. split; [exact ISZ|]. split; [rewrite VSBF2; intros y Hy; apply IAP; revert Hy; clear; cbn [In]; tauto|].
        destruct (x_va x2) as [ya|]; [exact IAP2| exact I].
    - exact VSBF2.
    - rewrite VEQ2. olia DLEN.
    - (* [comment removed for export] *)
      (first [ pose proof ((live_geom LayoutPU _ _ _ _ _ AINV1 LWA1)) as dR_21; dand5 dR_21 as _ _ _ Whi1 _ | pose proof (live_geom LayoutPU _ _ _ _ _ AINV1 LWA1) as (_ & _ & _ & Whi1 & _) ]).
      (first [ pose proof ((live_geom LayoutPU _ _ _ _ _ AINV1 LVS1)) as dR_22; dand5 dR_22 as _ _ _ Shi1 _ | pose proof (live_geom LayoutPU _ _ _ _ _ AINV1 LVS1) as (_ & _ & _ & Shi1 & _) ]).
      (first [ pose proof ((live_geom LayoutPU _ _ _ _ _ AINV1 LVB1)) as dR_23; dand5 dR_23 as _ _ _ Bhi1 _ | pose proof (live_geom LayoutPU _ _ _ _ _ AINV1 LVB1) as (_ & _ & _ & Bhi1 & _) ]).
      pose proof (as_live_disjoint _ _ _ _ _ _ _ AINV1 LVEP1 LWA1 NE_Vw) as DJW1.
      pose proof (as_live_disjoint _ _ _ _ _ _ _ AINV1 LVS1 LWA1 (not_eq_sym NE_wS)) as DJW2.
      pose proof (as_live_disjoint _ _ _ _ _ _ _ AINV1 LVB1 LWA1 (not_eq_sym NB_W)) as DJW3.
      assert (WS1_3 : ws1_obj LayoutPU H A1 m3 wa VEP).
      { eapply (ws1_obj_munch LayoutPU); [exact WS1_2| exact MU| exact WM|]. intros a Ha. unfold h_ws, h_wsbuf in Ha. cbn [outside]. olia Ha VEPhi Whi1 G2 CV DJW1. }
      eapply (ws1_obj_ccall LayoutPU H A1 A2 m3 md1 m4 (h_sp H) PARSE_STACK); [exact AINV3| exact HC2| exact HG| exact WS1_3| apply Z.le_refl
        | unfold PARSE_STACK, DOINCL_STACK, REALLOC_STACK; olia LOP CEIL| exact WAL2| exact (proj1 VEPO2)|].
      intros a Ha. unfold pzone; subst x0 v2; cbn [x_vv x_va x_vi x_v pe_VEP pe_S pe_H E]. unfold blk, h_vsc. unfold h_ws, h_wsbuf in Ha.
      olia Ha VEPhi Whi1 Shi1 Bhi1 G2 CV DJW1 DJW2 DJW3.
    - exact DATA4.
    - (* [comment removed for export] *)
      intros p k Hp Nb.
      assert (NBp : p <> vb_buf vv1) by (unhide REL; eapply (fresh_ne A A1 b); [exact REL| exact Hp| exact Nb]).
      apply HL2; [unhide LIVE1; rewrite (LIVE1 p Nb NBp); exact Hp|].
      subst x0; unfold pst_blocks; cbn [x_vv x_va x_vi x_v]. intros [X|[X|X]]; [exact (NBp X)| exact X| exact X].
    - (* [comment removed for export] *)
      intros x Hx.
      assert (PB : pst_blocks x2 x).
      { unfold pst_blocks. unfold parse_blocks in Hx. revert Hx. clear. destruct (x_va x2); destruct (x_vi x2); cbn [option_map]; intros Hx; tauto. }
      destruct (HN2 x PB) as [P0 | D0].
      + subst x0; unfold pst_blocks in P0; cbn [x_vv x_va x_vi x_v] in P0. destruct P0 as [->|[[]|[]]].
        unhide REL. destruct REL as [EB|[F1 _]]; [left; exact EB| right; exact F1].
      + destruct (Z.eq_dec x b) as [->|NXb]; [left; reflexivity| right].
        destruct (Z.eq_dec x (vb_buf vv1)) as [->|NXv].
        * unhide REL. destruct REL as [EB|[F1 _]]; [exfalso; exact (NXb EB)| exact F1].
        * unhide LIVE1. rewrite <- (LIVE1 x NXb NXv). exact D0.
    - (* [comment removed for export] *)
      rewrite pw_bytes_world. cbn [pe_LB0 E] in LB2. exact LB2.
    - rewrite pw_nlive_world. cbn [pe_NL0 E] in NL2. exact NL2.
    - (* [comment removed for export] *)
      unhide CF1. unhide FRm1.
      assert (C_a : cframe LayoutPU (owned A) (owned A) (h_sp H) PARSE_STACK (parse_changed H VEP S b) nowhere m m1).
      { eapply (cframe_stores LayoutPU _ _ _ _ m m1); [exact MU0| | exact MAP1].
        intros a Ha NO. cbn [outside] in NO. unfold parse_changed, blk.
        destruct (Classical_Prop.classic (h_sp H + -208 <= a < h_sp H)) as [X|X]; [left; unfold PARSE_STACK, DOINCL_STACK, REALLOC_STACK; olia X|].
        right; left. olia Ha NO X VEPlo. }
      assert (C_b : cframe LayoutPU (owned A) (owned A1) (h_sp H) PARSE_STACK
                      (fun a => blk VEP 312 a \/ blk b 16 a \/ S <= a < S + 40) (blk (vb_buf vv1) (vb_size vv1)) m1 m2).
      { eapply (cframe_reframe LayoutPU); [exact CF1| clear - CV; unfold_stacks_g; lia| clear - CV; lia| exact MAP2]. }
      assert (C_ab : cframe LayoutPU (owned A) (owned A1) (h_sp H) PARSE_STACK (parse_changed H VEP S b) (blk (vb_buf vv1) (vb_size vv1)) m m2).
      { eapply (cframe_seq LayoutPU _ _ _ _ _ _ _ _ _ _ _ _ _ m m1 m2 C_a C_b); [apply Z.le_refl| apply Z.le_refl| exact MAP2| intros a X; exact X| |].
        - intros a [X|[X|X]]; right; unfold parse_changed; [left; exact X| right; right; left; exact X| right; left; split; [exact NS0| exact X]].
        - intros a X; right; left; exact X. }
      assert (C_c : cframe LayoutPU (owned A1) (owned A1) (h_sp H) PARSE_STACK (parse_changed H VEP S b) nowhere m2 m3).
      { eapply (cframe_stores LayoutPU _ _ _ _ m2 m3); [exact MU| | exact MAP3].
        intros a Ha NO. cbn [outside] in NO. unfold parse_changed, blk.
        destruct (Classical_Prop.classic (h_sp H + -176 <= a < h_sp H + -104)) as [X|X]; [left; unfold PARSE_STACK, DOINCL_STACK, REALLOC_STACK; olia X|].
        right; left. olia Ha NO X VEPlo. }
      assert (C_abc : cframe LayoutPU (owned A) (owned A1) (h_sp H) PARSE_STACK (parse_changed H VEP S b) (blk (vb_buf vv1) (vb_size vv1)) m m3).
      { eapply (cframe_seq LayoutPU _ _ _ _ _ _ _ _ _ _ _ _ _ m m2 m3 C_ab C_c); [apply Z.le_refl| apply Z.le_refl| exact MAP3| intros a X; exact X| intros a X; right; exact X| intros a X; left; exact X]. }
      eapply (cframe_seq LayoutPU _ _ _ _ _ _ _ _ _ _ _ _ _ m m3 m4 C_abc HC2); [apply Z.le_refl| apply Z.le_refl| exact (proj1 (proj2 HC2))| intros a X; exact X| |].
      + intros a Z1. subst x0 v2; unfold pzone in Z1; cbn [x_vv x_va x_vi x_v pe_VEP pe_S pe_H E] in Z1.
        unfold parse_changed. destruct Z1 as [Z1|[Z1|[Z1|[Z1|[Z1|Z1]]]]].
        * right; left; exact Z1.
        * right; right; left. split; [exact NS0| exact Z1].
        * left; exact Z1.
        * destruct Z1.
        * destruct Z1.
        * right; right; right; right. exact Z1.
      + intros a X. right; left. exact X.
  Qed.
End S.

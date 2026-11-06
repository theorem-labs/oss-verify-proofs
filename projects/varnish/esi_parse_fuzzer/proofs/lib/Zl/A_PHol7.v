(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j AIcpghc AIcpya4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.

Module A_PH8ea.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j AIcpghc AIcpya4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PMark.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
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
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Ltac show_left := match goal with |- ?G => idtac "LEFTOVER:" G end.
Local Tactic Notation "klia" ne_hyp_list(hs) := try (generalize alloc_ceiling_val); clear - hs; try pose proof alloc_ceiling_val; lia.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HDIT : vep_do_include_tag_stmt.

  Section X.
    Variables (E : penv) (x : pst) (T : TSet).
    Hypothesis PE : penv_ok E.
    Hypothesis PHI : phi E x = 16 * (pe_e E - x_p x) + 5.
    Hypothesis KL : latch_K E x T.

    Let LNX : word := Z_to_bv 64 142560.   (* [comment removed for export] *)

    (* [comment removed for export] *)
    #[using="KL PHI PE"] Lemma intag_tail : forall (d : Z) (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
        (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word),
      pinvg d E xc Ac (aview Ac mc) (* [comment removed for export] *) -> 0 <= d <= ptag xc -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
      (x_st xc = S_InTag \/ x_st xc = S_TagError) -> x_v xc Fattr_vsb = 0 -> x_p x < x_p xc ->
      srealizes rsegs (mkCfg (call_ms E 0x8cab4 (x_p xc) ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 LNX s10 s11 t3 t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc DB AINVc MDFc STc AV0 LT.
      clear - PE PHI KL PIc DB AINVc MDFc STc AV0 LT; try pose proof alloc_ceiling_val.
      assert (EVA : x_va xc = None).
      { pose proof (pi_va _ _ _ _ PIc) as VA. unfold va_world in VA. revert VA AV0. clear. destruct (x_va xc); [| reflexivity]. intros VA AV0. exfalso. exact (proj1 VA AV0). }
      world_open PE PIc AINVc. unfold call_ms, S9. cbv zeta. rewrite EFP in *.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview Ac mc)) as MU. pose proof (wmono_refl rsegs (aview Ac mc)) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (CFP : client_fp LPA Ac (aview Ac mc) [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      hide_neqs.
      ago AINVc. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0. zstep.
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 2. zstep. zstep.
      astop AINVc MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p xc) S_NxtTag (fupd (fupd (x_v xc) Fin_esi_tag 0) Fstate (vi_st VIA S_NxtTag)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) Ac _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINVc HFR MU WM WZ. all: show_left.
        all: first [ split; [intros _; apply DELIM1; destruct STc as [X|X]; rewrite X; discriminate | intros X; discriminate X]
                   | intros X; exfalso; exact (X AV0)
                   | cf_stores CF MU PE0 STK FR; left; left; unfold blk; lia
                   | revert OUT; destruct STc as [X|X]; rewrite X; clear; cbv [oacost oicost x_va x_vi]; intros; lia ].
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDFc | exact SBM].
      - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LT; try pose proof alloc_ceiling_val. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HDIT"] Lemma intag_do_include : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
        (t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word),
      pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
      x_st xc = S_InTag -> x_p x < x_p xc -> x_v xc Flast_mark = 1 ->
      srealizes rsegs (mkCfg (call_ms E vep_do_include_entry (x_p xc) (Z_to_bv 64 0x8cab4) t0 t1 t2 s1
                                 (Z_to_bv 64 (pe_VEP E)) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 LNX s10 s11 t3 t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc AINVc MDFc STc LT LM.
      pose proof PIc as PIc0. (first [ pose proof ((pinv_sizes _ _ _ _ PIc)) as dR_1; dand4 dR_1 as OUT' WBB LEN0 SZ0 | pose proof (pinv_sizes _ _ _ _ PIc) as (OUT' & WBB & LEN0 & SZ0) ]). (first [ pose proof ((pinv_seccred _ _ _ _ PIc)) as dR_2; dand3 dR_2 as SCB SCN SC15 | pose proof (pinv_seccred _ _ _ _ PIc) as (SCB & SCN & SC15) ]). pose proof (pinv_primcred _ _ _ _ PIc) as (PCB & PCD & PCR).   (* [comment removed for export] *)
      world_open PE PIc AINVc. unfold call_ms, S9. cbv zeta. rewrite EFP in *.
      assert (AV0 : x_v xc Fattr_vsb = 0).
      { destruct (Z.eq_dec (x_v xc Fattr_vsb) 0) as [X|X]; [exact X| exfalso; exact (AVSB X)]. }
      assert (EVA : x_va xc = None).
      { revert VA AV0. clear. destruct (x_va xc); [| reflexivity]. intros VA AV0. exfalso. exact (proj1 VA AV0). }
      rewrite EVA in *. unfold oabuf in *. rewrite EVA in *. unfold oacost, oicost in OUT. rewrite EVA in OUT. cbv beta iota in OUT.
      unfold PARSE_LIVE, pe_N in BUDL. unfold PARSE_NLIVE in BUDN.
      assert (EDS : DOINCL_STACK = 8784) by (vm_compute; reflexivity).
      (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINVc LVS)) as dR_3; dand4 dR_3 as _ _ Slo _ | destruct (live_geomP LPA _ _ _ _ _ AINVc LVS) as (_ & _ & Slo & _) ]). unfold kHighMemBeg in Slo. all_app_facts.
      pose proof (vsb_extendsize_tight (vb_size (x_vv xc) + match x_vi xc with Some yi => vb_len yi | None => 0 end + 9)) as EXT.
      assert (IB : match x_vi xc with Some yi => 0 <= vb_len yi <= vb_size yi | None => True end).
      { clear - VI; try pose proof alloc_ceiling_val. destruct (x_vi xc) as [yi|]; [| exact I]. (first [ dand3 VI as _ IO _ | destruct VI as (_ & IO & _) ]). (first [ pose proof (IO) as dR_5; dand3 dR_5 as _ VIi _ | pose proof IO as (_ & VIi & _) ]). unfold vsb_inv in VIi. lia. }
      eapply (HDIT (pe_VEP E) (x_v xc) (x_tag xc) (x_q xc) (x_vv xc) (x_vi xc) (pe_H E) (pe_lo E) (pe_SB E) (pe_NS E)
                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc mdc Ac T);
        [ exact AINVc | exact MI | reflexivity | reflexivity
        | exact (pi_vep _ _ _ _ PIc0) | exact BASE | exact HENV
        | rewrite FLG; exact FL | exact B_em | exact B_ic | exact LM | exact AV0
        | rewrite VSBF; exact VSBO | rewrite VSBF; exact NE1 | exact D_VB
        | exact ROOM
        | revert OUT CNT VERP PLE NN DLEN EE IB; unfold vep_cnt, NMAX; clear; destruct (x_vi xc); intros; lia
        | revert LB BUDL OUT CNT VERP PLE NN ROOM IB VI; unfold world_bytes, x_vio, vep_cnt, NMAX; clear; destruct (x_vi xc) as [yi|]; cbn [option_map];
          [(intros LB BUDL OUT CNT VERP PLE NN ROOM IB; (first [ intro dR_15; dand5 dR_15 as _ _ _ ISZ _ | intros (_ & _ & _ & ISZ & _) ])) | intros]; lia
        | revert NL BUDN; unfold world_nlive, x_vio; clear; destruct (x_vi xc); cbn [option_map]; intros; lia
        | revert SCB SC15 OUT CNT VERP PLE CR0 LEN0 VI; unfold vep_cnt, pe_N, PARSE_CRED; clear; destruct (x_vi xc) as [yi|];
          [ (intros SCB SC15 OUT CNT VERP PLE CR0 LEN0; (first [ intro dR_16; dand3 dR_16 as _ IO _ | intros (_ & IO & _) ])); (first [ pose proof (IO) as dR_6; dand3 dR_6 as _ VIi _ | pose proof IO as (_ & VIi & _) ]); unfold vsb_inv in VIi;
            pose proof (div4096_add (vb_len (x_vv xc) + (x_p xc - pe_DATA E) + 4096) (vb_len yi) ltac:(try (generalize alloc_ceiling_val); clear - LEN0 VERP; try pose proof alloc_ceiling_val; lia) ltac:(try (generalize alloc_ceiling_val); clear - VIi; try pose proof alloc_ceiling_val; lia)) as DA;
            assert (T8 : (vb_len (x_vv xc) + (x_p xc - pe_DATA E) + 4096 + vb_len yi) / 4096 <= Z.of_nat (length (pe_inp E)) / 682 + 1)
              by (try (generalize alloc_ceiling_val); clear - OUT CNT VERP PLE VIi; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia);
            try (generalize alloc_ceiling_val); clear - SCB DA T8 CR0; try pose proof alloc_ceiling_val; lia
          | intros; lia ]
        | exact PCD (* [comment removed for export] *)
        | eapply frames_same_lib; [exact FRS| exact LIBF]   (* [comment removed for export] *)
        | clear - VI D_IV D_IBV D_IS D_IBS D_IB D_IBB VSBF; try pose proof alloc_ceiling_val; unfold oibuf in *; rewrite ?VSBF;
          destruct (x_vi xc) as [yi|]; [| exact VI]; (first [ dand5 VI as Q1 Q2 Q3 Q4 Q5 | destruct VI as (Q1 & Q2 & Q3 & Q4 & Q5) ]);
          exact (conj Q1 (conj Q2 (conj Q3 (conj D_IV (conj D_IBV (conj D_IS (conj D_IB (conj D_IBS D_IBB))))))))
        | reflexivity
        | rewrite unsigned_lit by (klia FRB); rewrite Zminus_mod, SP16; reflexivity
        | rewrite unsigned_lit by (klia FRB); exact STK
        | exact CEIL
        | rewrite unsigned_lit by (klia FRB); rewrite EDS; klia LOP
        | rewrite unsigned_lit by (klia FRB); rewrite EDS; eapply (stack_shadow_sub LPA); [exact SS| rewrite PARSE_STACK_val; clear; lia| clear; lia| rewrite PARSE_STACK_val; klia LOP CEIL ACV]
        | ].
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' vv' vr'. cbv zeta.
      intros AINV1 MI1 MDF1 ST1 HENV1 VEPO1 VK VST IC1 IS1 VSBO1 LEN1 SZ1 REL LIVE1 FA1 TC1 SCC1 PCC1 CF1.   (* [comment removed for export] *)
      rewrite unsigned_lit in ST1, CF1 by (klia FRB). rewrite EDS in CF1. rewrite VSBF in VSBO1, CF1. try rewrite VSBF in LIVE1.
      replace (ret_pc (Z_to_bv 64 0x8cab4)) with (Z_to_bv 64 0x8cab4) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      (* [comment removed for export] *)
      set (v3 := fupd (fupd (fupd (x_v xc) Fstate (vv' Fstate)) Finclude_src 0) Finclude_continue (vv' Finclude_continue)).
      assert (EQF : forall f, vv' f = v3 f).
      { intros f. subst v3. destruct f; cbn [fupd vf_beq vf_index N.eqb Pos.eqb];
          first [ reflexivity | exact IS1 | (apply VK; clear; cbv; intros [X|[X|[X|[]]]]; discriminate X) ]. }
      assert (VEPO3 : vep_obj LPA A' (aview A' m') (pe_VEP E) v3 (x_tag xc) (x_q xc)).
      { (first [ dand4 VEPO1 as L1 C1 T1 P1 | destruct VEPO1 as (L1 & C1 & T1 & P1) ]). split; [exact L1|]. split; [| exact (conj T1 P1)].
        unfold vep_cells in C1 |- *. rewrite !EQF in C1. exact C1. }
      pose proof (proj1 VEPO3) as LVEP1.
      (* [comment removed for export] *)
      set (Vi := fun a : Z => blk (pe_VEP E) 312 a \/ newblk (vb_buf (x_vv xc)) (vb_size (x_vv xc)) a \/ (pe_S E <= a < pe_S E + 40)
                           \/ match x_vi xc with Some yi => vsb_blocks (x_v xc Finclude_src) yi a | None => False end
                           \/ (h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320)) in CF1.
      assert (CV1 : vcover (pe_H E) Ac [pe_DATA E] Vi).
      { intros a [X|[X|[X|[X|X]]]].
        - eapply cover_blk; [exact LVEP| wz_not_in| exact X].
        - eapply cover_newblk; [exact LVB| wz_not_in| exact X].
        - eapply cover_rng; [exact LVS| wz_not_in| exact X].
        - clear - X VI D_ID D_IBD; try pose proof alloc_ceiling_val. unfold oibuf in *. destruct (x_vi xc) as [yi|]; [| destruct X].
          (first [ dand3 VI as _ IO _ | destruct VI as (_ & IO & _) ]). (first [ pose proof (IO) as dR_10; dand5 dR_10 as _ _ LIS LIB _ | pose proof IO as (_ & _ & LIS & LIB & _) ]).
          destruct X as [X|X]; [eapply cover_newblk; [exact LIS| wz_not_in| exact X] | eapply cover_newblk; [exact LIB| wz_not_in| exact X]].
        - apply cover_vsc. exact X. }
      assert (WIN : alloc_ceiling <= pe_sp E - 320 - 8784) by (klia LOP CEIL).
      assert (W0 : 0 <= 8784) by (clear; lia).
      (* [comment removed for export] *)
      assert (LK : forall p k, a_live Ac p = Some k -> p <> vb_buf (x_vv xc) ->
                   ~ (match x_vi xc with Some yi => p = x_v xc Finclude_src \/ p = vb_buf yi | None => False end) ->
                   a_live A' p = Some k).
      { intros p k Hp NB NI. clear - Hp NB NI LIVE1 REL; try pose proof alloc_ceiling_val.
        assert (NB' : p <> vb_buf vr') by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact Hp| exact NB]).
        destruct (x_vi xc) as [yi|].
        - (first [ dand4 LIVE1 as _ _ LQ _ | destruct LIVE1 as (_ & _ & LQ & _) ]). rewrite (LQ p NB NB'); [exact Hp| |]; intros ->; apply NI; [left| right]; reflexivity.
        - destruct LIVE1 as (LQ & _). rewrite (LQ p). exact Hp. }
      assert (LDATA1 : a_live A' (pe_DATA E) = Some (Z.of_nat (length (pe_inp E)))).
      { apply LK; [exact LDATA| exact (not_eq_sym D_BD)|]. clear - D_ID D_IBD; try pose proof alloc_ceiling_val. unfold oibuf in *. destruct (x_vi xc); [| intros X; exact X].
        intros [X|X]; [exact (D_ID (eq_sym X))| exact (D_IBD (eq_sym X))]. }
      assert (WAL1 : a_live A' (pe_wa E) = Some 40).
      { apply LK; [exact WAL| exact D_WB|]. clear - D_IW D_IBW; try pose proof alloc_ceiling_val. unfold oibuf in *. destruct (x_vi xc); [| intros X; exact X].
        intros [X|X]; [exact (D_IW (eq_sym X))| exact (D_IBW (eq_sym X))]. }
      assert (NB_V : pe_VEP E <> vb_buf vr') by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LVEP| exact D_VB]).
      assert (NB_W : pe_wa E <> vb_buf vr') by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact WAL| exact D_WB]).
      assert (NB_D : pe_DATA E <> vb_buf vr') by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LDATA| exact (not_eq_sym D_BD)]).
      (* [comment removed for export] *)
      assert (FR1 : rw_cells rsegs (aview A' m') (pe_sp E - 320) (pframe E j0 j8)).
      { eapply (pframe_call E Ac A' mc mdc _ _ _ _ _ _ j0 j8);
          [exact PE| exact AINVc| exact CF1| exact HFR| exact WIN| exact W0| unfold pe_fp, PARSE_FRAME; klia WIN| exact CV1| unfold pframe; cbv zeta; exact FR]. }
      assert (DATA1 : data_obj LPA A' (aview A' m') (pe_DATA E) (pe_inp E)).
      { eapply (data_obj_call (pe_H E) Ac A' mc mdc _ _ _ _ _ _ AINVc CF1 HFR WIN); [exact CV1| in_list| exact LDATA1| exact DATA]. }
      assert (SS1 : stack_shadow LPA (aview A' m') (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64)).
      { eapply (stack_shadow_call (pe_H E) Ac A' mc mdc _ _ _ _ _ _ AINVc CF1 HFR WIN); [exact CV1| rewrite PARSE_STACK_val; klia LOP CEIL ACV| exact SS]. }
      pose proof (lib_frames_same Ac A' 1%nat 1%nat (frames_same_lib _ _ FRS LIBF) FA1) as FS1.
      (* [comment removed for export] *)
      assert (SZQ : match x_vi xc with None => vb_size vr' = vb_size (x_vv xc) | Some _ => True end).
      { clear - LIVE1 REL VSBO1 LVB; try pose proof alloc_ceiling_val. destruct (x_vi xc) as [yi|]; [exact I|]. destruct LIVE1 as (LQ & _).
        pose proof (proj1 (proj2 (proj2 (proj2 VSBO1)))) as LVB1. rewrite LQ in LVB1.
        destruct REL as [EB|[F1 F2]]; [rewrite EB in LVB1; rewrite LVB in LVB1; injection LVB1; lia| rewrite F1 in LVB1; discriminate LVB1]. }
      (* [comment removed for export] *)
      assert (STI : exists stI, vv' Fstate = vi_st VIA stI /\ (stI = S_InTag \/ stI = S_TagError)).
      { destruct VST as [X|X]; [exists S_InTag; rewrite X, STATE, STc; split; [reflexivity| left; reflexivity] | exists S_TagError; split; [exact X| right; reflexivity]]. }
      (first [ dex1 STI as stI; destruct STI as [ESTI STI] | dand3 STI as stI ESTI STI | destruct STI as (stI & ESTI & STI) ]).
      set (xI := PST (x_p xc) stI v3 (x_tag xc) (x_q xc) vr' None None).
      assert (PI1 : pinvg (Z.min 48 (ptag xI)) E xI A' (aview A' m')).   (* [comment removed for export] *)
      { subst xI. apply Build_pinvg; psimp.
        - exact VEPO3.
        - subst v3. unfold vep_base; psimp. unfold vep_base in BASE; exact BASE.
        - subst v3; psimp. exact FLG.
        - subst v3; psimp. exact VSBF.
        - subst v3; psimp. exact STUP.
        - subst v3; psimp. exact ESTI.
        - subst v3. unfold vep_cnt; psimp. unfold vep_cnt in CNT; exact CNT.
        - subst v3; psimp. exact VERP.
        - exact PLE.
        - subst v3; psimp. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | exact IC1].
        - subst v3; psimp. exact TAGI.
        - subst v3; psimp. split; [intros _; exact (DELIM1 ltac:(discriminate))| intros X; exfalso; destruct STI as [-> | ->]; discriminate X].
        - subst v3; psimp. exact ESIC.
        - intros X; exfalso; destruct STI as [-> | ->]; discriminate X.
        - intros X; exfalso; destruct STI as [-> | ->]; discriminate X.
        - subst v3; psimp. exact DOST.
        - subst v3; psimp. destruct STI as [-> | ->]; [exact ARMED| intros X; destruct X].
        - subst v3; psimp. destruct ATTR as [X|(X1 & X2 & X3)]; [left; exact X| right; refine (conj X1 (conj X2 _))].
          destruct STI as [-> | ->]; [left; exact I| right; left; reflexivity].
        - destruct STI as [-> | ->]; intros X; destruct X.
        - intros X; exfalso; destruct STI as [-> | ->]; discriminate X.
        - intros X; exfalso; destruct STI as [-> | ->]; discriminate X.
        - intros X; exfalso; destruct STI as [-> | ->]; discriminate X.
        - exact VSBO1.
        - klia SZ1 ROOM LEN1.
        - subst v3; psimp. unfold oacost, oicost. cbn [x_va x_vi]. revert OUT LEN1 IB STI. clear. intros OUT LEN1 IB [-> | ->]; destruct (x_vi xc); cbv beta iota in *; lia.
        - intros y Hy. split; [apply (proj1 (APART y Hy))|].
          cbn in Hy. destruct Hy as [<-|[<-|[<-|[]]]]; apply not_eq_sym; [exact NB_V| exact NB_W| exact NB_D].
        - exact WAL1.
        - subst v3; psimp. intros X. exfalso. exact (X AV0).
        - subst v3; psimp. exact AV0.
        - subst v3; psimp. reflexivity.
        - exact DATA1.
        - exact HENV1.
        - rewrite EFP. exact ST1.
        - exists j0, j8. rewrite EFP. exact FR1.
        - exact MI1.
        - exact SS1.
        - revert LB LIVE1 SZQ. clear. unfold world_bytes, x_vio. destruct (x_vi xc); cbn [option_map]; intros; lia.
        - revert NL LIVE1. clear. unfold world_nlive, x_vio. destruct (x_vi xc); cbn [option_map]; intros; lia.
        - rewrite TC1. exact TC.
        - intros ff. rewrite (FS1 ff). apply FRS.
        - intros p k Lp NBp. pose proof (KEEP p k Lp NBp) as LA. apply LK; [exact LA| |].
          + intros ->. destruct (NEW (vb_buf (x_vv xc)) ltac:(unfold parse_blocks; left; reflexivity)) as [EQ|EQ]; [exact (NBp EQ)| rewrite EQ in Lp; discriminate Lp].
          + clear - NEW Lp NBp; try pose proof alloc_ceiling_val. unfold x_vio in NEW. destruct (x_vi xc) as [yi|]; [| intros X; exact X].
            intros [-> | ->].
            * destruct (NEW (x_v xc Finclude_src) ltac:(unfold parse_blocks; cbn [option_map]; right; right; left; reflexivity)) as [EQ|EQ]; [exact (NBp EQ)| rewrite EQ in Lp; discriminate Lp].
            * destruct (NEW (vb_buf yi) ltac:(unfold parse_blocks; cbn [option_map]; right; right; right; reflexivity)) as [EQ|EQ]; [exact (NBp EQ)| rewrite EQ in Lp; discriminate Lp].
        - subst v3. intros p Hp. unfold parse_blocks in Hp. cbn [option_map] in Hp. destruct Hp as [Hp|[Hp|Hp]]; [| destruct Hp| destruct Hp].
          subst p. destruct REL as [EQ|[E1 E2]].
          + rewrite EQ. apply NEW. unfold parse_blocks. left. reflexivity.
          + destruct (Z.eq_dec (vb_buf vr') (pe_b E)) as [EQ|NEQ]; [left; exact EQ| right].
            destruct (a_live (pe_A0 E) (vb_buf vr')) as [k|] eqn:EK; [| reflexivity].
            pose proof (KEEP _ _ EK NEQ) as LA. rewrite LA in E1. discriminate E1.
        - eapply (cframe_step_call E xc (PST (x_p xc) stI v3 (x_tag xc) (x_q xc) vr' None None) Ac A' _ _ (pe_sp E - 320) 8784);
            [ rewrite ?EVA; exact CF | exact CF1 | rewrite PARSE_STACK_val; klia W0 | klia W0
            | eapply parse_window_mapped; [exact PE| rewrite EFP; exact ST1| rewrite EFP; exact FR1]
            | intros a [Ha|[Ha|[Ha|[Ha|Ha]]]]; unfold pzone, parse_changed, parse_new;
              [ left; left; exact Ha | right; left; exact Ha | left; right; left; split; [klia Slo| exact Ha]
              | right; right; right; revert Ha; unfold x_vio; clear; destruct (x_vi xc); cbn [option_map]; intros Ha; exact Ha
              | left; right; right; right; exact Ha ]
            | intros a Ha; unfold parse_new in Ha; cbn [x_v x_vv x_va x_vi x_vio option_map] in Ha;
              destruct Ha as [Ha|[Ha|Ha]]; [left; exact Ha| destruct Ha| destruct Ha] ].
        - exact CR0.
        - klia VERP.
        - cbv beta iota in WL, SC.
          assert (PIL : match x_vi xc with Some yi => vsb_pot yi | None => 0 end
                        + (x_p xc - pe_DATA E - 0 - match x_vi xc with Some yi => vb_len yi | None => 0 end) / 4096
                        <= (x_p xc - pe_DATA E - 0 - 0) / 4096).
          { clear - VI WL; try pose proof alloc_ceiling_val. destruct (x_vi xc) as [yi|].
            - (first [ dand6 VI as _ IO _ ISZ ILEN _ | destruct VI as (_ & IO & _ & ISZ & ILEN & _) ]). (first [ pose proof (IO) as dR_14; dand3 dR_14 as _ VIi _ | pose proof IO as (_ & VIi & _) ]). unfold vsb_inv in VIi.
              pose proof (vsb_pot_len yi ISZ ltac:(lia) ltac:(lia)) as P1.
              pose proof (div4096_add (vb_len yi) (x_p xc - pe_DATA E - 0 - vb_len yi) ltac:(lia) ltac:(lia)) as P2.
              replace (vb_len yi + (x_p xc - pe_DATA E - 0 - vb_len yi)) with (x_p xc - pe_DATA E - 0 - 0) in P2 by lia. lia.
            - rewrite !Z.sub_0_r. lia. }
          revert SC SCC1 PIL. clear. intros; lia.
        - exact PR0.
        - split; exact I.
        - (* [comment removed for export] *)
          eapply (pc_xfer _ _ _ _ _ _ _ _ PC PCC1). destruct STI as [-> | ->]; subst v3; pc_arith. }
      eapply (intag_tail (Z.min 48 (ptag xI)) xI A'); [exact PI1| pose proof (ptag_range xI) as PTR; revert PTR; clear; intros; lia | exact AINV1| exact (amd_frame_trans _ _ _ MDFc MDF1)| subst xI; cbn [x_st]; exact STI| subst xI v3; psimp; exact AV0| subst xI; cbn [x_p]; exact LT].
    Qed.
  End X.
End S.
End A_PH8ea.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PHol7.A_PH8ea.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold vep_error_post, vep_do_remove_post, VEPERR_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@DBY]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
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
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@VEPlo; @TAG; @Dlo; @G2; @FRB; @WL; @LQ; @DLEN; @ACV; @VERP; @EE; @Hk; @KS; @LOP; @Ha; @DJfV; @NN; @CEIL; @H; @VEPhi; @PLTc; @SZ; @SR; @QE; @LQ'; @ACV__; @EVSC; @Ha__; @H4; @DJ_VD; @DJfD; @PLT; @VEP16; @H0; @K2; @KU; @BR; @SPH; @OUT; @K3; @EP1; @K0; @H2; @H3; @LT; @Dhi; @PLE; @VR; @EQ1; @H5; @DSR; @K1; @X])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
Ltac show_left := match goal with |- ?G => idtac "LEFTOVER:" G end.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.
  Hypothesis HVE : vep_error_stmt.
  Hypothesis HDC : vep_do_comment_stmt.
  Hypothesis HDR : vep_do_remove_stmt.
  Hypothesis HDIT : vep_do_include_tag_stmt.

  Section X.
    Variables (E : penv) (x : pst) (T : TSet).
    Hypothesis PE : penv_ok E.
    Hypothesis PHI : phi E x = 16 * (pe_e E - x_p x) + 5.
    Hypothesis KL : latch_K E x T.

    Let LNX : word := Z_to_bv 64 142560.   (* [comment removed for export] *)

    (* [comment removed for export] *)

    (* [comment removed for export] *)
    #[using="KL PHI PE HDC"] Lemma intag_do_comment : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
        (t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word),
      pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
      x_st xc = S_InTag -> x_p x < x_p xc ->
      srealizes rsegs (mkCfg (call_ms E vep_do_comment_entry (x_p xc) (Z_to_bv 64 0x8cab4) t0 t1 t2 s1
                                 (Z_to_bv 64 (pe_VEP E)) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 LNX s10 s11 t3 t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc AINVc MDFc STc LT.
      clear - HMC HVE HDC HDR PE PHI KL PIc AINVc MDFc STc LT; try pose proof alloc_ceiling_val as ACV__.
      world_open PE PIc AINVc. unfold call_ms, S9. cbv zeta. rewrite EFP in *.
      pose proof (munch_refl [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] (aview Ac mc)) as MU.
      pose proof (wmono_refl rsegs (aview Ac mc)) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
      assert (CFP : client_fp LPA Ac (aview Ac mc) [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      pose proof (cenv_intro Ac mc mdc AINVc) as CE. fold_aview.
      destruct HENV as (_ & GLOB & HOBJ & HSH).
      assert (SHVD : shadowed LPA (aview Ac mc) (pe_VEP E) 312).
      { exists (pe_VEP E), 312. split; [pose proof SHV0 as T__; rewrite EzsV in T__; exact T__|].
        split; [try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val as ACV__; Z.div_mod_to_equations; lia|]. try (generalize alloc_ceiling_val); clear - VEPlo VEPhi; try pose proof alloc_ceiling_val as ACV__. lia. }
      assert (KHV : kHighMemBeg <= pe_VEP E) by (unfold kHighMemBeg; try (generalize alloc_ceiling_val); clear - VEPlo; try pose proof alloc_ceiling_val as ACV__; lia).
      assert (M8V : pe_VEP E mod 8 = 0) by (try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val as ACV__; Z.div_mod_to_equations; lia).
      assert (DJV : h_ff (pe_H E) + HFSIZE <= pe_VEP E \/ pe_VEP E + 312 <= h_ff (pe_H E)) by (unhide_djf; unfold HFSIZE; try (generalize alloc_ceiling_val); clear - DJfV; try pose proof alloc_ceiling_val as ACV__; lia).
      assert (EVSC : h_vsc (pe_H E) = h_ff (pe_H E) + 32) by reflexivity. unfold kHighMemBeg in G2. all_app_facts.
      pose proof (sh_boundL (Clg:=Clg) (h_ff (pe_H E)) 8192 ltac:(try (generalize alloc_ceiling_val); clear -G2; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(clear; lia) G3) as SHFB. rewrite SHMAX_val in SHFB.
      hide_neqs.
      ago AINVc. fold_cl_segs.
      unhide DJfV.
      icall (HDC (pe_VEP E) (fupd (x_v xc) Fstate (stA (x_st xc))) (x_tag xc) (x_q xc) (pe_H E) (pe_lo E)) by
        (rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - FRB; try pose proof alloc_ceiling_val as ACV__; lia);
         first [ reflexivity | exact VEPC | exact TAG | exact PADS | exact B_em | exact (proj1 BASE) | exact GLOB | exact HOBJ | exact HSH | exact HG
               | exact CE | exact SHVD | exact KHV | exact M8V | exact VEPhi | exact DJV | exact STK | exact CEIL | exact MI
               | unfold VEPERR_STACK; try (generalize alloc_ceiling_val); clear - LOP; try pose proof alloc_ceiling_val as ACV__; lia ]).
      hide DJfV.
      lazymatch goal with X : glob_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into GLOB1 end.
      lazymatch goal with X : hobj_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into HOBJ1 end.
      lazymatch goal with X : stk _ ?v _ _ |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into STK end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV1 : henv_ok LPA VIA (pe_H E) Ac v)
          by (split; [exact HFR| split; [exact GLOB1| split; [exact HOBJ1|]]];
              eapply hshadow_munch; [exact HSH| exact MU| exact HG|];
              intros a__ Ha__; unfold HFSIZE in Ha__; change (8192 / 8) with 1024 in Ha__; cbn [outside]; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo LOP CEIL ACV EVSC G2; try pose proof alloc_ceiling_val as ACV__; lia);
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] v) as MU2; pose proof (wmono_refl rsegs v) as WM2
      end.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0. zstep.
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 2. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV2 : henv_ok LPA VIA (pe_H E) Ac v)
          by (eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold HOBJ_END, HFSIZE, h_cp in Ha__; change (8192 / 8) with 1024 in Ha__;
              cbn [outside]; unhide_djf; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo VEPhi ACV EVSC G2 DJfV; try pose proof alloc_ceiling_val as ACV__; lia)
      end.
      clear HENV1.
      astop AINVc MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p xc) S_NxtTag (fupd (fupd (x_v xc) Fin_esi_tag 0) Fstate (vi_st VIA S_NxtTag)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) Ac _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINVc HFR MU WM WZ.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha].
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDFc | exact SBM].
      - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LT; try pose proof alloc_ceiling_val as ACV__. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HDR"] Lemma intag_do_remove : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
        (t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word),
      pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
      x_st xc = S_InTag -> x_p x < x_p xc ->
      srealizes rsegs (mkCfg (call_ms E vep_do_remove_entry (x_p xc) (Z_to_bv 64 0x8cab4) t0 t1 t2 s1
                                 (Z_to_bv 64 (pe_VEP E)) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 LNX s10 s11 t3 t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc AINVc MDFc STc LT.
      clear - HMC HVE HDC HDR PE PHI KL PIc AINVc MDFc STc LT; try pose proof alloc_ceiling_val as ACV__.
      world_open PE PIc AINVc. unfold call_ms, S9. cbv zeta. rewrite EFP in *.
      pose proof (munch_refl [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] (aview Ac mc)) as MU.
      pose proof (wmono_refl rsegs (aview Ac mc)) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
      assert (CFP : client_fp LPA Ac (aview Ac mc) [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      pose proof (cenv_intro Ac mc mdc AINVc) as CE. fold_aview.
      destruct HENV as (_ & GLOB & HOBJ & HSH).
      assert (SHVD : shadowed LPA (aview Ac mc) (pe_VEP E) 312).
      { exists (pe_VEP E), 312. split; [pose proof SHV0 as T__; rewrite EzsV in T__; exact T__|].
        split; [try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val as ACV__; Z.div_mod_to_equations; lia|]. try (generalize alloc_ceiling_val); clear - VEPlo VEPhi; try pose proof alloc_ceiling_val as ACV__. lia. }
      assert (KHV : kHighMemBeg <= pe_VEP E) by (unfold kHighMemBeg; try (generalize alloc_ceiling_val); clear - VEPlo; try pose proof alloc_ceiling_val as ACV__; lia).
      assert (M8V : pe_VEP E mod 8 = 0) by (try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val as ACV__; Z.div_mod_to_equations; lia).
      assert (DJV : h_ff (pe_H E) + HFSIZE <= pe_VEP E \/ pe_VEP E + 312 <= h_ff (pe_H E)) by (unhide_djf; unfold HFSIZE; try (generalize alloc_ceiling_val); clear - DJfV; try pose proof alloc_ceiling_val as ACV__; lia).
      assert (EVSC : h_vsc (pe_H E) = h_ff (pe_H E) + 32) by reflexivity. unfold kHighMemBeg in G2. all_app_facts.
      pose proof (sh_boundL (Clg:=Clg) (h_ff (pe_H E)) 8192 ltac:(try (generalize alloc_ceiling_val); clear -G2; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(clear; lia) G3) as SHFB. rewrite SHMAX_val in SHFB.
      hide_neqs.
      ago AINVc. fold_cl_segs.
      unhide DJfV.
      try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_VEPC); icall (HDR (pe_VEP E) (fupd (x_v xc) Fstate (stA (x_st xc))) (x_tag xc) (x_q xc) (pe_H E) (pe_lo E)) by
        (rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - FRB; try pose proof alloc_ceiling_val as ACV__; lia);
         first [ reflexivity | exact VEPC | exact TAG | exact PADS | exact B_em | exact B_et | exact B_rm | exact (proj1 BASE) | exact GLOB | exact HOBJ | exact HSH | exact HG
               | exact CE | exact SHVD | exact KHV | exact M8V | exact VEPhi | exact DJV | exact STK | exact CEIL | exact MI
               | unfold VEPERR_STACK; try (generalize alloc_ceiling_val); clear - LOP; try pose proof alloc_ceiling_val as ACV__; lia ]).
      hide DJfV.
      lazymatch goal with X : glob_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into GLOB1 end.
      lazymatch goal with X : hobj_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into HOBJ1 end.
      lazymatch goal with X : stk _ ?v _ _ |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into STK end.
      lazymatch goal with X : rw_cells _ ?v (pe_VEP E) (vep_cells _ _ _) |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into VEPC end.
      lazymatch goal with X : bool01 ?r |- _ => first [constr_eq r (x_v xc Femptytag); fail | constr_eq r (x_v xc Fendtag); fail | constr_eq r (x_v xc Fremove); fail | rename X into RMB; rename r into rm] end.
      unfold vep_cells in VEPC. cbn [fupd vf_beq vf_index N.eqb Pos.eqb vi_st VIA stA] in VEPC.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV1 : henv_ok LPA VIA (pe_H E) Ac v)
          by (split; [exact HFR| split; [exact GLOB1| split; [exact HOBJ1|]]];
              eapply hshadow_munch; [exact HSH| exact MU| exact HG|];
              intros a__ Ha__; unfold HFSIZE in Ha__; change (8192 / 8) with 1024 in Ha__; cbn [outside]; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo VEPhi LOP CEIL ACV EVSC G2; try pose proof alloc_ceiling_val as ACV__; lia);
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] v) as MU2; pose proof (wmono_refl rsegs v) as WM2
      end.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0. zstep.
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 2. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV2 : henv_ok LPA VIA (pe_H E) Ac v)
          by (eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold HOBJ_END, HFSIZE, h_cp in Ha__; change (8192 / 8) with 1024 in Ha__;
              cbn [outside]; unhide_djf; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo VEPhi ACV EVSC G2 DJfV; try pose proof alloc_ceiling_val as ACV__; lia)
      end.
      clear HENV1.
      astop AINVc MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p xc) S_NxtTag (fupd (fupd (fupd (x_v xc) Fremove rm) Fin_esi_tag 0) Fstate (vi_st VIA S_NxtTag)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) Ac _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINVc HFR MU WM WZ.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha].
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDFc | exact SBM].
      - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LT; try pose proof alloc_ceiling_val as ACV__. lia.
    Qed.

    (* [comment removed for export] *)

    (* [comment removed for export] *)
    #[using="KL PHI PE HDIT HDR HDC HMC"] Lemma intag_gt : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
        (ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 s10 s11 t3 t4 t5 t6 : word),
      pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
      x_st xc = S_InTag -> x_p x <= x_p xc -> x_p xc < pe_e E ->
      srealizes rsegs (mkCfg (loop_ms E 0x8ca38 (x_p xc) ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 LNX s10 s11 t3 t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc AINVc MDFc STc LQ PLTc.
      clear - HMC HVE HDC HDR HDIT PE PHI KL PIc AINVc MDFc STc LQ PLTc; try pose proof alloc_ceiling_val as ACV__.
      pose proof (intag_do_include HDIT E x T PE PHI KL) as DOI.
      world_open PE PIc AINVc. unfold loop_ms, S9, T0. rewrite EFP in *.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview Ac mc)) as MU. pose proof (wmono_refl rsegs (aview Ac mc)) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (DSR : 0 <= x_v xc Fdostuff < 2^64 /\ x_v xc Fdostuff <> 0).
      { split; [| exact (ARMED I)]. clear - DOST; try pose proof alloc_ceiling_val as ACV__. destruct DOST as [-> |[-> |[-> | ->]]]; cbn; lia. }
      destruct DSR as [DSR DNZ].
      set (xg := PST (x_p xc + 1) S_InTag (x_v xc) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)).
      assert (PIg : pinv E xg Ac (aview Ac mc)).
      { subst xg. apply Build_pinv; psimp; pinv_close PE0 AINVc HFR MU WM WZ.
        - (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__. lia.
        - (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - PLTc; try pose proof alloc_ceiling_val as ACV__. unfold pe_e, pe_N in *. lia.
        - (* [comment removed for export] *) revert VA. clear. cbn [x_va x_v x_p x_vv]. destruct (x_va xc); [| intros X; exact X]. intros (H1 & H2 & H3 & H4 & H5). refine (conj H1 (conj H2 (conj H3 (conj _ H5)))). lia.
        - (* [comment removed for export] *) revert VI. clear. cbn [x_vi x_va x_v x_p x_vv]. destruct (x_vi xc); [| intros X; exact X]. intros (H1 & H2 & H3 & H4 & H5 & H6 & H7). refine (conj H1 (conj H2 (conj H3 (conj H4 (conj _ (conj H6 H7)))))). lia. }
      hide_neqs.
      ago AINVc. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KU; zify_cond KU.
      { exfalso. try (generalize alloc_ceiling_val); clear - KU PLTc Dhi EE ACV; try pose proof alloc_ceiling_val as ACV__. unfold pe_e, pe_N in *. rewrite ?unsigned_lit in KU by lia. lia. }
      clear KU.
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 8 0.
      zstep. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. apply DNZ. try (generalize alloc_ceiling_val); clear - K1 DSR; try pose proof alloc_ceiling_val as ACV__. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      astop0 AINVc.
      eapply (mark_call HMC E xg Ac _ _ T (x_p xc + 1) (x_p xc + 1) 1 0x8ca78);
        [ exact PE | exact PIg | assumption | eapply amd_frame_sbm_r; [exact MDFc | exact SBM]
        | subst xg; cbn [x_p]; clear; lia | try (generalize alloc_ceiling_val); clear - PLTc; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia | right; reflexivity | clear; lia | reflexivity
        | subst xg; cbn [x_st]; intros [X|X]; discriminate X | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (ST1 : x_st x1 = S_InTag) by (rewrite EX1; reflexivity).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EP1 : x_p x1 = x_p xc + 1) by (rewrite EX1; reflexivity).
      clear - HMC HVE HDC HDR HDIT PE PHI KL DOI PI1 AINV1 MDF1 VK LM1 ST1 EV1 EP1 LQ; try pose proof alloc_ceiling_val as ACV__.
      rewrite <- EV1 in LM1.
      world_open PE PI1 AINV1. unfold call_ms, S9. cbv zeta. rewrite EFP in *. rewrite <- EP1.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      assert (DSR : 0 <= x_v x1 Fdostuff < 2^64) by (clear - DOST; try pose proof alloc_ceiling_val as ACV__; destruct DOST as [-> |[-> |[-> | ->]]]; cbn; lia).
      hide_neqs.
      ago AINV1. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0. zstep. zstep. zstep.
      (* [comment removed for export] *)
      vrechk SHV0 EzsV (pe_VEP E + 272) 8 0. zstep. zstep. zstep.
      set (xd := PST (x_p x1) S_InTag (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)).
      (* [comment removed for export] *)
      pose proof DOST as DOST0.
      destruct DOST as [D0|[DI|[DR|DC]]]; [exfalso; exact (ARMED I D0)| | |].
      - rewrite DI. cbn [vi_do_include VIA]. zstep.
        astop AINV1 MU WM CFP. fold_cl_segs.
        lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PId : pinv E xd A1 (aview A1 mr)) end.
        { subst xd. apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
          (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
        eapply (DOI xd A1); [exact PId| assumption| eapply amd_frame_sbm_r; [exact MDF1 | exact SBM]| reflexivity
          | subst xd; cbn [x_p]; try (generalize alloc_ceiling_val); clear - LQ EP1; try pose proof alloc_ceiling_val as ACV__; lia| subst xd; psimp; exact LM1].
      - rewrite DR. cbn [vi_do_remove VIA]. zstep.
        astop AINV1 MU WM CFP. fold_cl_segs.
        lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PId : pinv E xd A1 (aview A1 mr)) end.
        { subst xd. apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
          (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
        eapply (intag_do_remove xd A1); [exact PId| assumption| eapply amd_frame_sbm_r; [exact MDF1 | exact SBM]| reflexivity
          | subst xd; cbn [x_p]; try (generalize alloc_ceiling_val); clear - LQ EP1; try pose proof alloc_ceiling_val as ACV__; lia].
      - rewrite DC. cbn [vi_do_comment VIA]. zstep.
        astop AINV1 MU WM CFP. fold_cl_segs.
        lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PId : pinv E xd A1 (aview A1 mr)) end.
        { subst xd. apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
          (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
        eapply (intag_do_comment xd A1); [exact PId| assumption| eapply amd_frame_sbm_r; [exact MDF1 | exact SBM]| reflexivity
          | subst xd; cbn [x_p]; try (generalize alloc_ceiling_val); clear - LQ EP1; try pose proof alloc_ceiling_val as ACV__; lia].
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HVE"] Lemma intag_err : forall (site : Z) (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
        (ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 s10 s11 t3 t4 t5 t6 : word),
      (site = 0x8cb00 \/ site = 0x8cd1c) ->
      pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
      x_st xc = S_InTag -> x_p x <= x_p xc -> x_p xc < pe_e E ->
      srealizes rsegs (mkCfg (loop_ms E site (x_p xc) ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 LNX s10 s11 t3 t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros SITE PIc AINVc MDFc STc LQ PLTc.
      clear - HMC HVE HDC HDR PE PHI KL SITE PIc AINVc MDFc STc LQ PLTc; try pose proof alloc_ceiling_val as ACV__.
      world_open PE PIc AINVc. unfold loop_ms, S9, T0. rewrite EFP in *.
      pose proof (munch_refl [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] (aview Ac mc)) as MU.
      pose proof (wmono_refl rsegs (aview Ac mc)) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
      assert (CFP : client_fp LPA Ac (aview Ac mc) [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      pose proof (cenv_intro Ac mc mdc AINVc) as CE. fold_aview.
      destruct HENV as (_ & GLOB & HOBJ & HSH).
      assert (SHVD : shadowed LPA (aview Ac mc) (pe_VEP E) 312).
      { exists (pe_VEP E), 312. split; [pose proof SHV0 as T__; rewrite EzsV in T__; exact T__|].
        split; [try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val as ACV__; Z.div_mod_to_equations; lia|]. try (generalize alloc_ceiling_val); clear - VEPlo VEPhi; try pose proof alloc_ceiling_val as ACV__. lia. }
      assert (KHV : kHighMemBeg <= pe_VEP E) by (unfold kHighMemBeg; try (generalize alloc_ceiling_val); clear - VEPlo; try pose proof alloc_ceiling_val as ACV__; lia).
      assert (M8V : pe_VEP E mod 8 = 0) by (try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val as ACV__; Z.div_mod_to_equations; lia).
      assert (DJV : h_ff (pe_H E) + HFSIZE <= pe_VEP E \/ pe_VEP E + 312 <= h_ff (pe_H E)) by (unhide_djf; unfold HFSIZE; try (generalize alloc_ceiling_val); clear - DJfV; try pose proof alloc_ceiling_val as ACV__; lia).
      assert (EVSC : h_vsc (pe_H E) = h_ff (pe_H E) + 32) by reflexivity. unfold kHighMemBeg in G2. all_app_facts.
      pose proof (sh_boundL (Clg:=Clg) (h_ff (pe_H E)) 8192 ltac:(try (generalize alloc_ceiling_val); clear -G2; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(clear; lia) G3) as SHFB. rewrite SHMAX_val in SHFB.
      hide_neqs.
      ago AINVc. fold_cl_segs.
      destruct SITE as [-> | ->].
      all: zstep; zstep; zstep; zstep.
      all: unhide DJfV.
      all: icall (HVE (pe_VEP E) (fupd (x_v xc) Fstate (stA (x_st xc))) (x_tag xc) (x_q xc) (pe_H E) (pe_lo E)) by
        (rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - FRB; try pose proof alloc_ceiling_val as ACV__; lia);
         first [ reflexivity | exact VEPC | exact TAG | exact PADS | exact (proj1 BASE) | exact GLOB | exact HOBJ | exact HSH | exact HG
               | exact CE | exact SHVD | exact KHV | exact M8V | exact VEPhi | exact DJV | exact STK | exact CEIL | exact MI
               | unfold VEPERR_STACK; try (generalize alloc_ceiling_val); clear - LOP; try pose proof alloc_ceiling_val as ACV__; lia ]).
      all: hide DJfV.
      all: lazymatch goal with X : glob_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into GLOB1 end.
      all: lazymatch goal with X : hobj_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into HOBJ1 end.
      all: lazymatch goal with X : stk _ ?v _ _ |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into STK end.
      all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV1 : henv_ok LPA VIA (pe_H E) Ac v)
          by (split; [exact HFR| split; [exact GLOB1| split; [exact HOBJ1|]]];
              eapply hshadow_munch; [exact HSH| exact MU| exact HG|];
              intros a__ Ha__; unfold HFSIZE in Ha__; change (8192 / 8) with 1024 in Ha__; cbn [outside]; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo LOP CEIL ACV EVSC G2; try pose proof alloc_ceiling_val as ACV__; lia);
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] v) as MU2; pose proof (wmono_refl rsegs v) as WM2
      end.
      (* [comment removed for export] *)
      all: vrechk SHV0 EzsV (pe_VEP E + 64) 8 0.
      all: do 8 zstep.   (* [comment removed for export] *)
      all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV2 : henv_ok LPA VIA (pe_H E) Ac v)
          by (eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold HOBJ_END, HFSIZE, h_cp in Ha__; change (8192 / 8) with 1024 in Ha__;
              cbn [outside]; unhide_djf; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo VEPhi ACV EVSC G2 DJfV; try pose proof alloc_ceiling_val as ACV__; lia)
      end.
      all: clear HENV1.
      all: astop AINVc MU WM CFP; fold_cl_segs.
      all: eapply (KL (PST (x_p xc) S_TagError (fupd (x_v xc) Fstate (vi_st VIA S_TagError)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) Ac _ _);
        [ apply Build_pinv; psimp; pinv_close PE0 AINVc HFR MU WM WZ
        | assumption
        | eapply amd_frame_sbm_r; [exact MDFc | exact SBM]
        | psimp; intros _; split; [| discriminate]; rewrite PHI; unfold phi, rank; psimp; try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__; lia ].
     
      all: try (cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha]).
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HDIT HDR HDC HVE HMC"] Lemma intag_exit2 : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
        (ra t1 t2 s1 a0 a1 a4 a5 a6 s10 s11 t3 t4 t5 t6 : word),
      pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
      x_st xc = S_InTag -> x_p x <= x_p xc ->
      srealizes rsegs (mkCfg (loop_ms E 0x8ca10 (x_p xc) ra t1 t2 s1 a0 a1
                                 (Z_to_bv 64 ((pe_VEP E + 88) / 8)) (Z_to_bv 64 ((pe_VEP E + 84) / 8)) a4 a5 a6 LNX s10 s11 t3 t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc AINVc MDFc STc LQ.
      clear - HMC HVE HDC HDR HDIT PE PHI KL PIc AINVc MDFc STc LQ; try pose proof alloc_ceiling_val as ACV__.
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms, S9, T0. rewrite EFP in *.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview Ac mc)) as MU. pose proof (wmono_refl rsegs (aview Ac mc)) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (CFP : client_fp LPA Ac (aview Ac mc) [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      destruct (data_shadow Ac mc mdc _ _ AINVc DATA) as [SHD D16]. fold_cl_segs. fold_aview.
      pose proof (shpat_sh_boundL (Clg:=Clg) (pe_DATA E) (Z.of_nat (length (pe_inp E))) ltac:(try (generalize alloc_ceiling_val); clear - Dlo; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(clear; lia) Dhi) as SHDB. rewrite SHMAX_val in SHDB.
      pose proof (got_vct_cell _ (consts_hold_ainv LPA Ac mc mdc AINVc)) as GOTV. pose proof (vct_shadowA _ (consts_hold_ainv LPA Ac mc mdc AINVc)) as VSH. fold_cl_segs. fold_aview.
      unfold GOTA_vct, VCT_TYPTABA in GOTV. unfold VCT_TYPTABA in VSH.
      assert (VSHB : 0 <= sh 148416 /\ sh 148416 + Z.of_nat (length (repeat (Z_to_bv 8 0) 64)) <= 17594064011264).
      { unfold sh. rewrite kShadowOffset_val. change (148416 / 8) with 18552. change (Z.of_nat (length (repeat (Z_to_bv 8 0) 64))) with 64. clear; lia. }
      hide_neqs.
      ago AINVc. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0.
      { (* [comment removed for export] *)
        astop0 AINVc.
        eapply (KL xc Ac); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]|].
        intros H. exfalso. unsign K0. try (generalize alloc_ceiling_val); clear - H K0 VERP Dlo Dhi EE ACV; try pose proof alloc_ceiling_val as ACV__. unfold pe_e, pe_N in *. lia. }
      assert (PLTc : x_p xc < pe_e E) by (unsign K0; try (generalize alloc_ceiling_val); clear - K0 PLE VERP Dlo Dhi EE ACV; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia). clear K0.
      (* [comment removed for export] *)
      zstep. if_cases KU; zify_cond KU.
      2:{ exfalso. try (generalize alloc_ceiling_val); clear - KU VERP Dlo; try pose proof alloc_ceiling_val as ACV__. rewrite ?unsigned_lit in KU by lia. lia. }
      clear KU.
      (* [comment removed for export] *)
      shadow_chk SHD 1 11.
      destruct (look_read rsegs E xc _ DBY ltac:(try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__; lia) PLTc) as (b & Hnth & Hlook & RDP).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta. zstep. zstep. if_cases K1; zify_cond K1.
      2:{ (* [comment removed for export] *)
          astop0 AINVc.
          eapply (intag_gt xc Ac); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]| exact STc| exact LQ| exact PLTc]. }
      (* [comment removed for export] *)
      zstep. vrechk SHV0 EzsV (pe_VEP E + 84) 4 0.
      zstep. zstep. pose proof B_em as EM; destruct EM as [EM|EM]; rewrite EM, sx32_small by (clear; lia).
      all: zstep; if_cases K2; zify_cond K2; try (exfalso; try (generalize alloc_ceiling_val); clear - K2; try pose proof alloc_ceiling_val as ACV__; rewrite ?unsigned_lit in K2 by (clear; lia); lia); clear K2.
      2:{ (* [comment removed for export] *)
          astop0 AINVc.
          eapply (intag_err 0x8cb00 xc Ac); [left; reflexivity| exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]| exact STc| exact LQ| exact PLTc]. }
      (* [comment removed for export] *)
      zstep. vrechk SHV0 EzsV (pe_VEP E + 88) 4 0.
      zstep. zstep. pose proof B_ca as CA; destruct CA as [CA|CA]; rewrite CA, sx32_small by (clear; lia).
      all: zstep; if_cases K3; zify_cond K3; try (exfalso; try (generalize alloc_ceiling_val); clear - K3; try pose proof alloc_ceiling_val as ACV__; rewrite ?unsigned_lit in K3 by (clear; lia); lia); clear K3.
      { (* [comment removed for export] *)
        astop0 AINVc.
        eapply (intag_err 0x8cd1c xc Ac); [right; reflexivity| exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]| exact STc| exact LQ| exact PLTc]. }
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      replace (Z.shiftl (bv_unsigned b) 1) with (2 * bv_unsigned b) by (rewrite Z.shiftl_mul_pow2; clear; lia).
      zstep. zstep; if_cases KU; zify_cond KU; [ exfalso; revert KU; rewrite ?zb_lxor_ones by (clear; lia); clear - BR; intros KU; lia | clear KU ].
      zstep.
      zstep. zstep. shadow_addr VSH 2. zstep. lit0. chk_branch.
      pose proof (vct_readA _ (bv_unsigned b) _ MI BR eq_refl) as RDV. unfold wa, VCT_TYPTABA in RDV.
      zstep. clear RDV. cbv beta. rewrite zx16_vct.
      pose proof (vct_range (bv_unsigned b)) as VR.
      zstep. zstep. if_cases K4; zify_cond K4.
      2:{ (* [comment removed for export] *)
          astop0 AINVc.
          eapply (intag_err 0x8cd1c xc Ac); [right; reflexivity| exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]| exact STc| exact LQ| exact PLTc]. }
      (* [comment removed for export] *)
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep.
      astop AINVc MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p xc) S_Attr (fupd (x_v xc) Fstate (vi_st VIA S_Attr)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) Ac _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINVc HFR MU WM WZ.
        + (* [comment removed for export] *) intros _ _ _. unfold vct_namestart. unfold look in Hlook |- *. cbn [x_p]. rewrite <- Hlook. apply (proj2 (Bool.negb_true_iff _)). apply Z.eqb_neq. clear - K4; try pose proof alloc_ceiling_val as ACV__. exact K4.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDFc | exact SBM].
      - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="LNX KL PHI PE HDIT HDR HDC HVE HMC"] Lemma intag_body : forall (A : AS) (m : mem) (md : Model) (ra t1 t2 s1 a2 a3 a4 a5 a6 s6 s10 t3 t4 t5 t6 : word),
      pinv E x A (aview A m) -> ainv A m md -> amd_frame (pe_md0 E) md -> x_st x = S_InTag -> x_p x < pe_e E ->
      srealizes rsegs (mkCfg (disp_ms E x ra t1 t2 s1 a2 a3 a4 a5 a6 s6 s10 t3 t4 t5 t6 m) md) T.
    Proof.
      intros until t6. intros PI AINV MDF ST PLT.
      handler_prologue PE PI AINV ST.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
      assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (CFP : client_fp LPA A (aview A m) [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      destruct (data_shadow A m md _ _ AINV DATA) as [SHD D16]. fold_cl_segs. fold_aview.
      pose proof (shpat_sh_boundL (Clg:=Clg) (pe_DATA E) (Z.of_nat (length (pe_inp E))) ltac:(try (generalize alloc_ceiling_val); clear - Dlo; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(clear; lia) Dhi) as SHDB. rewrite SHMAX_val in SHDB.
      pose proof (got_vct_cell _ (consts_hold_ainv LPA A m md AINV)) as GOTV. pose proof (vct_shadowA _ (consts_hold_ainv LPA A m md AINV)) as VSH. fold_cl_segs. fold_aview.
      unfold GOTA_vct, VCT_TYPTABA in GOTV. unfold VCT_TYPTABA in VSH.
      assert (VSHB : 0 <= sh 148416 /\ sh 148416 + Z.of_nat (length (repeat (Z_to_bv 8 0) 64)) <= 17594064011264).
      { unfold sh. rewrite kShadowOffset_val. change (148416 / 8) with 18552. change (Z.of_nat (length (repeat (Z_to_bv 8 0) 64))) with 64. clear; lia. }
      hide_neqs.
      ago AINV. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      rewrite (shr3_div8 (pe_VEP E + 84)), (shr3_div8 (pe_VEP E + 88)).
      (* [comment removed for export] *)
      zstep; if_cases K0; zify_cond K0; try (exfalso; unsign K0; try (generalize alloc_ceiling_val); clear - K0 PLT VERP Dlo Dhi EE ACV; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia); [].
      clear K0. zstep.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ ?P _ =>
      assert (LOOP : forall (k : nat) (q ca : Z) (ra' t1' t2' s1' a1' a4' a5' a6' s10' s11' t3' t4' t5' t6' : word) (mc : mem),
        munch [(pe_VEP E, pe_VEP E + 312)] (aview A m) mc -> wmono rsegs (aview A m) mc -> mem_inv rsegs mc ->
        rw_cells rsegs mc (pe_VEP E) (vep_cells (fupd (fupd (fupd (x_v x) Fstate (stA (x_st x))) Ftag_i 0) Fcanattr ca) (x_tag x) (x_q x)) ->
        rw_cells rsegs mc (pe_sp E - 320) (pframe E j0 j8) ->
        bytes_at rsegs mc (pe_DATA E) (pe_inp E) -> stk rsegs mc (pe_lo E) (pe_sp E - 320) ->
        bytes_at rsegs mc (sh (pe_VEP E)) zsV -> bytes_at rsegs mc (sh (pe_DATA E)) (shpat (Z.of_nat (length (pe_inp E)))) ->
        bytes_at rsegs mc (sh 148416) (repeat (Z_to_bv 8 0) 64) -> ro_cells rsegs mc 694256 [C8 (Z_to_bv 64 148416)] ->
        bool01 ca -> (x_p x < q -> ca = 1) ->
        q + Z.of_nat k = pe_e E -> x_p x <= q -> q < pe_e E ->
        evt rsegs P (loop_ms E 0x8c6c4 q ra' t1' t2' s1' (Z_to_bv 64 q) a1' (Z_to_bv 64 ((pe_VEP E + 88) / 8)) (Z_to_bv 64 ((pe_VEP E + 84) / 8))
                            a4' a5' a6' (Z_to_bv 64 142560) s10' s11' t3' t4' t5' t6' mc))
      end.
      { induction k as [|k IH]; intros until mc; intros MUc WMc MIc VEPCc FRc DBYc STKc SHVc SHDc VSHc GOTVc Bca CA1 Hk LQ QE.
        { exfalso. try (generalize alloc_ceiling_val); clear - Hk QE; try pose proof alloc_ceiling_val as ACV__. lia. }
        unfold loop_ms, S9, T0. rewrite EFP.
        clear VEPC FR DBY STK MI SHV0 SHD VSH GOTV MU WM.
        unfold vep_cells in VEPCc. psimp_in VEPCc. unfold pframe in FRc. cbv zeta in FRc.
        (* [comment removed for export] *)
        assert (CKq : forall q' v', q <= q' -> q' <= pe_e E -> (v' = (fupd (fupd (x_v x) Ftag_i 0) Fcanattr ca) \/ (v' = fupd (fupd (fupd (fupd (x_v x) Ftag_i 0) Fcanattr ca) Femptytag 1) Fcanattr 0 /\ q' = q + 1)) ->
                  forall mr, munch [(pe_VEP E, pe_VEP E + 312)] (aview A m) mr -> wmono rsegs (aview A m) mr -> mem_inv rsegs mr ->
                  rw_cells rsegs mr (pe_VEP E) (vep_cells (fupd v' Fstate (stA (x_st x))) (x_tag x) (x_q x)) ->
                  rw_cells rsegs mr (pe_sp E - 320) (pframe E j0 j8) -> stk rsegs mr (pe_lo E) (pe_sp E - 320) ->
                  pinv E (PST q' S_InTag v' (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A mr).
        { intros q' v' LQ' QE' HV mr MUr WMr MIr VEPCr FRr STKr.
          destruct HV as [-> | [-> EQ1]]; unfold vep_cells in VEPCr; psimp_in VEPCr; apply Build_pinv; psimp; pinv_close PE0 AINV HFR MUr WMr WZ.
         
          all: try (try (generalize alloc_ceiling_val); clear - VERP LQ LQ'; try pose proof alloc_ceiling_val as ACV__; lia).
          all: try (try (generalize alloc_ceiling_val); clear - QE'; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia).
          all: try (revert OUT LQ LQ'; unfold oacost, oicost; cbn [x_va x_vi x_st x_p x_vv]; clear; intros; lia).
          all: try (revert VA LQ LQ'; clear - PE0 AINV HFR MUr WMr WZ; try pose proof alloc_ceiling_val as ACV__; cbn [x_va x_v x_p x_vv]; intros VA LQ LQ'; world_close PE0 AINV HFR MUr WMr WZ).
          all: try (revert VI LQ LQ'; clear - PE0 AINV HFR MUr WMr WZ; try pose proof alloc_ceiling_val as ACV__; cbn [x_vi x_va x_v x_p x_vv]; intros VI LQ LQ'; world_close PE0 AINV HFR MUr WMr WZ).
          all: cf_stores CF MUr PE0 STKr FRr; left; left; unfold blk; lia. }
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ ?P _ =>
        assert (EXIT1 : forall (b : byte) (ra_ t1_ t2_ s1_ a0_ a1_ a5_ a6_ s10_ s11_ t3_ t4_ t5_ t6_ : word),
          nth_error (pe_inp E) (Z.to_nat (q - pe_DATA E)) = Some b ->
          evt rsegs P (loop_ms E 0x8c9b0 q ra_ t1_ t2_ s1_ a0_ a1_ (Z_to_bv 64 ((pe_VEP E + 88) / 8)) (Z_to_bv 64 ((pe_VEP E + 84) / 8))
                              (Z_to_bv 64 (bv_unsigned b)) a5_ a6_ (Z_to_bv 64 142560) s10_ s11_ t3_ t4_ t5_ t6_ mc))
        end.
        { intros until t6_. intros Hnth. unfold loop_ms, S9, T0. rewrite EFP.
          pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
          (* [comment removed for export] *)
          zstep. zstep. if_cases Ks; zify_cond Ks.
          { (* [comment removed for export] *)
            astop AINV MUc WMc CFP. fold_cl_segs.
            lazymatch goal with H : ainv A ?mr ?mdr, MUx : munch _ _ (aview A ?mr), WMx : wmono _ _ (aview A ?mr), MIx : mem_inv _ (aview A ?mr),
                                 VX : rw_cells _ (aview A ?mr) (pe_VEP E) _, FX : rw_cells _ (aview A ?mr) (pe_sp E - 320) _, SX : stk _ (aview A ?mr) _ _
              |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ =>
              pose proof (CKq q _ ltac:(clear; lia) ltac:(try (generalize alloc_ceiling_val); clear - QE; try pose proof alloc_ceiling_val as ACV__; lia) (or_introl eq_refl) _ MUx WMx MIx ltac:(unfold vep_cells; psimp; exact VX) FX SX) as PIq end.
            lazymatch type of PIq with pinv _ ?xq _ _ => eapply (intag_exit2 xq A) end; [exact PIq| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| reflexivity| cbn [x_p]; exact LQ]. }
          (* [comment removed for export] *)
          zstep. vrechk SHVc EzsV (pe_VEP E + 84) 4 0.
          zstep. zstep. pose proof B_em as EM; destruct EM as [EM|EM]; rewrite EM, sx32_small by (clear; lia).
          all: zstep; if_cases K2; zify_cond K2; try (exfalso; try (generalize alloc_ceiling_val); clear - K2; try pose proof alloc_ceiling_val as ACV__; rewrite ?unsigned_lit in K2 by (clear; lia); lia); clear K2.
          2:{ (* [comment removed for export] *)
            astop AINV MUc WMc CFP. fold_cl_segs.
            lazymatch goal with H : ainv A ?mr ?mdr, MUx : munch _ _ (aview A ?mr), WMx : wmono _ _ (aview A ?mr), MIx : mem_inv _ (aview A ?mr),
                                 VX : rw_cells _ (aview A ?mr) (pe_VEP E) _, FX : rw_cells _ (aview A ?mr) (pe_sp E - 320) _, SX : stk _ (aview A ?mr) _ _
              |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ =>
              pose proof (CKq q _ ltac:(clear; lia) ltac:(try (generalize alloc_ceiling_val); clear - QE; try pose proof alloc_ceiling_val as ACV__; lia) (or_introl eq_refl) _ MUx WMx MIx ltac:(unfold vep_cells; psimp; exact VX) FX SX) as PIq end.
            lazymatch type of PIq with pinv _ ?xq _ _ => eapply (intag_exit2 xq A) end; [exact PIq| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| reflexivity| cbn [x_p]; exact LQ]. }
          (* [comment removed for export] *)
          (* [comment removed for export] *)
          zstep. zstep. if_cases KU; zify_cond KU.
          2:{ exfalso. try (generalize alloc_ceiling_val); clear - KU QE Dhi EE ACV; try pose proof alloc_ceiling_val as ACV__. unfold pe_e, pe_N in *. rewrite ?unsigned_lit in KU by lia. lia. }
          clear KU.
          vrechk SHVc EzsV (pe_VEP E + 84) 4 0. zstep. zstep. zstep.
          zstep. vrechk SHVc EzsV (pe_VEP E + 88) 4 0. zstep. zstep. zstep. zstep.
          astop AINV MUc WMc CFP. fold_cl_segs.
          lazymatch goal with H : ainv A ?mr ?mdr, MUx : munch _ _ (aview A ?mr), WMx : wmono _ _ (aview A ?mr), MIx : mem_inv _ (aview A ?mr),
                               VX : rw_cells _ (aview A ?mr) (pe_VEP E) _, FX : rw_cells _ (aview A ?mr) (pe_sp E - 320) _, SX : stk _ (aview A ?mr) _ _
            |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ =>
            pose proof (CKq (q + 1) _ ltac:(clear; lia) ltac:(try (generalize alloc_ceiling_val); clear - QE; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia) (or_intror (conj eq_refl eq_refl)) _ MUx WMx MIx ltac:(unfold vep_cells; psimp; exact VX) FX SX) as PIq end.
          lazymatch type of PIq with pinv _ ?xq _ _ => eapply (intag_exit2 xq A) end; [exact PIq| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| reflexivity| cbn [x_p]; try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__; lia]. }
        (* [comment removed for export] *)
        (* [comment removed for export] *)
        zstep. if_cases KU; zify_cond KU.
        2:{ exfalso. try (generalize alloc_ceiling_val); clear - KU LQ VERP Dlo; try pose proof alloc_ceiling_val as ACV__. rewrite ?unsigned_lit in KU by lia. lia. }
        clear KU.
        (* [comment removed for export] *)
        shadow_chk SHDc 1 14.
        (* [comment removed for export] *)
        destruct (payload_read rsegs E _ q DBYc ltac:(try (generalize alloc_ceiling_val); clear - LQ VERP; try pose proof alloc_ceiling_val as ACV__; lia) QE) as (b & Hnth & RDP).
        pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
        zstep. clear RDP. cbv beta. zstep. zstep. zstep. zstep.
        replace (Z.shiftl (bv_unsigned b) 1) with (2 * bv_unsigned b) by (rewrite Z.shiftl_mul_pow2; clear; lia).
        (* [comment removed for export] *)
        zstep. zstep. shadow_addr VSHc 2. zstep. lit0. chk_branch.
        pose proof (vct_readA _ (bv_unsigned b) _ MIc BR eq_refl) as RDV. unfold wa, VCT_TYPTABA in RDV.
        zstep. clear RDV. cbv beta. rewrite zx16_vct.
        pose proof (vct_range (bv_unsigned b)) as VR.
        zstep. zstep. if_cases K1; zify_cond K1.
        { eapply EXIT1. exact Hnth. }
        (* [comment removed for export] *)
        zstep. vrechk SHVc EzsV (pe_VEP E + 84) 4 0.
        zstep. zstep. pose proof B_em as EM; destruct EM as [EM|EM]; rewrite EM, sx32_small by (clear; lia).
        all: zstep; if_cases K2; zify_cond K2; try (exfalso; try (generalize alloc_ceiling_val); clear - K2; try pose proof alloc_ceiling_val as ACV__; rewrite ?unsigned_lit in K2 by (clear; lia); lia); clear K2.
        2:{ (* [comment removed for export] *)
            astop AINV MUc WMc CFP. fold_cl_segs.
            lazymatch goal with H : ainv A ?mr ?mdr, MUx : munch _ _ (aview A ?mr), WMx : wmono _ _ (aview A ?mr), MIx : mem_inv _ (aview A ?mr),
                                 VX : rw_cells _ (aview A ?mr) (pe_VEP E) _, FX : rw_cells _ (aview A ?mr) (pe_sp E - 320) _, SX : stk _ (aview A ?mr) _ _
              |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ =>
              pose proof (CKq q _ ltac:(clear; lia) ltac:(try (generalize alloc_ceiling_val); clear - QE; try pose proof alloc_ceiling_val as ACV__; lia) (or_introl eq_refl) _ MUx WMx MIx ltac:(unfold vep_cells; psimp; exact VX) FX SX) as PIq end.
            lazymatch type of PIq with pinv _ ?xq _ _ => eapply (intag_exit2 xq A) end; [exact PIq| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| reflexivity| cbn [x_p]; exact LQ]. }
        (* [comment removed for export] *)
        zstep. vrechk SHVc EzsV (pe_VEP E + 88) 4 0.
        zstep. zstep. zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. if_cases K3; zify_cond K3.
        - lazymatch goal with MUx : munch _ _ ?mr, WMx : wmono _ _ ?mr, MIx : mem_inv _ ?mr, VX : rw_cells _ ?mr (pe_VEP E) _, FX : rw_cells _ ?mr (pe_sp E - 320) _,
                               DX : bytes_at _ ?mr (pe_DATA E) _, SX : stk _ ?mr _ _, H1 : bytes_at _ ?mr (sh (pe_VEP E)) _, H2 : bytes_at _ ?mr (sh (pe_DATA E)) _,
                               H3 : bytes_at _ ?mr (sh 148416) _, H4 : ro_cells _ ?mr 694256 _
            |- evt _ _ (MS _ _ _ _ _ ?mr _) =>
            eapply (IH (q + 1) 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ mr MUx WMx MIx ltac:(unfold vep_cells; psimp; exact VX) ltac:(unfold pframe; cbv zeta; exact FX) DX SX H1 H2 H3 H4);
            [right; reflexivity| intros _; reflexivity| try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - K3 Hk QE; try pose proof alloc_ceiling_val as ACV__; lia] end.
        - (* [comment removed for export] *)
          zstep. zstep.
          astop AINV MUc WMc CFP. fold_cl_segs.
          set (xq := PST (pe_e E) S_InTag (fupd (fupd (x_v x) Ftag_i 0) Fcanattr 1) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
          lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIq : pinv E xq A (aview A mr)) end.
          { subst xq. lazymatch goal with MUx : munch _ _ ?mr, WMx : wmono _ _ ?mr |- pinv _ _ _ ?mr =>
              apply Build_pinv; psimp; pinv_close PE0 AINV HFR MUx WMx WZ end.
            + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ QE; try pose proof alloc_ceiling_val as ACV__. lia.
            + (* [comment removed for export] *) clear. lia.
            + (* [comment removed for export] *) revert OUT LQ QE. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
            + (* [comment removed for export] *) lazymatch goal with MUx : munch _ _ ?mr, WMx : wmono _ _ ?mr |- _ => world_close PE0 AINV HFR MUx WMx WZ end.
            + (* [comment removed for export] *) lazymatch goal with MUx : munch _ _ ?mr, WMx : wmono _ _ ?mr |- _ => world_close PE0 AINV HFR MUx WMx WZ end.
            + (* [comment removed for export] *) lazymatch goal with MUx : munch _ _ ?mr, SX : stk _ ?mr _ _, FX : rw_cells _ ?mr (pe_sp E - 320) _ |- _ => cf_stores CF MUx PE0 SX FX end. left; left. unfold blk. lia. }
          eapply (intag_exit2 xq A); [exact PIq| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| reflexivity| subst xq; cbn [x_p]; try (generalize alloc_ceiling_val); clear - LQ QE; try pose proof alloc_ceiling_val as ACV__; lia]. }
      eapply (LOOP (Z.to_nat (pe_e E - x_p x)) (x_p x) (x_v x Fcanattr));
        [exact MU| exact WM| exact MI| unfold vep_cells; psimp; exact VEPC| unfold pframe; cbv zeta; exact FR| exact DBY| exact STK
        | exact SHV0| exact SHD| exact VSH| exact GOTV| exact B_ca| intros X; exfalso; try (generalize alloc_ceiling_val); clear - X; try pose proof alloc_ceiling_val as ACV__; lia
        | try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val as ACV__; rewrite Z2Nat.id by lia; lia| clear; lia| exact PLT].
    Qed.
  End X.

  #[using="HDIT HDR HDC HVE HMC"] Lemma PH_InTag : handler_stmt S_InTag.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    eapply (intag_body E x T PE); [unfold phi, rank; rewrite ST; reflexivity| exact KL| exact PI| exact AINV| exact MDF| exact ST| exact PLT].
  Qed.
End S.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Vsb A_World A_Img A_Cocsh A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.

Module A_PHd8z.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient ATac AIcpm9j AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj.A_PPutc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold vep_error_post, VEPERR_STACK in H.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
Ltac show_left := match goal with |- ?G => idtac "LEFTOVER:" G end.
Local Tactic Notation "klia" ne_hyp_list(hs) := try (generalize alloc_ceiling_val); clear - hs; try pose proof alloc_ceiling_val as ACV__; lia.
(* [comment removed for export] *)
Tactic Notation "shadow_chkn" constr(SRC) constr(k) constr(U) integer(n) :=
  zstep; zstep; shadow_addr SRC k;
  lazymatch goal with |- evt ?segs ?Q _ =>
    eapply (evt_cut segs _ Q);
    [ zstep; do n zstep;
      let K := fresh "KS" in
      zstep; if_cases K; zify_cond K;
      [ first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ]
      | first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ] ]
    | let ms := fresh "ms" in let x := fresh "junk" in
      intros ms [x ->]; simp_regs ]
  end;
  shadow_cleanup.

Section S.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HVE : vep_error_stmt.
  Hypothesis HDS : VSB_destroy_stmt.
  Hypothesis HPC : VSB_putc_stmt.

  Section X.
    Variables (E : penv) (x : pst) (T : TSet).
    Hypothesis PE : penv_ok E.
    Hypothesis PHI : phi E x = 16 * (pe_e E - x_p x) + 1.
    Hypothesis KL : latch_K E x T.

    Let LTE : word := Z_to_bv 64 143872.   (* [comment removed for export] *)
    Let LIT : word := Z_to_bv 64 144000.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    Let JT4 : word := Z_to_bv 64 ((pe_VEP E + 232) / 8).
    Let JA6 : word := Z_to_bv 64 ((pe_VEP E + 224) / 8).

    (* [comment removed for export] *)
    Lemma attr_vsb_range : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model),
      pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> 0 <= x_v xc Fattr_vsb < 2^64.
    Proof.
      intros xc Ac mc mdc PIc AINVc. pose proof (pi_va _ _ _ _ PIc) as VA. unfold va_world in VA.
      pose proof alloc_ceiling_num as ACV. destruct (x_va xc) as [ya|].
      - destruct VA as (_ & AOBJ & _). pose proof (live_geomP LPA _ _ _ _ _ AINVc (proj1 (proj2 (proj2 AOBJ)))) as (_ & _ & L1 & L2 & _). unfold kHighMemBeg in L1. all_app_facts. unhide_app. lia.
      - rewrite VA. lia.
    Qed.

    (* [comment removed for export] *)
    Definition av_gtfin_T : Prop :=
      forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model) (m2 : mem) (y : vsb_rec)
             (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word),
        pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
        x_st xc = S_AttrValue -> x_p x <= x_p xc -> x_p xc < pe_e E -> x_va xc = Some y ->
        munch [(pe_sp E - 304 - 64, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] (aview Ac mc) m2 ->
        wmono rsegs (aview Ac mc) m2 ->
        mem_inv rsegs m2 -> stk rsegs m2 (pe_lo E) (pe_fp E) -> rw_cells rsegs m2 (pe_fp E) (pframe E JT4 JA6) ->
        rw_cells rsegs m2 (pe_VEP E) (vep_cells (fupd (fupd (x_v xc) Fstate (vi_st VIA S_TagError)) Fattr_delim 0) (x_tag xc) (x_q xc)) ->
        bytes_at rsegs m2 (sh (pe_VEP E)) (repeat (Z_to_bv 8 0) 39) ->
        henv_ok LPA VIA (pe_H E) Ac m2 ->
        evt rsegs (EvtAcct.srz_at_r rsegs (ahull Ac) (alhull Ac) (aeager Ac) mc mdc T)
            (call_ms E 0x8d360 (x_p xc) ra t0 t1 t2 (Z_to_bv 64 (x_v xc Fattr_vsb)) a1 a2 a3 a4 a5 a6 a7 s2 LTE LIT t3 t4 t5 t6 m2).

    (* [comment removed for export] *)
    #[using="KL PHI PE HDS HVE"] Lemma av_gt (AVG : av_gtfin_T) : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
        (ra a0 a1 a2 a3 a4 a5 a6 s2 t4 t5 t6 : word),
      pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
      x_st xc = S_AttrValue -> x_p x <= x_p xc -> x_p xc < pe_e E ->
      rw_cells rsegs (aview Ac mc) (pe_fp E) (pframe E JT4 JA6) ->
      srealizes rsegs (mkCfg (loop_ms E 0x8d304 (x_p xc) (S8 E) ra a0 a1 a2 a3 a4 a5 a6 s2 LTE LIT t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc AINVc MDFc STc LQ PLTc FRX.
      clear - AVG HVE HDS PE PHI KL PIc AINVc MDFc STc LQ PLTc FRX; try pose proof alloc_ceiling_val as ACV__.
      pose proof PIc as PIc0. pose proof (attr_vsb_range _ _ _ _ PIc AINVc) as ATR.
      world_open PE PIc AINVc. unfold loop_ms, S8. rewrite EFP in *. clear FR. pose proof FRX as FR. unfold pframe in FR. cbv zeta in FR. unfold JT4, JA6 in FR.
      pose proof (munch_refl [(pe_sp E - 304 - 64, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] (aview Ac mc)) as MU.
      pose proof (wmono_refl rsegs (aview Ac mc)) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_sp E - 304 - 64, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
      assert (CFP : client_fp LPA Ac (aview Ac mc) [(pe_sp E - 304 - 64, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)])
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
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      unhide DJfV.
      try clear DBY. icall (HVE (pe_VEP E) (fupd (x_v xc) Fstate (stA (x_st xc))) (x_tag xc) (x_q xc) (pe_H E) (pe_lo E)) by
        (rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - FRB; try pose proof alloc_ceiling_val as ACV__; lia);
         first [ reflexivity | exact VEPC | exact TAG | exact PADS | exact (proj1 BASE) | exact GLOB | exact HOBJ | exact HSH | exact HG
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
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep.
      zstep. zstep. vrechk SHV0 EzsV (pe_VEP E + 232) 4 0. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. vrechk SHV0 EzsV (pe_VEP E + 224) 8 0. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV2 : henv_ok LPA VIA (pe_H E) Ac v)
          by (eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold HOBJ_END, HFSIZE, h_cp in Ha__; change (8192 / 8) with 1024 in Ha__;
              cbn [outside]; unhide_djf; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo VEPhi ACV EVSC G2 DJfV; try pose proof alloc_ceiling_val as ACV__; lia)
      end.
      clear HENV1.
      set (xt := PST (x_p xc) S_TagError (fupd (fupd (x_v xc) Fstate (vi_st VIA S_TagError)) Fattr_delim 0) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)).
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      - (* [comment removed for export] *)
        destruct (x_va xc) as [y|] eqn:EVA; [| exfalso; exact (K1 VA)].
        lazymatch goal with MUx : munch _ (aview Ac mc) ?mf, WMx : wmono _ (aview Ac mc) ?mf, MIx : mem_inv _ ?mf,
                             SX : stk _ ?mf _ _, FX : rw_cells _ ?mf (pe_sp E - 304) _, VX : rw_cells _ ?mf (pe_VEP E) _, HX : bytes_at _ ?mf (sh (pe_VEP E)) _
          |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
          eapply (AVG xc Ac mc mdc mf y); [exact PIc0| exact AINVc| exact MDFc| exact STc| exact LQ| exact PLTc| exact EVA
            | exact MUx| exact WMx| exact MIx| rewrite EFP; exact SX| rewrite EFP; unfold pframe, JT4, JA6; cbv zeta; exact FX
            | unfold vep_cells; psimp; exact VX| rewrite <- EzsV; exact HX| exact HENV2] end.
      - (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        astop AINVc MU WM CFP. fold_cl_segs.
        eapply (KL xt Ac _ _); subst xt.
        + apply Build_pinv; psimp; pinv_close PE0 AINVc HFR MU WM WZ. all: show_left.
          all: first [ intros X; exfalso; apply X; exact K1
                     | cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha]
                     | destruct ATTR as [X|(X1 & X2 & X3)]; [left; exact X| right; refine (conj X1 (conj X2 _)); right; left; reflexivity] ].
        + assumption.
        + eapply amd_frame_sbm_r; [exact MDFc | exact SBM].
        + psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__. lia.
    Qed.

    (* [comment removed for export] *)
    Definition av_finish_T : Prop :=
      forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model) (m2 : mem) (y : vsb_rec) (ra a1 a2 a3 a4 a5 t5 t6 : word),
        pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
        x_st xc = S_AttrValue -> x_p x <= x_p xc -> x_p xc < pe_e E -> x_va xc = Some y ->
        munch [(pe_VEP E, pe_VEP E + 312)] (aview Ac mc) m2 -> wmono rsegs (aview Ac mc) m2 ->
        client_fp LPA Ac (aview Ac mc) [(pe_VEP E, pe_VEP E + 312)] ->
        mem_inv rsegs m2 -> stk rsegs m2 (pe_lo E) (pe_fp E) -> rw_cells rsegs m2 (pe_fp E) (pframe E JT4 JA6) ->
        rw_cells rsegs m2 (pe_VEP E) (vep_cells (fupd (fupd (x_v xc) Fattr_delim 0) Fstate (stA S_InTag)) (x_tag xc) (x_q xc)) ->
        bytes_at rsegs m2 (sh (pe_VEP E)) (repeat (Z_to_bv 8 0) 39) ->
        evt rsegs (EvtAcct.srz_at_r rsegs (ahull Ac) (alhull Ac) (aeager Ac) mc mdc T)
            (loop_ms E 0x8d2b0 (x_p xc + 1) (S8 E) ra (Z_to_bv 64 (x_v xc Fattr_vsb)) a1 a2 a3 a4 a5 JA6
                     (Z_to_bv 64 ((pe_VEP E + 224) / 8 + 2147450880)) LTE LIT JT4 t5 t6 m2).

    (* [comment removed for export] *)
    #[using="KL PHI PE"] Lemma av_delim (AVF : av_finish_T) : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
        (ra a0 a1 a3 a4 s2 t5 t6 : word),
      pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
      x_st xc = S_AttrValue -> x_p x <= x_p xc -> x_p xc < pe_e E ->
      rw_cells rsegs (aview Ac mc) (pe_fp E) (pframe E JT4 JA6) ->
      srealizes rsegs (mkCfg (loop_ms E 0x8d26c (x_p xc) (S8 E) ra a0 a1 (Z_to_bv 64 ((pe_VEP E + 232) / 8 + 2147450880)) a3 a4
                                 (Z_to_bv 64 (pe_VEP E + 232)) JA6 s2 LTE LIT JT4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc AINVc MDFc STc LQ PLTc FRX.
      clear - AVF PE PHI KL PIc AINVc MDFc STc LQ PLTc FRX; try pose proof alloc_ceiling_val as ACV__.
      pose proof PIc as PIc0. pose proof (attr_vsb_range _ _ _ _ PIc AINVc) as ATR.
      world_open PE PIc AINVc. unfold loop_ms, S8. rewrite EFP in *. clear FR. pose proof FRX as FR. unfold pframe in FR. cbv zeta in FR. unfold JT4, JA6 in FR |- *.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview Ac mc)) as MU. pose proof (wmono_refl rsegs (aview Ac mc)) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (CFP : client_fp LPA Ac (aview Ac mc) [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      hide_neqs.
      ago AINVc. fold_cl_segs.
      (* [comment removed for export] *)
      vrechk SHV0 EzsV (pe_VEP E + 232) 4 0. zstep. vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep.
      (* [comment removed for export] *)
      zstep. zstep. vrechk SHV0 EzsV (pe_VEP E + 224) 8 0. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      - (* [comment removed for export] *)
        destruct (x_va xc) as [y|] eqn:EVA; [| exfalso; exact (K1 VA)].
        lazymatch goal with MUx : munch _ (aview Ac mc) ?mf, WMx : wmono _ (aview Ac mc) ?mf, MIx : mem_inv _ ?mf,
                             SX : stk _ ?mf _ _, FX : rw_cells _ ?mf (pe_sp E - 304) _, VX : rw_cells _ ?mf (pe_VEP E) _, HX : bytes_at _ ?mf (sh (pe_VEP E)) _
          |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
          eapply (AVF xc Ac mc mdc mf y); [exact PIc0| exact AINVc| exact MDFc| exact STc| exact LQ| exact PLTc| exact EVA
            | exact MUx| exact WMx| exact CFP| exact MIx| rewrite EFP; exact SX| rewrite EFP; unfold pframe, JT4, JA6; cbv zeta; exact FX
            | unfold vep_cells; psimp; exact VX| rewrite <- EzsV; exact HX] end.
      - (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        astop AINVc MU WM CFP. fold_cl_segs.
        eapply (KL (PST (x_p xc + 1) S_InTag (fupd (fupd (x_v xc) Fattr_delim 0) Fstate (vi_st VIA S_InTag)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) Ac _ _).
        + apply Build_pinv; psimp; pinv_close PE0 AINVc HFR MU WM WZ. all: show_left.
          all: first [ klia VERP | try (generalize alloc_ceiling_val); clear - PLTc; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia
                     | intros X; exfalso; exact (X K1)
                     | world_close PE0 AINVc HFR MU WM WZ
                     | cf_stores CF MU PE0 STK FR; left; left; unfold blk; lia
                     | destruct ATTR as [X|(X1 & X2 & X3)]; [left; exact X| right; refine (conj X1 (conj X2 _)); left; exact I] ].
        + assumption.
        + eapply amd_frame_sbm_r; [exact MDFc | exact SBM].
        + psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HPC HDS HVE"] Lemma av_loop (AVF : av_finish_T) (AVG : av_gtfin_T) : forall (k : nat) (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
        (ra a0 a1 a2 a3 a4 a5 t5 t6 : word),
      pe_e E - x_p xc = Z.of_nat k ->
      pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
      x_st xc = S_AttrValue -> x_p x <= x_p xc -> x_p xc < pe_e E ->
      rw_cells rsegs (aview Ac mc) (pe_fp E) (pframe E JT4 JA6) ->
      srealizes rsegs (mkCfg (loop_ms E 0x8ce84 (x_p xc) (S8 E) ra a0 a1 a2 a3 a4 a5 JA6 (Z_to_bv 64 (x_p xc)) LTE LIT JT4 t5 t6 mc) mdc) T.
    Proof.
      induction k as [|k IH]; intros until t6; intros Hk PIc AINVc MDFc STc LQ PLTc FRX.
      { exfalso. try (generalize alloc_ceiling_val); clear - Hk PLTc; try pose proof alloc_ceiling_val as ACV__. lia. }
      (* [comment removed for export] *)
      assert (TAIL : forall (xn : pst) (An : AS) (mn : mem) (mdn : Model) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a7' t3' t5' t6' : word),
        pinv E xn An (aview An mn) -> ainv An mn mdn -> amd_frame (pe_md0 E) mdn ->
        x_st xn = S_AttrValue -> x_p xn = x_p xc + 1 ->
        rw_cells rsegs (aview An mn) (pe_fp E) (pframe E JT4 JA6) ->
        srealizes rsegs (mkCfg (call_ms E 0x8cf14 (x_p xc) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' JA6 a7' (Z_to_bv 64 (x_p xc)) LTE LIT t3' JT4 t5' t6' mn) mdn) T).
      { intros until t6'. intros PIn AINVn MDFn STn EPn FRn.
        clear - IH PE PHI KL PIn AINVn MDFn STn EPn FRn LQ Hk PLTc; try pose proof alloc_ceiling_val as ACV__.
        unfold JT4, JA6 in FRn |- *.
        pose proof PIn as PIn0. pose proof (pi_pe _ _ _ _ PIn) as PLEn. pose proof (pi_verp _ _ _ _ PIn) as VERPn.
        world_open PE PIn AINVn. unfold call_ms, S8. cbv zeta. rewrite EFP in *.
        hide_neqs.
        ago AINVn. fold_cl_segs.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        zstep. if_cases K9; zify_cond K9.
        - (* [comment removed for export] *)
          astop0 AINVn. rewrite <- EPn.
          eapply (IH xn An); [try (generalize alloc_ceiling_val); clear - Hk EPn; try pose proof alloc_ceiling_val as ACV__; lia| exact PIn0| assumption| eapply amd_frame_sbm_r; [exact MDFn | exact SBM]| exact STn
            | try (generalize alloc_ceiling_val); clear - LQ EPn; try pose proof alloc_ceiling_val as ACV__; lia| rewrite EPn; try (generalize alloc_ceiling_val); clear - K9 Hk PLTc PLEn EPn; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia| exact FRn].
        - (* [comment removed for export] *)
          zstep. astop0 AINVn. rewrite <- EPn.
          eapply (KL xn An _ _); [exact PIn0| assumption| eapply amd_frame_sbm_r; [exact MDFn | exact SBM]|].
          rewrite EPn. intros H. exfalso. try (generalize alloc_ceiling_val); clear - H K9 Hk PLTc PLEn; try pose proof alloc_ceiling_val as ACV__. unfold pe_e, pe_N in *. lia. }
      clear IH.
      pose proof PIc as PIc0. pose proof (attr_vsb_range _ _ _ _ PIc AINVc) as ATR.
      world_open PE PIc AINVc. unfold loop_ms, S8. rewrite EFP in *. clear FR. pose proof FRX as FR. unfold pframe in FR. cbv zeta in FR. unfold JT4, JA6 in FR |- *.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview Ac mc)) as MU. pose proof (wmono_refl rsegs (aview Ac mc)) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (CFP : client_fp LPA Ac (aview Ac mc) [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      destruct (data_shadow Ac mc mdc _ _ AINVc DATA) as [SHD D16]. fold_cl_segs. fold_aview.
      pose proof (shpat_sh_boundL (Clg:=Clg) (pe_DATA E) (Z.of_nat (length (pe_inp E))) ltac:(try (generalize alloc_ceiling_val); clear - Dlo; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(clear; lia) Dhi) as SHDB. rewrite SHMAX_val in SHDB.
      pose proof (got_vct_cell _ (consts_hold_ainv LPA Ac mc mdc AINVc)) as GOTV. pose proof (vct_shadowA _ (consts_hold_ainv LPA Ac mc mdc AINVc)) as VSH. fold_cl_segs. fold_aview.
      unfold GOTA_vct, VCT_TYPTABA in GOTV. unfold VCT_TYPTABA in VSH.
      assert (VSHB : 0 <= sh 148832 /\ sh 148832 + Z.of_nat (length (repeat (Z_to_bv 8 0) 64)) <= 17594064011264).
      { unfold sh. rewrite kShadowOffset_val. change (148832 / 8) with 18604. change (Z.of_nat (length (repeat (Z_to_bv 8 0) 64))) with 64. clear; lia. }
      assert (DR : 0 <= x_v xc Fattr_delim < 2^31) by (destruct (DELIM2 eq_refl) as [D|[D|D]]; rewrite D; clear; lia).
      hide_neqs.
      ago AINVc. fold_cl_segs.
      (* [comment removed for export] *)
      shadow_chkn SHD 1 11 1.
      (* [comment removed for export] *)
      destruct (look_read (Clg:=Clg) rsegs E xc _ DBY ltac:(try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__; lia) PLTc) as (b & Hnth & Hlook & RDP).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta. zstep. zstep. if_cases K1; zify_cond K1.
      { astop0 AINVc.
        eapply (av_gt AVG xc Ac); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]| exact STc| exact LQ| exact PLTc| try rewrite EFP; exact FRX]. }
      (* [comment removed for export] *)
      zstep. vrechk SHV0 EzsV (pe_VEP E + 232) 4 0.
      zstep. rewrite (sx32_small _ DR).
      zstep. if_cases K2; zify_cond K2.
      { astop0 AINVc.
        eapply (av_delim AVF xc Ac); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]| exact STc| exact LQ| exact PLTc| try rewrite EFP; exact FRX]. }
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ ?P _ =>
      assert (COLLECT : forall (a0v a2v a3v a4v : word),
        evt rsegs P (loop_ms E 0x8ceec (x_p xc) (S8 E) ra a0v (Z_to_bv 64 (bv_unsigned b)) a2v a3v a4v (Z_to_bv 64 (pe_VEP E + 232))
                        (Z_to_bv 64 ((pe_VEP E + 224) / 8)) (Z_to_bv 64 (x_p xc)) LTE LIT (Z_to_bv 64 ((pe_VEP E + 232) / 8)) t5 t6 (aview Ac mc)))
      end.
      { intros a0v a2v a3v a4v. unfold loop_ms, S8. rewrite EFP.
        (* [comment removed for export] *)
        zstep. vrechk SHV0 EzsV (pe_VEP E + 224) 8 0. zstep. zstep.
        zstep. if_cases K5; zify_cond K5.
        - (* [comment removed for export] *)
          set (xn := PST (x_p xc + 1) S_AttrValue (x_v xc) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)).
          assert (PIn : pinv E xn Ac (aview Ac mc)).
          { subst xn. apply Build_pinv; psimp; pinv_close PE0 AINVc HFR MU WM WZ. all: show_left.
            all: first [ klia VERP | try (generalize alloc_ceiling_val); clear - PLTc; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia | exact (conj DELIM1 DELIM2)
                       | world_close PE0 AINVc HFR MU WM WZ ]. }
          astop0 AINVc.
          eapply (TAIL xn Ac); [exact PIn| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]| reflexivity| reflexivity| try rewrite EFP; exact FRX].
        - (* [comment removed for export] *)
          assert (EVA : exists y, x_va xc = Some y).
          { clear - VA K5; try pose proof alloc_ceiling_val as ACV__. destruct (x_va xc) as [y|]; [exists y; reflexivity| exfalso; exact (K5 VA)]. }
          destruct EVA as [y EVA].
          zstep.
          astop0 AINVc.
          eapply (putc_call HPC E xc Ac _ _ T (x_p xc) 0x8cf0c y JT4 JA6);
            [exact PE| exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]| exact EVA| exact STc| exact PLTc| clear; lia| reflexivity
            | rewrite EFP; exact FRX|].
          intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1 y1 x1 EX1 PI1 AINV1 MDF1 LEN1 FR1. subst x1.
          clear - TAIL PE PI1 AINV1 MDF1 FR1 STc; try pose proof alloc_ceiling_val as ACV__.
          pose proof PI1 as PI10.
          world_open PE PI1 AINV1. unfold call_ms, S8. cbv zeta. rewrite EFP in *. clear FR. pose proof FR1 as FR. unfold pframe in FR. cbv zeta in FR. unfold JT4, JA6 in FR |- *.
          unfold after_putc. cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi].
          hide_neqs.
          ago AINV1. fold_cl_segs.
          (* [comment removed for export] *)
          zstep. zstep.
          astop0 AINV1.
          eapply (TAIL (after_putc xc y1) A1); [exact PI10| assumption| eapply amd_frame_sbm_r; [exact MDF1 | exact SBM]| exact STc| reflexivity| try rewrite EFP; exact FR1]. }
      (* [comment removed for export] *)
      zstep. zstep. if_cases K3; zify_cond K3.
      { (* [comment removed for export] *) apply COLLECT. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      replace (Z.shiftl (bv_unsigned b) 1) with (2 * bv_unsigned b) by (rewrite Z.shiftl_mul_pow2; clear; lia).
      zstep. zstep. shadow_addr VSH 2. zstep. lit0. chk_branch.
      pose proof (vct_readA _ (bv_unsigned b) _ MI BR eq_refl) as RDV. unfold wa, VCT_TYPTABA in RDV.
      zstep. clear RDV. cbv beta. rewrite zx16_vct.
      pose proof (vct_range (bv_unsigned b)) as VR.
      zstep. zstep. if_cases K4; zify_cond K4.
      { astop0 AINVc.
        eapply (av_delim AVF xc Ac); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]| exact STc| exact LQ| exact PLTc| try rewrite EFP; exact FRX]. }
      apply COLLECT.
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HPC HDS HVE"] Lemma av_body (AVF : av_finish_T) (AVG : av_gtfin_T) : forall (A : AS) (m : mem) (md : Model) (ra a2 a3 a4 a5 a6 s2 s5 s11 t4 t5 t6 : word),
      pinv E x A (aview A m) -> ainv A m md -> amd_frame (pe_md0 E) md -> x_st x = S_AttrValue -> x_p x < pe_e E ->
      srealizes rsegs (mkCfg (disp_ms E x ra a2 a3 a4 a5 a6 s2 s5 s11 t4 t5 t6 m) md) T.
    Proof.
      intros until t6. intros PI AINV MDF ST PLT.
      handler_prologue PE PI AINV ST.
      rewrite (shr3_div8 (pe_VEP E + 224)), (shr3_div8 (pe_VEP E + 232)).
      pose proof (munch_refl [(pe_sp E - 304, pe_sp E - 304 + 16)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
      assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                           [(pe_sp E - 304, pe_sp E - 304 + 16)]) by wzone_tac.
      assert (CFP : client_fp LPA A (aview A m) [(pe_sp E - 304, pe_sp E - 304 + 16)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      hide_neqs.
      ago AINV. fold_cl_segs.
      (* [comment removed for export] *)
      zstep; if_cases K0; zify_cond K0; try (exfalso; unsign K0; try (generalize alloc_ceiling_val); clear - K0 PLT VERP Dlo Dhi EE ACV; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia); [].
      clear K0. zstep. zstep. zstep.
      astop AINV MU WM CFP. fold_cl_segs.
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIx : pinv E x A (aview A mr)) end.
      { apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ. all: show_left.
        all: rewrite ?ST; try assumption.
        all: first [ exact (conj DELIM1 DELIM2) | cf_stores CF MU PE0 STK FR ]. }
      eapply (av_loop AVF AVG (Z.to_nat (pe_e E - x_p x)) x A);
        [try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val as ACV__; rewrite Z2Nat.id by lia; reflexivity| exact PIx| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| exact ST| clear; lia| exact PLT
        | rewrite EFP; unfold pframe, JT4, JA6; cbv zeta; exact FR].
    Qed.
  End X.
End S.
End A_PHd8z.


Module A_PH76v.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient ATac AIcpm9j AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_Img A_ImgAny A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDswi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDswi A_VEr47.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj.A_PPutc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App.A_Fpx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDswi.A_PKitX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDswi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHmhz.A_PHd8z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
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

Local Tactic Notation "klia" ne_hyp_list(hs) := try (generalize alloc_ceiling_val); clear - hs; try pose proof alloc_ceiling_val as ACV__; lia.

Section S.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Section X.
    Variables (E : penv) (x : pst) (T : TSet).
    Hypothesis PE : penv_ok E.
    Hypothesis PHI : phi E x = 16 * (pe_e E - x_p x) + 1.
    Hypothesis KL : latch_K E x T.

    (* [comment removed for export] *)
    #[using="KL PHI PE"] Lemma av_ret : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model) (m : mem) (md : Model) (y : vsb_rec)
        (fj0 fj8 : word) (A4 : AS) (m4 : mem) (md4 : Model) (v4 : vep) (vi4 : option vsb_rec)
        (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      let vv := fupd (fupd (x_v xc) Fattr_delim 0) Fstate (stA S_InTag) in
      let yf := vsb_set_flags y VSB_FLAGS_FIN in
      let W := [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 304 - 64, pe_sp E - 304); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                (vb_buf y, vb_buf y + vb_size y); (ERRNOA, ERRNOA + 4); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] in
      pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
      x_st xc = S_AttrValue -> x_p x <= x_p xc -> x_p xc < pe_e E -> x_va xc = Some y -> vb_error y = 0 ->
      (* [comment removed for export] *)
      ainv Ac m md -> same_but_materialized mdc md ->
      munch W (aview Ac mc) (aview Ac m) -> wmono rsegs (aview Ac mc) (aview Ac m) ->
      wzonex E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Finclude_src; oibuf xc] W ->
      stk rsegs (aview Ac m) (pe_lo E) (pe_sp E - 304) -> rw_cells rsegs (aview Ac m) (pe_sp E - 304) (pframe E fj0 fj8) ->
      vsb_obj LPA Ac (aview Ac m) (x_v xc Fattr_vsb) yf true ->
      (* [comment removed for export] *)
      ainv A4 m4 md4 -> mem_inv rsegs (aview A4 m4) -> amd_frame md md4 ->
      stk rsegs (aview A4 m4) (pe_lo E) (pe_sp E - 304) -> henv_ok LPA VIA (pe_H E) A4 (aview A4 m4) ->
      vep_obj LPA A4 (aview A4 m4) (pe_VEP E) v4 (x_tag xc) (x_q xc) ->
      frames_same Ac A4 -> a_tinycred A4 = a_tinycred Ac -> a_seccred A4 = a_seccred Ac -> a_primcred A4 = a_primcred Ac (* [comment removed for export] *) ->
      (  (x_vi xc = None /\ v4 = fupd (fupd vv Finclude_src (x_v xc Fattr_vsb)) Fattr_vsb 0 /\ vi4 = Some yf /\
          (forall r, a_live A4 r = a_live Ac r) /\ a_livebytes A4 = a_livebytes Ac /\ a_nlive A4 = a_nlive Ac)
      \/ (x_vi xc <> None /\ v4 = fupd (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0) Finclude_src 0 /\ vi4 = None /\
          a_live A4 (x_v xc Fattr_vsb) = None /\ a_live A4 (vb_buf y) = None /\
          match x_vi xc with
          | Some yi => a_live A4 (x_v xc Finclude_src) = None /\ a_live A4 (vb_buf yi) = None /\
                       a_livebytes A4 = a_livebytes Ac - 80 - vb_size y - vb_size yi /\ a_nlive A4 = a_nlive Ac - 4
          | None => False end /\
          (forall r, r <> x_v xc Fattr_vsb -> r <> vb_buf y -> r <> x_v xc Finclude_src ->
                     r <> match x_vi xc with Some yi => vb_buf yi | None => 0 end -> a_live A4 r = a_live Ac r))
      \/ (x_vi xc = None /\ v4 = fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0 /\ vi4 = None /\
          a_live A4 (x_v xc Fattr_vsb) = None /\ a_live A4 (vb_buf y) = None /\
          a_livebytes A4 = a_livebytes Ac - 40 - vb_size y /\ a_nlive A4 = a_nlive Ac - 2 /\
          (forall r, r <> x_v xc Fattr_vsb -> r <> vb_buf y -> a_live A4 r = a_live Ac r))
      \/ (vv Fmatch_hit = vi_tbl_attr_include VIA + 16 (* [comment removed for export] *) /\ exists ic, bool01 ic /\ v4 = fupd (fupd vv Finclude_continue ic) Fattr_vsb 0 /\ vi4 = x_vi xc /\
          a_live A4 (x_v xc Fattr_vsb) = None /\ a_live A4 (vb_buf y) = None /\
          a_livebytes A4 = a_livebytes Ac - 40 - vb_size y /\ a_nlive A4 = a_nlive Ac - 2 /\
          (forall r, r <> x_v xc Fattr_vsb -> r <> vb_buf y -> a_live A4 r = a_live Ac r))) ->
      match vi4 with
      | None => v4 Finclude_src = 0
      | Some yi => v4 Finclude_src <> 0 /\ vsb_obj LPA A4 (aview A4 m4) (v4 Finclude_src) yi true /\ vb_error yi = 0
      end ->
      cframe LPA (owned Ac) (owned A4) (pe_sp E - 304) DOINCL_STACK
             (fun a => blk (pe_VEP E) 312 a \/ vsb_blocks (x_v xc Fattr_vsb) yf a
                       \/ match x_vi xc with Some yi => vsb_blocks (x_v xc Finclude_src) yi a | None => False end
                       \/ (h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320))
             nowhere (aview Ac m) (aview A4 m4) ->
      srealizes rsegs (mkCfg (call_ms E 0x8d2ec (x_p xc + 1) (Z_to_bv 64 0x8d2ec) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                                 (Z_to_bv 64 ((pe_VEP E + 224) / 8 + 2147450880)) (Z_to_bv 64 143872) (Z_to_bv 64 144000)
                                 t3 t4 t5 t6 m4) md4) T.
    Proof.
      intros until t6. intros vv yf W PIc AINVc MDFc STc LQ PLTc EVA E0 AINV SBM MU WM WZ STK3 FRX AOBJ3
             AINV4 MI4 MDF4 ST4 HENV4 VEPO4 FS4 TC4 SCC4 PCC4 OUT4 VI4 CF4.   (* [comment removed for export] *)
      pose proof PIc as PIc0. subst W. unfold ERRNOA in MU, WZ.
      world_open PE PIc AINVc. unfold call_ms. cbv zeta. rewrite EFP in *.
      clear VEPC FR STK MI SHV0. unfold oibuf in *.
      rewrite EVA in VA. (first [ dand5 VA as ANZ AOBJc ASZ ALEN AAP | destruct VA as (ANZ & AOBJc & ASZ & ALEN & AAP) ]).
      (first [ pose proof (AOBJc) as dR_2; dand5 dR_2 as _ AVIc LAS LAB _ | pose proof AOBJc as (_ & AVIc & LAS & LAB & _) ]). (first [ pose proof (AVIc) as dR_3; dand7 dR_3 as Vsz Vlen _ _ _ Vb0 _ | pose proof AVIc as (Vsz & Vlen & _ & _ & _ & Vb0 & _) ]).
      assert (EDS : DOINCL_STACK = 8768) by (vm_compute; reflexivity). rewrite EDS in CF4.
      assert (WIN : alloc_ceiling <= pe_sp E - 304 - 8768) by (klia LOP CEIL).
      assert (W0 : 0 <= 8768) by (clear; lia).
      destruct (ATTRST I ltac:(right; rewrite EVA; discriminate)) as [EAT MH].
      assert (DI : x_v xc Fdostuff = vi_do_include VIA).
      { unhide ATTR. clear - ATTR EAT. destruct ATTR as [A0|(A1 & A2 & A3)]; [| exact A2].
        exfalso. rewrite A0 in EAT. cbn [vi_tbl_attr_include VIA] in EAT. unfold TBL_attr_include in EAT. lia. }
      (* [comment removed for export] *)
      assert (VSBO3 : vsb_obj LPA Ac (aview Ac m) (pe_S E) (x_vv xc) false)
        by (eapply (vsb_obj_storesx _ _ _ _ _ _ _ PE0 AINVc HFR MU WM WZ); [in_list| in_list| exact VSBO]).
      assert (DATA3 : data_obj LPA Ac (aview Ac m) (pe_DATA E) (pe_inp E))
        by (eapply (data_obj_storesx _ _ _ _ _ _ _ PE0 AINVc HFR MU WM WZ); [in_list| exact DATA]).
      assert (SS3 : stack_shadow LPA (aview Ac m) (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64))
        by (eapply (stack_shadow_storesx _ _ _ _ _ _ _ PE0 AINVc HFR MU WM WZ); exact SS).
      assert (IB : match x_vi xc with Some yi => a_live Ac (x_v xc Finclude_src) = Some 40 /\ a_live Ac (vb_buf yi) = Some (vb_size yi) /\
                                               0 <= vb_len yi /\ 0 <= vb_size yi /\ vb_size yi <= vb_len yi + 4096 | None => True end).
      { clear - VI; try pose proof alloc_ceiling_val. destruct (x_vi xc) as [yi|]; [| exact I]. (first [ dand5 VI as _ IO _ ISZ _ | destruct VI as (_ & IO & _ & ISZ & _) ]).
        (first [ pose proof (IO) as dR_5; dand5 dR_5 as _ VIi LIS LIB _ | pose proof IO as (_ & VIi & LIS & LIB & _) ]). unfold vsb_inv in VIi. refine (conj LIS (conj LIB _)). lia. }
      clear VSBO DATA SS HENV.
      unfold oabuf in *. rewrite ?EVA in *. cbn [oabuf x_va] in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI.
      (* [comment removed for export] *)
      set (Vx := fun a : Z => blk (pe_VEP E) 312 a \/ vsb_blocks (x_v xc Fattr_vsb) yf a
                           \/ match x_vi xc with Some yi => vsb_blocks (x_v xc Finclude_src) yi a | None => False end
                           \/ (h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320)) in CF4.
      assert (CVx : vcover (pe_H E) Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E] Vx).
      { intros a [X|[X|[X|X]]].
        - eapply cover_blk; [exact LVEP| wz_not_in| exact X].
        - subst yf. unfold vsb_blocks in X. cbn [vb_buf vb_size vsb_set_flags] in X. destruct X as [X|X].
          + eapply cover_newblk; [exact LAS| wz_not_in| exact X].
          + eapply cover_newblk; [exact LAB| wz_not_in| exact X].
        - clear - X IB D_IS D_IB D_ID D_IBS D_IBB D_IBD; try pose proof alloc_ceiling_val. unfold oibuf in *. destruct (x_vi xc) as [yi|]; [| destruct X].
          (first [ dand3 IB as LIS LIB _ | destruct IB as (LIS & LIB & _) ]).
          destruct X as [X|X]; [eapply cover_newblk; [exact LIS| wz_not_in| exact X] | eapply cover_newblk; [exact LIB| wz_not_in| exact X]].
        - apply cover_vsc. exact X. }
      (* [comment removed for export] *)
      assert (FR4 : rw_cells rsegs (aview A4 m4) (pe_sp E - 304) (pframe E fj0 fj8)).
      { eapply (pframe_call E Ac A4 m md _ _ _ _ _ _ fj0 fj8);
          [exact PE| exact AINV| exact CF4| exact HFR| exact WIN| exact W0| unfold pe_fp, PARSE_FRAME; klia WIN| exact CVx| unfold pframe; cbv zeta; exact FRX]. }
      assert (SS4 : stack_shadow LPA (aview A4 m4) (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64)).
      { eapply (stack_shadow_call (pe_H E) Ac A4 m md _ _ _ _ _ _ AINV CF4 HFR WIN); [exact CVx| rewrite PARSE_STACK_val; klia LOP CEIL ACV| exact SS3]. }
      pose proof (proj1 HENV4) as HFR4.
      (first [ dand4 VEPO4 as LVEP4 VEPC4 _ _ | destruct VEPO4 as (LVEP4 & VEPC4 & _ & _) ]).
      pose proof (as_live_shadow LPA _ _ _ _ 312 AINV4 LVEP4) as SHV4. fold_cl_segs. fold_aview.
      change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV4. rewrite <- EzsV in SHV4.
      (* [comment removed for export] *)
      assert (CFh : cframe LPA (owned (pe_A0 E)) (owned Ac) (pe_sp E) PARSE_STACK (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E))
                           (parse_new (x_v xc) (x_vv xc) (Some y) (x_vio xc)) (pe_v0 E) (aview Ac m)).
      { eapply (cframe_after _ _ _ _ _ _ (pe_v0 E) (aview Ac mc));
          [ exact CF | exact MU
          | intros a__ Ha__ NO__; cbn [outside] in NO__; change (cl_errno LPA) with 6193972;
            unfold parse_changed, parse_new, vsb_blocks;
            assert (CASES : (pe_VEP E <= a__ < pe_VEP E + 312) \/ (pe_sp E - 304 - 64 <= a__ < pe_sp E - 304) \/
                            (x_v xc Fattr_vsb <= a__ < x_v xc Fattr_vsb + 40) \/ (vb_buf y <= a__ < vb_buf y + vb_size y) \/
                            (6193972 <= a__ < 6193972 + 4) \/ (h_vsc (pe_H E) + 1304 <= a__ < h_vsc (pe_H E) + 1320))
              by (clear - Ha__ NO__; lia);
            clear NO__; destruct CASES as [X|[X|[X|[X|[X|X]]]]];
            [ right; left; left; unfold blk; split; [klia VEPlo| exact X]
            | left; rewrite PARSE_STACK_val; klia X
            | right; right; left; right; left; left; unfold newblk, blk; left; split; [exact ANZ| exact X]
            | right; right; left; right; left; right; unfold newblk, blk; left; split; [klia Vb0| exact X]
            | right; right; right; exact X
            | right; left; right; right; right; exact X ]
          | eapply parse_window_mapped; [exact PE| exact STK3| exact FRX] ]. }
      (* [comment removed for export] *)
      assert (LK : forall p k, a_live Ac p = Some k -> p <> x_v xc Fattr_vsb -> p <> vb_buf y ->
                   ~ (match x_vi xc with Some yi => p = x_v xc Finclude_src \/ p = vb_buf yi | None => False end) ->
                   a_live A4 p = Some k).
      { intros p k Hp N1 N2 NI. clear - Hp N1 N2 NI OUT4; try pose proof alloc_ceiling_val.
        destruct OUT4 as [(_ & _ & _ & LQA & _)|[(_ & _ & _ & _ & _ & DI2 & LQA)|[(_ & _ & _ & _ & _ & _ & _ & LQA)|(_ & ic & _ & _ & _ & _ & _ & _ & _ & LQA)]]].
        - rewrite LQA. exact Hp.
        - destruct (x_vi xc) as [yi|]; [| destruct DI2].
          rewrite LQA; [exact Hp| exact N1| exact N2| intros ->; apply NI; left; reflexivity| intros ->; apply NI; right; reflexivity].
        - rewrite LQA; [exact Hp| exact N1| exact N2].
        - rewrite LQA; [exact Hp| exact N1| exact N2]. }
      assert (NIX : forall p, p <> x_v xc Finclude_src -> p <> match x_vi xc with Some yi => vb_buf yi | None => 0 end ->
                    ~ (match x_vi xc with Some yi => p = x_v xc Finclude_src \/ p = vb_buf yi | None => False end)).
      { clear. intros p N1 N2. destruct (x_vi xc) as [yi|]; [| intros X; exact X]. intros [X|X]; [exact (N1 X)| exact (N2 X)]. }
      assert (LVS4 : a_live A4 (pe_S E) = Some 40)
        by (apply (LK _ _ LVS); [exact (not_eq_sym D_AS)| exact (not_eq_sym D_ABS)| apply NIX; [exact (not_eq_sym D_IS)| exact (not_eq_sym D_IBS)]]).
      assert (LVB4 : a_live A4 (vb_buf (x_vv xc)) = Some (vb_size (x_vv xc)))
        by (apply (LK _ _ LVB); [exact (not_eq_sym D_AB)| exact (not_eq_sym D_ABB)| apply NIX; [exact (not_eq_sym D_IB)| exact (not_eq_sym D_IBB)]]).
      assert (LDATA4 : a_live A4 (pe_DATA E) = Some (Z.of_nat (length (pe_inp E))))
        by (apply (LK _ _ LDATA); [exact (not_eq_sym D_AD)| exact (not_eq_sym D_ABD)| apply NIX; [exact (not_eq_sym D_ID)| exact (not_eq_sym D_IBD)]]).
      assert (WAL4 : a_live A4 (pe_wa E) = Some 40)
        by (apply (LK _ _ WAL); [exact (not_eq_sym D_AW)| exact (not_eq_sym D_ABW)| apply NIX; [exact (not_eq_sym D_IW)| exact (not_eq_sym D_IBW)]]).
      assert (DATA4 : data_obj LPA A4 (aview A4 m4) (pe_DATA E) (pe_inp E)).
      { eapply (data_obj_call (pe_H E) Ac A4 m md _ _ _ _ _ _ AINV CF4 HFR WIN); [exact CVx| in_list| exact LDATA4| exact DATA3]. }
      assert (VSBO4 : vsb_obj LPA A4 (aview A4 m4) (pe_S E) (x_vv xc) false).
      { eapply (vsb_obj_call (pe_H E) Ac A4 m md _ _ _ _ _ _ AINV CF4 HFR WIN); [exact CVx| in_list| in_list| exact LVS4| exact LVB4| exact VSBO3]. }
      clear VSBO3 DATA3 SS3.
      (* [comment removed for export] *)
      assert (CFc : forall vi5 : option vsb_rec,
                (forall a, match vi5 with Some z => vsb_blocks (v4 Finclude_src) z a | None => False end -> Vx a) ->
                cframe LPA (owned (pe_A0 E)) (owned A4) (pe_sp E) PARSE_STACK (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E))
                       (parse_new v4 (x_vv xc) None (option_map (fun z => (z, true)) vi5)) (pe_v0 E) (aview A4 m4)).
      { intros vi5 H5.
        pose proof (cframe_step_call E xc (PST (x_p xc) S_InTag v4 (x_tag xc) (x_q xc) (x_vv xc) None vi5) Ac A4 (aview Ac m) (aview A4 m4) (pe_sp E - 304) 8768) as STEP.
        unfold x_vio in STEP. cbn [x_v x_vv x_va x_vi x_p x_st] in STEP.
        eapply STEP;
          [ rewrite EVA; exact CFh | exact CF4 | rewrite PARSE_STACK_val; klia W0 | klia W0
          | eapply parse_window_mapped; [exact PE| exact ST4| exact FR4]
          | intros a Ha; unfold pzone, parse_changed, parse_new, x_vio; rewrite EVA; cbn [option_map];
            destruct Ha as [Ha|[Ha|[Ha|Ha]]];
            [ left; left; exact Ha
            | right; right; left; revert Ha; subst yf; unfold vsb_blocks; cbn [vb_buf vb_size vsb_set_flags]; intros Ha; exact Ha
            | right; right; right; revert Ha; clear; destruct (x_vi xc); intros Ha; exact Ha
            | left; right; right; right; exact Ha ]
          | intros a Ha; unfold parse_new in Ha; destruct Ha as [Ha|[Ha|Ha]];
            [ right; unfold pzone, parse_new; right; left; exact Ha
            | destruct Ha
            | right; unfold pzone; (* [comment removed for export] *)
              pose proof (H5 a ltac:(revert Ha; clear; destruct vi5; cbn [option_map]; intros Ha; exact Ha)) as VX;
              subst Vx; cbv beta in VX; unfold parse_changed, parse_new, x_vio; rewrite EVA; cbn [option_map];
              destruct VX as [X|[X|[X|X]]];
              [ left; left; exact X
              | right; right; left; revert X; subst yf; unfold vsb_blocks; cbn [vb_buf vb_size vsb_set_flags]; intros X; exact X
              | right; right; right; revert X; clear; destruct (x_vi xc); intros X; exact X
              | left; right; right; right; exact X ] ] ]. }
      (* [comment removed for export] *)
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A4 m4)) as MU5. pose proof (wmono_refl rsegs (aview A4 m4)) as WM5.
      assert (WZ5 : wzone E A4 [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; vb_buf y; x_v xc Finclude_src;
                                 match x_vi xc with Some yi => vb_buf yi | None => 0 end] [(pe_VEP E, pe_VEP E + 312)]).
      { cbn [wzone]. split; [| exact I]. left. exists (pe_VEP E), 312. split; [exact LVEP4|]. split; [wz_not_in| clear; lia]. }
      assert (CFP5 : client_fp LPA A4 (aview A4 m4) [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR4| exact ST4| unfold pframe; cbv zeta; exact FR4| exact WZ5]).
      unfold vep_cells in VEPC4. unfold pframe in FR4. cbv zeta in FR4.
      pose proof (rw_cells_bound _ _ _ _ VEPC4) as VEPB4.
      hide_neqs.
      ago AINV4. fold_cl_segs.
      (* [comment removed for export] *)
      vrechk SHV4 EzsV (pe_VEP E + 224) 8 0.
      (* [comment removed for export] *)
      zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      astop AINV4 MU5 WM5 CFP5. fold_cl_segs.
      lazymatch goal with A5 : ainv A4 ?m5 ?md5, SB5 : same_but_materialized md4 ?md5 |- srealizes _ (mkCfg (MS _ _ _ _ _ ?m5 _) ?md5) _ =>
        rename A5 into AINV5; rename SB5 into SBM5; rename m5 into mf; rename md5 into mdf end.
      unhide_neqs.
      assert (EVSC : h_vsc (pe_H E) = h_ff (pe_H E) + 32) by reflexivity.
      (* [comment removed for export] *)
      assert (KEEP4 : forall p k, a_live (pe_A0 E) p = Some k -> p <> pe_b E -> a_live A4 p = Some k).
      { intros p k Lp NBp. pose proof (KEEP p k Lp NBp) as LA. apply (LK _ _ LA).
        - intros ->. destruct (NEW (x_v xc Fattr_vsb) ltac:(unfold parse_blocks; right; left; left; reflexivity)) as [X|X]; [exact (NBp X)| rewrite X in Lp; discriminate Lp].
        - intros ->. destruct (NEW (vb_buf y) ltac:(unfold parse_blocks; right; left; right; reflexivity)) as [X|X]; [exact (NBp X)| rewrite X in Lp; discriminate Lp].
        - clear - NEW Lp NBp. unfold x_vio in NEW. destruct (x_vi xc) as [yi|]; [| intros X; exact X]. intros [-> | ->].
          + destruct (NEW (x_v xc Finclude_src) ltac:(unfold parse_blocks; cbn [option_map]; right; right; left; reflexivity)) as [X|X]; [exact (NBp X)| rewrite X in Lp; discriminate Lp].
          + destruct (NEW (vb_buf yi) ltac:(unfold parse_blocks; cbn [option_map]; right; right; right; reflexivity)) as [X|X]; [exact (NBp X)| rewrite X in Lp; discriminate Lp]. }
      assert (HENV5 : henv_ok LPA VIA (pe_H E) A4 (aview A4 mf)).
      { eapply (henv_stores _ _ _ _ _ _ _ PE0 AINV4 HFR4 MU5 WM5 WZ5); [| exact HENV4].
        intros a Ha. cbn [outside]. unhide DJfV. klia Ha DJfV EVSC. }
      assert (VSBO5 : vsb_obj LPA A4 (aview A4 mf) (pe_S E) (x_vv xc) false)
        by (eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV4 HFR4 MU5 WM5 WZ5); [in_list| in_list| exact VSBO4]).
      assert (DATA5 : data_obj LPA A4 (aview A4 mf) (pe_DATA E) (pe_inp E))
        by (eapply (data_obj_stores _ _ _ _ _ _ _ PE0 AINV4 HFR4 MU5 WM5 WZ5); [in_list| exact DATA4]).
      assert (SS5 : stack_shadow LPA (aview A4 mf) (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64))
        by (eapply (stack_shadow_stores _ _ _ _ _ _ _ PE0 AINV4 HFR4 MU5 WM5 WZ5); exact SS4).
      assert (MAP5 : mapped (aview A4 mf) (pe_sp E - PARSE_STACK) PARSE_STACK)
        by (eapply parse_window_mapped; [exact PE| exact ST4| unfold pframe; cbv zeta; exact FR4]).
      assert (FS5 : frames_same (pe_A0 E) A4) by (intros ff; rewrite (FS4 ff); apply FRS).
      assert (TC5 : a_tinycred A4 = a_tinycred (pe_A0 E)) by (rewrite TC4; exact TC).
      assert (PYF : vsb_pot yf = vsb_pot y) by reflexivity. assert (LYF : vb_len yf = vb_len y) by reflexivity.
      assert (SYF : vb_size yf = vb_size y) by reflexivity. assert (BYF : vb_buf yf = vb_buf y) by reflexivity.
      pose proof (vsb_pot_len y ASZ ltac:(klia Vlen) ltac:(klia Vsz)) as PLa.
      (* [comment removed for export] *)
      assert (CF5 : forall (st5 : vstate) (vi5 : option vsb_rec),
                (forall a, match vi5 with Some z => vsb_blocks (v4 Finclude_src) z a | None => False end -> Vx a) ->
                cframe LPA (owned (pe_A0 E)) (owned A4) (pe_sp E) PARSE_STACK (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E))
                       (parse_new (fupd v4 Fattr_vsb 0) (x_vv xc) None (option_map (fun z => (z, true)) vi5)) (pe_v0 E) (aview A4 mf)).
      { intros st5 vi5 H5.
        pose proof (cframe_step_stores E (PST (x_p xc) S_InTag v4 (x_tag xc) (x_q xc) (x_vv xc) None vi5)
                      (PST (x_p xc + 1) st5 (fupd v4 Fattr_vsb 0) (x_tag xc) (x_q xc) (x_vv xc) None vi5) A4 (aview A4 m4) (aview A4 mf)
                      [(pe_VEP E, pe_VEP E + 312)]) as STEP5.
        unfold x_vio in STEP5. cbn [x_v x_vv x_va x_vi x_p x_st option_map] in STEP5.
        eapply STEP5;
          [ exact (CFc vi5 H5) | exact MU5
          | w_in_zone_tac; left; left; unfold blk; split; [klia VEPlo| exact Ha]
          | exact MAP5
          | intros a Ha; unfold pzone; right; unfold parse_new, x_vio; cbn [x_v x_vv x_va x_vi option_map];
            unfold parse_new in Ha; destruct Ha as [Ha|[Ha|Ha]];
            [ left; exact Ha | destruct Ha | right; right; revert Ha; clear; destruct vi5; cbn [option_map fupd vf_beq vf_index N.eqb Pos.eqb]; intros Ha; exact Ha ] ]. }
      clear CFc.
      destruct OUT4 as [(VIN & EV4 & EVI4 & LQA & LBQ & NLQ)|[(VINN & EV4 & EVI4 & DA & DB & DI2 & LQA)|[(VIN & EV4 & EVI4 & DA & DB & LBQ & NLQ & LQA)|(HIT4 & ic & ICB & EV4 & EVI4 & DA & DB & LBQ & NLQ & LQA)]]]; subst vi4 v4.
      - (* [comment removed for export] *)
        rewrite VIN in *. cbn [option_map] in CF5.
        set (x5 := PST (x_p xc + 1) S_InTag (fupd (fupd (fupd vv Finclude_src (x_v xc Fattr_vsb)) Fattr_vsb 0) Fattr_vsb 0)
                       (x_tag xc) (x_q xc) (x_vv xc) None (Some yf)).
        eapply (KL x5 A4 _ _);
          [ | exact AINV5
          | eapply amd_frame_sbm_r; [eapply amd_frame_trans; [eapply amd_frame_sbm_r; [exact MDFc| exact SBM]| exact MDF4]| exact SBM5]
          | subst x5; psimp; intros _; split; [| discriminate]; rewrite PHI; unfold phi, rank; psimp; klia LQ ].
        subst x5 vv. apply Build_pinv; psimp.
        all: lazymatch goal with
             | |- 0 <= _ /\ 0 <= _ /\ _ <= _ - pe_DATA _ => rewrite ?LYF; klia Vlen ALEN
             | |- _ - _ <= a_seccred _ <= _ => idtac
             | |- 0 <> 0 -> _ => let X := fresh in intros X; exfalso; exact (X eq_refl)
             | |- _ => pinv_close PE0 AINV4 HFR4 MU5 WM5 WZ5
             end.
        + (* [comment removed for export] *) klia VERP.
        + (* [comment removed for export] *) klia PLTc.
        + (* [comment removed for export] *) revert OUT Vlen. unfold oacost, oicost. rewrite EVA, VIN. cbn [x_va x_vi vb_len vsb_set_flags]. rewrite ?LYF. clear. intros; lia.
        + (* [comment removed for export] *) refine (conj ANZ (conj _ (conj E0 (conj ASZ (conj _ (conj AAP I)))))); [| rewrite LYF; klia ALEN].
          psimp_in VI4. (first [ dand3 VI4 as _ IO4 _ | destruct VI4 as (_ & IO4 & _) ]).
          eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV4 HFR4 MU5 WM5 WZ5); [in_list| in_list| exact IO4].
        + (* [comment removed for export] *) rewrite LBQ, LB. unfold world_bytes, x_vio. rewrite VIN. cbn [option_map]. rewrite ?SYF. clear. lia.
        + (* [comment removed for export] *) rewrite NLQ, NL. unfold world_nlive, x_vio. rewrite VIN. cbn [option_map]. clear. lia.
        + (* [comment removed for export] *) intros p Hp. apply NEW. revert Hp. unfold parse_blocks, x_vio. rewrite VIN. cbn [option_map fupd vf_beq vf_index N.eqb Pos.eqb]. rewrite ?BYF. clear.
          intros [Hp|[[]|Hp]]; [left; exact Hp| right; left; exact Hp].
        + (* [comment removed for export] *) apply (CF5 S_InTag (Some yf)). intros a Ha. subst Vx. cbv beta. right. left. psimp_in Ha. exact Ha.
        + (* [comment removed for export] *) rewrite SCC4, PYF, LYF. revert SC Vlen ALEN. clear. intros SC Vlen ALEN.
          assert (MONO : (x_p xc - pe_DATA E - vb_len y - 0) / 4096 <= (x_p xc + 1 - pe_DATA E - 0 - vb_len y) / 4096) by (apply Z.div_le_mono; lia).
          lia.
      - (* [comment removed for export] *)
        destruct (x_vi xc) as [yi|] eqn:EVI; [| destruct DI2]. (first [ dand4 DI2 as DIS DIB LBQ NLQ | destruct DI2 as (DIS & DIB & LBQ & NLQ) ]). clear VINN.
        cbn [option_map] in *. (first [ dand5 IB as LIS LIB ILEN ISZ0 ISZ | destruct IB as (LIS & LIB & ILEN & ISZ0 & ISZ) ]).
        set (x5 := PST (x_p xc + 1) S_TagError (fupd (fupd (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0) Finclude_src 0) Fattr_vsb 0)
                       (x_tag xc) (x_q xc) (x_vv xc) None None).
        eapply (KL x5 A4 _ _);
          [ | exact AINV5
          | eapply amd_frame_sbm_r; [eapply amd_frame_trans; [eapply amd_frame_sbm_r; [exact MDFc| exact SBM]| exact MDF4]| exact SBM5]
          | subst x5; psimp; intros _; split; [| discriminate]; rewrite PHI; unfold phi, rank; psimp; klia LQ ].
        subst x5 vv. apply Build_pinv; psimp.
        all: lazymatch goal with
             | |- 0 <= _ /\ 0 <= _ /\ _ <= _ - pe_DATA _ => klia PLTc VERP
             | |- _ - _ <= a_seccred _ <= _ => idtac
             | |- 0 <> 0 -> _ => let X := fresh in intros X; exfalso; exact (X eq_refl)
             | |- _ => pinv_close PE0 AINV4 HFR4 MU5 WM5 WZ5
             end.
        + (* [comment removed for export] *) klia VERP.
        + (* [comment removed for export] *) klia PLTc.
        + (* [comment removed for export] *) revert OUT Vlen ILEN. unfold oacost, oicost. rewrite EVA, EVI. cbn [x_va x_vi vb_len vsb_set_flags]. rewrite ?LYF. clear. intros; lia.
        + (* [comment removed for export] *) rewrite LBQ, LB. unfold world_bytes, x_vio. rewrite ?EVI. cbn [option_map]. rewrite ?SYF. clear. lia.
        + (* [comment removed for export] *) rewrite NLQ, NL. unfold world_nlive, x_vio. rewrite ?EVI. cbn [option_map]. clear. lia.
        + (* [comment removed for export] *) intros p Hp. apply NEW. revert Hp. unfold parse_blocks. clear. intros [Hp|[[]|[]]]. left; exact Hp.
        + (* [comment removed for export] *) apply (CF5 S_TagError None). intros a Ha. destruct Ha.
        + (* [comment removed for export] *) rewrite SCC4. revert SC Vlen ALEN PLa ILEN ISZ0 ISZ WL. clear. intros.
          pose proof (vsb_pot_len yi ISZ ILEN ISZ0) as PLi.
          pose proof (div4096_add (vb_len y) (vb_len yi) ltac:(lia) ltac:(lia)) as D1.
          pose proof (div4096_add (vb_len y + vb_len yi) (x_p xc - pe_DATA E - vb_len y - vb_len yi) ltac:(lia) ltac:(lia)) as D2.
          replace (vb_len y + vb_len yi + (x_p xc - pe_DATA E - vb_len y - vb_len yi)) with (x_p xc - pe_DATA E) in D2 by lia.
          assert (MONO : (x_p xc - pe_DATA E) / 4096 <= (x_p xc + 1 - pe_DATA E - 0 - 0) / 4096) by (apply Z.div_le_mono; lia).
          lia.
      - (* [comment removed for export] *)
        rewrite VIN in *. cbn [option_map] in *.
        set (x5 := PST (x_p xc + 1) S_TagError (fupd (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0) Fattr_vsb 0)
                       (x_tag xc) (x_q xc) (x_vv xc) None None).
        eapply (KL x5 A4 _ _);
          [ | exact AINV5
          | eapply amd_frame_sbm_r; [eapply amd_frame_trans; [eapply amd_frame_sbm_r; [exact MDFc| exact SBM]| exact MDF4]| exact SBM5]
          | subst x5; psimp; intros _; split; [| discriminate]; rewrite PHI; unfold phi, rank; psimp; klia LQ ].
        subst x5 vv. apply Build_pinv; psimp.
        all: lazymatch goal with
             | |- 0 <= _ /\ 0 <= _ /\ _ <= _ - pe_DATA _ => klia PLTc VERP
             | |- _ - _ <= a_seccred _ <= _ => idtac
             | |- 0 <> 0 -> _ => let X := fresh in intros X; exfalso; exact (X eq_refl)
             | |- _ => pinv_close PE0 AINV4 HFR4 MU5 WM5 WZ5
             end.
        + (* [comment removed for export] *) klia VERP.
        + (* [comment removed for export] *) klia PLTc.
        + (* [comment removed for export] *) revert OUT Vlen. unfold oacost, oicost. rewrite EVA, VIN. cbn [x_va x_vi vb_len vsb_set_flags]. rewrite ?LYF. clear. intros; lia.
        + (* [comment removed for export] *) rewrite LBQ, LB. unfold world_bytes, x_vio. rewrite VIN. cbn [option_map]. rewrite ?SYF. clear. lia.
        + (* [comment removed for export] *) rewrite NLQ, NL. unfold world_nlive, x_vio. rewrite VIN. cbn [option_map]. clear. lia.
        + (* [comment removed for export] *) intros p Hp. apply NEW. revert Hp. unfold parse_blocks. clear. intros [Hp|[[]|[]]]. left; exact Hp.
        + (* [comment removed for export] *) apply (CF5 S_TagError None). intros a Ha. destruct Ha.
        + (* [comment removed for export] *) rewrite SCC4. revert SC Vlen ALEN PLa. clear. intros.
          pose proof (div4096_add (vb_len y) (x_p xc - pe_DATA E - vb_len y - 0) ltac:(lia) ltac:(lia)) as D2.
          replace (vb_len y + (x_p xc - pe_DATA E - vb_len y - 0)) with (x_p xc - pe_DATA E) in D2 by lia.
          assert (MONO : (x_p xc - pe_DATA E) / 4096 <= (x_p xc + 1 - pe_DATA E - 0 - 0) / 4096) by (apply Z.div_le_mono; lia).
          lia.
      - (* [comment removed for export] *)
        set (x5 := PST (x_p xc + 1) S_InTag (fupd (fupd (fupd vv Finclude_continue ic) Fattr_vsb 0) Fattr_vsb 0)
                       (x_tag xc) (x_q xc) (x_vv xc) None (x_vi xc)).
        eapply (KL x5 A4 _ _);
          [ | exact AINV5
          | eapply amd_frame_sbm_r; [eapply amd_frame_trans; [eapply amd_frame_sbm_r; [exact MDFc| exact SBM]| exact MDF4]| exact SBM5]
          | subst x5; psimp; intros _; split; [| discriminate]; rewrite PHI; unfold phi, rank; psimp; klia LQ ].
        subst x5 vv. apply Build_pinv; psimp.
        all: lazymatch goal with
             | |- 0 <= _ /\ 0 <= _ /\ _ <= _ - pe_DATA _ => klia WL Vlen
             | |- _ - _ <= a_seccred _ <= _ => idtac
             | |- 0 <> 0 -> _ => let X := fresh in intros X; exfalso; exact (X eq_refl)
             | |- _ => pinv_close PE0 AINV4 HFR4 MU5 WM5 WZ5
             end.
        + (* [comment removed for export] *) klia VERP.
        + (* [comment removed for export] *) klia PLTc.
        + (* [comment removed for export] *) revert OUT Vlen. unfold oacost, oicost. rewrite EVA. cbn [x_va x_vi vb_len vsb_set_flags]. rewrite ?LYF. clear. destruct (x_vi xc); intros; lia.
        + (* [comment removed for export] *) psimp_in VI4. destruct (x_vi xc) as [yi|]; [| exact VI4].
          (first [ dand7 VI as I1 _ I3 I4 I5 I6 _ | destruct VI as (I1 & _ & I3 & I4 & I5 & I6 & _) ]). (first [ dand3 VI4 as _ IO4 _ | destruct VI4 as (_ & IO4 & _) ]).
          refine (conj I1 (conj _ (conj I3 (conj I4 (conj _ (conj I6 I)))))); [| klia I5].
          eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV4 HFR4 MU5 WM5 WZ5); [in_list| in_list| exact IO4].
        + (* [comment removed for export] *) rewrite LBQ, LB. unfold world_bytes, x_vio. rewrite ?SYF. clear. destruct (x_vi xc); cbn [option_map]; lia.
        + (* [comment removed for export] *) rewrite NLQ, NL. unfold world_nlive, x_vio. clear. destruct (x_vi xc); cbn [option_map]; lia.
        + (* [comment removed for export] *) intros p Hp. apply NEW. revert Hp. unfold parse_blocks, x_vio. clear. destruct (x_vi xc); cbn [option_map fupd vf_beq vf_index N.eqb Pos.eqb]; intros [Hp|[[]|Hp]];
            first [left; exact Hp| right; right; exact Hp| destruct Hp].
        + (* [comment removed for export] *) apply (CF5 S_InTag (x_vi xc)). intros a Ha. subst Vx. cbv beta. right. right. left.
          revert Ha. clear. destruct (x_vi xc); cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; intros Ha; exact Ha.
        + (* [comment removed for export] *) rewrite SCC4. revert SC Vlen ALEN PLa WL. clear. destruct (x_vi xc) as [yi|]; intros.
          * pose proof (div4096_add (vb_len y) (x_p xc - pe_DATA E - vb_len y - vb_len yi) ltac:(lia) ltac:(lia)) as D2.
            replace (vb_len y + (x_p xc - pe_DATA E - vb_len y - vb_len yi)) with (x_p xc - pe_DATA E - vb_len yi) in D2 by lia.
            assert (MONO : (x_p xc - pe_DATA E - vb_len yi) / 4096 <= (x_p xc + 1 - pe_DATA E - 0 - vb_len yi) / 4096) by (apply Z.div_le_mono; lia).
            lia.
          * pose proof (div4096_add (vb_len y) (x_p xc - pe_DATA E - vb_len y - 0) ltac:(lia) ltac:(lia)) as D2.
            replace (vb_len y + (x_p xc - pe_DATA E - vb_len y - 0)) with (x_p xc - pe_DATA E - 0) in D2 by lia.
            assert (MONO : (x_p xc - pe_DATA E - 0) / 4096 <= (x_p xc + 1 - pe_DATA E - 0 - 0) / 4096) by (apply Z.div_le_mono; lia).
            lia.
    Qed.
  End X.
End S.
End A_PH76v.


Module A_PHv1x.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient ATac AIcpm9j AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_Img A_ImgAny A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDswi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDswi A_VEr47.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDncj.A_PPutc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App.A_Fpx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDswi.A_PKitX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDswi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHmhz.A_PHd8z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHmhz.A_PH76v.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold vep_error_post, VEPERR_STACK, VSB_finish_post, FINISH_STACK, ASSERT_STACK, ERRNOA in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@ERR]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
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
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LOP; @CEIL; @VEPlo; @H; @ABlo; @SPR; @Alo; @V6; @G2; @Ha__; @H0; @H4; @TAG; @EVSC; @WL; @SPH; @ATlo; @ABUlo; @A16; @Ahi; @V1; @V2; @ACV; @VEPhi; @K; @Vlen; @SHSB; @SHBB; @AB16; @ABhi; @AVI; @LBS; @DJfV; @DJfA; @DJfAB; @OUT; @LB; @LB5; @NL; @NL5; @EAT; @KS; @SHAlo; @NO__; @X; @DLEN; @FRB; @Vsz; @SC; @PL_; @DA_; @MONO; @LQ])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
Local Tactic Notation "klia" ne_hyp_list(hs) := try (generalize alloc_ceiling_val); clear - hs; try pose proof alloc_ceiling_val as ACV__; lia.
(* [comment removed for export] *)
Tactic Notation "shadow_chkn" constr(SRC) constr(k) constr(U) integer(n) :=
  zstep; zstep; shadow_addr SRC k;
  lazymatch goal with |- evt ?segs ?Q _ =>
    eapply (evt_cut segs _ Q);
    [ zstep; do n zstep;
      let K := fresh "KS" in
      zstep; if_cases K; zify_cond K;
      [ first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ]
      | first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ] ]
    | let ms := fresh "ms" in let x := fresh "junk" in
      intros ms [x ->]; simp_regs ]
  end;
  shadow_cleanup.


Section S.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HVE : vep_error_stmt.
  Hypothesis HDS : VSB_destroy_stmt.
  Hypothesis HFI : VSB_finish_stmt.
  Hypothesis HDIA : vep_do_include_attr_stmt.

  Section X.
    Variables (E : penv) (x : pst) (T : TSet).
    Hypothesis PE : penv_ok E.
    Hypothesis PHI : phi E x = 16 * (pe_e E - x_p x) + 1.
    Hypothesis KL : latch_K E x T.

    #[using="KL PHI PE HDIA HFI HDS HVE"] Lemma av_finish : av_finish_T E x T.
    Proof.
      unfold av_finish_T. cbv zeta.
      intros xc Ac mc mdc m2 y ra a1 a2 a3 a4 a5 t5 t6 PIc AINVc MDFc STc LQ PLTc EVA MU12 WM12 CFP12 MI2 STK2 FRX VEPC2 SHVX.
      pose proof PIc as PIc0. unfold pframe in FRX.
      world_open PE PIc AINVc. rename FR into FRc. rename STK into STKc. clear VEPC MI.
      unfold loop_ms, S8. rewrite EFP in *.
      (* [comment removed for export] *)
      rewrite EVA in VA. (first [ dand5 VA as ANZ AOBJc ASZ ALEN AAP | destruct VA as (ANZ & AOBJc & ASZ & ALEN & AAP) ]).
      assert (WZ12 : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                              [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (AOBJ2 : vsb_obj LPA Ac m2 (x_v xc Fattr_vsb) y false)
        by (eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINVc HFR MU12 WM12 WZ12); [in_list| in_list| exact AOBJc]).
      (first [ pose proof ((vsb_obj_geom LPA Ac mc mdc _ _ _ AINVc AOBJc)) as dR_2; dand11 dR_2 as A16 Alo Ahi Aimg AB16 ABlo ABhi ABimg DSB _ _ | pose proof (vsb_obj_geom LPA Ac mc mdc _ _ _ AINVc AOBJc) as (A16 & Alo & Ahi & Aimg & AB16 & ABlo & ABhi & ABimg & DSB & _ & _) ]).
      (first [ pose proof (AOBJc) as dR_3; dand6 dR_3 as _ _ LAS LAB ASB _ | pose proof AOBJc as (_ & _ & LAS & LAB & ASB & _) ]).
      (first [ pose proof (AOBJ2) as dR_4; dand6 dR_4 as AVC AVI _ _ _ (bs & AU8 & LBS & _) | pose proof AOBJ2 as (AVC & AVI & _ & _ & _ & (bs & AU8 & LBS & _)) ]). fold_cl_segs.
      destruct (vsb_shadows LPA Ac mc mdc _ _ _ AINVc AOBJc) as [SHSa SHBa]. fold_cl_segs. fold_aview.
      unfold kHighMemBeg in Alo. all_app_facts.
      pose proof (shpat_sh_bound (Clg:=Clg) (x_v xc Fattr_vsb) 40 ltac:(klia Alo) ltac:(clear; lia) Ahi) as SHSB. rewrite SHMAX_val in SHSB.
      pose proof (shpat_sh_bound (Clg:=Clg) (vb_buf y) (vb_size y) ltac:(klia ABlo) ltac:(klia ABlo) ABhi) as SHBB. rewrite SHMAX_val in SHBB.
      eapply (bytes_at_munch LPA) in SHSa; [| exact MU12| intros a__ Ha__; cbn [outside]; klia Ha__ SHSB VEPlo].
      eapply (bytes_at_munch LPA) in SHBa; [| exact MU12| intros a__ Ha__; cbn [outside]; klia Ha__ SHBB VEPlo].
      pose proof (as_live_disjoint LPA Ac mc mdc _ _ _ _ AINVc LAS LVEP D_AV) as DXA.
      unfold oabuf in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI. rewrite EVA in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI.
      pose proof (as_live_disjoint LPA Ac mc mdc _ _ _ _ AINVc LAB LVEP D_ABV) as DXB.
      unfold vep_cells in VEPC2. psimp_in VEPC2.
      assert (SPR : 0 <= pe_sp E < 2^64) by (klia SPH LOP CEIL ACV).
      assert (NAI : x_v xc Finclude_src <> x_v xc Fattr_vsb /\ x_v xc Finclude_src <> vb_buf y /\
                    oibuf xc <> x_v xc Fattr_vsb /\ oibuf xc <> vb_buf y).
      { clear - VI D_AI D_AA; try pose proof alloc_ceiling_val as ACV__. unfold oibuf in *. destruct (x_vi xc) as [yi|].
        - exact (D_AI ltac:(discriminate) ltac:(discriminate)).
        - rewrite VI. (first [ pose proof ((D_AA ltac:(discriminate))) as dR_5; dand3 dR_5 as _ ATlo ABUlo | destruct (D_AA ltac:(discriminate)) as (_ & ATlo & ABUlo) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
      (first [ dand4 NAI as NIA NIB NBA NBB | destruct NAI as (NIA & NIB & NBA & NBB) ]).
      (* [comment removed for export] *)
      assert (MU : munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 304 - 64, pe_sp E - 304); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                          (vb_buf y, vb_buf y + vb_size y); (ERRNOA, ERRNOA + 4); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] (aview Ac mc) m2)
        by (eapply munch_weaken; [| exact MU12]; clear; unfold sub_fp; cbn [outside]; intros; lia).
      assert (MUa : munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 304 - 64, pe_sp E - 304); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                           (vb_buf y, vb_buf y + vb_size y); (ERRNOA, ERRNOA + 4)] (aview Ac mc) m2)
        by (eapply munch_weaken; [| exact MU12]; clear; unfold sub_fp; cbn [outside]; intros; lia).
      pose proof WM12 as WM.
      assert (WZ : wzonex E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Finclude_src; oibuf xc]
                     [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 304 - 64, pe_sp E - 304); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                      (vb_buf y, vb_buf y + vb_size y); (ERRNOA, ERRNOA + 4); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzonex_tac.
      assert (WZa : wzonex E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Finclude_src; oibuf xc]
                     [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 304 - 64, pe_sp E - 304); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                      (vb_buf y, vb_buf y + vb_size y); (ERRNOA, ERRNOA + 4)]) by wzonex_tac.
      assert (CFP : client_fpx Ac (aview Ac mc)
                     [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 304 - 64, pe_sp E - 304); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                      (vb_buf y, vb_buf y + vb_size y); (ERRNOA, ERRNOA + 4); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)])
        by (eapply wzonex_client_fpx; [exact PE| exact HFR| exact STKc| unfold pframe; cbv zeta; exact FRc| exact WZ]).
      pose proof MU12 as MUv. clear WM12 CFP12 WZ12. unfold ERRNOA in MU, MUa.
      destruct (rw_errno_any m2) as [e0 ERR].
      pose proof (cenv_intro Ac mc mdc AINVc) as CE. fold_aview.
      assert (CE2 : cenv m2)
        by (eapply cenv_munch; [exact CE| exact MUv| repeat (apply Forall_cons; [unfold const_free_ivl, CONSTS_TOP; cbn; klia VEPlo VEPhi|]); apply Forall_nil]).
      clear MUv MU12.
      (first [ pose proof (AVI) as dR_7; dand8 dR_7 as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | pose proof AVI as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
      rewrite <- EzsV in SHVX. clear SHV0.
      hide Aimg. hide ABimg. hide Verr. hide_neqs.
      (* [comment removed for export] *)
      zstep.
      icall (HFI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pe_F E) (pe_fc E) _ (x_v xc Fattr_vsb) y bs e0 (pe_lo E)) by
        (rewrite ?unsigned_lit by (klia SPR LOP CEIL ACV);
         lazymatch goal with
         | |- @eq (bv _) _ _ => reflexivity
         | |- rw_cells _ _ _ (vsb_cells _) => exact AVC
         | |- rw_cells _ _ _ [C4 _] => exact ERR
         | |- u8arr _ _ _ _ => exact AU8
         | |- vsb_inv _ _ => exact AVI
         | |- Z.of_nat _ = _ => exact LBS
         | |- shadowed _ _ _ 40 => exists (x_v xc Fattr_vsb), 40; split; [exact SHSa|]; split; [clear - A16; Z.div_mod_to_equations; lia| klia Alo Ahi]
         | |- shadowed _ _ _ (vb_size _) => exists (vb_buf y), (vb_size y); split; [exact SHBa|]; split; [clear - AB16; Z.div_mod_to_equations; lia| klia ABlo ABhi]
         | |- shadowed _ _ _ 4 => apply errno_shadowed; exact (proj1 CE2)
         | |- cenv _ => exact CE2
         | |- _ \/ _ => exact DSB
         | |- stk _ _ _ _ => exact STK2
         | |- mem_inv _ _ => exact MI2
         | |- app_range _ _ _ => first [assumption | exact ABlo_a]
         | |- _ mod 8 = 0 => clear - A16; Z.div_mod_to_equations; lia
         | |- _ => first [assumption | unfold kHighMemBeg, FINISH_STACK, ASSERT_STACK; klia Alo Ahi ABhi LOP CEIL ACV SPR]
         end).
      try clear AVC AU8 ERR STK2.
      lazymatch goal with X : rw_cells _ ?mq _ (vsb_cells _) |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into AVC3 end.
      lazymatch goal with X : u8arr _ ?mq (vb_buf _) _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into AU83 end.
      lazymatch goal with X : rw_cells _ ?mq 6193972 _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into ERR3 end.
      lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STK3 end.
      (* [comment removed for export] *)
      set (yf := vsb_set_flags y VSB_FLAGS_FIN).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
        assert (AOBJ3 : vsb_obj LPA Ac m3 (x_v xc Fattr_vsb) yf true) end.
      { subst yf. split; [exact AVC3|]. split; [| split; [exact LAS|]; split; [exact LAB|]; split; [exact ASB|]].
        - clear - AVI. unfold vsb_inv in *. cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf vsb_set_flags].
          (first [ dand6 AVI as V1 V2 V3 V4 V5 V6 | destruct AVI as (V1 & V2 & V3 & V4 & V5 & V6) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; try lia.
        - exists (upd bs (Z.to_nat (vb_len y)) (Z_to_bv 8 0)). cbn [vb_buf vb_size vb_len vsb_set_flags].
          split; [exact AU83|]. split; [rewrite upd_length; exact LBS|].
          intros _. apply nth_error_upd_same. clear - AVI LBS. unfold vsb_inv in AVI. lia. }
      (* [comment removed for export] *)
      unhide DJfV. unhide DJfS. unhide DJfB.
      pose proof (as_frame_blk_disjoint LPA _ _ _ _ HCLASS ageh _ _ AINVc HFh LAS) as DJfA.
      pose proof (as_frame_blk_disjoint LPA _ _ _ _ HCLASS ageh _ _ AINVc HFh LAB) as DJfAB.
      change (fsize HCLASS) with 8192 in DJfA, DJfAB.
      assert (EVSC : h_vsc (pe_H E) = h_ff (pe_H E) + 32) by reflexivity.
      pose proof (sh_boundL (Clg:=Clg) (h_ff (pe_H E)) 8192 ltac:(klia G2) ltac:(clear; lia) G3) as SHFB. rewrite SHMAX_val in SHFB.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
        assert (HENV3 : henv_ok LPA VIA (pe_H E) Ac m3)
          by (eapply (henv_storesx _ _ _ _ _ _ _ PE0 AINVc HFR MUa WM WZa);
              [intros a__ Ha__; cbn [outside]; unfold ERRNOA; klia Ha__ VEPhi VEPlo ACV EVSC G2 DJfV DJfA DJfAB Alo Ahi ABlo ABhi LOP CEIL SPR| exact HENV]) end.
      hide DJfV. hide DJfS. hide DJfB. clear MUa WZa.
      (* [comment removed for export] *)
      unhide Verr. pose proof Verr as E0.
      (* [comment removed for export] *)
      rewrite E0. change (vsb_result 0 0) with 0.
      zstep. kdead2.
      destruct (ATTRST I ltac:(right; rewrite EVA; discriminate)) as [EAT MH].
      assert (DI : x_v xc Fdostuff = vi_do_include VIA).
      { unhide ATTR. clear - ATTR EAT. destruct ATTR as [A0|(A1 & A2 & A3)]; [| exact A2].
        exfalso. rewrite A0 in EAT. cbn [vi_tbl_attr_include VIA] in EAT. unfold TBL_attr_include in EAT. lia. }
      (* [comment removed for export] *)
      zstep. vchk SHVX EzsV 8 0. zstep. rewrite DI. cbn [vi_do_include VIA].
      zstep. kdead2. zstep. zstep. zstep.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
        assert (VI3 : match x_vi xc with None => x_v xc Finclude_src = 0 | Some yi =>
                        x_v xc Finclude_src <> 0 /\ vsb_obj LPA Ac m3 (x_v xc Finclude_src) yi true /\ vb_error yi = 0 /\
                        vb_size yi <= vb_len yi + 4096 /\ vb_len yi <= x_p xc - pe_DATA E /\
                        vsb_apart (x_v xc Finclude_src) yi [pe_VEP E; pe_wa E; pe_DATA E; pe_S E; vb_buf (x_vv xc)] end);
        [ destruct (x_vi xc) as [yi|] eqn:EVI; [| exact VI]; (first [ dand7 VI as I1 I2 I3 I4 I5 I6 _ | destruct VI as (I1 & I2 & I3 & I4 & I5 & I6 & _) ]);
          refine (conj I1 (conj _ (conj I3 (conj I4 (conj I5 I6)))));
          eapply (vsb_obj_storesx _ _ _ _ _ _ _ PE0 AINVc HFR MU WM WZ); [in_list| in_list| exact I2] |];
        assert (VSBO3 : vsb_obj LPA Ac m3 (pe_S E) (x_vv xc) false)
          by (eapply (vsb_obj_storesx _ _ _ _ _ _ _ PE0 AINVc HFR MU WM WZ); [in_list| in_list| exact VSBO]);
        assert (DATA3 : data_obj LPA Ac m3 (pe_DATA E) (pe_inp E))
          by (eapply (data_obj_storesx _ _ _ _ _ _ _ PE0 AINVc HFR MU WM WZ); [in_list| exact DATA]);
        assert (SS3 : stack_shadow LPA m3 (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64))
          by (eapply (stack_shadow_storesx _ _ _ _ _ _ _ PE0 AINVc HFR MU WM WZ); exact SS)
      end.
      unfold oibuf in NBA, NBB, D_IBV, D_IBS, D_IBB, D_IBD, D_IBW.
      astopx AINVc MU WM CFP. fold_cl_segs.
      lazymatch goal with AINVs : ainv Ac ?ms ?mds |- srealizes _ (mkCfg (MS _ _ _ _ _ ?ms _) ?mds) _ =>
      eapply (HDIA (pe_VEP E) (fupd (fupd (x_v xc) Fattr_delim 0) Fstate (stA S_InTag)) (x_tag xc) (x_q xc) yf (x_vi xc) (pe_H E) (pe_lo E)
                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pe_F E) (pe_fc E) ms mds Ac T);
        [ exact AINVs | assumption | reflexivity | reflexivity
        | split; [exact LVEP|]; split; [unfold vep_cells; psimp; exact VEPC2|]; split; [exact TAG| exact PADS]
        | unfold vep_base; psimp; exact BASE
        | exact HENV3
        | psimp; cbn [vi_tbl_attr_include VIA] in MH |- *; exact MH
        | psimp; exact B_ic
        | psimp; exact ANZ
        | psimp; exact AOBJ3
        | subst yf; cbn [vb_error vsb_set_flags]; exact E0
        | psimp; exact D_AV
        | subst yf; cbn [vb_buf vsb_set_flags]; exact D_ABV
        | psimp; subst yf; cbn [vb_buf vsb_set_flags]; clear - VI3 D_IV D_IBV NIA NIB NBA NBB;
          destruct (x_vi xc) as [yi|]; [| exact VI3]; (first [ dand5 VI3 as Q1 Q2 Q3 Q4 Q5 | destruct VI3 as (Q1 & Q2 & Q3 & Q4 & Q5) ]);
          exact (conj Q1 (conj Q2 (conj Q3 (conj D_IV (conj D_IBV (conj NIA (conj NIB (conj NBA NBB))))))))
        | reflexivity
        | rewrite unsigned_lit by (klia SPR LOP CEIL ACV); rewrite Zminus_mod, SP16; reflexivity
        | rewrite unsigned_lit by (klia SPR LOP CEIL ACV); exact STK3
        | exact CEIL
        | rewrite unsigned_lit by (klia SPR LOP CEIL ACV); unfold_stacks; klia LOP
        | ]
      end.
      intros t0z t1z t2z a0z a1z a2z a3z a4z a5z a6z a7z t3z t4z t5z t6z A4 m4 md4 v4 vi4. cbv zeta.
      intros AINV4 MI4 MDF4 ST4 HENV4 VEPO4 FS4 TC4 SCC4 PCC4 OUT4 VI4 CF4.   (* [comment removed for export] *)
      rewrite unsigned_lit in ST4, CF4 by (klia SPR LOP CEIL ACV).
      replace (ret_pc (Z_to_bv 64 0x8d2ec)) with (Z_to_bv 64 0x8d2ec) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      lazymatch goal with AINVm : ainv Ac ?mm ?mdm, SBMm : same_but_materialized mdc ?mdm, MUm : munch _ (aview Ac mc) (aview Ac ?mm) |- _ =>
        eapply (av_ret E x T PE PHI KL xc Ac mc mdc mm mdm y _ _ A4 m4 md4 v4 vi4);
        [ exact PIc0 | exact AINVc | exact MDFc | exact STc | exact LQ | exact PLTc | exact EVA | exact E0
        | exact AINVm | exact SBMm | exact MUm | exact WM | exact WZ | exact STK3 | exact FRX | exact AOBJ3
        | exact AINV4 | exact MI4 | exact MDF4 | exact ST4 | exact HENV4 | exact VEPO4 | exact FS4 | exact TC4 | exact SCC4 | exact PCC4 (* [comment removed for export] *)
        | exact OUT4 | exact VI4 | exact CF4 ]
      end.
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HFI HDS"] Lemma av_gtfin : av_gtfin_T E x T.
    Proof.
      unfold av_gtfin_T. cbv zeta.
      intros xc Ac mc mdc m2 y ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 PIc AINVc MDFc STc LQ PLTc EVA MU12 WM12 MI2 STK2 FRX VEPC2 SHVX HENV2.
      pose proof PIc as PIc0. unfold pframe in FRX.
      world_open PE PIc AINVc. rename FR into FRc. rename STK into STKc. clear VEPC MI.
      unfold call_ms, S8. cbv zeta. rewrite EFP in *.
      (* [comment removed for export] *)
      rewrite EVA in VA. (first [ dand5 VA as ANZ AOBJc ASZ ALEN AAP | destruct VA as (ANZ & AOBJc & ASZ & ALEN & AAP) ]).
      assert (WZ12 : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                              [(pe_sp E - 304 - 64, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
      assert (AOBJ2 : vsb_obj LPA Ac m2 (x_v xc Fattr_vsb) y false)
        by (eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINVc HFR MU12 WM12 WZ12); [in_list| in_list| exact AOBJc]).
      (first [ pose proof ((vsb_obj_geom LPA Ac mc mdc _ _ _ AINVc AOBJc)) as dR_2; dand11 dR_2 as A16 Alo Ahi Aimg AB16 ABlo ABhi ABimg DSB _ _ | pose proof (vsb_obj_geom LPA Ac mc mdc _ _ _ AINVc AOBJc) as (A16 & Alo & Ahi & Aimg & AB16 & ABlo & ABhi & ABimg & DSB & _ & _) ]).
      (first [ pose proof (AOBJc) as dR_3; dand6 dR_3 as _ _ LAS LAB ASB _ | pose proof AOBJc as (_ & _ & LAS & LAB & ASB & _) ]).
      (first [ pose proof (AOBJ2) as dR_4; dand6 dR_4 as AVC AVI _ _ _ (bs & AU8 & LBS & _) | pose proof AOBJ2 as (AVC & AVI & _ & _ & _ & (bs & AU8 & LBS & _)) ]). fold_cl_segs.
      destruct (vsb_shadows LPA Ac mc mdc _ _ _ AINVc AOBJc) as [SHSa SHBa]. fold_cl_segs. fold_aview.
      unfold kHighMemBeg in Alo. all_app_facts.
      pose proof (shpat_sh_bound (Clg:=Clg) (x_v xc Fattr_vsb) 40 ltac:(klia Alo) ltac:(clear; lia) Ahi) as SHSB. rewrite SHMAX_val in SHSB.
      pose proof (shpat_sh_bound (Clg:=Clg) (vb_buf y) (vb_size y) ltac:(klia ABlo) ltac:(klia ABlo) ABhi) as SHBB. rewrite SHMAX_val in SHBB.
      assert (EVSC : h_vsc (pe_H E) = h_ff (pe_H E) + 32) by reflexivity.
      assert (SPR : 0 <= pe_sp E < 2^64) by (klia SPH LOP CEIL ACV).
      pose proof (sh_mono 17594333495296 (x_v xc Fattr_vsb) ltac:(klia Alo)) as SHAlo. change (sh 17594333495296) with 2201439137792 in SHAlo.
      eapply (bytes_at_munch LPA) in SHSa; [| exact MU12| intros a__ Ha__; cbn [outside]; klia Ha__ SHSB SHAlo VEPlo LOP CEIL ACV G2 EVSC SPR].
      eapply (bytes_at_munch LPA) in SHBa; [| exact MU12| intros a__ Ha__; cbn [outside]; klia Ha__ SHBB ABlo VEPlo LOP CEIL ACV G2 EVSC SPR].
      pose proof (as_live_disjoint LPA Ac mc mdc _ _ _ _ AINVc LAS LVEP D_AV) as DXA.
      unfold oabuf in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI. rewrite EVA in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI.
      pose proof (as_live_disjoint LPA Ac mc mdc _ _ _ _ AINVc LAB LVEP D_ABV) as DXB.
      unfold vep_cells in VEPC2. psimp_in VEPC2.
      assert (NAI : x_v xc Finclude_src <> x_v xc Fattr_vsb /\ x_v xc Finclude_src <> vb_buf y /\
                    oibuf xc <> x_v xc Fattr_vsb /\ oibuf xc <> vb_buf y).
      { clear - VI D_AI D_AA; try pose proof alloc_ceiling_val as ACV__. unfold oibuf in *. destruct (x_vi xc) as [yi|].
        - exact (D_AI ltac:(discriminate) ltac:(discriminate)).
        - rewrite VI. (first [ pose proof ((D_AA ltac:(discriminate))) as dR_5; dand3 dR_5 as _ ATlo ABUlo | destruct (D_AA ltac:(discriminate)) as (_ & ATlo & ABUlo) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
      (first [ dand4 NAI as NIA NIB NBA NBB | destruct NAI as (NIA & NIB & NBA & NBB) ]).
      (* [comment removed for export] *)
      assert (MU : munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 304 - 64, pe_sp E - 304); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                          (vb_buf y, vb_buf y + vb_size y); (ERRNOA, ERRNOA + 4); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] (aview Ac mc) m2)
        by (eapply munch_weaken; [| exact MU12]; clear; unfold sub_fp; cbn [outside]; intros; lia).
      pose proof WM12 as WM.
      assert (WZ : wzonex E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Finclude_src; oibuf xc]
                     [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 304 - 64, pe_sp E - 304); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                      (vb_buf y, vb_buf y + vb_size y); (ERRNOA, ERRNOA + 4); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzonex_tac.
      assert (CFP : client_fpx Ac (aview Ac mc)
                     [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 304 - 64, pe_sp E - 304); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                      (vb_buf y, vb_buf y + vb_size y); (ERRNOA, ERRNOA + 4); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)])
        by (eapply wzonex_client_fpx; [exact PE| exact HFR| exact STKc| unfold pframe; cbv zeta; exact FRc| exact WZ]).
      pose proof MU12 as MUv. clear WM12 WZ12. unfold ERRNOA in MU.
      destruct (rw_errno_any m2) as [e0 ERR].
      pose proof (cenv_intro Ac mc mdc AINVc) as CE. fold_aview.
      assert (CE2 : cenv m2)
        by (eapply cenv_munch; [exact CE| exact MUv| repeat (apply Forall_cons; [unfold const_free_ivl, CONSTS_TOP; cbn; klia VEPlo VEPhi LOP CEIL ACV G2 EVSC SPR|]); apply Forall_nil]).
      clear MUv MU12.
      (first [ pose proof (AVI) as dR_7; dand8 dR_7 as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | pose proof AVI as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
      rewrite <- EzsV in SHVX. clear SHV0.
      hide Aimg. hide ABimg. hide Verr. hide_neqs.
      (* [comment removed for export] *)
      pose proof (munch_refl [(pe_sp E - 304 - 64, pe_sp E - 304); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                              (vb_buf y, vb_buf y + vb_size y); (ERRNOA, ERRNOA + 4)] m2) as MU3.
      pose proof (wmono_refl rsegs m2) as WM3. unfold ERRNOA in MU3.
      (* [comment removed for export] *)
      zstep.
      icall (HFI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pe_F E) (pe_fc E) _ (x_v xc Fattr_vsb) y bs e0 (pe_lo E)) by
        (rewrite ?unsigned_lit by (klia SPR LOP CEIL ACV);
         lazymatch goal with
         | |- @eq (bv _) _ _ => reflexivity
         | |- rw_cells _ _ _ (vsb_cells _) => exact AVC
         | |- rw_cells _ _ _ [C4 _] => exact ERR
         | |- u8arr _ _ _ _ => exact AU8
         | |- vsb_inv _ _ => exact AVI
         | |- Z.of_nat _ = _ => exact LBS
         | |- shadowed _ _ _ 40 => exists (x_v xc Fattr_vsb), 40; split; [exact SHSa|]; split; [clear - A16; Z.div_mod_to_equations; lia| klia Alo Ahi]
         | |- shadowed _ _ _ (vb_size _) => exists (vb_buf y), (vb_size y); split; [exact SHBa|]; split; [clear - AB16; Z.div_mod_to_equations; lia| klia ABlo ABhi]
         | |- shadowed _ _ _ 4 => apply errno_shadowed; exact (proj1 CE2)
         | |- cenv _ => exact CE2
         | |- _ \/ _ => exact DSB
         | |- stk _ _ _ _ => exact STK2
         | |- mem_inv _ _ => exact MI2
         | |- app_range _ _ _ => first [assumption | exact ABlo_a]
         | |- _ mod 8 = 0 => clear - A16; Z.div_mod_to_equations; lia
         | |- _ => first [assumption | unfold kHighMemBeg, FINISH_STACK, ASSERT_STACK; klia Alo Ahi ABhi LOP CEIL ACV SPR]
         end).
      try clear AVC AU8 ERR STK2.
      lazymatch goal with X : rw_cells _ ?mq _ (vsb_cells _) |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into AVC3 end.
      lazymatch goal with X : u8arr _ ?mq (vb_buf _) _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into AU83 end.
      lazymatch goal with X : rw_cells _ ?mq 6193972 _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into ERR3 end.
      lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STK3 end.
      (* [comment removed for export] *)
      set (yf := vsb_set_flags y VSB_FLAGS_FIN).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
        assert (AOBJ3 : vsb_obj LPA Ac m3 (x_v xc Fattr_vsb) yf true) end.
      { subst yf. split; [exact AVC3|]. split; [| split; [exact LAS|]; split; [exact LAB|]; split; [exact ASB|]].
        - clear - AVI. unfold vsb_inv in *. cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf vsb_set_flags].
          (first [ dand6 AVI as V1 V2 V3 V4 V5 V6 | destruct AVI as (V1 & V2 & V3 & V4 & V5 & V6) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; try lia.
        - exists (upd bs (Z.to_nat (vb_len y)) (Z_to_bv 8 0)). cbn [vb_buf vb_size vb_len vsb_set_flags].
          split; [exact AU83|]. split; [rewrite upd_length; exact LBS|].
          intros _. apply nth_error_upd_same. clear - AVI LBS. unfold vsb_inv in AVI. lia. }
      (* [comment removed for export] *)
      unhide DJfV. unhide DJfS. unhide DJfB.
      pose proof (as_frame_blk_disjoint LPA _ _ _ _ HCLASS ageh _ _ AINVc HFh LAS) as DJfA.
      pose proof (as_frame_blk_disjoint LPA _ _ _ _ HCLASS ageh _ _ AINVc HFh LAB) as DJfAB.
      change (fsize HCLASS) with 8192 in DJfA, DJfAB.
      pose proof (sh_boundL (Clg:=Clg) (h_ff (pe_H E)) 8192 ltac:(klia G2) ltac:(clear; lia) G3) as SHFB. rewrite SHMAX_val in SHFB.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
        assert (HENV3 : henv_ok LPA VIA (pe_H E) Ac m3)
          by (eapply henv_ok_munch; [exact HENV2| exact MU3| exact WM3| exact HG|];
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold HOBJ_END, HFSIZE, h_cp in Ha__; change (8192 / 8) with 1024 in Ha__;
              cbn [outside]; klia Ha__ SHFB VEPhi VEPlo ACV EVSC G2 DJfV DJfA DJfAB Alo Ahi ABlo ABhi LOP CEIL SPR) end.
      hide DJfV. hide DJfS. hide DJfB. clear MU3 WM3.
      (* [comment removed for export] *)
      unhide Verr. pose proof Verr as E0. rewrite E0. change (vsb_result 0 0) with 0.
      zstep. kdead2. zstep. zstep. zstep.
      astopx AINVc MU WM CFP. fold_cl_segs.
      lazymatch goal with AINVs : ainv Ac ?ms ?mds |- srealizes _ (mkCfg (MS _ _ _ _ _ ?ms _) ?mds) _ =>
      eapply (destroy_attr_fin HDS E xc Ac mc ms mdc mds T 0x8ccc8
                [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 304 - 64, pe_sp E - 304); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                 (vb_buf y, vb_buf y + vb_size y); (ERRNOA, ERRNOA + 4); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]
                (fupd (fupd (x_v xc) Fstate (vi_st VIA S_TagError)) Fattr_delim 0) y yf true);
        [ exact PE | exact PIc0 | exact AINVc | exact AINVs | exact MU | exact WM | exact WZ | exact HENV3
        | lazymatch goal with H : mem_inv _ ?v |- mem_inv _ ?v => exact H end | exact STK3 | exact FRX
        | unfold vep_cells; psimp; exact VEPC2
        | psimp; reflexivity | psimp; reflexivity | exact EVA | exact AOBJ3 | subst yf; reflexivity | subst yf; reflexivity
        | clear; lia | reflexivity
        | eapply (cframe_after _ _ _ _ _ _ (pe_v0 E) (aview Ac mc));
          [ unfold parse_new; psimp; unfold parse_new in CF; psimp_in CF; exact CF
          | exact MU
          | intros a__ Ha__ NO__; cbn [outside] in NO__; change (cl_errno LPA) with 6193972;
            unfold parse_changed, vsb_blocks; rewrite EVA; cbn [option_map];
            assert (CASES : (pe_VEP E <= a__ < pe_VEP E + 312) \/ (pe_sp E - 304 - 64 <= a__ < pe_sp E - 304) \/
                            (x_v xc Fattr_vsb <= a__ < x_v xc Fattr_vsb + 40) \/ (vb_buf y <= a__ < vb_buf y + vb_size y) \/
                            (6193972 <= a__ < 6193972 + 4) \/ (h_vsc (pe_H E) + 1304 <= a__ < h_vsc (pe_H E) + 1320))
              by (clear - Ha__ NO__; lia);
            clear NO__; destruct CASES as [X|[X|[X|[X|[X|X]]]]];
            [ right; left; left; unfold blk; split; [klia VEPlo| exact X]
            | left; rewrite PARSE_STACK_val; klia X
            | right; right; left; right; left; left; unfold newblk, blk; left; split; [exact ANZ| exact X]
            | right; right; left; right; left; right; unfold newblk, blk; left; split; [klia ABlo| exact X]
            | right; right; right; exact X
            | right; left; right; right; right; exact X ]
          | eapply parse_window_mapped; [exact PE| exact STK3| exact FRX] ]
        | ]
      end.
      clear MU WM WZ CFP HENV3 AOBJ3 FRX STK3. try clear AVC3. try clear AU83. try clear ERR3.
      intros t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x A5 m6 md5 AINV5 MI5 MDF5 STK5 FR5 VEPC5 HENV6 DATA5 VSBO5 WAL5 LVEP5 VI5 SS5 LB5 NL5 TC5 SCC5 PCC5 FS5 KEEP5 CF5.
      unfold call_ms. cbv zeta. rewrite EFP in *.
      pose proof (proj1 HENV6) as HFR5.
      unfold pframe in FR5. cbv zeta in FR5.
      (* [comment removed for export] *)
      ago AINV5. fold_cl_segs.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A5 m6)) as MU6. pose proof (wmono_refl rsegs (aview A5 m6)) as WM6.
      assert (WZ6 : wzone E A5 [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Finclude_src; oibuf xc] [(pe_VEP E, pe_VEP E + 312)]).
      { cbn [wzone]. split; [| exact I]. left. exists (pe_VEP E), 312. split; [exact LVEP5|]. split; [wz_not_in| clear; lia]. }
      set (xf := PST (x_p xc) S_TagError (fupd (fupd (fupd (x_v xc) Fstate (vi_st VIA S_TagError)) Fattr_delim 0) Fattr_vsb 0)
                     (x_tag xc) (x_q xc) (x_vv xc) None (x_vi xc)).
      assert (PIf : pinv E xf A5 (aview A5 m6)).
      { subst xf. unfold vep_cells in VEPC5. psimp_in VEPC5. unfold vi_world in VI5. psimp_in VI5.
        apply Build_pinv; psimp; pinv_close PE0 AINV5 HFR5 MU6 WM6 WZ6.
        + (* [comment removed for export] *) revert OUT OA0 Vlen. unfold oacost, oicost. rewrite ?EVA. cbn [x_va x_vi x_st x_p x_vv]. clear. destruct (x_vi xc); intros; lia.
        + (* [comment removed for export] *) revert LB LB5. rewrite ?EVA. clear. unfold world_bytes, x_vio. cbn [option_map]. destruct (x_vi xc); cbn [option_map]; intros; lia.
        + (* [comment removed for export] *) revert NL NL5. rewrite ?EVA. clear. unfold world_nlive, x_vio. cbn [option_map]. destruct (x_vi xc); cbn [option_map]; intros; lia.
        + (* [comment removed for export] *) rewrite TC5. exact TC.
        + (* [comment removed for export] *) intros ff. rewrite (FS5 ff). apply FRS.
        + (* [comment removed for export] *) intros p Hp. apply NEW. revert Hp. rewrite ?EVA. unfold parse_blocks. psimp. clear. intros [Hp|[[]|Hp]]; [left; exact Hp| right; right; exact Hp].
        + (* [comment removed for export] *) rewrite SCC5. revert SC WL ASZ Vlen Vsz. rewrite ?EVA. cbn [x_va x_vi x_p].
          clear. intros SC WL ASZ Vlen Vsz.
          pose proof (vsb_pot_len y ASZ ltac:(lia) ltac:(lia)) as PL_.
          pose proof (div4096_add (vb_len y) (x_p xc - pe_DATA E - vb_len y - match x_vi xc with Some yi => vb_len yi | None => 0 end) ltac:(lia) ltac:(lia)) as DA_.
          assert (MONO : (vb_len y + (x_p xc - pe_DATA E - vb_len y - match x_vi xc with Some yi => vb_len yi | None => 0 end)) / 4096
                         <= (x_p xc - pe_DATA E - 0 - match x_vi xc with Some yi => vb_len yi | None => 0 end) / 4096)
            by (apply Z.div_le_mono; lia).
          lia. }
      hide_neqs.
      astop0 AINV5.
      lazymatch goal with SBx : same_but_materialized mdc ?mds, SBy : same_but_materialized md5 _ |- _ =>
      eapply (KL xf A5 _ _);
        [ exact PIf | assumption
        | eapply amd_frame_sbm_r; [eapply amd_frame_trans; [eapply amd_frame_sbm_r; [exact MDFc| exact SBx]| exact MDF5]| exact SBy]
        | subst xf; psimp; intros _; split; [| discriminate]; rewrite PHI; unfold phi, rank; psimp; klia LQ ] end.
    Qed.
  End X.
End S.
End A_PHv1x.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHmhz.A_PHd8z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHmhz.A_PH76v OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHmhz.A_PHv1x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section S.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HVE : vep_error_stmt.
  Hypothesis HDS : VSB_destroy_stmt.
  Hypothesis HPC : VSB_putc_stmt.
  Hypothesis HFI : VSB_finish_stmt.
  Hypothesis HDIA : vep_do_include_attr_stmt.

  Lemma PH_AttrValue : handler_stmt S_AttrValue.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    assert (PHI : phi E x = 16 * (pe_e E - x_p x) + 1) by (unfold phi, rank; rewrite ST; reflexivity).
    exact (av_body HVE HDS HPC E x T PE PHI KL (av_finish HVE HDS HFI HDIA E x T PE PHI KL) (av_gtfin HDS HFI E x T PE PHI KL) A m md _ _ _ _ _ _ _ _ _ _ _ _ PI AINV MDF ST PLT).
  Qed.
End S.

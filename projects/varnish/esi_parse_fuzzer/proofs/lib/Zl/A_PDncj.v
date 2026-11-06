(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PCall.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.

Module A_PH0ci.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Lemma PH_Attr : handler_stmt S_Attr.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    pose proof (DELIM1 ltac:(discriminate)) as DL0.
    assert (AV0 : x_v x Fattr_vsb = 0).
    { destruct (Z.eq_dec (x_v x Fattr_vsb) 0) as [X|X]; [exact X| exfalso; exact (AVSB X)]. }
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 4 0. zstep. rewrite DL0, sx32_small by (clear; lia).
    zstep; if_cases K1; zify_cond K1; try (exfalso; try (generalize alloc_ceiling_val); clear - K1; try pose proof alloc_ceiling_val; rewrite ?unsigned_lit in K1 by (clear; lia); lia); [].
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0.
    destruct ATTR as [AT0|(ATI & DOI & _)].
    - (* [comment removed for export] *)
      zstep. rewrite AT0. zstep; if_cases K2; zify_cond K2; try (exfalso; try (generalize alloc_ceiling_val); clear - K2; try pose proof alloc_ceiling_val; rewrite ?unsigned_lit in K2 by (clear; lia); lia); [].
      (* [comment removed for export] *)
      zstep. zstep. zstep; if_cases KU; zify_cond KU; [ exfalso; clear - KU VERP Dlo; lia | clear KU ].
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 8 0. zstep. rewrite AV0. zstep; if_cases K3; zify_cond K3; try (exfalso; try (generalize alloc_ceiling_val); clear - K3; try pose proof alloc_ceiling_val; rewrite ?unsigned_lit in K3 by (clear; lia); lia); [].
      (* [comment removed for export] *)
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep.
      astop AINV MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x + 1) S_SkipAttribute (fupd (x_v x) Fstate (vi_st VIA S_SkipAttribute)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
      + apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
      * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val. lia.
      * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val. lia.
      * (* [comment removed for export] *) left. exact AT0.
      * (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
      * (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
        * (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      + assumption.
      + eapply amd_frame_sbm_r; [exact MDF | exact SBM].
      + (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. destruct (vct_xmlname _); try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val; lia.
    - (* [comment removed for export] *)
      zstep. rewrite ATI. cbn [vi_tbl_attr_include VIA]. unfold TBL_attr_include.
      zstep; if_cases K2; zify_cond K2; try (exfalso; try (generalize alloc_ceiling_val); clear - K2; try pose proof alloc_ceiling_val; rewrite ?unsigned_lit in K2 by (clear; lia); lia); [].
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 8 0. zstep.
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep.
      astop AINV MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x) S_Match (fupd (fupd (x_v x) Fmatch TBL_attr_include) Fstate (vi_st VIA S_Match)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
      + apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
      * (* [comment removed for export] *) intros _. exact (ARMED I).
      * (* [comment removed for export] *) right. split; [exact ATI|]. split; [exact DOI|]. left. reflexivity.
      * (* [comment removed for export] *) intros _ _. exact ATI.
      * (* [comment removed for export] *) intros _ _ HLT. refine (LOOKA eq_refl _ HLT). rewrite ATI. cbn [vi_tbl_attr_include VIA]. unfold TBL_attr_include. clear. lia.
        * (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      + assumption.
      + eapply amd_frame_sbm_r; [exact MDF | exact SBM].
      + (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. cbn [vi_tbl_attr_include vi_tbl_esi VIA]. unfold TBL_bom, TBL_starttag, TBL_esi, TBL_attr_include. cbn [Z.eqb Pos.eqb]. lia.
  Qed.
End S.
End A_PH0ci.

Module A_PH9dv.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_ESITag : handler_stmt S_ESITag.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 4 0. zstep. zstep.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 4 1. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    astop AINV MU WM CFP. fold_cl_segs.
    set (xc := PST (x_p x) S_ESITag (fupd (fupd (x_v x) Fin_esi_tag 1) Fesi_found 1) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
    assert (PIc : pinv E xc A (aview A m0)).
    { subst xc. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
      + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
    eapply (mark_call HMC E xc A _ _ T (x_p x) (x_p x) (1) 0x8c4f0);
      [ exact PE | exact PIc | exact AINV0 | eapply amd_frame_sbm_r; [exact MDF | exact SBM]
      | subst xc; cbn [x_p]; try (generalize alloc_ceiling_val); clear -PLT; try pose proof alloc_ceiling_val; lia | subst xc; cbn [x_p]; first [exact PLE | try (generalize alloc_ceiling_val); clear -PLT; try pose proof alloc_ceiling_val; lia] | first [left; reflexivity | right; reflexivity] | clear; lia | reflexivity
      | subst xc; cbn [x_st]; intros [X|X]; discriminate X | ].
    subst xc.
    intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
    assert (ST1 : x_st x1 = S_ESITag) by (rewrite EX1; cbn [x_st after_mark]; first [reflexivity | exact ST]).
    assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
    assert (EP1 : x_p x1 = x_p x) by (rewrite EX1; reflexivity).
    clear - HMC PE ST PLT KL KX PI1 AINV1 MDF1 VK VERP1 LM1 OP1 ST1 EV1 EP1; try pose proof alloc_ceiling_val.
    world_open PE PI1 AINV1. unfold call_ms. cbv zeta. rewrite EFP in *. rewrite <- EP1 in PLT |- *.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
    assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    hide_neqs.
    ago AINV1. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 4 0. zstep. zstep. zstep.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 8 2. zstep. zstep. zstep.
    (* [comment removed for export] *)
    vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep.
    astop AINV1 MU WM CFP. fold_cl_segs.
    eapply (KL (PST (x_p x1) S_Match (fupd (fupd (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) Fmatch TBL_esi) Fstate (vi_st VIA S_Match)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
    - apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
      + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
    - assumption.
    - eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
    - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. cbn [vi_tbl_attr_include vi_tbl_esi VIA]. unfold TBL_bom, TBL_starttag, TBL_esi, TBL_attr_include. cbn [Z.eqb Pos.eqb]. lia.
  Qed.
End S.
End A_PH9dv.

Module A_PH_BOM.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_BOM : handler_stmt S_BOM.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    pose proof PI as PI0. pose proof (pi_pe _ _ _ _ PI) as PLE.
    unfold disp_ms, loop_ms; rewrite ST; cbn [disp_pc disp_a1 disp_a2 disp_a6 disp_s1 disp_s6 disp_s10 disp_pos oreg vi_st VIA stA].
    ago AINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    astop0 AINV.
    eapply (mark_call HMC E x A _ _ T (x_p x) (x_p x) 1 0x8ba94);
      [ exact PE | exact PI0 | exact AINV0 | eapply amd_frame_sbm_r; [exact MDF | exact SBM]
      | clear; lia | exact PLE | right; reflexivity | clear; lia | reflexivity
      | rewrite ST; intros [X|X]; discriminate X | ].
    intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
    assert (ST1 : x_st x1 = S_BOM) by (rewrite EX1, <- ST; reflexivity).
    assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
    assert (EP1 : x_p x1 = x_p x) by (rewrite EX1; reflexivity).
    clear - HMC PE ST PLT KL KX PI1 AINV1 MDF1 VK VERP1 LM1 OP1 ST1 EV1 EP1; try pose proof alloc_ceiling_val.
    world_open PE PI1 AINV1. unfold call_ms. cbv zeta. rewrite EFP in *. rewrite <- EP1 in PLT |- *.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
    assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    hide_neqs.
    ago AINV1. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 4 0.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 1 0.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (rw_cells_read_sub rsegs mx _ _ 4 1 VEPC ltac:(clear; lia) ltac:(cbn; clear; lia)) as RDF end.
    match type of RDF with _ = Some ?r => change r with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x1 Fflags)))] in RDF end.
    remember (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x1 Fflags)))) as fb eqn:Efb in RDF.
    set (RWv := rw_cells rsegs _ (pe_VEP E)) in VEPC.
    zstep. subst RWv. clear RDF. cbv beta. zstep. zstep. zstep. zstep. (* [comment removed for export] *) if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep.
      astop AINV1 MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x1) S_NxtTag (fupd (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) Fstate (vi_st VIA S_NxtTag)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
      + apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
        * (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      + assumption.
      + eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
      + (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
    - (* [comment removed for export] *)
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep.
      astop AINV1 MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x1) S_TestXml (fupd (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) Fstate (vi_st VIA S_TestXml)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
      + apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
        * (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      + assumption.
      + eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
      + (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
  Qed.
End S.
End A_PH_BOM.

Module A_PHarb.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HVE : vep_error_stmt.

  #[using="HVE"] Lemma PH_ESI_Include : handler_stmt S_ESI_Include.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    assert (WZh : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                          [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    pose proof (cenv_intro A m md AINV) as CE. fold_aview.
    pose proof HENV as (_ & GLOB & HOBJ & HSH).
    assert (SHVD : shadowed LPA (aview A m) (pe_VEP E) 312).
    { exists (pe_VEP E), 312. split; [pose proof SHV0 as T__; rewrite EzsV in T__; exact T__|].
      split; [try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia|]. try (generalize alloc_ceiling_val); clear - VEPlo VEPhi; try pose proof alloc_ceiling_val. lia. }
    assert (KHV : kHighMemBeg <= pe_VEP E) by (unfold kHighMemBeg; try (generalize alloc_ceiling_val); clear - VEPlo; try pose proof alloc_ceiling_val; lia).
    assert (M8V : pe_VEP E mod 8 = 0) by (try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia).
    assert (DJV : h_ff (pe_H E) + HFSIZE <= pe_VEP E \/ pe_VEP E + 312 <= h_ff (pe_H E)) by (unhide_djf; unfold HFSIZE; try (generalize alloc_ceiling_val); clear - DJfV; try pose proof alloc_ceiling_val; lia).
    assert (EVSC : h_vsc (pe_H E) = h_ff (pe_H E) + 32) by reflexivity. unfold kHighMemBeg in G2. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) (h_ff (pe_H E)) 8192 ltac:(try (generalize alloc_ceiling_val); clear -G2; try pose proof alloc_ceiling_val; lia) ltac:(clear; lia) G3) as SHFB. rewrite SHMAX_val in SHFB.
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 4 0. zstep. destruct B_rm as [RM|RM]; rewrite RM, sx32_small by (clear; lia).
    all: zstep; (* [comment removed for export] *) zstep; if_cases K1; zify_cond K1; try (exfalso; try (generalize alloc_ceiling_val); clear - K1; try pose proof alloc_ceiling_val; rewrite ?unsigned_lit in K1 by (clear; lia); lia); clear K1.
    2:{ (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      unhide DJfV.
      try clear DBY. icall (HVE (pe_VEP E) (fupd (x_v x) Fstate (stA (x_st x))) (x_tag x) (x_q x) (pe_H E) (pe_lo E)) by
        (rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - FRB; try pose proof alloc_ceiling_val; lia);
         first [ reflexivity | exact VEPC | exact TAG | exact PADS | exact (proj1 BASE) | exact GLOB | exact HOBJ | exact HSH | exact HG
               | exact CE | exact SHVD | exact KHV | exact M8V | exact VEPhi | exact DJV | exact STK | exact CEIL | exact MI
               | unfold VEPERR_STACK; try (generalize alloc_ceiling_val); clear - LOP; try pose proof alloc_ceiling_val; lia ]).
      hide DJfV.
      lazymatch goal with X : glob_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into GLOB1 end.
      lazymatch goal with X : hobj_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into HOBJ1 end.
      lazymatch goal with X : stk _ ?v _ _ |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into STK end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV1 : henv_ok LPA VIA (pe_H E) A v)
          by (split; [exact HFR| split; [exact GLOB1| split; [exact HOBJ1|]]];
              eapply hshadow_munch; [exact HSH| exact MU| exact HG|];
              intros a__ Ha__; unfold HFSIZE in Ha__; change (8192 / 8) with 1024 in Ha__; cbn [outside]; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo LOP CEIL ACV EVSC G2; try pose proof alloc_ceiling_val; lia);
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] v) as MU2; pose proof (wmono_refl rsegs v) as WM2
      end.
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV2 : henv_ok LPA VIA (pe_H E) A v)
          by (eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold HOBJ_END, HFSIZE, h_cp in Ha__; change (8192 / 8) with 1024 in Ha__;
              cbn [outside]; unhide_djf; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo VEPhi ACV EVSC G2 DJfV; try pose proof alloc_ceiling_val; lia)
      end.
      clear HENV1.
      astop AINV MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x) S_TagError (fupd (x_v x) Fstate (vi_st VIA S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha].
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
      - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
 }
    (* [comment removed for export] *)
    vchk SHV0 EzsV 4 0. zstep. destruct B_et as [ET|ET]; rewrite ET, sx32_small by (clear; lia).
    all: zstep; if_cases K2; zify_cond K2; try (exfalso; try (generalize alloc_ceiling_val); clear - K2; try pose proof alloc_ceiling_val; rewrite ?unsigned_lit in K2 by (clear; lia); lia); clear K2.
    2:{ (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      unhide DJfV.
      try clear DBY. icall (HVE (pe_VEP E) (fupd (x_v x) Fstate (stA (x_st x))) (x_tag x) (x_q x) (pe_H E) (pe_lo E)) by
        (rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - FRB; try pose proof alloc_ceiling_val; lia);
         first [ reflexivity | exact VEPC | exact TAG | exact PADS | exact (proj1 BASE) | exact GLOB | exact HOBJ | exact HSH | exact HG
               | exact CE | exact SHVD | exact KHV | exact M8V | exact VEPhi | exact DJV | exact STK | exact CEIL | exact MI
               | unfold VEPERR_STACK; try (generalize alloc_ceiling_val); clear - LOP; try pose proof alloc_ceiling_val; lia ]).
      hide DJfV.
      lazymatch goal with X : glob_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into GLOB1 end.
      lazymatch goal with X : hobj_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into HOBJ1 end.
      lazymatch goal with X : stk _ ?v _ _ |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into STK end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV1 : henv_ok LPA VIA (pe_H E) A v)
          by (split; [exact HFR| split; [exact GLOB1| split; [exact HOBJ1|]]];
              eapply hshadow_munch; [exact HSH| exact MU| exact HG|];
              intros a__ Ha__; unfold HFSIZE in Ha__; change (8192 / 8) with 1024 in Ha__; cbn [outside]; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo LOP CEIL ACV EVSC G2; try pose proof alloc_ceiling_val; lia);
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] v) as MU2; pose proof (wmono_refl rsegs v) as WM2
      end.
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV2 : henv_ok LPA VIA (pe_H E) A v)
          by (eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold HOBJ_END, HFSIZE, h_cp in Ha__; change (8192 / 8) with 1024 in Ha__;
              cbn [outside]; unhide_djf; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo VEPhi ACV EVSC G2 DJfV; try pose proof alloc_ceiling_val; lia)
      end.
      clear HENV1.
      astop AINV MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x) S_TagError (fupd (x_v x) Fstate (vi_st VIA S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha].
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
      - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
 }
    (* [comment removed for export] *)
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MUh. pose proof (wmono_refl rsegs (aview A m)) as WMh.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0. zstep. zstep. zstep.
    (* [comment removed for export] *)
    vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0. zstep. zstep. zstep. zstep.
    astop AINV MU WM CFP. fold_cl_segs.
    eapply (KL (PST (x_p x) S_InTag (fupd (fupd (fupd (x_v x) Fdostuff (vi_do_include VIA)) Fstate (vi_st VIA S_InTag)) Fattr TBL_attr_include) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
    - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
      + (* [comment removed for export] *) right; left. reflexivity.
      + (* [comment removed for export] *) right. split; [reflexivity|]. split; [reflexivity|]. left. exact I.
      + (* [comment removed for export] *) eapply (henv_stores _ _ _ _ _ _ _ PE0 AINV HFR MUh WMh WZh); [intros a__ Ha__; cbn [outside]; unhide_djf; unfold h_vsc, pe_fp, PARSE_FRAME in *; first [clear - Ha__ DJfV DJfS DJfB DJfD; lia | lia]| split; [exact HFR| split; [exact GLOB| split; [exact HOBJ| exact HSH]]]].
      + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha].
    - assumption.
    - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
    - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
  Qed.
End S.
End A_PHarb.

Module A_PHcyi.
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

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HVE : vep_error_stmt.

  #[using="HVE"] Lemma PH_ESI_Bogon : handler_stmt S_ESI_Bogon.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    pose proof (cenv_intro A m md AINV) as CE. fold_aview.
    destruct HENV as (_ & GLOB & HOBJ & HSH).
    assert (SHVD : shadowed LPA (aview A m) (pe_VEP E) 312).
    { exists (pe_VEP E), 312. split; [pose proof SHV0 as T__; rewrite EzsV in T__; exact T__|].
      split; [try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia|]. try (generalize alloc_ceiling_val); clear - VEPlo VEPhi; try pose proof alloc_ceiling_val. lia. }
    assert (KHV : kHighMemBeg <= pe_VEP E) by (unfold kHighMemBeg; try (generalize alloc_ceiling_val); clear - VEPlo; try pose proof alloc_ceiling_val; lia).
    assert (M8V : pe_VEP E mod 8 = 0) by (try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia).
    assert (DJV : h_ff (pe_H E) + HFSIZE <= pe_VEP E \/ pe_VEP E + 312 <= h_ff (pe_H E)) by (unhide_djf; unfold HFSIZE; try (generalize alloc_ceiling_val); clear - DJfV; try pose proof alloc_ceiling_val; lia).
    assert (EVSC : h_vsc (pe_H E) = h_ff (pe_H E) + 32) by reflexivity. unfold kHighMemBeg in G2. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) (h_ff (pe_H E)) 8192 ltac:(try (generalize alloc_ceiling_val); clear -G2; try pose proof alloc_ceiling_val; unfold kHighMemBeg in G2; all_app_facts; lia) ltac:(clear; lia) G3) as SHFB. rewrite SHMAX_val in SHFB.
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    unhide DJfV.
    try clear DBY. icall (HVE (pe_VEP E) (fupd (x_v x) Fstate (stA (x_st x))) (x_tag x) (x_q x) (pe_H E) (pe_lo E)) by
      (rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - FRB; try pose proof alloc_ceiling_val; lia);
       first [ reflexivity | exact VEPC | exact TAG | exact PADS | exact (proj1 BASE) | exact GLOB | exact HOBJ | exact HSH | exact HG
             | exact CE | exact SHVD | exact KHV | exact M8V | exact VEPhi | exact DJV | exact STK | exact CEIL | exact MI
             | unfold VEPERR_STACK; try (generalize alloc_ceiling_val); clear - LOP; try pose proof alloc_ceiling_val; lia ]).
    hide DJfV.
    lazymatch goal with X : glob_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into GLOB1 end.
    lazymatch goal with X : hobj_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into HOBJ1 end.
    lazymatch goal with X : stk _ ?v _ _ |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into STK end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
      assert (HENV1 : henv_ok LPA VIA (pe_H E) A v)
        by (split; [exact HFR| split; [exact GLOB1| split; [exact HOBJ1|]]];
            eapply hshadow_munch; [exact HSH| exact MU| exact HG|];
            intros a__ Ha__; unfold HFSIZE in Ha__; change (8192 / 8) with 1024 in Ha__; cbn [outside]; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo LOP CEIL ACV EVSC G2; try pose proof alloc_ceiling_val; lia);
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] v) as MU2; pose proof (wmono_refl rsegs v) as WM2
    end.
    (* [comment removed for export] *)
    vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
      assert (HENV2 : henv_ok LPA VIA (pe_H E) A v)
        by (eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
            intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold HOBJ_END, HFSIZE, h_cp in Ha__; change (8192 / 8) with 1024 in Ha__;
            cbn [outside]; unhide_djf; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo VEPhi ACV EVSC G2 DJfV; try pose proof alloc_ceiling_val; lia)
    end.
    clear HENV1.
    astop AINV MU WM CFP. fold_cl_segs.
    eapply (KL (PST (x_p x) S_TagError (fupd (x_v x) Fstate (vi_st VIA S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
    - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
      + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha].
    - assumption.
    - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
    - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
  Qed.
End S.
End A_PHcyi.

Module A_PHmgj.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PCall.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)


Local Tactic Notation "klia" ne_hyp_list(hs) := try (generalize alloc_ceiling_val); clear - hs; try pose proof alloc_ceiling_val; lia.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HNA : VSB_new_auto_stmt.

  #[using="HNA"] Lemma PH_AttrGetValue : handler_stmt S_AttrGetValue.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    pose proof PI as PI0. (first [ pose proof ((pinv_sizes _ _ _ _ PI)) as dR_1; dand4 dR_1 as OUT' WBB LEN0 SZ0 | pose proof (pinv_sizes _ _ _ _ PI) as (OUT' & WBB & LEN0 & SZ0) ]).
    handler_prologue PE PI AINV ST.
    assert (AV0 : x_v x Fattr_vsb = 0).
    { destruct (Z.eq_dec (x_v x Fattr_vsb) 0) as [X|X]; [exact X| exfalso; exact (AVSB X)]. }
    assert (EVA : x_va x = None).
    { revert VA AV0. clear. destruct (x_va x); [| reflexivity]. intros VA AV0. exfalso. exact (proj1 VA AV0). }
    assert (WNL2 : 0 <= world_nlive (x_va x) (x_vio x) <= 2) by (rewrite EVA; unfold world_nlive, x_vio; clear; destruct (x_vi x); cbn; lia).
    unfold PARSE_LIVE, pe_N in BUDL. unfold PARSE_NLIVE in BUDN.
    assert (ENA : NEWAUTO_STACK = 8320) by (vm_compute; reflexivity).
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. rewrite (shr3_div8 (pe_VEP E + 224)). vrechk SHV0 EzsV (pe_VEP E + 224) 8 0.
    (* [comment removed for export] *)
    zstep. zstep. rewrite AV0. zstep; if_cases K1; zify_cond K1; try (exfalso; try (generalize alloc_ceiling_val); clear - K1; try pose proof alloc_ceiling_val; rewrite ?unsigned_lit in K1 by (clear; lia); lia); [].
    zstep.
    astop0 AINV.
    lazymatch goal with H : ainv A ?mm ?mdd |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mm _) ?mdd) _ => rename H into AINVc end.
    eapply HNA;
      [ exact AINVc | exact MI
      | klia LB BUDL WBB NN EE | klia NL BUDN WNL2
      | pose proof (pinv_primcred _ _ _ _ PI0) as (_ & _ & PCR); unfold PRIM_ROOM in PCR; klia PCR (* [comment removed for export] *)
      | rewrite unsigned_lit by (klia VEPB); klia VEPhi
      | reflexivity
      | rewrite unsigned_lit by (klia FRB); rewrite Zminus_mod, SP16; reflexivity
      | rewrite unsigned_lit by (klia FRB); exact STK
      | exact CEIL
      | rewrite unsigned_lit by (klia FRB); rewrite ENA; klia LOP
      | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md'. cbv zeta. intros AINV' MI' MDF' FSA TC' SCE PCE STK' RES.   (* [comment removed for export] *)
    rewrite unsigned_lit in STK', RES by (klia FRB). rewrite ENA in RES.
    replace (ret_pc (Z_to_bv 64 0x8cbdc)) with (Z_to_bv 64 0x8cbdc) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    assert (WIN : alloc_ceiling <= pe_sp E - 320 - 8320) by (klia LOP CEIL).
    pose proof (frames_same_fs A A' FSA) as FS.
    destruct RES as (b & RNZ & VSO & FRr & FRb & LQ & LB' & NL' & CF').
    (* [comment removed for export] *)
    - (* [comment removed for export] *)
      assert (LK : forall p k, a_live A p = Some k -> a_live A' p = Some k).
      { intros p k Hp. rewrite LQ; [exact Hp| intros ->; congruence| intros ->; congruence]. }
      (first [ pose proof ((world_keep E x A A' _ _ _ _ _ _ PE PI0 AINVc CF' WIN ltac:(clear; lia) ltac:(unfold pe_fp, PARSE_FRAME; clear; lia) LK FS)) as dR_4; dand9 dR_4 as VEPO1 VSBO1 VA1 VI1 DATA1 HENV1 (j0' & j8' & FR1) SS1 WAL1 | destruct (world_keep E x A A' _ _ _ _ _ _ PE PI0 AINVc CF' WIN ltac:(clear; lia) ltac:(unfold pe_fp, PARSE_FRAME; clear; lia) LK FS)
        as (VEPO1 & VSBO1 & VA1 & VI1 & DATA1 & HENV1 & (j0' & j8' & FR1) & SS1 & WAL1) ]).
      assert (NEWd : forall p k, a_live A p = Some k -> p <> r /\ p <> b) by (intros p k Hp; split; intros ->; congruence).
      pose proof (NEWd _ _ LVEP) as [NrV NbV]. pose proof (NEWd _ _ WAL) as [NrW NbW]. pose proof (NEWd _ _ LDATA) as [NrD NbD].
      pose proof (NEWd _ _ LVS) as [NrS NbS]. pose proof (NEWd _ _ LVB) as [NrB NbB].
      assert (NI : match x_vi x with None => True | Some y => (x_v x Finclude_src <> r /\ x_v x Finclude_src <> b) /\ (vb_buf y <> r /\ vb_buf y <> b) end).
      { clear - VI NEWd; try pose proof alloc_ceiling_val. destruct (x_vi x) as [yi|]; [| exact I]. (first [ dand3 VI as _ (_ & _ & L1 & L2 & _) _ | destruct VI as (_ & (_ & _ & L1 & L2 & _) & _) ]).
        split; [exact (NEWd _ _ L1)| exact (NEWd _ _ L2)]. }
      (first [ pose proof (VSO) as dR_6; dand6 dR_6 as _ _ Lr Lb Nrb _ | pose proof VSO as (_ & _ & Lr & Lb & Nrb & _) ]). cbn [vb_buf vb_size vsb_fresh] in Lb, Nrb.
      assert (CFm : cframe LPA (owned (pe_A0 E)) (owned A') (pe_sp E) PARSE_STACK (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E))
                           (parse_new (x_v (PST (x_p x) S_AttrGetValue (fupd (x_v x) Fattr_vsb r) (x_tag x) (x_q x) (x_vv x) (Some (vsb_fresh b)) (x_vi x))) (x_vv (PST (x_p x) S_AttrGetValue (fupd (x_v x) Fattr_vsb r) (x_tag x) (x_q x) (x_vv x) (Some (vsb_fresh b)) (x_vi x))) (x_va (PST (x_p x) S_AttrGetValue (fupd (x_v x) Fattr_vsb r) (x_tag x) (x_q x) (x_vv x) (Some (vsb_fresh b)) (x_vi x))) (x_vio (PST (x_p x) S_AttrGetValue (fupd (x_v x) Fattr_vsb r) (x_tag x) (x_q x) (x_vv x) (Some (vsb_fresh b)) (x_vi x)))) (pe_v0 E) (aview A' m')).
      { eapply (cframe_step_call E x (PST (x_p x) S_AttrGetValue (fupd (x_v x) Fattr_vsb r) (x_tag x) (x_q x) (x_vv x) (Some (vsb_fresh b)) (x_vi x)) A A' _ _ (pe_sp E - 320) 8320);
          [ exact CF | exact CF' | rewrite PARSE_STACK_val; clear; lia | clear; lia
          | eapply parse_window_mapped; [exact PE| exact STK'| exact FR1]
          | intros a Ha; destruct Ha
          | intros a Ha; unfold parse_new in Ha; cbn [x_v x_vv x_va x_vi x_vio option_map fupd vf_beq vf_index N.eqb Pos.eqb] in Ha; unfold vsb_blocks in Ha; cbn [vb_buf vb_size vsb_fresh] in Ha;
            destruct Ha as [Ha|[Ha|Ha]]; [right; right; left; exact Ha| left; exact Ha| right; right; right; right; exact Ha] ]. }
      clear VEPC FR STK MI SHV0 HENV VSBO DATA SS VA WAL CF LVEP LVS LVB HFR.
      (first [ dand4 VEPO1 as LVEP1 VEPC1 _ _ | destruct VEPO1 as (LVEP1 & VEPC1 & _ & _) ]). unfold vep_cells in VEPC1. rewrite STATE in VEPC1. cbn [vi_st VIA stA] in VEPC1.
      unfold pframe in FR1. cbv zeta in FR1. rewrite EFP in FR1. unfold va_world in VA1. unfold vi_world in VI1.
      pose proof (proj1 HENV1) as HFR1.
      pose proof (proj1 (proj2 (proj2 VSBO1))) as LVS1. pose proof (proj1 (proj2 (proj2 (proj2 VSBO1)))) as LVB1.
      pose proof (as_live_shadow LPA _ _ _ _ 312 AINV' LVEP1) as SHV1. fold_cl_segs. fold_aview.
      change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV1. rewrite <- EzsV in SHV1.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A' m')) as MU1. pose proof (wmono_refl rsegs (aview A' m')) as WM1.
      unhide_neqs.
      assert (WZ1 : wzone E A' [pe_S E; vb_buf (x_vv x); pe_DATA E; r; b; x_v x Finclude_src; oibuf x]
                            [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (CFP1 : client_fp LPA A' (aview A' m') [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR1| exact STK'| unfold pframe; cbv zeta; exact FR1| exact WZ1]).
      hide_neqs.
      ago AINV'. fold_cl_segs.
      (* [comment removed for export] *)
      vrechk SHV1 EzsV (pe_VEP E + 224) 8 0. zstep. zstep.
      (* [comment removed for export] *)
      vrechk SHV1 EzsV (pe_VEP E + 64) 8 2. zstep. zstep. zstep. zstep.
      astop AINV' MU1 WM1 CFP1. fold_cl_segs.
      eapply (KL (PST (x_p x) S_AttrDelim (fupd (fupd (x_v x) Fattr_vsb r) Fstate (vi_st VIA S_AttrDelim)) (x_tag x) (x_q x) (x_vv x) (Some (vsb_fresh b)) (x_vi x)) A' _ _).
      + apply Build_pinv; psimp; pinv_close PE0 AINV' HFR1 MU1 WM1 WZ1.
        all: try lazymatch goal with |- _ - _ <= a_seccred _ <= _ => cbn [vb_len vb_size vsb_fresh]; rewrite (vsb_pot_small (vsb_fresh b)) by (cbn; clear; lia); rewrite SCE; rewrite EVA in WL, SC; revert WL SC; clear; intros; lia end.
        all: try lazymatch goal with |- 0 <= _ /\ 0 <= _ /\ _ <= _ - pe_DATA _ => cbn [vb_len vsb_fresh]; rewrite EVA in WL; klia WL end.
        * (* [comment removed for export] *) intros _ _. exact (ATTRST I (or_introl eq_refl)).
        * (* [comment removed for export] *)
          revert OUT. unfold oacost, oicost. rewrite EVA. cbn [x_va x_vi x_st x_p x_vv vb_len vsb_fresh]. clear. intros; lia.
        * (* [comment removed for export] *)
          split; [exact RNZ|]. split; [eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV' HFR1 MU1 WM1 WZ1); [in_list| in_list| exact VSO]|].
          split; [cbn; clear; lia|]. split; [cbn; try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val; lia|].
          intros y Hy. cbn in Hy. cbn [vb_buf vsb_fresh].
          destruct Hy as [<-|[<-|[<-|[<-|[<-|[]]]]]]; split; apply not_eq_sym; assumption.
        * (* [comment removed for export] *)
          rewrite EVA in VI1. revert VI1 NI. destruct (x_vi x) as [yi|] eqn:EVI; intros VI1 NI; [| exact VI1].
          (first [ dand7 VI1 as Q1 Q2 Q3 Q4 Q5 Q6 _ | destruct VI1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _) ]). destruct NI as [[N1 N2] [N3 N4]].
          refine (conj Q1 (conj _ (conj Q3 (conj Q4 (conj Q5 (conj Q6 _)))))).
          { eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV' HFR1 MU1 WM1 WZ1); [in_list| in_list| exact Q2]. }
          intros y Hy. cbn in Hy. cbn [vb_buf vsb_fresh].
          destruct Hy as [<-|[<-|[]]]; [split; [exact N1| exact N3] | split; [exact N2| exact N4]].
        * (* [comment removed for export] *) revert LB LB'. rewrite EVA. clear. unfold world_bytes, x_vio. cbn [option_map vb_size vsb_fresh]. destruct (x_vi x); cbn [option_map vb_size]; intros; lia.
        * (* [comment removed for export] *) revert NL NL'. rewrite EVA. clear. unfold world_nlive, x_vio. cbn [option_map]. destruct (x_vi x); cbn [option_map]; intros; lia.
        * (* [comment removed for export] *) rewrite TC'. exact TC.
        * (* [comment removed for export] *) intros ff. rewrite (FSA ff). apply FRS.
        * (* [comment removed for export] *) intros p k Lp NBp. apply LK. exact (KEEP p k Lp NBp).
        * (* [comment removed for export] *) intros p Hp. unfold parse_blocks in Hp. psimp_in Hp. cbn [vb_buf vsb_fresh] in Hp.
          destruct Hp as [Hp|[[Hp|Hp]|Hp]].
          -- apply NEW. unfold parse_blocks. left. exact Hp.
          -- subst p. destruct (Z.eq_dec r (pe_b E)) as [EQ|NEQ]; [left; exact EQ| right].
             destruct (a_live (pe_A0 E) r) as [k|] eqn:EK; [| reflexivity]. exfalso. pose proof (KEEP _ _ EK NEQ) as LA. rewrite LA in FRr. discriminate FRr.
          -- subst p. destruct (Z.eq_dec b (pe_b E)) as [EQ|NEQ]; [left; exact EQ| right].
             destruct (a_live (pe_A0 E) b) as [k|] eqn:EK; [| reflexivity]. exfalso. pose proof (KEEP _ _ EK NEQ) as LA. rewrite LA in FRb. discriminate FRb.
          -- apply NEW. unfold parse_blocks. right. right. exact Hp.
        * (* [comment removed for export] *) eapply (cframe_step_stores _ _ (PST (x_p x) S_AttrDelim (fupd (fupd (x_v x) Fattr_vsb r) Fstate (vi_st VIA S_AttrDelim)) (x_tag x) (x_q x) (x_vv x) (Some (vsb_fresh b)) (x_vi x)));
            [ exact CFm | exact MU1 | w_in_zone_tac; left; left; unfold blk; lia
            | eapply parse_window_mapped; [exact PE0| exact STK'| unfold pframe; cbv zeta; exact FR1]
            | intros a Y; eapply parse_new_same; [| | exact Y]; psimp; reflexivity ].
      + assumption.
      + eapply amd_frame_sbm_r; [eapply amd_frame_trans; [eapply amd_frame_sbm_r; [exact MDF| exact SBM]| exact MDF'] | eassumption].
      + (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
  Qed.
End S.
End A_PHmgj.

Module A_PHuri.
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
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Lemma PH_Start : handler_stmt S_Start.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    destruct (data_shadow A m md _ _ AINV DATA) as [SHD D16]. fold_cl_segs. fold_aview.
    (* [comment removed for export] *)
    pose proof (rw_cells_read_sub rsegs _ _ _ 4 1 VEPC ltac:(clear; lia) ltac:(cbn; clear; lia)) as RDF.
    match type of RDF with _ = Some ?r => change r with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x Fflags)))] in RDF end.
    remember (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x Fflags)))) as fb eqn:Efb in RDF.
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 1 0.
    (* [comment removed for export] *)
    set (RWv := rw_cells rsegs (aview A m) (pe_VEP E)) in VEPC.
    zstep. subst RWv. clear RDF. cbv beta. zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep.
      astop AINV MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x) S_BOM (fupd (x_v x) Fstate (vi_st VIA S_BOM)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      - exact AINV0.
      - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
      - psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
    (* [comment removed for export] *)
    zstep; if_cases KU; zify_cond KU; [ clear KU | exfalso; clear - KU VERP Dlo; lia ].
    (* [comment removed for export] *)
    pchk SHD 1 11.
    (* [comment removed for export] *)
    destruct (look_read rsegs E x _ DBY ltac:(try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val; lia) PLT) as (b & Hnth & Hlook & RDP).
    pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
    zstep. clear RDP. cbv beta. zstep. zstep. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep.
      astop AINV MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x) S_BOM (fupd (x_v x) Fstate (vi_st VIA S_BOM)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      - exact AINV0.
      - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
      - psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. vchk_at SHV0 EzsV 8 0. zstep. zstep. zstep.
    (* [comment removed for export] *)
    vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep.
    astop AINV MU WM CFP. fold_cl_segs.
    eapply (KL (PST (x_p x) S_Match (fupd (fupd (x_v x) Fmatch TBL_bom) Fstate (vi_st VIA S_Match))
                    (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
    - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
      + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
    - exact AINV0.
    - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
    - (* [comment removed for export] *)
      psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST.
      cbn [vi_tbl_attr_include vi_tbl_esi VIA]. unfold TBL_bom, TBL_starttag, TBL_esi, TBL_attr_include. cbn [Z.eqb Pos.eqb]. lia.
  Qed.
End S.
End A_PHuri.

Module A_PHvy4.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_NotXml : handler_stmt S_NotXml.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    pose proof PI as PI0. pose proof (pi_pe _ _ _ _ PI) as PLE.
    unfold disp_ms, loop_ms; rewrite ST; cbn [disp_pc disp_a1 disp_a2 disp_a6 disp_s1 disp_s6 disp_s10 disp_pos oreg vi_st VIA stA].
    ago AINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    astop0 AINV.
    eapply (mark_call HMC E x A _ _ T (x_p x) (pe_e E) 0 0x8d7cc);
      [ exact PE | exact PI0 | exact AINV0 | eapply amd_frame_sbm_r; [exact MDF | exact SBM]
      | try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val; lia | clear; lia | left; reflexivity | clear; lia | reflexivity
      | rewrite ST; intros [X|X]; discriminate X | ].
    intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
    assert (ST1 : x_st x1 = S_NotXml) by (rewrite EX1, <- ST; reflexivity).
    assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
    assert (EP1 : x_p x1 = pe_e E) by (rewrite EX1; reflexivity).
    clear - HMC PE ST KL KX PI1 AINV1 MDF1 VK VERP1 LM1 OP1 ST1 EV1 EP1; try pose proof alloc_ceiling_val.
    world_open PE PI1 AINV1. unfold call_ms. cbv zeta. rewrite EFP in *.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
    assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    hide_neqs.
    ago AINV1. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 4 0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    astop AINV1 MU WM CFP. fold_cl_segs.
    eapply (KX (PST (pe_e E) S_NotXml (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1))
                    (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
    - apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
      + (* [comment removed for export] *) rewrite <- EP1. exact VERP.
      + (* [comment removed for export] *) revert OUT. rewrite EP1. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
      + (* [comment removed for export] *) rewrite <- EP1. pinv_close PE0 AINV1 HFR MU WM WZ.
      + (* [comment removed for export] *) rewrite <- EP1. pinv_close PE0 AINV1 HFR MU WM WZ.
      + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
    - assumption.
    - eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
    - reflexivity.
  Qed.
End S.
End A_PHvy4.

Module A_PHxtw.
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

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HVE : vep_error_stmt.

  #[using="HVE"] Lemma PH_ESI_Comment : handler_stmt S_ESI_Comment.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_sp E - 320 - 64, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    assert (WZh : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                          [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    pose proof (cenv_intro A m md AINV) as CE. fold_aview.
    destruct HENV as (_ & GLOB & HOBJ & HSH).
    assert (SHVD : shadowed LPA (aview A m) (pe_VEP E) 312).
    { exists (pe_VEP E), 312. split; [pose proof SHV0 as T__; rewrite EzsV in T__; exact T__|].
      split; [try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia|]. try (generalize alloc_ceiling_val); clear - VEPlo VEPhi; try pose proof alloc_ceiling_val. lia. }
    assert (KHV : kHighMemBeg <= pe_VEP E) by (unfold kHighMemBeg; try (generalize alloc_ceiling_val); clear - VEPlo; try pose proof alloc_ceiling_val; lia).
    assert (M8V : pe_VEP E mod 8 = 0) by (try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia).
    assert (DJV : h_ff (pe_H E) + HFSIZE <= pe_VEP E \/ pe_VEP E + 312 <= h_ff (pe_H E)) by (unhide_djf; unfold HFSIZE; try (generalize alloc_ceiling_val); clear - DJfV; try pose proof alloc_ceiling_val; lia).
    assert (EVSC : h_vsc (pe_H E) = h_ff (pe_H E) + 32) by reflexivity. unfold kHighMemBeg in G2. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) (h_ff (pe_H E)) 8192 ltac:(try (generalize alloc_ceiling_val); clear -G2; try pose proof alloc_ceiling_val; lia) ltac:(clear; lia) G3) as SHFB. rewrite SHMAX_val in SHFB.
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 4 0.
    zstep. destruct B_rm as [RM|RM]; rewrite RM, sx32_small by (clear; lia).
    all: zstep; (* [comment removed for export] *) zstep; if_cases K1; zify_cond K1; try (exfalso; try (generalize alloc_ceiling_val); clear - K1; try pose proof alloc_ceiling_val; rewrite ?unsigned_lit in K1 by (clear; lia); lia); clear K1.
    2:{ (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      unhide DJfV.
      try clear DBY. icall (HVE (pe_VEP E) (fupd (x_v x) Fstate (stA (x_st x))) (x_tag x) (x_q x) (pe_H E) (pe_lo E)) by
        (rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - FRB; try pose proof alloc_ceiling_val; lia);
         first [ reflexivity | exact VEPC | exact TAG | exact PADS | exact (proj1 BASE) | exact GLOB | exact HOBJ | exact HSH | exact HG
               | exact CE | exact SHVD | exact KHV | exact M8V | exact VEPhi | exact DJV | exact STK | exact CEIL | exact MI
               | unfold VEPERR_STACK; try (generalize alloc_ceiling_val); clear - LOP; try pose proof alloc_ceiling_val; lia ]).
      hide DJfV.
      lazymatch goal with X : glob_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into GLOB1 end.
      lazymatch goal with X : hobj_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into HOBJ1 end.
      lazymatch goal with X : stk _ ?v _ _ |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into STK end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV1 : henv_ok LPA VIA (pe_H E) A v)
          by (split; [exact HFR| split; [exact GLOB1| split; [exact HOBJ1|]]];
              eapply hshadow_munch; [exact HSH| exact MU| exact HG|];
              intros a__ Ha__; unfold HFSIZE in Ha__; change (8192 / 8) with 1024 in Ha__; cbn [outside]; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo LOP CEIL ACV EVSC G2; try pose proof alloc_ceiling_val; lia);
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] v) as MU2; pose proof (wmono_refl rsegs v) as WM2
      end.
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV2 : henv_ok LPA VIA (pe_H E) A v)
          by (eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold HOBJ_END, HFSIZE, h_cp in Ha__; change (8192 / 8) with 1024 in Ha__;
              cbn [outside]; unhide_djf; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo VEPhi ACV EVSC G2 DJfV; try pose proof alloc_ceiling_val; lia)
      end.
      clear HENV1.
      astop AINV MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x) S_TagError (fupd (x_v x) Fstate (vi_st VIA S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha].
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
      - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
 }
    (* [comment removed for export] *)
    vchk SHV0 EzsV 4 0.
    zstep. destruct B_et as [ET|ET]; rewrite ET, sx32_small by (clear; lia).
    all: zstep; if_cases K2; zify_cond K2; try (exfalso; try (generalize alloc_ceiling_val); clear - K2; try pose proof alloc_ceiling_val; rewrite ?unsigned_lit in K2 by (clear; lia); lia); clear K2.
    2:{ (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      unhide DJfV.
      try clear DBY. icall (HVE (pe_VEP E) (fupd (x_v x) Fstate (stA (x_st x))) (x_tag x) (x_q x) (pe_H E) (pe_lo E)) by
        (rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - FRB; try pose proof alloc_ceiling_val; lia);
         first [ reflexivity | exact VEPC | exact TAG | exact PADS | exact (proj1 BASE) | exact GLOB | exact HOBJ | exact HSH | exact HG
               | exact CE | exact SHVD | exact KHV | exact M8V | exact VEPhi | exact DJV | exact STK | exact CEIL | exact MI
               | unfold VEPERR_STACK; try (generalize alloc_ceiling_val); clear - LOP; try pose proof alloc_ceiling_val; lia ]).
      hide DJfV.
      lazymatch goal with X : glob_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into GLOB1 end.
      lazymatch goal with X : hobj_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into HOBJ1 end.
      lazymatch goal with X : stk _ ?v _ _ |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into STK end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV1 : henv_ok LPA VIA (pe_H E) A v)
          by (split; [exact HFR| split; [exact GLOB1| split; [exact HOBJ1|]]];
              eapply hshadow_munch; [exact HSH| exact MU| exact HG|];
              intros a__ Ha__; unfold HFSIZE in Ha__; change (8192 / 8) with 1024 in Ha__; cbn [outside]; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo LOP CEIL ACV EVSC G2; try pose proof alloc_ceiling_val; lia);
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] v) as MU2; pose proof (wmono_refl rsegs v) as WM2
      end.
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV2 : henv_ok LPA VIA (pe_H E) A v)
          by (eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold HOBJ_END, HFSIZE, h_cp in Ha__; change (8192 / 8) with 1024 in Ha__;
              cbn [outside]; unhide_djf; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo VEPhi ACV EVSC G2 DJfV; try pose proof alloc_ceiling_val; lia)
      end.
      clear HENV1.
      astop AINV MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x) S_TagError (fupd (x_v x) Fstate (vi_st VIA S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha].
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
      - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
 }
    (* [comment removed for export] *)
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MUh. pose proof (wmono_refl rsegs (aview A m)) as WMh.
    zstep. vchk SHV0 EzsV 8 0. zstep. zstep. zstep.
    vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep.
    astop AINV MU WM CFP. fold_cl_segs.
    eapply (KL (PST (x_p x) S_InTag (fupd (fupd (x_v x) Fdostuff (vi_do_comment VIA)) Fstate (vi_st VIA S_InTag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
    - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
      + (* [comment removed for export] *) right; right; right. reflexivity.
      + (* [comment removed for export] *) eapply (henv_stores _ _ _ _ _ _ _ PE0 AINV HFR MUh WMh WZh); [intros a__ Ha__; cbn [outside]; unhide_djf; unfold h_vsc, pe_fp, PARSE_FRAME in *; first [clear - Ha__ DJfV DJfS DJfB DJfD; lia | lia]| split; [exact HFR| split; [exact GLOB| split; [exact HOBJ| exact HSH]]]].
      + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha].
    - assumption.
    - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
    - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
  Qed.
End S.
End A_PHxtw.

Module A_PHypf.
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
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.
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

Ltac icall_consts_in H ::= unfold memset_esicmt_post, ASAN_MEMSET_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot_lia_prev := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Lemma PH_Comment : handler_stmt S_Comment.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_sp E - 320 - 2208, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_sp E - 320 - 2208, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_sp E - 320 - 2208, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. vchk_at SHV0 EzsV 8 0.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    zstep. vchk_at SHV0 EzsV 8 3.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. vchk_at SHV0 EzsV 8 0.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0.
    (* [comment removed for export] *)
    zstep. vrechk SHV0 EzsV (pe_VEP E + 64) 8 0.
    zstep. zstep. zstep. zstep.
    astop AINV MU WM CFP. fold_cl_segs.
    eapply (KL (PST (x_p x) S_Until
                    (fupd (fupd (fupd (fupd (fupd (fupd (x_v x) Fesicmt 0) Fesicmt_p 0) Funtil LIT_arrow) Funtil_p LIT_arrow)
                          Funtil_s (vi_st VIA S_NxtTag)) Fstate (vi_st VIA S_Until))
                    (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
    - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
      + (* [comment removed for export] *) left. split; reflexivity.
      + (* [comment removed for export] *) intros _. split; [left; reflexivity|]. split; [unfold LIT_arrow; cbn; lia| reflexivity].
      + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
    - exact AINV0.
    - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
    - (* [comment removed for export] *)
      psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
  Qed.
End S.
End A_PHypf.

Module A_PPutc.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PMark.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Tactic Notation "klia" ne_hyp_list(hs) := try (generalize alloc_ceiling_val); clear - hs; try pose proof alloc_ceiling_val; lia.

Lemma PUTC_STACK_val : PUTC_STACK = 8336.
Proof. vm_compute. reflexivity. Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HPC : VSB_putc_stmt.

  Definition after_putc (x : pst) (y1 : vsb_rec) : pst :=
    PST (x_p x + 1) (x_st x) (x_v x) (x_tag x) (x_q x) (x_vv x) (Some y1) (x_vi x).

  Lemma putc_call : forall (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet) (ps ret : Z) (y : vsb_rec) (fj0 fj8 : word)
      (t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s6 s10 s11 t3 t4 t5 t6 : word),
    penv_ok E -> pinv E x A (aview A m) -> ainv A m md -> amd_frame (pe_md0 E) md ->
    x_va x = Some y -> x_st x = S_AttrValue -> x_p x < pe_e E -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
    rw_cells rsegs (aview A m) (pe_fp E) (pframe E fj0 fj8) ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A1 : AS) (m1 : mem) (md1 : Model)
            (y1 : vsb_rec) (x1 : pst),
        x1 = after_putc x y1 ->
        pinv E x1 A1 (aview A1 m1) -> ainv A1 m1 md1 -> amd_frame (pe_md0 E) md1 ->
        vb_len y <= vb_len y1 <= vb_len y + 1 ->
        rw_cells rsegs (aview A1 m1) (pe_fp E) (pframe E fj0 fj8) ->
        srealizes rsegs (mkCfg (call_ms E ret ps (Z_to_bv 64 ret) t0' t1' t2' s1 a0' a1' a2' a3' a4' a5' a6' a7' s6 s10 s11 t3' t4' t5' t6' m1) md1) T) ->
    srealizes rsegs (mkCfg (call_ms E VSB_putc_entry ps (Z_to_bv 64 ret) t0 t1 t2 s1
                               (Z_to_bv 64 (x_v x Fattr_vsb)) a1 a2 a3 a4 a5 a6 a7 s6 s10 s11 t3 t4 t5 t6 m) md) T.
  Proof.
    intros until t6. intros PE PI AINV MDF0 EVA STx PLT RR RET FRX K.
    pose proof PI as PI0. (first [ pose proof ((pinv_sizes _ _ _ _ PI)) as dR_1; dand4 dR_1 as OUT' WBB LEN0 SZ0 | pose proof (pinv_sizes _ _ _ _ PI) as (OUT' & WBB & LEN0 & SZ0) ]). (first [ pose proof ((pinv_seccred _ _ _ _ PI)) as dR_2; dand3 dR_2 as SCB SCN SC15 | pose proof (pinv_seccred _ _ _ _ PI) as (SCB & SCN & SC15) ]). pose proof (pinv_primcred _ _ _ _ PI) as (PCB & PCD & PCR).   (* [comment removed for export] *)
    pose proof (world_nlive_nonneg (x_va x) (x_vio x)) as WNL.
    world_open PE PI AINV. unfold call_ms in K |- *. cbv zeta in K |- *. rewrite EFP in *. clear FR. pose proof FRX as FR. unfold pframe in FR. cbv zeta in FR.
    rewrite EVA in VA. (first [ dand5 VA as ANZ AOBJ AROOM ALEN AAP | destruct VA as (ANZ & AOBJ & AROOM & ALEN & AAP) ]).
    (first [ pose proof (AOBJ) as dR_4; dand5 dR_4 as _ VIa LAS LAB _ | pose proof AOBJ as (_ & VIa & LAS & LAB & _) ]). pose proof VIa as VIa'. unfold vsb_inv in VIa'.
    unfold oabuf in *. rewrite EVA in *.
    pose proof (vsb_extendsize_tight (vb_size y + 1)) as EXT.
    unfold PARSE_LIVE, pe_N in BUDL. unfold PARSE_NLIVE in BUDN.
    eapply (HPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A (x_v x Fattr_vsb) y (pe_lo E));
      [ exact AINV | exact MI | reflexivity | exact AOBJ
      | unfold EXT_MAX; klia AROOM ALEN PLE EE NN VERP
      | revert LB BUDL EXT AROOM ALEN PLE EE NN VERP WBB OUT' OA0 OI0; unfold world_bytes, x_vio, oacost; cbn [option_map]; clear; intros; lia
      | klia NL BUDN WNL
      | klia SC15
      | exact PCR (* [comment removed for export] *)
      | reflexivity
      | rewrite unsigned_lit by (klia FRB); rewrite Zminus_mod, SP16; reflexivity
      | rewrite unsigned_lit by (klia FRB); exact STK
      | exact CEIL
      | rewrite unsigned_lit by (klia FRB); rewrite PUTC_STACK_val; klia LOP
      | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1 y1. cbv zeta.
    intros AINV1 MI1 MDF1 VSO1 LEN1 SZ1 STEP1 LIVE1 REL FSA LB1 TC1 NL1 SCC1 PCC1 ST1 CF1.   (* [comment removed for export] *)
    rewrite unsigned_lit in ST1, CF1 by (klia FRB). rewrite PUTC_STACK_val in CF1.
    rewrite (ret_pc_even ret RR RET).
    (* [comment removed for export] *)
    assert (HC : hcover A [pe_VEP E; pe_S E; vb_buf (x_vv x); pe_DATA E]
                        (fun a => newblk (vb_buf y) (vb_size y) a \/ (x_v x Fattr_vsb <= a < x_v x Fattr_vsb + 40))).
    { intros a [X|X].
      - eapply hcover_newblk; [exact LAB| wz_not_in| exact X].
      - eapply hcover_rng; [exact LAS| wz_not_in| exact X]. }
    pose proof (hcover_vcover (pe_H E) _ _ _ HC) as CV1.
    assert (WIN : alloc_ceiling <= pe_sp E - 320 - 8336) by (klia LOP CEIL).
    assert (W0 : 0 <= 8336) by (clear; lia).
    (* [comment removed for export] *)
    assert (LVEP1 : a_live A1 (pe_VEP E) = Some 312) by (eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LVEP| exact (not_eq_sym D_ABV)]).
    assert (LVS1 : a_live A1 (pe_S E) = Some 40) by (eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LVS| exact (not_eq_sym D_ABS)]).
    assert (LVB1 : a_live A1 (vb_buf (x_vv x)) = Some (vb_size (x_vv x))) by (eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LVB| exact (not_eq_sym D_ABB)]).
    assert (LDATA1 : a_live A1 (pe_DATA E) = Some (Z.of_nat (length (pe_inp E)))) by (eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LDATA| exact (not_eq_sym D_ABD)]).
    assert (WAL1 : a_live A1 (pe_wa E) = Some 40) by (eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact WAL| exact (not_eq_sym D_ABW)]).
    assert (NB_V : pe_VEP E <> vb_buf y1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LVEP| exact (not_eq_sym D_ABV)]).
    assert (NB_W : pe_wa E <> vb_buf y1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact WAL| exact (not_eq_sym D_ABW)]).
    assert (NB_D : pe_DATA E <> vb_buf y1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LDATA| exact (not_eq_sym D_ABD)]).
    assert (NB_S : pe_S E <> vb_buf y1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LVS| exact (not_eq_sym D_ABS)]).
    assert (NB_B : vb_buf (x_vv x) <> vb_buf y1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LVB| exact (not_eq_sym D_ABB)]).
    (* [comment removed for export] *)
    assert (VEPO1 : vep_obj LPA A1 (aview A1 m1) (pe_VEP E) (x_v x) (x_tag x) (x_q x)).
    { eapply (vep_obj_call (pe_H E) A A1 m md _ _ _ _ _ _ AINV CF1 HFR WIN); [exact CV1| in_list| exact LVEP1| exact (pi_vep _ _ _ _ PI0)]. }
    assert (FR1 : rw_cells rsegs (aview A1 m1) (pe_sp E - 320) (pframe E fj0 fj8)).
    { eapply (pframe_call E A A1 m md _ _ _ _ _ _ fj0 fj8);
        [exact PE| exact AINV| exact CF1| exact HFR| exact WIN| exact W0| unfold pe_fp, PARSE_FRAME; klia WIN| exact CV1| unfold pframe; cbv zeta; exact FR]. }
    assert (HENV1 : henv_ok LPA VIA (pe_H E) A1 (aview A1 m1)).
    { eapply (henv_call (pe_H E) A A1 m md _ _ _ _ _ _ AINV CF1 WIN); [exact HC| | exact HENV].
      intros ff k age Hf. exists age. rewrite (FSA ff). exact Hf. }
    assert (DATA1 : data_obj LPA A1 (aview A1 m1) (pe_DATA E) (pe_inp E)).
    { eapply (data_obj_call (pe_H E) A A1 m md _ _ _ _ _ _ AINV CF1 HFR WIN); [exact CV1| in_list| exact LDATA1| exact DATA]. }
    assert (VSBO1 : vsb_obj LPA A1 (aview A1 m1) (pe_S E) (x_vv x) false).
    { eapply (vsb_obj_call (pe_H E) A A1 m md _ _ _ _ _ _ AINV CF1 HFR WIN); [exact CV1| in_list| in_list| exact LVS1| exact LVB1| exact VSBO]. }
    assert (SS1 : stack_shadow LPA (aview A1 m1) (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64)).
    { eapply (stack_shadow_call (pe_H E) A A1 m md _ _ _ _ _ _ AINV CF1 HFR WIN); [exact CV1| rewrite PARSE_STACK_val; klia LOP CEIL ACV| exact SS]. }
    assert (VI1 : vi_world E (after_putc x y1) A1 (aview A1 m1)).
    { unfold vi_world, after_putc. cbn [x_vi x_v x_va x_vv x_p].
      destruct (x_vi x) as [yi|] eqn:EVI; [| exact VI].
      (first [ dand7 VI as Q1 Q2 Q3 Q4 Q5 Q6 Q7 | destruct VI as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7) ]). (first [ pose proof ((D_AI ltac:(discriminate) ltac:(discriminate))) as dR_6; dand4 dR_6 as NIA NIB NBA NBB | destruct (D_AI ltac:(discriminate) ltac:(discriminate)) as (NIA & NIB & NBA & NBB) ]).
      unfold oibuf in NBA, NBB. rewrite EVI in NBA, NBB. cbn in NBA, NBB.
      (first [ pose proof (Q2) as dR_7; dand5 dR_7 as _ _ LIS LIB _ | pose proof Q2 as (_ & _ & LIS & LIB & _) ]).
      assert (HCi : hcover A [x_v x Finclude_src; vb_buf yi] (fun a => newblk (vb_buf y) (vb_size y) a \/ (x_v x Fattr_vsb <= a < x_v x Fattr_vsb + 40))).
      { intros a [X|X].
        - eapply hcover_newblk; [exact LAB| wz_not_in| exact X].
        - eapply hcover_rng; [exact LAS| wz_not_in| exact X]. }
      refine (conj Q1 (conj _ (conj Q3 (conj Q4 (conj _ (conj Q6 _)))))).
      - eapply (vsb_obj_call (pe_H E) A A1 m md _ _ _ _ _ _ AINV CF1 HFR WIN);
          [exact (hcover_vcover (pe_H E) _ _ _ HCi)| in_list| in_list
          | eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LIS| exact NIB]
          | eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LIB| exact NBB]
          | exact Q2].
      - klia Q5.
      - intros z Hz. cbn in Hz. destruct Hz as [<-|[<-|[]]].
        + exact (conj NIA NBA).
        + split; [eapply (fresh_ne _ _ _ _ _ _ REL); [exact LIS| exact NIB] | eapply (fresh_ne _ _ _ _ _ _ REL); [exact LIB| exact NBB]]. }
    assert (PI1 : pinv E (after_putc x y1) A1 (aview A1 m1)).
    { unfold after_putc. apply Build_pinv; psimp; rewrite ?STx; cbn beta iota; try pinv_triv.
      - (* [comment removed for export] *) rewrite STATE, STx. reflexivity.
      - (* [comment removed for export] *) klia VERP.
      - (* [comment removed for export] *) klia PLT.
      - exact (conj DELIM1 DELIM2).
      - intros X1 _. apply ATTRST; [exact X1| right; discriminate].
      - (* [comment removed for export] *)
        try (generalize alloc_ceiling_val); clear - OUT LEN1 EVA; try pose proof alloc_ceiling_val. unfold oacost, oicost in *. rewrite EVA in OUT. cbn [x_va x_vi x_st x_p x_vv x_v] in *. lia.
      - (* [comment removed for export] *)
        split; [exact ANZ|]. split; [exact VSO1|]. split; [klia SZ1 LEN1 AROOM|]. split; [klia ALEN LEN1|].
        intros z Hz. split; [exact (proj1 (AAP z Hz))|].
        cbn in Hz. destruct Hz as [<-|[<-|[<-|[<-|[<-|[]]]]]]; apply not_eq_sym; [exact NB_V| exact NB_W| exact NB_D| exact NB_S| exact NB_B].
      - exists fj0, fj8. exact FR1.
      - (* [comment removed for export] *) revert LB LB1. clear. unfold world_bytes, x_vio. cbn [option_map]. intros; lia.
      - rewrite NL1. exact NL.
      - rewrite TC1. exact TC.
      - intros ff. rewrite (FSA ff). apply FRS.
      - (* [comment removed for export] *) intros p k Lp NBp. pose proof (KEEP p k Lp NBp) as LA.
        eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LA|].
        intros ->. destruct (NEW (vb_buf y) ltac:(unfold parse_blocks; right; left; right; reflexivity)) as [EQ|EQ]; [exact (NBp EQ)| rewrite EQ in Lp; discriminate Lp].
      - (* [comment removed for export] *) intros p Hp. unfold parse_blocks in Hp. cbn [option_map] in Hp.
        destruct Hp as [Hp|[[Hp|Hp]|Hp]].
        + apply NEW. unfold parse_blocks. left. exact Hp.
        + apply NEW. unfold parse_blocks. right. left. left. exact Hp.
        + subst p. destruct REL as [EQ|[E1 E2]].
          * rewrite EQ. apply NEW. unfold parse_blocks. right. left. right. reflexivity.
          * destruct (Z.eq_dec (vb_buf y1) (pe_b E)) as [EQ|NEQ]; [left; exact EQ| right].
            destruct (a_live (pe_A0 E) (vb_buf y1)) as [k|] eqn:EK; [| reflexivity].
            pose proof (KEEP _ _ EK NEQ) as LA. rewrite LA in E1. discriminate E1.
        + apply NEW. unfold parse_blocks. right. right. exact Hp.
      - (* [comment removed for export] *)
        eapply (cframe_step_call E x (after_putc x y1) A A1 _ _ (pe_sp E - 320) 8336);
          [ rewrite EVA; exact CF | exact CF1 | rewrite PARSE_STACK_val; klia W0 | klia W0
          | eapply parse_window_mapped; [exact PE| exact ST1| exact FR1]
          | intros a [Ha|Ha]; unfold pzone, parse_new; rewrite EVA; right; right; left; unfold vsb_blocks;
            [ right; exact Ha | left; left; split; [exact ANZ| exact Ha] ]
          | intros a Ha; unfold after_putc, parse_new in Ha; cbn [x_v x_vv x_va x_vi x_vio option_map] in Ha;
            unfold vsb_blocks in Ha;
            destruct Ha as [Ha|[[Ha|Ha]|Ha]];
            [ right; unfold pzone, parse_new; right; left; exact Ha
            | right; unfold pzone, parse_new, vsb_blocks; rewrite EVA; right; right; left; left; exact Ha
            | left; exact Ha
            | right; unfold pzone, parse_new; right; right; right; exact Ha ] ].
      - (* [comment removed for export] *) klia WL LEN1.
      - (* [comment removed for export] *) lazymatch goal with |- _ - (_ + _ + ?s' / 4096) <= _ <= _ =>
          lazymatch type of SC with _ - (_ + _ + ?s / 4096) <= _ <= _ =>
            assert (DV : s / 4096 <= s' / 4096) by (apply Z.div_le_mono; klia LEN1) end end.
        revert SC SCC1 DV. clear. intros; lia.
      - (* [comment removed for export] *)
        split; [| exact (proj2 PPH)]. eapply (vsb_phi_putc y y1); [exact (proj1 PPH)| klia VIa'| klia VIa'| exact LEN1| exact STEP1].
      - (* [comment removed for export] *)
        eapply (pc_xfer _ _ _ _ _ _ _ _ PC PCC1). unfold after_putc. pc_unfold. cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi]. rewrite EVA, STx. klia LEN1. }
    exact (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 m1 md1 y1 _ eq_refl PI1 AINV1 (amd_frame_trans _ _ _ MDF0 MDF1) ltac:(klia LEN1) FR1).
  Qed.
End S.
End A_PPutc.

   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
Local Tactic Notation "klia" ne_hyp_list(hs) := try (generalize alloc_ceiling_val); clear - hs; try pose proof alloc_ceiling_val; lia.

Lemma DESTROY_STACK_val : DESTROY_STACK = 8224.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition vep_pre36 (v : vep) (q : vep_pads) : list cell :=
  vep_pre33 v q ++ [C8 (Z_to_bv 64 (v Fesicmt)); C8 (Z_to_bv 64 (v Fesicmt_p)); C8 (Z_to_bv 64 (v Fattr))].
Definition vep_post37 (v : vep) (tag : list byte) (q : vep_pads) : list cell :=
  [ C4 (Z_to_bv 64 (v Fattr_delim)); CB 4 (p236 q); C8 (Z_to_bv 64 (v Fmatch)); C8 (Z_to_bv 64 (v Fmatch_hit));
    CB 8 tag; C4 (Z_to_bv 64 (v Ftag_i)); CB 4 (p268 q); C8 (Z_to_bv 64 (v Fdostuff));
    C8 (Z_to_bv 64 (v Finclude_src)); C4 (Z_to_bv 64 (v Finclude_continue)); C4 (Z_to_bv 64 (v Fnm_skip)); C4 (Z_to_bv 64 (v Fnm_verbatim));
    C4 (Z_to_bv 64 (v Fnm_pending)); C4 (Z_to_bv 64 (v Flast_mark)); CB 4 (p308 q) ].
Lemma vep_cells_split_attr : forall v tag q,
  vep_cells v tag q = vep_pre36 v q ++ [C8 (Z_to_bv 64 (v Fattr_vsb))] ++ vep_post37 v tag q.
Proof. intros; reflexivity. Qed.
Lemma vep_cells_attr0 : forall v tag q,
  vep_cells (fupd v Fattr_vsb 0) tag q = vep_pre36 v q ++ [C8 (Z_to_bv 64 0)] ++ vep_post37 v tag q.
Proof. intros; reflexivity. Qed.
Lemma vep_pre36_size : forall v q, cells_size (vep_pre36 v q) = 224%nat.
Proof. intros; reflexivity. Qed.
Lemma vep_post37_size : forall v tag q, cells_size (vep_post37 v tag q) = 80%nat.
Proof. intros; reflexivity. Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HDS : VSB_destroy_stmt.

  #[using="HDS"] Lemma destroy_attr : forall (E : penv) (x : pst) (A : AS) (m m2 : mem) (md md2 : Model) (T : TSet) (ret : Z)
      (W : list (Z * Z)) (v' : vep) (fj0 fj8 : word)
      (t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s6 s10 s11 t3 t4 t5 t6 : word) (ps : Z),
    penv_ok E -> pinv E x A (aview A m) -> ainv A m md -> ainv A m2 md2 ->
    munch W (aview A m) (aview A m2) -> wmono rsegs (aview A m) (aview A m2) ->
    wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x] W ->
    (forall a, h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320 -> outside W a) ->
    mem_inv rsegs (aview A m2) -> stk rsegs (aview A m2) (pe_lo E) (pe_fp E) -> rw_cells rsegs (aview A m2) (pe_fp E) (pframe E fj0 fj8) ->
    rw_cells rsegs (aview A m2) (pe_VEP E) (vep_cells v' (x_tag x) (x_q x)) ->
    v' Fattr_vsb = x_v x Fattr_vsb -> v' Finclude_src = x_v x Finclude_src ->
    x_va x <> None -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
    cframe LPA (owned (pe_A0 E)) (owned A) (pe_sp E) PARSE_STACK (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E))
           (parse_new v' (x_vv x) (x_va x) (x_vio x)) (pe_v0 E) (aview A m2) ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A1 : AS) (m1 : mem) (md1 : Model) (ya : vsb_rec),
        x_va x = Some ya ->
        ainv A1 m1 md1 -> mem_inv rsegs (aview A1 m1) -> amd_frame md2 md1 ->
        stk rsegs (aview A1 m1) (pe_lo E) (pe_fp E) -> rw_cells rsegs (aview A1 m1) (pe_fp E) (pframe E fj0 fj8) ->
        rw_cells rsegs (aview A1 m1) (pe_VEP E) (vep_cells (fupd v' Fattr_vsb 0) (x_tag x) (x_q x)) ->
        henv_ok LPA VIA (pe_H E) A1 (aview A1 m1) -> data_obj LPA A1 (aview A1 m1) (pe_DATA E) (pe_inp E) ->
        vsb_obj LPA A1 (aview A1 m1) (pe_S E) (x_vv x) false ->
        a_live A1 (pe_wa E) = Some 40 -> a_live A1 (pe_VEP E) = Some 312 ->
        vi_world E (PST (x_p x) (x_st x) (fupd v' Fattr_vsb 0) (x_tag x) (x_q x) (x_vv x) None (x_vi x)) A1 (aview A1 m1) ->
        stack_shadow LPA (aview A1 m1) (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64) ->
        a_livebytes A1 = a_livebytes A - 40 - vb_size ya -> a_nlive A1 = a_nlive A - 2 -> a_tinycred A1 = a_tinycred A ->
        a_seccred A1 = a_seccred A -> a_primcred A1 = a_primcred A (* [comment removed for export] *) -> frames_same A A1 ->
        (forall p k, a_live (pe_A0 E) p = Some k -> p <> pe_b E -> a_live A1 p = Some k) ->
        cframe LPA (owned (pe_A0 E)) (owned A1) (pe_sp E) PARSE_STACK (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E))
               (parse_new (fupd v' Fattr_vsb 0) (x_vv x) None (x_vio x)) (pe_v0 E) (aview A1 m1) ->
        srealizes rsegs (mkCfg (call_ms E ret ps (Z_to_bv 64 ret) t0' t1' t2' s1 a0' a1' a2' a3' a4' a5' a6' a7' s6 s10 s11 t3' t4' t5' t6' m1) md1) T) ->
    srealizes rsegs (mkCfg (call_ms E VSB_destroy_entry ps (Z_to_bv 64 ret) t0 t1 t2 s1
                               (Z_to_bv 64 (pe_VEP E + 224)) a1 a2 a3 a4 a5 a6 a7 s6 s10 s11 t3 t4 t5 t6 m2) md2) T.
  Proof.
    intros until ps. intros PE PI AINV0 AINV2 MU WM WZ NCNT MI2 STK2 FR2 VEPC2 EAV EIS VNN RR RET CF2 K.
    pose proof PI as PI0.
    world_open PE PI AINV0. unfold call_ms in K |- *. cbv zeta in K |- *. rewrite EFP in *.
    clear VEPC FR STK MI SHV0.
    (* [comment removed for export] *)
    assert (VSBO2 : vsb_obj LPA A (aview A m2) (pe_S E) (x_vv x) false)
      by (eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV0 HFR MU WM WZ); [in_list| in_list| exact VSBO]).
    assert (DATA2 : data_obj LPA A (aview A m2) (pe_DATA E) (pe_inp E))
      by (eapply (data_obj_stores _ _ _ _ _ _ _ PE0 AINV0 HFR MU WM WZ); [in_list| exact DATA]).
    assert (HENV2 : henv_ok LPA VIA (pe_H E) A (aview A m2))
      by (eapply (henv_stores _ _ _ _ _ _ _ PE0 AINV0 HFR MU WM WZ); [exact NCNT| exact HENV]).
    assert (SS2 : stack_shadow LPA (aview A m2) (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64))
      by (eapply (stack_shadow_stores _ _ _ _ _ _ _ PE0 AINV0 HFR MU WM WZ); exact SS).
    destruct (x_va x) as [ya|] eqn:EVA; [| exfalso; exact (VNN eq_refl)].
    (first [ dand5 VA as ANZ AOBJ0 ASZ ALEN AAP | destruct VA as (ANZ & AOBJ0 & ASZ & ALEN & AAP) ]).
    assert (AOBJ2 : vsb_obj LPA A (aview A m2) (x_v x Fattr_vsb) ya false)
      by (eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV0 HFR MU WM WZ); [in_list| in_list| exact AOBJ0]).
    assert (VI2 : match x_vi x with None => x_v x Finclude_src = 0 | Some yi =>
                    x_v x Finclude_src <> 0 /\ vsb_obj LPA A (aview A m2) (x_v x Finclude_src) yi true /\ vb_error yi = 0 /\
                    vb_size yi <= vb_len yi + 4096 /\ vb_len yi <= x_p x - pe_DATA E /\
                    vsb_apart (x_v x Finclude_src) yi [pe_VEP E; pe_wa E; pe_DATA E; pe_S E; vb_buf (x_vv x)] end).
    { destruct (x_vi x) as [yi|] eqn:EVI; [| exact VI]. (first [ dand7 VI as I1 I2 I3 I4 I5 I6 _ | destruct VI as (I1 & I2 & I3 & I4 & I5 & I6 & _) ]).
      refine (conj I1 (conj _ (conj I3 (conj I4 (conj I5 I6))))).
      eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV0 HFR MU WM WZ); [in_list| in_list| exact I2]. }
    clear VSBO DATA HENV SS AOBJ0 VI.
    (first [ pose proof (AOBJ2) as dR_3; dand6 dR_3 as _ _ LAS LAB ASB _ | pose proof AOBJ2 as (_ & _ & LAS & LAB & ASB & _) ]).
    unfold oabuf in *. rewrite ?EVA in *. cbn [oabuf x_va] in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI.
    pose proof (as_live_disjoint LPA A _ _ _ _ _ _ AINV0 LAS LVEP D_AV) as DXS.
    pose proof (as_live_disjoint LPA A _ _ _ _ _ _ AINV0 LAB LVEP D_ABV) as DXB.
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV0 LAS)) as dR_4; dand5 dR_4 as _ _ SAlo SAhi _ | destruct (live_geomP LPA _ _ _ _ _ AINV0 LAS) as (_ & _ & SAlo & SAhi & _) ]).
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV0 LAB)) as dR_5; dand5 dR_5 as B0 _ BAlo BAhi _ | destruct (live_geomP LPA _ _ _ _ _ AINV0 LAB) as (B0 & _ & BAlo & BAhi & _) ]).
    unfold kHighMemBeg in SAlo, BAlo. all_app_facts.
    (* [comment removed for export] *)
    rewrite vep_cells_split_attr in VEPC2. rewrite EAV in VEPC2.
    lazymatch type of VEPC2 with rw_cells _ _ _ (_ ++ ?mid ++ ?post) =>
      destruct (proj1 (rw_cells_app rsegs _ (pe_VEP E) (vep_pre36 v' (x_q x)) (mid ++ post)) VEPC2) as [VPRE V3] end.
    clear VEPC2. rewrite vep_pre36_size in V3. change (Z.of_nat 224) with 224 in V3.
    lazymatch type of V3 with rw_cells _ _ _ (?mid ++ ?post) =>
      destruct (proj1 (rw_cells_app rsegs _ (pe_VEP E + 224) mid post) V3) as [VMID VPOST] end.
    clear V3. cbn [cells_size csize Nat.add] in VPOST. replace (pe_VEP E + 224 + Z.of_nat 8) with (pe_VEP E + 232) in VPOST by (clear; lia).
    assert (W0 : 0 <= 8224) by (clear; lia).
    eapply (HDS _ _ _ _ t0 t1 t2 _ s1 _ a1 a2 a3 a4 a5 a6 a7 _ _ _ s6 _ _ _ _ s10 s11 t3 t4 t5 t6 _ _ _ _ A (pe_VEP E + 224) (x_v x Fattr_vsb) ya false (pe_lo E) T);
      [ exact AINV2 | exact MI2 | reflexivity | exact VMID
      | eapply cobj_block; [exact LVEP| cbn; intros [X|[X|[]]]; [exact (D_AV X)| exact (D_ABV X)]| klia VEPlo| klia VEPlo]
      | try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia | klia VEPhi
      | exact AOBJ2 | reflexivity
      | rewrite unsigned_lit by (klia FRB); rewrite Zminus_mod, SP16; reflexivity
      | rewrite unsigned_lit by (klia FRB); exact STK2 | exact CEIL
      | rewrite unsigned_lit by (klia FRB); rewrite DESTROY_STACK_val; klia LOP | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1. cbv zeta.
    intros AINV1 MI1 MDF1 FSA LB1 TC1 NL1 SCC1 PCC1 STK1 PS0 DEADS DEADB LQ CF1.   (* [comment removed for export] *)
    rewrite unsigned_lit in STK1, CF1 by (klia FRB). rewrite DESTROY_STACK_val in CF1.
    rewrite (ret_pc_even ret RR RET).
    pose proof (frames_same_fs A A1 FSA) as FS.
    assert (WIN : alloc_ceiling <= pe_sp E - 320 - 8224) by (klia LOP CEIL).
    (* [comment removed for export] *)
    assert (LK : forall p k, a_live A p = Some k -> p <> x_v x Fattr_vsb -> p <> vb_buf ya -> a_live A1 p = Some k)
      by (intros p k Hp N1 N2; rewrite (LQ p N1 N2); exact Hp).
    assert (LVEP1 : a_live A1 (pe_VEP E) = Some 312) by (apply (LK _ _ LVEP); [exact (not_eq_sym D_AV)| exact (not_eq_sym D_ABV)]).
    assert (WAL1 : a_live A1 (pe_wa E) = Some 40) by (apply (LK _ _ WAL); [exact (not_eq_sym D_AW)| exact (not_eq_sym D_ABW)]).
    assert (LDATA1 : a_live A1 (pe_DATA E) = Some (Z.of_nat (length (pe_inp E)))) by (apply (LK _ _ LDATA); [exact (not_eq_sym D_AD)| exact (not_eq_sym D_ABD)]).
    assert (LVS1 : a_live A1 (pe_S E) = Some 40) by (apply (LK _ _ LVS); [exact (not_eq_sym D_AS)| exact (not_eq_sym D_ABS)]).
    assert (LVB1 : a_live A1 (vb_buf (x_vv x)) = Some (vb_size (x_vv x))) by (apply (LK _ _ LVB); [exact (not_eq_sym D_AB)| exact (not_eq_sym D_ABB)]).
    (* [comment removed for export] *)
    assert (CVX : forall excl, ~ In (x_v x Fattr_vsb) excl -> ~ In (vb_buf ya) excl -> ~ In (pe_VEP E) excl ->
                  vcover (pe_H E) A excl (fun a => newblk (x_v x Fattr_vsb) 40 a \/ newblk (vb_buf ya) (vb_size ya) a \/ (pe_VEP E + 224 <= a < pe_VEP E + 224 + 8))).
    { intros excl N1 N2 N3 a [Ha|[Ha|Ha]].
      - eapply cover_newblk; [exact LAS| exact N1| exact Ha].
      - eapply cover_newblk; [exact LAB| exact N2| exact Ha].
      - eapply cover_rng; [exact LVEP| exact N3| klia Ha]. }
    assert (HC : hcover A [] (fun a => newblk (x_v x Fattr_vsb) 40 a \/ newblk (vb_buf ya) (vb_size ya) a \/ (pe_VEP E + 224 <= a < pe_VEP E + 224 + 8))).
    { intros a [Ha|[Ha|Ha]].
      - eapply hcover_newblk; [exact LAS| intros []| exact Ha].
      - eapply hcover_newblk; [exact LAB| intros []| exact Ha].
      - eapply hcover_rng; [exact LVEP| intros []| klia Ha]. }
    (* [comment removed for export] *)
    assert (FR1 : rw_cells rsegs (aview A1 m1) (pe_sp E - 320) (pframe E fj0 fj8)).
    { eapply (pframe_call E A A1 m2 md2 _ _ _ _ _ [] fj0 fj8);
        [exact PE| exact AINV2| exact CF1| exact HFR| exact WIN| exact W0| unfold pe_fp, PARSE_FRAME; klia WIN| apply CVX; intros []| unfold pframe; cbv zeta; exact FR2]. }
    assert (DATA1 : data_obj LPA A1 (aview A1 m1) (pe_DATA E) (pe_inp E)).
    { eapply (data_obj_call (pe_H E) A A1 m2 md2 _ _ _ _ _ [pe_DATA E] AINV2 CF1 HFR WIN);
        [apply CVX; wz_not_in | left; reflexivity| exact LDATA1| exact DATA2]. }
    assert (VSBO1 : vsb_obj LPA A1 (aview A1 m1) (pe_S E) (x_vv x) false).
    { eapply (vsb_obj_call (pe_H E) A A1 m2 md2 _ _ _ _ _ [pe_S E; vb_buf (x_vv x)] AINV2 CF1 HFR WIN);
        [apply CVX; wz_not_in
        | left; reflexivity| right; left; reflexivity| exact LVS1| exact LVB1| exact VSBO2]. }
    assert (HENV1 : henv_ok LPA VIA (pe_H E) A1 (aview A1 m1)).
    { eapply (henv_call (pe_H E) A A1 m2 md2 _ _ _ _ _ [] AINV2 CF1 WIN); [exact HC| exact FS| exact HENV2]. }
    assert (SS1 : stack_shadow LPA (aview A1 m1) (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64)).
    { eapply (stack_shadow_call (pe_H E) A A1 m2 md2 _ _ _ _ _ [] AINV2 CF1 HFR WIN); [apply CVX; intros []| rewrite PARSE_STACK_val; klia LOP CEIL ACV| exact SS2]. }
    assert (VI1 : vi_world E (PST (x_p x) (x_st x) (fupd v' Fattr_vsb 0) (x_tag x) (x_q x) (x_vv x) None (x_vi x)) A1 (aview A1 m1)).
    { unfold vi_world. cbn [x_vi x_v x_va x_p x_vv]. psimp. rewrite EIS.
      destruct (x_vi x) as [yi|] eqn:EVI; [| exact VI2]. (first [ dand6 VI2 as I1 I2 I3 I4 I5 I6 | destruct VI2 as (I1 & I2 & I3 & I4 & I5 & I6) ]).
      (first [ pose proof (I2) as dR_7; dand5 dR_7 as _ _ LIS LIB _ | pose proof I2 as (_ & _ & LIS & LIB & _) ]).
      unfold oibuf in D_IBV, D_IBS, D_IBB, D_IBD, D_IBW. rewrite EVI in D_IBV, D_IBS, D_IBB, D_IBD, D_IBW.
      unfold oibuf in D_AI. rewrite EVI in D_AI. cbn beta iota in D_AI. (first [ pose proof ((D_AI ltac:(discriminate) ltac:(discriminate))) as dR_8; dand4 dR_8 as NIA NIB NIbA NIbB | destruct (D_AI ltac:(discriminate) ltac:(discriminate)) as (NIA & NIB & NIbA & NIbB) ]).
      refine (conj I1 (conj _ (conj I3 (conj I4 (conj I5 (conj I6 I)))))).
      eapply (vsb_obj_call (pe_H E) A A1 m2 md2 _ _ _ _ _ [x_v x Finclude_src; vb_buf yi] AINV2 CF1 HFR WIN);
        [ apply CVX; wz_not_in
        | left; reflexivity| right; left; reflexivity
        | apply (LK _ _ LIS); [exact NIA| exact NIB]
        | apply (LK _ _ LIB); [exact NIbA| exact NIbB]
        | exact I2 ]. }
    (* [comment removed for export] *)
    assert (AVX : forall a n, pe_VEP E <= a -> a + n <= pe_VEP E + 312 -> (a + n <= pe_VEP E + 224 \/ pe_VEP E + 232 <= a) -> 0 <= n ->
                  avoids_call (pe_sp E - 320) 8224 (fun a0 => newblk (x_v x Fattr_vsb) 40 a0 \/ newblk (vb_buf ya) (vb_size ya) a0 \/ (pe_VEP E + 224 <= a0 < pe_VEP E + 224 + 8)) a n).
    { intros a n H1 H2 H3 H4. split; [left; klia H2 VEPhi CEIL LOP ACV|]. intros i Hi [X|[X|X]].
      - destruct X as [[_ X]|[_ X]]; [klia X DXS H1 H2 Hi| pose proof (live_sh_low A m md _ _ _ AINV0 LAS X) as SL; rewrite SHMAX_val in SL; klia SL VEPlo H1 Hi].
      - destruct X as [[_ X]|[_ X]]; [klia X DXB H1 H2 Hi| pose proof (live_sh_low A m md _ _ _ AINV0 LAB X) as SL; rewrite SHMAX_val in SL; klia SL VEPlo H1 Hi].
      - klia X H3 Hi H4. }
    assert (VEPC1 : rw_cells rsegs (aview A1 m1) (pe_VEP E) (vep_cells (fupd v' Fattr_vsb 0) (x_tag x) (x_q x))).
    { rewrite vep_cells_attr0.
      apply (proj2 (rw_cells_app rsegs _ (pe_VEP E) (vep_pre36 v' (x_q x)) _)). rewrite vep_pre36_size. split.
      - eapply (rw_cells_ccall LPA A A1 _ _ _ _ _ _ CF1); [| | exact VPRE]; rewrite vep_pre36_size.
        + eapply (crange_block (L:=LPA)); [exact AINV2| exact LVEP| klia VEPlo| change (Z.of_nat 224) with 224; klia VEPlo| clear; lia].
        + apply AVX; change (Z.of_nat 224) with 224; klia VEPlo.
      - change (Z.of_nat 224) with 224.
        apply (proj2 (rw_cells_app rsegs _ (pe_VEP E + 224) [C8 (Z_to_bv 64 0)] _)). split; [exact PS0|].
        cbn [cells_size csize Nat.add]. replace (pe_VEP E + 224 + Z.of_nat 8) with (pe_VEP E + 232) by (clear; lia).
        eapply (rw_cells_ccall LPA A A1 _ _ _ _ _ _ CF1); [| | exact VPOST]; rewrite vep_post37_size.
        + eapply (crange_block (L:=LPA)); [exact AINV2| exact LVEP| klia VEPlo| change (Z.of_nat 80) with 80; klia VEPlo| clear; lia].
        + apply AVX; change (Z.of_nat 80) with 80; klia VEPlo. }
    (* [comment removed for export] *)
    assert (CFX : cframe LPA (owned (pe_A0 E)) (owned A1) (pe_sp E) PARSE_STACK (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E))
                         (parse_new (fupd v' Fattr_vsb 0) (x_vv x) None (x_vio x)) (pe_v0 E) (aview A1 m1)).
    { pose proof (cframe_step_call E (PST (x_p x) (x_st x) v' (x_tag x) (x_q x) (x_vv x) (Some ya) (x_vi x))
                    (PST (x_p x) (x_st x) (fupd v' Fattr_vsb 0) (x_tag x) (x_q x) (x_vv x) None (x_vi x)) A A1 (aview A m2) (aview A1 m1) (pe_sp E - 320) 8224) as STEP.
      cbn [x_v x_vv x_va x_vi x_vio x_p x_st option_map] in STEP. unfold x_vio in CF2 |- *. rewrite ?EVA in CF2. cbn [option_map] in CF2 |- *.
      eapply STEP;
        [ exact CF2 | exact CF1 | rewrite PARSE_STACK_val; klia W0 | klia W0
        | eapply parse_window_mapped; [exact PE| exact STK1| exact FR1]
        | intros a [Ha|[Ha|Ha]]; unfold pzone, parse_changed, parse_new; cbn [x_v x_vv x_va x_vi x_vio option_map];
          [ right; right; left; unfold vsb_blocks; rewrite EAV; left; exact Ha
          | right; right; left; unfold vsb_blocks; right; exact Ha
          | left; left; split; [klia VEPlo| klia Ha] ]
        | intros a Ha; right; unfold pzone, parse_new; cbn [x_v x_vv x_va x_vi x_vio option_map]; right;
          unfold parse_new in Ha; destruct Ha as [Ha|[Ha|Ha]]; [left; exact Ha| destruct Ha| right; right; exact Ha] ]. }
    assert (KEEP1 : forall p k, a_live (pe_A0 E) p = Some k -> p <> pe_b E -> a_live A1 p = Some k).
    { intros p k Lp NBp. pose proof (KEEP p k Lp NBp) as LA. apply (LK _ _ LA).
      - intros ->. destruct (NEW (x_v x Fattr_vsb) ltac:(unfold parse_blocks; right; left; left; reflexivity)) as [X|X]; [exact (NBp X)| rewrite X in Lp; discriminate Lp].
      - intros ->. destruct (NEW (vb_buf ya) ltac:(unfold parse_blocks; right; left; right; reflexivity)) as [X|X]; [exact (NBp X)| rewrite X in Lp; discriminate Lp]. }
    exact (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 m1 md1 ya eq_refl AINV1 MI1 MDF1 STK1 FR1 VEPC1 HENV1 DATA1 VSBO1 WAL1 LVEP1 VI1 SS1 LB1 NL1 TC1 SCC1 PCC1 FSA KEEP1 CFX).
  Qed.
End S.

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
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_Cocsh B_Co6gg B_Leaves.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, ASSERT_STACK, ASSERT_STATE_STACK, INDENT_STACK, DATA_STACK, LEN_STACK, FINISH_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma assert_VSB_integrity_ok : assert_VSB_integrity_stmt.
  Proof.
    unfold assert_VSB_integrity_stmt.
    intros until lo. intros A0 VSBC VINV SHD CE SAL Slo Shi ST LO CEIL MI.
    rewrite A0. unfold assert_VSB_integrity_entry, ASSERT_STACK in *.
    (first [ dand8 SHD as P NP SHS PAL P0 PLE PGE PCE | destruct SHD as (P & NP & SHS & PAL & P0 & PLE & PGE & PCE) ]). fold_cl_segs.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC.
    (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vb16 | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vb16) ]).
    unfold vsb_cells in VSBC.
    pose proof alloc_ceiling_num as ACV. unfold kHighMemBeg in Slo. all_app_facts.
    pose proof (shpat_sh_boundL (Clg:=Clg) P NP ltac:(lia) ltac:(lia) ltac:(lia)) as SHPB.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] v) as MU.
    pose proof (wmono_refl rsegs v) as WM.
    open_map_cells MC.
    carve_frame 32%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K. { dead K. } clear K.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K. { exfalso. apply K. apply land7_of_mod8; lia. } clear K.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk SHS 4%Z 11.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. revert K. vm_compute. congruence. } clear K.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHS 8%Z. zstep. zstep. if_cases K; zify_cond K. { dead K. } clear K.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHS 8%Z.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHS 8%Z.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K; zify_cond K. { dead K. } clear K.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold vsb_leaf_post, leaf_post.
    do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.

  (* [comment removed for export] *)
  Ltac vsb_leaf_prologue A0 SHD CE VINV VSBC ST W sp lo v :=
    rewrite A0;
    let P := fresh "P" in let NP := fresh "NP" in let SHS := fresh "SHS" in
    let PAL := fresh "PAL" in let P0 := fresh "P0" in let PLE := fresh "PLE" in let PGE := fresh "PGE" in let PCE := fresh "PCE" in
    (first [ dand8 SHD as P NP SHS PAL P0 PLE PGE PCE | destruct SHD as (P & NP & SHS & PAL & P0 & PLE & PGE & PCE) ]); fold_cl_segs;
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC;
    pose proof VINV as VINV0;
    let Vsz := fresh "Vsz" in let Vlen := fresh "Vlen" in let Verr := fresh "Verr" in let Vind := fresh "Vind" in
    let Vfl := fresh "Vfl" in let Vb0 := fresh "Vb0" in let Vb47 := fresh "Vb47" in let Vb16 := fresh "Vb16" in
    (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vb16 | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vb16) ]);
    pose proof alloc_ceiling_num as ACV; unfold kHighMemBeg in *; all_app_facts;
    pose proof (shpat_sh_boundL (Clg:=Clg) P NP ltac:(lia) ltac:(lia) ltac:(lia)) as SHPB;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption);
    pose proof (munch_refl [(bv_unsigned sp - W, bv_unsigned sp)] v) as MU;
    pose proof (wmono_refl rsegs v) as WM;
    pose proof (rw_cells_bound _ _ _ _ VSBC) as SB; rewrite vsb_cells_size in SB; unfold vsb_cells in VSBC;
    open_map_cells MC.

  (* [comment removed for export] *)
  Ltac call_assert SHS CE MU VSBC VINV0 STc :=
    icall (assert_VSB_integrity_ok)
      by (try rewrite unsigned_lit by lia; unfold ASSERT_STACK, kHighMemBeg;
          first [ reflexivity
                | exact VSBC
                | exact VINV0
                | (eexists _, _; split; [exact SHS| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia])
                | (eapply cenv_munch; [exact CE| exact MU| repeat constructor; unfold const_free_ivl, CONSTS_TOP; cbn; lia])
                | exact STc
                | assumption
                | lia ]).

  (* [comment removed for export] *)
  Ltac call_assert_state SHS CE MU VSBC VINV0 STc :=
    icall (assert_VSB_state_ok)
      by (try rewrite unsigned_lit by lia; unfold ASSERT_STATE_STACK, kHighMemBeg;
          first [ reflexivity
                | exact VSBC
                | exact VINV0
                | (eexists _, _; split; [exact SHS| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia])
                | (eapply cenv_munch; [exact CE| exact MU| repeat constructor; unfold const_free_ivl, CONSTS_TOP; cbn; lia])
                | exact STc
                | assumption
                | lia ]).

  (* [comment removed for export] *)
  Ltac vsb_leaf_ret FR sp :=
    try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia; try rewrite (Z_to_bv_bv_unsigned sp);
    lazymatch goal with STx : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      release_frame FR STx (bv_unsigned sp) end;
    apply evt_done; hnf;
    (* [comment removed for export] *)
    repeat (lazymatch goal with |- ex _ => eexists | |- word => exact (Z_to_bv 64 0) end);
    split; [reflexivity|];
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma VSB_data_ok : VSB_data_stmt.
  Proof.
    unfold VSB_data_stmt.
    intros until lo. intros A0 VSBC VINV SHD CE SAL Slo Shi ST LO CEIL MI.
    unfold VSB_data_entry, DATA_STACK, ASSERT_STACK in *.
    vsb_leaf_prologue A0 SHD CE VINV VSBC ST 64 sp lo v.
    carve_frame 32%nat ST.
    do 4 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. call_assert SHS CE MU VSBC VINV0 ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with STx : stk _ _ lo _ |- _ => call_assert_state SHS CE MU VSBC VINV0 STx end.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K. { dead K. } clear K.
    zstep. zstep. if_cases K; zify_cond K. { exfalso. apply K. apply land7_of_mod8; lia. } clear K.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHS 8%Z.
    zstep.
    (* [comment removed for export] *)
    do 4 zstep. zstep. vsb_leaf_ret FR sp.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma VSB_len_ok : VSB_len_stmt.
  Proof.
    unfold VSB_len_stmt.
    intros until lo. intros A0 VSBC VINV SHD CE SAL Slo Shi ST LO CEIL MI.
    unfold VSB_len_entry, LEN_STACK, ASSERT_STACK in *.
    vsb_leaf_prologue A0 SHD CE VINV VSBC ST 64 sp lo v.
    carve_frame 32%nat ST.
    do 4 zstep.
    zstep. zstep. zstep. zstep.
    zstep. call_assert SHS CE MU VSBC VINV0 ST.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K. { dead K. } clear K.
    zstep. zstep. if_cases K; zify_cond K. { exfalso. apply K. apply land7_of_mod8; lia. } clear K.
    (* [comment removed for export] *)
    zstep. shadow_chk SHS 4%Z 12.
    zstep.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. shadow_chk0 SHS 8%Z. zstep.
      do 4 zstep. zstep.
      pose proof Verr as E; rewrite E in *.   (* [comment removed for export] *)
      vsb_leaf_ret FR sp.
    - (* [comment removed for export] *)
      exfalso. rewrite Verr in K. revert K; vm_compute; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma vsb_indent_ok : vsb_indent_stmt.
  Proof.
    unfold vsb_indent_stmt.
    intros until lo. intros A0 VSBC VINV SHD CE SAL Slo Shi ST LO CEIL MI.
    unfold vsb_indent_entry, INDENT_STACK in *.
    vsb_leaf_prologue A0 SHD CE VINV VSBC ST 80 sp lo v.
    carve_frame 80%nat ST.
    do 10 zstep.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K. { exfalso. apply K. apply land7_of_mod8; lia. } clear K.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk SHS 4%Z 12.
    (* [comment removed for export] *)
    zstep. rewrite Vind. zstep. if_cases K; zify_cond K. 2:{ exfalso. revert K. vm_compute. congruence. } clear K.
    do 10 zstep. zstep.
    try replace (bv_unsigned sp + -80 + 80) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold vsb_leaf_post, leaf_post.
    do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.
End S.

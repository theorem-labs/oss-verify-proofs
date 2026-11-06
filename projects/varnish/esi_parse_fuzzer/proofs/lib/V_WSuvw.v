(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Img0 Img0 V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import R_strlen R_strcpy V_WSwg5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition REQ9 : list byte :=
  Eval vm_compute in match image_bytes rsegs 0x10577 9 with Some bs => bs | None => [] end.
Lemma REQ9_ro : ro_bytes_b rsegs 0x10577 REQ9 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma REQ9_eq : REQ9 = [Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 113] ++ Z_to_bv 8 0 :: skipn 4 REQ9.
Proof. reflexivity. Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  #[using="AI"] Lemma WS_Init_ok : WS_Init_stmt.
  Proof.
    unfold WS_Init_stmt.
    intros H junk40 junk32 lo. intros until m.
    intros A0 A1 A2 A3 WSC WEC GLOB HG IMG SPH ST LO CEIL MI.
    rewrite A0, A1, A2, A3. unfold WS_Init_entry. unfold WSINIT_STACK in *.
    pose proof alloc_ceiling_val as ACV.
    (first [ dand3 HG as G16 GCE GHI | destruct HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
    (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as EBSS BSS CP [cnt CNT] | pose proof GLOB as (EBSS & BSS & CP & [cnt CNT]) ]). rewrite EBSS in BSS. cbn [vi_bss VI0 al_segs LayoutP0] in BSS.
    cbn [al_segs LayoutP0] in CP, CNT.
    pose proof IMG as IMG0. (first [ dand5 IMG as _ _ _ GCP _ | destruct IMG as (_ & _ & _ & GCP & _) ]). unfold GOT_cp in GCP.
    rewrite Ews in WSC |- *. rewrite Ewb in WEC |- *.
    pose proof (rw_cells_bound _ _ _ _ WSC) as WSB. pose proof (rw_cells_bound _ _ _ _ WEC) as WEB.
    cbn [cells_size csize Nat.add] in WSB, WEB.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (h_sp H + 1080, h_sp H + 1080 + 40); (h_sp H + 16, h_sp H + 16 + 32)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (rw_CB_length _ _ _ _ _ WSC) as L40. pose proof (rw_CB_length _ _ _ _ _ WEC) as L32.
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB rsegs m (h_sp H + 1080) [] 40 junk40 [] [8; 8; 8; 8; 8]%nat WSC eq_refl) as WS1. clear WSC.
    pose proof (rw_cells_split_CB rsegs m (h_sp H + 16) [] 32 junk32 [] [4; 4; 8; 8; 8]%nat WEC eq_refl) as WE1. clear WEC.
    cbn [mk_CB_cells app] in WS1, WE1.
    carve_frame 48%nat ST.
    do 6 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases K; zify_cond K. 2:{ kill K. } clear K.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K. { kill K. } clear K.
    zstep. zstep. if_cases K; zify_cond K.
    { exfalso. apply K. apply land7_of_mod8; [lia|]. apply align_mod8_of16; [exact G16| reflexivity]. }
    clear K.
    zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch type of WS1 with rw_cells _ ?mx _ (_ :: ?rest) =>
      assert (WS2 : rw_cells rsegs mx (h_sp H + 1080)
                ([C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ++ rest))
        by (apply (rw_cells_recast _ _ _ _ _ WS1);
            [ cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; rewrite ?firstn_length, ?skipn_length; lia
            | reflexivity ]) end.
    clear WS1. cbn [app] in WS2.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (ro_bytes_at rsegs mx 0x10577 REQ9 ltac:(assumption) ltac:(lia) ltac:(cbn; lia) (ro_bytes_b_sound _ _ _ REQ9_ro)) as STR end.
    rewrite REQ9_eq in STR.
    call_lit strlen_spec by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ _ _ => rewrite unsigned_lit by lia; exact STR
      | |- ~ In _ _ => cbn; intros [X|[X|[X|X]]]; try discriminate X; exact X
      | |- mem_inv _ _ => assumption
      | |- _ => rewrite unsigned_lit by lia; cbn; lia
      end).
    clear POST STR. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch type of WS2 with rw_cells _ ?mx _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
      pose proof (proj1 (rw_cells_app rsegs mx (h_sp H + 1080) [c0] (c1 :: c2 :: c3 :: c4 :: rest)) WS2) as [WSa WSbc];
      pose proof (proj1 (rw_cells_app rsegs mx _ [c1; c2; c3; c4] rest) WSbc) as [WSb WSc] end.
    clear WS2 WSbc.
    pose proof (rwc_eq _ _ _ (h_sp H + 1084) _ WSb ltac:(cbn; lia)) as WSb'. clear WSb. rename WSb' into WSb.
    pose proof (rwc_eq _ _ _ (h_sp H + 1088) _ WSc ltac:(cbn; lia)) as WSc'. clear WSc. rename WSc' into WSc.
    call_lit (strcpy_req_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h_sp H + 1084) lo) by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- rw_cells _ _ _ _ => exact WSb
      | |- mem_inv _ _ => assumption
      | |- @eq word _ _ => reflexivity
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    match goal with X : rw_cells rsegs _ (h_sp H + 1084) _ |- _ => rename X into WID end.
    match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    zstep.
    (* [comment removed for export] *)
    assert (WS0P : forall mq,
      rw_cells rsegs mq (h_sp H + 1080) [C4 (Z_to_bv 64 905626964)] ->
      rw_cells rsegs mq (h_sp H + 1084) (map C1 REQ_BYTES) ->
      rw_cells rsegs mq (h_sp H + 1088) [C8 (Z_to_bv 64 (h_sp H + 16)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_sp H + 1032))] ->
      rw_cells rsegs mq (h_sp H + 16) [C4 (Z_to_bv 64 478787243); C4 (Z_to_bv 64 1016); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_sp H + 32))] ->
      ws0_obj LayoutP0 H mq).
    { intros mq Xa Xb Xc Xe.
      pose proof (rwc_eq _ _ _ (h_sp H + 1084 + Z.of_nat (cells_size (map C1 REQ_BYTES))) _ Xc ltac:(cbn; lia)) as Xc'.
      pose proof (proj2 (rw_cells_app rsegs mq (h_sp H + 1084) _ _) (conj Xb Xc')) as Xbc.
      pose proof (rwc_eq _ _ _ (h_sp H + 1080 + Z.of_nat (cells_size [C4 (Z_to_bv 64 905626964)])) _ Xbc ltac:(cbn; lia)) as Xbc'.
      pose proof (proj2 (rw_cells_app rsegs mq (h_sp H + 1080) _ _) (conj Xa Xbc')) as Xabc.
      cbn [map app REQ_BYTES] in Xabc.
      apply (ws0_obj_intro LayoutP0 H mq ws_id_req); [left; reflexivity| |].
      - unfold ws_cells, ws_rec_of, ws_id_req, WS_MAGIC. cbn [ws_id ws_s ws_f ws_r ws_e al_segs LayoutP0].
        rewrite Ews, Ewb. replace (h_sp H + 16 + 1016) with (h_sp H + 1032) by lia.
        apply (rw_cells_recast _ _ _ _ _ Xabc); [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity| reflexivity].
      - unfold wsemu_cells, wsemu_WS0, WS_EMU_MAGIC. cbn [we_len we_ws we_first we_last al_segs LayoutP0].
        rewrite Ewb. replace (h_sp H + 16 + 16) with (h_sp H + 32) by lia. exact Xe. }
    call_lit (WS_Assert_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H None lo) by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => exact ST
      | |- ws_state _ _ _ => cbn [ws_state]; apply WS0P; assumption
      | |- glob_ok _ _ _ _ => eapply (glob_ok_munch LayoutP0); [exact GLOB| exact MU| exact WM| intros a Ha; unfold h_cp, h_vsc in Ha; rewrite EBSS in Ha; cbn [vi_bss VI0] in Ha; cbn [outside]; lia]
      | |- henv_geom _ => split; [exact G16| split; [exact GCE| unfold HFRAME; lia]]
      | |- img_ok0 _ => eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG0]
      | |- mem_inv _ _ => assumption
      | |- @eq word _ _ => rewrite ?Ews; reflexivity
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    apply evt_done. unfold WS_Init_post.
    do 16 eexists. split; [reflexivity|]. split; [rewrite Ews, Ewb; exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [exact POST|]. split; [apply WS0P; assumption|].
    eapply (glob_ok_munch LayoutP0); [exact GLOB| exact MU| exact WM|].
    intros a Ha; unfold h_cp, h_vsc in Ha; rewrite EBSS in Ha; cbn [vi_bss VI0] in Ha; cbn [outside]; lia.
  Qed.
End S.

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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Po6qc A_Vsb A_World A_Img A_Cocsh A_VSe3i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
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

Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, ASSERT_STACK in H.
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
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia01
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot_lia_prev := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
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

  #[using="AI"] Lemma VSB_finish_ok : VSB_finish_stmt.
  Proof.
    unfold VSB_finish_stmt.
    intros until lo. intros A0 TP VSBC VINV U8 LBS ERR SHD SHDB SHDE CE SAL Slo Shi Blo Bhi DSB ST LO CEIL MI.
    rewrite A0, TP. change (cl_tp LPA) with (Z_to_bv 64 0x5e83d8).
    unfold VSB_finish_entry, FINISH_STACK, ASSERT_STACK, ERRNOA in *.
    (first [ dand8 SHD as P NP SHS PAL P0 PLE PGE PCE | destruct SHD as (P & NP & SHS & PAL & P0 & PLE & PGE & PCE) ]). fold_cl_segs.
    (first [ dand8 SHDB as Q NQ SHB QAL Q0 QLE QGE QCE | destruct SHDB as (Q & NQ & SHB & QAL & Q0 & QLE & QGE & QCE) ]). fold_cl_segs.
    (first [ dand8 SHDE as PE NE SHE EAL E0 ELE EGE ECE | destruct SHDE as (PE & NE & SHE & EAL & E0 & ELE & EGE & ECE) ]). fold_cl_segs.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC.
    pose proof VINV as VINV0. (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
    pose proof alloc_ceiling_num as ACV. unfold kHighMemBeg in *. all_app_facts.
    pose proof (shpat_sh_boundL (Clg:=Clg) P NP ltac:(lia) ltac:(lia) ltac:(lia)) as SHPB. rewrite SHMAX_val in SHPB.
    pose proof (shpat_sh_boundL (Clg:=Clg) Q NQ ltac:(lia) ltac:(lia) ltac:(lia)) as SHQB. rewrite SHMAX_val in SHQB.
    pose proof (shpat_sh_boundL (Clg:=Clg) PE NE ltac:(lia) ltac:(lia) ltac:(lia)) as SHEB. rewrite SHMAX_val in SHEB.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (rw_cells_bound _ _ _ _ VSBC) as SB. rewrite vsb_cells_size in SB. unfold vsb_cells in VSBC.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (S, S + 40); (vb_buf vr, vb_buf vr + vb_size vr); (6193972, 6193972 + 4)] v) as MU.
    pose proof (wmono_refl rsegs v) as WM.
    open_map_cells MC.
    carve_frame 32%nat ST.
    do 4 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    icall (assert_VSB_integrity_ok)
      by (try rewrite unsigned_lit by lia; unfold ASSERT_STACK, kHighMemBeg;
          first [ reflexivity
                | exact VSBC
                | exact VINV0
                | (eexists _, _; split; [exact SHS| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia])
                | (eapply cenv_munch; [exact CE| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; lia])
                | exact ST
                | assumption
                | lia ]).
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
    (* [comment removed for export] *)
    zstep. shadow_chk SHS 4 13.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (rw_cells_read_sub rsegs mx _ _ 34 1 VSBC ltac:(lia) ltac:(cbn; lia)) as RDF end.
    rewrite Vfl in RDF. unfold VSB_FLAGS_LIVE in RDF.
    match type of RDF with _ = Some ?r => let r' := eval vm_compute in r in change r with r' in RDF end.
    zstep. zstep. zstep. if_cases K5; zify_cond K5. { dead K5. } clear K5 RDF.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHS 8. zstep. shadow_chk0 SHS 8.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk SHB 1 14.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok rsegs _ _ _ (vb_len vr) _ U8 ltac:(lia) eq_refl) as SOK.
    zstep. rewrite le1_single. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    pose proof (u8arr_write rsegs _ _ _ (vb_len vr) (Z_to_bv 8 0) U8 ltac:(lia)) as U8'. clear U8. store_done.
    (* [comment removed for export] *)
    shadow_rechk SHS (S + 32) 4 12.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. rewrite Vfl. zstep.
    match type of VSBC with context [Z.lor ?x ?y] => let r := eval vm_compute in (Z.lor x y) in change (Z.lor x y) with r in VSBC end.
    (* [comment removed for export] *)
    shadow_chk SHS 4 12. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_addr_at SHE 6193972 4.
    match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
      let e' := eval vm_compute in e in change e with e' in RD end.
    lazymatch goal with |- evt ?segs ?Q _ =>
      eapply (evt_cut segs _ Q);
      [ zstep;
        let K := fresh "KS" in
        zstep; if_cases K; zify_cond K;
        [ first [ shadow_fast K; shadow_join 12 | shadow_dead | shadow_slow 12 ]
        | first [ shadow_fast K; shadow_join 12 | shadow_dead | shadow_slow 12 ] ]
      | let ms := fresh "ms" in let x := fresh "junk" in
        intros ms [x ->]; simp_regs ]
    end.
    shadow_cleanup.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    do 3 zstep. zstep. zstep.
    try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold VSB_finish_post, vsb_result, ERRNOA.
    pose proof Verr as E; rewrite E in *;   (* [comment removed for export] *)
      match goal with |- context [Z.b2z ?x + -1] => let r := eval vm_compute in (Z.b2z x + -1) in change (Z.b2z x + -1) with r end;
      match type of ERR with context [sx32 ?x] => let r := eval vm_compute in (sx32 x) in change (sx32 x) with r in ERR end;
      unfold V_Stgw7.ENOMEM; cbn [Z.eqb Pos.eqb];
      do 15 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]);
      (split; [unfold vsb_cells; cbn [vb_error vb_buf vb_size vb_len vb_flags vb_indent vsb_set_flags]; rewrite E; exact VSBC|]);
      (split; [exact U8'|]); (split; [exact ERR| exact ST]).
  Qed.
End S.

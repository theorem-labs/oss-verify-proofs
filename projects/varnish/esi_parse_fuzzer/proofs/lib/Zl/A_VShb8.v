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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Po6qc A_Img A_Cocsh B_Co6gg B_Leaves A_VSe3i A_VSa8f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.

Module A_VSbwu.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Po6qc A_Img A_Cocsh B_Co6gg B_Leaves A_VSe3i.
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

Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, ASSERT_STACK, ASSERT_STATE_STACK in H.
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

(* [comment removed for export] *)
Ltac dead_b2z :=
  repeat match goal with |- context [Z.lxor ?x 9223372036854775808] => rewrite (lxor_2_63 x) by lia end;
  repeat match goal with
  | |- context [?x =? ?y] => first [ rewrite (proj2 (Z.eqb_neq x y)) by lia | rewrite (proj2 (Z.eqb_eq x y)) by lia ]
  | |- context [?x <? ?y] => first [ rewrite (proj2 (Z.ltb_ge x y)) by lia | rewrite (proj2 (Z.ltb_lt x y)) by lia ]
  end;
  cbn; first [ congruence | lia | discriminate ].

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  #[using="AI"] Lemma VSB_finish_ok : VSB_finish_stmt.
  Proof.
    unfold VSB_finish_stmt.
    intros until lo. intros A0 TP VSBC VINV U8 LBS ERR SHD SHDB SHDE CE SAL Slo Shi Blo Bhi DSB ST LO CEIL MI.
    rewrite A0, TP. change (cl_tp LPA) with (Z_to_bv 64 0x5e7bd8).
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
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (S, S + 40); (vb_buf vr, vb_buf vr + vb_size vr); (6191924, 6191924 + 4)] v) as MU.
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
    zstep. zstep. zstep.
    icall (assert_VSB_state_ok)
      by (try rewrite unsigned_lit by lia; unfold ASSERT_STATE_STACK, kHighMemBeg;
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
    zstep. if_cases KU; zify_cond KU. { dead KU. } clear KU.
    zstep. zstep. if_cases KU; zify_cond KU. { exfalso. apply KU. apply land7_of_mod8; lia. } clear KU.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHS 8. zstep. shadow_chk0 SHS 8.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. dead_b2z. } clear KU.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. dead_b2z. } clear KU.
    (* [comment removed for export] *)
    zstep. if_cases KU; zify_cond KU. { dead KU. } clear KU.
    (* [comment removed for export] *)
    shadow_chk SHB 1 12.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok rsegs _ _ _ (vb_len vr) _ U8 ltac:(lia) eq_refl) as SOK.
    zstep. rewrite le1_single. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    pose proof (u8arr_write rsegs _ _ _ (vb_len vr) (Z_to_bv 8 0) U8 ltac:(lia)) as U8'. clear U8. store_done.
    (* [comment removed for export] *)
    zstep. shadow_chk SHS 4 12.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite Vfl. zstep.
    match type of VSBC with context [Z.lor ?x ?y] => let r := eval vm_compute in (Z.lor x y) in change (Z.lor x y) with r in VSBC end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KU; zify_cond KU. { dead KU. } clear KU.
    zstep. zstep. if_cases KU; zify_cond KU. { dead KU. } clear KU.
    (* [comment removed for export] *)
    zstep. shadow_chk SHS 4 12.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_addr_at SHE 6191924 4.
    match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
      let e' := eval vm_compute in e in change e with e' in RD end.
    lazymatch goal with |- evt ?segs ?Q _ =>
      eapply (evt_cut segs _ Q);
      [ zstep; zstep;
        let K := fresh "KS" in
        zstep; if_cases K; zify_cond K;
        [ first [ shadow_fast K; shadow_join 13 | shadow_dead | shadow_slow 13 ]
        | first [ shadow_fast K; shadow_join 13 | shadow_dead | shadow_slow 13 ] ]
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
End A_VSbwu.

   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, ASSERT_STACK, ASSERT_STATE_STACK, INDENT_STACK in H.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot_lia_prev := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@Vlen; @Slo; @LO; @SB; @SZ; @SR; @EM; @SPR; @Blo; @Vsz; @ACV; @Blo'; @LO0; @NS1; @Vb0; @KR0; @CEIL; @Shi; @KU; @H; @Vsz'; @Vb0'; @S8; @Vb47; @Vlen'; @LBS1; @NO; @LBS; @VNE; @DSB; @V16K; @V16C0; @VNE0; @DSB'; @X; @Verr; @Vind; @Vfl; @KX; @KR; @NS4; @LBY'; @VINV0; @PC; @Vbm'; @Vb47'; @VINV1; @Vbm; @E0])).
Ltac hot_lia_full := first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac dead_b2z :=
  repeat match goal with |- context [Z.lxor ?x 9223372036854775808] => rewrite (lxor_2_63 x) by lia end;
  repeat match goal with
  | |- context [?x =? ?y] => first [ rewrite (proj2 (Z.eqb_neq x y)) by lia | rewrite (proj2 (Z.eqb_eq x y)) by lia ]
  | |- context [?x <? ?y] => first [ rewrite (proj2 (Z.ltb_ge x y)) by lia | rewrite (proj2 (Z.ltb_lt x y)) by lia ]
  end;
  cbn; first [ congruence | lia | discriminate ].

Section S.
Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac vsb_leaf_call SPEC VSBC VINV0 SHS CE MU STc :=
    icall SPEC
      by (try rewrite unsigned_lit by lia; unfold ASSERT_STACK, ASSERT_STATE_STACK, INDENT_STACK, kHighMemBeg;
          first [ reflexivity
                | exact VSBC
                | exact VINV0
                | (eexists _, _; split; [exact SHS| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia])
                | (eapply cenv_munch; [exact CE| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; lia])
                | exact STc
                | assumption
                | lia ]);
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into STc end.

  (* [comment removed for export] *)
  Ltac putc_store_tail SHS SHB U8 E0 S vr a1 :=
    shadow_rechk0 SHS (S + 24) 8;
    (let KU := fresh "KU" in
     zstep; zstep; zstep; if_cases KU; zify_cond KU; [ exfalso; unsign KU; klia KU |]; clear KU);
    zstep; shadow_chk0 SHS 8; shadow_rechk0 SHS (S + 24) 8;
    zstep; zstep; zstep; zstep; zstep;
    (let KU := fresh "KU" in zstep; if_cases KU; zify_cond KU; [ exfalso; revert KU; dead_b2z |]; clear KU);
    (let KU := fresh "KU" in zstep; zstep; zstep; zstep; zstep; if_cases KU; zify_cond KU; [ exfalso; revert KU; dead_b2z |]; clear KU);
    (let KU := fresh "KU" in zstep; if_cases KU; zify_cond KU; [ exfalso; dead KU |]; clear KU);
    shadow_chk SHB 1 12;
    pose proof (u8arr_store_ok rsegs _ _ _ (vb_len vr) _ U8 ltac:(lia) eq_refl) as SOK;
    zstep; rewrite le1_single;
    pose proof (u8arr_write rsegs _ _ _ (vb_len vr) (Z_to_bv 8 (bv_unsigned a1)) U8 ltac:(lia)) as U8'; clear U8; store_done;
    shadow_rechk SHS (S + 4) 4 11;
    zstep; rewrite E0; zstep; zstep; do 8 zstep; zstep; zstep.

  #[using="AI16"] Lemma VSB_putc_ok : VSB_putc_stmt.
  Proof.
    unfold VSB_putc_stmt, frames_same.
    intros until T. cbv zeta. intros AINV MI A0 VOBJ EM LBY NLV SCM PCM TP SP16 ST CEIL LO K.   (* [comment removed for export] *)
    rewrite A0. pose proof alloc_ceiling_num as ACV.
    unfold PUTC_STACK, EXT_STACK, ASTK, EXT_MAX in *. unfold VSB_putc_entry.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (first [ pose proof ((vsb_obj_geom LPA A m md S vr false AINV VOBJ)) as dR_1; dand11 dR_1 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A m md S vr false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof (vsb_shadows LPA A m md S vr false AINV VOBJ) as [SHS SHB]. fold_cl_segs.
    pose proof VOBJ as VOBJ0. vsb_open VOBJ. (first [ dex1 VBUF as bs0; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs0 U8 LBS _ | destruct VBUF as (bs0 & U8 & LBS & _) ]). pose proof VINV as VINV0.
    (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
    unfold kHighMemBeg in Slo, Blo. all_app_facts. unfold vsb_cells in VSBC.
    assert (S8 : S mod 8 = 0) by (apply mod8_of_mod16; exact S16).
    assert (B8 : vb_buf vr mod 8 = 0) by (apply mod8_of_mod16; exact B16).
    pose proof (shpat_sh_boundL (Clg:=Clg) S 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHSB. rewrite SHMAX_val in SHSB.
    pose proof (shpat_sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(lia) ltac:(lia) ltac:(lia)) as SHBB. rewrite SHMAX_val in SHBB.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(lia) ltac:(lia) ltac:(lia)) as SHBN. rewrite SHMAX_val in SHBN.
    pose proof (cenv_intro A m md AINV) as CE.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC. open_map_cells MC.
    pose proof (rw_cells_bound _ _ _ _ VSBC) as SB. cbn [cells_size csize Nat.add length] in SB.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8336, bv_unsigned sp); (S, S + 40); (vb_buf vr, vb_buf vr + vb_size vr)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8336, bv_unsigned sp); (S, S + 40); (vb_buf vr, vb_buf vr + vb_size vr)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] |].
      split; [right; left; exists S, 40; split; [exact VLS|lia]|].
      split; [right; left; exists (vb_buf vr), (vb_size vr); split; [exact VLB|lia]| exact I]. }
    ago AINV. fold_cl_segs.
    carve_frame 64%nat ST.
    do 9 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    vsb_leaf_call assert_VSB_integrity_ok VSBC VINV0 SHS CE MU ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    vsb_leaf_call assert_VSB_state_ok VSBC VINV0 SHS CE MU ST.
    (* [comment removed for export] *)
    zstep. if_cases KU; zify_cond KU. { dead KU. } clear KU.
    zstep. zstep. if_cases KU; zify_cond KU. { exfalso. apply KU. apply land7_of_mod8; [lia| exact S8]. } clear KU.
    (* [comment removed for export] *)
    zstep. shadow_chk SHS 4 11.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      exfalso. rewrite Verr in KE. revert KE. vm_compute. first [ intros X; discriminate X | intros X; apply X; reflexivity | congruence ].
    - (* [comment removed for export] *)
      assert (E0 : vb_error vr = 0) by exact Verr.
      clear KE. zstep. zstep.
      vsb_leaf_call vsb_indent_ok VSBC VINV0 SHS CE MU ST.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHS 8.
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. unsign KU. klia KU. } clear KU.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHS 8. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. dead_b2z. } clear KU.
      (* [comment removed for export] *)
      zstep. if_cases KR; zify_cond KR; unsign KR.
      + (* [comment removed for export] *)
        zstep. zstep. zstep.
        astop AINV MU WM CFP. fold_cl_segs.
        lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
          pose proof (crange_stack (Clg:=Clg) (L:=LPA) A _ _ (aview A mx) (bv_unsigned sp - 64) 64 AINV0 ltac:(lia) ltac:(lia)
                        (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CF end.
        pose proof (as_minv LPA A _ _ AINV) as [_ MH]. pose proof (as_minv LPA A _ _ AINV0) as [_ MH0].
        pose proof (VSB_extend_ok) as HEXT. unfold VSB_extend_stmt in HEXT.
        eapply HEXT;
          [ exact AINV0 | assumption | reflexivity | reflexivity
          | split; [exact VSBC|]; split; [exact VINV0|]; split; [exact VLS|]; split; [exact VLB|]; split; [exact VNE|];
            exists bs0; split; [exact U8|]; split; [exact LBS| intros X; discriminate X]
          | lia | unfold EXT_MAX; lia | exact LBY | exact NLV | intros _; exact SCM | apply prim_room_ext; [lia| exact PCM] (* [comment removed for export] *) | exact TP
          | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
          | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; unfold EXT_STACK, ASTK; lia
          | ].
        clear HEXT VSBC U8 SHS SHB.
        intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' vr'. cbv zeta.
        intros AINV' MI' MDF VOBJ' LIVEq FRS TCR NLV' ST' OUT.
        fold_cl_segs. fold_aview. rewrite unsigned_lit in OUT, ST' by lia. unfold EXT_STACK, ASTK in OUT.
        (first [ pose proof ((vsb_obj_geom LPA A' m' md' S vr' false AINV' VOBJ')) as dR_4; dand11 dR_4 as _ _ _ _ B16' Blo' Bhi' Bimg' DSB' Smap' Bmap' | pose proof (vsb_obj_geom LPA A' m' md' S vr' false AINV' VOBJ') as (_ & _ & _ & _ & B16' & Blo' & Bhi' & Bimg' & DSB' & Smap' & Bmap') ]).
        pose proof (vsb_shadows LPA A' m' md' S vr' false AINV' VOBJ') as [SHS' SHB']. fold_cl_segs. fold_aview.
        unfold kHighMemBeg in Blo'. all_app_facts.
        pose proof VOBJ' as VOBJ1. vsb_open VOBJ'. (first [ dex1 VBUF as bs1; dand3 VBUF as U8n LBS1 _ | dand4 VBUF as bs1 U8n LBS1 _ | destruct VBUF as (bs1 & U8n & LBS1 & _) ]).
        pose proof VINV as VINV1. (first [ dand8 VINV as Vsz' Vlen' Verr' Vind' Vfl' Vb0' Vb47' Vbm' | destruct VINV as (Vsz' & Vlen' & Verr' & Vind' & Vfl' & Vb0' & Vb47' & Vbm') ]).
        unfold vsb_cells in VSBC.
        pose proof (shpat_sh_boundL (Clg:=Clg) (vb_buf vr') (vb_size vr') ltac:(lia) ltac:(lia) ltac:(lia)) as SHBB'. rewrite SHMAX_val in SHBB'.
        pose proof (as_minv LPA A' _ _ AINV') as [_ MH'].
        destruct OUT as (nb & Er & Ev & COPY & FRESH & REL & LBY' & SCR & PCR & FRK); subst r.   (* [comment removed for export] *)
        (* [comment removed for export] *)
        * (* [comment removed for export] *)
          subst vr'. cbn [vb_buf vb_size vb_len vb_error vb_flags vb_indent vsb_set_buf_size] in *.
          (first [ pose proof ((vsb_extendsize_spec (vb_size vr + 1) ltac:(lia))) as dR_7; dand3 dR_7 as NS1 NS2 NS3 | pose proof (vsb_extendsize_spec (vb_size vr + 1) ltac:(lia)) as (NS1 & NS2 & NS3) ]).
          pose proof (vsb_extendsize_tight (vb_size vr + 1)) as NS4.
          clear ST. acall_xfer FRK. rename ST' into ST.
          assert (NB8 : nb mod 8 = 0) by (apply mod8_of_mod16; exact B16').
          pose proof (munch_refl [(bv_unsigned sp - 8336, bv_unsigned sp); (S, S + 40); (nb, nb + vsb_extendsize (vb_size vr + 1))] (aview A' m')) as MU2.
          pose proof (wmono_refl rsegs (aview A' m')) as WM2.
          assert (WMAP2 : mapped (aview A' m') (bv_unsigned sp - 8336) 8336).
          { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
          assert (CFP2 : client_fp LPA A' (aview A' m') [(bv_unsigned sp - 8336, bv_unsigned sp); (S, S + 40); (nb, nb + vsb_extendsize (vb_size vr + 1))]).
          { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8336)) with 8336 by lia; exact WMAP2 |].
            split; [right; left; exists S, 40; split; [exact VLS0|lia]|].
            split; [right; left; eexists _, _; split; [exact VLB0| lia]| exact I]. }
          ago AINV'. fold_cl_segs. fix_ret_pc.
          zstep. if_cases KX; zify_cond KX. { dead KX. } clear KX.
          (* [comment removed for export] *)
          shadow_rechk SHS' (S + 4) 4 11.
          zstep. rewrite E0. zstep. if_cases KY; zify_cond KY. 2:{ exfalso. revert KY. vm_compute. congruence. } clear KY.
          (* [comment removed for export] *)
          putc_store_tail SHS' SHB' U8n E0 S vr a1.
          try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
          release_frame FR ST (bv_unsigned sp).
          astop AINV' MU2 WM2 CFP2.
          lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
            eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' mx mdx
                      (vsb_set_len (vsb_set_buf_size vr nb (vsb_extendsize (vb_size vr + 1))) (vb_len vr + 1))) end;
            [ assumption | assumption | | | cbn [vsb_set_len vsb_set_buf_size vb_len]; lia
            | cbn [vsb_set_len vsb_set_buf_size vb_size vb_len]; lia
            | right; cbn [vsb_set_len vsb_set_buf_size vb_size vb_len]; split; [lia| reflexivity] (* [comment removed for export] *)
            | exact LIVEq | right; cbn [vsb_set_len vsb_set_buf_size vb_buf]; split; [exact FRESH| exact REL] | exact FRS
            | cbn [vsb_set_len vsb_set_buf_size vb_size]; lia
            | exact TCR | exact NLV'
            | pose proof (vsb_pot_credit _ _ vr nb 1 ltac:(try (generalize alloc_ceiling_val); clear - VINV0; try pose proof alloc_ceiling_val as ACV__; unfold vsb_inv in VINV0; lia) ltac:(lia) SCR) as PC;
              unfold vsb_pot in *; cbn [vb_size vsb_set_len vsb_set_buf_size] in *; try (generalize alloc_ceiling_val); clear - PC; try pose proof alloc_ceiling_val as ACV__; lia
            | pose proof (vsb_ppot_credit _ _ vr nb 1 ltac:(clear - VINV0; unfold vsb_inv in VINV0; lia) ltac:(clear; lia) PCR) as PP;
              unfold vsb_ppot in *; cbn [vb_size vsb_set_len vsb_set_buf_size] in *; first [exact PP | clear - PP; lia] (* [comment removed for export] *)
            | exact ST | ].
          -- eapply amd_frame_sbm_l; [exact SBM | exact MH |]. eapply amd_frame_sbm_r; [exact MDF | eassumption].
          -- split; [exact VSBC|].
             split; [unfold vsb_inv; cbn [vsb_set_len vsb_set_buf_size vb_size vb_len vb_error vb_indent vb_flags vb_buf];
                    unfold vsb_inv in VINV1; cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf vsb_set_buf_size] in VINV1; lia|].
             split; [exact VLS0|]. split; [exact VLB0|]. split; [exact VNE0|].
             eexists; split; [exact U8'|]. split; [rewrite upd_length; cbn [vsb_set_len vsb_set_buf_size vb_size]; lia| intros X; discriminate X].
          -- cbn [vsb_set_len vsb_set_buf_size vb_buf vb_size].
             lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?vfin =>
             eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A m) _ (aview A' m') vfin _ _);
               [ exact MU | | exact FRK | lia | lia | intros a X; exact X
               | intros a X; left; exact X
               | exact MU2 | | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] ] end.
             ++ intros a Ha NO. cbn [outside] in NO. unfold newblk, blk. lia.
             ++ intros a Ha NO. cbn [outside] in NO. unfold newblk, blk. lia.
      + (* [comment removed for export] *)
        putc_store_tail SHS SHB U8 E0 S vr a1.
        try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
        release_frame FR ST (bv_unsigned sp).
        astop AINV MU WM CFP.
        pose proof (as_minv LPA A _ _ AINV) as [_ MH].
        lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
          eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A mx mdx (vsb_set_len vr (vb_len vr + 1))) end;
          [ assumption | assumption | eapply amd_frame_sbm; [exact SBM| exact MH] |
          | cbn [vsb_set_len vb_len]; lia | cbn [vsb_set_len vb_size vb_len]; lia
          | left; reflexivity (* [comment removed for export] *)
          | intros q _ _; reflexivity | left; reflexivity | intros ff; reflexivity
          | cbn [vsb_set_len vb_size]; lia | reflexivity | reflexivity | unfold vsb_pot; cbn [vb_size vsb_set_len]; lia
          | unfold vsb_ppot; cbn [vb_size vsb_set_len]; lia (* [comment removed for export] *) | exact ST | ].
        * split; [exact VSBC|]. split; [unfold vsb_inv; cbn [vsb_set_len vb_size vb_len vb_error vb_indent vb_flags vb_buf]; lia|].
          split; [exact VLS|]. split; [exact VLB|]. split; [exact VNE|].
          eexists. split; [exact U8'|]. split; [rewrite upd_length; cbn [vsb_set_len vb_size vb_len]; lia| intros X; discriminate X].
        * cbn [vsb_set_len vb_buf vb_size].
          eapply (cframe_noalloc LPA); [exact MU | | | intros a X; left; exact X].
          -- intros a Ha NO. cbn [outside] in NO. unfold newblk, blk. lia.
          -- eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia].
  Qed.
End S.

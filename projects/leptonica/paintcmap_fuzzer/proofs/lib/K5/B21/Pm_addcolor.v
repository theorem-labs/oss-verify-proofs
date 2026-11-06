(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Pm_iface Pm_iface2 Pm_ckit LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section ADDCOLOR.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorInt.

Theorem pixcmapAddColor_ok : pixcmapAddColor_cps RT.
Proof using AF GP RERR.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo cmap cv
    FDO MST -> -> COBJ ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixcmapAddColor, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  pose proof RERR as RE. unfold returnError_cps in RE.
  pose proof COBJ as ((pad & CMC) & (INC & CM0 & CM16 & _) & (INA & AR0 & AR16 & ARN) & (HD & ENA & NB) & NEQ).
  destruct cv as [arr depth nalloc n]. cbn [c_arr c_depth c_nalloc c_n] in *. unfold cmap_cells in CMC. cbn [c_arr c_depth c_nalloc c_n] in CMC.
  assert (NA : 2 <= nalloc <= 256) by (rewrite ENA; destruct HD as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia).
  assert (DR : 1 <= depth <= 8) by (destruct HD as [<-|[<-|[<-|[<-|[]]]]]; lia).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(cmap + 16, cmap + 20); (arr, arr + 4 * nalloc)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP cmap 24.
  chunk_facts RT AF GP arr (4 * nalloc).
  assert (DCA : cmap + 24 <= arr \/ arr + 4 * nalloc <= cmap) by (apply (live_apart RT AF Σ m cmap 24 arr (4 * nalloc) ART0 INC INA); congruence).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  destruct (Z_lt_ge_dec n nalloc) as [NLT|NGE].
  - (* [comment removed for export] *)
    assert (EA1 : a1 = Z_to_bv 64 (bv_unsigned a1)) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (EA2 : a2 = Z_to_bv 64 (bv_unsigned a2)) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (EA3 : a3 = Z_to_bv 64 (bv_unsigned a3)) by (symmetry; apply Z_to_bv_bv_unsigned).
    set (cr := bv_unsigned a1) in *. set (cg := bv_unsigned a2) in *. set (cb := bv_unsigned a3) in *.
    rewrite EA1, EA2, EA3. clear EA1 EA2 EA3. clearbody cr cg cb.
    pose proof (proj1 (af_acc_live RT AF Σ m arr (4 * nalloc) ART0 INA)) as WRA.
    pose proof (wr_at_sub m arr (4 * nalloc) (arr + n * 4) 4 WRA ltac:(lia) ltac:(lia) ltac:(lia)) as WRQ.
    apply wr_at_rw_CB in WRQ; [| lia]. destruct WRQ as (qj & QC). change (Z.to_nat 4) with 4%nat in QC. clear WRA.
    (* [comment removed for export] *)
    assert (Q1 : arr + n * 4 + 4 <= cmap \/ cmap + 24 <= arr + n * 4) by (destruct DCA; [right|left]; lia).
    assert (Q2 : arr + n * 4 + 4 <= 65536 \/ 6475776 <= arr + n * 4)
      by (lazymatch goal with D : arr + 4 * nalloc <= 65536 \/ _ |- _ => destruct D; [left|right]; lia end).
    assert (Q3 : arr + n * 4 + 4 <= 2147446784 \/ 17594333495296 <= arr + n * 4)
      by (lazymatch goal with D : arr + 4 * nalloc <= 2147446784 \/ _ |- _ => destruct D; [left|right]; lia end).
    park_disj.
    Time walk_to AF MST [(usp - 16, usp); (cmap + 16, cmap + 20); (arr, arr + 4 * nalloc)] [0x8d908].
    rewrite ?(sx32_small n) by lia. rewrite ?(sx32_small nalloc) by lia.
    try br.
    Time awalk [0x91ba8; 0x8d908].
    set (q := arr + n * 4) in *.
    assert (QLO : arr <= q) by (unfold q; lia). assert (QHI : q + 4 <= arr + 4 * nalloc) by (unfold q; lia).
    clearbody q.
    Time awalk [0x8d908].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists cmap, 24; split; [solve [in_live_tac]| lia]|
                          split; [intros zz Hzz; right; right; left; exists arr, (4 * nalloc); split; [solve [in_live_tac]| lia]| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| exact HxO]) end.
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    exists Σ, 0. split; [| repeat split; try reflexivity; lia].
    eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
    split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
    left. split; [reflexivity| split; [lia|]].
    unfold cmapv_n, cmap_obj, cmap_cells, chunk, cmap_ok; cbn [c_arr c_depth c_nalloc c_n].
    split; [exists pad; exact CMC|].
    split; [split; [exact INC| split; [lia| split; [assumption| lia]]]|].
    split; [split; [exact INA| split; [lia| split; [assumption| lia]]]|].
    split; [split; [exact HD| split; [exact ENA| lia]]| exact NEQ].
  - (* [comment removed for export] *)
    park_disj.
    Time walk_to AF MST [(usp - 16, usp)] [0x8d908].
    rewrite ?(sx32_small n) by lia. rewrite ?(sx32_small nalloc) by lia.
    try br.
    Time awalk [0x8d908].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    (eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |]).
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, 1 end.
    split; [| alg_tac].
    eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
    split; [intros a Ha Ho; apply AGF; split; [| exact Ho]; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in Ha end; exact Ha|].
    right. split; [reflexivity| split; [cbn [c_n c_nalloc]; lia|]].
    unfold cmap_obj, cmap_cells, chunk, cmap_ok; cbn [c_arr c_depth c_nalloc c_n].
    split; [exists pad; exact CMC|].
    split; [split; [solve [in_live_tac]| split; [lia| split; [assumption| lia]]]|].
    split; [split; [solve [in_live_tac]| split; [lia| split; [assumption| lia]]]|].
    split; [split; [exact HD| split; [exact ENA| lia]]| exact NEQ].
Qed.
End ADDCOLOR.

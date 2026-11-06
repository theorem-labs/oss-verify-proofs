(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Pm_iface Pm_iface2 Pm_ckit.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Ltac from_disj D := let X := fresh "X" in pose proof D as X; unfold parked in X; destruct X as [X|X]; [left|right]; lia.

Lemma tr_cmapcopy2 : In [0x916fc] CLIENT_TRACES.  Proof. vm_compute. tauto. Qed.

Section CMAPCOPY.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis VALS : pixcmapIsValid_stk_cps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.

Theorem pixcmapCopy_ok : pixcmapCopy_cps RT.
Proof using AF RC GP VALS RERR.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo cmaps cv ras
    FDO MST -> -> COBJ UCTX EMP TRC ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixcmapCopy, PMCOPY_CALLOC1, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  unfold uctx in UCTX.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  pose proof RERR as RE. unfold returnError_cps in RE. pose proof VALS as VS. unfold pixcmapIsValid_stk_cps in VS.
  pose proof COBJ as ((pad & CMC) & (INC & CM0 & CM16 & _) & (INA & AR0 & AR16 & ARN) & (HD & ENA & NB) & NEQ).
  destruct cv as [arr depth nalloc n]. cbn [c_arr c_depth c_nalloc c_n] in *. unfold cmap_cells in CMC. cbn [c_arr c_depth c_nalloc c_n] in CMC.
  assert (NA : 2 <= nalloc <= 256) by (rewrite ENA; destruct HD as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia).
  assert (DR : 1 <= depth <= 8) by (destruct HD as [<-|[<-|[<-|[<-|[]]]]]; lia).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP cmaps 24.
  chunk_facts RT AF GP arr (4 * nalloc).
  park_disj.
  Time walk_to AF MST [(usp - 64, usp)] [0x91944; 0x5ed80; 0x5d568; 0x8dad0].
  split_at FR 1%nat FRhi.
  split_last_CB FR [4%nat; 4%nat].
  split_at FR 1%nat FRv.
  destruct (cb4_c4' _ _ _ FRv) as (xv & PVC). clear FRv.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { eapply VS with (lo := lo) (cmap := cmaps) (pv := usp + -60) (cv := mkCmapv arr depth nalloc n) (x := xv); rt_side idtac.
    all: lazymatch goal with
         | |- cmap_obj _ _ _ _ =>
             unfold cmap_obj, cmap_cells, chunk, cmap_ok; cbn [c_arr c_depth c_nalloc c_n];
             split; [exists pad; exact CMC|]; repeat split; first [assumption | lia]
         | |- rw_cells _ _ _ [C4 _] => exact PVC
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- _ mod 4 = 0 => clear - SPA; Z.div_mod_to_equations; lia
         | |- _ <= _ => rewrite ?unsigned_lit by lia; unfold USTACK_TOP; lia
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]|
                                 cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]]).
  lazymatch goal with
  | FRlo : rw_cells asegs ?mm (usp + -64) [CB 4 ?j], PV : rw_cells asegs ?mm (usp + -60) [C4 ?y], FH : rw_cells asegs ?mm (usp + -56) ?cs |- _ =>
      let J := fresh "FRJ" in
      assert (J : rw_cells asegs mm (usp + -64) ([CB 4 j] ++ ([C4 y] ++ cs)));
      [ apply rw_cells_app; split; [exact FRlo|]; cbn [cells_size csize Nat.add];
        apply rw_cells_app; split; [replace (usp + -64 + Z.of_nat 4) with (usp + -60) by lia; exact PV|];
        cbn [cells_size csize Nat.add]; replace (usp + -64 + Z.of_nat 4 + Z.of_nat 4) with (usp + -56) by lia; exact FH
      | cbn [app] in J; clear FRlo PV FH; rename J into FR ]
  end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  Time walk_to AF MST [(usp - 64, usp)] [0x91944; 0x5ed80; 0x5d568; 0x8dad0].
  brfork HBV.
  1:{ (* [comment removed for export] *)
      Time awalk [0x91944; 0x5ed80; 0x5d568; 0x8dad0].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
      (eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |]).
      after_call RT AF.
      fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
      refresh RT AF. park_disj.
      Time walk_to AF MST [(usp - 64, usp)] (@nil Z).
      cps_stop.
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, 0, (mkCmapv 0 0 0 0) end.
      split; [| change (0 =? 0) with true; cbv iota; alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { lazymatch goal with WMx : wmono asegs ?m0 ?mf |- wmono asegs ?m0 ?mf => exact WMx end. }
      split; [intros a Ha _; apply AGF; exact Ha| intros NZ; contradiction NZ; reflexivity]. }
  (* [comment removed for export] *)
  Time awalk [0x91944; 0x5ed80; 0x5d568; 0x8dad0].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm))) _ =>
    assert (UW : unwind_okC mm (Z_to_bv 64 0x916d4) s0 (Z_to_bv 64 (usp + -64)))
      by (assert (USPx : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range);
          exists ras; split; [| rewrite unsigned_lit by (clear; lia); exact TRC];
          rewrite unsigned_lit by (clear - USPx LOR STa; lia);
          destruct ras as [|ra1 ras'];
          [ cbn [chain_ok] in *; unfold link_invalid in *; specialize (EMP eq_refl); clear - EMP UCTX LOR; lia
          | cbn [chain_ok] in UCTX |- *; destruct UCTX as (U1 & U2 & U3 & U4 & fp1 & U5 & U6 & U7); unfold USTACK_TOP in *;
            split; [clear - U1; lia|]; split; [exact U2|]; split; [exact U3|]; split; [exact U4|]; exists fp1; split; [exact U5|]; split;
            [ apply (rw_cells_agree_nw asegs m _ _ _ U6); eapply agree_sub; [exact AGF|]; cbv beta; intros xx Hxx;
              cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hxx; change (Z.of_nat 16) with 16 in Hxx; left; unfold USTACK_TOP; clear - Hxx U1 U3; lia
            | eapply chain_ok_keep; [exact U7|]; eapply agree_sub; [exact AGF|]; cbv beta; intros xx Hxx; left; clear - Hxx U1; lia ] ]) end.
  eapply cps_seq; [eapply (gp_calloc RT GP) with (lo := lo) (nmemb := 1) (size := 24); rt_side idtac;
    lazymatch goal with
       | |- unwind_okC _ _ _ _ => exact UW
       | |- (_ <= CALLOC_MAX) => unfold CALLOC_MAX; lia
       | |- (Z.of_nat (length (rt_live _ _)) < LIVE_MAX) => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length]; unfold LIVE_MAX in *; lia
       | |- ?g => idtac "LEFTOVER:" g
       end |].
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  lazymatch goal with H : rw_cells asegs ?mm ?p [CB (Z.to_nat (1 * 24)) ?bs] |- _ =>
    pose proof (rw_cells_recell mm p [CB (Z.to_nat (1 * 24)) bs]
                  [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)] H
                  ltac:(cbn; tauto) eq_refl eq_refl) as CMD; clear H end.
  change (1 * 24) with 24 in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 24) :: _ |- _ => set (cmapd := p) in *; rename H into LVC end.
  chunk_facts RT AF GP cmapd 24.
  assert (CMAPD_AP : forall a, PF a -> a < cmapd \/ cmapd + 24 <= a).
  { intros a Ha.
    lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (cmapd, 24) :: _, FRS : rt_frames RT ?S = _, SP0 : rt_sp0 RT ?S = _ |- _ =>
      apply (new_chunk_apart RT AF S mm cmapd 24 _ _ usp a A L FRS ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul)) end.
    apply (aclient_mono _ _ usp _ _ _ _ Ha); [solve [live_add_tac]| solve [frames_sub_tac]| lia]. }
  assert (DCC : cmapd + 24 <= cmaps \/ cmaps + 24 <= cmapd).
  { lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (cmapd, 24) :: _ |- _ =>
      apply (af_live_disj RT AF S mm cmapd 24 cmaps 24 [] _ A L); cbn [app]; solve [in_live_tac] end. }
  assert (DCA : cmapd + 24 <= arr \/ arr + 4 * nalloc <= cmapd).
  { lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (cmapd, 24) :: _ |- _ =>
      apply (af_live_disj RT AF S mm cmapd 24 arr (4 * nalloc) [] _ A L); cbn [app]; solve [in_live_tac] end. }
  park_disj.
  Time walk_to AF MST [(usp - 64, usp); (cmapd, cmapd + 24)] [0x91944; 0x5ed80; 0x5d568; 0x8dad0].
  rewrite (sx32_small nalloc) by lia. rewrite (unsigned_lit nalloc) by lia.
  rewrite (swrap32_small (nalloc * 4)) by lia.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists cmapd, 24; split; [solve [in_live_tac]| lia]| exact I]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (CMAPD_AP _ Hx); split; [lia| split; [lia| exact I]]).
  eapply cps_seq; [eapply (gp_calloc RT GP) with (lo := lo) (nmemb := 1) (size := 4 * nalloc); rt_side idtac;
    lazymatch goal with
       | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_cmapcopy2| left; ul]
       | |- (_ <= CALLOC_MAX) => unfold CALLOC_MAX; lia
       | |- (Z.of_nat (length (rt_live _ _)) < LIVE_MAX) => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length]; unfold LIVE_MAX in *; lia
       | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; lia
       | |- 0 < _ => lia
       | |- ?g => idtac "LEFTOVER:" g
       end |].
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  replace (1 * (4 * nalloc)) with (4 * nalloc) in * by lia.
  lazymatch goal with H : rt_live RT ?S = (?p, 4 * nalloc) :: _ |- _ => set (arrd := p) in *; rename H into LVA end.
  chunk_facts RT AF GP arrd (4 * nalloc).
  assert (ARRD_AP : forall a, PF a -> a < arrd \/ arrd + 4 * nalloc <= a).
  { intros a Ha. lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (arrd, 4 * nalloc) :: _, FRS : rt_frames RT ?S = _, SP0 : rt_sp0 RT ?S = _ |- _ =>
      apply (new_chunk_apart RT AF S mm arrd (4 * nalloc) _ _ usp a A L FRS ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul)) end.
    apply (aclient_mono _ _ usp _ _ _ _ Ha); [solve [live_add_tac]| solve [frames_sub_tac]| lia]. }
  assert (DAC : arrd + 4 * nalloc <= cmapd \/ cmapd + 24 <= arrd)
    by (lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (arrd, 4 * nalloc) :: _ |- _ =>
          apply (af_live_disj RT AF S mm arrd (4 * nalloc) cmapd 24 [] _ A L); cbn [app]; solve [in_live_tac] end).
  assert (DAS : arrd + 4 * nalloc <= cmaps \/ cmaps + 24 <= arrd)
    by (lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (arrd, 4 * nalloc) :: _ |- _ =>
          apply (af_live_disj RT AF S mm arrd (4 * nalloc) cmaps 24 [] _ A L); cbn [app]; solve [in_live_tac] end).
  assert (DAA : arrd + 4 * nalloc <= arr \/ arr + 4 * nalloc <= arrd)
    by (lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (arrd, 4 * nalloc) :: _ |- _ =>
          apply (af_live_disj RT AF S mm arrd (4 * nalloc) arr (4 * nalloc) [] _ A L); cbn [app]; solve [in_live_tac] end).
  unpark_all. park_disj.
  Time walk_to AF MST [(usp - 64, usp); (cmapd, cmapd + 24)] [0x91944; 0x5ed80; 0x5d568; 0x8dad0].
  rewrite (sx32_small n) by lia. rewrite (unsigned_lit n) by lia.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists cmapd, 24; split; [solve [in_live_tac]| lia]| exact I]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (CMAPD_AP _ Hx); split; [lia| split; [lia| exact I]]).
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
    pose proof (proj1 (af_acc_live RT AF S mm arr (4 * nalloc) A ltac:(solve [in_live_tac]))) as WRA;
    pose proof (wr_at_sub mm arr (4 * nalloc) arr (n * 4) WRA ltac:(lia) ltac:(lia) ltac:(lia)) as WRS;
    assert (INAD : In (arrd, 4 * nalloc) (rt_live RT S)) by (solve [in_live_tac]);
    assert (INAS : In (arr, 4 * nalloc) (rt_live RT S)) by (solve [in_live_tac]);
    pose proof (af_acc_live RT AF S mm arrd (4 * nalloc) A INAD) as (WRD & ACCD) end.
  apply wr_at_rw_CB in WRS; [| lia]. destruct WRS as (sbs & SBC).
  pose proof SBC as [[[SBL _] _] _]. cbn in SBL. apply u8arr_of_rw_cells in SBC. destruct SBC as [SB _].
  assert (SBL' : Z.of_nat (length sbs) = n * 4) by (rewrite SBL; lia).
  eapply cps_seq;
  [ pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0;
    eapply MC0 with (lo := lo) (d := arrd) (s := arr) (bs := sbs); rewrite ?SBL';
    lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
         | |- bytes_at _ _ _ _ => exact SB
         | |- ART _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- checked_src _ _ _ _ _ _ _ =>
             unfold checked_src; rewrite ?unsigned_lit by lia;
             split; [intros _; split; [apply (acc_sub asegs _ arr (4 * nalloc)); [assumption| lia| lia]|
                                       left; exists arr, (4 * nalloc); split; [exact INAS| lia]]| left; lia]
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by lia;
             split; [intros _; split; [apply (acc_sub asegs _ arrd (4 * nalloc)); [exact ACCD| lia| lia]| left; exists arrd, (4 * nalloc); split; [exact INAD| lia]]|];
             split; [intros i Hi; right; right; left; exists arrd, (4 * nalloc); split; [exact INAD| lia]|
                     apply (wr_at_sub _ arrd (4 * nalloc)); [exact WRD| lia| lia| lia]]
         | |- call_ok _ _ _ _ _ =>
             unfold call_ok; rewrite ?unsigned_lit by lia; split; [assumption|];
             repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN, RT_STACK, USTACK_TOP;
             split; [lia| split; [lia| split; [lia| clear - SPA; Z.div_mod_to_equations; lia]]]   (* [comment removed for export] *)
         | |- _ \/ _ => from_disj DAA
         | |- (_ <= _ <= _) => lia
         | |- (_ < _) => lia
         | |- ?g => idtac "LEFTOVER:" g
         end |].
  rewrite ?SBL'. clear SB.
  (* [comment removed for export] *)
  assert (SEGn : arrd + n * 4 <= 65536 \/ 6471680 <= arrd) by (lazymatch goal with D : parked (arrd + 4 * nalloc <= 65536 \/ _) |- _ => from_disj D end).
  assert (DASn : arrd + n * 4 <= cmaps \/ cmaps + 24 <= arrd) by (from_disj DAS).
  assert (DACn : arrd + n * 4 <= cmapd \/ cmapd + 24 <= arrd) by (from_disj DAC).
  repeat match goal with H : rw_cells asegs _ arrd _ |- _ => clear H end.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]| pose proof (ARRD_AP _ Hx); lia]).
  refresh RT AF. park_disj.
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 64, usp); (cmapd, cmapd + 24)] (@nil Z).
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists cmapd, 24; split; [solve [in_live_tac]| lia]| exact I]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (CMAPD_AP _ Hx); split; [lia| split; [lia| exact I]]) end.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, cmapd, (mkCmapv arrd depth nalloc n) end.
  assert (CNZ : cmapd <> 0) by lia.
  split; [| replace (cmapd =? 0) with false by (symmetry; apply Z.eqb_neq; exact CNZ); cbn [c_arr c_nalloc]; alg_tac].
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
  { lazymatch goal with WMx : wmono asegs ?m0 ?mf |- wmono asegs ?m0 ?mf => exact WMx end. }
  split; [intros a Ha _; apply AGF; exact Ha| intros _].
  cbn [c_arr c_depth c_nalloc c_n]. split; [| repeat split; reflexivity].
  unfold cmap_obj, cmap_cells, chunk, cmap_ok; cbn [c_arr c_depth c_nalloc c_n].
  rewrite (sx32_small depth), (sx32_small nalloc), (sx32_small n) in CMD by lia.
  split; [exists (repeat (Z_to_bv 8 0) 4); exact CMD|].
  split; [split; [solve [in_live_tac]| split; [lia| split; [assumption| lia]]]|].
  split; [split; [solve [in_live_tac]| split; [lia| split; [assumption| lia]]]|].
  split; [split; [exact HD| split; [exact ENA| lia]]|].
  unfold parked in DAC; lia.
Qed.
End CMAPCOPY.

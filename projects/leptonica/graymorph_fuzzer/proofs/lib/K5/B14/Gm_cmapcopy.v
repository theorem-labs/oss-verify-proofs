(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Gm_iface Gm_kit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition CC_STOPS : list Z := [0x99404; 0x61c00; 0x603e8; 0x9097c].

Lemma tr_cmapcopy2 : In [RA_CMAPCOPY_CALLOC2] CLIENT_TRACES.
Proof. apply ct_mem_In. vm_compute. reflexivity. Qed.

Section CC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis IVN : pixcmapIsValid_null_cps RT.

Theorem pixcmapCopy_ok : pixcmapCopy_cps RT.
Proof using AF RC GP IVN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo cmaps cvs ra1 ras
    FDO MST -> -> CO UCTX TRM ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP). unfold uctx in UCTX.
  pose proof CO as CO0.
  destruct CO as ((pad & CMC) & (INC & CM0 & CM16 & _) & (INA & AR0 & AR16 & ARN) & (HD & ENA & NB) & NEQ).
  destruct cvs as [arr depth nalloc n]. cbn [c_arr c_depth c_nalloc c_n] in *. unfold cmap_cells in CMC. cbn [c_arr c_depth c_nalloc c_n] in CMC.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixcmapCopy, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, CC_STOPS in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  pose proof IVN as IV. unfold pixcmapIsValid_null_cps in IV.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP cmaps 24.
  chunk_facts RT AF GP arr (4 * nalloc).
  assert (NA : 2 <= nalloc <= 256) by (rewrite ENA; destruct HD as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia).
  assert (DR : 1 <= depth <= 8) by (destruct HD as [<-|[<-|[<-|[<-|[]]]]]; lia).
  (* [comment removed for export] *)
  pose proof NA as NAh. hide NAh. pose proof NB as NBh. hide NBh. pose proof DR as DRh. hide DRh.
  carve_frame 64%nat ST.
  Time walk_to AF MST [(usp - 64, usp)] [0x99404; 0x61c00; 0x603e8; 0x9097c].
  (* [comment removed for export] *)
  split_at FR 1%nat FRrest.
  split_last_CB FR [4%nat; 4%nat].
  split_at FR 1%nat PVC.
  destruct (cb4_c4' _ _ _ PVC) as (xv & PVC'). clear PVC.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { eapply IV with (lo := lo) (cmap := cmaps) (pv := usp + -60) (cv := mkCmapv arr depth nalloc n) (x := xv); rt_side idtac.
    all: lazymatch goal with
         | |- cmap_obj _ ?mm _ _ =>
             apply (cmap_obj_keep (rt_live RT Σ) m mm _ _); [| exact CO0];
             intros bq kq Hin aq Haq; apply AGF; right; right; left; exists bq, kq; split; [exact Hin| exact Haq]
         | |- optrV _ _ _ _ _ => right; rewrite ?unsigned_lit by lia; unfold USTACK_TOP; repeat split; first [lia | clear - SPA; Z.div_mod_to_equations; lia]
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- ?g => idtac "LEFT:" g
         end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]|
                                 cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  Time walk_to AF MST [(usp - 64, usp)] [0x99404; 0x61c00; 0x603e8; 0x9097c].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 1) (size := 24); rt_side idtac.
    all: lazymatch goal with
         | |- (_ <= CALLOC_MAX) => unfold CALLOC_MAX; lia
         | |- (Z.of_nat _ < LIVE_MAX) =>
             repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length]; unfold LIVE_MAX in *; lia
         | |- unwind_okC _ _ _ _ =>
             exists (ra1 :: ras); rewrite ?unsigned_lit by ul; split; [| exact TRM];
             apply (chain_ok_lower _ usp (usp + -64) _ ra1 ras); [| lia];
             apply (chain_ok_keep (ra1 :: ras) m _ usp (bv_unsigned s0) UCTX);
             eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
         | |- ?g => idtac "LEFT:" g
         end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  lazymatch goal with H : rw_cells asegs ?mm ?p [CB (Z.to_nat (1 * 24)) ?bs] |- _ =>
    pose proof (rw_cells_recell mm p [CB (Z.to_nat (1 * 24)) bs]
                  [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)] H
                  ltac:(cbn; tauto) eq_refl eq_refl) as CMD; clear H end.
  change (1 * 24) with 24 in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 24) :: _ |- _ => rename H into LVC; set (cmd := p) in * end.
  chunk_facts RT AF GP cmd 24.
  assert (CMD_AP : forall a, PF a -> a < cmd \/ cmd + 24 <= a).
  { intros a Ha. lazymatch goal with A : ART RT ?S ?mm, FRS : rt_frames RT ?S = _, SP0 : rt_sp0 RT ?S = _ |- _ =>
      apply (new_chunk_apart RT AF S mm cmd 24 _ _ usp a A LVC FRS ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul)) end.
    apply (aclient_mono _ _ usp _ _ _ _ Ha); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]. }
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
    assert (DC1 : cmd + 24 <= cmaps \/ cmaps + 24 <= cmd)
      by (apply (af_live_disj RT AF S mm cmd 24 cmaps 24 [] _ A LVC); cbn [app]; solve [in_live_tac]);
    assert (DC2 : cmd + 24 <= arr \/ arr + 4 * nalloc <= cmd)
      by (apply (af_live_disj RT AF S mm cmd 24 arr (4 * nalloc) [] _ A LVC); cbn [app]; solve [in_live_tac]) end.
  lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  Time walk_to AF MST [(usp - 64, usp)] [0x99404; 0x61c00; 0x603e8; 0x9097c].
  cwalk [0x99404; 0x61c00; 0x603e8; 0x9097c].
  (* [comment removed for export] *)
  rewrite (sx32_small nalloc) by lia. rewrite (unsigned_lit nalloc) by lia.
  rewrite (bv_swrap_small 32 (nalloc * 4)) by (change (bv_half_modulus 32) with (2^31); lia).
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 1) (size := nalloc * 4); rt_side idtac.
    all: lazymatch goal with
         | |- (_ <= CALLOC_MAX) => unfold CALLOC_MAX; lia
         | |- (Z.of_nat _ < LIVE_MAX) =>
             repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length]; unfold LIVE_MAX in *; lia
         | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite ?unsigned_lit by ul; [exact tr_cmapcopy2| left; ul]
         | |- ?g => idtac "LEFT:" g
         end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  replace (1 * (nalloc * 4)) with (4 * nalloc) in * by lia.
  lazymatch goal with H : rt_live RT ?S = (?p, 4 * nalloc) :: _ |- _ => rename H into LVA; set (ard := p) in * end.
  chunk_facts RT AF GP ard (4 * nalloc).
  assert (ARD_AP : forall a, PF a -> a < ard \/ ard + 4 * nalloc <= a).
  { intros a Ha. lazymatch goal with A : ART RT ?S ?mm, FRS : rt_frames RT ?S = _ |- _ =>
      apply (new_chunk_apart RT AF S mm ard (4 * nalloc) _ _ usp a A LVA FRS ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul)) end.
    apply (aclient_mono _ _ usp _ _ _ _ Ha); [solve [live_add_tac]| solve [frames_sub_tac]| lia]. }
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
    assert (DA1 : ard + 4 * nalloc <= cmd \/ cmd + 24 <= ard)
      by (apply (af_live_disj RT AF S mm ard (4 * nalloc) cmd 24 [] _ A LVA); cbn [app]; solve [in_live_tac]);
    assert (DA2 : ard + 4 * nalloc <= cmaps \/ cmaps + 24 <= ard)
      by (apply (af_live_disj RT AF S mm ard (4 * nalloc) cmaps 24 [] _ A LVA); cbn [app]; solve [in_live_tac]);
    assert (DA3 : ard + 4 * nalloc <= arr \/ arr + 4 * nalloc <= ard)
      by (apply (af_live_disj RT AF S mm ard (4 * nalloc) arr (4 * nalloc) [] _ A LVA); cbn [app]; solve [in_live_tac]) end.
  lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  Time walk_to AF MST [(usp - 64, usp); (cmd, cmd + 24)] [0x99404; 0x61c00; 0x603e8; 0x9097c].
  cwalk [0x99404; 0x61c00; 0x603e8; 0x9097c].
  (* [comment removed for export] *)
  rewrite (sx32_small n) by lia. rewrite (unsigned_lit n) by lia.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists cmd, 24; split; [solve [in_live_tac]| lia]| exact I]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (CMD_AP _ Hx); split; [lia| split; [lia| exact I]]).
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm))) _ =>
    pose proof (af_acc_live RT AF S mm arr (4 * nalloc) A ltac:(solve [in_live_tac])) as (WRA & ACCA);
    pose proof (af_acc_live RT AF S mm ard (4 * nalloc) A ltac:(solve [in_live_tac])) as (WRD & ACCD);
    pose proof (wr_at_sub mm arr (4 * nalloc) arr (4 * n) WRA ltac:(lia) ltac:(lia) ltac:(lia)) as WRS;
    pose proof (wr_at_sub mm ard (4 * nalloc) ard (4 * n) WRD ltac:(lia) ltac:(lia) ltac:(lia)) as WRDS end.
  apply wr_at_rw_CB in WRS; [| lia]. destruct WRS as (sbs & SBC).
  pose proof SBC as [[[SBL _] _] _]. cbn in SBL. apply u8arr_of_rw_cells in SBC. destruct SBC as [SB _].
  assert (SBL' : Z.of_nat (length sbs) = 4 * n) by (rewrite SBL; lia).
  (* [comment removed for export] *)
  assert (Q3 : ard + 4 * n <= arr \/ arr + 4 * n <= ard) by (unfold parked in DA3; lia).
  assert (Q4 : arr + 4 * n <= lo).
  { lazymatch goal with A : ART RT ?S ?mm |- _ =>
      pose proof (af_live_range RT AF S mm arr (4 * nalloc) A ltac:(solve [in_live_tac])) as (_ & R & _) end.
    repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in R end. unfold STACK_WIN in R. lia. }
  assert (Q5 : ard + 4 * n <= cmd \/ cmd + 24 <= ard) by (unfold parked in DA1; lia).
  assert (Q6 : ard + 4 * n <= cmaps \/ cmaps + 24 <= ard) by (unfold parked in DA2; lia).
  assert (Q7 : 0 <= ard <= 2^47 /\ 0 <= arr <= 2^47 /\ (ard + 4 * n <= 65536 \/ 6598656 <= ard)).
  { lazymatch goal with A : ART RT ?S ?mm |- _ =>
      pose proof (af_live_range RT AF S mm arr (4 * nalloc) A ltac:(solve [in_live_tac])) as (R1 & R2 & _);
      pose proof (af_live_range RT AF S mm ard (4 * nalloc) A ltac:(solve [in_live_tac])) as (R3 & R4 & R5) end.
    repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in R2, R4 end. unfold STACK_WIN, SEGTOP_A in *. lia. }
  destruct Q7 as (Q7a & Q7b & Q8).
  eapply cps_seq.
  { pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0;
    eapply MC0 with (lo := lo) (d := ard) (s := arr) (bs := sbs); rewrite ?SBL'.
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia]
         | |- bytes_at _ _ _ _ => exact SB
         | |- ART _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- checked_src _ _ _ _ _ _ _ =>
             unfold checked_src; rewrite ?unsigned_lit by lia;
             split; [intros _; split; [apply (acc_sub asegs _ arr (4 * nalloc)); [exact ACCA| lia| lia]|
                                       left; exists arr, (4 * nalloc); split; [solve [in_live_tac]| lia]]| left; exact Q4]
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by lia;
             split; [intros _; split; [apply (acc_sub asegs _ ard (4 * nalloc)); [exact ACCD| lia| lia]|
                                       left; exists ard, (4 * nalloc); split; [solve [in_live_tac]| lia]]|];
             split; [intros i Hi; right; right; left; exists ard, (4 * nalloc); split; [solve [in_live_tac]| lia]| exact WRDS]
         | |- call_ok _ _ _ _ _ => call_ok_tac
         | |- _ \/ _ => exact Q3
         | |- (_ <= _ <= _) => first [exact Q7a | exact Q7b]
         | |- (_ < _) => lia
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  rewrite SBL'. clear SB.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]| pose proof (ARD_AP _ Hx); lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  Time walk_to AF MST [(usp - 64, usp); (cmd, cmd + 24)] (@nil Z).
  cwalk (@nil Z).
  (* [comment removed for export] *)
  lazymatch goal with ST' : stk asegs _ lo (usp + -64) |- _ => release_frame FR ST' (usp + -60) end.
  lazymatch goal with ST' : stk asegs _ lo (usp + -60), CV : rw_cells asegs _ (usp + -60) _ |- _ => release_frame CV ST' (usp + -56) end.
  lazymatch goal with ST' : stk asegs _ lo (usp + -56) |- _ => release_frame FRrest ST' usp end.
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists cmd, 24; split; [solve [in_live_tac]| lia]| exact I]]).
  lazymatch goal with MUx : munch _ ?mm ?mc' |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc' _))) _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (CMD_AP _ Hx); split; [lia| split; [lia| exact I]]) end.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, cmd, (mkCmapv ard depth nalloc n) end.
  split.
  2:{ cbn [c_arr c_nalloc]. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end.
      repeat split; auto; lia. }
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
  { lazymatch goal with WMx : wmono asegs ?m0 ?mf |- wmono asegs ?m0 ?mf => exact WMx end. }
  split; [intros a Ha _; apply AGF; exact Ha|].
  cbn [c_arr c_depth c_nalloc c_n]. split; [| repeat split; reflexivity].
  unfold cmap_obj, cmap_cells, chunk, cmap_ok. cbn [c_arr c_depth c_nalloc c_n].
  unfold hid in NAh, NBh, DRh.
  assert (NE : ard <> cmd) by (unfold parked in DA1; clear - DA1 NAh; lia).
  split; [eexists; lazymatch goal with H : rw_cells asegs ?mm cmd _ |- rw_cells asegs ?mm cmd _ =>
            rewrite (sx32_small depth), (sx32_small nalloc), (sx32_small n) in H by (clear - NAh NBh DRh; lia); exact H end|].
  split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| clear; lia]]]|].
  split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| clear - NAh; lia]]]|].
  split; [split; [exact HD| split; [exact ENA| clear - NBh; lia]]| exact NE].
Qed.
End CC.

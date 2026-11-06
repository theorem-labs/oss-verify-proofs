(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Cf_iface CfX_kit LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma tr_pixacreate1 : In [0x8e74c] CLIENT_TRACES.
Proof. vm_compute. tauto. Qed.
Lemma tr_pixacreate2 : In [0x8e7b8] CLIENT_TRACES.
Proof. vm_compute. tauto. Qed.
Lemma tr_pixacreate_boxa : In [0x8ee4c] CLIENT_TRACES.
Proof. vm_compute. tauto. Qed.

Section PIXACREATE.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis BOXAC : boxaCreate_cps RT.

Theorem pixaCreate_ok : pixaCreate_cps RT.
Proof using AF GP BOXAC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ras
    FDO MST -> -> UCTX TR0 EMP ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL, uctx in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixaCreate in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof ST as (STa & STb & _).
  refresh RT AF. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 32, usp)] [0x5edec; 0x8ee20].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  (* [comment removed for export] *)
  eapply cps_seq; [eapply (gp_calloc RT GP) with (lo := lo) (nmemb := 1) (size := 32); rt_side idtac |].
  all: lazymatch goal with
       | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_pixacreate1| left; ul]
       | |- (_ <= CALLOC_MAX) => unfold CALLOC_MAX; lia
       | |- (Z.of_nat (length (rt_live _ _)) < LIVE_MAX) => clear - LVB; lia
       | |- _ => idtac
       end.
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  lazymatch goal with H : rw_cells asegs ?mm ?p [CB (Z.to_nat (1 * 32)) ?bs] |- _ =>
    pose proof (rw_cells_recell mm p [CB (Z.to_nat (1 * 32)) bs]
                  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H
                  ltac:(cbn; tauto) eq_refl eq_refl) as PAC; clear H end.
  change (1 * 32) with 32 in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 32) :: _ |- _ => set (pa := p) in *; rename H into LV1 end.
  assert (PA0 : 0 < pa) by (first [assumption | lia]).
  chunk_facts RT AF GP pa 32.
  assert (PA_AP : forall a, PF a -> a < pa \/ pa + 32 <= a).
  { intros a Ha. lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (pa, 32) :: _, FRS : rt_frames RT ?S = _, SP0 : rt_sp0 RT ?S = _ |- _ =>
      apply (new_chunk_apart RT AF S mm pa 32 _ _ usp a A L FRS ltac:(rewrite SP0; ul) Ha) end. }
  assert (PALO : pa + 32 <= lo) by (clear - CKR LOW; lia).
  unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 32, usp); (pa, pa + 32)] [0x5edec; 0x8ee20].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pa, 32; split; [solve [in_live_tac]| lia]| exact I]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (PA_AP _ Hx); split; [lia| split; [lia| exact I]]).
  eapply cps_seq; [eapply (gp_calloc RT GP) with (lo := lo) (nmemb := 20) (size := 8); rt_side idtac |].
  all: lazymatch goal with
       | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_pixacreate2| left; ul]
       | |- (_ <= CALLOC_MAX) => unfold CALLOC_MAX; lia
       | |- (Z.of_nat (length (rt_live _ _)) < LIVE_MAX) => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length]; clear - LVB; lia
       | |- _ => idtac
       end.
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  change (20 * 8) with 160 in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 160) :: _ |- _ => set (parr := p) in *; rename H into LV2 end.
  chunk_facts RT AF GP parr 160.
  assert (PARR_AP : forall a, PF a -> a < parr \/ parr + 160 <= a).
  { intros a Ha. lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (parr, 160) :: _, FRS : rt_frames RT ?S = _, SP0 : rt_sp0 RT ?S = _ |- _ =>
      apply (new_chunk_apart RT AF S mm parr 160 _ _ usp a A L FRS ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul)) end.
    apply (aclient_mono _ _ usp _ _ _ _ Ha); [solve [live_add_tac]| solve [frames_sub_tac]| lia]. }
  assert (DPP : parr + 160 <= pa \/ pa + 32 <= parr).
  { lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (parr, 160) :: _ |- _ =>
      apply (af_live_disj RT AF S mm parr 160 pa 32 [] _ A L); cbn [app]; solve [in_live_tac] end. }
  unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 32, usp); (pa, pa + 32)] [0x5edec; 0x8ee20].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pa, 32; split; [solve [in_live_tac]| lia]| exact I]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (PA_AP _ Hx); split; [lia| split; [lia| exact I]]).
  pose proof BOXAC as BC. unfold boxaCreate_cps in BC.
  eapply cps_seq.
  { eapply BC with (lo := lo) (n := 20) (ras := @nil Z); rt_side idtac.
    all: lazymatch goal with
         | |- uctx _ _ _ _ => unfold uctx; rewrite ?unsigned_lit by ul; cbn [chain_ok]; unfold link_invalid; left; ul
         | |- In _ CLIENT_TRACES => exact tr_pixacreate_boxa
         | |- _ = [] -> _ => intros _; rewrite ?unsigned_lit by ul; left; ul
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- _ <= _ <= _ => clear; lia
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]| exact I]).
  change (20 * 8) with 160 in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 160) :: (?q, 24) :: _ |- _ => set (barr := p) in *; set (ba := q) in *; rename H into LV3 end.
  lazymatch goal with H : boxa_new _ _ ba 20 barr |- _ => destruct H as (((bpad & BAC) & (BAIN & BA0 & BA16 & _) & (BRIN & BR0 & BR16 & _) & _ & NBB) & BRC) end.
  unfold boxa_cells in BAC. change (8 * 20) with 160 in *.
  chunk_facts RT AF GP ba 24. chunk_facts RT AF GP barr 160.
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
    pose proof (af_live_disj RT AF S mm barr 160 ba 24 [] _ A LV3 ltac:(cbn [app]; left; reflexivity)) as D1;
    pose proof (af_live_disj RT AF S mm barr 160 parr 160 [] _ A LV3 ltac:(cbn [app]; right; rewrite LV2; left; reflexivity)) as D2;
    pose proof (af_live_disj RT AF S mm barr 160 pa 32 [] _ A LV3 ltac:(cbn [app]; right; rewrite LV2, LV1; right; left; reflexivity)) as D3;
    pose proof (af_live_disj RT AF S mm ba 24 parr 160 [(barr, 160)] _ A LV3 ltac:(cbn [app]; right; rewrite LV2; left; reflexivity)) as D4;
    pose proof (af_live_disj RT AF S mm ba 24 pa 32 [(barr, 160)] _ A LV3 ltac:(cbn [app]; right; rewrite LV2, LV1; right; left; reflexivity)) as D5 end.
  refresh RT AF. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 32, usp); (pa, pa + 32)] (@nil Z).
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pa, 32; split; [solve [in_live_tac]| lia]| exact I]]).
  lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (PA_AP _ Hx); split; [lia| split; [lia| exact I]]) end.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, pa, parr, ba, barr end.
  split.
  2:{ repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end. repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end. rewrite LV3, LV2, LV1. repeat split; reflexivity. }
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
  { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
  split; [intros a Ha _; apply AGF; exact Ha|].
  unfold pixa_obj, pixa_cells, boxa_empty, boxa_cells, chunk. change (8 * 20) with 160.
  split; [eexists; exact PAC|].
  split; [split; [rewrite LV3, LV2, LV1; right; right; right; left; reflexivity| repeat split; first [assumption | lia]]|].
  split; [split; [rewrite LV3, LV2; right; right; left; reflexivity| repeat split; first [assumption | lia]]|].
  split; [split; [eexists; exact BAC|]; split; [split; [exact BAIN| repeat split; first [assumption | lia]]|];
          split; [split; [exact BRIN| repeat split; first [assumption | lia]]|]; split; [clear; lia| exact NBB]|].
  split; [clear; lia|].
  unfold parked in D1, D2, D3, D4, D5, DPP.
  repeat constructor; cbn [In]; clear - D1 D2 D3 D4 D5 DPP; intuition lia.
Qed.
End PIXACREATE.

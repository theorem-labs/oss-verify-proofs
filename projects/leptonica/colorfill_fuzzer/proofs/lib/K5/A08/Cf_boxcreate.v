(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Cf_iface CfX_kit.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma tr_boxcreate : In [0x8ea3c] CLIENT_TRACES.
Proof. vm_compute. tauto. Qed.

Section BOXCREATE.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem boxCreate_ok : boxCreate_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo x y w h
    FDO MST -> -> -> -> -> XR YR WR HR ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_boxCreate in *.
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
  Time walk_to AF MST [(usp - 48, usp)] [0x5ec64].
  (* [comment removed for export] *)
  brfork HNEG.
  1:{ exfalso. pose proof (Z.add_lor_land h w) as E. pose proof (Z.land_nonneg h w) as L. clear - HNEG E L WR HR. lia. }
  clear HNEG.
  Time cwalk [0x5ec64].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq; [eapply (gp_calloc RT GP) with (lo := lo) (nmemb := 1) (size := 20); rt_side idtac |].
  all: lazymatch goal with
       | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_boxcreate| left; ul]
       | |- (_ <= CALLOC_MAX) => unfold CALLOC_MAX; lia
       | |- (Z.of_nat (length (rt_live _ _)) < LIVE_MAX) => clear - LVB; lia
       | |- _ => idtac
       end.
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  lazymatch goal with H : rw_cells asegs ?mm ?p [CB (Z.to_nat (1 * 20)) ?bs] |- _ =>
    pose proof (rw_cells_recell mm p [CB (Z.to_nat (1 * 20)) bs]
                  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] H
                  ltac:(cbn; tauto) eq_refl eq_refl) as BXC; clear H end.
  change (1 * 20) with 20 in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 20) :: _ |- _ => set (b := p) in *; rename H into LVB1 end.
  chunk_facts RT AF GP b 20.
  assert (BOX_AP : forall a, PF a -> a < b \/ b + 20 <= a).
  { intros a Ha. lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (b, 20) :: _, FRS : rt_frames RT ?S = _, SP0 : rt_sp0 RT ?S = _ |- _ =>
      apply (new_chunk_apart RT AF S mm b 20 _ _ usp a A L FRS ltac:(rewrite SP0; ul) Ha) end. }
  unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 48, usp); (b, b + 20)] (@nil Z).
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists b, 20; split; [solve [in_live_tac]| lia]| exact I]]).
  lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (BOX_AP _ Hx); split; [lia| split; [lia| exact I]]) end.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, b end.
  split.
  2:{ repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end. repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end. repeat split; first [exact LVB1 | reflexivity]. }
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
  { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
  split; [intros a Ha _; apply AGF; exact Ha|].
  split; [unfold box_cells; exact BXC|]. unfold chunk. split; [rewrite LVB1; left; reflexivity|]. repeat split; first [assumption | lia].
Qed.
End BOXCREATE.

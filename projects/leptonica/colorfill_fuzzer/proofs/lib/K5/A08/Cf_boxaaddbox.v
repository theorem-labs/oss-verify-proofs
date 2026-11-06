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
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Cf_iface Cf_kit CfX_kit.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section BOXAADDBOX.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem boxaAddBox_ok : boxaAddBox_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ba arr b x y w h
    FDO MST -> -> -> -> BN BO NBA NBR ENV.
  unfold lpost, lenv, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct BN as (((pad & BAC) & (BAIN & BA0 & BA16 & _) & (ARIN & AR0 & AR16 & _) & _ & NAB) & ARC).
  destruct BO as (BXC & (BIN & B0 & B16 & _)).
  unfold boxa_cells in BAC. unfold box_cells in BXC.
  change (Z.to_nat (1 * 8)) with 8%nat in ARC. change (8 * 1) with 8 in ARIN.
  pose proof (rw_cells_recell m arr _ [C8 (Z_to_bv 64 0)] ARC ltac:(cbn; tauto) eq_refl eq_refl) as ARC8. clear ARC.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_boxaAddBox in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(ba, ba + 4); (arr, arr + 8)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof ST as (STa & STb & _).
  (* [comment removed for export] *)
  pose proof (live_apart RT AF Σ m ba 24 arr 8 ART0 BAIN ARIN ltac:(intros E; apply NAB; symmetry; exact E)) as D1.
  pose proof (live_apart RT AF Σ m b 20 ba 24 ART0 BIN BAIN NBA) as D2.
  pose proof (live_apart RT AF Σ m b 20 arr 8 ART0 BIN ARIN NBR) as D3.
  chunk_facts RT AF GP ba 24. chunk_facts RT AF GP arr 8. chunk_facts RT AF GP b 20.
  refresh RT AF. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 64, usp); (ba, ba + 4); (arr, arr + 8)] (@nil Z).
  (* [comment removed for export] *)
  sx32_fix. rewrite !(unsigned_lit 0) by (clear; lia). change (0 * 8) with 0. rewrite !Z.add_0_r.
  Time cwalk (@nil Z).
  rewrite (sx32_small 0) in BAC by (clear; lia). rewrite (unsigned_lit 0) in BAC by (clear; lia). change (0 + 1) with 1 in BAC.
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul|
                        split; [intros zz Hzz; right; right; left; exists ba, 24; split; [exact BAIN| lia]|
                        split; [intros zz Hzz; right; right; left; exists arr, 8; split; [exact ARIN| lia]| exact I]]]).
  agf_munch AGF MU ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| split; [tauto| exact I]]]).
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  exists Σ. split; [| repeat split; reflexivity].
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [assumption| assumption]]]| split; assumption]|].
  split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
  unfold boxa_one, boxa_cells, box_obj, box_cells, chunk.
  split; [eexists; exact BAC|]. split; [split; [exact BAIN| repeat split; first [assumption | lia]]|].
  split; [split; [exact ARIN| repeat split; first [assumption | lia]]|].
  split; [exact ARC8|]. split; [split; [exact BXC| split; [exact BIN| repeat split; first [assumption | lia]]]|].
  split; [exact NAB|]. split; [exact NBA| exact NBR].
Qed.
End BOXAADDBOX.

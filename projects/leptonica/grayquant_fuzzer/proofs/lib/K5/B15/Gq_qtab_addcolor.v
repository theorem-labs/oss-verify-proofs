(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_fuzzkit Gm_iface Gm_kit Gq_iface Gq_thr_iface Gq_thr2_iface Gq_qtab_defs
  LeptB_guard LeptB_guard2 Gq_guardx.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


Section AC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem pixcmapAddColor_gray_ok : pixcmapAddColor_gray_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    cmap cv v FDO MST -> -> -> -> -> VB CMO NLT NAL256 ENV.
  unfold lpost, lenv, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct cv as [carr depth nalloc n]. cbn [c_arr c_depth c_nalloc c_n] in *. subst nalloc.
  pose proof CMO as ((pad & CMC) & (CMIN & CM0 & CM16 & _) & (CAIN & CA0 & CA16 & _) & CMOK & CANE).
  unfold cmap_cells in CMC. cbn [c_arr c_depth c_nalloc c_n] in CMC.
  pose proof CMOK as (DOK & NAL & NRG).
  cbn [c_arr c_depth c_nalloc c_n] in CMIN, CM0, CM16, CAIN, CA0, CA16, CANE, DOK, NAL, NRG.   (* [comment removed for export] *)
  change (4 * 256) with 1024 in CAIN.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixcmapAddColor, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (W2 := [(cmap + 16, cmap + 20); (carr + 4 * n, carr + 4 * n + 4)]).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside W2 a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof (live_apart RT AF Σ m cmap 24 carr 1024 ART0 CMIN CAIN ltac:(intro E; apply CANE; symmetry; exact E)) as DCA.
  chunk_facts RT AF GP cmap 24. chunk_facts RT AF GP carr 1024.
  pose proof (af_acc_live RT AF Σ m cmap 24 ART0 CMIN) as (_ & ACCM). pose proof (af_acc_live RT AF Σ m carr 1024 ART0 CAIN) as (WRA & ACCA).
  (* [comment removed for export] *)
  destruct (wr_at_rw_C1 m (carr + 4 * n) (wr_at_sub m carr 1024 (carr + 4 * n) 1 WRA ltac:(lia) ltac:(lia) ltac:(lia))) as (q0 & QB0).
  destruct (wr_at_rw_C1 m (carr + 4 * n + 1) (wr_at_sub m carr 1024 (carr + 4 * n + 1) 1 WRA ltac:(lia) ltac:(lia) ltac:(lia))) as (q1 & QB1).
  destruct (wr_at_rw_C1 m (carr + 4 * n + 2) (wr_at_sub m carr 1024 (carr + 4 * n + 2) 1 WRA ltac:(lia) ltac:(lia) ltac:(lia))) as (q2 & QB2).
  destruct (wr_at_rw_C1 m (carr + 4 * n + 3) (wr_at_sub m carr 1024 (carr + 4 * n + 3) 1 WRA ltac:(lia) ltac:(lia) ltac:(lia))) as (q3 & QB3).
  hide CMO.
  carve_frame 16%nat ST.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 16, usp); (cmap + 16, cmap + 20); (carr + 4 * n, carr + 4 * n + 4)] [0x97820].
  replace (carr + n * 4 + 2) with (carr + 4 * n + 2) by lia. replace (carr + n * 4) with (carr + 4 * n) by lia.
  awalk [0x97820].
  set (A4 := carr + 4 * n) in *.
  awalk1.
  subst A4.
  awalk [0x97820].
  try (lazymatch goal with ST' : stk asegs _ _ (_ + -16) |- _ => release_frame FR ST' usp end).
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul
     | split; [intros zz Hzz; right; right; left; exists cmap, 24; split; [exact CMIN| lia]
     | split; [intros zz Hzz; right; right; left; exists carr, 1024; split; [exact CAIN| lia]| exact I]]]).
  lazymatch goal with MUx : munch _ m _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx1 Hx2]; pose proof (PFS _ (conj Hx1 Hx2)); try unfold W2 in Hx2; cbn [outside] in Hx2; repeat split; try exact I; first [lia | tauto]) end.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
  split.
  - eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; assumption]]| split; assumption]|].
    split; [intros a Ha Ho; apply AGF; split; assumption|].
    split.
    + (* [comment removed for export] *)
      unfold cmap_obj, cmap_cells, cmap_ok. cbn [c_arr c_depth c_nalloc c_n].
      split; [| split; [split; [exact CMIN| split; [lia| split; [assumption| lia]]]| split; [split; [exact CAIN| split; [lia| split; [assumption| lia]]]| split; [| exact CANE]]]].
      * exists pad. lazymatch goal with H : rw_cells asegs ?mm cmap _ |- rw_cells asegs ?mm cmap _ => exact H end.
      * split; [exact DOK| split; [exact NAL| lia]].
    + (* [comment removed for export] *)
      lazymatch goal with Q0 : rw_cells asegs ?mm (carr + 4 * n) [C1 _], Q1 : rw_cells asegs ?mm (carr + 4 * n + 1) [C1 _],
                          Q2 : rw_cells asegs ?mm (carr + 4 * n + 2) [C1 _], Q3 : rw_cells asegs ?mm (carr + 4 * n + 3) [C1 _] |- _ =>
        apply (proj2 (rw_cells_app mm (carr + 4 * n) [C1 _] [C1 _; C1 _; C1 _])); split; [exact Q0|];
        lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (carr + 4 * n + 1) by (cbn [cells_size csize Nat.add]; lia) end;
        apply (proj2 (rw_cells_app mm (carr + 4 * n + 1) [C1 _] [C1 _; C1 _])); split; [exact Q1|];
        lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (carr + 4 * n + 2) by (cbn [cells_size csize Nat.add]; lia) end;
        apply (proj2 (rw_cells_app mm (carr + 4 * n + 2) [C1 _] [C1 _])); split; [exact Q2|];
        lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (carr + 4 * n + 3) by (cbn [cells_size csize Nat.add]; lia) end;
        replace (Z_to_bv 8 255) with (Z_to_bv 8 (-1)) by (apply bv_eq; vm_compute; reflexivity); exact Q3 end.
  - repeat split; auto; lia.
Qed.
End AC.

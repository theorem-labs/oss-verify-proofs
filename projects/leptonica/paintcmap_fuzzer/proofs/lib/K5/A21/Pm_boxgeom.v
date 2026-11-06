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
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Pm_iface Pm_kit PmX_kit.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section BOXGEOM.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem boxGetGeometry_ok : boxGetGeometry_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo b x y w h px py pw ph x0 y0 w0 h0
    FDO MST -> -> -> -> -> -> BO XR YR WR HR OPX OPY OPW OPH OXY OYW OWH CX CY CW CH ENV.
  unfold box_obj in BO.
  unfold lpost, lenv, keeps, keepsL, optrF in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct OPX as (OWX & PX0 & PX8 & PXH & PXS). destruct OPY as (OWY & PY0 & PY8 & PYH & PYS).
  destruct OPW as (OWW & PW0 & PW8 & PWH & PWS). destruct OPH as (OWH' & PH0 & PH8 & PHH & PHS).
  destruct BO as (BXC & (INB & BX0 & BX16 & _)).
  assert (AKX : accok (rt_live RT Σ) (rt_frames RT Σ) m px 4) by (right; exact OWX).
  assert (AKY : accok (rt_live RT Σ) (rt_frames RT Σ) m py 4) by (right; exact OWY).
  assert (AKW : accok (rt_live RT Σ) (rt_frames RT Σ) m pw 4) by (right; exact OWW).
  assert (AKH : accok (rt_live RT Σ) (rt_frames RT Σ) m ph 4) by (right; exact OWH').
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  (* [comment removed for export] *)
  assert (LOC : forall p, own_frame (rt_frames RT Σ) m p 4 -> p + 4 <= lo /\ (p + 4 <= b \/ b + 20 <= p)).
  { intros p (f & k & Hin & Q1 & Q2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R1 & _ & R2). specialize (R2 b 20 INB). lia. }
  destruct (LOC _ OWX) as (LX & AX). destruct (LOC _ OWY) as (LY & AY). destruct (LOC _ OWW) as (LW & AW'). destruct (LOC _ OWH') as (LHh & AH). clear LOC.
  unfold entry_st, e_boxGetGeometry, box_cells in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(px, px + 4); (py, py + 4); (pw, pw + 4); (ph, ph + 4)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [HH|HH]; [left; exact HH| right; unfold STACK_WIN in HH; lia]. }
  pose proof ST as (STa & STb & _).
  chunk_facts RT AF GP b 20.
  refresh RT AF.
  cps_walk AF MST.
  pose proof (munch_refl [(usp - 16, usp); (px, px + 4); (py, py + 4); (pw, pw + 4); (ph, ph + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  Time awalk0.
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul|
     split; [intros zz Hzz; exact (accok_aclient _ _ _ _ px 4 zz AKX Hzz)| split; [intros zz Hzz; exact (accok_aclient _ _ _ _ py 4 zz AKY Hzz)|
     split; [intros zz Hzz; exact (accok_aclient _ _ _ _ pw 4 zz AKW Hzz)| split; [intros zz Hzz; exact (accok_aclient _ _ _ _ ph 4 zz AKH Hzz)| exact I]]]]]).
  agf_munch AGF MU ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; cbn [outside] in HxO;
                                   split; [clear - HxS LOW LOR; lia| clear - HxO; tauto]).
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  exists Σ. split; [| repeat split; reflexivity].
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [assumption| assumption]]]| split; assumption]|].
  split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
  rewrite (sx32_small x) in CX by (clear - XR; lia). rewrite (sx32_small y) in CY by (clear - YR; lia).
  rewrite (sx32_small w) in CW by (clear - WR; lia). rewrite (sx32_small h) in CH by (clear - HR; lia).
  split; [exact CX| split; [exact CY| split; [exact CW| exact CH]]].
Qed.
End BOXGEOM.

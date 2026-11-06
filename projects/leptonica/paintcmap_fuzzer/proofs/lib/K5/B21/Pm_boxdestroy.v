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
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Pm_iface Pm_kit PmX_kit LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section BOXDESTROY.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Lemma tr_boxdestroy : In [0x8e2bc] CLIENT_TRACES.  Proof. vm_compute. tauto. Qed.

Theorem boxDestroy_ok : boxDestroy_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp b x y w h
    FDO MST -> -> OP PPC BO ENV LVPOS.
  unfold box_obj in BO.
  pose proof (gp_free RT GP) as FREE.
  unfold lpost_f, lenv, keeps, keepsL, optrF in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct OP as (OWNF & PP0 & PP8 & PPH & PPS).
  destruct BO as (BXC & (INB & BX0 & BX16 & _)).
  assert (OWN : accok (@nil (Z * Z)) (rt_frames RT Σ) m pp 8) by (right; exact OWNF).   (* [comment removed for export] *)
  set (LVF := live_remove b (rt_live RT Σ)) in *.
  assert (LVFS : forall e, In e LVF -> In e (rt_live RT Σ)) by (intros e He; exact (live_remove_sub _ _ _ He)).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (PPLO : pp + 8 <= lo).
  { destruct OWNF as (f & k & Hin & Q1 & Q2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). lia. }
  unfold entry_st, e_boxDestroy, box_cells in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient LVF (rt_frames RT Σ) usp a /\ outside [(pp, pp + 8)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0) as [HH|HH]; [| left; exact HH| right; unfold STACK_WIN in HH; lia].
    apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ usp a Ha); [exact LVFS| auto| lia]. }
  assert (SUBB : forall e, In e LVF -> In e (rt_live RT Σ) /\ fst e <> b)
    by (intros e He; split; [exact (LVFS _ He)| exact (proj2 (live_remove_in _ _ _ He))]).
  assert (SPW : rt_sp0 RT Σ - STACK_WIN <= usp) by (unfold STACK_WIN; clear - LOW LOR; lia).
  assert (BX_AP : forall a, PF a -> a < b \/ b + 20 <= a)
    by (intros a [Ha _]; exact (removed_chunk_apart RT AF Σ m b 20 LVF usp a ART0 INB SUBB SPW Ha)).
  (* [comment removed for export] *)
  assert (PPBX : pp + 8 <= b \/ b + 20 <= pp).
  { destruct OWNF as (f & k & Hin & Q1 & Q2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & R). specialize (R b 20 INB). lia. }
  clear SUBB SPW.
  chunk_facts RT AF GP b 20.
  refresh RT AF.
  cps_walk AF MST.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp); (b + 16, b + 20)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 32%nat ST.
  Time awalk [0x5ee14].
  assert (AMO : amo_aligned AW (Z_to_bv 64 (b + 16)) = true) by (apply cfx_amo_aligned; [clear - BX0 CKR SP0R; lia| clear - BX16; Z.div_mod_to_equations; lia]).
  cfx_amo_sub1 AMO 1 ltac:(clear; lia).
  rewrite ?(sx32_small 1) by (clear; lia). try br.
  Time awalk [0x5ee14].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists b, 20; split; [exact INB| lia]| exact I]]).
  to_entry.
  agf_munch AGF MU ltac:(fun Hx => cbn [outside]; pose proof (BX_AP _ Hx) as HxA; pose proof (PFS _ Hx) as HxS; split; [clear - HxS LOW LOR; lia| split; [clear - HxA; lia| exact I]]).
  eapply cps_seq.
  { eapply FREE with (lo := lo) (p := b) (n := 20); try reflexivity; try assumption.
    - unfold call_ok. rewrite unsigned_lit by ul. split; [eassumption| ul].
    - apply unwind_okC_of_ok; [exact tr_boxdestroy|]. left.
      rewrite (unsigned_lit (pp / 8 + SHB)) by (unfold SHB; clear - PP0 PPLO LOR SPT; Z.div_mod_to_equations; lia).
      rewrite (unsigned_lit (usp + -32)) by (clear - LOR STa SPT; lia).
      unfold SHB; clear - PPLO LOR LOW SP0W PP0 STa; Z.div_mod_to_equations; lia. }
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  cps_walk AF MST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(usp - 32, usp); (pp, pp + 8)] mm) as MU3; pose proof (wmono_refl asegs mm) as WM3 end.
  Time awalk0.
  cps_stop.
  agf_munch AGF MU3 ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx1 Hx2]; cbn [outside] in Hx2; pose proof (PFS _ (conj Hx1 Hx2)) as HxS;
                                    split; [clear - HxS LOW LOR PPLO; lia| split; [clear - Hx2; tauto| exact I]]).
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
  eexists. split.
  - eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [| split; [assumption| assumption]]| split; assumption]|].
    + lazymatch goal with A : ART RT ?S ?mm, MUx : munch ?W ?mm ?mf, WMx : wmono asegs ?mm ?mf |- ART RT ?S ?mf =>
        apply (art_client_writes RT AF S mm mf (usp + -32) W A MUx WMx) end.
      * repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end. ul.
      * cbn [ivls_client]. split; [intros zz Hzz; left; ul|]. split; [| exact I]. intros zz Hzz.
        lazymatch goal with |- aclient ?lv' ?frs' ?sp' _ => 
          apply (aclient_mono (@nil (Z * Z)) (rt_frames RT Σ) sp' lv' frs' sp' zz); [exact (accok_aclient _ _ _ sp' pp 8 zz OWN Hzz)| solve [live_sub_tac]| solve [frames_sub_tac]| lia] end.
    + split; [| assumption]. intros a Ha Ho. apply AGF. split; [| exact Ho].
      lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with LVF in Ha by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity) end.
      exact Ha.
  - repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end. repeat split; auto; lia.
Qed.
End BOXDESTROY.

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
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


Section CD.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FREE : free_contractC RT.

Lemma tr_cd1 : In [0x927e4] CLIENT_TRACES.  Proof. vm_compute. tauto. Qed.
Lemma tr_cd2 : In [0x927ec] CLIENT_TRACES.  Proof. vm_compute. tauto. Qed.

Lemma pixcmapDestroy_ok : pixcmapDestroy_cps RT.
Proof using AF GP FREE.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pc cmap cv
    FDO MST -> -> OP PCC CO ENV RES.
  unfold lpost_f, lenv, keeps, keepsL, optrL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct OP as (OWN & PC0 & PC8 & PCH & PCS).
  destruct CO as ((pad & CMC) & (INC & CM0 & CM16 & _) & (INA & AR0 & AR16 & _) & CMOK & NEQ).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (arr := c_arr cv) in *.
  assert (ACCP : acc asegs m pc 8).
  { apply (accok_acc RT AF Σ m pc 8 ART0 ltac:(lia)). destruct OWN as [(p & k & Hin & H1 & H2)|OF]; [left| right; exact OF].
    exists p, k. split; [exact (live_remove_sub _ _ _ (live_remove_sub _ _ _ Hin))| lia]. }
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (PCLO : pc + 8 <= lo).
  { destruct OWN as [(p & k & Hin & H1 & H2)|(f & k & Hin & H1 & H2 & _)].
    - pose proof (af_live_range RT AF Σ m p k ART0 (live_remove_sub _ _ _ (live_remove_sub _ _ _ Hin))) as (_ & R & _). lia.
    - pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). lia. }
  pose proof (af_acc_live RT AF Σ m cmap 24 ART0 INC) as (WRC & ACCC).
  pose proof (af_live_range RT AF Σ m cmap 24 ART0 INC) as (_ & CMR & CMS).
  unfold entry_st, e_pixcmapDestroy, cmap_cells, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (LVF := live_remove cmap (live_remove arr (rt_live RT Σ))) in *.
  set (PF := fun a => aclient LVF (rt_frames RT Σ) usp a /\ outside [(pc, pc + 8)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0) as [H|H]; [| left; exact H| right; unfold STACK_WIN in H; lia].
    apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ usp a Ha); [| auto| lia].
    intros e He. exact (live_remove_sub _ _ _ (live_remove_sub _ _ _ He)). }
  cps_walk AF MST.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 32%nat ST.
  Time awalk [0x5ee14].
  cps_stop. to_entry.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_writes RT AF Σ m m1 (usp + -32) _ ART0 MU WM); [ul|].
    cbn [ivls_client]. split; [| exact I]. intros x Hx. left. ul. }
  agf_munch AGF MU ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
  eapply cps_seq.
  { eapply FREE with (lo := lo); try reflexivity; try eassumption.
    - unfold call_ok. rewrite unsigned_lit by ul. split; [exact ST| ul].
    - apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_cd1| left; ul]. }
  after_call RT AF.
  agf_call AGF AG ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  cps_walk AF MST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(usp - 32, usp)] mm) as MU1; pose proof (wmono_refl asegs mm) as WM1 end.
  awalk [0x5ee14].
  cps_stop. to_entry.
  agf_munch AGF MU1 ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
  eapply cps_seq.
  { eapply FREE with (lo := lo); try reflexivity; try eassumption.
    - solve [in_live_tac].
    - unfold call_ok. rewrite unsigned_lit by ul. split; [eassumption| ul].
    - apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_cd2| left; ul]. }
  after_call RT AF.
  agf_call AGF AG0 ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  cps_walk AF MST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(usp - 32, usp); (pc, pc + 8)] mm) as MU2; pose proof (wmono_refl asegs mm) as WM2 end.
  Time awalk0.
  cps_stop.
  agf_munch AGF MU2 ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx1 Hx2]; cbn [outside] in Hx2; split; [destruct (PFS _ (conj Hx1 Hx2)); lia| split; [tauto| exact I]]).
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
          apply (aclient_mono LVF (rt_frames RT Σ) sp' lv' frs' sp' zz); [exact (accok_aclient _ _ _ sp' pc 8 zz OWN Hzz)| solve [live_sub_tac]| solve [frames_sub_tac]| lia] end.
    + split; [| assumption]. intros a Ha Ho. apply AGF. split; [| exact Ho].
      lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with LVF in Ha; [exact Ha|] end.
      repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. reflexivity.
  - repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end. repeat split; auto; lia.
Qed.
End CD.

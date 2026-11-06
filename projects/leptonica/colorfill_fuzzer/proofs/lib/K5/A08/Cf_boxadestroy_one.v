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
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Cf_iface Cf_kit CfX_kit.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section BOXAD1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Lemma tr_bd0 : In [0x8ef90] CLIENT_TRACES.  Proof. vm_compute. tauto. Qed.
Lemma tr_bd1 : In [0x8f094] CLIENT_TRACES.  Proof. vm_compute. tauto. Qed.
Lemma tr_bd2 : In [0x8f09c] CLIENT_TRACES.  Proof. vm_compute. tauto. Qed.

Theorem boxaDestroy_one_ok : boxaDestroy_one_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pc cmap arr b x y w h
    FDO MST -> -> OP PCC CO ENV LVPOS.
  unfold boxa_one, box_obj in CO.
  pose proof (gp_free RT GP) as FREE.
  unfold lpost_f, lenv, keeps, keepsL, optrL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct OP as (OWN & PC0 & PC8 & PCH & PCS).
  destruct CO as ((bpad & CMC) & (INC & CM0 & CM16 & _) & (INA & AR0 & AR16 & _) & ARC & (BXC & (INB & BX0 & BX16 & _)) & NEQ & NEB & NEBA).
  set (LVF := live_remove cmap (live_remove arr (live_remove b (rt_live RT Σ)))) in *.
  assert (LVFS : forall e, In e LVF -> In e (rt_live RT Σ))
    by (intros e He; exact (live_remove_sub _ _ _ (live_remove_sub _ _ _ (live_remove_sub _ _ _ He)))).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (PCLO : pc + 8 <= lo).
  { destruct OWN as [(p & k & Hin & H1 & H2)|(f & k & Hin & H1 & H2 & _)].
    - pose proof (af_live_range RT AF Σ m p k ART0 (LVFS _ Hin)) as (_ & R & _). lia.
    - pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). lia. }
  pose proof (af_live_range RT AF Σ m cmap 24 ART0 INC) as (_ & CMR & CMS).
  unfold entry_st, e_boxaDestroy, boxa_cells, box_cells, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient LVF (rt_frames RT Σ) usp a /\ outside [(pc, pc + 8)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0) as [H|H]; [| left; exact H| right; unfold STACK_WIN in H; lia].
    apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ usp a Ha); [exact LVFS| auto| lia]. }
  assert (SUBC : forall e, In e LVF -> In e (rt_live RT Σ) /\ fst e <> cmap)
    by (intros e He; split; [exact (LVFS _ He)| exact (proj2 (live_remove_in _ _ _ He))]).
  assert (SUBA : forall e, In e LVF -> In e (rt_live RT Σ) /\ fst e <> arr)
    by (intros e He; split; [exact (LVFS _ He)| exact (proj2 (live_remove_in _ _ _ (live_remove_sub _ _ _ He)))]).
  assert (SUBB : forall e, In e LVF -> In e (rt_live RT Σ) /\ fst e <> b)
    by (intros e He; split; [exact (LVFS _ He)| exact (proj2 (live_remove_in _ _ _ (live_remove_sub _ _ _ (live_remove_sub _ _ _ He))))]).
  assert (SPW : rt_sp0 RT Σ - STACK_WIN <= usp) by (unfold STACK_WIN; clear - LOW LOR; lia).
  assert (BA_AP : forall a, PF a -> a < cmap \/ cmap + 24 <= a)
    by (intros a [Ha _]; exact (removed_chunk_apart RT AF Σ m cmap 24 LVF usp a ART0 INC SUBC SPW Ha)).
  assert (AR_AP : forall a, PF a -> a < arr \/ arr + 8 <= a)
    by (intros a [Ha _]; exact (removed_chunk_apart RT AF Σ m arr 8 LVF usp a ART0 INA SUBA SPW Ha)).
  assert (BX_AP : forall a, PF a -> a < b \/ b + 20 <= a)
    by (intros a [Ha _]; exact (removed_chunk_apart RT AF Σ m b 20 LVF usp a ART0 INB SUBB SPW Ha)).
  (* [comment removed for export] *)
  assert (PPBA : pc + 8 <= cmap \/ cmap + 24 <= pc).
  { pose proof (removed_chunk_apart RT AF Σ m cmap 24 LVF usp pc ART0 INC SUBC SPW (accok_aclient _ _ _ usp pc 8 pc OWN ltac:(clear; lia))) as E1.
    pose proof (removed_chunk_apart RT AF Σ m cmap 24 LVF usp (pc + 7) ART0 INC SUBC SPW (accok_aclient _ _ _ usp pc 8 (pc + 7) OWN ltac:(clear; lia))) as E2.
    clear - E1 E2. lia. }
  assert (PPAR : pc + 8 <= arr \/ arr + 8 <= pc).
  { pose proof (removed_chunk_apart RT AF Σ m arr 8 LVF usp pc ART0 INA SUBA SPW (accok_aclient _ _ _ usp pc 8 pc OWN ltac:(clear; lia))) as E1.
    pose proof (removed_chunk_apart RT AF Σ m arr 8 LVF usp (pc + 7) ART0 INA SUBA SPW (accok_aclient _ _ _ usp pc 8 (pc + 7) OWN ltac:(clear; lia))) as E2.
    clear - E1 E2. lia. }
  assert (PPBX : pc + 8 <= b \/ b + 20 <= pc).
  { pose proof (removed_chunk_apart RT AF Σ m b 20 LVF usp pc ART0 INB SUBB SPW (accok_aclient _ _ _ usp pc 8 pc OWN ltac:(clear; lia))) as E1.
    pose proof (removed_chunk_apart RT AF Σ m b 20 LVF usp (pc + 7) ART0 INB SUBB SPW (accok_aclient _ _ _ usp pc 8 (pc + 7) OWN ltac:(clear; lia))) as E2.
    clear - E1 E2. lia. }
  pose proof (live_apart RT AF Σ m cmap 24 arr 8 ART0 INC INA ltac:(congruence)) as D_CA.
  pose proof (live_apart RT AF Σ m cmap 24 b 20 ART0 INC INB ltac:(congruence)) as D_CB.
  pose proof (live_apart RT AF Σ m arr 8 b 20 ART0 INA INB ltac:(congruence)) as D_AB.
  clear SUBC SUBA SUBB SPW.
  chunk_facts RT AF GP cmap 24. chunk_facts RT AF GP arr 8. chunk_facts RT AF GP b 20.
  assert (ACCP : acc asegs m pc 8).
  { apply (accok_acc RT AF Σ m pc 8 ART0 ltac:(lia)). destruct OWN as [(p & k & Hin & H1 & H2)|OF]; [left| right; exact OF].
    exists p, k. split; [exact (LVFS _ Hin)| lia]. }
  refresh RT AF. lib_refresh RT GP.
  cps_walk AF MST.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 144, usp); (cmap + 8, cmap + 12); (b + 16, b + 20); (arr, arr + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 144%nat ST.
  Time awalk [0x5ec5c].
  assert (AMO : amo_aligned AW (Z_to_bv 64 (cmap + 8)) = true) by (apply cfx_amo_aligned; [clear - CM0 CMR SP0R; lia| clear - CM16; Z.div_mod_to_equations; lia]).
  cfx_amo_sub1 AMO 1 ltac:(clear; lia).
  rewrite ?(sx32_small 1) by (clear; lia). try br.
  Time awalk [0x5ec5c].
  assert (AMO2 : amo_aligned AW (Z_to_bv 64 (b + 16)) = true) by (apply cfx_amo_aligned; [clear - BX0 CKR1 SP0R; lia| clear - BX16; Z.div_mod_to_equations; lia]).
  cfx_amo_sub1 AMO2 1 ltac:(clear; lia).
  rewrite ?(sx32_small 1) by (clear; lia). try br.
  Time awalk [0x5ec5c].
  cps_stop. to_entry.
  lazymatch goal with MUx : munch _ m ?mm |- _ =>
    assert (ART1 : ART RT Σ mm)
      by (apply (art_client_writes RT AF Σ m mm (usp + -144) _ ART0 MUx WM); [ul|];
          cbn [ivls_client]; split; [intros z Hz; left; ul|
            split; [intros z Hz; right; right; left; exists cmap, 24; split; [exact INC| lia]|
            split; [intros z Hz; right; right; left; exists b, 20; split; [exact INB| lia]|
            split; [intros z Hz; right; right; left; exists arr, 8; split; [exact INA| lia]| exact I]]]]) end.
  agf_munch AGF MU ltac:(fun Hx => cbn [outside]; pose proof (BA_AP _ Hx); pose proof (AR_AP _ Hx); pose proof (BX_AP _ Hx);
                                   split; [destruct (PFS _ Hx); lia| split; [lia| split; [lia| split; [lia| exact I]]]]).
  eapply cps_seq.
  { eapply FREE with (lo := lo) (p := b) (n := 20); try reflexivity; try assumption.
    - unfold call_ok. rewrite unsigned_lit by ul. split; [exact ST| ul].
    - apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_bd0| left; ul]. }
  Time after_call RT AF.
  agf_call AGF AG ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  cps_walk AF MST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(usp - 144, usp); (arr, arr + 8)] mm) as MU1; pose proof (wmono_refl asegs mm) as WM1 end.
  Time awalk [0x5ec5c].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists arr, 8; split; [solve [in_live_tac]| lia]| exact I]]).
  to_entry.
  agf_munch AGF MU1 ltac:(fun Hx => cbn [outside]; pose proof (AR_AP _ Hx); split; [destruct (PFS _ Hx); lia| split; [lia| exact I]]).
  eapply cps_seq.
  { eapply FREE with (lo := lo) (p := arr) (n := 8); try reflexivity; try assumption.
    - solve [in_live_tac].
    - unfold call_ok. rewrite unsigned_lit by ul. split; [eassumption| ul].
    - apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_bd1| left; ul]. }
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  cps_walk AF MST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(usp - 144, usp)] mm) as MU2; pose proof (wmono_refl asegs mm) as WM2 end.
  Time awalk [0x5ec5c].
  cps_stop. to_entry.
  agf_munch AGF MU2 ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
  eapply cps_seq.
  { eapply FREE with (lo := lo) (p := cmap) (n := 24); try reflexivity; try assumption.
    - solve [in_live_tac].
    - unfold call_ok. rewrite unsigned_lit by ul. split; [eassumption| ul].
    - apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_bd2| left; ul]. }
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  cps_walk AF MST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(usp - 144, usp); (pc, pc + 8)] mm) as MU3; pose proof (wmono_refl asegs mm) as WM3 end.
  Time awalk0.
  cps_stop.
  agf_munch AGF MU3 ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx1 Hx2]; cbn [outside] in Hx2; pose proof (PFS _ (conj Hx1 Hx2)) as HxS;
                                    split; [clear - HxS LOW LOR PCLO; lia| split; [clear - Hx2; tauto| exact I]]).
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
  eexists. split.
  - eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [| split; [assumption| assumption]]| split; assumption]|].
    + lazymatch goal with A : ART RT ?S ?mm, MUx : munch ?W ?mm ?mf, WMx : wmono asegs ?mm ?mf |- ART RT ?S ?mf =>
        apply (art_client_writes RT AF S mm mf (usp + -144) W A MUx WMx) end.
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
End BOXAD1.

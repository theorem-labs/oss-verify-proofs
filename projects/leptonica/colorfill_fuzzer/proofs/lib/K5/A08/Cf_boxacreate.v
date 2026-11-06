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
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Cf_iface CfX_kit.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma tr_boxacreate2 : In [0x8ed68] CLIENT_TRACES.
Proof. vm_compute. tauto. Qed.

Section BOXACREATE.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem boxaCreate_ok : boxaCreate_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n ras
    FDO MST -> -> NR UCTX TR0 EMP ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL, uctx in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_boxaCreate in *.
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
  assert (NLO : 1 <= n) by (clear - NR; lia). assert (NHI : n <= 20) by (clear - NR; lia).
  refresh RT AF. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 48, usp)] [0x5ec64].
  (* [comment removed for export] *)
  replace (bv_swrap 32 (n + 18446744073699551615)) with (n - 10000001)
    by (unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296; change (4294967296 / 2) with 2147483648; clear - NLO NHI; Z.div_mod_to_equations; lia).
  brfork HN.
  2:{ exfalso. clear - HN NLO NHI. Z.div_mod_to_equations. lia. }
  clear HN.
  cwalk [0x5ec64].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm))) _ =>
    assert (UW : unwind_okC mm (Z_to_bv 64 0x8ed04) s0 (Z_to_bv 64 (usp + -48))) end.
  { exists ras. split; [| rewrite unsigned_lit by (clear; lia); exact TR0].
    rewrite unsigned_lit by (clear - USP LOR STa; lia).
    destruct ras as [|ra1 ras'].
    - cbn [chain_ok] in *. unfold link_invalid in *. specialize (EMP eq_refl). clear - EMP UCTX LOR. lia.
    - cbn [chain_ok] in UCTX |- *. destruct UCTX as (U1 & U2 & U3 & U4 & fp1 & U5 & U6 & U7). unfold USTACK_TOP in *.
      split; [clear - U1; lia|]. split; [exact U2|]. split; [exact U3|]. split; [exact U4|]. exists fp1. split; [exact U5|]. split.
      + apply (rw_cells_agree_nw asegs m _ _ _ U6). eapply agree_sub; [exact AGF|]. cbv beta. intros xx Hxx.
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hxx. change (Z.of_nat 16) with 16 in Hxx. left. unfold USTACK_TOP. clear - Hxx U1 U3. lia.
      + eapply chain_ok_keep; [exact U7|]. eapply agree_sub; [exact AGF|]. cbv beta. intros xx Hxx. left. clear - Hxx U1. lia. }
  eapply cps_seq; [eapply (gp_calloc RT GP) with (lo := lo) (nmemb := 1) (size := 24); rt_side idtac |].
  all: lazymatch goal with
       | |- unwind_okC _ _ _ _ => exact UW
       | |- (_ <= CALLOC_MAX) => unfold CALLOC_MAX; lia
       | |- (Z.of_nat (length (rt_live _ _)) < LIVE_MAX) => clear - LVB; lia
       | |- _ => idtac
       end.
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  lazymatch goal with H : rw_cells asegs ?mm ?p [CB (Z.to_nat (1 * 24)) ?bs] |- _ =>
    pose proof (rw_cells_recell mm p [CB (Z.to_nat (1 * 24)) bs]
                  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0)] H
                  ltac:(cbn; tauto) eq_refl eq_refl) as BAC; clear H end.
  change (1 * 24) with 24 in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 24) :: _ |- _ => set (ba := p) in *; rename H into LV1 end.
  chunk_facts RT AF GP ba 24.
  assert (BA_AP : forall a, PF a -> a < ba \/ ba + 24 <= a).
  { intros a Ha. lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (ba, 24) :: _, FRS : rt_frames RT ?S = _, SP0 : rt_sp0 RT ?S = _ |- _ =>
      apply (new_chunk_apart RT AF S mm ba 24 _ _ usp a A L FRS ltac:(rewrite SP0; ul) Ha) end. }
  unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 48, usp); (ba, ba + 24)] [0x5ec64].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists ba, 24; split; [solve [in_live_tac]| lia]| exact I]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (BA_AP _ Hx); split; [lia| split; [lia| exact I]]).
  eapply cps_seq; [eapply (gp_calloc RT GP) with (lo := lo) (nmemb := n) (size := 8); rt_side idtac |].
  all: lazymatch goal with
       | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_boxacreate2| left; ul]
       | |- (_ <= CALLOC_MAX) => unfold CALLOC_MAX; lia
       | |- (Z.of_nat (length (rt_live _ _)) < LIVE_MAX) => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length]; clear - LVB; lia
       | |- _ => idtac
       end.
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  lazymatch goal with H : rt_live RT ?S = (?p, n * 8) :: _ |- _ => set (arr := p) in *; rename H into LV2 end.
  chunk_facts RT AF GP arr (n * 8).
  assert (ARR_AP : forall a, PF a -> a < arr \/ arr + n * 8 <= a).
  { intros a Ha. lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (arr, n * 8) :: _, FRS : rt_frames RT ?S = _, SP0 : rt_sp0 RT ?S = _ |- _ =>
      apply (new_chunk_apart RT AF S mm arr (n * 8) _ _ usp a A L FRS ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul)) end.
    apply (aclient_mono _ _ usp _ _ _ _ Ha); [solve [live_add_tac]| solve [frames_sub_tac]| lia]. }
  assert (DAB : arr + n * 8 <= ba \/ ba + 24 <= arr).
  { lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (arr, n * 8) :: _ |- _ =>
      apply (af_live_disj RT AF S mm arr (n * 8) ba 24 [] _ A L); cbn [app]; solve [in_live_tac] end. }
  unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 48, usp); (ba, ba + 24)] (@nil Z).
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists ba, 24; split; [solve [in_live_tac]| lia]| exact I]]).
  lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (BA_AP _ Hx); split; [lia| split; [lia| exact I]]) end.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, ba, arr end.
  split.
  2:{ repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end. repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end. rewrite LV2, LV1. repeat split; reflexivity. }
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
  { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
  split; [intros a Ha _; apply AGF; exact Ha|].
  unfold boxa_new, boxa_empty, boxa_cells, chunk.
  split.
  - split; [eexists; exact BAC|]. 
    split; [split; [rewrite LV2, LV1; right; left; reflexivity| repeat split; first [assumption | lia]]|].
    split; [split; [rewrite LV2; left; f_equal; lia| repeat split; first [assumption | lia]]|].
    split; [lia|]. unfold parked in DAB. clear - DAB NLO. lia.
  - lazymatch goal with H : rw_cells asegs _ arr _ |- _ => exact H end.
Qed.
End BOXACREATE.

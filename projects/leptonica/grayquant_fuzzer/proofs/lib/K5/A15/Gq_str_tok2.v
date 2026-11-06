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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Image.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit D_iface D_defs
  Gq_numa Gq_gaps Gq_iface Gq_thr_iface Gq_parse_kit Gq_parse_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section STRTOK.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GG : gq_gaps RT.

Theorem strtokSafe_2_ok : strtokSafe_gq_cps RT false 6 3 10 [49; 49; 53].
Proof using AF GP GG.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ns tl w0
    FDO MST -> -> -> -> INS NSC OP TLC ENV RES.
  cbv iota in TLC |- *.
  unfold lpost, lenv, lres, keeps, keepsL, optrF in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct OP as (OWNF & TL0 & TL8 & TLH & TLS).
  pose proof OWNF as (ff & kf & FIN & F1 & F2 & F8 & F0 & FT & FB).
  assert (OWN0 : accok (rt_live RT Σ) (rt_frames RT Σ) m tl 8) by (right; exact OWNF).
  pose proof OWN0 as OWN. hide OWN0. hide FB. hide OWNF.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_strtokSafe, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(tl, tl + 8)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof (af_live_range RT AF Σ m ns 14 ART0 INS) as (NS0 & NSHI & NSSEG).
  pose proof (gp_live_hi RT GP Σ m ns 14 ART0 INS) as NSSH.
  assert (TLLO : tl + 8 <= lo).
  { pose proof (af_frames_range RT AF Σ m ff kf ART0 FIN) as (_ & R & _).
    unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. lia. }
  assert (TLNS : tl + 8 <= ns \/ ns + 14 <= tl).
  { pose proof (af_frames_range RT AF Σ m ff kf ART0 FIN) as (_ & _ & _ & D).
    specialize (D ns 14 INS). clear - D F1 F2. lia. }
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  assert (NSR : 0 < ns /\ ns + 14 < 2^47) by (clear - NS0 NSHI SP0R; lia).
  destruct NSR as [NSR0 NSR1].
  assert (TLR : 0 < tl /\ tl + 8 < 2^47) by (clear - TL0 TLLO LOR SPT; lia).
  destruct TLR as [_ TLR1].
  unfold LIT_SEPS, LIT_EDGEVALS in *. cbn [str_cells EDGE_STR app map] in NSC.
  refresh RT AF. unfold shad, SHB in *.
  tok_stops ltac:(fun stops =>
    walk_to AF MST [(usp - 96, usp); (tl, tl + 8)] stops; pwalk stops;
    schrs RT AF GP GG MST lo usp tl ff kf PFS stops).
  (* [comment removed for export] *)
  at_call RT AF ltac:(tok_ivt tl) ltac:(fun Hx => tok_pft PFS Hx).
  assert (TRC : In [0x9143c] CLIENT_TRACES) by (apply ct_mem_In; vm_compute; reflexivity).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 4) (size := 1); rt_side idtac.
    - unfold CALLOC_MAX; lia.
    - apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact TRC| left; lia]. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx Ho]; apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  change (4 * 1) with 4 in *. change (Z.to_nat 4) with 4%nat in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 4) :: _ |- _ => rename H into LVA; rename S into Σ1; rename p into sub end.
  assert (INA : In (sub, 4) (rt_live RT Σ1)) by (rewrite LVA; left; reflexivity).
  assert (INS1 : In (ns, 14) (rt_live RT Σ1)) by (rewrite LVA; right; exact INS).
  lazymatch goal with H : rt_frames RT Σ1 = rt_frames RT Σ |- _ => rename H into FRA end.
  lazymatch goal with A : ART RT Σ1 ?mm |- cps _ (ASTA RT Σ1 _ _) _ =>
    pose proof (af_live_range RT AF Σ1 mm sub 4 A INA) as (_ & PAHI & PASEG);
    pose proof (gp_live_hi RT GP Σ1 mm sub 4 A INA) as PASH;
    assert (NCA : forall a, PF a -> a < sub \/ sub + 4 <= a)
      by (intros a [Ha _]; apply (new_chunk_apart RT AF Σ1 mm sub 4 (rt_live RT Σ) (rt_frames RT Σ) usp a A LVA);
          [ assumption | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]);
    assert (SUBNS : sub + 4 <= ns \/ ns + 14 <= sub)
      by (pose proof (af_live_disj RT AF Σ1 mm sub 4 ns 14 [] (rt_live RT Σ) A LVA ltac:(cbn [app]; exact INS)) as X; clear - X; lia);
    assert (SUBTL : tl + 8 <= sub \/ sub + 4 <= tl)
      by (pose proof (af_frames_range RT AF Σ1 mm ff kf A ltac:(rewrite FRA; exact FIN)) as (_ & _ & _ & D);
          specialize (D sub 4 INA); clear - D F1 F2; lia) end.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  assert (SUBR0 : 0 < sub) by assumption.
  assert (SUBR1 : sub + 4 < 2^47) by (clear - PAHI SP0R1; lia).
  own_cur RT tl ff kf.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  (* [comment removed for export] *)
  tok_stops ltac:(fun stops =>
    walk_to AF MST [(usp - 96, usp); (tl, tl + 8); (sub, sub + 4)] stops; pwalk stops;
    schrs RT AF GP GG MST lo usp tl ff kf PFS stops).
  cps_stop.
  art_now RT AF ltac:(tok_ivt tl).
  lazymatch goal with
  | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => tok_pft PFS Hx)
  end.
  lazymatch goal with H : rw_cells asegs ?mm sub ?cs |- _ =>
    assert (SUBC : rw_cells asegs mm sub (str_cells ([49; 49; 53] ++ [0])))
      by (apply (rw_cells_recell mm sub cs _ H); [clear; cbn; tauto | vm_compute; reflexivity | vm_compute; reflexivity]) end.
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  exists Σ1, sub.
  split; [| rewrite LVA; repeat split; first [assumption | reflexivity | lia]].
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [exact WM | assumption]]]| split; assumption]|].
  split; [intros a Ha Ho; apply AGF; split; [exact Ha | exact Ho]|].
  split; [exact SUBC | exact TLC].
Qed.
End STRTOK.

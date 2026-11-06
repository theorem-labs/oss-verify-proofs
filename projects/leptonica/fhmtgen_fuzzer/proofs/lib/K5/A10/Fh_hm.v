(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Gm_iface Fh_iface Fh_sel_iface Fh_statics Fh_selkit Fh_hm_defs
  Fh_hm_s0 Fh_hm_s1 Fh_hm_s2 Fh_hm_s3 Fh_hm_s4 Fh_hm_s5 Fh_hm_s6 Fh_hm_s7 Fh_hm_s8 Fh_hm_s9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section HM.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis CRT : selaCreate_cps RT.
Hypothesis BRK : selCreateBrick_cps RT.
Hypothesis SET : selSetElement_cps RT.
Hypothesis ADD : selaAddSel_cps RT.

Theorem selaAddHitMiss_ok : selaAddHitMiss_cps RT.
Proof using AF GP CRT BRK SET ADD.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST -> -> ENV RES.
  pose proof ENV as ENV0. pose proof RES as RES0.
  unfold lpost, lenv, lres, keeps, keepsL in ENV, RES |- *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_selaAddHitMiss, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  walk_to AF MST [(usp - 32, usp)] [e_selaCreate].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { eapply CRT with (lo := lo); rt_side idtac.
    all: lazymatch goal with
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; exact He| intros e He; exact He| lia]| exact I]).
  lazymatch goal with H : sela_obj (rt_live RT ?S) _ ?p ?q [] |- _ => rename H into SAO; rename S into Σ1; rename p into sela; rename q into arr end.
  lazymatch goal with H : rt_live RT Σ1 = _ |- _ => rename H into LV1 end.
  pose proof SAO as (_ & (SAIN & SA0 & _) & (ARIN & AR0 & _) & _).
  lazymatch goal with A : ART RT Σ1 ?mm |- cps _ (ASTA RT Σ1 _ _) _ =>
    assert (NCSA : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> (a < sela \/ sela + 16 <= a) /\ (a < arr \/ arr + 400 <= a))
      by (intros a Ha; split;
          [ apply (new_chunks_apart RT AF Σ1 mm _ (rt_live RT Σ) (rt_frames RT Σ) usp A LV1 ltac:(assumption)
                     ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul) sela 16 a ltac:(right; left; reflexivity) Ha)
          | apply (new_chunks_apart RT AF Σ1 mm _ (rt_live RT Σ) (rt_frames RT Σ) usp A LV1 ltac:(assumption)
                     ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul) arr 400 a ltac:(left; reflexivity) Ha) ]) end.
  chunk_facts RT AF GP sela 16.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  refresh RT AF. unfold SHB in *.
  walk_to AF MST [(usp - 32, usp)] [0xa89c8].
  cps_stop.
  lazymatch goal with FRx : rw_cells asegs _ (usp + -32) [CB 8 ?f; _; _; _] |- _ => set (fj := f) in * end.
  assert (CTX : hm_ctx RT Σ m sp lo sela arr) by (split; [exact ENV0| split; [exact RES0| exact NCSA]]).
  (* [comment removed for export] *)
  assert (K10 : hm_cont RT PMc QF Σ m usp lo fj s1 s0 ra sela arr gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 0xa901c 10).
  { clear AGF SAO LV1. 
    repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : munch _ _ _ |- _ => clear H end.
    repeat match goal with H : acc asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : ART RT _ _ |- _ => lazymatch type of H with ART RT Σ m => fail | _ => clear H end end.
    repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
    repeat match goal with H : mem_inv asegs _ |- _ => clear H end.
    repeat match goal with H : stk asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : LIBH _ |- _ => clear H end.
    repeat match goal with H : io_ssp _ |- _ => clear H end.
    intros Σk mc sels ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc'
      (ARTk & MIk & STk & LHk & SSPk & AGF0 & WMk & FRc & SAOk & UPTO & LVK & LENK & POSK & FRK & SPK & CRK).
    unfold hm_state.
    refresh RT AF. unfold SHB in *.
    walk_to AF MST [(usp - 32, usp)] (@nil Z).
    cps_stop.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    exists Σk, sela, arr, sels.
    split; [| split; [exact (hm_sels_upto_10 sels UPTO)| split; [exact LVK| split; [exact FRK| split; [exact SPK| exact CRK]]]]].
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [assumption| assumption]]]| split; assumption]|].
    split; [intros a Ha _; apply AGF0; exact Ha| exact SAOk]. }
  pose proof (hm_seg9 RT AF GP BRK SET ADD Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo fj sela arr QF FDO MST CTX K10) as K9.
  pose proof (hm_seg8 RT AF GP BRK SET ADD Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo fj sela arr QF FDO MST CTX K9) as K8.
  pose proof (hm_seg7 RT AF GP BRK SET ADD Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo fj sela arr QF FDO MST CTX K8) as K7.
  pose proof (hm_seg6 RT AF GP BRK SET ADD Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo fj sela arr QF FDO MST CTX K7) as K6.
  pose proof (hm_seg5 RT AF GP BRK SET ADD Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo fj sela arr QF FDO MST CTX K6) as K5.
  pose proof (hm_seg4 RT AF GP BRK SET ADD Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo fj sela arr QF FDO MST CTX K5) as K4.
  pose proof (hm_seg3 RT AF GP BRK SET ADD Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo fj sela arr QF FDO MST CTX K4) as K3.
  pose proof (hm_seg2 RT AF GP BRK SET ADD Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo fj sela arr QF FDO MST CTX K3) as K2.
  pose proof (hm_seg1 RT AF GP BRK SET ADD Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo fj sela arr QF FDO MST CTX K2) as K1.
  pose proof (hm_seg0 RT AF GP BRK SET ADD Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo fj sela arr QF FDO MST CTX K1) as K0.
  clear K1 K2 K3 K4 K5 K6 K7 K8 K9 K10.
  unfold hm_cont, hm_state in K0. fold usp in K0.
  eapply K0.
  unfold hm_inv.
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact AGF|]. split; [assumption|]. split; [exact FR|]. split; [exact SAO|].
  split. { split; [reflexivity| intros j Hj; lia]. }
  split; [exact LV1|].
  split. { rewrite LV1. unfold sela_live. cbn [rev flat_map app length]. change (hm_count 0) with 2. rewrite !Nat2Z.inj_succ. lia. }
  split. { intros p n Hp. rewrite LV1 in Hp. destruct Hp as [E|[E|Hp]]; [injection E as _ <-; lia| injection E as _ <-; lia| exact (LVP p n Hp)]. }
  split; [assumption|]. split; assumption.
Qed.
End HM.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Lept_chain Gm_iface Gm_livekit Gm_livekit2 Fh_iface Fh_addb1_defs LeptB_guard LeptB_guard2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section ADDB1W.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem pixAddBorder1_of_general : pixAddBorder1_cps RT e_pixAddBorderGeneral -> pixAddBorder1_cps RT e_pixAddBorder.
Proof using AF GP.
  intros GEN Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    pixs vs cvs ras FDO MST -> -> ARGS POBJ D1 VDATA TRC ENV RES.
  destruct ARGS as [(E & _)|(_ & -> & ->)]; [exfalso; unfold e_pixAddBorderGeneral, e_pixAddBorder in E; lia|].
  pose proof ENV as ENV0. pose proof RES as RES0.
  unfold lpost, lenv, keeps, keepsL, lres in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & _).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixAddBorder, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF0 := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF0 m) as AGF.
  assert (PFS : forall a, PF0 a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (CMIN : p_cmap vs <> 0 -> In (p_cmap vs, 24) (rt_live RT Σ)).
  { intros NZ. destruct POBJ as (_ & _ & _ & _ & [Z0|((_ & (CI & _) & _) & _)]); [contradiction| exact CI]. }
  chunk_facts RT AF GP pixs 64.
  unfold pix_cells in PXC.
  hide POBJ.
  lib_refresh RT GP.
  carve_frame 16%nat ST.
  walk_to AF MST [(usp - 16, usp)] [e_pixAddBorderGeneral].
  cwalk [e_pixAddBorderGeneral].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; clear - P LOR; split; [lia| exact I]).
  eapply cps_seq.
  { eapply GEN with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs) (ras := ras); rt_side idtac;
      lazymatch goal with
      | |- addborder1_args _ _ _ _ _ _ => left; repeat split; reflexivity
      | |- pix_obj _ ?mc pixs _ _ =>
          unfold hid in POBJ; apply (pix_obj_agree_cm (rt_live RT Σ) PF0 m mc pixs vs cvs POBJ AGF);
          [intros NZ a Ha; right; right; left; exists (p_cmap vs), 24; split; [exact (CMIN NZ)| exact Ha] | unfold pix_cells; exact PXC]
      | |- p_d vs = 1 => exact D1
      | |- p_data vs <> 0 => exact VDATA
      | |- p_cmap vs <> 0 -> _ =>
          let NZ := fresh "NZ" in intros NZ; destruct (TRC NZ) as (UCTX & TIN); split;
          [ unfold uctx in UCTX |- *; rewrite ?unsigned_lit by ul; rewrite ?Z_to_bv_bv_unsigned;
            eapply chain_ok_keep; [exact UCTX|]; eapply agree_sub; [exact AGF|]; cbv beta; intros xx Hxx; left; exact Hxx
          | rewrite ?Z_to_bv_bv_unsigned; exact TIN ]
      | |- lenv _ _ _ _ _ _ => lenv_tac
      | |- lres _ _ _ _ _ => lres_tac
      | |- ?g => idtac "LEFTOVER:" g
      end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
  lazymatch goal with H : new_pix1 RT _ _ _ ?r _ _ ?v ?cv |- _ => exists r, v, cv; rename H into NP end.
  split; [| split; [assumption| split; [alg_tac| split; [alg_tac| ]]]].
  2:{ repeat match goal with H : rt_credit RT _ = _ |- _ => revert H end; repeat match goal with H : _ <= rt_credit RT _ |- _ => revert H end; clear; intros; lia. }
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split.
  { split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption].
    repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
  split; [| exact NP].
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
  intros a Ha Ho; exact (AGF a Ha).
Qed.
End ADDB1W.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section ERR.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis STDERR : lept_stderr_cps RT.

Lemma fmt_err_in : In (0x2dca0, [true; true]) LEPT_FMTS.
Proof. unfold LEPT_FMTS. left. reflexivity. Qed.

Lemma returnError_ok : forall entry, entry = e_returnErrorInt \/ entry = e_returnErrorPtr -> returnError_cps RT entry.
Proof using AF GP STDERR.
  intros entry HE Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST -> L0 L1 ENV FRB CRB.
  unfold lpost, lenv in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_returnErrorInt, e_returnErrorPtr in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold STDERR_STACK, LSTK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  carve_frame 16%nat ST.
  destruct HE as [-> | ->].
  all: walk_to AF MST [(usp - 16, usp)] [0xe757c].
  all: at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                     ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  all: (eapply cps_seq; [eapply STDERR with (lo := lo) (fmt := 0x2dca0) (kinds := [true; true]); rt_side idtac |]).
  all: lazymatch goal with
       | |- lept_args_lit _ _ => cbn [lept_args_lit]; split; [assumption| split; [assumption| exact I]]
       | |- (_ <= _) => unfold STDERR_STACK, RT_STACK; lia
       | |- _ => idtac
       end.
  all: after_call RT AF.
  all: fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  all: refresh RT AF.
  all: walk_to AF MST [(usp - 16, usp)] (@nil Z).
  all: try (lazymatch goal with ST' : stk asegs _ _ (_ + -16) |- _ => release_frame FR ST' usp end).
  all: cps_stop.
  all: lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mf _))) _ =>
      lazymatch goal with A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf |- _ =>
        assert (ARTf : ART RT S mf)
          by (apply (art_client_writes RT AF S mm mf (usp + -16) W A MUx WMx);
              [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
              | cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I] ]);
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
      end end.
  all: apply cps_finish; intros c Hc; subst QF; cbv beta.
  all: lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
  all: split.
  all: try (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
      repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
      repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end;
      repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; solve [auto]).
  all: (eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists).
  all: (split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|]).
  all: unfold lpost, rt_after.
  all: (split; [split; [split; [exact ARTf | split; [ | split]] | split] | ]).
  all: try assumption.
  all: try (intros a Ha; exact (AGF a Ha)).
Qed.
End ERR.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib SegsS0 StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel BzTac BzDefs BzInv BzTables BzContracts BzContracts0 BzWalkArith S0_bzd_out S0_bzd_loop1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require JunkFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia RelLiaR.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0_bzd_entry.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_bzd_out OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_bzd_loop1.
 Unset Lia Cache.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.

Local Ltac BzTac.bz32 ::= JunkFast.bz32_j.
Local Ltac BzTac2.bz32l ::= JunkFast.bz32l_j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac lia ::= RelLia.lia_rf3.
Local Ltac StoreFast.tlia ::= RelLiaR.tlia_rr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.


Section BZD.
  Variable z : bzdctx.
  Hypothesis ZOK : bzdctx_ok z.
  Notation cx := (z_cx z).
  Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)). Notation usp := (bv_unsigned (z_sp z)).

  Theorem S0_bzd_entry : bzd_entry_spec z.
  Proof.
    unfold bzd_entry_spec. intros until b. intros HD Hstrm Hst SM HbS IM ST MI.
    cps_destruct IM as (GOT & SV & RNA & CRC).
    pose proof ZOK as Z'. cps_destruct Z' as (CX & USP & LO1 & LO2 & FJL & PAYL & SPI & SPI2).
    pose proof (proj1 CX) as CL. unfold ctx_lin in CL. cbv zeta in CL.
    cps_destruct CL as (LS1 & LS2 & LR1 & LR2 & LR3 & LR4 & LD1 & LD2 & LD3 & LD4 & LP1 & LP2 & _ & LSTRM & _).
    pose proof (proj2 (proj2 CX)) as CS. unfold ctx_sep, disj in CS. cbv zeta in CS.
    cps_destruct CS as (_ & _ & _ & _ & _ & _ & _ & IA1 & _). unfold img_apart, IHI in IA1.
    bz_ceil; unfold DSTATE_SIZE, CEILING, STACK_TOP, IMG_HI_MAX, D14 in *.
    pose proof (word_urange (z_sp z)) as USPR.
    pose proof crc_words_length as CWL. pose proof rnums_words_length as RNL.
    pose proof (munch_refl ([(usp - 112, usp)])%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    carve_frame 112%nat ST.
    wstep.
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    wstep. wstep.
    wstep. first [ if_cases K1; zify_cond K1; [exfalso; lia|] | if_cases K1; zify_cond K1; [|exfalso; lia] | idtac ].
    wstep. rewrite HbS.
    wstep. first [ if_cases K2; zify_cond K2; [exfalso; lia|] | if_cases K2; zify_cond K2; [|exfalso; lia] | idtac ].
    wstep. rewrite Hstrm.
    wstep. first [ if_cases K3; zify_cond K3; [exfalso; lia|] | if_cases K3; zify_cond K3; [|exfalso; lia] | idtac ].
    wstep. wstep. wstep. wstep.
    wstep. rewrite ?sx32_lit by lia. rewrite Hst.
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    wstep. if_false. wstep. if_false. wstep. if_false.
    wstep. wstep. wstep.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) =>
      pose proof (proj1 (proj1 FR)) as WF; cbn [cells_wf] in WF; destruct WF as [LJ _];
      apply evt_done; unfold bzd_entry_post; hnf;
      do 15 eexists; exists j end.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact FR|]. split; [exact LJ|]. split; [exact ST|].
    split; [exact HD|]. split; [exact SM|]. unfold IMGC. split; [exact GOT|]. split; [exact SV|]. split; [exact RNA| exact CRC].
  Qed.
End BZD.

End ACeilS1.
End S0_bzd_entry.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzContracts BzContracts0 DecCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDOKp DecCutF S0F_bzd_loop1 S0F_dec_U0F.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_loop1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_dec_U0F.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacF.

Section ACeilS1. Context {ACEIL__ : ACeil}.

Theorem S0F_dec14F_spec : dec14F_spec DI_S0.
Proof.
  unfold dec14F_spec. intros A J d s t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 AF.
  apply (S0F_dec14F A J d s t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6). exact AF.
Qed.

End ACeilS1.

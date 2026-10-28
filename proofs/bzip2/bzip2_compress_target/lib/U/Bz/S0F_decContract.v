(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzDefs BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 BzWalkArith S0_bzd_out S0_bzd_loop1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require JunkFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require RelLiaR.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0_bzd_entry.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_bzd_loop1.
 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
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
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
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
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

Lemma rw_cells_C8_CB8 : forall m A v post,
  rw_cells s0segs m A (C8 v :: post) -> rw_cells s0segs m A (CB 8 (le8 v) :: post).
Proof.
  intros m A v post [[Hwf Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf] in Hwf |- *. split; [apply length_le8| exact (proj2 Hwf)].
  - exact Hb.
  - exact Hw.
Qed.
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
    pose proof (proj1 (proj2 CX)) as AL. unfold ctx_al in AL. destruct AL as (ALS & ALP & _).
    assert (LE7S : Z.land S 7 = 0%Z).
    { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3)%Z with 8%Z.
      rewrite <- (Z.mod_mod_divide S 16 8) by (exists 2%Z; reflexivity). rewrite ALS. reflexivity. }
    assert (LE7T : Z.land STRM 7 = 0%Z).
    { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3)%Z with 8%Z. rewrite LSTRM.
      rewrite <- (Z.mod_mod_divide (b_sp (z_cx z)) 16 8) by (exists 2%Z; reflexivity). rewrite ALP. reflexivity. }
    pose proof (proj2 (proj2 CX)) as CS. unfold ctx_sep, disj in CS. cbv zeta in CS.
    cps_destruct CS as (_ & _ & _ & _ & _ & _ & _ & IA1 & _). unfold img_apart, IHI in IA1.
    bz_ceil; unfold DSTATE_SIZE, CEILING, STACK_TOP, IMG_HI_MAX, D14 in *.
    pose proof (word_urange (z_sp z)) as USPR.
    pose proof crc_words_length as CWL. pose proof rnums_words_length as RNL.
    pose proof (munch_refl ([(usp - 112, usp)])%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    carve_frame 112%nat ST.
    wstep.
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    wstep.
    wstep. first [ if_cases K1; zify_cond K1; [exfalso; lia|] | if_cases K1; zify_cond K1; [|exfalso; lia] | idtac ].
    wstep. rewrite ?LE7T. wstep; try notrap.
    wstep. rewrite HbS.
    wstep. first [ if_cases K2; zify_cond K2; [exfalso; lia|] | if_cases K2; zify_cond K2; [|exfalso; lia] | idtac ].
    wstep. rewrite ?LE7S. wstep; try notrap.
    wstep. rewrite Hstrm.
    wstep. first [ if_cases K3; zify_cond K3; [exfalso; lia|] | if_cases K3; zify_cond K3; [|exfalso; lia] | idtac ].
    wstep. wstep. wstep. wstep.
    wstep. rewrite ?sx32_lit by lia. rewrite Hst.
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    wstep; try notrap. wstep; try notrap. wstep; try notrap.
    wstep. wstep.
    lazymatch type of FR with rw_cells _ _ _ (C8 ?v :: _) =>
      apply rw_cells_C8_CB8 in FR;
      apply evt_done; unfold bzd_entry_post; hnf;
      do 15 eexists; exists (le8 v) end.
    split; [first [reflexivity | st_eq]|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact FR|]. split; [apply length_le8|]. split; [exact ST|].
    split; [exact HD|]. split; [exact SM|]. unfold IMGC. split; [exact GOT|]. split; [exact SV|]. split; [exact RNA| exact CRC].
  Qed.
End BZD.

End ACeilS1.
End S0_bzd_entry.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs BzContracts BzContracts0 DecCut.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDOKp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF S0F_bzd_loop1 S0F_dec_U0F.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_loop1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U0F.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.

Section ACeilS1. Context {ACEIL__ : ACeil}.

Theorem S0F_dec14F_spec : dec14F_spec DI_S0.
Proof.
  unfold dec14F_spec. intros A J d s t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 AF.
  apply (S0F_dec14F A J d s t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6). exact AF.
Qed.

End ACeilS1.

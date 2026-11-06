(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib Arr Frame. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzDefs. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2 BzInv. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzLemmasMtf. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCut DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecAuxM DecTac DecTac2 DecTacM BzWalkArith3 S0_dec_U13 S0_decCuts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_decCuts7.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_decCuts7.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac.DecAuxB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAuxM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCuts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCuts7.S0_decCutsB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCuts7.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Musl Require Import S0_memset.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFastM.
Local Ltac DecTacM.revive_f H MUL WML AOK ::= DecFastM.revive_f_fast H MUL WML AOK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require RelLiaR.
Local Ltac lia ::= RelLia.lia_rf3.
Local Ltac StoreFast.tlia ::= RelLiaR.tlia_rr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma addiw_m1 : forall x, (-1 <= x <= 2147483646)%Z ->
  bv_swrap 32 (Z.land x 18446744073709551615 + 1) = (x + 1)%Z.
Proof.
  intros x Hx. destruct (Z.eq_dec x (-1)) as [->|NE].
  - vm_compute. reflexivity.
  - rewrite (land64_small x) by lia. rewrite swrap32_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)

End ACeilS1.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxMemSound FxValSound FxStepSound FxStepMain FxRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition agree (n : int) (rho rho' : int -> word) : Prop :=
  rho' 0%uint63 = Z_to_bv 64 0 /\ forall t, to_Z t < to_Z n -> rho' t = rho t.

Definition rho_upd (rho : int -> word) (t : int) (a : word) : int -> word :=
  fun t' => if (t' =? t)%uint63 then a else rho t'.

Section Rn.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Variable RO : itrie unit.
Hypothesis Hcode : code_ok segs code.

Definition Rn (n : int) (rho : int -> word) (F : fstate) (ms : machine_state) : Prop :=
  forall rho', agree n rho rho' -> R segs IM rho' F ms.

Theorem fx_run_Rn : forall n rho bp k F F' r cnt ms,
  (k <= 61)%nat ->
  fx_run IM code RO bp k F = (F', r, cnt) ->
  rho 0%uint63 = Z_to_bv 64 0 ->
  Rn n rho F ms ->
  exists ms', rsteps segs (nat_of_int cnt) ms = MachineOk ms'
    /\ Rn n rho F' ms'
    /\ (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms'))
    /\ (forall x, ~ claimed_wr IM rho (f_mem F) x -> ms_mem ms' x = ms_mem ms x)
    /\ (forall x, claimed_wr IM rho (f_mem F') x -> claimed_wr IM rho (f_mem F) x)
    /\ ms_rom ms' = ms_rom ms.
Proof.
  intros n rho bp k F F' r cnt ms Hk Hrun Hrho0 HRn.
  assert (Hag : agree n rho rho) by (split; [exact Hrho0 | intros; reflexivity]).
  destruct (fx_run_sound_frame segs IM rho Hrho0 code RO Hcode bp k F F' r cnt Hk Hrun)
    as (_ & Hmono & Hrun_rho).
  destruct (Hrun_rho ms (HRn rho Hag)) as (ms' & Hsteps & HR' & Hec & Hfr & Hrom).
  exists ms'. split; [exact Hsteps|]. split.
  - (* [comment removed for export] *)
    intros rho' Hag'. pose proof (proj1 Hag') as H0'.
    destruct (fx_run_sound_frame segs IM rho' H0' code RO Hcode bp k F F' r cnt Hk Hrun)
      as (_ & _ & Hrun').
    destruct (Hrun' ms (HRn rho' Hag')) as (ms'' & Hsteps' & HR'' & _).
    rewrite Hsteps in Hsteps'. injection Hsteps' as <-. exact HR''.
  - split; [exact Hec|]. split; [exact Hfr|]. split; [exact Hmono | exact Hrom].
Qed.

(* [comment removed for export] *)
Theorem fx_run_Rn_shape : forall n rho bp k F F' r cnt ms ms',
  (k <= 61)%nat ->
  fx_run IM code RO bp k F = (F', r, cnt) ->
  rho 0%uint63 = Z_to_bv 64 0 ->
  Rn n rho F ms ->
  rsteps segs (nat_of_int cnt) ms = MachineOk ms' ->
  ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms.
Proof.
  intros n rho bp k F F' r cnt ms ms' Hk Hrun Hrho0 HRn Hsteps.
  assert (Hag : agree n rho rho) by (split; [exact Hrho0 | intros; reflexivity]).
  destruct (fx_run_sound_shape segs IM rho Hrho0 code RO Hcode bp k F F' r cnt Hk Hrun ms (HRn rho Hag))
    as (ms'' & Hsteps' & _ & Hfr & Hfc).
  rewrite Hsteps in Hsteps'. injection Hsteps' as <-. split; assumption.
Qed.
End Rn.

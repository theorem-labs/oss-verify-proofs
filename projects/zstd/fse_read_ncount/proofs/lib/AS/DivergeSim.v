(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import PropExec.
Import ListNotations.
Open Scope bv_scope.
Section WithFP1.
Context {fx : FPState}.
#[using="Type"] Lemma is_prefix_app_mono {A} : forall (e a b : list A),
is_prefix a b -> is_prefix (e ++ a) (e ++ b).
Proof. induction e; cbn; auto. Qed.
Section WithSegs.
Variable segs : list Segment.
Definition silent_loop (P : config -> Prop) : Prop :=
forall c, P c ->
m_halted (cfg_model c) = None /\
ms_svc_pending (cfg_ms c) = None /\
exists ms' model',
mi_account_step segs (cfg_ms c) (cfg_model c) = MachineOk (ms', model') /\
P (mkCfg ms' model').
Inductive to_spin : machine_state -> Model -> Prop :=
| ts_spin : forall ms model,
ms_svc_pending ms = None ->
mi_account_step segs ms model = MachineOk (ms, model) ->
to_spin ms model
| ts_step : forall ms model ms' model',
ms_svc_pending ms = None ->
mi_account_step segs ms model = MachineOk (ms', model') ->
to_spin ms' model' ->
to_spin ms model.
End WithSegs.
End WithFP1.
Section WithFP2.
Context {fx : FPState}.
Section TwoBranchToy.
Variable segs : list Segment.
Variable c0 : config.
Variable evs_g : list event.
Variable c_g c_r : config.
Variable T : list event.
Variable P : config -> Prop.
Hypothesis Hsplit : forall evs to, sstep segs c0 evs to ->
(evs = evs_g /\ to = SNext c_g) \/ (evs = [] /\ to = SNext c_r).
Hypothesis Hstep_g : sstep segs c0 evs_g (SNext c_g).
Hypothesis Hg_obs : forall tr, obs_trace segs c_g tr <-> is_prefix tr T.
Hypothesis Hg_noerr : ~ reaches_error segs c_g.
Hypothesis Hloop : silent_loop segs P.
Hypothesis HP_r : P c_r.
End TwoBranchToy.
End WithFP2.
Module SelfJumpImage.
End SelfJumpImage.

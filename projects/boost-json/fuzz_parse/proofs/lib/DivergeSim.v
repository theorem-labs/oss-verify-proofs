(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem3Run06config3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsj4dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem5Statenb5Model37Corelib7Numbers7BinNumsr14Npos35stdpp9bitvectorbdefinitionst12bv37Corelib4Init5Logicv33andv32eq37Corelib4Init9Datatypeshh24Nonehh26optionhh24prodv32ex09cfg_model06cfg_mshh24pairj49MachineOkj4emachine_resultj4ems_svc_pending0fmi_account_step05mkCfgnb8m_haltedhh24list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehrd7Segment" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

Lemma is_prefix_app_mono {A} : forall (e a b : list A),
  is_prefix a b -> is_prefix (e ++ a) (e ++ b).
Proof. induction e; cbn; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End FPX1.

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!hr5!hv2@1$0$1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition silent_loop : ltac2:(zQ "10!ic>1P>0$0PP") := ltac2:(zQ "h40!mb!q9!sa!ue!hg7!hgd!hia!hj2!hjc!hk4!hk9!hl4!ic!hlc!hm4!hn0!ho1!hp2!hq3!hqa\1P>0$cP>1c$c>0@1^2^1@2$4@3$5@1$7@1$3@1$2#k0@1$h3@1$a^2@1$6@1$3@1$2#k0@2$4@3$5@1$7@1$3@1$2#k0@1$h0@1$b^2@1$6@1$3@1$2#k0@2$9$0\3ms'$0@2$9$1\6model'$1@2$4@3$5@1$f@2$8$0$1@3$h1?4segs@1$b^4@1$a^4@2$e@2$8$0$1@4$d$0$1^2^1@1^5@2$h2^2^1").

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section TwoBranchToy.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Module SelfJumpImage.

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)
End FPX2.

End SelfJumpImage.
(* [comment removed for export] *)

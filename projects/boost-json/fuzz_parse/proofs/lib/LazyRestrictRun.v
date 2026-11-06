(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import CatSim LazyRestrict.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemantics0dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem5Statek65Model37Corelib7Numbers7BinNumsnc4Npos35stdpp9bitvectorbdefinitionspc2bv37Corelib4Init5Logicre2eq37Corelib4Init9Datatypest74Nonet76optiont74prod3h5LinuxProcessSemanticsfLinuxProcessSem3Runhg65mkCfg79OSSVerify6Proofsaboost_jsonafuzz_parse3libfLazyRestrictRun8WithSegs~~~~~~hjb6dstepst74pair09MachineOk0emachine_result0ems_svc_pendinghg66confighg6fmi_account_stepk68m_haltedre3and69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~hv08lazy_invt74boolt74truere2ex06ms_mem04stephv07hiddenbhv08restricthv0h5same_but_materializedhv0dunrestrict_to69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~ipe6mstepst74list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeiu87Segmenthv0flazy_ranges_okb" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : ltac2:(zQ "20!iu1!jhd@1$0$1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive dsteps : config -> config -> Prop :=
| ds_refl : forall c, dsteps c c
| ds_step : forall ms model ms' model' c3,
    m_halted model = None ->
    ms_svc_pending ms = None ->
    mi_account_step segs ms model = MachineOk (ms', model') ->
    dsteps (mkCfg ms' model') c3 ->
    dsteps (mkCfg ms model) c3.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma dsteps_account : ltac2:(zQ "h10!j7!n4!p5!r9!t2!uf!v6!vf!hj2!ho6!hp0!hp7!hq2!hr2!hs2!hsc!htf>2ms$0>5model$1>3ms'$0>6model'$1>2c3$e>0@3$4@1$6@1$3@1$2#k0@1$h0^4@1$5@1$3@1$2#k0>0@3$4@1$6@1$3@1$2#k0@1$d^6@1$5@1$3@1$2#k0>0@3$4@1$c@2$7$0$1@3$f?4segs^7^6@2$b@2$7$0$1@4$a$0$1^5^4>0@2$9@2$8^6^5^4@2$9@2$8^9^8^5").
Proof. intros. eapply ds_step; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithLazy.
Variables L S : list (word * word).
Hypothesis HL : ltac2:(zQ "40!ijb!ik2!t2!ji8@3$2$0@2$3?4segs?1L$1").

Theorem account_step_restrict : ltac2:(zQ "h70!j7!n4!t2!hua!p5!r9!vf!hp7!hq2!iif!uf!ijb!v6!hp0!ik2!ik9!ike!il6!hsc!ilc!im7!in3!iod>3msF$0>3ms1$0>5model$1>0@3$9?1L?1S^1>0@3$2@1$8$0@2$h1?4segs@3$h4?1L?1S^4@2$7$0^3@2$f$1\6model'$1@2$3@3$2@1$8@2$6$0$1@3$h2?4segs^6^4@2$7@2$6$0$1@4$d$0$1@4$h6?1L?1S^6^5^1@2$3@3$9?1L?1S^1@2$3@2$h5^4^1>1a@1$5@1$4#k0>0@3$2$b@3$h3?1L?1S^1$e@3$2@1$c@1$5@1$4#8@2$h0^7^2@1$a@1$5@1$4#8").
Proof.
  intros msF ms1 model Hinv Hstep.
  ndestruct (step_restrict segs L S msF ms1 HL Hstep) as (rep & Hsa & Hval & Hvis & Hnone & _).
  destruct (materialize_restrict L S model (accessed_ranges _ rep) Hinv Hvis) as (pages & Hmat & Hinv').
  exists (with_vm_backing (m_vm_lazy model) pages model).
  unfold mi_account_step. rewrite Hsa, Hmat, Hval.
  split; [reflexivity|]. split; [exact Hinv'|]. split; [|exact Hnone].
  apply same_but_materialized_with_vm_backing.
Qed.

(* [comment removed for export] *)
Theorem msteps_restrict_gen : ltac2:(zQ "h10!j7!hua!t2!n4!p5!hj2!iif!im7!iod!r9!uf!v6!ik9!htf!it7!in3!ho6>3ms0$0>3ms1$0>0@3$e?4segs^2^1>3msF$0>5model$3>0@3$2$0^5@3$7?1L?1S^2>0@3$6?1L?1S^2>0@3$2@1$b@1$9@1$4#k0@1$d^3@1$a@1$9@1$4#k0@2$c$3\6model'$3@2$1@2$h0@2$5^6^5@2$5@4$8?1L?1S^6^8^1@2$1@3$6?1L?1S^1@2$1@2$f^5^1@3$2$0@3$7?1L?1S@4$8?1L?1S^6^8^8").
Proof.
  intros ms0 ms1 Hms; induction Hms as [ms | ms ms' ms'' Hsvc Hstep Hms IH];
    intros msF model -> Hinv Hh.
  - exists model. rewrite unrestrict_restrict_self.
    split; [apply ds_refl|]. split; [exact Hinv|].
    split; [apply same_but_materialized_refl | reflexivity].
  - ndestruct (account_step_restrict msF ms' model Hinv Hstep) as (model1 & Hacc & Hinv1 & Hsame1 & Hnone).
    specialize (IH (unrestrict_to L S msF ms') model1).
    rewrite (restrict_unrestrict_to L S msF ms' Hnone) in IH.
    assert (Hh1 : m_halted model1 = None)
      by (rewrite (same_but_materialized_halted _ _ Hsame1); exact Hh).
    ndestruct (IH eq_refl Hinv1 Hh1) as (model' & Hd & Hinv' & Hsame' & Hr).
    rewrite unrestrict_to_idem in Hd, Hr.
    exists model'. split; [|split; [exact Hinv'|split; [|exact Hr]]].
    + eapply dsteps_account; [exact Hh | exact Hsvc | exact Hacc | exact Hd].
    + eapply same_but_materialized_trans; eassumption.
Qed.

Theorem msteps_restrict : ltac2:(zQ "h10!hua!p5!r9!t2!j7!n4!uf!v6!hj2!htf!iif!im7!iod!ik9!it7!in3!ho6>3msF$4>3ms1$4>5model$5>0@3$a?1L?1S^1>0@3$3@1$7@1$2@1$1#k0@1$9^2@1$6@1$2@1$1#k0>0@3$e?4segs@3$b?1L?1S^5^4@2$d$5\6model'$5@2$0@2$h0@2$8^7^5@2$8@4$c?1L?1S^7^6^1@2$0@3$a?1L?1S^1@2$0@2$f^5^1@2$0@3$3@1$7@1$2@1$1#k0@1$9^1@1$6@1$2@1$1#k0@3$3$4@3$b?1L?1S@4$c?1L?1S^7^6^6").
Proof.
  intros msF ms1 model Hinv Hh Hms.
  destruct (msteps_restrict_gen _ _ Hms msF model eq_refl Hinv Hh) as (model' & Hd & Hinv' & Hsame & Hr).
  exists model'. repeat (split; [assumption|]).
  split; [|exact Hr].
  rewrite (same_but_materialized_halted _ _ Hsame). exact Hh.
Qed.

End WithLazy.
End WithSegs.
(* [comment removed for export] *)

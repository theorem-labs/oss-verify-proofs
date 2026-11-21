(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's whole input with its mmap base, launch facts, group id and channel reader, from the published premises; the hand-off tables of the run's CONFIG_RSEQ value; the launch conjunct handed to main). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BShapeAlg BpinAlg Bcfg BxSymExec3 BothPlanCore BothPlan BothPlanSound BothInit BsImages BsPlanImages BsHSTab BsStartup BsStartupPlan BsStartupRanges BsStartupHS1 BsStartupHSC BsStartupHSA BsStartupHSF BsStartupCerts BsMainState BsPlanRegen BsStartupRegen.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma HSF_asan_pc_main : forall h ch, HSF_asan h = Some ch -> pc ch = A_MAIN.
Proof. exact HSF_asan_pc. Qed.

Section Top.
  Variables sp0 brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp0.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hfit : entry_stack_fits sp0 (in_argv inp) (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).
  (* LPS #38: [AsanInit]'s Section discharges the two launch facts, so everything
     above it needs them.  Both are published premises: [valid_launch] is
     [Run.valid_input]'s launch clause and [entry_launch_ok_va] is
     [Run.valid_entry]'s fifth conjunct (BaseAsan*.v already destructs both). *)
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp.

  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis MAIN : forall c, P_mainL sp0 brk0 mbase rdraw inp c -> srealizes ASEGS c T.

  Lemma holes_ok :
    holes_stmt ASEGS ASAN_H BothInit.LIMIT HSF_asan
               (SINV0 APH AENTRY sp0 rdraw brk0 mbase inp)
               (argH0 sp0 rdraw inp)
               (BsStartup.HOLES T) (in_fs inp).
  Proof using Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hlaunch Hlau MAIN.
    intros h ch Hh E R FULL model HC. unfold BsStartup.HOLES.
    rewrite (HSF_asan_pc_main h ch Hh). apply MAIN. split; [|exact Hlau].
    split; [exact (conj Hsp (conj Hbrk (conj Hmb (conj Hva (conj Hve (conj Hfit (conj Huid Hhw)))))))|].
    exists h, ch, E, R, FULL, model. split; [exact Hh|]. split; [exact (HSF_asan_pc_main h ch Hh)|]. split; [reflexivity | exact HC].
  Qed.
End Top.

Theorem as_startup_srealizes :
  forall (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (T : TSet),
    valid_sp sp0 -> valid_brk ASEGS brk0 -> valid_mmap_base mbase ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
    valid_id (in_uid inp) -> valid_id (in_gid inp) -> valid_hwcap (in_hwcap inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp ->
    in_channel_reader inp = true ->
    T [] ->
    (forall c, P_mainL sp0 brk0 mbase rdraw inp c -> srealizes ASEGS c T) ->
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH sp0 brk0 mbase rdraw BothInit.LIMIT inp) T.
Proof.
  intros sp0 brk0 mbase rdraw inp T Hsp Hbrk Hmb Hva Hve Hfit Huid Hgid Hhw Hlaunch Hlau Hrdr T_nil MAIN.
  (* LPS 727298f3: the hand-off tables up to 100 .. 105 are the run's own CONFIG_RSEQ value's *)
  set (R := rseq_z (kb_rseq (in_kernel inp))).
  assert (Hr : R = 0 \/ R = 1) by (unfold R, rseq_z; destruct (kb_rseq (in_kernel inp)); [right | left]; reflexivity).
  (* [as_startup_T]'s Section keeps only the hypotheses its proofs read, so its arguments are given by
     name and the rest discharged by what each one states *)
  apply (as_startup_T AsanUbsan.M.init_pc sp0 rdraw brk0 mbase inp) with
    (RANGES := startup_plan_xranges) (HS1 := HS1_asan_r R) (HSC := HSC_asan_r R) (HSA := HSA_asan_r R)
    (HSF := HSF_asan) (plan1 := psh FSH startup_plan) (shape1 := AsStartupCert1.startup_shape)
    (KC0 := CERT_KC0) (BFUEL := CERT_BFUEL) (FUEL := CERT_FUEL).
  all: lazymatch goal with
       | |- @eq cres _ _ => exact (AsStartupCert1.startup_cert R Hr)
       | |- holes_only _ = true => exact AsStartupCert1.startup_shape_holes
       | |- level_certified _ _ _ (HS1_asan_r _) _ => exact (cert2 R)
       | |- level_certified _ _ _ (HSC_asan_r _) _ => exact (cert3 R)
       | |- level_certified _ _ _ (HSA_asan_r _) _ => exact (cert4 R)
       | |- context [holes_stmt] => eapply holes_ok; eassumption
       | |- Z.of_N _ = _ => reflexivity
       | |- _ => assumption
       end.
Qed.

Lemma LIMIT_eq : BothInit.LIMIT = target_alloc_limit.
Proof. reflexivity. Qed.

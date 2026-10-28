(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BShapeAlg BpinAlg Bcfg BxSymExec3 BothPlanCore BothPlan BothPlanSound BothInit BsImages BsPlanImages BsHSTab BsStartup BsStartupPlan BsStartupRanges BsStartupHS1 BsStartupHSC BsStartupHSA BsStartupHSF BsStartupCerts BsMainState.
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

  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis MAIN : forall c, P_main sp0 brk0 mbase rdraw inp c -> srealizes ASEGS c T.

  Lemma holes_ok :
    holes_stmt ASEGS ASAN_H BothInit.LIMIT HSF_asan
               (SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
               (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
               (BsStartup.HOLES T) (in_fs inp).
  Proof.
    intros h ch Hh E R FULL model HC. unfold BsStartup.HOLES.
    rewrite (HSF_asan_pc_main h ch Hh). apply MAIN.
    split; [exact (conj Hsp (conj Hbrk (conj Hmb (conj Hva (conj Hve (conj Hfit (conj Huid Hhw)))))))|].
    exists h, ch, E, R, FULL, model. split; [exact Hh|]. split; [exact (HSF_asan_pc_main h ch Hh)|]. split; [reflexivity | exact HC].
  Qed.
End Top.

Theorem as_startup_srealizes :
  forall (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (T : TSet),
    valid_sp sp0 -> valid_brk ASEGS brk0 -> valid_mmap_base mbase ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
    valid_id (in_uid inp) -> valid_hwcap (in_hwcap inp) ->
    T [] ->
    (forall c, P_main sp0 brk0 mbase rdraw inp c -> srealizes ASEGS c T) ->
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH sp0 brk0 mbase rdraw BothInit.LIMIT inp) T.
Proof.
  intros sp0 brk0 mbase rdraw [argv envp fs stdin uid gid groups net nofile sigmask hw abterm vasz urandom tmp] T Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw T_nil MAIN.
  exact (as_startup_T sp0 rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urandom tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
           startup_plan_xranges HS1_asan HSC_asan HSA_asan HSF_asan startup_plan AsStartupCert1.startup_shape
           CERT_KC0 CERT_BFUEL CERT_FUEL AsStartupCert1.startup_cert AsStartupCert1.startup_shape_holes cert2 cert3 cert4
           T T_nil
           (holes_ok sp0 brk0 mbase rdraw (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw abterm vasz urandom tmp)
                     Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw T MAIN)).
Qed.

Lemma LIMIT_eq : BothInit.LIMIT = target_alloc_limit.
Proof. reflexivity. Qed.

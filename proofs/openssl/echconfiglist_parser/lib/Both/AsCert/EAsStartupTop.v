(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec ShapeAlg SpinAlg Scfg AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsHSTab.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import
  AsImages AsPlanImages AsStartup EAsStartupPlan EAsStartupRanges EAsStartupHS1 EAsStartupHSC EAsStartupHSA EAsStartupCerts EAsS6State.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require EAsStartupCert_startup_plan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Amb.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma HSA_easan_pc : forall h ch, HSA_easan h = Some ch -> pc ch = A_S6.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSA_easan_table fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh.
Qed.

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
  Hypothesis S6 : forall c, P_s6 sp0 brk0 mbase rdraw inp c -> realizes ASEGS c T.

  Lemma holes_ok :
    holes_stmt ASEGS ASAN_H AsanInit.LIMIT HSA_easan
               (SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
               (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
               (AsStartup.HOLES T) (in_fs inp).
  Proof.
    intros h ch Hh E R FULL model HC. unfold AsStartup.HOLES.
    apply srealizes_of_realizes. rewrite (HSA_easan_pc h ch Hh). apply S6.
    split; [exact (conj Hsp (conj Hbrk (conj Hmb (conj Hva (conj Hve (conj Hfit (conj Huid Hhw)))))))|].
    exists h, ch, E, R, FULL, model. split; [exact Hh|]. split; [exact (HSA_easan_pc h ch Hh)|]. split; [reflexivity | exact HC].
  Qed.
End Top.

Theorem as_startup_srealizes :
  forall (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (T : TSet),
    valid_sp sp0 -> valid_brk ASEGS brk0 -> valid_mmap_base mbase ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
    valid_id (in_uid inp) -> valid_hwcap (in_hwcap inp) ->
    T [] ->
    (forall c, P_s6 sp0 brk0 mbase rdraw inp c -> realizes ASEGS c T) ->
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH sp0 brk0 mbase rdraw AsanInit.LIMIT inp) T.
Proof.
  intros sp0 brk0 mbase rdraw inp T Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw T_nil S6.
  rewrite Amb.init_config_canon.
  exact (as_startup_T sp0 rdraw brk0 mbase (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
           (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_abort_terminal inp) (in_va_size inp) (in_urandom inp)
           Hsp Hbrk Hva Hve Hfit Huid Hhw
           startup_plan_xranges HS1_easan HSC_easan HSA_easan startup_plan EAsStartupCert_startup_plan.startup_shape
           EAsStartupCert_startup_plan.KC0 EAsStartupCert_startup_plan.BFUEL EAsStartupCert_startup_plan.FUEL
           EAsStartupCert_startup_plan.startup_cert EAsStartupCert_startup_plan.startup_shape_holes cert2 cert3
           T T_nil
           (holes_ok sp0 brk0 mbase rdraw inp Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw T S6)).
Qed.

(* [comment removed for export] *)
Lemma LIMIT_eq : AsanInit.LIMIT = target_alloc_limit.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

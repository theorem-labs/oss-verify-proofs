(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up invariant is SINV0 at the run's base, closed by cs_ok_SINV0L under the launch fact; as_startup_srealizes takes the channel-reader and launch premises and the hand-off tables of the run's CONFIG_RSEQ value); as_startup_srealizes is generic in the Leaf class of its walk, and its S6 continuation is an srealizes walk of that class. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Asan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec ShapeAlg SpinAlg Scfg AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanInitL AsHSTab.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.AsCert Require Import
  AsImages AsPlanImages AsStartup EAsStartupPlan EAsStartupRanges EAsStartupHS1 EAsStartupHSC EAsStartupHSA EAsStartupCerts EAsS6State.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.AsCert Require EAsStartupCert_startup_plan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Amb.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import Leaf.
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
  Context {LF : Leaf}.
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
  (** #38: [Run.valid_entry]'s fifth conjunct, the defining fact of the base the
      start-up invariant is repacked over *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp.

  Variable T : TSet.
  Hypothesis T_nil : T [].
  (* an srealizes walk of the class in scope: the S6 continuation may end in leaves *)
  Hypothesis S6 : forall c, P_s6 sp0 brk0 mbase rdraw inp c -> srealizes ASEGS c T.

  (** the start-up phase's invariant is [SINV0] at the run's base; [P_s6] closes it
      ([AsanInitL.cs_ok_SINV0L], the one place the witness is introduced) *)
  Lemma holes_ok :
    holes_stmt ASEGS ASAN_H AsanInit.LIMIT HSA_easan
               (SINV0 APH Asan.M.init_pc sp0 rdraw brk0 mbase inp)
               (argH0 sp0 rdraw inp)
               (AsStartup.HOLES T) (in_fs inp).
  Proof using All.
    intros h ch Hh E R FULL model HC. unfold AsStartup.HOLES.
    rewrite (HSA_easan_pc h ch Hh). apply S6.
    split; [exact (conj Hsp (conj Hbrk (conj Hmb (conj Hva (conj Hve (conj Hfit (conj Huid Hhw)))))))|].
    exists h, ch, E, R, FULL, model. split; [exact Hh|]. split; [exact (HSA_easan_pc h ch Hh)|]. split; [reflexivity|].
    eapply cs_ok_SINV0L; [exact Hmb | exact Hlau | exact HC].
  Qed.
End Top.

Theorem as_startup_srealizes {LF : Leaf} :
  forall (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (T : TSet),
    valid_sp sp0 -> valid_brk ASEGS brk0 -> valid_mmap_base mbase ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
    valid_id (in_uid inp) -> valid_hwcap (in_hwcap inp) ->
    (* 08b1429: [Run.valid_input]'s reader clause *)
    in_channel_reader inp = true ->
    (* #38: [Run.valid_input]'s launch clause and [Run.valid_entry]'s fifth conjunct *)
    valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp ->
    T [] ->
    (forall c, P_s6 sp0 brk0 mbase rdraw inp c -> srealizes ASEGS c T) ->
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp0 brk0 mbase rdraw AsanInit.LIMIT inp) T.
Proof.
  intros sp0 brk0 mbase rdraw inp T Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hrdr Hlaunch Hlau T_nil S6.
  (* LPS 727298f3: the hand-off tables up to 91/94 are the run's CONFIG_RSEQ value's ([EAsStartupHS1],
     [EAsStartupHSC]); the S6 table is met over both values ([EAsStartupHSA]) *)
  exact (as_startup_T sp0 rdraw brk0 mbase inp Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hrdr Hlaunch Hlau
           startup_plan_xranges (HS1_easan_r (rseq_z (kb_rseq (in_kernel inp)))) (HSC_easan_r (rseq_z (kb_rseq (in_kernel inp))))
           HSA_easan startup_plan_k EAsStartupCert_startup_plan.startup_shape
           EAsStartupCert_startup_plan.KC0 EAsStartupCert_startup_plan.BFUEL EAsStartupCert_startup_plan.FUEL
           (EAsStartupCert_startup_plan.startup_cert_k (in_kernel inp)) EAsStartupCert_startup_plan.startup_shape_holes
           (cert2 _) (cert3 _)
           T T_nil
           (holes_ok sp0 brk0 mbase rdraw inp Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hlau T T_nil S6)).
Qed.

(* [comment removed for export] *)
Lemma LIMIT_eq : AsanInit.LIMIT = target_alloc_limit.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

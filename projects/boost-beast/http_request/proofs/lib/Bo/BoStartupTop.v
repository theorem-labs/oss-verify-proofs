(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's channel-reader, launch and entry premises; the start-up invariant with its mmap base; the start-up certificate taken at the run's CONFIG_RSEQ value over the computed hand-off tables). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec ShapeAlg SpinAlg Scfg AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit BothImages BothPlanImages AsHSTab BoStartup BoStartupPlan BoStartupRanges BoStartupHS1 BoStartupHSC BoStartupHSA BoStartupHSF BoStartupCerts BoMainState.
From OSSVerify.boost_beast.http_request.images Require AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanInitL.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma HSF_both_pc_main : forall h ch, HSF_both h = Some ch -> pc ch = A_MAIN.
Proof. exact HSF_both_pc. Qed.

Section Top.
  Variables sp0 brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp0.
  Hypothesis Hbrk : valid_brk BSEGS2 brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hfit : entry_stack_fits sp0 (in_argv inp) (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).
  (* [Run.valid_entry]'s fifth conjunct: the defining fact of the base [P_main]'s invariant
     is repacked over ([cs_ok_SINV0L], As/AsanInitL.v:174) *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp.

  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis MAIN : forall c, P_main sp0 brk0 mbase rdraw inp c -> srealizes BSEGS2 c T.

  (* the start-up phase's invariant is [SINV0] at the run's base (Bo/BoStartup.v:168);
     [P_main] holds it as [SINV0L] *)
  Lemma holes_ok :
    holes_stmt BSEGS2 BOTH_H AsanInit.LIMIT HSF_both
               (SINV0 BPH2 OSSVerify.boost_beast.http_request.images.AsanUbsan.M.init_pc sp0 rdraw brk0 mbase inp)
               (argH0 sp0 rdraw inp)
               (BoStartup.HOLES T) (in_fs inp).
  Proof.
    intros h ch Hh E R FULL model HC. unfold BoStartup.HOLES.
    rewrite (HSF_both_pc_main h ch Hh). apply MAIN.
    split; [exact (conj Hsp (conj Hbrk (conj Hmb (conj Hva (conj Hve (conj Hfit (conj Huid Hhw)))))))|].
    exists h, ch, E, R, FULL, model. split; [exact Hh|]. split; [exact (HSF_both_pc_main h ch Hh)|]. split; [reflexivity|].
    eapply cs_ok_SINV0L; [exact Hmb | exact Hlau | exact HC].
  Qed.
End Top.

Theorem bo_startup_srealizes :
  forall (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (T : TSet),
    valid_sp sp0 -> valid_brk BSEGS2 brk0 -> valid_mmap_base mbase ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
    valid_id (in_uid inp) -> valid_hwcap (in_hwcap inp) ->
    (* [Run.valid_input_channel_reader], [Run.valid_input]'s launch clause and
       [Run.valid_entry]'s fifth conjunct: what Bo/BoStartup.v:163-166 takes *)
    in_channel_reader inp = true -> valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp ->
    T [] ->
    (forall c, P_main sp0 brk0 mbase rdraw inp c -> srealizes BSEGS2 c T) ->
    srealizes BSEGS2 (init_config BSEGS2 AsanUbsan.M.init_pc BPH2 sp0 brk0 mbase rdraw AsanInit.LIMIT inp) T.
Proof.
  intros sp0 brk0 mbase rdraw inp T Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hrdr Hlaunch Hlau T_nil MAIN.
  (* [as_startup_T]'s Section (Bo/BoStartup.v:137-193) generalised over what its proof uses, in
     declaration order: sp rdraw brk0 mbase inp, then Hsp Hbrk Hmb Hva Hve Huid Hhw Hlaunch Hlau
     Hrdr (no Hfit: neither [init_cs_ok] nor [asan_node_x_sound_all] reads it), then the
     certificate's RANGES HS1 HSC HSA HSF plan1 shape1 KC0 BFUEL FUEL cert1 shape1_holes cert2
     cert3 cert4, then T T_nil HOLESF_sound.  LPS 727298f3: the hand-off tables up to 100 .. 105 are
     one per CONFIG_RSEQ value ([BoStartupHS1], [BoStartupHSC], [BoStartupHSA]), taken at the run's
     own value, and the plan is the renumbered [startup_plan_k]. *)
  exact (as_startup_T sp0 rdraw brk0 mbase inp Hsp Hbrk Hmb Hva Hve Huid Hhw Hlaunch Hlau Hrdr
           startup_plan_xranges (HS1_both_r (rseq_z (kb_rseq (in_kernel inp)))) (HSC_both_r (rseq_z (kb_rseq (in_kernel inp))))
           (HSA_both_r (rseq_z (kb_rseq (in_kernel inp)))) HSF_both startup_plan_k BoStartupCert1.startup_shape
           CERT_KC0 CERT_BFUEL CERT_FUEL (BoStartupCert1.startup_cert_k (in_kernel inp)) BoStartupCert1.startup_shape_holes
           (cert2 (rseq_z (kb_rseq (in_kernel inp)))) (cert3 (rseq_z (kb_rseq (in_kernel inp)))) (cert4 (rseq_z (kb_rseq (in_kernel inp))))
           T T_nil
           (holes_ok sp0 brk0 mbase rdraw inp Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hlau T MAIN)).
Qed.

(* [comment removed for export] *)
Theorem bo_startup_realizes :
  forall (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (T : TSet),
    valid_sp sp0 -> valid_brk BSEGS2 brk0 -> valid_mmap_base mbase ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
    valid_id (in_uid inp) -> valid_hwcap (in_hwcap inp) ->
    in_channel_reader inp = true -> valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp ->
    T [] ->
    (forall c, P_main sp0 brk0 mbase rdraw inp c -> realizes BSEGS2 c T) ->
    realizes BSEGS2 (init_config BSEGS2 AsanUbsan.M.init_pc BPH2 sp0 brk0 mbase rdraw AsanInit.LIMIT inp) T.
Proof.
  intros sp0 brk0 mbase rdraw inp T Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hrdr Hlaunch Hlau T_nil MAIN.
  apply realizes_of_srealizes.
  apply (bo_startup_srealizes sp0 brk0 mbase rdraw inp T Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hrdr Hlaunch Hlau T_nil).
  intros c Hc. apply srealizes_of_realizes. exact (MAIN c Hc).
Qed.

(* [comment removed for export] *)
Lemma LIMIT_eq : AsanInit.LIMIT = target_alloc_limit.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ASEGS_eq : BSEGS2 = AsanUbsan.M.loaded_segments.
Proof. reflexivity. Qed.
Lemma APH_eq : BPH2 = AsanUbsan.M.phdrs.
Proof. reflexivity. Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec Scfg ShapeAlg SpinAlg HeapCeil Spec AsanInit AsPlanImages AsMainState.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common.LimSim Require Import LimSimSys.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bridge Require Import MustExitIn.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsIface Fuzz_stmt AsInstanceMain AS_InstFree AS_InstanceKit AS_InstanceClosed.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top Require Import PlainTop AsanClosed BaseAsan.
Import ListNotations.
Open Scope Z_scope.

Local Existing Instance fx0.

Section Open.

  (* [comment removed for export] *)
  Lemma asan_realizes_entry :
    forall en inp,
      valid_entry ASANI en inp -> valid_input inp ->
      match en with mkEntry sp brk mbase rnd =>
        realizes asegs (init_config asegs Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
                 (spec (in_argv inp) (in_fs inp)) end.
  Proof.
    intros [sp brk mbase rnd] inp Hen Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    pose proof Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _).
    apply realizes_of_srealizes.
    exact (AsanClosed.as_realizes_closed sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds Hhw).
  Qed.

  (* [comment removed for export] *)
  Lemma asan_must_exit_big :
    forall en inp, valid_entry ASANI en inp -> valid_input inp ->
      must_exit_in_scfg forced_only_cfg exit_codes_02 ASANI target_alloc_limit en inp.
  Proof.
    intros en inp Hen Hvalid.
    apply (must_exit_in_scfg_mono forced_only_cfg (@the_scfg hunspell_scfg));
      [apply forced_only_cfg_least | apply run_decided_classic |].
    pose proof (asan_realizes_entry en inp Hen Hvalid) as RZ.
    destruct en as [sp brk mbase rnd]. cbn [must_exit_in_scfg ASANI].
    eapply realizes_must_exit_in; [exact RZ | left; reflexivity | apply spec_exits].
  Qed.

  (* [comment removed for export] *)
  Theorem asan_halts :
    halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source exit_codes_02 ASANI.
  Proof.
    intros en inp Hen Hvalid SWB.
    apply (must_exit_in_scfg_relim_closed forced_only_cfg exit_codes_02 ASANI target_alloc_limit ShippedBudgets.lim_source en inp).
    - unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia.
    - exact SWB.
    - exact (asan_must_exit_big en inp Hen Hvalid).
  Qed.
End Open.

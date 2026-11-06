(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec ShapeAlg SpinAlg Scfg Spec HeapCeil AsanInit AsPlanImages AsMainState AsStartupTop.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsIface Fuzz_stmt AsInstance AsInstanceMain AS_InstFree AS_InstanceKit AS_InstanceClosed AsTop.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJA Require Import L_top.
Import ListNotations.
Open Scope Z_scope.

Local Existing Instance fx0.

(* [comment removed for export] *)
Definition FUZZ : forall (HC : HeapCeil) (H : asr), asan_rt_hyps H -> fuzz_stmt H := fun HC H RT => @fuzz_all HC H RT.

Section Open.

  Theorem as_realizes_closed :
    forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
      valid_sp sp -> valid_brk asegs brk -> valid_mmap_base mbase ->
      entry_stack_fits sp (in_argv inp) (in_envp inp) ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp -> valid_hwcap (in_hwcap inp) ->
      srealizes asegs (init_config asegs Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
                (spec (in_argv inp) (in_fs inp)).
  Proof.
    apply (as_realizes_spec AsMainState.P_main).
    - intros sp0 brk0 mbase rdraw inp T Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Tnil MAIN.
      pose proof (as_startup_srealizes sp0 brk0 mbase rdraw inp T Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Tnil MAIN) as S.
      rewrite LIMIT_eq in S. exact S.
    - exact as_instance_closed.
    - exact FUZZ.
  Qed.
End Open.

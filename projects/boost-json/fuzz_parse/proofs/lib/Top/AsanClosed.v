(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: as_realizes_closed over the run's segment list (run_segments), with the launch facts valid_launch, entry_launch_ok_va and the channel reader. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec ShapeAlg SpinAlg Scfg Spec HeapCeil AsanInit AsPlanImages AsMainState AsStartupTop.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common.Cfg Require RomStableS.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsIface Fuzz_stmt AsInstance AsInstanceMain AS_InstFree AS_InstanceKit AS_InstanceClosed AsTop.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJA Require Import L_top.
Import ListNotations.
Open Scope Z_scope.

Local Existing Instance fx0.

(* [comment removed for export] *)
Definition FUZZ : forall (HC : HeapCeil) (H : asr), asan_rt_hyps H -> fuzz_stmt H := fun HC H RT => @fuzz_all HC H RT.

Section Open.

  (* LPS 727298f3 port: the walk is over the run's segment list ([Run.run_segments]): the walk
     over the image's own segments ([As.AsTop.as_realizes_spec]) is lifted by
     [RomStableS.srun_init] ([vdso_image] of those segments is [None] by computation).  The
     launch facts [valid_launch], [entry_launch_ok_va] and the channel reader, which
     [Run.valid_input] and [Run.valid_entry] give, are premises. *)
  Theorem as_realizes_closed :
    forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
      valid_sp sp -> valid_brk asegs brk -> valid_mmap_base mbase ->
      entry_stack_fits sp (in_argv inp) (in_envp inp) ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp -> valid_hwcap (in_hwcap inp) ->
      valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> in_channel_reader inp = true ->
      srealizes (run_segments asegs inp sp mbase)
        (init_config (run_segments asegs inp sp mbase) Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
        (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hva Hve Hfs Hcr Hhw Hvl Hlau Hrdr.
    apply RomStableS.srun_init; [vm_compute; reflexivity |].
    apply (as_realizes_spec AsMainState.P_main); try assumption.
    - intros sp0 brk0 mbase0 rdraw inp0 T Hsp0 Hbrk0 Hmb0 Hva0 Hve0 Hfit0 Huid0 Hhw0 Hvl0 Hlau0 Hrdr0 Tnil MAIN.
      pose proof (as_startup_srealizes sp0 brk0 mbase0 rdraw inp0 T Hsp0 Hbrk0 Hmb0 Hva0 Hve0 Hfit0 Huid0 Hhw0
                    Hvl0 Hlau0 Hrdr0 Tnil MAIN) as S.
      rewrite LIMIT_eq in S. exact S.
    - exact as_instance_closed.
    - exact FUZZ.
  Qed.
End Open.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up invariant at the run's mmap base, and the state at main with the launch conjunct). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec Scfg AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsImages AsPlanImages AsHSTab AsStartupHSF.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition A_MAIN : Z := 0xe87ac.

Definition N_HOLES : nat := 6.

Definition P_main (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config) : Prop :=
  (valid_sp sp0 /\ valid_brk ASEGS brk0 /\ valid_mmap_base mbase /\ valid_argv (in_argv inp) /\ valid_envp (in_envp inp)
   /\ entry_stack_fits sp0 (in_argv inp) (in_envp inp) /\ valid_id (in_uid inp) /\ valid_hwcap (in_hwcap inp))
  /\ exists (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
    HSF_asan h = Some ch /\ pc ch = A_MAIN /\
    c = cfg_of ASEGS R A_MAIN FULL model /\
    cs_ok ASEGS ASAN_H AsanInit.LIMIT
          (SINV0 APH AENTRY sp0 rdraw brk0 mbase inp)
          (argH0 sp0 rdraw inp)
          (in_fs inp) E ch R FULL model.

(** The state at main with [Run.valid_entry]'s launch conjunct at the run's mmap base, which the argument lemmas at
    main (AsMainIfaceArgs) read: the strings' place at the top of the entry block.  The start-up hands it over. *)
Definition P_mainL (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config) : Prop :=
  P_main sp0 brk0 mbase rdraw inp c /\ entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp.

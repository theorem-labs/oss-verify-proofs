(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (P_s6 is stated over AsanInitL's SINV0L and argH0 of the run's input). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Asan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec Scfg AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanInitL AsHSTab.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.AsCert Require Import AsImages AsPlanImages EAsStartupHSA.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition A_S6 : Z := 0x1ab70c.
(* [comment removed for export] *)
Definition A_S6_END : Z := 0x1f42d8.
(* [comment removed for export] *)
Definition A_MAIN : Z := 0x1f3df4.

Definition N_HOLES : nat := 4.

(** #38: past start-up the run's mmap base is closed inside the invariant
    ([AsanInitL.SINV0L]); [mbase] stays a parameter for [valid_mmap_base] only *)
Definition P_s6 (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config) : Prop :=
  (valid_sp sp0 /\ valid_brk ASEGS brk0 /\ valid_mmap_base mbase /\ valid_argv (in_argv inp) /\ valid_envp (in_envp inp)
   /\ entry_stack_fits sp0 (in_argv inp) (in_envp inp) /\ valid_id (in_uid inp) /\ valid_hwcap (in_hwcap inp))
  /\ exists (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
    HSA_easan h = Some ch /\ pc ch = A_S6 /\
    c = cfg_of ASEGS R A_S6 FULL model /\
    cs_ok ASEGS ASAN_H AsanInit.LIMIT
          (SINV0L APH Asan.M.init_pc sp0 rdraw brk0 inp)
          (argH0 sp0 rdraw inp)
          (in_fs inp) E ch R FULL model.

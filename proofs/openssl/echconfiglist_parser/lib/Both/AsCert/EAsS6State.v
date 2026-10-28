(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec Scfg AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsHSTab.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages EAsStartupHSA.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition A_S6 : Z := 0x1a6634.
(* [comment removed for export] *)
Definition A_S6_END : Z := 0x1ef200.
(* [comment removed for export] *)
Definition A_MAIN : Z := 0x1eed1c.

Definition N_HOLES : nat := 4.

Definition P_s6 (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config) : Prop :=
  (valid_sp sp0 /\ valid_brk ASEGS brk0 /\ valid_mmap_base mbase /\ valid_argv (in_argv inp) /\ valid_envp (in_envp inp)
   /\ entry_stack_fits sp0 (in_argv inp) (in_envp inp) /\ valid_id (in_uid inp) /\ valid_hwcap (in_hwcap inp))
  /\ exists (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
    HSA_easan h = Some ch /\ pc ch = A_S6 /\
    c = cfg_of ASEGS R A_S6 FULL model /\
    cs_ok ASEGS ASAN_H AsanInit.LIMIT
          (SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
          (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
          (in_fs inp) E ch R FULL model.

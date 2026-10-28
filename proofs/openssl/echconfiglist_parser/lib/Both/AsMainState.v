(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec Scfg AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsHSTab.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages EAsS6State.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsHole Require Import ES6End0 ES6End1 ES6End2 ES6End3 ES6End4 ES6End5 EAsChain.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition A_MAIN : Z := 0x1eed1c.
Lemma A_MAIN_eq : A_MAIN = EAsS6State.A_MAIN.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition N_HOLES : nat := 6.
Definition HSF_asan_table : list (nat * acs) :=      (* [comment removed for export] *)
  [(0%nat, es6end0); (1%nat, es6end1); (2%nat, es6end2); (3%nat, es6end3); (4%nat, es6end4); (5%nat, es6end5)].
Definition HSF_asan (h : nat) : option acs := hs_lookup h HSF_asan_table.
Lemma HSF_asan_MAINST : forall h, HSF_asan h = EAsChain.MAINST h.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition P_main (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config) : Prop :=
  EAsChain.P_main sp0 brk0 mbase rdraw inp c.

(* [comment removed for export] *)
Lemma P_main_H : forall sp0 brk0 mbase rdraw inp c, P_main sp0 brk0 mbase rdraw inp c ->
  (valid_sp sp0 /\ valid_brk ASEGS brk0 /\ valid_mmap_base mbase /\ valid_argv (in_argv inp) /\ valid_envp (in_envp inp)
   /\ entry_stack_fits sp0 (in_argv inp) (in_envp inp) /\ valid_id (in_uid inp) /\ valid_hwcap (in_hwcap inp))
  /\ exists (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
    HSF_asan h = Some ch /\ pc ch = A_MAIN /\
    c = cfg_of ASEGS R A_MAIN FULL model /\
    cs_ok ASEGS ASAN_H AsanInit.LIMIT
          (SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
          (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
          (in_fs inp) E ch R FULL model.
Proof.
  intros sp0 brk0 mbase rdraw inp c [V (h & ch & E & R & FULL & model & Hh & Hpc & Hc & HC & _)].
  split; [exact V|]. exists h, ch, E, R, FULL, model.
  split; [exact Hh|]. split; [exact Hpc|]. split; [exact Hc|]. exact HC.
Qed.

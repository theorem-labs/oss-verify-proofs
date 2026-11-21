(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from UbStartupRz.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput; the launch premises valid_launch and entry_launch_ok_va; the run's segment list run_segments; the launch's reservations with the vDSO pair). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim StartupTac ShapeSet RealizesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UbStartup.
Import ListNotations.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UbStartupRz.
From OSSVerify.Proofs.fast_float.from_chars.lib.BudgetWit Require Import Common_SysNodesCfgB Rzb.

Open Scope bv_scope.
Local Instance ubrz_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Theorem ub_startup_rz_b : forall (cfg : SpuriousCfg) (K : TSet) sp brk mbase rnd lim inp,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     main_entry inp mbase (0x22780 : word) sp rnd tid regs mem ->
     Rzb.rzb (run_segments SEGS inp sp mbase) cfg
       (mkCfg (mkst regs (0x228cc : word) mem (seg_rom (run_segments SEGS inp sp mbase)))
              (with_tid tid (cfg_model (init_config (run_segments SEGS inp sp mbase) Ubsan.M.init_pc
                                                    Ubsan.M.phdrs sp brk mbase rnd lim inp)))) K) ->
  Rzb.rzb (run_segments SEGS inp sp mbase) cfg
    (init_config (run_segments SEGS inp sp mbase) Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase rnd lim inp) K.
Proof.
  intros cfg K sp brk mbase rnd lim inp Hsp Hva Hve Hvl Hlau HK.
  set (P := fun (st : machine_state) (model : Model) =>
              Rzb.rzb (run_segments SEGS inp sp mbase) cfg (mkCfg st model) K).
  change (P (cfg_ms (init_config (run_segments SEGS inp sp mbase) Ubsan.M.init_pc
                                   Ubsan.M.phdrs sp brk mbase rnd lim inp))
            (cfg_model (init_config (run_segments SEGS inp sp mbase) Ubsan.M.init_pc
                                   Ubsan.M.phdrs sp brk mbase rnd lim inp))).
  apply (ub_startup sp brk mbase rnd lim inp P);
    [ | | exact Hsp | exact Hva | exact Hve | exact Hvl | exact Hlau | exact HK ].
  - intros model Hh Hl st st' Hms H. unfold P in *.
    eapply Rzb.rzb_isteps;
      [exact Hh | exact Hl | apply UbStartupRz.isteps_of_msteps; apply msteps_run_segments; exact Hms | exact H].
  - intros regs pc mem rom model w HF HE Hh Hl H17 Ht HKt. unfold P in *.
    eapply (Common_SysNodesCfgB.rzb_set_tid (run_segments SEGS inp sp mbase) cfg regs pc mem rom model w K
              (fetch_word_run_segments _ _ _ _ _ _ HF) HE Hh Hl H17 Ht). exact HKt.
Qed.

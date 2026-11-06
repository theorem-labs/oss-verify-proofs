(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim StartupTac ShapeSet RealizesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UbStartup.
Import ListNotations.
Open Scope bv_scope.
Local Instance ubrz_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma isteps_of_msteps : forall segs ms ms', CatSim.msteps segs ms ms' -> isteps segs ms ms'.
Proof.
  intros segs ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hst _ IH];
    [apply ist_refl | eapply ist_step; eassumption].
Qed.

Theorem ub_startup_rz : forall (cfg : SpuriousCfg) (K : TSet) sp brk mbase rnd lim inp,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     main_entry sp (in_argv inp) (in_envp inp) (in_uid inp) tid (in_hwcap inp) rnd regs mem ->
     realizes_cfg SEGS cfg
       (mkCfg (mkst regs (0x228cc : word) mem (seg_rom SEGS))
              (with_tid tid (init_model (segments_reserved SEGS) brk mbase sp lim inp))) K) ->
  realizes_cfg SEGS cfg (init_config SEGS Ubsan.M.init_pc
                                     Ubsan.M.phdrs sp brk mbase rnd lim inp) K.
Proof.
  intros cfg K sp brk mbase rnd lim inp Hsp Hva Hve HK.
  set (P := fun (st : machine_state) (model : Model) => realizes_cfg SEGS cfg (mkCfg st model) K).
  change (P (cfg_ms (init_config SEGS Ubsan.M.init_pc
                                   Ubsan.M.phdrs sp brk mbase rnd lim inp))
            (cfg_model (init_config SEGS Ubsan.M.init_pc
                                   Ubsan.M.phdrs sp brk mbase rnd lim inp))).
  apply (ub_startup P); [ | | exact Hsp | exact Hva | exact Hve | exact HK ].
  - intros model Hh Hl st st' Hms H. unfold P in *.
    eapply rzc_isteps; [exact Hh | exact Hl | apply isteps_of_msteps; exact Hms | exact H].
  - intros regs pc mem model w HF HE Hh Hl H17 Ht HKt. unfold P in *.
    eapply (rzc_set_tid SEGS cfg regs pc mem (seg_rom SEGS) model w K HF HE Hh Hl H17 Ht). exact HKt.
Qed.

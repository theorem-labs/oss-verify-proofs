(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require ShapeAlg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition halt_ev (m' : Model) (code : word) : event :=
  match m_killed m' with
  | Some sig => KillEv sig (m_fs m')
  | None => ExitEv code (m_fs m')
  end.

Lemma sstep_svc_inv : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs ACFG (mkCfg ms model) e st ->
  (exists eff model' evs,
      syscall_spec_acfg (sys_input segs ms x8) model (Ok eff model' evs)
      /\ ((exists model'', m_halted model' = None /\ e = evs
             /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
             /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
          \/ (m_halted model' = None /\ e = []
              /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
              /\ st = SError)
          \/ (exists code, m_halted model' = Some code
              /\ e = evs ++ [halt_ev model' code]
              /\ st = SNext (mkCfg ms model'))))
  \/ (exists eff, check_syscall (sys_input segs ms x8) eff model = CheckUnmodeled
      /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  pose proof (sstep_cfg_sys_inv_acfg segs ms model x8 e st Hsvc Hss) as Hinv. cbv zeta in Hinv.
  destruct Hinv as [(eff & model' & evs & Hs & Hh' & Hm)
                   | [(eff & model' & evs & code & Hs & Hh' & Hk & -> & ->)
                     | [(eff & model' & evs & sig & Hs & Hk & -> & ->) | (Hs & -> & ->)]]].
  - left. exists eff, model', evs. split; [exact Hs|].
    revert Hm. destruct (materialize_model_accesses model' (syscall_effect_accesses eff)) as [model''|] eqn:Hmat;
      intros [-> ->].
    + (* [comment removed for export] *)
      left. exists model''. split; [exact Hh'|]. split; [reflexivity|]. split; [first [exact Hmat | reflexivity] | reflexivity].
    + (* [comment removed for export] *)
      right. left. split; [exact Hh'|]. split; [reflexivity|]. split; [first [exact Hmat | reflexivity] | reflexivity].
  - (* [comment removed for export] *)
    left. exists eff, model', evs. split; [exact Hs|].
    right. right. exists code. split; [exact Hh'|].
    split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity].
  - (* [comment removed for export] *)
    left. exists eff, model', evs. split; [exact Hs|].
    right. right.
    destruct (m_halted model') as [code|] eqn:Hhc;
      [| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk].
    exists code. split; [reflexivity|]. split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity].
  - (* [comment removed for export] *)
    right. exists (mkEffect (Z_to_bv 64 0) [] []). split; [|split; reflexivity].
    apply check_syscall_err_iff. exact (proj1 (syscall_spec_acfg_unmodeled _ _) Hs).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition open_I (model : Model) : Type := {e : Z | In e openat_errnos} + unit.

Definition open_nx (ms : machine_state) (model : Model) (mk : word -> Model)
  (i : open_I model) : config :=
  match i with
  | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | inr _ => mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                   (mk (alloc_fd (m_fds model)))
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.

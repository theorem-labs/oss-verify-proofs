(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs Monad State Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15 HaltsFO YK18.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import LimSimSys.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.

Lemma init_config_not_halted : forall segs pc ph sp brk mb rnd lim inp,
  m_halted (cfg_model (init_config segs pc ph sp brk mb rnd lim inp)) = None.
Proof. intros. reflexivity. Qed.

Theorem halts_budgets_of_srealizes : forall S segs pc ph (Lbig Lsmall : Z),
  (Lsmall <= Lbig)%Z ->
  (forall sp brk mb rnd inp,
      valid_entry (mkImage segs pc ph) (mkEntry sp brk mb rnd) inp -> valid_input inp ->
      exists T, srealizes segs (init_config segs pc ph sp brk mb rnd Lbig inp) T /\ shape_ok S T) ->
  halts_allowed_T_scfg_budgets forced_only_cfg Lsmall S (mkImage segs pc ph).
Proof.
  intros S segs pc ph Lbig Lsmall HLE H [sp brk mb rnd] inp Hen Hinp SWB.
  apply (must_exit_in_scfg_relim_closed forced_only_cfg S (mkImage segs pc ph) Lbig Lsmall (mkEntry sp brk mb rnd) inp HLE SWB).
  cbn [must_exit_in_scfg].
  destruct (H sp brk mb rnd inp Hen Hinp) as (T & HR & HS).
  exact (fo_exits_must_exit segs S _ T (srealizes_fo segs _ _ HR) HS (init_config_not_halted _ _ _ _ _ _ _ _ _)).
Qed.

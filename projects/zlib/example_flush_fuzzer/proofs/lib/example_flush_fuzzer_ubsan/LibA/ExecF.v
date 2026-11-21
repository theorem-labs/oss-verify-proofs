(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import Exec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.LibA Require Import AcctCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.


Definition footprint := Z -> nat -> Prop.

Definition acc_in (RNG : footprint) (acc : word * nat) : Prop :=
  RNG (bv_unsigned (fst acc)) (snd acc).

Definition rng (RNG : footprint) (lo : Z) (len : Z) : Prop :=
  0 <= lo /\ lo + len <= 2^64 /\
  forall b (j : nat), lo <= b -> b + Z.of_nat j <= lo + len -> RNG b j.










Section WithSegs.
Variable segs : list Segment.


Definition mstepF (RNG : footprint) (ms ms' : machine_state) : Prop :=
  ms_svc_pending ms = None /\
  exists accs, RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' accs)
          /\ Forall (acc_in RNG) accs.

Inductive mstepsF (RNG : footprint) : machine_state -> machine_state -> Prop :=
| mstepsF_refl : forall ms, mstepsF RNG ms ms
| mstepsF_cons : forall ms ms1 ms2, mstepF RNG ms ms1 -> mstepsF RNG ms1 ms2 -> mstepsF RNG ms ms2.

Definition evtF (RNG : footprint) (Q : machine_state -> Prop) (ms : machine_state) : Prop :=
  exists ms', mstepsF RNG ms ms' /\ Q ms'.




















Definition cstep (c c' : machine_state * Model) : Prop :=
  m_halted (snd c) = None /\ ms_svc_pending (fst c) = None /\
  mi_account_step segs (fst c) (snd c) = MachineOk c'.

Inductive csteps : machine_state * Model -> machine_state * Model -> Prop :=
| csteps_refl : forall c, csteps c c
| csteps_cons : forall c c1 c2, cstep c c1 -> csteps c1 c2 -> csteps c c2.









Definition footprint_ok (lz : list (word * word)) (AL : word -> Prop) (RNG : footprint) : Prop :=
  forall b (j k : nat), RNG b j -> (k < j)%nat -> 0 <= b < 2^64 -> page_ok lz AL (page_base_of (b + Z.of_nat k)).


Lemma accesses_ok_of_footprint : forall lz AL RNG accs,
  footprint_ok lz AL RNG -> Forall (acc_in RNG) accs -> accesses_ok lz AL accs.
Proof.
  intros lz AL RNG accs FOK F p Hp.
  apply accesses_pages_in in Hp as [[]|(a & n & k & Hin & Hk & ->)].
  apply (FOK (bv_unsigned a) n k).
  - apply (proj1 (Forall_forall _ _) F (a, n) Hin).
  - exact Hk.
  - pose proof (bv_unsigned_in_range 64 a). change (bv_modulus 64) with (2^64)%Z in H. lia.
Qed.

Lemma mstepF_lift : forall lz AL N RNG ms ms' mo,
  footprint_ok lz AL RNG -> ainv lz AL N mo -> m_halted mo = None ->
  mstepF RNG ms ms' ->
  exists mo', cstep (ms, mo) (ms', mo') /\ ainv lz AL N mo' /\ same_but_mat mo mo'.
Proof.
  intros lz AL N RNG ms ms' mo FOK INV Hh [Hs (accs & E & F)].
  destruct (mi_account_step_ok segs lz AL N ms mo ms' accs E INV (accesses_ok_of_footprint _ _ _ _ FOK F))
    as (mo' & Ha & INV' & SB).
  exists mo'. split; [|auto]. split; [exact Hh|]. split; [exact Hs|]. exact Ha.
Qed.

Theorem evtF_lift : forall lz AL N RNG Q ms mo,
  footprint_ok lz AL RNG -> ainv lz AL N mo -> m_halted mo = None ->
  evtF RNG Q ms ->
  exists ms' mo', csteps (ms, mo) (ms', mo') /\ Q ms' /\ ainv lz AL N mo' /\ same_but_mat mo mo'.
Proof.
  intros lz AL N RNG Q ms mo FOK INV Hh (msf & RUN & HQ).
  revert mo INV Hh. induction RUN as [ms0|ms0 ms1 ms2 ST RUN IH]; intros mo INV Hh.
  - exists ms0, mo. split; [constructor|]. split; [exact HQ|]. split; [exact INV| apply same_but_mat_refl].
  - destruct (mstepF_lift lz AL N RNG ms0 ms1 mo FOK INV Hh ST) as (mo1 & C1 & INV1 & SB1).
    destruct (IH HQ mo1 INV1) as (ms' & mo' & CS & HQ' & INV' & SB').
    { rewrite (same_but_mat_halted _ _ SB1). exact Hh. }
    exists ms', mo'. split; [econstructor; eauto|]. split; [exact HQ'|]. split; [exact INV'|].
    eapply same_but_mat_trans; eauto.
Qed.




End WithSegs.

Arguments mstepF segs RNG ms ms' /.


Definition fp_ok (lz : list (word * word)) (AL : word -> Prop) : footprint :=
  fun b j => forall k : nat, (k < j)%nat -> 0 <= b < 2^64 -> page_ok lz AL (page_base_of (b + Z.of_nat k)).








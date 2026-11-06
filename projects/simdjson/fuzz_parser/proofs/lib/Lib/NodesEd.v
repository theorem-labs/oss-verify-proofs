(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* The mmap and mprotect nodes read through the edited checkers of [MmEd]: a node step under [ACFG] is an outcome
   of the edited checker (for mmap outside the MAP_FIXED read-write corner), and an outcome of the edited checker
   is a node step. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Cfg MmEd.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import ITree Nodes.
Import ListNotations.

Lemma modeled_not_fixed_rw : forall p f o, mmap_modeled_b p f o = true -> mmap_fixed_rw_b p f o = false.
Proof.
  intros p f o H. unfold mmap_modeled_b in H. unfold mmap_fixed_rw_b.
  apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. apply Z.eqb_eq in H. rewrite H.
  replace (Z.eqb (MAP_PRIVATE + MAP_ANONYMOUS) (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)) with false by reflexivity.
  rewrite andb_false_r. reflexivity.
Qed.

Lemma noaccess_not_fixed_rw : forall p f o, mmap_noaccess_b p f o = true -> mmap_fixed_rw_b p f o = false.
Proof.
  intros p f o H. unfold mmap_noaccess_b in H. unfold mmap_fixed_rw_b.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply Z.eqb_eq in H. rewrite H. reflexivity.
Qed.

Lemma fixed_noaccess_not_fixed_rw : forall p f o, mmap_fixed_noaccess_b p f o = true -> mmap_fixed_rw_b p f o = false.
Proof.
  intros p f o H. unfold mmap_fixed_noaccess_b in H. unfold mmap_fixed_rw_b.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply Z.eqb_eq in H. rewrite H. reflexivity.
Qed.

Lemma nstep_mmap_ed : forall addr len prot flags mo eff mo' evs,
  nstep (NMmap addr len prot flags) mo eff mo' evs ->
  mmap_corner_free (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) mo eff ->
  mmap_noreserve_b (Z_to_bv 64 flags) = false /\
  check_mmap_ed (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs.
Proof.
  intros addr len prot flags mo eff mo' evs H Hcf. cbn [nstep node_input] in H.
  destruct H as (_ & Hnr & Hs & Hns). split; [exact Hnr|].
  apply check_syscall_ok_iff in Hs.
  exact (check_mmap_ed_of_ns
           (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags;
                            Z_to_bv 64 (-1); Z_to_bv 64 0]) mo eff mo' evs ltac:(reflexivity) Hs Hns Hcf).
Qed.

Lemma nstep_mmap_of_ed : forall addr len prot flags mo eff mo' evs,
  mmap_noreserve_b (Z_to_bv 64 flags) = false ->
  check_mmap_ed (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs ->
  nstep (NMmap addr len prot flags) mo eff mo' evs.
Proof.
  intros addr len prot flags mo eff mo' evs Hnr H.
  destruct (ns_of_check_mmap_ed
              (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags;
                               Z_to_bv 64 (-1); Z_to_bv 64 0]) mo eff mo' evs ltac:(reflexivity) H) as [Hc Hns].
  apply nstep_mmap_iff. split; [exact Hnr|]. split; [|exact Hns].
  rewrite check_syscall_mmap in Hc by reflexivity. exact Hc.
Qed.

Lemma nstep_mprotect_ed : forall addr len prot mo eff mo' evs,
  nstep (NMprotect addr len prot) mo eff mo' evs ->
  check_mprotect_ed (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo = CheckOk mo' evs.
Proof.
  intros addr len prot mo eff mo' evs H. cbn [nstep node_input] in H.
  destruct H as (_ & Hs & Hns). apply check_syscall_ok_iff in Hs.
  exact (check_mprotect_ed_of_ns (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot])
           mo eff mo' evs ltac:(reflexivity) Hs Hns).
Qed.

Lemma nstep_mprotect_of_ed : forall addr len prot mo eff mo' evs,
  check_mprotect_ed (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo = CheckOk mo' evs ->
  nstep (NMprotect addr len prot) mo eff mo' evs.
Proof.
  intros addr len prot mo eff mo' evs H.
  destruct (ns_of_check_mprotect_ed
              (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]) mo eff mo' evs ltac:(reflexivity) H)
    as [Hc Hns].
  apply nstep_mprotect_iff. split; [|exact Hns].
  rewrite check_syscall_mprotect in Hc by reflexivity. exact Hc.
Qed.

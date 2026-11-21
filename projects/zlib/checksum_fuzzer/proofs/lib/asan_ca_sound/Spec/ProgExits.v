(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Lib Require Import ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound Require Import TopLevel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.AS Require Import ShapeAlg ShapeHaltsA.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.LibA Require Import HaltsB.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Spec Require Import Prelim Monad STree Malloc Stdio Harness Adapter Driver Prog.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Malloc Require Import ProgDeps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section ProgExits.
Variable C : Z -> Prop.

Lemma ev_step_exits : forall atop e, mexits C (ev_step atop e) (fun _ => True).
Proof.
  intros atop e. destruct e; cbn [ev_step]; try apply mexits_unr.
  - apply mexits_if; intros _.
    + mex_auto.
    + apply mexits_seq; [apply mexits_get_true|]. intros s. apply mexits_seq; [apply mexits_sys_true; exact I|]. intros [|]; mex_auto.
  - apply mexits_if; intros _; [| apply mexits_if; intros _]; mex_auto.
  - mex_auto.
  - mex_auto.
Qed.

Lemma membed_exits : forall {R} atop (t : stree ev Z R), mexits C (membed atop t) (fun _ => True).
Proof.
  intros R atop t. induction t as [r|e k IH]; cbn [membed]; [apply mexits_ret; exact I|].
  apply mexits_seq; [apply ev_step_exits|]. intros z. apply IH.
Qed.

Lemma raw_malloc_exits : forall n, mexits C (raw_malloc n) (fun _ => True).
Proof.
  intros n. unfold raw_malloc. apply mexits_seq; [apply mexits_get_true|]. intros s.
  apply mexits_seq; [apply membed_exits|]. intros [st' p]. cbn beta iota. mex_auto.
Qed.

Lemma raw_free_exits : forall p, mexits C (raw_free p) (fun _ => True).
Proof.
  intros p. unfold raw_free. apply mexits_seq; [apply mexits_get_true|]. intros s.
  apply mexits_seq; [apply membed_exits|]. intros st'. mex_auto.
Qed.

Lemma io_diag_exits : forall d, mexits C (io_diag io d) (fun _ => True).
Proof. exact (io_S_diag_exits C ps_so set_so_ps). Qed.
Lemma io_emit_exits : forall v, mexits C (io_emit io v) (fun _ => True).
Proof. exact (io_S_emit_exits C ps_so set_so_ps). Qed.
Lemma io_exit_exits : mexits C (io_exit io) (fun _ => True).
Proof. exact (io_S_exit_exits C ps_so set_so_ps). Qed.

Lemma fuzz_one_exits : forall pl, mexits C (fuzz_one pl) (fun rc => rc = 0).
Proof. intros pl. unfold fuzz_one, Harness.fuzz_one. apply mexits_ret. reflexivity. Qed.

Lemma run_exits : forall cfg pl, mexits C (run cfg pl) (fun c => c = 0 \/ c = 2).
Proof.
  intros cfg pl. unfold run.
  exact (target_run_exits C raw_malloc raw_free fuzz_one (io_emit io) raw_malloc_exits raw_free_exits io_emit_exits fuzz_one_exits cfg pl).
Qed.

Lemma alloc_init_exits : forall b, mexits C (alloc_init b) (fun _ => True).
Proof. intros b. unfold alloc_init. apply target_alloc_init_exits. Qed.

Lemma alloc_count_exits : forall K : Z -> Prop, K 0 -> mexits C alloc_count (fun n => K (if n <? COUNT_MAX then n else COUNT_MAX)).
Proof. intros K HK. unfold alloc_count. apply target_alloc_count_exits. exact HK. Qed.

Lemma startup_exits : mexits C startup (fun _ => True).
Proof. unfold startup. mex_auto. Qed.

Definition code02 (c : Z) : Prop := c = 0 \/ c = 2.

Lemma main_model_exits02 : forall rs argv,
  mexits C (main_model io raw_malloc raw_free rs alloc_init run alloc_count argv) code02.
Proof.
  intros rs argv.
  apply (main_model_exits C io raw_malloc raw_free rs alloc_init run alloc_count
           io_diag_exits raw_malloc_exits raw_free_exits code02).
  - right; reflexivity.
  - exact alloc_init_exits.
  - exact run_exits.
  - apply alloc_count_exits. left; reflexivity.
Qed.
End ProgExits.

Lemma prog_with_exits : forall rs argv, mexits code02 (prog_with rs argv) (fun _ => True).
Proof.
  intros rs argv. unfold prog_with.
  apply mexits_seq; [apply startup_exits|]. intros _.
  apply (mexits_bind code02 _ _ code02); [apply main_model_exits02|]. intros code Hc.
  apply (exit_model_exits code02 io); [apply io_exit_exits| exact Hc].
Qed.

Theorem prog_exits_in : forall segs rs inp en, exits_in code02 (fun _ => True) (prog segs rs inp en).
Proof.
  intros segs rs inp en. unfold prog, prog_itree.
  eapply exits_in_mono; [| intros ? _; exact I].
  apply (exits_in_ebind code02 _ _ (fun _ => True)).
  eapply exits_in_mono; [exact (prog_with_exits rs (argv_Z (in_argv inp)) _)|].
  intros [|[v s]] H; cbn; [exact I|]. destruct v.
Qed.

Theorem prog_ends_in_02 : forall segs rs inp en mo,
  ends_in [Z_to_bv 64 0; Z_to_bv 64 2] (tree_traces (prog segs rs inp en) mo).
Proof.
  intros segs rs inp en mo.
  apply (exits_in_ends_in code02 _ (prog segs rs inp en) (fun _ => True)); [| apply prog_exits_in].
  intros c [-> | ->].
  - left. apply bv_eq. vm_compute. reflexivity.
  - right. left. apply bv_eq. vm_compute. reflexivity.
Qed.

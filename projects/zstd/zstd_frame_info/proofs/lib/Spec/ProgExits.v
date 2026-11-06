(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes HaltsTreeB.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad STree Malloc Stdio Adapter Driver Harness Prog MExits.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Definition EXITS02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HarnessX.
Context {St ptr : Type}.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable new_handler : Monad.M St Empty_set.
Variable S : list word.
Hypothesis MAL : forall n, mexits S (raw_malloc n).
Hypothesis FRE : forall p, mexits S (raw_free p).
Hypothesis NH : mexits S new_handler.

Lemma fuzz_malloc_exits : forall sz, mexits S (Harness.fuzz_malloc raw_malloc new_handler sz).
Proof. intros sz. unfold Harness.fuzz_malloc. mex. all: try (destruct a; mex). all: try (destruct a0). Qed.

Lemma free_opt_exits : forall p, mexits S (Harness.free_opt raw_free p).
Proof. intros p. unfold Harness.free_opt. mex. Qed.

Local Hint Resolve fuzz_malloc_exits free_opt_exits : mexits.

Lemma fuzz_one_exits : forall data, mexits S (Harness.fuzz_one raw_malloc raw_free new_handler data).
Proof. intros data. unfold Harness.fuzz_one. mex. Qed.

Lemma fuzz_one_post : forall data, mpost (fun rc => rc = 0) (Harness.fuzz_one raw_malloc raw_free new_handler data).
Proof. intros data. unfold Harness.fuzz_one. mpo. all: try reflexivity. Qed.
End HarnessX.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ProgX.
Context {rc : RunConst.runConstT}.

Lemma new_handler_exits : forall S, mexits S Prog.new_handler.
Proof. intros S. unfold Prog.new_handler. apply mexits_munr. Qed.

Lemma prog_fuzz_one_exits : forall S data, mexits S (Prog.fuzz_one data).
Proof.
  intros S data. unfold Prog.fuzz_one.
  (* [comment removed for export] *)
  apply fuzz_one_exits; first [apply raw_malloc_exits | apply raw_free_exits | apply new_handler_exits].
Qed.

Lemma prog_fuzz_one_post : forall data, mpost (fun r => r = 0) (Prog.fuzz_one data).
Proof. intros data. unfold Prog.fuzz_one. apply fuzz_one_post. Qed.

Lemma prog_run_exits : forall S c p, mexits S (Prog.run c p).
Proof.
  intros S c p. unfold Prog.run.
  apply target_run_exits; [apply raw_malloc_exits | apply raw_free_exits | apply prog_fuzz_one_exits |].
  intros v. unfold Prog.io. apply io_S_emit_exits.
Qed.

Lemma prog_run_post : forall c p, mpost (fun x => x = 0 \/ x = 2) (Prog.run c p).
Proof. intros c p. unfold Prog.run. apply target_run_post. apply prog_fuzz_one_post. Qed.

Lemma startup_exits : forall S, mexits S Prog.startup.
Proof. intros S. unfold Prog.startup. mex. Qed.

Lemma mask0_in : In (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255)) EXITS02.
Proof. left. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma mask2_in : In (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) EXITS02.
Proof. right; left. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma prog_with_exits : forall rs argv, mexits EXITS02 (Prog.prog_with rs argv).
Proof.
  intros rs argv. unfold Prog.prog_with.
  apply mexits_bind; [apply startup_exits|]. intros _.
  apply (mexits_bind_P EXITS02 (fun c => c = 0 \/ c = 2)).
  - unfold Prog.io. apply main_model_exits; unfold Prog.alloc_init, Prog.alloc_count;
      first [ apply io_S_diag_exits | apply io_S_emit_exits | apply io_S_exit_exits
            | apply raw_malloc_exits | apply raw_free_exits | apply target_alloc_init_exits
            | apply prog_run_exits | apply target_alloc_count_exits ].
  - unfold Prog.io. apply main_model_post; unfold Prog.alloc_count; [apply prog_run_post | apply target_alloc_count_post].
  - intros code [-> | ->]; apply exit_model_exits; [apply io_S_exit_exits | apply mask0_in | apply io_S_exit_exits | apply mask2_in].
Qed.

(* [comment removed for export] *)
Theorem prog_texits : forall segs rs inp en, texits nexit EXITS02 (Prog.prog segs rs inp en).
Proof.
  intros segs rs inp en. unfold Prog.prog, Prog.prog_itree, ebind.
  apply texits_bind; [apply prog_with_exits|]. intros [|[e s']]; [exact I | destruct e].
Qed.
End ProgX.

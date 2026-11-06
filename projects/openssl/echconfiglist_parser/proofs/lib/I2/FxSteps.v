(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Fixpoint rsteps (n : nat) (ms : machine_state) {struct n} : machine_result machine_state :=
  match n with
  | O => MachineOk ms
  | S n' =>
    match ms_svc_pending ms with
    | Some _ => MachineOk ms
    | None =>
      match RiscvSemantics.step segs ms with
      | MachineOk ms' => rsteps n' ms'
      | MachineFault => MachineFault
      | MachineUnmodeled => MachineUnmodeled
      end
    end
  end.

Lemma rsteps_svc_pending : forall n ms x8,
  ms_svc_pending ms = Some x8 -> rsteps n ms = MachineOk ms.
Proof. intros [|n] ms x8 H; cbn [rsteps]; [reflexivity | rewrite H; reflexivity]. Qed.

Lemma rsteps_add : forall n m ms,
  rsteps (n + m) ms =
    match rsteps n ms with
    | MachineOk ms' => rsteps m ms'
    | MachineFault => MachineFault
    | MachineUnmodeled => MachineUnmodeled
    end.
Proof.
  induction n as [|n IH]; intros m ms; [reflexivity|].
  cbn [Nat.add rsteps].
  destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
  - symmetry. apply (rsteps_svc_pending m ms x8 Hsvc).
  - destruct (RiscvSemantics.step segs ms) as [ms'| |]; [apply IH | reflexivity | reflexivity].
Qed.

Lemma rsteps_trans : forall n m ms1 ms2 ms3,
  rsteps n ms1 = MachineOk ms2 -> rsteps m ms2 = MachineOk ms3 ->
  rsteps (n + m) ms1 = MachineOk ms3.
Proof. intros n m ms1 ms2 ms3 H1 H2. rewrite rsteps_add, H1. exact H2. Qed.
End WithSegs.

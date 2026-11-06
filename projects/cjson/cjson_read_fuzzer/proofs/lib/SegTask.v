(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics State.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.

Lemma find_segment_top : forall segs x n, find_segment segs x n <> None ->
  exists seg, In seg segs /\ x + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|seg rest IH]; intros x n H; cbn [find_segment] in H; [congruence|].
  destruct (Z.of_N (seg_base seg) <=? x) eqn:E1; destruct (x + n <=? Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) eqn:E2; cbn [andb] in H.
  - exists seg. split; [left; reflexivity|]. apply Z.leb_le in E2. exact E2.
  - destruct (IH x n H) as (s & Hin & Hs). exists s. split; [right; exact Hin| exact Hs].
  - destruct (IH x n H) as (s & Hin & Hs). exists s. split; [right; exact Hin| exact Hs].
  - destruct (IH x n H) as (s & Hin & Hs). exists s. split; [right; exact Hin| exact Hs].
Qed.

Lemma segs_task_of_tops : forall segs (top : Z),
  forallb (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? top) segs = true -> top <= TASK_SIZE ->
  forall x, find_segment segs x 1 <> None -> x < TASK_SIZE.
Proof.
  intros segs top Htops Htop x H. destruct (find_segment_top _ _ _ H) as (seg & Hin & Hx).
  pose proof (proj1 (forallb_forall _ _) Htops seg Hin) as T. apply Z.leb_le in T. lia.
Qed.

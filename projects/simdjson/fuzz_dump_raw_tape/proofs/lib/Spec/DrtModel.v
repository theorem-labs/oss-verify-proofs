(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import String Ascii ZArith Bool List Lia.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim SjModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Target.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : target_ops M ptr.
Variable d : list Z.

Local Notation "x <- m ;; k" := (bind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bind ops m (fun _ => k)) (at level 61, right associativity).

Definition drt_free_nulls : M unit :=
  lib_free ops None ;;; lib_free ops None ;;; lib_free ops None ;;; lib_free ops None.

Definition drt_print : M unit :=
  ok <- cho ops ;;
  if ok =? 0 then ret ops tt
  else drt_free_nulls.

Definition drt_copy_phase (len : Z) (rc : option Z) : M unit :=
  if len <=? SJ_PADMAX then
    cp <- newnt ops (SJ_COPY len) ;;
    (match rc with
     | Some c => r <- newnt ops c ;; del ops r
     | None => ret ops tt
     end) ;;;
    drt_print ;;;
    del ops cp
  else ret ops tt.

Definition fuzz_one_with (rc : option Z) : M Z :=
  let len := zlength d in
  sb <- newnt ops (SJ_SBUF len) ;;
  tp <- newnt ops (SJ_TAPE len) ;;
  im <- newnt ops SJ_IMPL ;;
  ix <- newnt ops (SJ_IDX len) ;;
  oc <- newnt ops SJ_OC ;;
  ia <- newnt ops SJ_IA ;;
  drt_copy_phase len rc ;;;
  del ops sb ;;; del ops tp ;;; del ops ia ;;; del ops oc ;;; del ops ix ;;; del ops im ;;;
  ret ops 0.

Definition fuzz_one : M Z := fuzz_one_with (sj_root_copy d).

Fixpoint run_calls (n : nat) (rc : Z) : M Z :=
  match n with
  | O => ret ops rc
  | S n' =>
      rc' <- fuzz_one ;;
      out_stdout ops (Zdecimal rc' ++ [10]) ;;;
      run_calls n' rc'
  end.

Definition target_run (cfg : list Z) : M Z :=
  let c := match cfg with [] => 0 | b :: _ => b end in
  let calls := Z.to_nat (Z.land c 3 + 1) in
  let plen := zlength d in

  a <- (if plen =? 0 then ret ops (Some None)
        else r <- lib_malloc ops plen ;;
             ret ops (match r with None => None | Some p => Some (Some p) end)) ;;
  match a with
  | None => ret ops 2
  | Some owned =>
      rc <- run_calls calls 0 ;;
      lib_free ops owned ;;;
      ret ops (if rc =? 0 then 0 else 1)
  end.

End Target.

Module DrtRun.
Import SjRun.

Definition target_tree (cfg payload : list Z) : ttree Z := target_run tree_ops payload cfg.

Definition target_events (cfg payload : list Z) (coracle : list Z) : list tevent :=
  let '(evs, r) := run_tree_c (target_tree cfg payload) [] coracle 0%nat [] in
  evs ++ match r with Some rc => [TReturn rc] | None => [] end.

End DrtRun.

Module DrtModelTests.
Import SjRun DrtRun.

Example ex_small_ok :
  target_events [0] [91; 49; 44; 50; 93] [1]
  = [TMalloc 5 (Some 0%nat);
     TMalloc 128 (Some 1%nat); TMalloc 512 (Some 2%nat); TMalloc 96 (Some 3%nat); TMalloc 292 (Some 4%nat);
     TMalloc 8192 (Some 5%nat); TMalloc 1024 (Some 6%nat); TMalloc 69 (Some 7%nat);
     TFree None; TFree None; TFree None; TFree None;
     TFree (Some 7%nat);
     TFree (Some 1%nat); TFree (Some 2%nat); TFree (Some 6%nat); TFree (Some 5%nat); TFree (Some 4%nat); TFree (Some 3%nat);
     TStdout [48; 10];
     TFree (Some 0%nat);
     TReturn 0].
Proof. vm_compute. reflexivity. Qed.

Example ex_small_err :
  target_events [0] [91; 49; 44; 50; 93] [0]
  = [TMalloc 5 (Some 0%nat);
     TMalloc 128 (Some 1%nat); TMalloc 512 (Some 2%nat); TMalloc 96 (Some 3%nat); TMalloc 292 (Some 4%nat);
     TMalloc 8192 (Some 5%nat); TMalloc 1024 (Some 6%nat); TMalloc 69 (Some 7%nat);
     TFree (Some 7%nat);
     TFree (Some 1%nat); TFree (Some 2%nat); TFree (Some 6%nat); TFree (Some 5%nat); TFree (Some 4%nat); TFree (Some 3%nat);
     TStdout [48; 10];
     TFree (Some 0%nat);
     TReturn 0].
Proof. vm_compute. reflexivity. Qed.

Example ex_root_number :
  target_events [0] [32; 49; 50] [1]
  = [TMalloc 3 (Some 0%nat);
     TMalloc 128 (Some 1%nat); TMalloc 512 (Some 2%nat); TMalloc 96 (Some 3%nat); TMalloc 292 (Some 4%nat);
     TMalloc 8192 (Some 5%nat); TMalloc 1024 (Some 6%nat); TMalloc 67 (Some 7%nat);
     TMalloc 66 (Some 8%nat); TFree (Some 8%nat);
     TFree None; TFree None; TFree None; TFree None;
     TFree (Some 7%nat);
     TFree (Some 1%nat); TFree (Some 2%nat); TFree (Some 6%nat); TFree (Some 5%nat); TFree (Some 4%nat); TFree (Some 3%nat);
     TStdout [48; 10];
     TFree (Some 0%nat);
     TReturn 0].
Proof. vm_compute. reflexivity. Qed.

Example ex_two_calls_empty :
  target_events [1] [] [0; 0]
  = [TMalloc 128 (Some 0%nat); TMalloc 512 (Some 1%nat); TMalloc 96 (Some 2%nat); TMalloc 292 (Some 3%nat);
     TMalloc 8192 (Some 4%nat); TMalloc 1024 (Some 5%nat); TMalloc 64 (Some 6%nat);
     TFree (Some 6%nat);
     TFree (Some 0%nat); TFree (Some 1%nat); TFree (Some 5%nat); TFree (Some 4%nat); TFree (Some 3%nat); TFree (Some 2%nat);
     TStdout [48; 10];
     TMalloc 128 (Some 7%nat); TMalloc 512 (Some 8%nat); TMalloc 96 (Some 9%nat); TMalloc 292 (Some 10%nat);
     TMalloc 8192 (Some 11%nat); TMalloc 1024 (Some 12%nat); TMalloc 64 (Some 13%nat);
     TFree (Some 13%nat);
     TFree (Some 7%nat); TFree (Some 8%nat); TFree (Some 12%nat); TFree (Some 11%nat); TFree (Some 10%nat); TFree (Some 9%nat);
     TStdout [48; 10];
     TFree None;
     TReturn 0].
Proof. vm_compute. reflexivity. Qed.

End DrtModelTests.

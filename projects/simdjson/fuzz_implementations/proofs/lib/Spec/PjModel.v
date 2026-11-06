(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import String Ascii ZArith Bool List Lia.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition PJ_INLINE : Z := 64.

Definition PJ_OUTMAX (len : Z) : Z := 64 * len + 4096.

Definition PJ_CAPMAX (len : Z) : Z := 2 * PJ_OUTMAX len.

Definition PJ_FUEL : nat := 24.

Definition chain_ok (len cap z : Z) : bool := (2 * cap <=? z) && (z <=? PJ_CAPMAX len).

Section Target.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : target_ops M ptr.
Variable d : list Z.

Local Notation "x <- m ;; k" := (bind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bind ops m (fun _ => k)) (at level 61, right associativity).

Definition del_opt (b : option ptr) : M unit :=
  match b with Some p => del ops p | None => ret ops tt end.

Fixpoint pj_chain (fuel : nat) (len cap : Z) (blk : option ptr) : M (option ptr) :=
  match fuel with
  | O => ret ops blk
  | S f =>
      z <- cho ops ;;
      if chain_ok len cap z then
        b <- newnt ops z ;;
        del_opt blk ;;;
        pj_chain f len z (Some b)
      else ret ops blk
  end.

Definition pj_free_nulls : M unit :=
  lib_free ops None ;;; lib_free ops None ;;; lib_free ops None ;;; lib_free ops None.

Definition pj_print (len : Z) : M unit :=
  ok <- cho ops ;;
  if ok =? 0 then ret ops tt
  else
    blk <- pj_chain PJ_FUEL len PJ_INLINE None ;;
    del_opt blk ;;;
    pj_free_nulls.

Definition pj_copy_phase (len : Z) (rc : option Z) : M unit :=
  if len <=? SJ_PADMAX then
    cp <- newnt ops (SJ_COPY len) ;;
    (match rc with
     | Some c => r <- newnt ops c ;; del ops r
     | None => ret ops tt
     end) ;;;
    pj_print len ;;;
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
  pj_copy_phase len rc ;;;
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

Lemma chain_ok_spec : forall len cap z, chain_ok len cap z = true <-> 2 * cap <= z <= PJ_CAPMAX len.
Proof.
  intros len cap z. unfold chain_ok. rewrite andb_true_iff, !Z.leb_le. tauto.
Qed.

Lemma PJ_OUTMAX_pos : forall len, 0 <= len -> 4096 <= PJ_OUTMAX len.
Proof. intros len H. unfold PJ_OUTMAX. lia. Qed.

Lemma PJ_CAPMAX_bound : forall len, 0 <= len <= SJ_PADMAX -> 8192 <= PJ_CAPMAX len <= 134217728.
Proof. intros len H. unfold PJ_CAPMAX, PJ_OUTMAX, SJ_PADMAX in *. lia. Qed.

Lemma chain_ok_step : forall len cap z, 0 <= len <= SJ_PADMAX -> PJ_INLINE <= cap -> chain_ok len cap z = true ->
  PJ_INLINE <= z /\ 128 <= z <= 134217728 /\ cap + z <= 201326592.
Proof.
  intros len cap z Hl Hc H. apply chain_ok_spec in H. pose proof (PJ_CAPMAX_bound len Hl). unfold PJ_INLINE in *. lia.
Qed.

Lemma chain_ok_machine : forall len cap need, 0 <= len -> 0 <= cap -> cap < need -> need <= PJ_OUTMAX len ->
  chain_ok len cap (Z.max (2 * cap) need) = true.
Proof.
  intros len cap need Hl Hc Hn Hb. apply chain_ok_spec. unfold PJ_CAPMAX. lia.
Qed.

Lemma chain_fuel : forall len cap k, 0 <= len <= SJ_PADMAX -> 0 <= k -> 64 * 2 ^ k <= cap -> cap <= PJ_CAPMAX len -> k < 22.
Proof.
  intros len cap k Hl Hk Hc Hm. pose proof (PJ_CAPMAX_bound len Hl) as [_ HB].
  destruct (Z.lt_ge_cases k 22) as [?|Hge]; [assumption|exfalso].
  assert (2 ^ 22 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 22) with 4194304 in *. lia.
Qed.

Lemma pj_out_bound : forall len n sn i c size, 0 <= len <= SJ_PADMAX -> 8 * n <= SJ_TAPE len -> sn <= SJ_SBUF len ->
  1 <= i <= n -> 0 <= c <= sn -> size <= 41 * (i - 1) + 6 * c + 2 -> size <= PJ_OUTMAX len.
Proof.
  intros len n sn i c size Hl Hn Hs Hi Hc Hsz. unfold PJ_OUTMAX, SJ_TAPE, SJ_SBUF, sj_cap, SJ_PADMAX in *.
  destruct (Z.max_spec len 32) as [[Hlt E]|[Hge E]]; rewrite E in *.
  -
    change (roundup64 (32 + 3)) with 64 in Hn. change (roundup64 (5 * (32 / 3) + 64)) with 128 in Hs. lia.
  - pose proof (roundup64_lt (len + 3)) as R1. pose proof (roundup64_lt (5 * (len / 3) + 64)) as R2.
    assert (H3 : 3 * (len / 3) <= len) by (apply Z.mul_div_le; lia).
    set (q := len / 3) in *. set (r1 := roundup64 (len + 3)) in *. set (r2 := roundup64 (5 * q + 64)) in *. lia.
Qed.

Module PjRun.
Import SjRun.

Definition target_tree (cfg payload : list Z) : ttree Z := target_run tree_ops payload cfg.

Definition target_events (cfg payload : list Z) (coracle : list Z) : list tevent :=
  let '(evs, r) := run_tree_c (target_tree cfg payload) [] coracle 0%nat [] in
  evs ++ match r with Some rc => [TReturn rc] | None => [] end.

End PjRun.

Module PjModelTests.
Import SjRun PjRun.

Example ex_small_ok :
  target_events [0] [91; 49; 44; 50; 93] [1; 0]
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

Example ex_chain :
  target_events [0] [91; 49; 44; 50; 93] [1; 128; 256; 512; 0]
  = [TMalloc 5 (Some 0%nat);
     TMalloc 128 (Some 1%nat); TMalloc 512 (Some 2%nat); TMalloc 96 (Some 3%nat); TMalloc 292 (Some 4%nat);
     TMalloc 8192 (Some 5%nat); TMalloc 1024 (Some 6%nat); TMalloc 69 (Some 7%nat);
     TMalloc 128 (Some 8%nat);
     TMalloc 256 (Some 9%nat); TFree (Some 8%nat);
     TMalloc 512 (Some 10%nat); TFree (Some 9%nat);
     TFree (Some 10%nat);
     TFree None; TFree None; TFree None; TFree None;
     TFree (Some 7%nat);
     TFree (Some 1%nat); TFree (Some 2%nat); TFree (Some 6%nat); TFree (Some 5%nat); TFree (Some 4%nat); TFree (Some 3%nat);
     TStdout [48; 10];
     TFree (Some 0%nat);
     TReturn 0].
Proof. vm_compute. reflexivity. Qed.

Example ex_root_number :
  target_events [0] [32; 49; 50] [1; 0]
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

End PjModelTests.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import String Ascii ZArith Bool List Lia.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition IMP_VEC : Z := 8.

Definition IMP_SCAP0 : Z := 24.

Definition copy_ok (len S : Z) : bool := (0 <? S) && (S <=? PJ_CAPMAX len).

Section Target.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : target_ops M ptr.
Variable d : list Z.

Local Notation "x <- m ;; k" := (bind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bind ops m (fun _ => k)) (at level 61, right associativity).

Definition imp_static (v : option ptr) : M (option ptr) :=
  match v with
  | Some p => ret ops (Some p)
  | None => p <- newnt ops IMP_VEC ;; ret ops (Some p)
  end.

Definition imp_copy (len : Z) : M (option ptr) :=
  S <- cho ops ;;
  if copy_ok len S then b <- newnt ops S ;; ret ops (Some b) else ret ops None.

Definition imp_print (len : Z) : M unit :=
  ok <- cho ops ;;
  if ok =? 0 then ret ops tt
  else
    blk <- pj_chain ops PJ_FUEL len PJ_INLINE None ;;
    sblk <- pj_chain ops PJ_FUEL len IMP_SCAP0 None ;;
    del_opt ops blk ;;;
    cpy <- imp_copy len ;;
    del_opt ops sblk ;;;
    pj_free_nulls ops ;;;
    del_opt ops cpy.

Definition imp_copy_phase (len : Z) (rc : option Z) : M unit :=
  if len <=? SJ_PADMAX then
    cp <- newnt ops (SJ_COPY len) ;;
    (match rc with
     | Some c => r <- newnt ops c ;; del ops r
     | None => ret ops tt
     end) ;;;
    imp_print len ;;;
    del ops cp
  else ret ops tt.

Definition fuzz_one_with (rc : option Z) (v : option ptr) : M (Z * option ptr) :=
  let len := zlength d in
  v' <- imp_static v ;;
  sb <- newnt ops (SJ_SBUF len) ;;
  tp <- newnt ops (SJ_TAPE len) ;;
  im <- newnt ops SJ_IMPL ;;
  ix <- newnt ops (SJ_IDX len) ;;
  oc <- newnt ops SJ_OC ;;
  ia <- newnt ops SJ_IA ;;
  imp_copy_phase len rc ;;;
  del ops sb ;;; del ops tp ;;; del ops ia ;;; del ops oc ;;; del ops ix ;;; del ops im ;;;
  ret ops (0, v').

Definition fuzz_one (v : option ptr) : M (Z * option ptr) := fuzz_one_with (sj_root_copy d) v.

Fixpoint run_calls (n : nat) (rc : Z) (v : option ptr) : M (Z * option ptr) :=
  match n with
  | O => ret ops (rc, v)
  | S n' =>
      r <- fuzz_one v ;;
      out_stdout ops (Zdecimal (fst r) ++ [10]) ;;;
      run_calls n' (fst r) (snd r)
  end.

Definition target_run (cfg : list Z) : M (Z * option ptr) :=
  let c := match cfg with [] => 0 | b :: _ => b end in
  let calls := Z.to_nat (Z.land c 3 + 1) in
  let plen := zlength d in

  a <- (if plen =? 0 then ret ops (Some None)
        else r <- lib_malloc ops plen ;;
             ret ops (match r with None => None | Some p => Some (Some p) end)) ;;
  match a with
  | None => unreachable ops
  | Some owned =>
      r <- run_calls calls 0 None ;;
      lib_free ops owned ;;;
      ret ops ((if fst r =? 0 then 0 else 1), snd r)
  end.

End Target.

Lemma copy_ok_spec : forall len S, copy_ok len S = true <-> 0 < S <= PJ_CAPMAX len.
Proof. intros len S. unfold copy_ok. rewrite andb_true_iff, Z.ltb_lt, Z.leb_le. tauto. Qed.

Lemma copy_ok_machine : forall len L, 0 <= len -> 23 <= L <= PJ_OUTMAX len -> copy_ok len (8 * ((L + 8) / 8)) = true.
Proof.
  intros len L Hl HL. apply copy_ok_spec. unfold PJ_CAPMAX. pose proof (PJ_OUTMAX_pos len Hl).
  pose proof (Z.div_mod (L + 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (L + 8) 8 ltac:(lia)). lia.
Qed.

Lemma schain_ok_step : forall len cap z, 0 <= len <= SJ_PADMAX -> IMP_SCAP0 <= cap -> chain_ok len cap z = true ->
  IMP_SCAP0 <= z /\ 48 <= z <= 134217728 /\ cap + z <= 201326592.
Proof.
  intros len cap z Hl Hc H. apply chain_ok_spec in H. pose proof (PJ_CAPMAX_bound len Hl). unfold IMP_SCAP0 in *. lia.
Qed.

Lemma schain_fuel : forall len cap k, 0 <= len <= SJ_PADMAX -> 0 <= k -> 24 * 2 ^ k <= cap -> cap <= PJ_CAPMAX len -> k < 23.
Proof.
  intros len cap k Hl Hk Hc Hm. pose proof (PJ_CAPMAX_bound len Hl) as [_ HB].
  destruct (Z.lt_ge_cases k 23) as [?|Hge]; [assumption|exfalso].
  assert (2 ^ 23 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 23) with 8388608 in *. lia.
Qed.

Lemma schain_ok_machine : forall len cap L, 0 <= len -> IMP_SCAP0 <= cap -> cap - 1 < L -> L <= PJ_OUTMAX len ->
  chain_ok len cap (2 * cap) = true.
Proof.
  intros len cap L Hl Hc HL Hb. apply chain_ok_spec. unfold PJ_CAPMAX, IMP_SCAP0 in *. lia.
Qed.

Module ImpRun.
Import SjRun.

Definition target_tree (cfg payload : list Z) : ttree (Z * option nat) := target_run tree_ops payload cfg.

Definition target_events (cfg payload : list Z) (coracle : list Z) : list tevent * option (Z * option nat) :=
  run_tree_c (target_tree cfg payload) [] coracle 0%nat [].

End ImpRun.

Module ImpModelTests.
Import SjRun ImpRun.

Example ex_small_ok :
  target_events [0] (repeat 123 33) [1; 0; 48; 0; 48]
  = ([TMalloc 33 (Some 0%nat);
      TMalloc 8 (Some 1%nat);
      TMalloc 128 (Some 2%nat); TMalloc 512 (Some 3%nat); TMalloc 96 (Some 4%nat); TMalloc 292 (Some 5%nat);
      TMalloc 8192 (Some 6%nat); TMalloc 1024 (Some 7%nat); TMalloc 97 (Some 8%nat);
      TMalloc 48 (Some 9%nat);
      TMalloc 48 (Some 10%nat);
      TFree (Some 9%nat);
      TFree None; TFree None; TFree None; TFree None;
      TFree (Some 10%nat);
      TFree (Some 8%nat);
      TFree (Some 2%nat); TFree (Some 3%nat); TFree (Some 7%nat); TFree (Some 6%nat); TFree (Some 5%nat); TFree (Some 4%nat);
      TStdout [48; 10];
      TFree (Some 0%nat)],
     Some (0, Some 1%nat)).
Proof. vm_compute. reflexivity. Qed.

Example ex_two_calls_err :
  target_events [1] (repeat 34 20) [0; 0]
  = ([TMalloc 20 (Some 0%nat);
      TMalloc 8 (Some 1%nat);
      TMalloc 128 (Some 2%nat); TMalloc 512 (Some 3%nat); TMalloc 96 (Some 4%nat); TMalloc 292 (Some 5%nat);
      TMalloc 8192 (Some 6%nat); TMalloc 1024 (Some 7%nat); TMalloc 84 (Some 8%nat);
      TFree (Some 8%nat);
      TFree (Some 2%nat); TFree (Some 3%nat); TFree (Some 7%nat); TFree (Some 6%nat); TFree (Some 5%nat); TFree (Some 4%nat);
      TStdout [48; 10];
      TMalloc 128 (Some 9%nat); TMalloc 512 (Some 10%nat); TMalloc 96 (Some 11%nat); TMalloc 292 (Some 12%nat);
      TMalloc 8192 (Some 13%nat); TMalloc 1024 (Some 14%nat); TMalloc 84 (Some 15%nat);
      TFree (Some 15%nat);
      TFree (Some 9%nat); TFree (Some 10%nat); TFree (Some 14%nat); TFree (Some 13%nat); TFree (Some 12%nat); TFree (Some 11%nat);
      TStdout [48; 10];
      TFree (Some 0%nat)],
     Some (0, Some 1%nat)).
Proof. vm_compute. reflexivity. Qed.

Example ex_chains :
  target_events [0] (repeat 91 1024 ++ repeat 93 1024) [1; 128; 256; 512; 1024; 2048; 0; 48; 96; 192; 384; 768; 1536; 3072; 0; 2056]
  = ([TMalloc 2048 (Some 0%nat);
      TMalloc 8 (Some 1%nat);
      TMalloc 3520 (Some 2%nat); TMalloc 16896 (Some 3%nat); TMalloc 96 (Some 4%nat); TMalloc 8228 (Some 5%nat);
      TMalloc 8192 (Some 6%nat); TMalloc 1024 (Some 7%nat); TMalloc 2112 (Some 8%nat);
      TMalloc 128 (Some 9%nat);
      TMalloc 256 (Some 10%nat); TFree (Some 9%nat);
      TMalloc 512 (Some 11%nat); TFree (Some 10%nat);
      TMalloc 1024 (Some 12%nat); TFree (Some 11%nat);
      TMalloc 2048 (Some 13%nat); TFree (Some 12%nat);
      TMalloc 48 (Some 14%nat);
      TMalloc 96 (Some 15%nat); TFree (Some 14%nat);
      TMalloc 192 (Some 16%nat); TFree (Some 15%nat);
      TMalloc 384 (Some 17%nat); TFree (Some 16%nat);
      TMalloc 768 (Some 18%nat); TFree (Some 17%nat);
      TMalloc 1536 (Some 19%nat); TFree (Some 18%nat);
      TMalloc 3072 (Some 20%nat); TFree (Some 19%nat);
      TFree (Some 13%nat);
      TMalloc 2056 (Some 21%nat);
      TFree (Some 20%nat);
      TFree None; TFree None; TFree None; TFree None;
      TFree (Some 21%nat);
      TFree (Some 8%nat);
      TFree (Some 2%nat); TFree (Some 3%nat); TFree (Some 7%nat); TFree (Some 6%nat); TFree (Some 5%nat); TFree (Some 4%nat);
      TStdout [48; 10];
      TFree (Some 0%nat)],
     Some (0, Some 1%nat)).
Proof. vm_compute. reflexivity. Qed.

Example ex_empty :
  target_events [0] [] [0]
  = ([TMalloc 8 (Some 0%nat);
      TMalloc 128 (Some 1%nat); TMalloc 512 (Some 2%nat); TMalloc 96 (Some 3%nat); TMalloc 292 (Some 4%nat);
      TMalloc 8192 (Some 5%nat); TMalloc 1024 (Some 6%nat); TMalloc 64 (Some 7%nat);
      TFree (Some 7%nat);
      TFree (Some 1%nat); TFree (Some 2%nat); TFree (Some 6%nat); TFree (Some 5%nat); TFree (Some 4%nat); TFree (Some 3%nat);
      TStdout [48; 10];
      TFree None],
     Some (0, Some 0%nat)).
Proof. vm_compute. reflexivity. Qed.

End ImpModelTests.

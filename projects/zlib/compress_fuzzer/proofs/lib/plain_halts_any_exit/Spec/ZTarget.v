(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import String Ascii ZArith Bool List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim ZApi.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Export ZHarness.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record target_ops (M : Type -> Type) (ptr : Type) : Type := mkOps {
  ret : forall A : Type, A -> M A;
  bind : forall A B : Type, M A -> (A -> M B) -> M B;
  unreachable : forall A : Type, M A;
  lib_malloc : Z -> M (option ptr);
  lib_free : option ptr -> M unit;
  out_stderr : list Z -> M unit;
  out_stdout : list Z -> M unit;
  msg_store : list Z -> M unit;
  out_stderr_fw : list Z -> M unit
}.
Arguments mkOps {M ptr}.
Arguments ret {M ptr} _ {A}.
Arguments bind {M ptr} _ {A B}.
Arguments unreachable {M ptr} _ {A}.
Arguments lib_malloc {M ptr}.
Arguments lib_free {M ptr}.
Arguments out_stderr {M ptr}.
Arguments out_stdout {M ptr}.
Arguments msg_store {M ptr}.
Arguments out_stderr_fw {M ptr}.

Section Target.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : target_ops M ptr.
Variable za : zapi.

Local Notation "x <- m ;; k" := (bind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bind ops m (fun _ => k)) (at level 61, right associativity).

Definition deflate_init : M (option (ptr * ptr * ptr * ptr * ptr)) :=
  s <- lib_malloc ops (z_dstate za) ;;
  match s with
  | None => ret ops None
  | Some sp =>
      w <- lib_malloc ops (z_dwin za) ;;
      p <- lib_malloc ops (z_dprev za) ;;
      h <- lib_malloc ops (z_dhead za) ;;
      b <- lib_malloc ops (z_dpend za) ;;
      match w, p, h, b with
      | Some wp, Some pp, Some hp, Some bp => ret ops (Some (sp, wp, pp, hp, bp))
      | _, _, _, _ =>
          lib_free ops b ;;; lib_free ops h ;;; lib_free ops p ;;; lib_free ops w ;;;
          lib_free ops (Some sp) ;;;
          ret ops None
      end
  end.

Definition deflate_end (blk : ptr * ptr * ptr * ptr * ptr) : M unit :=
  let '(sp, wp, pp, hp, bp) := blk in
  lib_free ops (Some bp) ;;; lib_free ops (Some hp) ;;; lib_free ops (Some pp) ;;; lib_free ops (Some wp) ;;;
  lib_free ops (Some sp).

Definition test_deflate (d8 : list Z) (cl : Z) : M (list Z) :=
  r <- deflate_init ;;
  match r with
  | None => out_stderr ops (msg_err N_deflateInit Z_MEM_ERROR) ;;; ret ops (zrepeat 0 cl)
  | Some blk =>
      match test_deflate_pure za d8 cl with
      | None => unreachable ops
      | Some comprc => deflate_end blk ;;; ret ops comprc
      end
  end.

Inductive iloop_res : Type :=
| ILdone (is : IS za) (uc : list Z) (w : option ptr)
| ILerr (rc : Z) (w : option ptr).

Fixpoint iloop (fuel : nat) (comprc : list Z) (size cl : Z) (is : IS za) (uc : list Z) (w : option ptr) : M iloop_res :=
  match fuel with
  | O => unreachable ops
  | S f =>
      if (i_total_out za is <? size) && (i_total_in za is <? cl) then
        let wants := i_wants_window za comprc is && (match w with None => true | Some _ => false end) in
        r <- (if wants then lib_malloc ops (z_wsize za) else ret ops None) ;;
        let w' := if wants then r else w in
        let ok := if wants then (match r with Some _ => true | None => false end) else true in
        let '(is', bs, rc) := i_call za comprc is ok in
        if i_out_ok za size is bs then
          let uc' := zstore uc (i_total_out za is) bs in
          if rc =? Z_STREAM_END then ret ops (ILdone is' uc' w')
          else if rc =? Z_OK then (if i_next_ok za size cl is' then iloop f comprc size cl is' uc' w' else unreachable ops)
          else ret ops (ILerr rc w')
        else unreachable ops
      else ret ops (ILdone is uc w)
  end.

Definition test_inflate (d8 comprc : list Z) (size cl : Z) : M unit :=
  s <- lib_malloc ops (z_isize za) ;;
  match s with
  | None => out_stderr ops (msg_err N_inflateInit Z_MEM_ERROR)
  | Some sp =>
      r <- iloop (ZI_FUEL size cl) (norm8 comprc) size cl (i_init za) (zrepeat 0 size) None ;;
      match r with
      | ILerr rc w => out_stderr ops (msg_err N_inflate rc)
      | ILdone is uc w =>
          if i_end za is =? Z_OK then
            lib_free ops w ;;; lib_free ops (Some sp) ;;;
            (if zlist_eqb (norm8 uc) d8 then ret ops tt else out_stderr_fw ops MSG_BAD_INFLATE)
          else unreachable ops
      end
  end.

Definition fuzz_one (d : list Z) : M Z :=
  let size := zlength d in
  if (size <? 1) || (ZH_MAX <? size) then ret ops 0
  else
    let d8 := norm8 d in
    let cl := z_bound za size in
    c <- lib_malloc ops cl ;;
    match c with
    | None => ret ops 0
    | Some cp =>
        u <- lib_malloc ops size ;;
        match u with
        | None => ret ops 0
        | Some up =>
            comprc <- test_deflate d8 cl ;;
            test_inflate d8 comprc size cl ;;;
            lib_free ops (Some cp) ;;; lib_free ops (Some up) ;;;
            ret ops 0
        end
    end.

Fixpoint run_calls (d : list Z) (n : nat) (rc : Z) : M Z :=
  match n with
  | O => ret ops rc
  | S n' =>
      rc' <- fuzz_one d ;;
      out_stdout ops (Zdecimal rc' ++ [10]) ;;;
      run_calls d n' rc'
  end.

Definition target_run (d : list Z) (cfg : list Z) : M Z :=
  let c := match cfg with [] => 0 | b :: _ => b end in
  let calls := Z.to_nat (Z.land c 3 + 1) in
  let plen := zlength d in

  a <- (if plen =? 0 then ret ops (Some None)
        else r <- lib_malloc ops plen ;;
             ret ops (match r with None => None | Some p => Some (Some p) end)) ;;
  match a with
  | None => ret ops 2
  | Some owned =>
      rc <- run_calls d calls 0 ;;
      lib_free ops owned ;;;
      ret ops (if rc =? 0 then 0 else 1)
  end.

End Target.

Arguments ILdone {ptr za}.
Arguments ILerr {ptr za}.

Inductive tevent : Type :=
| TMalloc (n : Z) (r : option nat)
| TFree (p : option nat)
| TStderr (bytes : list Z)
| TStderrFw (bytes : list Z)
| TStdout (bytes : list Z)
| TReturn (rc : Z)
| TUnreachable.

Module ZRun.

Inductive ttree (A : Type) : Type :=
| TRet (a : A)
| TUnr
| TEv (e : tevent) (k : ttree A)
| TMallocQ (n : Z) (k : option nat -> ttree A).
Arguments TRet {A}.
Arguments TUnr {A}.
Arguments TEv {A}.
Arguments TMallocQ {A}.

Fixpoint tbind {A B} (m : ttree A) (f : A -> ttree B) : ttree B :=
  match m with
  | TRet a => f a
  | TUnr => TUnr
  | TEv e k => TEv e (tbind k f)
  | TMallocQ n k => TMallocQ n (fun r => tbind (k r) f)
  end.

Definition tree_ops : target_ops ttree nat :=
  mkOps (fun A (a : A) => TRet a)
        (fun A B m f => tbind m f)
        (fun A => TUnr)
        (fun n => TMallocQ n (fun r => TRet r))
        (fun p => TEv (TFree p) (TRet tt))
        (fun bs => TEv (TStderr bs) (TRet tt))
        (fun bs => TEv (TStdout bs) (TRet tt))
        (fun bs => TRet tt)
        (fun bs => TEv (TStderrFw bs) (TRet tt)).

Fixpoint run_tree {A} (t : ttree A) (oracle : list bool) (next : nat) (acc : list tevent)
  : list tevent * option A :=
  match t with
  | TRet a => (rev acc, Some a)
  | TUnr => (rev (TUnreachable :: acc), None)
  | TEv e k => run_tree k oracle next (e :: acc)
  | TMallocQ n k =>
      let '(ok, oracle') := match oracle with
                            | [] => (true, [])
                            | b :: o' => (b, o')
                            end in
      let r := if ok then Some next else None in
      run_tree (k r) oracle' (S next) (TMalloc n r :: acc)
  end.

Definition target_events (za : zapi) (cfg payload : list Z) (oracle : list bool) : list tevent :=
  let '(evs, r) := run_tree (target_run tree_ops za payload cfg) oracle 0%nat [] in
  evs ++ match r with Some rc => [TReturn rc] | None => [] end.

End ZRun.

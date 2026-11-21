(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import String Ascii ZArith Bool List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZTarget ZApiL ZHarnessL ZApiC ZHarnessC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section TargetC.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : target_ops M ptr.
Variable err_pieces : list (list Z) -> M unit.
Variable cb_exit : forall A : Type, M A.
Variable za : zapiC.

Local Notation "x <- m ;; k" := (bind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bind ops m (fun _ => k)) (at level 61, right associativity).

Definition deflate_initC : M (option (ptr * ptr * ptr * ptr * ptr)) :=
  s <- lib_malloc ops (zc_dstate za) ;;
  match s with
  | None => ret ops None
  | Some sp =>
      w <- lib_malloc ops (zc_dwin za) ;;
      p <- lib_malloc ops (zc_dprev za) ;;
      h <- lib_malloc ops (zc_dhead za) ;;
      b <- lib_malloc ops (zc_dpend za) ;;
      match w, p, h, b with
      | Some wp, Some pp, Some hp, Some bp => ret ops (Some (sp, wp, pp, hp, bp))
      | _, _, _, _ =>
          lib_free ops b ;;; lib_free ops h ;;; lib_free ops p ;;; lib_free ops w ;;;
          lib_free ops (Some sp) ;;;
          ret ops None
      end
  end.

Definition deflate_endC (blk : ptr * ptr * ptr * ptr * ptr) : M unit :=
  let '(sp, wp, pp, hp, bp) := blk in
  lib_free ops (Some bp) ;;; lib_free ops (Some hp) ;;; lib_free ops (Some pp) ;;; lib_free ops (Some wp) ;;;
  lib_free ops (Some sp).

(* The result is (output, *destLen, return code).  A deflateInit allocation failure returns Z_MEM_ERROR with
   *destLen = 0; otherwise the code is the one [c2_pure] computes. *)
Definition compress2M (N : Z) (src : list Z) (level : Z) : M (list Z * Z * Z) :=
  r <- deflate_initC ;;
  match r with
  | None => ret ops ([], 0, Z_MEM_ERROR)
  | Some blk =>
      match c2_pure za N src level with
      | None => unreachable ops
      | Some (out, tout, rc) => deflate_endC blk ;;; ret ops (out, tout, rc)
      end
  end.

Fixpoint u2_loopM (fuel : nat) (x : u2L za) (w : option ptr) : M (u2L za * Z * option ptr) :=
  match fuel with
  | O => unreachable ops
  | S f =>
      let wants := u2_wants za x && (match w with None => true | Some _ => false end) in
      r <- (if wants then lib_malloc ops (zc_wsize za) else ret ops None) ;;
      let w' := if wants then r else w in
      let ok := if wants then (match r with Some _ => true | None => false end) else true in
      match u2_stepP za ok x with
      | inl x' => u2_loopM f x' w'
      | inr (Some (x', err)) => ret ops (x', err, w')
      | inr None => unreachable ops
      end
  end.

(* The result is (output, *destLen, return code).  An inflateInit allocation failure returns Z_MEM_ERROR before
   [*destLen -= left], so *destLen keeps dlen; otherwise the code is the one [u2_result] computes (a failed window
   allocation gives Z_MEM_ERROR there, [zo_nomemC]). *)
Definition uncompress2M (dlen : Z) (src : list Z) : M (list Z * Z * Z) :=
  s <- lib_malloc ops (zc_isize za) ;;
  match s with
  | None => ret ops ([], dlen, Z_MEM_ERROR)
  | Some sp =>
      r <- u2_loopM (Z.to_nat (U2_FUEL dlen (zlength src))) (u2_x0 za dlen src) None ;;
      let '(xe, w) := r in
      let '(x, err) := xe in
      let '(out, tout, rc) := u2_result za dlen x err in
      lib_free ops w ;;; lib_free ops (Some sp) ;;;
      ret ops (out, tout, rc)
  end.

(* The issued binary is not built with harness patch 02: a failed assert calls __assert_fail, which aborts, and
   an abort is a death by signal, which the halting statement forbids.  So a failed check is a leaf the model
   must never reach ([TargetSafeR.fuzz_one_R] shows it is not, from the hypothesis that the harness's checks
   never fail), rather than the print-and-exit of the patched build.  The [let] keeps [err_pieces] and
   [cb_exit] among the definition's section variables, so every use of [fuzz_oneC] keeps its arguments. *)
Definition check_failM {A : Type} (k : ckfail) : M A :=
  let _ := (err_pieces, cb_exit) in unreachable ops.

Definition check_decompressM (data : list Z) (n cl cm flags : Z) : M unit :=
  k <- lib_malloc ops (n + 2) ;;
  match k with
  | None => ret ops tt
  | Some kp =>
      _ <- uncompress2M cl (zhdr_bytes cm flags ++ data) ;;
      lib_free ops (Some kp)
  end.

(* oss-fuzz #16582 (merged 945dd794): check_compress_level returns at once when compress2 or uncompress returns
   Z_MEM_ERROR, and check_decompress runs next, as on the path where both checks pass. *)
Definition fuzz_oneC (d : list Z) : M Z :=
  let size := zlength d in
  if (size <? ZC_MIN) || (ZC_MAX <? size) then ret ops 0
  else
    let d8 := norm8 d in
    let data := zdrop 3 d8 in
    let n := size - 3 in
    let cl := zc_bound za n in
    c <- lib_malloc ops cl ;;
    match c with
    | None => ret ops 0
    | Some cp =>
        u <- lib_malloc ops n ;;
        match u with
        | None => lib_free ops (Some cp) ;;; ret ops 0
        | Some up =>

            rc <- compress2M cl data (sel_level d8) ;;
            let '(cout, clen, crc) := rc in
            if crc =? Z_MEM_ERROR then
              check_decompressM data n cl (sel_cm d8) (sel_flags d8) ;;;
              lib_free ops (Some cp) ;;; lib_free ops (Some up) ;;;
              ret ops 0
            else
            ru <- uncompress2M n (norm8 cout) ;;
            let '(uout, ulen, urc) := ru in
            if urc =? Z_MEM_ERROR then
              check_decompressM data n cl (sel_cm d8) (sel_flags d8) ;;;
              lib_free ops (Some cp) ;;; lib_free ops (Some up) ;;;
              ret ops 0
            else if negb (n =? ulen) then check_failM CK1
            else if negb (zlist_eqb data (norm8 (bufC uout n))) then check_failM CK2
            else
              check_decompressM data n cl (sel_cm d8) (sel_flags d8) ;;;
              lib_free ops (Some cp) ;;; lib_free ops (Some up) ;;;
              ret ops 0
        end
    end.

Fixpoint run_callsC (d : list Z) (n : nat) (rc : Z) : M Z :=
  match n with
  | O => ret ops rc
  | S n' =>
      rc' <- fuzz_oneC d ;;
      out_stdout ops (Zdecimal rc' ++ [10]) ;;;
      run_callsC d n' rc'
  end.

Definition target_runC (d : list Z) (cfg : list Z) : M Z :=
  let c := match cfg with [] => 0 | b :: _ => b end in
  let calls := Z.to_nat (Z.land c 3 + 1) in
  let plen := zlength d in
  a <- (if plen =? 0 then ret ops (Some None)
        else r <- lib_malloc ops plen ;;
             ret ops (match r with None => None | Some p => Some (Some p) end)) ;;
  match a with
  | None => ret ops 2
  | Some owned =>
      rc <- run_callsC d calls 0 ;;
      lib_free ops owned ;;;
      ret ops (if rc =? 0 then 0 else 1)
  end.

End TargetC.

Module ZRunC.
Import ZRun.

Definition err_pieces_t (ps : list (list Z)) : ttree unit := TEv (TStderr (List.concat ps)) (TRet tt).
Definition cb_exit_t (A : Type) : ttree A := TEv (TReturn 77) TUnr.
Definition target_eventsC (za : zapiC) (cfg payload : list Z) (oracle : list bool) : list tevent :=
  let '(evs, r) := run_tree (target_runC tree_ops err_pieces_t cb_exit_t za payload cfg) oracle 0%nat [] in
  evs ++ match r with Some rc => [TReturn rc] | None => [] end.
End ZRunC.

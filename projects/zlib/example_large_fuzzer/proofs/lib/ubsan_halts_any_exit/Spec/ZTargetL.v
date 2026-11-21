(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import String Ascii ZArith Bool List Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZTarget ZApiL ZHarnessL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section TargetL.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : target_ops M ptr.
Variable za : zapiL.

Local Notation "x <- m ;; k" := (bind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bind ops m (fun _ => k)) (at level 61, right associativity).

Definition deflate_initL : M (option (ptr * ptr * ptr * ptr * ptr)) :=
  s <- lib_malloc ops (zl_dstate za) ;;
  match s with
  | None => ret ops None
  | Some sp =>
      w <- lib_malloc ops (zl_dwin za) ;;
      p <- lib_malloc ops (zl_dprev za) ;;
      h <- lib_malloc ops (zl_dhead za) ;;
      b <- lib_malloc ops (zl_dpend za) ;;
      match w, p, h, b with
      | Some wp, Some pp, Some hp, Some bp => ret ops (Some (sp, wp, pp, hp, bp))
      | _, _, _, _ =>
          lib_free ops b ;;; lib_free ops h ;;; lib_free ops p ;;; lib_free ops w ;;;
          lib_free ops (Some sp) ;;;
          ret ops None
      end
  end.

Definition deflate_endL (blk : ptr * ptr * ptr * ptr * ptr) : M unit :=
  let '(sp, wp, pp, hp, bp) := blk in
  lib_free ops (Some bp) ;;; lib_free ops (Some hp) ;;; lib_free ops (Some pp) ;;; lib_free ops (Some wp) ;;;
  lib_free ops (Some sp).

Definition emit_dexit (e : dexitL) : M unit :=
  match e with
  | DXL_ok => ret ops tt
  | DXL_err w rc => out_stderr ops (msg_err w rc)
  | DXL_greedy => out_stderr_fw ops MSGL_GREEDY
  | DXL_finish => out_stderr_fw ops MSGL_FINISH
  end.

Definition test_large_deflateM (N diff : Z) : M (list Z * Z) :=
  r <- deflate_initL ;;
  match r with
  | None => out_stderr ops (msg_err NL_deflateInit Z_MEM_ERROR) ;;; ret ops (zrepeat 0 N, diff)
  | Some blk =>
      let '(r1, ended) := test_large_deflate_pure za N in
      let '(r2, od) := r1 in
      let '(comprc, e) := r2 in
      let diff' := match od with Some d => d | None => diff end in
      (if ended then deflate_endL blk else ret ops tt) ;;;
      emit_dexit e ;;;
      ret ops (comprc, diff')
  end.

Inductive iloopL_res : Type :=
| ILLdone (is : ISL za) (w : option ptr)
| ILLerr (rc : Z) (w : option ptr).

Fixpoint iloopL (fuel : nat) (N : Z) (comprc : list Z) (is : ISL za) (w : option ptr) : M iloopL_res :=
  match fuel with
  | O => unreachable ops
  | S f =>
      let wants := i_wantsL za N comprc is && (match w with None => true | Some _ => false end) in
      r <- (if wants then lib_malloc ops (zl_wsize za) else ret ops None) ;;
      let w' := if wants then r else w in
      let ok := if wants then (match r with Some _ => true | None => false end) else true in
      let '(is', bs, rc) := i_callL za N comprc is ok in
      if rc =? Z_STREAM_END then ret ops (ILLdone is' w')
      else if rc =? Z_OK then iloopL f N comprc is' w'
      else ret ops (ILLerr rc w')
  end.

Definition test_large_inflateM (N : Z) (comprc : list Z) (diff : Z) : M unit :=
  s <- lib_malloc ops (zl_isize za) ;;
  match s with
  | None => out_stderr ops (msg_err NL_inflateInit Z_MEM_ERROR)
  | Some sp =>
      r <- iloopL (Z.to_nat (ZIL_FUEL N)) N (norm8 comprc) (il_init za) None ;;
      match r with
      | ILLerr rc w => out_stderr ops (msg_err NL_inflate rc)
      | ILLdone is w =>
          lib_free ops w ;;; lib_free ops (Some sp) ;;;
          if il_end za is =? Z_OK then
            (if il_total_out za is =? 2 * N + diff then ret ops tt else out_stderr ops (msgl_bad (il_total_out za is)))
          else out_stderr ops (msg_err NL_inflateEnd (il_end za is))
      end
  end.

Definition fuzz_oneL (d : list Z) (diff : Z) : M (Z * Z) :=
  let size := zlength d in
  if (size <? 1) || (ZL_MAX <? size) then ret ops (0, diff)
  else
    let N := NofL size in
    c <- lib_malloc ops N ;;
    u <- lib_malloc ops N ;;
    match c, u with
    | Some cp, Some up =>
        rd <- test_large_deflateM N diff ;;
        let '(comprc, diff') := rd in
        test_large_inflateM N comprc diff' ;;;
        lib_free ops (Some cp) ;;; lib_free ops (Some up) ;;;
        ret ops (0, diff')
    | _, _ =>
        lib_free ops c ;;; lib_free ops u ;;;
        ret ops (0, diff)
    end.

Fixpoint run_callsL (d : list Z) (n : nat) (rc diff : Z) : M Z :=
  match n with
  | O => ret ops rc
  | S n' =>
      r <- fuzz_oneL d diff ;;
      let '(rc', diff') := r in
      out_stdout ops (Zdecimal rc' ++ [10]) ;;;
      run_callsL d n' rc' diff'
  end.

Definition target_runL (d : list Z) (cfg : list Z) : M Z :=
  let c := match cfg with [] => 0 | b :: _ => b end in
  let calls := Z.to_nat (Z.land c 3 + 1) in
  let plen := zlength d in
  a <- (if plen =? 0 then ret ops (Some None)
        else r <- lib_malloc ops plen ;;
             ret ops (match r with None => None | Some p => Some (Some p) end)) ;;
  match a with
  | None => ret ops 2
  | Some owned =>
      rc <- run_callsL d calls 0 0 ;;
      lib_free ops owned ;;;
      ret ops (if rc =? 0 then 0 else 1)
  end.

End TargetL.

Arguments ILLdone {ptr za}.
Arguments ILLerr {ptr za}.

Definition target_eventsL (za : zapiL) (cfg payload : list Z) (oracle : list bool) : list tevent :=
  let '(evs, r) := ZRun.run_tree (target_runL ZRun.tree_ops za payload cfg) oracle 0%nat [] in
  evs ++ match r with Some rc => [TReturn rc] | None => [] end.

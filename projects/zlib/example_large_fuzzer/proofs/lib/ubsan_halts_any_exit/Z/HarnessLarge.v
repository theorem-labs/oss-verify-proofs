(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateParams.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState Inftrees InflateFast InflateArms Inflate HarnessSmall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition kMaxSizeL : Z := 524288.
Definition NofL (size : Z) : Z := 100 + 3 * size.

Definition WL_deflateInit : Z := 0.
Definition WL_deflate1 : Z := 1.
Definition WL_deflate2 : Z := 2.
Definition WL_deflate3 : Z := 3.
Definition WL_deflateEnd : Z := 4.
Definition WL_inflateInit : Z := 5.
Definition WL_inflate : Z := 6.
Definition WL_inflateEnd : Z := 7.

Inductive hexitL : Set :=
| HXL_ok
| HXL_err (which rc : Z)
| HXL_greedy
| HXL_finish
| HXL_bad (tout : Z)
| HXL_fuel.


Definition dinit9_run (chs : DCH) (z : zstrm) : option (option deflate_state * ZRet) :=
  dpure (deflateInit2_m dhooks (zc_none z) 9 Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY) chs.

Record dphase : Type := mkDP { dp_s : deflate_state; dp_z : zstrm; dp_out_rev : list Z; dp_nout : Z; dp_rest : list Z }.

Definition dp_apply (x : dphase) (s' : deflate_state) (zr : ZRet) (inp : list Z) : dphase :=
  mkDP s' (zr_strm zr) (rev_append (zr_output zr) (dp_out_rev x)) (dp_nout x + zlength (zr_output zr)) (zskipn (zr_consumed zr) inp).

Definition dcallL (N flush : Z) (inp : list Z) (x : dphase) : dphase * Z :=
  let zc := mkZCall inp (N - dp_nout x) (dp_z x) in
  let '(s', zr) := deflate_m (dp_s x) zc flush in
  (dp_apply x s' zr inp, zr_rc zr).

Definition pcallL (N level strategy : Z) (x : dphase) : dphase * Z :=
  let zc := mkZCall (dp_rest x) (N - dp_nout x) (dp_z x) in
  let '(s', zr) := deflateParams_m (dp_s x) zc level strategy in
  (dp_apply x s' zr (dp_rest x), zr_rc zr).

Definition tdeflL_body (N : Z) (s0 : deflate_state) (z0 : zstrm) : dphase * hexitL * option Z :=
  let zeros := zrepeat 0 N in
  let x0 := mkDP s0 z0 [] 0 [] in
  let '(x1, rc1) := dcallL N Z_NO_FLUSH zeros x0 in
  if negb (rc1 =? Z_OK) then (x1, HXL_err WL_deflate1 rc1, None)
  else if negb (zlength (dp_rest x1) =? 0) then (x1, HXL_greedy, None)
  else
    let '(x2, _) := pcallL N 0 Z_DEFAULT_STRATEGY x1 in
    let diff := dp_nout x2 in
    let comprc := rev_append (dp_out_rev x2) [] in
    let '(x3, rc3) := dcallL N Z_NO_FLUSH comprc x2 in
    if negb (rc3 =? Z_OK) then (x3, HXL_err WL_deflate2 rc3, Some diff)
    else
      let '(x4, _) := pcallL N 9 Z_FILTERED x3 in
      let '(x5, rc5) := dcallL N Z_NO_FLUSH zeros x4 in
      if negb (rc5 =? Z_OK) then (x5, HXL_err WL_deflate3 rc5, Some diff)
      else
        let '(x6, rc6) := dcallL N Z_FINISH (dp_rest x5) x5 in
        if negb (rc6 =? Z_STREAM_END) then (x6, HXL_finish, Some diff)
        else
          let rc := dend_rc (dp_s x6) in
          (x6, (if rc =? Z_OK then HXL_ok else HXL_err WL_deflateEnd rc), Some diff).

Definition comprL_of (x : dphase) (N : Z) : list Z := pad_to (rev_append (dp_out_rev x) []) N.


Record iphase : Type := mkIP { ip_s : inflate_state; ip_z : zstrm; ip_calls : Z; ip_asked : bool }.

Definition icallL (N : Z) (comprc : list Z) (wans : option (blk * (Z -> Z))) (x : iphase) : iphase * Z :=
  let zc := mkZCall (zskipn (zs_total_in (ip_z x)) comprc) N (ip_z x) in
  let '(r, asked) := inflate_p wans (ip_s x) zc Z_NO_FLUSH in
  let '(s', zr) := r in
  (mkIP s' (zr_strm zr) (ip_calls x + 1) (ip_asked x || asked), zr_rc zr).

Definition il_stepL (N : Z) (comprc : list Z) (wans : option (blk * (Z -> Z))) (x : iphase) : iphase + (iphase * hexitL) :=
  let '(x', rc) := icallL N comprc wans x in
  if rc =? Z_STREAM_END then inr (x', HXL_ok)
  else if rc =? Z_OK then inl x'
  else inr (x', HXL_err WL_inflate rc).

Definition ZIL_FUEL (N : Z) : Z := 2100 * N + 10000.

Definition il_runL (N : Z) (comprc : list Z) (wans : option (blk * (Z -> Z))) (x : iphase) : iphase * hexitL :=
  iterZ (ZIL_FUEL N) (il_stepL N comprc wans) (fun x => (x, HXL_fuel)) x.

Definition tinflL_body (N : Z) (wans : option (blk * (Z -> Z))) (comprc : list Z) (s0 : inflate_state) (z0 : zstrm) : iphase * hexitL :=
  let '(x1, e1) := il_runL N comprc wans (mkIP s0 z0 0 false) in
  match e1 with
  | HXL_ok => let rc := iend_rc (ip_s x1) in (x1, if rc =? Z_OK then HXL_ok else HXL_err WL_inflateEnd rc)
  | _ => (x1, e1)
  end.


Definition msg_nameL (which : Z) : list Z :=
  if which =? WL_deflateInit then [100;101;102;108;97;116;101;73;110;105;116]
  else if which =? WL_deflate1 then [100;101;102;108;97;116;101;32;108;97;114;103;101;32;49]
  else if which =? WL_deflate2 then [100;101;102;108;97;116;101;32;108;97;114;103;101;32;50]
  else if which =? WL_deflate3 then [100;101;102;108;97;116;101;32;108;97;114;103;101;32;51]
  else if which =? WL_deflateEnd then [100;101;102;108;97;116;101;69;110;100]
  else if which =? WL_inflateInit then [105;110;102;108;97;116;101;73;110;105;116]
  else if which =? WL_inflate then [108;97;114;103;101;32;105;110;102;108;97;116;101]
  else [105;110;102;108;97;116;101;69;110;100].
Definition err_msgL (which rc : Z) : list Z := msg_nameL which ++ [32;101;114;114;111;114;58;32] ++ dec_int rc ++ [10].
Definition greedy_msgL : list Z := [100;101;102;108;97;116;101;32;110;111;116;32;103;114;101;101;100;121;10].
Definition finish_msgL : list Z :=
  [100;101;102;108;97;116;101;32;108;97;114;103;101;32;115;104;111;117;108;100;32;114;101;112;111;114;116;32;90;95;83;84;82;69;65;77;95;69;78;68;10].
Definition bad_msgL (tout : Z) : list Z := [98;97;100;32;108;97;114;103;101;32;105;110;102;108;97;116;101;58;32] ++ dec_digits 20 tout [] ++ [10].

Definition exit_msgL (e : hexitL) : list Z :=
  match e with
  | HXL_err w rc => err_msgL w rc
  | HXL_greedy => greedy_msgL
  | HXL_finish => finish_msgL
  | HXL_bad tout => bad_msgL tout
  | _ => []
  end.


Record large_run : Type := mkLR {
  lr_N : Z;
  lr_dexit : hexitL; lr_dphase : option dphase;
  lr_diff : Z;
  lr_compr : list Z;
  lr_iexit : hexitL; lr_iphase : option iphase;
  lr_stderr : list Z }.

Definition large_run_of (g : N -> Z -> Z) (gi gw : Z -> Z) (size diff_prev : Z) : large_run :=
  let N := NofL size in
  let '(dexit, dp, odiff) :=
    match dinit9_run (dchs g) zstrm0 with
    | Some (Some s0, zr) =>
        if zr_rc zr =? Z_OK then let '(r, od) := tdeflL_body N s0 (zr_strm zr) in let '(x, e) := r in (e, Some x, od)
        else (HXL_err WL_deflateInit (zr_rc zr), None, None)
    | Some (None, zr) => (HXL_err WL_deflateInit (zr_rc zr), None, None)
    | None => (HXL_fuel, None, None)
    end in
  let diff := match odiff with Some d => d | None => diff_prev end in
  let compr := match dp with Some x => comprL_of x N | None => zrepeat 0 N end in
  let '(iexit, ip) :=
    match iinit_run [Some (5%N, gi)] zstrm0 with
    | Some (Some s0, zr) =>
        if zr_rc zr =? Z_OK then
          let '(x, e) := tinflL_body N (Some (6%N, gw)) compr s0 (zr_strm zr) in
          match e with
          | HXL_ok => let tout := zs_total_out (ip_z x) in
                      (if tout =? 2 * N + diff then HXL_ok else HXL_bad tout, Some x)
          | _ => (e, Some x)
          end
        else (HXL_err WL_inflateInit (zr_rc zr), None)
    | Some (None, zr) => (HXL_err WL_inflateInit (zr_rc zr), None)
    | None => (HXL_fuel, None)
    end in
  mkLR N dexit dp diff compr iexit ip (exit_msgL dexit ++ exit_msgL iexit).

Definition harness_large_call (size diff_prev : Z) : list Z * Z :=
  if (size <? 1) || (kMaxSizeL <? size) then ([], diff_prev)
  else let r := large_run_of (fun _ => g0) g0 g0 size diff_prev in (lr_stderr r, lr_diff r).

Fixpoint harness_large_msgs_from (size : Z) (calls : nat) (diff : Z) : list (list Z) :=
  match calls with
  | O => []
  | S k => let '(m, diff') := harness_large_call size diff in m :: harness_large_msgs_from size k diff'
  end.
Definition harness_large_msgs (size : Z) (calls : nat) : list (list Z) := harness_large_msgs_from size calls 0.

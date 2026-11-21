(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InflateState Inftrees InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateFast OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition kMaxSize : Z := 1048576.
Definition W_deflateInit : Z := 0.
Definition W_deflate1 : Z := 1.
Definition W_deflate2 : Z := 2.
Definition W_deflateEnd : Z := 3.
Definition W_inflateInit : Z := 4.
Definition W_inflate : Z := 5.
Definition W_inflateEnd : Z := 6.

Inductive hexit : Set := HX_ok | HX_err (which rc : Z) | HX_fuel.

Definition g0 : Z -> Z := fun _ => 0.

Definition DCH : Type := list (option (blk * (Z -> Z))).
Definition dhooks : zhooks DCH :=
  mkHooks (fun _ _ => fun chs : DCH => match chs with
                                      | [] => MRet (None, [])
                                      | c :: chs' => MRet (c, chs')
                                      end)
          (fun _ => fun chs : DCH => MRet (tt, chs)).
Definition dpure {A} (m : SM DCH A) (chs : DCH) : option A :=
  match m chs with MRet p => Some (fst p) | _ => None end.


Definition zc_none (z : zstrm) : ZCall := mkZCall [] 0 z.
Definition dinit_run (chs : DCH) (z : zstrm) : option (option deflate_state * ZRet) :=
  dpure (deflateInit2_m dhooks (zc_none z) Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY) chs.

Definition dchs (g : N -> Z -> Z) : DCH :=
  [Some (0%N, g 0%N); Some (1%N, g 1%N); Some (2%N, g 2%N); Some (3%N, g 3%N); Some (4%N, g 4%N)].

Record dloop : Type := mkDL {
  dl_s : deflate_state; dl_z : zstrm; dl_rest : list Z; dl_ain : Z; dl_out_rev : list Z; dl_calls : Z }.

Definition d_call (flush : Z) (x : dloop) : dloop * Z :=
  let ain := if flush =? Z_NO_FLUSH then 1 else dl_ain x in
  let zc := mkZCall (zfirstn ain (dl_rest x)) 1 (dl_z x) in
  let '(s', zr) := deflate_m (dl_s x) zc flush in
  (mkDL s' (zr_strm zr) (zskipn (zr_consumed zr) (dl_rest x)) (ain - zr_consumed zr)
        (rev_append (zr_output zr) (dl_out_rev x)) (dl_calls x + 1), zr_rc zr).

Definition dl1_step (n cb : Z) (x : dloop) : dloop + (dloop * hexit) :=
  if negb (zs_total_in (dl_z x) =? n) && (zs_total_out (dl_z x) <? cb) then
    let '(x', rc) := d_call Z_NO_FLUSH x in
    if rc =? Z_OK then inl x' else inr (x', HX_err W_deflate1 rc)
  else inr (x, HX_ok).
Definition dl2_step (x : dloop) : dloop + (dloop * hexit) :=
  let '(x', rc) := d_call Z_FINISH x in
  if rc =? Z_STREAM_END then inr (x', HX_ok)
  else if rc =? Z_OK then inl x' else inr (x', HX_err W_deflate2 rc).

Definition d_fuel (cb : Z) : Z := 2 * cb + 16.

Definition dl1_run (n cb : Z) (x : dloop) : dloop * hexit :=
  iterZ (d_fuel cb) (dl1_step n cb) (fun x => (x, HX_fuel)) x.
Definition dl2_run (cb : Z) (x : dloop) : dloop * hexit :=
  iterZ (d_fuel cb) dl2_step (fun x => (x, HX_fuel)) x.

Definition dend_rc (s : deflate_state) : Z :=
  if deflateStateCheck s then Z_STREAM_ERROR
  else if ds_status s =? BUSY_STATE then Z_DATA_ERROR else Z_OK.

Definition tdefl_body (d : list Z) (cb : Z) (s0 : deflate_state) (z0 : zstrm) : dloop * hexit :=
  let x0 := mkDL s0 z0 d 0 [] 0 in
  let '(x1, e1) := dl1_run (zlength d) cb x0 in
  match e1 with
  | HX_ok =>
      let '(x2, e2) := dl2_run cb x1 in
      match e2 with
      | HX_ok => let rc := dend_rc (dl_s x2) in
                 (x2, if rc =? Z_OK then HX_ok else HX_err W_deflateEnd rc)
      | _ => (x2, e2)
      end
  | _ => (x1, e1)
  end.

Definition pad_to (l : list Z) (len : Z) : list Z := l ++ zrepeat 0 (len - zlength l).
Definition compr_of (x : dloop) (cb : Z) : list Z := pad_to (rev_append (dl_out_rev x) []) cb.


Definition iinit_run (chs : DCH) (z : zstrm) : option (option inflate_state * ZRet) :=
  dpure (inflateInit2_m ivar_ref dhooks (zc_none z) MAX_WBITS) chs.

Definition inflate_p (ans : option (blk * (Z -> Z))) (s : inflate_state) (zc : ZCall) (flush : Z)
  : inflate_state * ZRet * bool :=
  match inflate_m ivar_ref dhooks s zc flush [ans] with
  | MRet (r, chs') => (r, match chs' with [] => true | _ => false end)
  | _ => ((s, zret0 (zc_strm zc) Z_STREAM_ERROR), false)
  end.

Record iloop : Type := mkIL {
  il_s : inflate_state; il_z : zstrm; il_rest : list Z; il_out_rev : list Z; il_calls : Z;
  il_asked : bool  }.

Definition i_call (ans : option (blk * (Z -> Z))) (x : iloop) : iloop * Z :=
  let zc := mkZCall (zfirstn 1 (il_rest x)) 1 (il_z x) in
  let '((s', zr), asked) := inflate_p ans (il_s x) zc Z_NO_FLUSH in
  (mkIL s' (zr_strm zr) (zskipn (zr_consumed zr) (il_rest x))
        (rev_append (zr_output zr) (il_out_rev x)) (il_calls x + 1) (il_asked x || asked), zr_rc zr).

Definition il_step (wans : option (blk * (Z -> Z))) (n cb : Z) (x : iloop) : iloop + (iloop * hexit) :=
  if (zs_total_out (il_z x) <? n) && (zs_total_in (il_z x) <? cb) then
    let '(x', rc) := i_call wans x in
    if rc =? Z_STREAM_END then inr (x', HX_ok)
    else if rc =? Z_OK then inl x' else inr (x', HX_err W_inflate rc)
  else inr (x, HX_ok).

Definition i_fuel (n cb : Z) : Z := n + cb + 16.
Definition il_run (wans : option (blk * (Z -> Z))) (n cb : Z) (x : iloop) : iloop * hexit :=
  iterZ (i_fuel n cb) (il_step wans n cb) (fun x => (x, HX_fuel)) x.

Definition iend_rc (s : inflate_state) : Z := if inflateStateCheck s then Z_STREAM_ERROR else Z_OK.

Definition tinfl_body (wans : option (blk * (Z -> Z))) (compr : list Z) (n : Z) (s0 : inflate_state) (z0 : zstrm)
  : iloop * hexit :=
  let x0 := mkIL s0 z0 compr [] 0 false in
  let '(x1, e1) := il_run wans n (zlength compr) x0 in
  match e1 with
  | HX_ok => let rc := iend_rc (il_s x1) in (x1, if rc =? Z_OK then HX_ok else HX_err W_inflateEnd rc)
  | _ => (x1, e1)
  end.

Definition uncompr_of (x : iloop) (n : Z) : list Z := pad_to (rev_append (il_out_rev x) []) n.


Definition ascii (s : list Z) := s.
Definition msg_name (which : Z) : list Z :=
  if which =? W_deflateInit then [100;101;102;108;97;116;101;73;110;105;116]
  else if which =? W_deflate1 then [100;101;102;108;97;116;101;32;115;109;97;108;108;32;49]
  else if which =? W_deflate2 then [100;101;102;108;97;116;101;32;115;109;97;108;108;32;50]
  else if which =? W_deflateEnd then [100;101;102;108;97;116;101;69;110;100]
  else if which =? W_inflateInit then [105;110;102;108;97;116;101;73;110;105;116]
  else if which =? W_inflate then [105;110;102;108;97;116;101]
  else [105;110;102;108;97;116;101;69;110;100].
Fixpoint dec_digits (fuel : nat) (v : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if v <? 10 then (48 + v) :: acc else dec_digits f (v / 10) ((48 + v mod 10) :: acc)
  end.
Definition dec_int (v : Z) : list Z := if v <? 0 then 45 :: dec_digits 20 (- v) [] else dec_digits 20 v [].
Definition err_msg (which rc : Z) : list Z :=
  msg_name which ++ [32;101;114;114;111;114;58;32] ++ dec_int rc ++ [10].
Definition bad_inflate_msg : list Z := [98;97;100;32;105;110;102;108;97;116;101;10].

Definition exit_msg (e : hexit) : list Z :=
  match e with HX_err w rc => err_msg w rc | _ => [] end.

Record small_run : Type := mkSR {
  sr_cb : Z;
  sr_dexit : hexit; sr_dloop : option dloop;
  sr_compr : list Z;
  sr_iexit : hexit; sr_iloop : option iloop;
  sr_cmp : bool;
  sr_stderr : list Z }.

Definition small_run_of (g : N -> Z -> Z) (gi gw : Z -> Z) (d : list Z) : small_run :=
  let n := zlength d in
  let cb := compressBound_m n in
  let '(dexit, dl) :=
    match dinit_run (dchs g) zstrm0 with
    | Some (Some s0, zr) =>
        if zr_rc zr =? Z_OK then let '(x, e) := tdefl_body d cb s0 (zr_strm zr) in (e, Some x)
        else (HX_err W_deflateInit (zr_rc zr), None)
    | Some (None, zr) => (HX_err W_deflateInit (zr_rc zr), None)
    | None => (HX_fuel, None)
    end in
  let compr := match dl with Some x => compr_of x cb | None => zrepeat 0 cb end in
  let '(iexit, il) :=
    match iinit_run [Some (5%N, gi)] zstrm0 with
    | Some (Some s0, zr) =>
        if zr_rc zr =? Z_OK then let '(x, e) := tinfl_body (Some (6%N, gw)) compr n s0 (zr_strm zr) in (e, Some x)
        else (HX_err W_inflateInit (zr_rc zr), None)
    | Some (None, zr) => (HX_err W_inflateInit (zr_rc zr), None)
    | None => (HX_fuel, None)
    end in
  let uncompr := match il with Some x => uncompr_of x n | None => zrepeat 0 n end in
  let cmp := match iexit with HX_ok => negb (zlist_eqb (zfirstn n uncompr) d) | _ => false end in
  mkSR cb dexit dl compr iexit il cmp
       (exit_msg dexit ++ exit_msg iexit ++ (if cmp then bad_inflate_msg else [])).

Definition harness_small_stderr (d : list Z) : list Z :=
  let n := zlength d in
  if (n <? 1) || (kMaxSize <? n) then [] else sr_stderr (small_run_of (fun _ => g0) g0 g0 d).

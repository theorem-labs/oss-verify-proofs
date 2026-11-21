(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface
  DeflateState DeflateLz DeflateBlk Deflate InflateState Inflate HarnessKit HarnessSmall HarnessFacts HarnessSmallStages HarnessStmt DeflInitLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.







Definition lx_log (msg : string) (x : lexit) : list hevent :=
  match x with LX_err rc => [HEerr (check_err_line msg rc)] | _ => [] end.




Fixpoint dl1_p (fuel : nat) (s : deflate_state) (c : czs) (data : arr) (len : Z) (compr : arr) (comprLen : Z)
  : (deflate_state * czs * arr * lexit) * bool :=
  match fuel with
  | O => ((s, c, compr, LX_fuel), true)
  | S f =>
      if negb (zs_total_in (cz_z c) =? len) && (zs_total_out (cz_z c) <? comprLen) then
        let c1 := cz_set_avail_out (cz_set_avail_in c 1) 1 in
        let '(zc, b1) := cz_call c1 data in
        let '(s1, r) := deflate_m s zc Z_NO_FLUSH in
        let '(c2, compr1, b2) := cz_ret c1 r compr in
        if zr_rc r =? Z_OK then
          let '(x, b) := dl1_p f s1 c2 data len compr1 comprLen in (x, b1 || b2 || b)
        else ((s1, c2, compr1, LX_err (zr_rc r)), b1 || b2)
      else ((s, c, compr, LX_cond), false)
  end.


Fixpoint dl2_p (fuel : nat) (s : deflate_state) (c : czs) (data : arr) (compr : arr)
  : (deflate_state * czs * arr * lexit) * bool :=
  match fuel with
  | O => ((s, c, compr, LX_fuel), true)
  | S f =>
      let c1 := cz_set_avail_out c 1 in
      let '(zc, b1) := cz_call c1 data in
      let '(s1, r) := deflate_m s zc Z_FINISH in
      let '(c2, compr1, b2) := cz_ret c1 r compr in
      if zr_rc r =? Z_STREAM_END then ((s1, c2, compr1, LX_end), b1 || b2)
      else if zr_rc r =? Z_OK then
        let '(x, b) := dl2_p f s1 c2 data compr1 in (x, b1 || b2 || b)
      else ((s1, c2, compr1, LX_err (zr_rc r)), b1 || b2)
  end.


Definition dend_p (s : deflate_state) : Z * list hevent :=
  if deflateStateCheck s then (Z_STREAM_ERROR, [])
  else ((if ds_status s =? BUSY_STATE then Z_DATA_ERROR else Z_OK), dend_events s).

Definition tdb_p (s : deflate_state) (z : zstrm) (data : arr) (len : Z) (compr : arr) (comprLen : Z)
  : (arr * lexit) * (list hevent * bool) :=
  let c := mkCZS 0 0 0 0 z in
  let '(x1, b1) := dl1_p (Z.to_nat (len + comprLen + 2)) s c data len compr comprLen in
  let '(s1, c1, compr1, stop1) := x1 in
  match stop1 with
  | LX_cond =>
      let '(x2, b2) := dl2_p (Z.to_nat (comprLen + 2)) s1 c1 data compr1 in
      let '(s2, c2, compr2, stop2) := x2 in
      match stop2 with
      | LX_end =>
          let '(rc, evs) := dend_p s2 in
          let stop3 := if rc =? Z_OK then LX_end else LX_err rc in
          ((compr2, stop3), (lx_log "deflateEnd" stop3 ++ evs, b1 || b2))
      | other => ((compr2, other), (lx_log "deflate small 2" other, b1 || b2))
      end
  | other => ((compr1, other), (lx_log "deflate small 1" other, b1))
  end.



Definition hgr (o : horacle) (r : option Z) : option (blk * (Z -> Z)) :=
  match r with Some k => Some (Z.to_N k, ho_garb o k) | None => None end.

Definition dsetup5 (o : horacle) (n : Z) (zc : ZCall) (wb memLevel : Z) : deflate_state :=
  s_pb (s_lbs (s_hd (s_prv (s_win (s_setup (ho_garb o n) (Z.to_N n) (cs_init zc) (di_wrap wb) (di_wb9 wb) memLevel)
                                  (hgr o (hgrant o (n + 1)))) (hgr o (hgrant o (n + 2)))) (hgr o (hgrant o (n + 3)))) memLevel)
       (hgr o (hgrant o (n + 4))).

Definition dinit_arrays_fail (o : horacle) (n : Z) : bool :=
  ho_fail o (n + 1) || ho_fail o (n + 2) || ho_fail o (n + 3) || ho_fail o (n + 4).

Definition dinit_p (o : horacle) (n : Z) (zc : ZCall) (level method wb memLevel strategy : Z)
  : (option deflate_state * ZRet) * (Z * list hevent) :=
  if ho_fail o n then ((None, zret_of_cs (cs_init zc) Z_MEM_ERROR), (n + 1, [HEmalloc (mul32 1 SIZEOF_deflate_state) None]))
  else
    let evs := dinit_events wb memLevel (Some n) (hgrant o (n + 1)) (hgrant o (n + 2)) (hgrant o (n + 3)) (hgrant o (n + 4)) in
    if dinit_arrays_fail o n then
      ((None, zret_of_cs (cset_msg (cs_init zc) (MSG_ERR Z_MEM_ERROR)) Z_MEM_ERROR),
       (n + 5, dend_events (s_fail (dsetup5 o n zc wb memLevel)) ++ evs))
    else
      ((Some (init_state o n zc level method wb memLevel strategy),
        zret_of_cs (ds_strm (init_state o n zc level method wb memLevel strategy)) Z_OK), (n + 5, evs)).



Definition tdefl_p (o : horacle) (n : Z) (data : arr) (dataLen : Z) (compr : arr) (comprLen : Z)
  : arr * (Z * list hevent * bool) :=
  let zs := ho_zs o 0 in
  let '(res, ne) := dinit_p o n (mkZCall [] 0 zs) Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY in
  let '(os, r) := res in
  let '(n1, evs1) := ne in
  let evs2 := (if zr_rc r =? Z_OK then [] else [HEerr (check_err_line "deflateInit" (zr_rc r))]) ++ evs1 in
  match os, negb (zr_rc r =? Z_OK) with
  | Some s, false =>
      let '(x, lb) := tdb_p s (zr_strm r) data dataLen compr comprLen in
      (fst x, (n1, fst lb ++ evs2, snd lb))
  | _, _ => (compr, (n1, evs2, false))
  end.




Fixpoint il_p (fuel : nat) (o : horacle) (n : Z) (s : inflate_state) (c : czs) (compr : arr) (comprLen : Z)
         (uncompr : arr) (uncomprLen : Z)
  : (inflate_state * czs * arr * lexit) * (Z * list hevent * bool) :=
  match fuel with
  | O => ((s, c, uncompr, LX_fuel), (n, [], true))
  | S f =>
      if (zs_total_out (cz_z c) <? uncomprLen) && (zs_total_in (cz_z c) <? comprLen) then
        let c1 := cz_set_avail_out (cz_set_avail_in c 1) 1 in
        let '(zc, b1) := cz_call c1 compr in
        let '(res, asked) := inflate_p ivar_ref (hans o n) s zc Z_NO_FLUSH in
        let '(s1, r) := res in
        let '(c2, uncompr1, b2) := cz_ret c1 r uncompr in
        let n1 := match asked with Some _ => n + 1 | None => n end in
        let ev1 := match asked with Some size => [HEmalloc size (hgrant o n)] | None => [] end in
        if zr_rc r =? Z_STREAM_END then ((s1, c2, uncompr1, LX_end), (n1, ev1, b1 || b2))
        else if zr_rc r =? Z_OK then
          let '(x, t) := il_p f o n1 s1 c2 compr comprLen uncompr1 uncomprLen in
          let '(n2, ev2, b) := t in (x, (n2, ev2 ++ ev1, b1 || b2 || b))
        else ((s1, c2, uncompr1, LX_err (zr_rc r)), (n1, HEerr (check_err_line "inflate" (zr_rc r)) :: ev1, b1 || b2))
      else ((s, c, uncompr, LX_cond), (n, [], false))
  end.


Definition iend_p (s : inflate_state) : Z * list hevent :=
  if inflateStateCheck s then (Z_STREAM_ERROR, [])
  else (Z_OK, HEfree (Z.of_N (is_self_blk s))
              :: match is_window_blk s with Some b => [HEfree (Z.of_N b)] | None => [] end).

Definition il_fuel (uncomprLen comprLen : Z) : nat := Z.to_nat (uncomprLen + comprLen + 2).

Definition tib_p (o : horacle) (n : Z) (s : inflate_state) (z : zstrm) (data : arr) (dataLen : Z)
           (compr : arr) (comprLen : Z) (uncompr : arr) (uncomprLen : Z)
  : (arr * lexit) * (Z * list hevent * bool) :=
  let c := mkCZS 0 0 0 0 z in
  let '(x, t) := il_p (il_fuel uncomprLen comprLen) o n s c compr comprLen uncompr uncomprLen in
  let '(s1, c1, unc1, stop) := x in
  let '(ne, b) := t in let '(n1, evs) := ne in
  match stop with
  | LX_err _ => ((unc1, stop), (n1, evs, b))
  | _ =>
      let '(rc, fe) := iend_p s1 in
      if negb (rc =? Z_OK) then ((unc1, stop), (n1, HEerr (check_err_line "inflateEnd" rc) :: fe ++ evs, b))
      else if memcmp_ne unc1 data dataLen then ((unc1, stop), (n1, HEerr (str_bytes "bad inflate" ++ [10]) :: fe ++ evs, b))
      else ((unc1, stop), (n1, fe ++ evs, b))
  end.


Definition tinfl_p (o : horacle) (n : Z) (data : arr) (dataLen : Z) (compr : arr) (comprLen : Z) (uncompr : arr) (uncomprLen : Z)
  : arr * (Z * list hevent * bool) :=
  let zs := ho_zs o 1 in
  let ev0 := HEmalloc (mul32 1 SIZEOF_inflate_state) (hgrant o n) in
  match hgrant o n with
  | None => (uncompr, (n + 1, [HEerr (check_err_line "inflateInit" Z_MEM_ERROR); ev0], false))
  | Some k =>
      let '(s, z) := iinit_state ivar_ref (ho_garb o k) (Z.to_N k) (zs_set_msg MSG_NULL zs) in
      let '(x, t) := tib_p o (n + 1) s z data dataLen compr comprLen uncompr uncomprLen in
      let '(ne, b) := t in let '(n2, evs) := ne in
      (fst x, (n2, evs ++ [ev0], b))
  end.






Definition ds0 : deflate_state :=
  init_state (ocanon []) 2 (mkZCall [] 0 zstrm0) Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY.
Definition zr0 : ZRet := zret_of_cs (ds_strm ds0) Z_OK.

Lemma ds0_sLM : ds0 = sLM (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) 2%N 3%N 4%N 5%N 6%N
                            (cs_init (mkZCall [] 0 zstrm0)) 1 15 8 6 0 8.
Proof. reflexivity. Qed.







Definition is0 (kI : Z) : inflate_state := fst (iinit_state ivar_ref (fun _ => 0) (Z.to_N kI) (zs_set_msg MSG_NULL zstrm0)).
Definition iz0 (kI : Z) : zstrm := snd (iinit_state ivar_ref (fun _ => 0) (Z.to_N kI) (zs_set_msg MSG_NULL zstrm0)).












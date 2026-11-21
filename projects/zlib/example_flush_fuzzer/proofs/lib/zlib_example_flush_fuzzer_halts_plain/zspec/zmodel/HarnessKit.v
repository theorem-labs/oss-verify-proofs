(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Bool String Strings.Byte.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.


Inductive hevent : Type :=
| HEcalloc (n : Z) (res : option Z)
| HEmalloc (n : Z) (res : option Z)
| HEfree (b : Z)
| HEerr (line : list Z).

Record horacle : Type := mkHO {
  ho_fail : Z -> bool;
  ho_garb : Z -> Z -> Z;
  ho_zs : Z -> zstrm
}.

Record hst : Type := mkHS {
  hs_o : horacle;
  hs_n : Z;
  hs_log : list hevent;
  hs_bad : bool
}.

Definition hlog (e : hevent) (st : hst) : hst := mkHS (hs_o st) (hs_n st) (e :: hs_log st) (hs_bad st).
Definition hflag (b : bool) (st : hst) : hst :=
  if b then mkHS (hs_o st) (hs_n st) (hs_log st) true else st.

Definition h_alloc (mk : Z -> option Z -> hevent) (n : Z) : SM hst (option Z) :=
  fun st =>
    let k := hs_n st in
    let r := if ho_fail (hs_o st) k then None else Some k in
    MRet (r, mkHS (hs_o st) (k + 1) (mk n r :: hs_log st) (hs_bad st)).
Definition h_malloc (n : Z) : SM hst (option Z) := h_alloc HEmalloc n.
Definition h_free (b : Z) : SM hst unit := fun st => MRet (tt, hlog (HEfree b) st).
Definition h_err (line : list Z) : SM hst unit := fun st => MRet (tt, hlog (HEerr line) st).
Definition h_bad (b : bool) : SM hst unit := fun st => MRet (tt, hflag b st).
Definition h_garb (k : Z) : SM hst (Z -> Z) := fun st => MRet (ho_garb (hs_o st) k, st).
Definition h_zs (j : Z) : SM hst zstrm := fun st => MRet (ho_zs (hs_o st) j, st).

Definition hz_hooks : zhooks hst :=
  mkHooks
    (fun items size =>
       do r <- h_malloc (mul32 items size) ;
       match r with
       | Some k => do g <- h_garb k ; sret (Some (Z.to_N k, g))
       | None => sret None
       end)
    (fun b => h_free (Z.of_N b)).

Definition hrun {A} (m : SM hst A) (st : hst) : option (A * hst) :=
  match m st with MRet p => Some p | _ => None end.


Definition str_bytes (s : string) : list Z :=
  List.map (fun b => Z.of_N (Byte.to_N b)) (list_byte_of_string s).

Fixpoint zdec_nat (fuel : nat) (n : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f =>
      let acc := (48 + n mod 10) :: acc in
      let q := n / 10 in
      if Z.eqb q 0 then acc else zdec_nat f q acc
  end.

Definition zdec (n : Z) : list Z :=
  if Z.ltb n 0 then 45 :: zdec_nat 20%nat (- n) [] else zdec_nat 20%nat n [].

Definition check_err_line (msg : string) (err : Z) : list Z :=
  str_bytes msg ++ str_bytes " error: " ++ zdec err ++ [10].

Definition check_err (err : Z) (msg : string) : SM hst bool :=
  if Z.eqb err Z_OK then sret false
  else h_err (check_err_line msg err) ;; sret true.


Record czs : Type := mkCZS {
  cz_next_in : Z;
  cz_avail_in : Z;
  cz_next_out : Z;
  cz_avail_out : Z;
  cz_z : zstrm
}.

Definition cz_set_in (c : czs) (next_in avail_in : Z) : czs :=
  mkCZS next_in avail_in (cz_next_out c) (cz_avail_out c) (cz_z c).
Definition cz_set_out (c : czs) (next_out avail_out : Z) : czs :=
  mkCZS (cz_next_in c) (cz_avail_in c) next_out avail_out (cz_z c).
Definition cz_set_avail_in (c : czs) (v : Z) : czs :=
  mkCZS (cz_next_in c) v (cz_next_out c) (cz_avail_out c) (cz_z c).
Definition cz_set_avail_out (c : czs) (v : Z) : czs :=
  mkCZS (cz_next_in c) (cz_avail_in c) (cz_next_out c) v (cz_z c).
Definition cz_call (c : czs) (inbuf : arr) : ZCall * bool :=
  (mkZCall (arr_slice inbuf (cz_next_in c) (cz_avail_in c)) (cz_avail_out c) (cz_z c),
   (arr_len inbuf <? cz_next_in c + cz_avail_in c) || (cz_next_in c <? 0) || (cz_avail_in c <? 0)).

Definition cz_ret (c : czs) (r : ZRet) (outbuf : arr) : czs * arr * bool :=
  let nout := zlength (zr_output r) in
  (mkCZS (cz_next_in c + zr_consumed r) (cz_avail_in c - zr_consumed r)
         (cz_next_out c + nout) (cz_avail_out c - nout) (zr_strm r),
   arr_upd outbuf (cz_next_out c) (zr_output r),
   (arr_len outbuf <? cz_next_out c + nout) || (cz_next_out c <? 0)).

Definition zero_buf (n : Z) : arr := arr_make n 0.

Definition memcmp_ne (a b : arr) (n : Z) : bool :=
  negb (zlist_eqb (arr_slice a 0 n) (arr_slice b 0 n)).

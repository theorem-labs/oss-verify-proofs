(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import FillWinModel BitsModel TreeModel SendModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Export TreesTab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition sym_d0 (s : deflate_state) (sx : Z) : Z := Z.land (sym_buf_get s sx) 255.
Definition sym_d1 (s : deflate_state) (sx : Z) : Z := Z.land (sym_buf_get s (sx + 1)) 255.
Definition sym_lc (s : deflate_state) (sx : Z) : Z := sym_buf_get s (sx + 1 + 1).
Definition sym_dist (s : deflate_state) (sx : Z) : Z := sym_d0 s sx + Z.shiftl (sym_d1 s sx) 8.

Definition sym_calls (s : deflate_state) (lfc ldl dfc ddl : arr) (sx : Z) : list (Z * Z) :=
  let dist := sym_dist s sx in
  let lc := sym_lc s sx in
  if dist =? 0 then [(arr_get lfc lc, arr_get ldl lc)]
  else
    let code := arr_get length_code_a lc in
    let extra := arr_get extra_lbits_a code in
    let dist' := dist - 1 in
    let dcode := d_code dist' in
    let dextra := arr_get extra_dbits_a dcode in
    [(arr_get lfc (code + LITERALS + 1), arr_get ldl (code + LITERALS + 1))]
    ++ (if negb (extra =? 0) then [(lc - arr_get base_length_a code, extra)] else [])
    ++ [(arr_get dfc dcode, arr_get ddl dcode)]
    ++ (if negb (dextra =? 0) then [(wrap32 (dist' - arr_get base_dist_a dcode), dextra)] else []).

Lemma compress_block_sym_eq : forall s lfc ldl dfc ddl sx,
  compress_block_sym s lfc ldl dfc ddl sx = (sbs_run s (sym_calls s lfc ldl dfc ddl sx), sx + 1 + 1 + 1).
Proof.
  intros. unfold compress_block_sym, sym_calls, sym_dist, sym_d0, sym_d1, sym_lc, send_code. cbv zeta.
  destruct (_ =? 0); [reflexivity|].
  destruct (negb (arr_get extra_lbits_a _ =? 0)); destruct (negb (arr_get extra_dbits_a _ =? 0)); reflexivity.
Qed.

Lemma cb_loop_S : forall f s lfc ldl dfc ddl sx,
  compress_block_loop (S f) s lfc ldl dfc ddl sx =
    let s' := sbs_run s (sym_calls s lfc ldl dfc ddl sx) in
    let sx' := sx + 1 + 1 + 1 in
    if sx' <? ds_sym_next s' then compress_block_loop f s' lfc ldl dfc ddl sx' else s'.
Proof. intros. cbn [compress_block_loop]. rewrite compress_block_sym_eq. reflexivity. Qed.




Definition PBB (s : deflate_state) : Prop :=
  forall i, 0 <= i < arr_len (ds_pending_buf s) -> 0 <= arr_get (ds_pending_buf s) i < 256.

Definition sym_ok (PBL : Z) (s : deflate_state) (lfc ldl dfc ddl : arr) (sx : Z) : Prop :=
  0 <= sx /\ ds_lit_bufsize s + sx + 1 + 1 + 1 <= PBL
  /\ (sym_dist s sx <> 0 -> sym_dist s sx - 1 < 32768)
  /\ (sym_dist s sx = 0 -> 0 <= arr_get ldl (sym_lc s sx) <= 15)
  /\ (sym_dist s sx <> 0 ->
        0 <= arr_get ldl (arr_get length_code_a (sym_lc s sx) + LITERALS + 1) <= 15
        /\ 0 <= arr_get ddl (d_code (sym_dist s sx - 1)) <= 15)
  /\ sbs_ok PBL s (sym_calls s lfc ldl dfc ddl sx).

Fixpoint cb_ok (PBL : Z) (fuel : nat) (s : deflate_state) (lfc ldl dfc ddl : arr) (sx : Z) : Prop :=
  match fuel with
  | O => True
  | S f =>
      sym_ok PBL s lfc ldl dfc ddl sx
      /\ (let s' := sbs_run s (sym_calls s lfc ldl dfc ddl sx) in
          let sx' := sx + 1 + 1 + 1 in
          if sx' <? ds_sym_next s' then cb_ok PBL f s' lfc ldl dfc ddl sx' else True)
  end.

Definition compress_block_ok (PBL : Z) (s : deflate_state) (lfc ldl dfc ddl : arr) : Prop :=
  BINV PBL s /\ PBB s
  /\ (ds_sym_next s <> 0 -> cb_ok PBL (Z.to_nat (ds_sym_next s)) s lfc ldl dfc ddl 0)
  /\ 0 <= arr_get ldl END_BLOCK <= 15
  /\ (let s1 := if negb (ds_sym_next s =? 0)
                then compress_block_loop (Z.to_nat (ds_sym_next s)) s lfc ldl dfc ddl 0 else s in
      sbs_ok PBL s1 [(arr_get lfc END_BLOCK, arr_get ldl END_BLOCK)]).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BgState BgWords BgLib BgArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition MONT_CTX_BYTES : Z := 96.

Section Mont.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : bn_ops M ptr.

Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation BM := (BM (M:=M) (ptr:=ptr)) (only parsing).

Local Notation "x <- m ;; k" := (bbind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bbind ops m (fun _ => k)) (at level 61, right associativity).
Local Notation bret := (bret ops).
Local Notation bunr := (bunr ops).
Local Notation bget := (bget ops).
Local Notation bset := (bset ops).

Definition BN_MONT_CTX_new : BM ptr :=
  p <- bmalloc ops MONT_CTX_BYTES ;;
  bsetmont ops 0 0 ;;;
  bset RMontRR (bn_nil 0) ;;;
  bset RMontN (bn_nil 0) ;;;
  bset RMontNi (bn_nil 0) ;;;
  bret p.

Definition BN_MONT_CTX_free (p : ptr) : BM unit :=
  rr <- bget RMontRR ;;
  n <- bget RMontN ;;
  ni <- bget RMontNi ;;
  if has_flag rr BN_FLG_MALLOCED || has_flag n BN_FLG_MALLOCED || has_flag ni BN_FLG_MALLOCED then bunr
  else
    BN_clear_free ops RMontRR None ;;;
    BN_clear_free ops RMontN None ;;;
    BN_clear_free ops RMontNi None ;;;
    bfree ops p ;;;
    bsetmont ops 0 0.

Definition BN_MONT_CTX_set (rmod : bnref) : BM unit :=
  m <- bget rmod ;;
  if is_zero_pure m then bunr
  else
    BN_CTX_start ops ;;;
    rRi <- BN_CTX_get ops ;;
    BN_copy ops RMontN rmod ;;;
    (n <- bget RMontN ;; bset RMontN (bn_with_neg n false)) ;;;
    nb <- BN_num_bits ops rmod ;;
    let ri := (nb + 63) / 64 * 64 in
    (st <- bgetst ops ;; bsetmont ops ri (st_n0 st)) ;;;
    BN_zero ops RMontRR ;;;
    BN_set_bit ops RMontRR 64 ;;;

    m <- bget rmod ;;

    if (bn_top m =? 0)%nat then bunr else
    let b0 := nth 0 (bn_buf m) 0 in
    bset RTmod (mkBN None [b0; 0] (if b0 =? 0 then 0%nat else 1%nat) false 0) ;;;
    tm <- bget RTmod ;;
    (if is_one_pure tm then BN_zero ops rRi else BN_mod_inverse ops rRi RMontRR RTmod) ;;;
    BN_lshift ops rRi rRi 64 ;;;
    x <- bget rRi ;;

    (if negb (is_zero_pure x) then (if lval (firstn (bn_top x) (bn_buf x)) <? 1 then bunr else BN_sub_word ops rRi 1) else BN_set_word ops rRi BN_MASK2) ;;;
    BN_div ops (Some rRi) None rRi RTmod ;;;
    x <- bget rRi ;;
    let n0 := if (0 <? bn_top x)%nat then nth 0 (bn_buf x) 0 else 0 in
    (st <- bgetst ops ;; bsetmont ops (st_ri st) n0) ;;;

    BN_zero ops RMontRR ;;;

    st <- bgetst ops ;;
    if negb (st_ri st =? ri) then bunr else
    BN_set_bit ops RMontRR (ri * 2) ;;;
    BN_mod ops RMontRR RMontRR RMontN ;;;
    rr <- bget RMontRR ;;
    n <- bget RMontN ;;

    if (bn_dmax rr <? bn_top n)%nat then bunr else
    bset RMontRR (mkBN (bn_d rr) (splice (bn_buf rr) (bn_top rr) (repeat 0 (bn_top n - bn_top rr))) (bn_top n)
                       (bn_neg rr) (bn_flags rr)) ;;;
    BN_CTX_end ops ;;;

    tm <- bget RTmod ;;
    if (match bn_d tm with Some _ => true | None => false end) then bunr else
    bset RTmod (bn_nil 0).

Definition bn_from_montgomery_word (ret r : bnref) : BM unit :=
  if (ret =? r)%nat || (ret =? RMontN)%nat || (r =? RMontN)%nat then bunr else
  n <- bget RMontN ;;
  let nl := bn_top n in
  if (nl =? 0)%nat then (b <- bget ret ;; bset ret (bn_with_top b 0))
  else
    let max := (2 * nl)%nat in
    bn_wexpand ops r max ;;;
    rb <- bget r ;;
    n <- bget RMontN ;;
    st <- bgetst ops ;;

    if negb ((0 <=? st_n0 st) && (st_n0 st <? 18446744073709551616)) then bunr else
    let np := firstn nl (bn_buf n) in

    let buf := splice (bn_buf rb) (bn_top rb) (repeat 0 (max - bn_top rb)) in
    let '(buf, carry) := mont_reduce_loop np (st_n0 st) nl nl 0 buf 0 in
    bset r (mkBN (bn_d rb) buf max (xorb (bn_neg rb) (bn_neg n)) (bn_flags rb)) ;;;
    bn_wexpand ops ret nl ;;;
    rt <- bget ret ;;
    rb <- bget r ;;
    let ap := slice (bn_buf rb) nl nl in
    bset ret (mkBN (bn_d rt) (splice (bn_buf rt) 0 (mont_final ap np carry)) nl (bn_neg rb) (bn_flags rt)) ;;;

    rb <- bget r ;;
    bset r (bn_with_buf rb (splice (bn_buf rb) nl (repeat 0 nl))).

Definition bn_mul_mont_fixed_top (rr ra rb : bnref) : BM unit :=
  n <- bget RMontN ;;
  a <- bget ra ;;
  b <- bget rb ;;
  if (2 * bn_top n <? bn_top a + bn_top b)%nat then bunr
  else
    BN_CTX_start ops ;;;
    tmp <- BN_CTX_get ops ;;
    (if (ra =? rb)%nat then bn_sqr_fixed_top ops tmp ra else bn_mul_fixed_top ops tmp ra rb) ;;;
    bn_from_montgomery_word rr tmp ;;;
    BN_CTX_end ops.

Definition BN_mod_mul_montgomery (rr ra rb : bnref) : BM unit :=
  bn_mul_mont_fixed_top rr ra rb ;;;
  (b <- bget rr ;; bset rr (bn_correct_top_pure b)).

Definition bn_to_mont_fixed_top (rr ra : bnref) : BM unit := bn_mul_mont_fixed_top rr ra RMontRR.
Definition BN_to_montgomery (rr ra : bnref) : BM unit := BN_mod_mul_montgomery rr ra RMontRR.

Definition bn_from_mont_fixed_top (ret ra : bnref) : BM unit :=
  BN_CTX_start ops ;;;
  t <- BN_CTX_get ops ;;
  BN_copy ops t ra ;;;
  bn_from_montgomery_word ret t ;;;
  BN_CTX_end ops.

Definition BN_from_montgomery (ret ra : bnref) : BM unit :=
  bn_from_mont_fixed_top ret ra ;;;
  (b <- bget ret ;; bset ret (bn_correct_top_pure b)).

Definition BN_RECP_CTX_init : BM unit :=
  bsetrecp ops 0 0 ;;;
  bset RRecpN (bn_nil 0) ;;;
  bset RRecpNr (bn_nil 0).

Definition BN_RECP_CTX_free : BM unit :=
  n <- bget RRecpN ;;
  nr <- bget RRecpNr ;;
  if has_flag n BN_FLG_MALLOCED || has_flag nr BN_FLG_MALLOCED then bunr
  else
    BN_free ops RRecpN None ;;;
    BN_free ops RRecpNr None ;;;
    bsetrecp ops 0 0.

Definition BN_RECP_CTX_set (rd : bnref) : BM unit :=
  d <- bget rd ;;
  if is_zero_pure d then bunr
  else
    BN_copy ops RRecpN rd ;;;
    BN_zero ops RRecpNr ;;;
    nb <- BN_num_bits ops rd ;;
    bsetrecp ops nb 0.

Definition BN_reciprocal (rr rm : bnref) (len : Z) : BM Z :=
  BN_CTX_start ops ;;;
  t <- BN_CTX_get ops ;;
  BN_set_bit ops t len ;;;
  BN_div ops (Some rr) None t rm ;;;
  BN_CTX_end ops ;;;
  bret len.

Fixpoint recp_fix_loop (fuel : nat) (r d : bnref) (j : Z) : BM unit :=
  match fuel with
  | O => bunr
  | S f =>
      c <- BN_ucmp ops r RRecpN ;;
      if c <? 0 then bret tt
      else if 2 <? j then bunr
      else BN_usub ops r r RRecpN ;;; BN_add_word ops d 1 ;;; recp_fix_loop f r d (j + 1)
  end.

Definition recp_rng (s : ST) : bool :=
  (0 <=? st_rbits s) && (st_rbits s <? 16777216) && (-2147483648 <=? st_rshift s) && (st_rshift s <? 2147483648).

Definition BN_div_recp (dv rem : option bnref) (rm : bnref) : BM unit :=
  BN_CTX_start ops ;;;
  d <- (match dv with Some x => bret x | None => BN_CTX_get ops end) ;;
  r <- (match rem with Some x => bret x | None => BN_CTX_get ops end) ;;
  a <- BN_CTX_get ops ;;
  b <- BN_CTX_get ops ;;
  c <- BN_ucmp ops rm RRecpN ;;
  if c <? 0 then
    BN_zero ops d ;;;
    BN_copy ops r rm ;;;
    BN_CTX_end ops
  else
    i0 <- BN_num_bits ops rm ;;
    st <- bgetst ops ;;
    if negb (recp_rng st) then bunr else
    let j := 2 * st_rbits st in
    let i := if i0 <? j then j else i0 in
    (if i =? st_rshift st then bret tt
     else sh <- BN_reciprocal RRecpNr RRecpN i ;; (st <- bgetst ops ;; bsetrecp ops (st_rbits st) sh)) ;;;
    st <- bgetst ops ;;
    if negb (recp_rng st) then bunr else
    if st_rshift st =? -1 then bunr
    else
      BN_rshift ops a rm (st_rbits st) ;;;
      BN_mul ops b a RRecpNr ;;;
      st <- bgetst ops ;;
      if negb (recp_rng st) then bunr else
      BN_rshift ops d b (i - st_rbits st) ;;;
      (x <- bget d ;; bset d (bn_with_neg x false)) ;;;
      BN_mul ops b RRecpN d ;;;
      BN_usub ops r rm b ;;;
      (x <- bget r ;; bset r (bn_with_neg x false)) ;;;
      recp_fix_loop 5 r d 0 ;;;
      (x <- bget r ;; m <- bget rm ;; bset r (bn_with_neg x (if is_zero_pure x then false else bn_neg m))) ;;;
      (x <- bget d ;; m <- bget rm ;; n <- bget RRecpN ;; bset d (bn_with_neg x (xorb (bn_neg m) (bn_neg n)))) ;;;
      BN_CTX_end ops.

Definition BN_mod_mul_reciprocal (rr rx ry : bnref) : BM unit :=
  BN_CTX_start ops ;;;
  a <- BN_CTX_get ops ;;
  (if (rx =? ry)%nat then BN_sqr ops a rx else BN_mul ops a rx ry) ;;;
  BN_div_recp None (Some rr) a ;;;
  BN_CTX_end ops.

End Mont.

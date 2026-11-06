(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BgState BgWords BgLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition opt_refs (o : option bnref) : list bnref := match o with Some r => [r] | None => [] end.
Definition live_refs {ptr} (c : bg_ctx ptr) (rs : list bnref) : bool := forallb (fun r => (r <? NFIX + gx_used c)%nat) rs.

Section Arith.
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

Definition bn_live {A} (rs : list bnref) (k : BM A) : BM A :=
  c <- bgetctx ops ;; (if live_refs c rs then k else bunr).

Definition bn_left_align (r : bnref) : BM Z :=
  b <- bget r ;;
  let top := bn_top b in
  let lshift := 64 - num_bits_word (nth (top - 1) (bn_buf b) 0) in
  bset r (bn_with_buf b (splice (bn_buf b) 0 (fst (lshift_limbs (firstn top (bn_buf b)) lshift 0)))) ;;;
  bret lshift.

Definition bn_div_fixed_top (dv rm : option bnref) (num divisor : bnref) : BM unit :=
  bn_live (num :: divisor :: opt_refs dv ++ opt_refs rm) (
  BN_CTX_start ops ;;;
  res <- (match dv with None => BN_CTX_get ops | Some r => bret r end) ;;
  tmp <- BN_CTX_get ops ;;
  snum <- BN_CTX_get ops ;;
  sdiv <- BN_CTX_get ops ;;
  BN_copy ops sdiv divisor ;;;
  norm_shift <- bn_left_align sdiv ;;
  (b <- bget sdiv ;; bset sdiv (bn_with_neg b false)) ;;;
  bn_lshift_fixed_top ops snum num norm_shift ;;;
  sd <- bget sdiv ;;
  sn <- bget snum ;;
  let div_n := bn_top sd in
  (if (bn_top sn <=? div_n)%nat then
     bn_wexpand ops snum (div_n + 1) ;;;
     sn' <- bget snum ;;

     bset snum (mkBN (bn_d sn') (splice (bn_buf sn') (bn_top sn) (repeat 0 (div_n - bn_top sn + 1)))
                     (div_n + 1) (bn_neg sn') (bn_flags sn'))
   else bret tt) ;;;
  sn <- bget snum ;;
  let num_n := bn_top sn in
  let loop := (num_n - div_n)%nat in
  let d0 := nth (div_n - 1) (bn_buf sd) 0 in
  let d1 := if (div_n =? 1)%nat then 0 else nth (div_n - 2) (bn_buf sd) 0 in
  bn_wexpand ops res loop ;;;
  nm <- bget num ;;
  dvs <- bget divisor ;;
  let num_neg := bn_neg nm in
  (r <- bget res ;; bset res (mkBN (bn_d r) (bn_buf r) loop (xorb num_neg (bn_neg dvs)) (bn_flags r))) ;;;
  bn_wexpand ops tmp (div_n + 1) ;;;
  sn <- bget snum ;;
  tm <- bget tmp ;;
  r <- bget res ;;
  let '(snb, tmb, rb) := div_loop (bn_buf sd) div_n loop num_n d0 d1 loop 0 (bn_buf sn, bn_buf tm, bn_buf r) in
  bset tmp (bn_with_buf tm tmb) ;;;
  bset res (bn_with_buf r rb) ;;;
  bset snum (mkBN (bn_d sn) snb div_n num_neg (bn_flags sn)) ;;;
  (match rm with Some r => bn_rshift_fixed_top ops r snum norm_shift | None => bret tt end) ;;;
  BN_CTX_end ops).

Definition BN_div (dv rm : option bnref) (num divisor : bnref) : BM unit :=
  d <- bget divisor ;;
  if (bn_top d =? 0)%nat then bunr
  else if nth (bn_top d - 1) (bn_buf d) 0 =? 0 then bunr
  else
    bn_div_fixed_top dv rm num divisor ;;;
    (match dv with Some r => (b <- bget r ;; bset r (bn_correct_top_pure b)) | None => bret tt end) ;;;
    (match rm with Some r => (b <- bget r ;; bset r (bn_correct_top_pure b)) | None => bret tt end).

Definition BN_mod (rm num divisor : bnref) : BM unit := BN_div None (Some rm) num divisor.

Definition bn_mul_fixed_top (rr ra rb : bnref) : BM unit :=
  bn_live [rr; ra; rb] (
  a <- bget ra ;;
  b <- bget rb ;;
  let al := bn_top a in
  let bl := bn_top b in
  if ((al =? 0) || (bl =? 0))%nat then BN_zero ops rr
  else
    let top := (al + bl)%nat in
    BN_CTX_start ops ;;;
    (if (rr =? ra)%nat || (rr =? rb)%nat then bunr
     else if ((al =? bl) && (al =? 8))%nat then
       bn_wexpand ops rr 16 ;;;
       r <- bget rr ;;
       bset rr (mkBN (bn_d r) (splice (bn_buf r) 0 (mul_comba8 (firstn 8 (bn_buf a)) (firstn 8 (bn_buf b)))) 16
                     (bn_neg r) (bn_flags r))
     else if ((16 <=? al) && (16 <=? bl) && (al <=? bl + 1) && (bl <=? al + 1))%nat then

       let kj := Z.to_nat (num_bits_word (Z.of_nat (Nat.max al bl)) - 1) in
       let j := Nat.pow 2 kj in
       t <- BN_CTX_get ops ;;
       if ((j <? al) || (j <? bl))%nat then
         bn_wexpand ops t (8 * j) ;;;
         bn_wexpand ops rr (8 * j) ;;;
         tb <- bget t ;;
         r <- bget rr ;;
         let '(ro, to) := mul_part_recursive kj kj (firstn al (bn_buf a)) (firstn bl (bn_buf b)) (al - j) (bl - j)
                                             (firstn (4 * j) (bn_buf r)) (bn_buf tb) in
         bset t (bn_with_buf tb to) ;;;
         bset rr (mkBN (bn_d r) (splice (bn_buf r) 0 ro) top (bn_neg r) (bn_flags r))
       else
         bn_wexpand ops t (4 * j) ;;;
         bn_wexpand ops rr (4 * j) ;;;
         tb <- bget t ;;
         r <- bget rr ;;
         let '(ro, to) := mul_recursive kj (firstn al (bn_buf a)) (firstn bl (bn_buf b)) (j - al) (j - bl)
                                        (firstn (2 * j) (bn_buf r)) (bn_buf tb) in
         bset t (bn_with_buf tb to) ;;;
         bset rr (mkBN (bn_d r) (splice (bn_buf r) 0 ro) top (bn_neg r) (bn_flags r))
     else
       bn_wexpand ops rr top ;;;
       r <- bget rr ;;
       bset rr (mkBN (bn_d r) (splice (bn_buf r) 0 (mul_normal (firstn al (bn_buf a)) (firstn bl (bn_buf b)))) top
                     (bn_neg r) (bn_flags r))) ;;;

    (r <- bget rr ;; bset rr (bn_with_neg r (xorb (bn_neg a) (bn_neg b)))) ;;;
    BN_CTX_end ops).

Definition BN_mul (rr ra rb : bnref) : BM unit :=
  bn_mul_fixed_top rr ra rb ;;;
  (b <- bget rr ;; bset rr (bn_correct_top_pure b)).

Definition bn_sqr_fixed_top (rr ra : bnref) : BM unit :=
  bn_live [rr; ra] (
  a <- bget ra ;;
  let al := bn_top a in
  if (al =? 0)%nat then (r <- bget rr ;; bset rr (mkBN (bn_d r) (bn_buf r) 0 false (bn_flags r)))
  else
    BN_CTX_start ops ;;;
    (if (rr =? ra)%nat then bunr
     else
       tmp <- BN_CTX_get ops ;;
       let max := (2 * al)%nat in
       bn_wexpand ops rr max ;;;
       (if (al =? 4)%nat then
          r <- bget rr ;;
          bset rr (bn_with_buf r (splice (bn_buf r) 0 (sqr_comba4 (firstn 4 (bn_buf a)))))
        else if (al =? 8)%nat then
          r <- bget rr ;;
          bset rr (bn_with_buf r (splice (bn_buf r) 0 (sqr_comba8 (firstn 8 (bn_buf a)))))
        else if (al <? 16)%nat then

          r <- bget rr ;;
          bset rr (bn_with_buf r (splice (bn_buf r) 0 (fst (sqr_normal (firstn al (bn_buf a)) (firstn max (bn_buf r))))))
        else
          let kj := Z.to_nat (num_bits_word (Z.of_nat al) - 1) in
          let j := Nat.pow 2 kj in
          if (al =? j)%nat then
            bn_wexpand ops tmp (4 * j) ;;;
            tb <- bget tmp ;;
            r <- bget rr ;;
            let '(ro, to) := sqr_recursive kj (firstn al (bn_buf a)) (firstn max (bn_buf r)) (bn_buf tb) in
            bset tmp (bn_with_buf tb to) ;;;
            bset rr (bn_with_buf r (splice (bn_buf r) 0 ro))
          else
            bn_wexpand ops tmp max ;;;
            tb <- bget tmp ;;
            r <- bget rr ;;
            let '(ro, to) := sqr_normal (firstn al (bn_buf a)) (firstn max (bn_buf r)) in
            bset tmp (bn_with_buf tb (splice (bn_buf tb) 0 to)) ;;;
            bset rr (bn_with_buf r (splice (bn_buf r) 0 ro))) ;;;

       (r <- bget rr ;; bset rr (mkBN (bn_d r) (bn_buf r) max false (bn_flags r)))) ;;;
    BN_CTX_end ops).

Definition BN_sqr (rr ra : bnref) : BM unit :=
  bn_sqr_fixed_top rr ra ;;;
  (b <- bget rr ;; bset rr (bn_correct_top_pure b)).

Definition BN_nnmod (rr ra rm : bnref) : BM unit :=
  if (rr =? rm)%nat then bunr
  else
    BN_mod rr ra rm ;;;
    r <- bget rr ;;
    if negb (bn_neg r) then bret tt
    else
      m <- bget rm ;;
      if bn_neg m then BN_sub ops rr rr rm else BN_add ops rr rr rm.

Definition BN_mod_mul (rr ra rb rm : bnref) : BM unit :=
  BN_CTX_start ops ;;;
  t <- BN_CTX_get ops ;;
  (if (ra =? rb)%nat then BN_sqr t ra else BN_mul t ra rb) ;;;
  BN_nnmod rr t rm ;;;
  BN_CTX_end ops.

Fixpoint inv_shift_loop (fuel : nat) (rB rX rn : bnref) (shift : Z) : BM Z :=
  match fuel with
  | O => bunr
  | S f =>
      b <- bget rB ;;
      if is_bit_set_pure b shift then bret shift
      else
        x <- bget rX ;;
        (if is_odd_pure x then BN_uadd ops rX rX rn else bret tt) ;;;
        BN_rshift1 ops rX rX ;;;
        inv_shift_loop f rB rX rn (shift + 1)
  end.

Fixpoint inv_binary_loop (fuel : nat) (rA rB rX rY rn : bnref) : BM unit :=
  match fuel with
  | O => bunr
  | S f =>
      b <- bget rB ;;
      if is_zero_pure b then bret tt
      else
        shift <- inv_shift_loop (Z.to_nat (num_bits_pure b) + 1) rB rX rn 0 ;;
        (if 0 <? shift then BN_rshift ops rB rB shift else bret tt) ;;;
        a <- bget rA ;;
        shift <- inv_shift_loop (Z.to_nat (num_bits_pure a) + 1) rA rY rn 0 ;;
        (if 0 <? shift then BN_rshift ops rA rA shift else bret tt) ;;;
        c <- BN_ucmp ops rB rA ;;
        (if 0 <=? c then BN_uadd ops rX rX rY ;;; BN_usub ops rB rB rA
         else BN_uadd ops rY rY rX ;;; BN_usub ops rA rA rB) ;;;
        inv_binary_loop f rA rB rX rY rn
  end.

Definition BN_mod_inverse (rR ra rn : bnref) : BM unit :=
  n <- bget rn ;;
  a <- bget ra ;;
  if abs_is_word_pure n 1 || is_zero_pure n then bunr
  else if has_flag a BN_FLG_CONSTTIME || has_flag n BN_FLG_CONSTTIME then bunr
  else
    BN_CTX_start ops ;;;
    rA <- BN_CTX_get ops ;;
    rB <- BN_CTX_get ops ;;
    rX <- BN_CTX_get ops ;;
    rD <- BN_CTX_get ops ;;
    rM <- BN_CTX_get ops ;;
    rY <- BN_CTX_get ops ;;
    rT <- BN_CTX_get ops ;;
    BN_one ops rX ;;;
    BN_zero ops rY ;;;
    BN_copy ops rB ra ;;;
    BN_copy ops rA rn ;;;
    (b <- bget rA ;; bset rA (bn_with_neg b false)) ;;;
    bB <- bget rB ;;
    c <- BN_ucmp ops rB rA ;;
    (if bn_neg bB || (0 <=? c) then BN_nnmod rB rB rA else bret tt) ;;;
    nb <- BN_num_bits ops rn ;;
    n2 <- bget rn ;;
    (if is_odd_pure n2 && (nb <=? 2048) then
       inv_binary_loop (Z.to_nat (2 * nb) + 2) rA rB rX rY rn
     else bunr) ;;;

    BN_sub ops rY rn rY ;;;
    bA <- bget rA ;;
    (if is_one_pure bA then
       y <- bget rY ;;
       c <- BN_ucmp ops rY rn ;;
       if negb (bn_neg y) && (c <? 0) then BN_copy ops rR rY else BN_nnmod rR rY rn
     else bunr) ;;;
    BN_CTX_end ops.

End Arith.

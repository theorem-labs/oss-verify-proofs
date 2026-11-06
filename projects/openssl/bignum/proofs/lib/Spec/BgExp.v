(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BgState BgWords BgLib BgArith BgMont.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition neg_limbs (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: l' => negw x :: map (fun y => BW - 1 - y) l'
  end.

Section Exp.
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

Section Window.
Variable mulop : bnref -> bnref -> bnref -> BM unit.

Fixpoint exp_table_loop (cnt : nat) (vals : list bnref) (d : bnref) : BM (list bnref) :=
  match cnt with
  | O => bret vals
  | S c =>
      v <- BN_CTX_get ops ;;
      mulop v (last vals 0%nat) d ;;;
      exp_table_loop c (vals ++ [v]) d
  end.

Fixpoint exp_sqr_loop (cnt : nat) (r : bnref) : BM unit :=
  match cnt with
  | O => bret tt
  | S c => mulop r r r ;;; exp_sqr_loop c r
  end.

Fixpoint exp_window_loop (fuel : nat) (rp r : bnref) (vals : list bnref) (window wstart : Z) (start : bool) : BM unit :=
  match fuel with
  | O => bunr
  | S f =>
      p <- bget rp ;;
      if negb (is_bit_set_pure p wstart) then
        (if start then bret tt else mulop r r r) ;;;
        if wstart =? 0 then bret tt
        else exp_window_loop f rp r vals window (wstart - 1) start
      else
        let '(wvalue, wend) := window_scan (is_bit_set_pure p) wstart (Z.to_nat (window - 1)) 1 1 0 in
        (if start then bret tt else exp_sqr_loop (Z.to_nat (wend + 1)) r) ;;;
        mulop r r (nth (Z.to_nat (Z.shiftr wvalue 1)) vals 0%nat) ;;;
        let wstart := wstart - (wend + 1) in
        if wstart <? 0 then bret tt
        else exp_window_loop f rp r vals window wstart false
  end.

Definition exp_table (window : Z) (v0 d : bnref) : BM (list bnref) :=
  if 1 <? window then
    mulop d v0 v0 ;;;
    exp_table_loop (Z.to_nat (2 ^ (window - 1)) - 1) [v0] d
  else bret [v0].

End Window.

Definition exp_bits0 (rr rm : bnref) : BM unit :=
  m <- bget rm ;;
  if abs_is_word_pure m 1 then BN_zero ops rr else BN_one ops rr.

Definition any_consttime (l : list bnref) : BM bool :=
  fold_right (fun r acc => b <- bget r ;; x <- acc ;; bret (has_flag b BN_FLG_CONSTTIME || x)) (bret false) l.

Definition BN_mod_exp_mont (rr ra rp rm : bnref) : BM unit :=
  m <- bget rm ;;
  if negb (is_odd_pure m) then bunr
  else
    ct <- any_consttime [rp; ra; rm] ;;
    if ct then bunr
    else
      bits <- BN_num_bits ops rp ;;
      if bits =? 0 then exp_bits0 rr rm
      else
        BN_CTX_start ops ;;;
        d <- BN_CTX_get ops ;;
        r <- BN_CTX_get ops ;;
        v0 <- BN_CTX_get ops ;;
        pm <- BN_MONT_CTX_new ops ;;
        BN_MONT_CTX_set ops rm ;;;
        a <- bget ra ;;
        c <- BN_ucmp ops ra rm ;;
        aa <- (if bn_neg a || (0 <=? c) then BN_nnmod ops v0 ra rm ;;; bret v0 else bret ra) ;;
        bn_to_mont_fixed_top ops v0 aa ;;;
        let window := window_bits bits in
        vals <- exp_table (bn_mul_mont_fixed_top ops) window v0 d ;;

        m <- bget rm ;;
        let j := bn_top m in

        if (j =? 0)%nat then bunr else
        (if Z.testbit (nth (j - 1) (bn_buf m) 0) 63 then

           if (r =? rm)%nat then bunr else
           bn_wexpand ops r j ;;;
           rb <- bget r ;;
           m <- bget rm ;;
           bset r (mkBN (bn_d rb) (splice (bn_buf rb) 0 (neg_limbs (firstn j (bn_buf m)))) j (bn_neg rb) (bn_flags rb))
         else bn_to_mont_fixed_top ops r ROne) ;;;
        exp_window_loop (bn_mul_mont_fixed_top ops) (Z.to_nat bits) rp r vals window (bits - 1) true ;;;
        BN_from_montgomery ops rr r ;;;
        BN_MONT_CTX_free ops pm ;;;
        BN_CTX_end ops.

Definition mw_mod_mul_word (r t : bnref) (w : Z) (rm : bnref) : BM (bnref * bnref) :=
  BN_mul_word ops r w ;;;
  BN_mod ops t r rm ;;;
  bret (t, r).

Definition mw_to_mont_word (r : bnref) (w : Z) : BM unit :=
  BN_set_word ops r w ;;;
  BN_to_montgomery ops r r.

Definition mw_flush (r t : bnref) (w : Z) (r_is_one : bool) (rm : bnref) : BM (bnref * bnref) :=
  if r_is_one then mw_to_mont_word r w ;;; bret (r, t) else mw_mod_mul_word r t w rm.

Fixpoint mw_loop (cnt : nat) (a : Z) (rp rm : bnref) (st : bnref * bnref * Z * bool) : BM (bnref * bnref * Z * bool) :=
  match cnt with
  | O => bret st
  | S c =>
      let '(r, t, w, r_is_one) := st in
      let b := Z.of_nat c in

      let next_w := mulw w w in
      let ovf := negb (next_w / w =? w) in
      rt <- (if ovf then mw_flush r t w r_is_one rm else bret (r, t)) ;;
      let '(r, t) := rt in
      let r_is_one := if ovf then false else r_is_one in
      let w := if ovf then 1 else next_w in
      (if r_is_one then bret tt else BN_mod_mul_montgomery ops r r r) ;;;

      p <- bget rp ;;
      if is_bit_set_pure p b then
        let next_w := mulw w a in
        let ovf := negb (next_w / a =? w) in
        rt <- (if ovf then mw_flush r t w r_is_one rm else bret (r, t)) ;;
        let '(r, t) := rt in
        let r_is_one := if ovf then false else r_is_one in
        let w := if ovf then a else next_w in
        mw_loop c a rp rm (r, t, w, r_is_one)
      else mw_loop c a rp rm (r, t, w, r_is_one)
  end.

Definition BN_mod_exp_mont_word (rr : bnref) (a : Z) (rp rm : bnref) : BM unit :=
  ct <- any_consttime [rp; rm] ;;
  if ct then bunr
  else
    m <- bget rm ;;
    if negb (is_odd_pure m) then bunr
    else
      let a := if (bn_top m =? 1)%nat then a mod (nth 0 (bn_buf m) 0) else a in
      bits <- BN_num_bits ops rp ;;
      if bits =? 0 then exp_bits0 rr rm
      else if a =? 0 then BN_zero ops rr
      else
        BN_CTX_start ops ;;;
        r <- BN_CTX_get ops ;;
        t <- BN_CTX_get ops ;;
        pm <- BN_MONT_CTX_new ops ;;
        BN_MONT_CTX_set ops rm ;;;
        st <- mw_loop (Z.to_nat (bits - 1)) a rp rm (r, t, a, true) ;;
        let '(r, t, w, r_is_one) := st in

        rt <- (if w =? 1 then bret (r, t) else mw_flush r t w r_is_one rm) ;;
        let '(r, t) := rt in
        let r_is_one := if w =? 1 then r_is_one else false in
        (if r_is_one then BN_one ops rr else BN_from_montgomery ops rr r) ;;;
        BN_MONT_CTX_free ops pm ;;;
        BN_CTX_end ops.

Definition BN_mod_exp_recp (rr ra rp rm : bnref) : BM unit :=
  ct <- any_consttime [rp; ra; rm] ;;
  if ct then bunr
  else
    bits <- BN_num_bits ops rp ;;
    if bits =? 0 then exp_bits0 rr rm
    else
      BN_RECP_CTX_init ops ;;;
      BN_CTX_start ops ;;;
      aa <- BN_CTX_get ops ;;
      v0 <- BN_CTX_get ops ;;
      m <- bget rm ;;
      (if bn_neg m then
         BN_copy ops aa rm ;;;
         (x <- bget aa ;; bset aa (bn_with_neg x false)) ;;;
         BN_RECP_CTX_set ops aa
       else BN_RECP_CTX_set ops rm) ;;;
      BN_nnmod ops v0 ra rm ;;;
      x <- bget v0 ;;
      (if is_zero_pure x then BN_zero ops rr
       else
         let window := window_bits bits in
         vals <- exp_table (BN_mod_mul_reciprocal ops) window v0 aa ;;
         if (rr =? rp)%nat then bunr
         else
           BN_one ops rr ;;;
           exp_window_loop (BN_mod_mul_reciprocal ops) (Z.to_nat bits) rp rr vals window (bits - 1) true) ;;;
      BN_CTX_end ops ;;;
      BN_RECP_CTX_free ops.

Definition BN_mod_exp_simple (rr ra rp rm : bnref) : BM unit :=
  ct <- any_consttime [rp; ra; rm] ;;
  if ct then bunr
  else if (rr =? rm)%nat then bunr
  else
    bits <- BN_num_bits ops rp ;;
    if bits =? 0 then exp_bits0 rr rm
    else
      BN_CTX_start ops ;;;
      d <- BN_CTX_get ops ;;
      v0 <- BN_CTX_get ops ;;
      BN_nnmod ops v0 ra rm ;;;
      x <- bget v0 ;;
      (if is_zero_pure x then BN_zero ops rr
       else
         let window := window_bits bits in
         let mulop := fun r a b => BN_mod_mul ops r a b rm in
         vals <- exp_table mulop window v0 d ;;
         if (rr =? rp)%nat then bunr
         else
           BN_one ops rr ;;;
           exp_window_loop mulop (Z.to_nat bits) rp rr vals window (bits - 1) true) ;;;
      BN_CTX_end ops.

Definition BN_mod_exp (rr ra rp rm : bnref) : BM unit :=
  m <- bget rm ;;
  if is_odd_pure m then
    a <- bget ra ;;
    ct <- any_consttime [rp; ra; rm] ;;
    if (bn_top a =? 1)%nat && negb (bn_neg a) && negb ct
    then BN_mod_exp_mont_word rr (nth 0 (bn_buf a) 0) rp rm
    else BN_mod_exp_mont rr ra rp rm
  else BN_mod_exp_recp rr ra rp rm.

Definition bg_split (data : list Z) : list Z * list Z * list Z * bool * bool :=
  if (2 <? length data)%nat then
    let len := Z.of_nat (length data) - 3 in
    let k0 := nth 0 data 0 mod 256 in
    let k1 := nth 1 data 0 mod 256 in
    let k2 := nth 2 data 0 mod 256 in
    let l1 := ((k0 * len) / 255) mod 512 in
    let l2 := ((k1 * (len - l1)) / 255) mod 512 in
    let l3 := (len - l1 - l2) mod 512 in
    let buf := skipn 3 data in
    (firstn (Z.to_nat l1) buf,
     firstn (Z.to_nat l2) (skipn (Z.to_nat l1) buf),
     firstn (Z.to_nat l3) (skipn (Z.to_nat (l1 + l2)) buf),
     Z.testbit k2 0, Z.testbit k2 2)
  else ([], [], [], false, false).

Definition fuzz_one (data : list Z) : BM Z :=
  p1 <- BN_new ops RB1 ;;
  p2 <- BN_new ops RB2 ;;
  p3 <- BN_new ops RB3 ;;
  p4 <- BN_new ops RB4 ;;
  p5 <- BN_new ops RB5 ;;
  pc <- BN_CTX_new ops ;;
  let '(n1, n2, n3, s1, s3) := bg_split data in
  BN_bin2bn ops n1 RB1 ;;;
  BN_set_negative ops RB1 s1 ;;;
  BN_bin2bn ops n2 RB2 ;;;
  BN_bin2bn ops n3 RB3 ;;;
  BN_set_negative ops RB3 s3 ;;;
  b3 <- bget RB3 ;;
  (if is_zero_pure b3 then bret tt
   else
     BN_mod_exp RB4 RB1 RB2 RB3 ;;;
     BN_mod_exp_simple RB5 RB1 RB2 RB3 ;;;
     b4 <- bget RB4 ;;
     b5 <- bget RB5 ;;
     if cmp_pure b4 b5 =? 0 then bret tt
     else bunr) ;;;

  BN_free ops RB1 (Some p1) ;;;
  BN_free ops RB2 (Some p2) ;;;
  BN_free ops RB3 (Some p3) ;;;
  BN_free ops RB4 (Some p4) ;;;
  BN_free ops RB5 (Some p5) ;;;
  BN_CTX_free ops pc ;;;

  bret 0.

End Exp.

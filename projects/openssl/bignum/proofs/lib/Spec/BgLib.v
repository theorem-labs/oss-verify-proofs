(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BgState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition has_flag {ptr} (b : bignum ptr) (f : Z) : bool := negb (Z.land (bn_flags b) f =? 0).

Definition num_bits_pure {ptr} (a : bignum ptr) : Z :=
  if (bn_top a =? 0)%nat then 0
  else (Z.of_nat (bn_top a) - 1) * 64 + num_bits_word (nth (bn_top a - 1) (bn_buf a) 0).

Definition is_bit_set_pure {ptr} (a : bignum ptr) (n : Z) : bool :=
  if n <? 0 then false
  else let i := Z.to_nat (n / 64) in
       if (bn_top a <=? i)%nat then false else Z.testbit (nth i (bn_buf a) 0) (n mod 64).

Definition is_odd_pure {ptr} (a : bignum ptr) : bool := (0 <? bn_top a)%nat && Z.odd (nth 0 (bn_buf a) 0).

Definition abs_is_word_pure {ptr} (a : bignum ptr) (w : Z) : bool :=
  ((bn_top a =? 1)%nat && (nth 0 (bn_buf a) 0 =? w)) || ((w =? 0) && (bn_top a =? 0)%nat).

Definition is_one_pure {ptr} (a : bignum ptr) : bool := abs_is_word_pure a 1 && negb (bn_neg a).

Definition is_zero_pure {ptr} (a : bignum ptr) : bool := (bn_top a =? 0)%nat.

Fixpoint add_word_limbs (l : list Z) (w : Z) : list Z * Z :=
  match l with
  | [] => ([], w)
  | x :: l' => if w =? 0 then (l, w)
               else let s := addw x w in
                    let '(r, w') := add_word_limbs l' (if s <? w then 1 else 0) in (s :: r, w')
  end.

Fixpoint sub_word_limbs (l : list Z) (w : Z) (i : nat) : list Z * nat :=
  match l with
  | [] => ([], i)
  | x :: l' => if w <=? x then ((x - w) :: l', i)
               else let '(r, i') := sub_word_limbs l' 1 (S i) in (subw x w :: r, i')
  end.

Definition item_prev (cur : option nat) : option nat :=
  match cur with Some (S i) => Some i | _ => None end.
Fixpoint pool_release (num : nat) (offset : nat) (cur : option nat) : option nat :=
  match num with
  | O => cur
  | S n => if (offset =? 0)%nat then pool_release n 15 (item_prev cur) else pool_release n (offset - 1) cur
  end.

Definition BN_MASK2 : Z := BW - 1.
Definition BN_STRUCT_BYTES : Z := 24.
Definition BN_CTX_BYTES : Z := 72.

Section Lib.
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

Definition bn_wexpand (r : bnref) (words : nat) : BM unit :=
  b <- bget r ;;
  if (words <=? bn_dmax b)%nat then bret tt
  else if BN_WORDS_MAX <? Z.of_nat words then bunr
  else if 512 <? Z.of_nat words then bunr
  else if has_flag b BN_FLG_STATIC_DATA then bunr
  else if has_flag b BN_FLG_SECURE then bunr
  else
    p <- bmalloc ops (8 * Z.of_nat words) ;;
    bfree_opt ops (bn_d b) ;;;
    bset r (mkBN (Some p) (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) (bn_top b) (bn_neg b) (bn_flags b)).

Definition BN_copy (ra rb : bnref) : BM unit :=
  b <- bget rb ;;
  if has_flag b BN_FLG_CONSTTIME then bunr
  else if (ra =? rb)%nat then bret tt
  else
    bn_wexpand ra (bn_top b) ;;;
    a <- bget ra ;;
    let buf := if (0 <? bn_top b)%nat then splice (bn_buf a) 0 (firstn (bn_top b) (bn_buf b)) else bn_buf a in
    bset ra (mkBN (bn_d a) buf (bn_top b) (bn_neg b) (bn_flags a)).

Definition BN_bin2bn (s : list Z) (r : bnref) : BM unit :=
  b <- bget r ;;
  match s with
  | [] =>
      bset r (mkBN (bn_d b) (repeat 0 (bn_dmax b)) 0 false (bn_flags b))
  | _ :: _ =>
      let s' := skip_zero_bytes s in
      match s' with
      | [] => bset r (bn_with_top b 0)
      | _ :: _ =>
          let n := ((length s' - 1) / 8 + 1)%nat in
          bn_wexpand r n ;;;
          b <- bget r ;;
          bset r (bn_correct_top_pure (mkBN (bn_d b) (splice (bn_buf b) 0 (bin2bn_limbs s')) n false (bn_flags b)))
      end
  end.

Definition BN_set_negative (r : bnref) (sgn : bool) : BM unit :=
  b <- bget r ;; bset r (bn_with_neg b (sgn && negb (bn_top b =? 0)%nat)).

Definition BN_zero (r : bnref) : BM unit := b <- bget r ;; bset r (bn_zero_pure b).

Definition BN_set_word (r : bnref) (w : Z) : BM unit :=
  bn_wexpand r 1 ;;;
  b <- bget r ;;
  bset r (mkBN (bn_d b) (upd (bn_buf b) 0 w) (if w =? 0 then 0%nat else 1%nat) false (bn_flags b)).

Definition BN_one (r : bnref) : BM unit := BN_set_word r 1.

Definition BN_set_bit (r : bnref) (n : Z) : BM unit :=
  if n <? 0 then bunr
  else
    let i := Z.to_nat (n / 64) in
    let j := n mod 64 in
    a <- bget r ;;
    (if (bn_top a <=? i)%nat then
       bn_wexpand r (i + 1) ;;;
       b <- bget r ;;

       bset r (mkBN (bn_d b) (splice (bn_buf b) (bn_top b) (repeat 0 (i + 1 - bn_top b))) (i + 1) (bn_neg b) (bn_flags b))
     else bret tt) ;;;
    b <- bget r ;;
    bset r (bn_with_buf b (upd (bn_buf b) i (Z.lor (nth i (bn_buf b) 0) (2 ^ j)))).

Definition BN_num_bits (r : bnref) : BM Z :=
  a <- bget r ;; if has_flag a BN_FLG_CONSTTIME then bunr else bret (num_bits_pure a).

Definition BN_ucmp (ra rb : bnref) : BM Z :=
  a <- bget ra ;;
  b <- bget rb ;;
  if has_flag a BN_FLG_CONSTTIME || has_flag b BN_FLG_CONSTTIME then bunr
  else bret (ucmp_pure a b).

Definition BN_new (r : bnref) : BM ptr :=
  p <- bmalloc ops BN_STRUCT_BYTES ;;
  bset r (bn_nil BN_FLG_MALLOCED) ;;;
  bret p.

Definition BN_free (r : bnref) (sp : option ptr) : BM unit :=
  b <- bget r ;;
  (if has_flag b BN_FLG_STATIC_DATA then bret tt else bfree_opt ops (bn_d b)) ;;;
  (if has_flag b BN_FLG_MALLOCED then match sp with Some p => bfree ops p | None => bunr end else bret tt) ;;;
  bset r (bn_nil 0).

Definition BN_clear_free (r : bnref) (sp : option ptr) : BM unit :=
  b <- bget r ;;
  (if has_flag b BN_FLG_STATIC_DATA then bret tt else bfree_opt ops (bn_d b)) ;;;
  (if has_flag b BN_FLG_MALLOCED then match sp with Some p => bfree ops p | None => bunr end else bret tt) ;;;
  bset r (bn_nil 0).

Definition BN_CTX_new : BM ptr :=
  p <- bmalloc ops BN_CTX_BYTES ;;
  bsetctx ops gx_nil ;;;
  bret p.

Definition BN_CTX_start : BM unit :=
  c <- bgetctx ops ;;
  if negb (gx_err_stack c =? 0)%nat || gx_too_many c then bunr
  else
    let depth := length (gx_frames c) in
    if (depth =? gx_ssize c)%nat then

      if negb (gx_ssize c =? 0)%nat then bunr
      else
        p <- bmalloc ops (4 * Z.of_nat BN_CTX_START_FRAMES) ;;
        bfree_opt ops (gx_indexes c) ;;;
        bsetctx ops (mkGx (gx_items c) (gx_current c) (gx_pused c) (Some p)
                          (gx_frames c ++ [gx_used c]) BN_CTX_START_FRAMES (gx_used c) 0 false)
    else
      bsetctx ops (mkGx (gx_items c) (gx_current c) (gx_pused c) (gx_indexes c)
                        (gx_frames c ++ [gx_used c]) (gx_ssize c) (gx_used c) 0 false).

Definition BN_CTX_get : BM bnref :=
  c <- bgetctx ops ;;
  if negb (gx_err_stack c =? 0)%nat || gx_too_many c then bunr
  else
    let psize := (BN_CTX_POOL_SIZE * length (gx_items c))%nat in
    i <- (if (gx_pused c =? psize)%nat then
            if (3 <=? length (gx_items c))%nat then bunr
            else
            p <- bmalloc ops POOL_ITEM_BYTES ;;
            s <- bgetst ops ;;
            bsetbns ops (st_bns s ++ repeat (bn_nil 0) BN_CTX_POOL_SIZE) ;;;
            bsetctx ops (mkGx (gx_items c ++ [p]) (Some (length (gx_items c))) (S (gx_pused c))
                              (gx_indexes c) (gx_frames c) (gx_ssize c) (gx_used c) 0 false) ;;;
            bret (gx_pused c)
          else
            let cur := if (gx_pused c =? 0)%nat then Some 0%nat
                       else if (gx_pused c mod BN_CTX_POOL_SIZE =? 0)%nat
                            then match gx_current c with Some k => Some (S k) | None => None end
                            else gx_current c in
            bsetctx ops (mkGx (gx_items c) cur (S (gx_pused c))
                              (gx_indexes c) (gx_frames c) (gx_ssize c) (gx_used c) 0 false) ;;;
            bret (gx_pused c)) ;;
    b <- bget (RPool i) ;;
    bset (RPool i) (bn_zero_pure b) ;;;
    c <- bgetctx ops ;;
    bsetctx ops (mkGx (gx_items c) (gx_current c) (gx_pused c)
                      (gx_indexes c) (gx_frames c) (gx_ssize c) (S (gx_used c)) 0 false) ;;;
    bret (RPool i).

Definition BN_CTX_end : BM unit :=
  c <- bgetctx ops ;;
  if negb (gx_err_stack c =? 0)%nat then bunr
  else
    match rev (gx_frames c) with
    | [] => bunr
    | fp :: rest =>
        let num := (gx_used c - fp)%nat in
        let pused := if (fp <? gx_used c)%nat then (gx_pused c - num)%nat else gx_pused c in
        let cur := if (fp <? gx_used c)%nat
                   then pool_release num ((gx_pused c - 1) mod BN_CTX_POOL_SIZE) (gx_current c)
                   else gx_current c in
        bsetctx ops (mkGx (gx_items c) cur pused (gx_indexes c) (rev rest) (gx_ssize c) fp 0 false)
    end.

Fixpoint pool_free_vals (i cnt : nat) : BM unit :=
  match cnt with
  | O => bret tt
  | S n => b <- bget (RPool i) ;;
           (match bn_d b with Some _ => BN_clear_free (RPool i) None | None => bret tt end) ;;;
           pool_free_vals (S i) n
  end.

Fixpoint pool_finish (items : list ptr) (k : nat) : BM unit :=
  match items with
  | [] => bret tt
  | it :: rest => pool_free_vals (BN_CTX_POOL_SIZE * k) BN_CTX_POOL_SIZE ;;; bfree ops it ;;; pool_finish rest (S k)
  end.

Definition BN_CTX_free (pc : ptr) : BM unit :=
  c <- bgetctx ops ;;
  bfree_opt ops (gx_indexes c) ;;;
  pool_finish (gx_items c) 0 ;;;
  bfree ops pc ;;;
  s <- bgetst ops ;;
  bsetbns ops (firstn NFIX (st_bns s)) ;;;
  bsetctx ops gx_nil.

Definition bn_lshift_fixed_top (rr ra : bnref) (n : Z) : BM unit :=
  if n <? 0 then bunr
  else
    let nw := Z.to_nat (n / 64) in
    let lb := n mod 64 in
    a0 <- bget ra ;;
    bn_wexpand rr (bn_top a0 + nw + 1) ;;;
    a <- bget ra ;;
    r <- bget rr ;;
    let buf := if (bn_top a =? 0)%nat then upd (bn_buf r) nw 0
               else let '(ls, mo) := lshift_limbs (firstn (bn_top a) (bn_buf a)) lb 0 in
                    splice (bn_buf r) nw (ls ++ [mo]) in
    let buf := if (nw =? 0)%nat then buf else splice buf 0 (repeat 0 nw) in
    bset rr (mkBN (bn_d r) buf (bn_top a + nw + 1) (bn_neg a) (bn_flags r)).

Definition BN_lshift (rr ra : bnref) (n : Z) : BM unit :=
  if n <? 0 then bunr
  else bn_lshift_fixed_top rr ra n ;;; (b <- bget rr ;; bset rr (bn_correct_top_pure b)).

Definition bn_rshift_fixed_top (rr ra : bnref) (n : Z) : BM unit :=
  if n <? 0 then bunr
  else
    let nw := Z.to_nat (n / 64) in
    let rb := n mod 64 in
    a <- bget ra ;;
    if (bn_top a <=? nw)%nat then BN_zero rr
    else
      let top := (bn_top a - nw)%nat in
      (if (rr =? ra)%nat then bret tt else bn_wexpand rr top) ;;;
      a <- bget ra ;;
      r <- bget rr ;;
      bset rr (mkBN (bn_d r) (splice (bn_buf r) 0 (rshift_limbs (slice (bn_buf a) nw top) rb))
                    top (bn_neg a) (bn_flags r)).

Definition BN_rshift (rr ra : bnref) (n : Z) : BM unit :=
  if n <? 0 then bunr
  else bn_rshift_fixed_top rr ra n ;;; (b <- bget rr ;; bset rr (bn_correct_top_pure b)).

Definition BN_rshift1 (rr ra : bnref) : BM unit :=
  a <- bget ra ;;
  if (bn_top a =? 0)%nat then BN_zero rr
  else
    let i := bn_top a in
    (if (rr =? ra)%nat then bret tt
     else bn_wexpand rr i ;;; (r <- bget rr ;; bset rr (bn_with_neg r (bn_neg a)))) ;;;
    a <- bget ra ;;
    r <- bget rr ;;
    let t := nth (i - 1) (bn_buf a) 0 in
    let top := if t =? 1 then (i - 1)%nat else i in
    bset rr (mkBN (bn_d r) (splice (bn_buf r) 0 (rshift_limbs (firstn i (bn_buf a)) 1)) top
                  (if (top =? 0)%nat then false else bn_neg r) (bn_flags r)).

Definition BN_add_word (r : bnref) (w : Z) : BM unit :=
  if w =? 0 then bret tt
  else
    a <- bget r ;;
    if (bn_top a =? 0)%nat then BN_set_word r w
    else if bn_neg a then bunr
    else
      let '(l, w') := add_word_limbs (firstn (bn_top a) (bn_buf a)) w in
      bset r (bn_with_buf a (splice (bn_buf a) 0 l)) ;;;
      if w' =? 0 then bret tt
      else
        bn_wexpand r (bn_top a + 1) ;;;
        b <- bget r ;;
        bset r (mkBN (bn_d b) (upd (bn_buf b) (bn_top a) w') (bn_top a + 1) (bn_neg b) (bn_flags b)).

Definition BN_sub_word (r : bnref) (w : Z) : BM unit :=
  if w =? 0 then bret tt
  else
    a <- bget r ;;
    if (bn_top a =? 0)%nat then bunr
    else if bn_neg a then bunr
    else if (bn_top a =? 1)%nat && (nth 0 (bn_buf a) 0 <? w) then
      bset r (mkBN (bn_d a) (upd (bn_buf a) 0 (w - nth 0 (bn_buf a) 0)) (bn_top a) true (bn_flags a))
    else
      let '(l, i) := sub_word_limbs (firstn (bn_top a) (bn_buf a)) w 0 in
      let buf := splice (bn_buf a) 0 l in
      let top := if (nth i buf 0 =? 0) && (i =? bn_top a - 1)%nat then (bn_top a - 1)%nat else bn_top a in
      bset r (mkBN (bn_d a) buf top (bn_neg a) (bn_flags a)).

Definition BN_mul_word (r : bnref) (w : Z) : BM unit :=
  a <- bget r ;;
  if (bn_top a =? 0)%nat then bret tt
  else if w =? 0 then BN_zero r
  else
    let '(l, ll) := mul_words (firstn (bn_top a) (bn_buf a)) w in
    bset r (bn_with_buf a (splice (bn_buf a) 0 l)) ;;;
    if ll =? 0 then bret tt
    else
      bn_wexpand r (bn_top a + 1) ;;;
      b <- bget r ;;
      bset r (mkBN (bn_d b) (upd (bn_buf b) (bn_top a) ll) (bn_top a + 1) (bn_neg b) (bn_flags b)).

Definition BN_uadd (rr ra rb : bnref) : BM unit :=
  a0 <- bget ra ;;
  b0 <- bget rb ;;
  let '(ra, rb) := if (bn_top a0 <? bn_top b0)%nat then (rb, ra) else (ra, rb) in
  a <- bget ra ;;
  b <- bget rb ;;
  let max := bn_top a in
  let min := bn_top b in
  bn_wexpand rr (max + 1) ;;;
  (r <- bget rr ;; bset rr (bn_with_top r max)) ;;;
  (if (max =? 0)%nat then bret tt
   else
     a <- bget ra ;;
     b <- bget rb ;;
     r <- bget rr ;;
     let '(s, carry) := add_words (firstn min (bn_buf a)) (firstn min (bn_buf b)) in
     let '(s2, carry) := add_carry_words (slice (bn_buf a) min (max - min)) carry in
     bset rr (mkBN (bn_d r) (splice (bn_buf r) 0 (s ++ s2 ++ [carry])) (max + Z.to_nat carry) (bn_neg r) (bn_flags r))) ;;;
  (r <- bget rr ;; bset rr (bn_with_neg r false)).

Definition BN_usub (rr ra rb : bnref) : BM unit :=
  a <- bget ra ;;
  b <- bget rb ;;
  let max := bn_top a in
  let min := bn_top b in
  if (max <? min)%nat then bunr
  else
    bn_wexpand rr max ;;;
    (if (max =? 0)%nat then bret tt
     else
       a <- bget ra ;;
       b <- bget rb ;;
       r <- bget rr ;;
       let '(s, borrow) := sub_words (firstn min (bn_buf a)) (firstn min (bn_buf b)) in
       let '(s2, _) := sub_part_pos (slice (bn_buf a) min (max - min)) borrow in
       bset rr (bn_with_buf r (splice (bn_buf r) 0 (s ++ s2)))) ;;;

    (r <- bget rr ;; bset rr (mkBN (bn_d r) (bn_buf r) (strip_top (bn_buf r) max) false (bn_flags r))).

Definition BN_add (rr ra rb : bnref) : BM unit :=
  a <- bget ra ;;
  b <- bget rb ;;
  r_neg <- (if Bool.eqb (bn_neg a) (bn_neg b) then
              BN_uadd rr ra rb ;;; bret (bn_neg a)
            else
              c <- BN_ucmp ra rb ;;
              if 0 <? c then BN_usub rr ra rb ;;; bret (bn_neg a)
              else if c <? 0 then BN_usub rr rb ra ;;; bret (bn_neg b)
              else BN_zero rr ;;; bret false) ;;
  r <- bget rr ;; bset rr (bn_with_neg r r_neg).

Definition BN_sub (rr ra rb : bnref) : BM unit :=
  a <- bget ra ;;
  b <- bget rb ;;
  r_neg <- (if negb (Bool.eqb (bn_neg a) (bn_neg b)) then
              BN_uadd rr ra rb ;;; bret (bn_neg a)
            else
              c <- BN_ucmp ra rb ;;
              if 0 <? c then BN_usub rr ra rb ;;; bret (bn_neg a)
              else if c <? 0 then BN_usub rr rb ra ;;; bret (negb (bn_neg b))
              else BN_zero rr ;;; bret false) ;;
  r <- bget rr ;; bset rr (bn_with_neg r r_neg).

End Lib.

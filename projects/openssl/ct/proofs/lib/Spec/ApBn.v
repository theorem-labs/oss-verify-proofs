(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim PrintfModel BnBase BnWords BnModel BnTree BgState BgLib ApFmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition RBL : bnref := 0%nat.
Definition RT : bnref := 1%nat.
Definition abs0 {ptr} : bstate ptr := mkST [bn_nil 0; bn_nil 0] gx_nil 0 0 0 0.

Definition BN_DEC_CONV : Z := 10000000000000000000.   (* [comment removed for export] *)
Definition BN_DEC_NUM : Z := 19.
Definition ULONG_MAX_SHR7 : Z := 144115188075855871.    (* [comment removed for export] *)

Section Bn.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : bn_ops M ptr.

Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation BM := (BM (M:=M) (ptr:=ptr)) (only parsing).
Local Notation "x <- m ;; k" := (bbind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bbind ops m (fun _ => k)) (at level 61, right associativity).
Local Notation "' pat <- m ;; k" := (bbind ops m (fun x__ => let 'pat := x__ in k)) (at level 61, pat pattern, m at next level, right associativity).
Local Notation bret := (bret ops).
Local Notation bunr := (bunr ops).
Local Notation bget := (bget ops).
Local Notation bset := (bset ops).

(* [comment removed for export] *)
Definition BN_dup (rt ra : bnref) : BM ptr :=
  p <- BN_new ops rt ;;
  BN_copy ops rt ra ;;;
  bret p.

(* [comment removed for export] *)
Fixpoint div_word_loop (i : nat) (buf : list Z) (w ret : Z) {struct i} : list Z * Z :=
  match i with
  | O => (buf, ret)
  | S i' =>
      let l := nth i' buf 0 in
      let d := div_words ret l w in
      let ret' := subw l (mulw d w) in
      div_word_loop i' (upd buf i' d) w ret'
  end.

Definition BN_div_word (r : bnref) (w : Z) : BM Z :=
  let w := Z.land w (BW - 1) in
  if w =? 0 then bunr                                                  (* [comment removed for export] *)
  else
    a <- bget r ;;
    if (bn_top a =? 0)%nat then bret 0
    else
      let j := 64 - num_bits_word w in
      let w := shlw w j in
      BN_lshift ops r r j ;;;                                            (* [comment removed for export] *)
      a <- bget r ;;
      let '(buf, ret) := div_word_loop (bn_top a) (bn_buf a) w 0 in
      let top := if (0 <? bn_top a)%nat && (nth (bn_top a - 1) buf 0 =? 0) then (bn_top a - 1)%nat else bn_top a in
      let ret := shrw ret j in
      bset r (mkBN (bn_d a) buf top (if (top =? 0)%nat then false else bn_neg a) (bn_flags a)) ;;;
      bret ret.

(* [comment removed for export] *)
Fixpoint bn2dec_loop (fuel : nat) (rt : bnref) (acc : list Z) {struct fuel} : BM (option (list Z)) :=
  match fuel with
  | O => t <- bget rt ;; if is_zero_pure t then bret (Some acc) else bret None    (* [comment removed for export] *)
  | S fuel' =>
      t <- bget rt ;;
      if is_zero_pure t then bret (Some acc)
      else w <- BN_div_word rt BN_DEC_CONV ;; bn2dec_loop fuel' rt (w :: acc)    (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Definition BN_bn2dec (rt ra : bnref) : BM (ptr * Z) :=
  a <- bget ra ;;
  let i := num_bits_pure a * 3 in
  let num := i / 10 + i / 1000 + 1 + 1 in
  let tbytes := num + 3 in
  let bn_data_num := num / BN_DEC_NUM + 1 in
  bn_data <- bmalloc ops (bn_data_num * 8) ;;                            (* [comment removed for export] *)
  buf <- bmalloc ops tbytes ;;
  tp <- BN_dup rt ra ;;
  t <- bget rt ;;
  r <- (if is_zero_pure t then bret (Some 1)                           (* [comment removed for export] *)
        else
          let neg := bn_neg t in
          ws <- bn2dec_loop (Z.to_nat bn_data_num) rt [] ;;
          match ws with
          | None => bret None
          | Some [] => bret None                                         (* [comment removed for export] *)
          | Some (w0 :: ws') =>
              (* [comment removed for export] *)
              let slen := (if neg then 1 else 0) + zdigits w0 + BN_DEC_NUM * zlength ws' in
              if tbytes <=? slen then bret None else bret (Some slen)
          end) ;;
  match r with
  | None => bunr                                                       (* [comment removed for export] *)
  | Some slen =>
      bfree ops bn_data ;;;
      BN_free ops rt (Some tp) ;;;
      bret (buf, slen)
  end.

(* [comment removed for export] *)
Record o2t : Type := mkO2T { o_l : Z; o_bn : bool; o_insub : bool; o_first : bool; o_n : Z }.

Definition o2t_init : o2t := mkO2T 0 false false true 0.

(* [comment removed for export] *)
Definition o2t_emit (st : o2t) (blp : option ptr) : BM (o2t * option ptr) :=
  (* [comment removed for export] *)
  st1 <- (if o_first st then
            (if o_bn st then
               (b <- bget RBL ;;
                (* [comment removed for export] *)
                BN_sub_word ops RBL 80 ;;; bret (mkO2T (o_l st) true (o_insub st) false (o_n st + 1)))
             else if 80 <=? o_l st then bret (mkO2T (o_l st - 80) false (o_insub st) false (o_n st + 1))
             else let i := o_l st / 40 in bret (mkO2T (o_l st - i * 40) false (o_insub st) false (o_n st + 1)))
          else bret st) ;;
  if o_bn st1 then
    ' (bndec, i) <- BN_bn2dec RT RBL ;;
    bfree ops bndec ;;;
    bret (mkO2T (o_l st1) false false false (o_n st1 + 1 + i), blp)
  else
    bret (mkO2T 0 false false false (o_n st1 + dotlu_len (o_l st1)), blp).

Fixpoint o2t_bytes (bytes : list Z) (st : o2t) (blp : option ptr) {struct bytes} : BM (option Z * option ptr) :=
  match bytes with
  | [] => bret (Some (o_n st), blp)
  | c :: rest =>
      (* [comment removed for export] *)
      let st := if o_insub st then st else mkO2T 0 false true (o_first st) (o_n st) in
      let low := Z.land c 127 in
      let cont := negb (Z.land c 128 =? 0) in
      match rest, cont with
      | [], true => bret (None, blp)                                    (* [comment removed for export] *)
      | _, _ =>
          (* [comment removed for export] *)
          st1 <- (if o_bn st then BN_add_word ops RBL low ;;; bret st
                  else bret (mkO2T (Z.lor (o_l st) low) false true (o_first st) (o_n st))) ;;
          if negb cont then
            ' (st2, blp2) <- o2t_emit st1 blp ;;
            o2t_bytes rest st2 blp2
          else
            (* [comment removed for export] *)
            ' (st2, blp2) <- (if negb (o_bn st1) && (ULONG_MAX_SHR7 <? o_l st1) then
                                (blp' <- match blp with
                                         | None => p <- BN_new ops RBL ;; bret (Some p)
                                         | Some p => bret (Some p)
                                         end ;;
                                 BN_set_word ops RBL (o_l st1) ;;;
                                 bret (mkO2T (o_l st1) true true (o_first st1) (o_n st1), blp'))
                              else bret (st1, blp)) ;;
            (if o_bn st2 then BN_lshift ops RBL RBL 7 ;;; o2t_bytes rest st2 blp2
             else o2t_bytes rest (mkO2T (Z.land (Z.shiftl (o_l st2) 7) (BW - 1)) false true (o_first st2) (o_n st2)) blp2)
      end
  end.

(* [comment removed for export] *)
Definition obj2txt_num (content : list Z) : BM Z :=
  ' (r, blp) <- o2t_bytes content o2t_init None ;;
  (match blp with Some p => BN_free ops RBL (Some p) | None => bret tt end) ;;;
  match r with Some n => bret n | None => bret (-1) end.

End Bn.

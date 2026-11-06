(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnKara.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record bn_ops (M : Type -> Type) (ptr : Type) : Type := mkBnOps {
  ret : forall A : Type, A -> M A;
  bind : forall A B : Type, M A -> (A -> M B) -> M B;
  unreachable : forall A : Type, M A;
  lib_malloc : Z -> M (option ptr);          (* [comment removed for export] *)
  lib_free : ptr -> M unit                   (* [comment removed for export] *)
}.
Arguments mkBnOps {M ptr}.
Arguments ret {M ptr} _ {A}.
Arguments bind {M ptr} _ {A B}.
Arguments unreachable {M ptr} _ {A}.
Arguments lib_malloc {M ptr}.
Arguments lib_free {M ptr}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record bignum (ptr : Type) : Type := mkBN {
  bn_d : option ptr;
  bn_buf : list Z;
  bn_top : nat;
  bn_neg : bool;
  bn_flags : Z
}.
Arguments mkBN {ptr}.
Arguments bn_d {ptr}.
Arguments bn_buf {ptr}.
Arguments bn_top {ptr}.
Arguments bn_neg {ptr}.
Arguments bn_flags {ptr}.

Definition bn_dmax {ptr} (b : bignum ptr) : nat := length (bn_buf b).
Definition bn_nil {ptr} (flags : Z) : bignum ptr := mkBN None [] 0 false flags.   (* [comment removed for export] *)

Definition BN_FLG_MALLOCED : Z := 1.
Definition BN_FLG_STATIC_DATA : Z := 2.
Definition BN_FLG_CONSTTIME : Z := 4.
Definition BN_FLG_SECURE : Z := 8.
Definition BN_CTX_POOL_SIZE : nat := 16.
Definition BN_CTX_START_FRAMES : nat := 32.
Definition POOL_ITEM_BYTES : Z := 400.      (* [comment removed for export] *)
Definition BN_WORDS_MAX : Z := 8388607.     (* [comment removed for export] *)

(* [comment removed for export] *)
Record bn_ctx (ptr : Type) : Type := mkCtx {
  cx_head : option ptr;
  cx_current : option ptr;
  cx_vals : list (bignum ptr);
  cx_pused : nat;
  cx_psize : nat;
  cx_indexes : option ptr;
  cx_frames : list nat;
  cx_ssize : nat;
  cx_used : nat;
  cx_err_stack : nat;
  cx_too_many : bool
}.
Arguments mkCtx {ptr}.
Arguments cx_head {ptr}.
Arguments cx_current {ptr}.
Arguments cx_vals {ptr}.
Arguments cx_pused {ptr}.
Arguments cx_psize {ptr}.
Arguments cx_indexes {ptr}.
Arguments cx_frames {ptr}.
Arguments cx_ssize {ptr}.
Arguments cx_used {ptr}.
Arguments cx_err_stack {ptr}.
Arguments cx_too_many {ptr}.

Definition ctx_nil {ptr} : bn_ctx ptr := mkCtx None None [] 0 0 None [] 0 0 0 false.

(* [comment removed for export] *)
Record lstate (ptr : Type) : Type := mkLS {
  ls_b1 : bignum ptr; ls_b2 : bignum ptr; ls_b3 : bignum ptr; ls_b4 : bignum ptr; ls_b5 : bignum ptr;
  ls_ctx : bn_ctx ptr
}.
Arguments mkLS {ptr}.
Arguments ls_b1 {ptr}.
Arguments ls_b2 {ptr}.
Arguments ls_b3 {ptr}.
Arguments ls_b4 {ptr}.
Arguments ls_b5 {ptr}.
Arguments ls_ctx {ptr}.

(* [comment removed for export] *)
Definition ls_init {ptr} : lstate ptr :=
  mkLS (bn_nil BN_FLG_MALLOCED) (bn_nil BN_FLG_MALLOCED) (bn_nil BN_FLG_MALLOCED) (bn_nil BN_FLG_MALLOCED)
       (bn_nil BN_FLG_MALLOCED) ctx_nil.

(* [comment removed for export] *)
Inductive bnref : Type := RB1 | RB2 | RB3 | RB4 | RB5 | RPool (i : nat).

Definition bnref_eqb (x y : bnref) : bool :=
  match x, y with
  | RB1, RB1 | RB2, RB2 | RB3, RB3 | RB4, RB4 | RB5, RB5 => true
  | RPool i, RPool j => (i =? j)%nat
  | _, _ => false
  end.

Definition getbn {ptr} (r : bnref) (s : lstate ptr) : bignum ptr :=
  match r with
  | RB1 => ls_b1 s | RB2 => ls_b2 s | RB3 => ls_b3 s | RB4 => ls_b4 s | RB5 => ls_b5 s
  | RPool i => nth i (cx_vals (ls_ctx s)) (bn_nil 0)
  end.

Fixpoint list_set {A} (l : list A) (i : nat) (v : A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: l', O => v :: l'
  | x :: l', S i' => x :: list_set l' i' v
  end.

Definition ctx_set_vals {ptr} (c : bn_ctx ptr) (v : list (bignum ptr)) : bn_ctx ptr :=
  mkCtx (cx_head c) (cx_current c) v (cx_pused c) (cx_psize c) (cx_indexes c) (cx_frames c) (cx_ssize c)
        (cx_used c) (cx_err_stack c) (cx_too_many c).

Definition set_ctx {ptr} (c : bn_ctx ptr) (s : lstate ptr) : lstate ptr :=
  mkLS (ls_b1 s) (ls_b2 s) (ls_b3 s) (ls_b4 s) (ls_b5 s) c.

Definition setbn {ptr} (r : bnref) (b : bignum ptr) (s : lstate ptr) : lstate ptr :=
  match r with
  | RB1 => mkLS b (ls_b2 s) (ls_b3 s) (ls_b4 s) (ls_b5 s) (ls_ctx s)
  | RB2 => mkLS (ls_b1 s) b (ls_b3 s) (ls_b4 s) (ls_b5 s) (ls_ctx s)
  | RB3 => mkLS (ls_b1 s) (ls_b2 s) b (ls_b4 s) (ls_b5 s) (ls_ctx s)
  | RB4 => mkLS (ls_b1 s) (ls_b2 s) (ls_b3 s) b (ls_b5 s) (ls_ctx s)
  | RB5 => mkLS (ls_b1 s) (ls_b2 s) (ls_b3 s) (ls_b4 s) b (ls_ctx s)
  | RPool i => set_ctx (ctx_set_vals (ls_ctx s) (list_set (cx_vals (ls_ctx s)) i b)) s
  end.

(* [comment removed for export] *)
Definition bn_with_buf {ptr} (b : bignum ptr) (buf : list Z) : bignum ptr := mkBN (bn_d b) buf (bn_top b) (bn_neg b) (bn_flags b).
Definition bn_with_top {ptr} (b : bignum ptr) (top : nat) : bignum ptr := mkBN (bn_d b) (bn_buf b) top (bn_neg b) (bn_flags b).
Definition bn_with_neg {ptr} (b : bignum ptr) (neg : bool) : bignum ptr := mkBN (bn_d b) (bn_buf b) (bn_top b) neg (bn_flags b).

(* [comment removed for export] *)
Definition bn_correct_top_pure {ptr} (b : bignum ptr) : bignum ptr :=
  let top := strip_top (bn_buf b) (bn_top b) in
  mkBN (bn_d b) (bn_buf b) top (if (top =? 0)%nat then false else bn_neg b) (bn_flags b).

(* [comment removed for export] *)
Definition bn_zero_pure {ptr} (b : bignum ptr) : bignum ptr := mkBN (bn_d b) (bn_buf b) 0 false (bn_flags b).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint add_carry_words (a : list Z) (c : Z) : list Z * Z :=
  match a with
  | [] => ([], c)
  | t1 :: a' => let t2 := addw t1 c in
                let '(r, c') := add_carry_words a' (if t2 =? 0 then c else 0) in (t2 :: r, c')
  end.

(* [comment removed for export] *)
Definition ucmp_pure {ptr} (a b : bignum ptr) : Z :=
  let i := Z.of_nat (bn_top a) - Z.of_nat (bn_top b) in
  if i =? 0 then cmp_words (firstn (bn_top a) (bn_buf a)) (firstn (bn_top b) (bn_buf b)) else i.

(* [comment removed for export] *)
Definition cmp_pure {ptr} (a b : bignum ptr) : Z :=
  if negb (Bool.eqb (bn_neg a) (bn_neg b)) then (if bn_neg a then -1 else 1)
  else
    let gt := if bn_neg a then -1 else 1 in
    let lt := if bn_neg a then 1 else -1 in
    if (bn_top b <? bn_top a)%nat then gt
    else if (bn_top a <? bn_top b)%nat then lt
    else let c := cmp_words (firstn (bn_top a) (bn_buf a)) (firstn (bn_top b) (bn_buf b)) in
         if c =? 0 then 0 else if 0 <? c then gt else lt.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint qhat_corr (fuel : nat) (q rem t2l t2h n2 d0 d1 : Z) : Z :=
  match fuel with
  | O => q
  | S f =>
      if (t2h <? rem) || ((t2h =? rem) && (t2l <=? n2)) then q
      else
        let q := subw q 1 in
        let rem := addw rem d0 in
        if rem <? d0 then q
        else qhat_corr f q rem (subw t2l d1) (if t2l <? d1 then subw t2h 1 else t2h) n2 d0 d1
  end.

Definition QHAT_FUEL : nat := 4.

(* [comment removed for export] *)
Definition div_qhat (n0 n1 n2 d0 d1 : Z) : Z :=
  if n0 =? d0 then BW - 1
  else
    let q := div_words n0 n1 d0 in
    let rem := subw n1 (mulw q d0) in
    let t2 := d1 * q in
    qhat_corr QHAT_FUEL q rem (t2 mod BW) (t2 / BW) n2 d0 d1.

(* [comment removed for export] *)
Definition div_step (sdiv : list Z) (div_n loop num_n : nat) (d0 d1 : Z) (i : nat)
                    (st : list Z * list Z * list Z) : list Z * list Z * list Z :=
  let '(snum, tmp, res) := st in
  let top := (num_n - 1 - i)%nat in
  let n0 := nth top snum 0 in
  let n1 := nth (top - 1) snum 0 in
  let n2 := if (div_n =? 1)%nat then 0 else nth (top - 2) snum 0 in
  let q := div_qhat n0 n1 n2 d0 d1 in
  let '(ml, l0) := mul_words (firstn div_n sdiv) q in
  let tmp := splice tmp 0 (ml ++ [l0]) in
  let w := (loop - 1 - i)%nat in
  let '(sl, bw) := sub_words (slice snum w (div_n + 1)) (slice tmp 0 (div_n + 1)) in
  let snum := splice snum w sl in
  let q := subw q bw in
  let mask := negw bw in
  let tmp := splice tmp 0 (map (fun x => Z.land x mask) (firstn div_n sdiv)) in
  let '(al, cy) := add_words (slice snum w div_n) (slice tmp 0 div_n) in
  let snum := splice snum w al in
  let snum := upd snum top (addw (nth top snum 0) cy) in
  let res := upd res w q in
  (snum, tmp, res).

Fixpoint div_loop (sdiv : list Z) (div_n loop num_n : nat) (d0 d1 : Z) (cnt i : nat)
                  (st : list Z * list Z * list Z) : list Z * list Z * list Z :=
  match cnt with
  | O => st
  | S c => div_loop sdiv div_n loop num_n d0 d1 c (S i) (div_step sdiv div_n loop num_n d0 d1 i st)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Model.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : bn_ops M ptr.

Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).

Definition BM (A : Type) : Type := LS -> M (A * LS)%type.

Definition bret {A} (a : A) : BM A := fun s => ret ops (a, s).
Definition bbind {A B} (m : BM A) (f : A -> BM B) : BM B :=
  fun s => bind ops (m s) (fun p => f (fst p) (snd p)).
Definition bunr {A} : BM A := fun _ => unreachable ops.
Definition bget (r : bnref) : BM BN := fun s => ret ops (getbn r s, s).
Definition bset (r : bnref) (b : BN) : BM unit := fun s => ret ops (tt, setbn r b s).
Definition bgetctx : BM (bn_ctx ptr) := fun s => ret ops (ls_ctx s, s).
Definition bsetctx (c : bn_ctx ptr) : BM unit := fun s => ret ops (tt, set_ctx c s).
(* [comment removed for export] *)
Definition bmalloc (n : Z) : BM ptr :=
  fun s => bind ops (lib_malloc ops n) (fun r => match r with Some p => ret ops (p, s) | None => unreachable ops end).
Definition bfree (p : ptr) : BM unit := fun s => bind ops (lib_free ops p) (fun _ => ret ops (tt, s)).
(* [comment removed for export] *)
Definition bfree_opt (p : option ptr) : BM unit := match p with Some q => bfree q | None => bret tt end.

Local Notation "x <- m ;; k" := (bbind m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bbind m (fun _ => k)) (at level 61, right associativity).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bn_wexpand (r : bnref) (words : nat) : BM unit :=
  b <- bget r ;;
  if (words <=? bn_dmax b)%nat then bret tt
  else if BN_WORDS_MAX <? Z.of_nat words then bunr                              (* [comment removed for export] *)
  else if negb (Z.land (bn_flags b) BN_FLG_STATIC_DATA =? 0) then bunr        (* [comment removed for export] *)
  else if negb (Z.land (bn_flags b) BN_FLG_SECURE =? 0) then bunr             (* [comment removed for export] *)
  else
    p <- bmalloc (8 * Z.of_nat words) ;;                                      (* [comment removed for export] *)
    bfree_opt (bn_d b) ;;;                                                    (* [comment removed for export] *)
    bset r (mkBN (Some p) (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) (bn_top b) (bn_neg b) (bn_flags b)).

(* [comment removed for export] *)
Definition BN_copy (ra rb : bnref) : BM unit :=
  b <- bget rb ;;
  if negb (Z.land (bn_flags b) BN_FLG_CONSTTIME =? 0) then bunr
  else if bnref_eqb ra rb then bret tt
  else
    bn_wexpand ra (bn_top b) ;;;
    a <- bget ra ;;
    let buf := if (0 <? bn_top b)%nat then splice (bn_buf a) 0 (firstn (bn_top b) (bn_buf b)) else bn_buf a in
    bset ra (mkBN (bn_d a) buf (bn_top b) (bn_neg b) (bn_flags a)).

(* [comment removed for export] *)
Definition BN_bin2bn (s : list Z) (r : bnref) : BM unit :=
  b <- bget r ;;
  match s with
  | [] =>   (* [comment removed for export] *)
      bset r (mkBN (bn_d b) (repeat 0 (bn_dmax b)) 0 false (bn_flags b))
  | _ :: _ =>
      let s' := skip_zero_bytes s in
      match s' with
      | [] => bset r (bn_with_top b 0)                    (* [comment removed for export] *)
      | _ :: _ =>
          let n := ((length s' - 1) / 8 + 1)%nat in
          bn_wexpand r n ;;;
          b <- bget r ;;
          bset r (bn_correct_top_pure (mkBN (bn_d b) (splice (bn_buf b) 0 (bin2bn_limbs s')) n false (bn_flags b)))
      end
  end.

(* [comment removed for export] *)
Definition BN_set_negative (r : bnref) (sgn : bool) : BM unit :=
  b <- bget r ;; bset r (bn_with_neg b (sgn && negb (bn_top b =? 0)%nat)).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition BN_CTX_start : BM unit :=
  c <- bgetctx ;;
  if negb (cx_err_stack c =? 0)%nat || cx_too_many c then bunr
  else
    let depth := length (cx_frames c) in
    if (depth =? cx_ssize c)%nat then
      (* [comment removed for export] *)
      if negb (cx_ssize c =? 0)%nat then bunr              (* [comment removed for export] *)
      else
        p <- bmalloc (4 * Z.of_nat BN_CTX_START_FRAMES) ;;
        bfree_opt (cx_indexes c) ;;;
        bsetctx (mkCtx (cx_head c) (cx_current c) (cx_vals c) (cx_pused c) (cx_psize c) (Some p)
                       (cx_frames c ++ [cx_used c]) BN_CTX_START_FRAMES (cx_used c) 0 false)
    else
      bsetctx (mkCtx (cx_head c) (cx_current c) (cx_vals c) (cx_pused c) (cx_psize c) (cx_indexes c)
                     (cx_frames c ++ [cx_used c]) (cx_ssize c) (cx_used c) 0 false).

(* [comment removed for export] *)
Definition BN_CTX_get : BM bnref :=
  c <- bgetctx ;;
  if negb (cx_err_stack c =? 0)%nat || cx_too_many c then bunr
  else
    (* [comment removed for export] *)
    i <- (if (cx_pused c =? cx_psize c)%nat then
            if negb (cx_psize c =? 0)%nat then bunr          (* [comment removed for export] *)
            else
              p <- bmalloc POOL_ITEM_BYTES ;;
              bsetctx (mkCtx (Some p) (Some p) (repeat (bn_nil 0) BN_CTX_POOL_SIZE) 1 BN_CTX_POOL_SIZE
                             (cx_indexes c) (cx_frames c) (cx_ssize c) (cx_used c) 0 false) ;;;
              bret 0%nat
          else
            let cur := if (cx_pused c =? 0)%nat then cx_head c else cx_current c in
            bsetctx (mkCtx (cx_head c) cur (cx_vals c) (S (cx_pused c)) (cx_psize c)
                           (cx_indexes c) (cx_frames c) (cx_ssize c) (cx_used c) 0 false) ;;;
            bret (cx_pused c)) ;;
    b <- bget (RPool i) ;;
    bset (RPool i) (bn_zero_pure b) ;;;                     (* [comment removed for export] *)
    c <- bgetctx ;;
    bsetctx (mkCtx (cx_head c) (cx_current c) (cx_vals c) (cx_pused c) (cx_psize c)
                   (cx_indexes c) (cx_frames c) (cx_ssize c) (S (cx_used c)) 0 false) ;;;
    bret (RPool i).

(* [comment removed for export] *)
Definition BN_CTX_end : BM unit :=
  c <- bgetctx ;;
  if negb (cx_err_stack c =? 0)%nat then bunr
  else
    match rev (cx_frames c) with
    | [] => bunr
    | fp :: rest =>
        let released := (fp <? cx_used c)%nat in
        let pused := if released then (cx_pused c - (cx_used c - fp))%nat else cx_pused c in
        let cur := if released && (pused =? 0)%nat then None else cx_current c in
        bsetctx (mkCtx (cx_head c) cur (cx_vals c) pused (cx_psize c)
                       (cx_indexes c) (rev rest) (cx_ssize c) fp 0 false)
    end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bn_left_align (r : bnref) : BM Z :=
  b <- bget r ;;
  let top := bn_top b in
  let lshift := 64 - num_bits_word (nth (top - 1) (bn_buf b) 0) in
  bset r (bn_with_buf b (splice (bn_buf b) 0 (fst (lshift_limbs (firstn top (bn_buf b)) lshift 0)))) ;;;
  bret lshift.

(* [comment removed for export] *)
Definition bn_lshift_fixed_top (rr ra : bnref) (n : Z) : BM unit :=
  if bnref_eqb rr ra || negb (n <? 64) then bunr
  else
    a <- bget ra ;;
    bn_wexpand rr (bn_top a + 1) ;;;
    r <- bget rr ;;
    let buf := if (bn_top a =? 0)%nat then upd (bn_buf r) 0 0
               else let '(ls, mo) := lshift_limbs (firstn (bn_top a) (bn_buf a)) n 0 in
                    splice (bn_buf r) 0 (ls ++ [mo]) in
    bset rr (mkBN (bn_d r) buf (bn_top a + 1) (bn_neg a) (bn_flags r)).

(* [comment removed for export] *)
Definition bn_rshift_fixed_top (rr ra : bnref) (n : Z) : BM unit :=
  if bnref_eqb rr ra || negb (n <? 64) then bunr
  else
    a <- bget ra ;;
    if (bn_top a =? 0)%nat then (r <- bget rr ;; bset rr (bn_zero_pure r))      (* [comment removed for export] *)
    else
      bn_wexpand rr (bn_top a) ;;;
      r <- bget rr ;;
      bset rr (mkBN (bn_d r) (splice (bn_buf r) 0 (rshift_limbs (firstn (bn_top a) (bn_buf a)) n))
                    (bn_top a) (bn_neg a) (bn_flags r)).

(* [comment removed for export] *)
Definition bn_div_fixed_top (dv rm num divisor : bnref) : BM unit :=
  BN_CTX_start ;;;
  tmp <- BN_CTX_get ;;
  snum <- BN_CTX_get ;;
  sdiv <- BN_CTX_get ;;
  BN_copy sdiv divisor ;;;
  norm_shift <- bn_left_align sdiv ;;
  (b <- bget sdiv ;; bset sdiv (bn_with_neg b false)) ;;;
  bn_lshift_fixed_top snum num norm_shift ;;;
  sd <- bget sdiv ;;
  sn <- bget snum ;;
  let div_n := bn_top sd in
  (if (bn_top sn <=? div_n)%nat then
     bn_wexpand snum (div_n + 1) ;;;
     sn' <- bget snum ;;
     (* [comment removed for export] *)
     bset snum (mkBN (bn_d sn') (splice (bn_buf sn') (bn_top sn) (repeat 0 (div_n - bn_top sn + 1)))
                     (div_n + 1) (bn_neg sn') (bn_flags sn'))
   else bret tt) ;;;
  sn <- bget snum ;;
  let num_n := bn_top sn in
  let loop := (num_n - div_n)%nat in
  let d0 := nth (div_n - 1) (bn_buf sd) 0 in
  let d1 := if (div_n =? 1)%nat then 0 else nth (div_n - 2) (bn_buf sd) 0 in
  bn_wexpand dv loop ;;;
  nm <- bget num ;;
  dvs <- bget divisor ;;
  let num_neg := bn_neg nm in
  (r <- bget dv ;; bset dv (mkBN (bn_d r) (bn_buf r) loop (xorb num_neg (bn_neg dvs)) (bn_flags r))) ;;;
  bn_wexpand tmp (div_n + 1) ;;;
  sn <- bget snum ;;
  tm <- bget tmp ;;
  r <- bget dv ;;
  let '(snb, tmb, rb) := div_loop (bn_buf sd) div_n loop num_n d0 d1 loop 0 (bn_buf sn, bn_buf tm, bn_buf r) in
  bset tmp (bn_with_buf tm tmb) ;;;
  bset dv (bn_with_buf r rb) ;;;
  bset snum (mkBN (bn_d sn) snb div_n num_neg (bn_flags sn)) ;;;
  bn_rshift_fixed_top rm snum norm_shift ;;;
  BN_CTX_end.

(* [comment removed for export] *)
Definition BN_div (dv rm num divisor : bnref) : BM unit :=
  d <- bget divisor ;;
  if (bn_top d =? 0)%nat then bunr                                           (* [comment removed for export] *)
  else if nth (bn_top d - 1) (bn_buf d) 0 =? 0 then bunr                     (* [comment removed for export] *)
  else
    bn_div_fixed_top dv rm num divisor ;;;
    (b <- bget dv ;; bset dv (bn_correct_top_pure b)) ;;;
    (b <- bget rm ;; bset rm (bn_correct_top_pure b)).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bn_mul_fixed_top (rr ra rb : bnref) : BM unit :=
  a <- bget ra ;;
  b <- bget rb ;;
  let al := bn_top a in
  let bl := bn_top b in
  if ((al =? 0) || (bl =? 0))%nat then (r <- bget rr ;; bset rr (bn_zero_pure r))
  else
    let top := (al + bl)%nat in
    BN_CTX_start ;;;
    (if bnref_eqb rr ra || bnref_eqb rr rb then bunr
     else if ((al =? bl) && (al =? 8))%nat then
       bn_wexpand rr 16 ;;;
       r <- bget rr ;;
       bset rr (mkBN (bn_d r) (splice (bn_buf r) 0 (mul_comba8 (firstn 8 (bn_buf a)) (firstn 8 (bn_buf b)))) 16
                     (bn_neg r) (bn_flags r))
     else if ((16 <=? al) && (16 <=? bl) && (al <=? bl + 1) && (bl <=? al + 1))%nat then
       (* [comment removed for export] *)
       let kj := Z.to_nat (num_bits_word (Z.of_nat (Nat.max al bl)) - 1) in
       let j := Nat.pow 2 kj in
       t <- BN_CTX_get ;;
       if ((j <? al) || (j <? bl))%nat then
         bn_wexpand t (8 * j) ;;;
         bn_wexpand rr (8 * j) ;;;
         tb <- bget t ;;
         r <- bget rr ;;
         let '(ro, to) := mul_part_recursive kj kj (firstn al (bn_buf a)) (firstn bl (bn_buf b)) (al - j) (bl - j)
                                             (firstn (4 * j) (bn_buf r)) (bn_buf tb) in
         bset t (bn_with_buf tb to) ;;;
         bset rr (mkBN (bn_d r) (splice (bn_buf r) 0 ro) top (bn_neg r) (bn_flags r))
       else
         bn_wexpand t (4 * j) ;;;
         bn_wexpand rr (4 * j) ;;;
         tb <- bget t ;;
         r <- bget rr ;;
         let '(ro, to) := mul_recursive kj (firstn al (bn_buf a)) (firstn bl (bn_buf b)) (j - al) (j - bl)
                                        (firstn (2 * j) (bn_buf r)) (bn_buf tb) in
         bset t (bn_with_buf tb to) ;;;
         bset rr (mkBN (bn_d r) (splice (bn_buf r) 0 ro) top (bn_neg r) (bn_flags r))
     else
       bn_wexpand rr top ;;;
       r <- bget rr ;;
       bset rr (mkBN (bn_d r) (splice (bn_buf r) 0 (mul_normal (firstn al (bn_buf a)) (firstn bl (bn_buf b)))) top
                     (bn_neg r) (bn_flags r))) ;;;
    (* [comment removed for export] *)
    (r <- bget rr ;; bset rr (bn_with_neg r (xorb (bn_neg a) (bn_neg b)))) ;;;
    BN_CTX_end.

(* [comment removed for export] *)
Definition BN_mul (rr ra rb : bnref) : BM unit :=
  bn_mul_fixed_top rr ra rb ;;;
  (b <- bget rr ;; bset rr (bn_correct_top_pure b)).

(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition BN_usub (rr ra rb : bnref) : BM unit :=
  a <- bget ra ;;
  b <- bget rb ;;
  let max := bn_top a in
  let min := bn_top b in
  if (max <? min)%nat then bunr                                              (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    (r <- bget rr ;; bset rr (mkBN (bn_d r) (bn_buf r) (strip_top (bn_buf r) max) false (bn_flags r))).

(* [comment removed for export] *)
Definition BN_ucmp (ra rb : bnref) : BM Z :=
  a <- bget ra ;;
  b <- bget rb ;;
  if negb (Z.land (bn_flags a) BN_FLG_CONSTTIME =? 0) || negb (Z.land (bn_flags b) BN_FLG_CONSTTIME =? 0) then bunr
  else bret (ucmp_pure a b).

(* [comment removed for export] *)
Definition BN_add (rr ra rb : bnref) : BM unit :=
  a <- bget ra ;;
  b <- bget rb ;;
  r_neg <- (if Bool.eqb (bn_neg a) (bn_neg b) then
              BN_uadd rr ra rb ;;; bret (bn_neg a)
            else
              c <- BN_ucmp ra rb ;;
              if 0 <? c then BN_usub rr ra rb ;;; bret (bn_neg a)
              else if c <? 0 then BN_usub rr rb ra ;;; bret (bn_neg b)
              else (r <- bget rr ;; bset rr (bn_zero_pure r)) ;;; bret false) ;;
  r <- bget rr ;; bset rr (bn_with_neg r r_neg).

(* [comment removed for export] *)

Definition MAX_LEN : nat := Z.to_nat 256000.

(* [comment removed for export] *)
Definition fuzz_one (data : list Z) : BM Z :=
  let data := firstn MAX_LEN data in
  let '(s1, s2, n1, n2) :=
    match data with
    | [] => (false, false, [], [])
    | b0 :: rest =>
        let len := length rest in
        let l1 := Z.to_nat ((Z.land b0 63 * Z.of_nat len) / 63) in
        (negb (Z.land b0 64 =? 0), negb (Z.land b0 128 =? 0), firstn l1 rest, skipn l1 rest)
    end in
  BN_bin2bn n1 RB1 ;;;
  BN_set_negative RB1 s1 ;;;
  BN_bin2bn n2 RB2 ;;;
  BN_set_negative RB2 s2 ;;;
  b2 <- bget RB2 ;;
  (if (bn_top b2 =? 0)%nat then bret tt                      (* [comment removed for export] *)
   else
     BN_div RB3 RB4 RB1 RB2 ;;;
     b1 <- bget RB1 ;; b2 <- bget RB2 ;; b3 <- bget RB3 ;; b4 <- bget RB4 ;;
     let z b := (bn_top (b : BN) =? 0)%nat in
     let success :=
       if z b1 then z b3 && z b4
       else if bn_neg b1 then (negb (Bool.eqb (bn_neg b3) (bn_neg b2)) || z b3) && (bn_neg b4 || z b4)
       else (Bool.eqb (bn_neg b3) (bn_neg b2) || z b3) && (negb (bn_neg b4) || z b4) in
     BN_mul RB5 RB3 RB2 ;;;
     BN_add RB5 RB5 RB4 ;;;
     b5 <- bget RB5 ;; b1 <- bget RB1 ;;
     if success && (cmp_pure b5 b1 =? 0) then bret tt
     else bunr)                                              (* [comment removed for export] *)
  ;;;
  (* [comment removed for export] *)
  bret 0.

End Model.

(* [comment removed for export] *)
Definition bn_init {M ptr} (ops : bn_ops M ptr) : M (list ptr * lstate ptr)%type :=
  let new n k := bind ops (lib_malloc ops n) (fun r => match r with Some p => k p | None => unreachable ops end) in
  new 24 (fun p1 => new 24 (fun p2 => new 24 (fun p3 => new 24 (fun p4 => new 24 (fun p5 => new 72 (fun pc =>
  ret ops ([p1; p2; p3; p4; p5; pc], ls_init))))))).

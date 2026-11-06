(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Module W.
  Definition M : Z := 2^64.
  Definition half : Z := 2^32.
  Definition max_word : Z := M - 1.                 (* [comment removed for export] *)
  Definition r_mask : Z := half - 1.                (* [comment removed for export] *)
  Definition l_mask : Z := max_word - r_mask.       (* [comment removed for export] *)
  Definition l_bit : Z := max_word - (max_word / 2).  (* [comment removed for export] *)

  Definition wrap (z : Z) : Z := z mod M.
  Definition add (a b : Z) : Z := wrap (a + b).
  Definition sub (a b : Z) : Z := wrap (a - b).
  Definition mul (a b : Z) : Z := wrap (a * b).
  Definition shl (a : Z) (k : Z) : Z := wrap (a * 2^k).      (* [comment removed for export] *)
  Definition shr (a : Z) (k : Z) : Z := a / 2^k.             (* [comment removed for export] *)
  Definition land (a b : Z) : Z := Z.land a b.
  Definition lor (a b : Z) : Z := Z.lor a b.
  Definition ltu (a b : Z) : bool := a <? b.
  Definition b2z (b : bool) : Z := if b then 1 else 0.
  (* [comment removed for export] *)
  Definition divu (a b : Z) : Z := if b =? 0 then max_word else a / b.
  Definition remu (a b : Z) : Z := if b =? 0 then a else a mod b.
End W.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition words := list Z.
Definition nth_w (ws : words) (i : nat) : Z := nth i ws 0.
Fixpoint upd (ws : words) (i : nat) (v : Z) : words :=
  match ws, i with
  | [], _ => []                       (* [comment removed for export] *)
  | _ :: t, O => v :: t
  | w :: t, S i' => w :: upd t i' v
  end.
Definition zeros (n : nat) : words := repeat 0 n.
(* [comment removed for export] *)
Definition slice (ws : words) (lo n : nat) : words := firstn n (skipn lo ws).
Definition splice (ws : words) (lo : nat) (seg : words) : words :=
  firstn lo ws ++ seg ++ skipn (lo + length seg) ws.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record sto := Sto {
  s_alloc : bool;      (* [comment removed for export] *)
  s_neg   : bool;      (* [comment removed for export] *)
  s_words : words;     (* [comment removed for export] *)
  s_cap   : nat;       (* [comment removed for export] *)
  s_blk   : nat        (* [comment removed for export] *)
}.

Definition inlined_capacity : nat := 2%nat.
Definition size (s : sto) : nat := length (s_words s).
Definition capacity (s : sto) : nat := if s_alloc s then s_cap s else inlined_capacity.
Definition set_words (s : sto) (ws : words) : sto := Sto (s_alloc s) (s_neg s) ws (s_cap s) (s_blk s).
Definition set_neg (s : sto) (b : bool) : sto := Sto (s_alloc s) b (s_words s) (s_cap s) (s_blk s).

(* [comment removed for export] *)
Definition sto_empty : sto := Sto false false [] inlined_capacity 0.
(* [comment removed for export] *)
Definition sto_of_word (w : Z) : sto := Sto false false (if w =? 0 then [] else [w]) inlined_capacity 0.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive site := SiteString   (* [comment removed for export] *)
                | SiteReserve  (* [comment removed for export] *)
                | SiteCopy.    (* [comment removed for export] *)
Inductive exn := SystemError22  (* [comment removed for export] *)
               | ZeroDivide     (* [comment removed for export] *)
               | AssertNMaxSize. (* [comment removed for export] *)
Inductive event :=
  | EAlloc (blk : nat) (bytes : Z) (where_ : site)   (* [comment removed for export] *)
  | EFree  (blk : nat) (bytes : Z)                   (* [comment removed for export] *)
  | EThrow (e : exn)      (* [comment removed for export] *)
  | ECatch.               (* [comment removed for export] *)

Record st := St { st_evs : list event (* [comment removed for export] *); st_next : nat }.
Definition st_init : st := St [] 0.

Definition M (A : Type) : Type := st -> A * st.
Definition ret {A} (a : A) : M A := fun s => (a, s).
Definition bind {A B} (m : M A) (k : A -> M B) : M B :=
  fun s => let (a, s1) := m s in k a s1.
Notation "'do' x <- m ; k" := (bind m (fun x => k))
  (at level 100, x pattern, m at next level, right associativity).
Notation "m ;; k" := (bind m (fun _ => k))
  (at level 100, k at level 200, right associativity).

Definition emit (e : event) : M unit := fun s => (tt, St (e :: st_evs s) (st_next s)).
Definition fresh : M nat := fun s => (st_next s, St (st_evs s) (S (st_next s))).
Definition alloc (bytes : Z) (w : site) : M nat :=
  do b <- fresh ; emit (EAlloc b bytes w) ;; ret b.
Definition events_of {A} (m : M A) : list event := rev (st_evs (snd (m st_init))).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition round_up (i : nat) : nat := (i + (8 - i mod 8))%nat.

(* [comment removed for export] *)
Definition reserve (s : sto) (n : nat) : M sto :=
  if (capacity s <? n)%nat then
    let cap_new := round_up n in
    do blk <- alloc (8 * Z.of_nat cap_new) SiteReserve ;
    (if s_alloc s then emit (EFree (s_blk s) (8 * Z.of_nat (s_cap s))) else ret tt) ;;
    ret (Sto true (s_neg s) (s_words s) cap_new blk)
  else ret s.

(* [comment removed for export] *)
Definition resize (s : sto) (n : nat) : M sto :=
  do s1 <- reserve s n ;
  ret (set_words s1 (if (n <=? size s1)%nat then firstn n (s_words s1)
                     else s_words s1 ++ zeros (n - size s1))).

(* [comment removed for export] *)
Fixpoint reduce_loop (fuel : nat) (ws : words) : words :=
  match fuel with
  | O => ws
  | S f => match ws with
           | [] => []
           | _ => if last ws 0 =? 0 then reduce_loop f (removelast ws) else ws
           end
  end.
Definition reduce (s : sto) : sto :=
  let ws := reduce_loop (size s) (s_words s) in
  Sto (s_alloc s) (if (length ws =? 0)%nat then false else s_neg s) ws (s_cap s) (s_blk s).

(* [comment removed for export] *)
Definition destroy (s : sto) : M unit :=
  if s_alloc s then emit (EFree (s_blk s) (8 * Z.of_nat (s_cap s))) else ret tt.

(* [comment removed for export] *)
Definition copy (src : sto) : M sto :=
  if s_alloc src then
    do blk <- alloc (8 * Z.of_nat (s_cap src)) SiteCopy ;
    ret (Sto true (s_neg src) (s_words src) (s_cap src) blk)
  else ret (Sto false (s_neg src) (s_words src) inlined_capacity 0).

(* [comment removed for export] *)
Definition assign (dst src : sto) : M sto :=
  do s1 <- resize dst (size src) ;
  ret (if (0 <? size src)%nat
       then Sto (s_alloc s1) (s_neg src) (s_words src) (s_cap s1) (s_blk s1)
       else s1).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint compare_loop (fuel : nat) (xs ys : words) : Z :=
  match fuel with
  | O => 0
  | S i => let a := nth_w xs i in let b := nth_w ys i in
           if b <? a then 1 else if a <? b then (-1) else compare_loop i xs ys
  end.
Definition compare (x y : sto) : Z :=
  if ((size x =? 0) && (size y =? 0))%nat then 0
  else if negb (Bool.eqb (s_neg x) (s_neg y)) then W.b2z (s_neg y) - W.b2z (s_neg x)
  else
    let code := if (size x <? size y)%nat then -1
                else if (size y <? size x)%nat then 1
                else compare_loop (size x) (s_words x) (s_words y) in
    if s_neg x then - code else code.

(* [comment removed for export] *)
Definition DDproduct (A B : Z) : Z * Z (* [comment removed for export] *) :=
  let hiA := W.shr A 32 in let loA := W.land A W.r_mask in
  let hiB := W.shr B 32 in let loB := W.land B W.r_mask in
  let lo := W.mul loA loB in
  let hi := W.mul hiA hiB in
  let mid1 := W.mul loA hiB in
  let mid2 := W.mul hiA loB in
  let old := lo in
  let lo := W.add lo (W.shl mid1 32) in
  let hi := W.add hi (W.add (W.b2z (W.ltu lo old)) (W.shr mid1 32)) in
  let old := lo in
  let lo := W.add lo (W.shl mid2 32) in
  let hi := W.add hi (W.add (W.b2z (W.ltu lo old)) (W.shr mid2 32)) in
  (hi, lo).

(* [comment removed for export] *)
Fixpoint mul_loop (fuel : nat) (i : nat) (dig carry y : Z) (ws : words) : words * Z :=
  match fuel with
  | O => (ws, carry)
  | S f =>
      let (hi, lo) := DDproduct dig y in
      let wi := W.add lo carry in
      let ws1 := upd ws i wi in
      let dig' := nth_w ws1 (S i) in
      let carry' := W.add hi (W.b2z (W.ltu wi lo)) in
      mul_loop f (S i) dig' carry' y ws1
  end.
Definition mul_word (s : sto) (y : Z) : M sto :=
  let len0 := size s in
  let dig := nth_w (s_words s) 0 in      (* [comment removed for export] *)
  do s1 <- resize s (S len0) ;
  let (ws, carry) := mul_loop len0 0 dig 0 y (s_words s1) in
  ret (reduce (set_words s1 (upd ws len0 carry))).

(* [comment removed for export] *)
Fixpoint add_carry_loop (fuel : nat) (i this_size : nat) (carry : Z) (ws : words) : words :=
  match fuel with
  | O => ws
  | S f => if ((i <? this_size)%nat && negb (carry =? 0)) then
             let d := W.add (nth_w ws i) carry in
             let carry' := W.b2z (W.ltu d carry) in
             add_carry_loop f (S i) this_size carry' (upd ws i d)
           else ws
  end.
Definition add_word (s : sto) (y : Z) : M sto :=
  do s1 <- resize s (S (size s)) ;
  let ws := s_words s1 in
  let this_size := size s1 in
  let carry := 0 in
  let d := W.add (nth_w ws 0) carry in
  let carry := W.b2z (W.ltu d carry) in
  let w0 := W.add d y in
  let carry := if W.ltu w0 d then 1 else carry in
  let ws1 := upd ws 0 w0 in
  let ws2 := add_carry_loop (this_size - 1) 1 this_size carry ws1 in
  ret (reduce (set_words s1 ws2)).

(* [comment removed for export] *)
Fixpoint shlw_loop (fuel : nat) (q : nat) (ws : words) : words :=   (* [comment removed for export] *)
  match fuel with
  | O => ws
  | S i => shlw_loop i q (upd ws i (if (i <? q)%nat then 0 else nth_w ws (i - q)))
  end.
Fixpoint shl_loop (fuel : nat) (k k1 mask : Z) (ws : words) : words :=   (* [comment removed for export] *)
  match fuel with
  | O => ws
  | S i => let wi := W.shl (nth_w ws i) k in
           let wi := if (0 <? i)%nat then W.lor wi (W.land (W.shr (nth_w ws (i - 1)) k1) mask) else wi in
           shl_loop i k k1 mask (upd ws i wi)
  end.
Definition shl_bits (s : sto) (k : Z) : M sto :=
  let sz0 := size s in
  let q := Z.to_nat (k / 64) in
  do sq <- (if negb (q =? 0)%nat then
              do s1 <- resize s (sz0 + q) ;
              ret (set_words s1 (shlw_loop (size s1) q (s_words s1)), k mod 64, size s1)
            else ret (s, k, sz0)) ;
  let '(s1, k, sz1) := sq in
  do s2 <- (if negb (k =? 0) then
              let k1 := 64 - k in
              let mask := W.sub (W.shl 1 k) 1 in
              do s2 <- resize s1 (S sz1) ;
              ret (set_words s2 (shl_loop (size s2) k k1 mask (s_words s2)))
            else ret s1) ;
  ret (reduce s2).

(* [comment removed for export] *)
Fixpoint shr_loop (fuel : nat) (i n : nat) (k k1 mask : Z) (ws : words) : words :=
  match fuel with
  | O => ws
  | S f => let wi := W.shr (nth_w ws i) k in
           let wi := if (i <? n)%nat then W.lor wi (W.shl (W.land (nth_w ws (S i)) mask) k1) else wi in
           shr_loop f (S i) n k k1 mask (upd ws i wi)
  end.
Definition shr_bits (s : sto) (k : Z) : M sto :=
  let q := Z.to_nat (k / 64) in
  if (size s <=? q)%nat then resize s 0
  else
    do sk <- (if (0 <? q)%nat then
                do s1 <- resize (set_words s (skipn q (s_words s) ++ skipn (size s - q) (s_words s))) (size s - q) ;
                ret (s1, k mod 64)
              else ret (s, k)) ;
    let '(s1, k) := sk in
    if ((0 <? q)%nat && (k =? 0)) then ret (reduce s1)
    else
      let n := (size s1 - 1)%nat in
      let k1 := 64 - k in
      let mask := W.sub (W.shl 1 k) 1 in
      ret (reduce (set_words s1 (shr_loop (S n) 0 n k k1 mask (s_words s1)))).

(* [comment removed for export] *)
Definition DDQ_FUEL1 : nat := 16%nat.
Definition DDQ_FUEL2 : nat := 8%nat.
Definition ddq1_cond (A B dHi dLo1 : Z) : bool := (dHi <? A) || ((A =? dHi) && (dLo1 <=? B)).
Definition ddq1_body (A B qHi dHi dLo1 : Z) : Z * Z * Z :=
  let x := W.sub B dLo1 in
  let A := W.sub A (W.add dHi (W.b2z (W.ltu B x))) in
  (A, x, W.add qHi 1).
Fixpoint ddq1_loop (fuel : nat) (A B qHi dHi dLo1 : Z) : Z * Z * Z :=
  match fuel with
  | O => (A, B, qHi)
  | S f => if ddq1_cond A B dHi dLo1
           then let '(A, B, qHi) := ddq1_body A B qHi dHi dLo1 in ddq1_loop f A B qHi dHi dLo1
           else (A, B, qHi)
  end.
Definition ddq2_cond (A B d : Z) : bool := negb (A =? 0) || (d <=? B).
Definition ddq2_body (A B qLo d : Z) : Z * Z * Z :=
  let x := W.sub B d in
  let A := W.sub A (W.b2z (W.ltu B x)) in
  (A, x, W.add qLo 1).
Fixpoint ddq2_loop (fuel : nat) (A B qLo d : Z) : Z * Z * Z :=
  match fuel with
  | O => (A, B, qLo)
  | S f => if ddq2_cond A B d
           then let '(A, B, qLo) := ddq2_body A B qLo d in ddq2_loop f A B qLo d
           else (A, B, qLo)
  end.
(* [comment removed for export] *)
Definition ddq_step1 (A B d : Z) : Z * Z * Z (* [comment removed for export] *) :=
  let dHi := W.shr d 32 in let dLo := W.land d W.r_mask in
  let qHi := W.divu A (W.add dHi 1) in
  let middle := W.mul qHi dLo in
  let left := W.mul qHi dHi in
  let x := W.sub B (W.shl middle 32) in
  let A := W.sub A (W.add (W.add (W.shr middle 32) left) (W.b2z (W.ltu B x))) in
  (A, x, qHi).
Definition ddq_step2 (A B d : Z) : Z * Z * Z (* [comment removed for export] *) :=
  let dHi := W.shr d 32 in let dLo := W.land d W.r_mask in
  let qLo := W.divu (W.lor (W.shl A 32) (W.shr B 32)) (W.add dHi 1) in
  let right := W.mul qLo dLo in
  let middle := W.mul qLo dHi in
  let x := W.sub B right in
  let A := W.sub A (W.b2z (W.ltu B x)) in
  let B := x in
  let x := W.sub B (W.shl middle 32) in
  let A := W.sub A (W.add (W.shr middle 32) (W.b2z (W.ltu B x))) in
  (A, x, qLo).
Definition DDquotient_f (f1 f2 : nat) (A B d : Z) : Z :=
  let dHi := W.shr d 32 in let dLo := W.land d W.r_mask in
  let dLo1 := W.shl dLo 32 in
  let '(A, B, qHi) := ddq_step1 A B d in
  let '(A, B, qHi) := ddq1_loop f1 A B qHi dHi dLo1 in
  let '(A, B, qLo) := ddq_step2 A B d in
  let '(A, B, qLo) := ddq2_loop f2 A B qLo d in
  W.add (W.shl qHi 32) qLo.
Definition DDquotient (A B d : Z) : Z := DDquotient_f DDQ_FUEL1 DDQ_FUEL2 A B d.

(* [comment removed for export] *)
Fixpoint subm_loop (fuel : nat) (i : nat) (carry q : Z) (a b : words) : words * Z :=
  match fuel with
  | O => (a, carry)
  | S f =>
      let (hi, lo) := DDproduct (nth_w b i) q in
      let d := nth_w a i in
      let ai := W.sub d lo in
      let carry := if W.ltu d ai then W.add carry 1 else carry in
      let a1 := upd a i ai in
      let d := nth_w a1 (S i) in
      let ai1 := W.sub d (W.add hi carry) in
      let carry := W.b2z (W.ltu d ai1) in
      subm_loop f (S i) carry q (upd a1 (S i) ai1) b
  end.
Fixpoint addback_loop (fuel : nat) (i : nat) (carry : Z) (a b : words) : words :=
  match fuel with
  | O => a
  | S f =>
      let d := W.add (nth_w a i) carry in
      let carry := W.b2z (W.ltu d carry) in
      let ai := W.add d (nth_w b i) in
      let carry := if W.ltu ai d then 1 else carry in
      addback_loop f (S i) carry (upd a i ai) b
  end.
Definition subtractmul (a b : words) (n : nat) (q : Z) : words * Z :=
  let (a1, carry) := subm_loop n 0 0 q a b in
  if negb (carry =? 0) then
    let q := W.sub q 1 in
    let a2 := addback_loop n 0 0 a1 b in
    (upd a2 n 0, q)
  else (a1, q).

(* [comment removed for export] *)
Fixpoint norm_count (fuel : nat) (y : Z) (x : Z) : Z :=
  match fuel with
  | O => x
  | S f => if W.land y W.l_bit =? 0 then norm_count f (W.shl y 1) (x + 1) else x
  end.
Definition NORM_FUEL : nat := 64%nat.
Definition normalize (denom num : sto) : M (sto * sto * Z * bool) :=
  if (size denom =? 0)%nat then ret (denom, num, 0, false)
  else
    let r := (size denom - 1)%nat in
    let y := nth_w (s_words denom) r in
    let x := norm_count NORM_FUEL y 0 in
    do denom1 <- shl_bits denom x ;
    do num1 <- shl_bits num x ;
    if ((0 <? r)%nat && W.ltu (nth_w (s_words denom1) r) (nth_w (s_words denom1) (r - 1)))
    then do denom2 <- mul_word denom1 W.max_word ;
         do num2 <- mul_word num1 W.max_word ;
         ret (denom2, num2, x, true)
    else ret (denom1, num1, x, false).

(* [comment removed for export] *)
Fixpoint halfdiv_loop (fuel : nat) (divisor dHi : Z) (this_ws quot_ws : words) : words * Z :=
  match fuel with
  | O => (quot_ws, dHi)
  | S i =>
      let vi := nth_w this_ws i in
      let dividend := W.lor (W.shl dHi 32) (W.shr vi 32) in
      let q1 := W.divu dividend divisor in
      let r := W.remu dividend divisor in
      let dividend := W.lor (W.shl r 32) (W.land vi W.r_mask) in
      let q2 := W.divu dividend divisor in
      let dHi := W.remu dividend divisor in
      halfdiv_loop i divisor dHi this_ws (upd quot_ws i (W.lor (W.shl q1 32) q2))
  end.

(* [comment removed for export] *)
Definition divstep (k l : nat) (d : Z) (denom_ws : words) (rem_ws quot_ws : words) : words * words :=
  let q := DDquotient (nth_w rem_ws k) (nth_w rem_ws (k - 1)) d in
  let lo := (k - l - 1)%nat in
  let (win, q') := subtractmul (slice rem_ws lo (l + 2)) denom_ws (l + 1) q in
  (splice rem_ws lo win, upd quot_ws lo q').
Fixpoint divloop (fuel : nat) (k l : nat) (d : Z) (denom_ws : words) (rem_ws quot_ws : words) : words * words :=
  match fuel with
  | O => (rem_ws, quot_ws)
  | S f => let (r1, q1) := divstep k l d denom_ws rem_ws quot_ws in
           divloop f (k - 1) l d denom_ws r1 q1
  end.

Inductive div_outcome :=
  | DivOk (quot rem : sto)
  | DivZero                          (* [comment removed for export] *)
  | DivAssert (quot_cur rem_cur : sto).  (* [comment removed for export] *)
Inductive un_outcome := UnOk (rem : sto) | UnAssert (rem_cur : sto).

(* [comment removed for export] *)
Definition divide_body (unnorm : sto -> Z -> bool -> M un_outcome)
           (this denom_ quot0 rem0 : sto) (remDesired : bool) : M div_outcome :=
  do denom <- copy denom_ ;
  if (size denom =? 0)%nat then
    (* [comment removed for export] *)
    emit (EThrow ZeroDivide) ;; destroy denom ;; ret DivZero
  else
  let quot_neg := xorb (s_neg this) (s_neg denom) in
  let rem_neg := s_neg this in
  do num <- copy this ;
  let num := set_neg num false in
  let denom := set_neg denom false in
  if compare num denom <? 0 then
    do quot1 <- assign quot0 (sto_of_word 0) ;          (* [comment removed for export] *)
    let quot1 := set_neg quot1 quot_neg in
    do rem1 <- assign rem0 num ;                        (* [comment removed for export] *)
    let rem1 := set_neg rem1 rem_neg in
    destroy num ;; destroy denom ;;
    ret (DivOk quot1 rem1)
  else
  let num_ws := s_words num in
  let this_ws := s_words this in
  if ((size denom =? 1) && (size num =? 1))%nat then
    do quot1 <- assign quot0 (sto_of_word (W.divu (nth_w num_ws 0) (nth_w (s_words denom) 0))) ;
    do rem1 <- assign rem0 (sto_of_word (W.remu (nth_w num_ws 0) (nth_w (s_words denom) 0))) ;
    let quot1 := set_neg quot1 quot_neg in
    let rem1 := set_neg rem1 rem_neg in
    destroy num ;; destroy denom ;;
    ret (DivOk quot1 rem1)
  else if ((size denom =? 1)%nat && (W.land (nth_w (s_words denom) 0) W.l_mask =? 0)) then
    let divisor := nth_w (s_words denom) 0 in
    do quot1 <- resize quot0 (size this) ;
    let (qws, dHi) := halfdiv_loop (size this) divisor 0 this_ws (s_words quot1) in
    let quot1 := reduce (set_words quot1 qws) in
    do rem1 <- assign rem0 (sto_of_word dHi) ;           (* [comment removed for export] *)
    let quot1 := set_neg quot1 quot_neg in
    let rem1 := set_neg rem1 rem_neg in
    destroy num ;; destroy denom ;;
    ret (DivOk quot1 rem1)
  else
    do num0 <- copy num ;                                (* [comment removed for export] *)
    do denom0 <- copy denom ;                            (* [comment removed for export] *)
    do nrm <- normalize denom num ;
    let '(denom, num, x, second_done) := nrm in
    let l := (size denom - 1)%nat in
    let n := (size num - 1)%nat in
    (* [comment removed for export] *)
    if (size num <? size denom)%nat then
      emit (EThrow AssertNMaxSize) ;;
      destroy denom0 ;; destroy num0 ;; destroy num ;; destroy denom ;;
      ret (DivAssert quot0 rem0)
    else
    do quot1 <- resize quot0 (n - l) ;
    let quot1 := set_words quot1 (zeros (size quot1)) in      (* [comment removed for export] *)
    do rem1 <- assign rem0 num ;                               (* [comment removed for export] *)
    do adj <- (if W.ltu (nth_w (s_words rem1) n) (nth_w (s_words denom) l) then ret (rem1, quot1, n)
               else do rem2 <- resize rem1 (S (size rem1)) ;
                    do quot2 <- resize quot1 (S (size quot1)) ;
                    ret (rem2, quot2, S n)) ;
    let '(rem1, quot1, n) := adj in
    let d := nth_w (s_words denom) l in
    let (rws, qws) := divloop (n - l) n l d (s_words denom) (s_words rem1) (s_words quot1) in
    let quot1 := set_neg (reduce (set_words quot1 qws)) quot_neg in
    let rem1 := set_words rem1 rws in
    do ur <- (if remDesired then unnorm rem1 x second_done else ret (UnOk rem1)) ;
    match ur with
    | UnAssert rem_cur =>
        (* [comment removed for export] *)
        destroy denom0 ;; destroy num0 ;; destroy num ;; destroy denom ;;
        ret (DivAssert quot1 rem_cur)
    | UnOk r =>
        let rem1 := if remDesired then set_neg r rem_neg else r in
        destroy denom0 ;; destroy num0 ;; destroy num ;; destroy denom ;;
        ret (DivOk quot1 rem1)
    end.

(* [comment removed for export] *)
Definition no_unnorm (rem : sto) (x : Z) (sd : bool) : M un_outcome := ret (UnOk rem).
Definition divide_nr (this denom_ quot0 rem0 : sto) : M div_outcome :=
  divide_body no_unnorm this denom_ quot0 rem0 false.

(* [comment removed for export] *)
Definition div_assign (this divisor : sto) : M (sto + sto) :=
  do out <- divide_nr this divisor this sto_empty ;
  match out with
  | DivOk q r => destroy r ;; ret (inl q)
  | DivZero => ret (inl this)                 (* [comment removed for export] *)
  | DivAssert qc rc => destroy rc ;; ret (inr qc)
  end.

(* [comment removed for export] *)
Definition unnormalize (rem0 : sto) (x : Z) (second_done : bool) : M un_outcome :=
  let rem := reduce rem0 in          (* [comment removed for export] *)
  do dr <- (if second_done then div_assign rem (sto_of_word W.max_word) else ret (inl rem)) ;
  match dr with
  | inr rem_cur => ret (UnAssert rem_cur)      (* [comment removed for export] *)
  | inl rem1 =>
      do r <- (if 0 <? x then shr_bits rem1 x else ret (reduce rem1)) ;
      ret (UnOk r)
  end.

Definition divide (this denom_ quot0 rem0 : sto) (remDesired : bool) : M div_outcome :=
  divide_body unnormalize this denom_ quot0 rem0 remDesired.

(* [comment removed for export] *)
Inductive mod_outcome := ModOk (x : sto) | ModZero | ModAssert (x_cur : sto).
Definition mod_assign (this divisor : sto) : M mod_outcome :=
  do out <- divide this divisor sto_empty this true ;
  match out with
  | DivOk q x => destroy q ;; ret (ModOk x)
  | DivZero => destroy sto_empty ;; ret ModZero
  | DivAssert qc xc => destroy qc ;; ret (ModAssert xc)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_digit (c : Z) : bool := (48 <=? c) && (c <=? 57).

(* [comment removed for export] *)
Fixpoint skip_zeros (fuel : nat) (cs : list Z) : nat :=
  match fuel, cs with
  | S f, c :: t => if c =? 48 then S (skip_zeros f t) else O
  | _, _ => O
  end.

(* [comment removed for export] *)
Definition num_words_est (len : nat) : nat :=
  if (len <? 10)%nat then 1%nat
  else Z.to_nat (((Z.of_nat len * 3402) / 1024 + 1 + 63) / 64).

Inductive parse_outcome := ParseOk (value : sto) | ParseErr.   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint digit_loop (fuel : nat) (cs : list Z) (v : sto) : M (option sto) :=
  match fuel, cs with
  | S f, c :: t => if is_digit c then
                     do v1 <- mul_word v 10 ;
                     do v2 <- add_word v1 (c - 48) ;
                     digit_loop f t v2
                   else destroy v ;; ret None         (* [comment removed for export] *)
  | _, _ => ret (Some v)
  end.

(* [comment removed for export] *)
Definition to_bigint_detail (cs : list Z) (neg : bool) (value : sto) : M parse_outcome :=
  let len := length cs in
  if (len =? 0)%nat then ret ParseErr
  else
    let p := skip_zeros len cs in
    if (p =? len)%nat then
      do value1 <- assign value (sto_of_word 0) ;      (* [comment removed for export] *)
      ret (ParseOk value1)
    else
      let nw := num_words_est len in
      do v <- reserve sto_empty nw ;                   (* [comment removed for export] *)
      do r <- digit_loop len cs v ;
      match r with
      | None => ret ParseErr
      | Some v1 =>
          let v2 := if neg then set_neg v1 true else v1 in
          do value1 <- assign value v2 ;               (* [comment removed for export] *)
          destroy v2 ;;                                (* [comment removed for export] *)
          ret (ParseOk value1)
      end.

(* [comment removed for export] *)
Definition to_bigint (cs : list Z) (value : sto) : M parse_outcome :=
  match cs with
  | [] => ret ParseErr
  | c :: t => if c =? 45 then to_bigint_detail t true value else to_bigint_detail cs false value
  end.

(* [comment removed for export] *)
Definition lit_a : list Z :=
  [53;54;54;53;52;50;53;48;53;54;52;48;53;54;49;51;53;52;49;53;54;51;49;53;53;52;53;51;49;53;53;52;53;49;51;56;49;51].

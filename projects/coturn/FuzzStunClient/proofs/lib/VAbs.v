(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition TWO64 : Z := 2 ^ 64.
Definition TWO63 : Z := 2 ^ 63.
Definition TWO32 : Z := 2 ^ 32.
Definition TWO31 : Z := 2 ^ 31.
Definition M64 : Z := 2 ^ 64 - 1.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bnd (A : vstate) (e : lin) : itv :=
  if lin_is_const e then itv_const (lc e) else lp_bounds (vs_store A) e.

Definition bnd_v (A : vstate) (v : absval) : itv :=
  match v with None => itv_top | Some e => bnd A e end.

(* [comment removed for export] *)
Definition qle (A : vstate) (e : lin) (c : Z) : bool :=
  if lin_is_const e then Z.leb (lc e) c else check_hi (vs_store A) e c.
Definition qge (A : vstate) (e : lin) (c : Z) : bool :=
  if lin_is_const e then Z.leb c (lc e) else check_lo (vs_store A) e c.
Definition qwithin (A : vstate) (e : lin) (lo hi : Z) : bool := if qge A e lo then qle A e hi else false.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition inU (A : vstate) (e : lin) : bool := qwithin A e 0 M64.
Definition inS (A : vstate) (e : lin) : bool := qwithin A e (- TWO63) (TWO63 - 1).
Definition inU_v (A : vstate) (v : absval) : bool := match v with Some e => inU A e | None => false end.
Definition inS_v (A : vstate) (v : absval) : bool := match v with Some e => inS A e | None => false end.

(* [comment removed for export] *)
Definition bnd_dead (A : vstate) (e : lin) : bool :=
  if lin_is_const e then false else itv_empty (lp_bounds (vs_store A) e).

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint norm_terms (B : box) (l : list term) (acc : lin) : lin :=
  match l with
  | [] => acc
  | (s, k) :: t =>
      let keep := laxpy acc k (lsym s) in
      if is_fixed s && negb (Pos.eqb s SIZE) then norm_terms B t keep
      else match box_get B s with
           | (Some lo, Some hi) => if Z.eqb lo hi then norm_terms B t (laddc acc (k * lo)) else norm_terms B t keep
           | _ => norm_terms B t keep
           end
  end.

Definition anorm (A : vstate) (e : lin) : lin := norm_terms (sbox (vs_store A)) (lt e) (lconst (lc e)).

Definition anorm_v (A : vstate) (v : absval) : absval :=
  match v with Some e => Some (anorm A e) | None => None end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition afresh (A : vstate) (b : itv) : absval * vstate :=
  let '(e, A') := fresh_lin A b in (Some e, A').

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive reading : Type :=
| RNone                          (* [comment removed for export] *)
| RBot                           (* [comment removed for export] *)
| RZone (lo hi shift : Z).       (* [comment removed for export] *)

Definition zone (lo hi : option Z) (signed : bool) : reading :=
  match lo, hi with
  | Some lo, Some hi =>
      if signed then
        (if Z.leb (- TWO63) lo && Z.ltb hi TWO63 then RZone lo hi 0
         else if Z.leb TWO63 lo && Z.ltb hi TWO64 then RZone (lo - TWO64) (hi - TWO64) (- TWO64)
         else RNone)
      else
        (if Z.leb 0 lo && Z.ltb hi TWO64 then RZone lo hi 0
         else if Z.ltb (- TWO64) lo && Z.ltb hi 0 then RZone (lo + TWO64) (hi + TWO64) TWO64
         else RNone)
  | _, _ => RNone
  end.

Definition readings (A : vstate) (v : absval) (signed : bool) : reading :=
  match v with
  | None => RNone
  | Some e =>
      let first :=
        if lin_is_const e then RNone
        else let '(lo, hi) := lin_range (sbox (vs_store A)) e in zone lo hi signed in
      match first with
      | RZone _ _ _ => first
      | _ =>
          let b := bnd A e in
          if (negb (lin_is_const e)) && itv_empty b then RBot
          else zone (fst b) (snd b) signed
      end
  end.

(* [comment removed for export] *)
Definition mixed (A : vstate) (v : absval) (other_hi : Z) : option (Z * Z) :=
  match v with
  | None => None
  | Some e =>
      let b := bnd A e in
      if (negb (lin_is_const e)) && itv_empty b then None else
      match b with
      | (Some lo, Some hi) => if Z.ltb lo 0 && Z.leb 0 hi && Z.ltb hi TWO64 && Z.ltb other_hi (lo + TWO64)
                              then Some (lo, hi) else None
      | _ => None
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cmp_lt (A : vstate) (a b : absval) (signed : bool) : option bool :=
  let ra := readings A a signed in
  let rb := readings A b signed in
  match ra, rb with
  | RBot, (RBot | RZone _ _ _) | RZone _ _ _, RBot => Some false
  | RZone alo ahi ash, RZone blo bhi bsh =>
      if Z.eqb ash bsh then
        match a, b with
        | Some ea, Some eb =>
            let d := lsub ea eb in
            if lin_is_const d then Some (Z.leb (lc d) (-1))
            else if qle A d (-1) then Some true
            else if qge A d 0 then Some false
            else None
        | _, _ => None
        end
      else if Z.ltb ahi blo then Some true
      else if Z.leb bhi alo then Some false
      else None
  | _, _ => None   (* [comment removed for export] *)
  end.

Definition is_eqne (k : ckind) : bool := match k with CK_eq => true | _ => false end.

(* [comment removed for export] *)
Definition bcond := (ckind * bool)%type.

Definition eval_eq (A : vstate) (a b : absval) : option bool :=
  match a, b with
  | Some ea, Some eb =>
      let d := lsub ea eb in
      if lin_is_const d then Some (Z.eqb (lc d mod TWO64) 0)
      else if qwithin A d 0 0 then Some true
      else if (if (if qge A d 1 then qle A d M64 else false) then true else (if qle A d (-1) then qge A d (- M64) else false)) then Some false
      else let '(m, rr) := lin_cong (scong (vs_store A)) d in
           if (if (if Z.ltb 1 m then negb (Z.eqb (rr mod m) 0) else false) then qwithin A d (- M64) M64 else false) then Some false
           else None
  | _, _ => None
  end.

Definition eval_cond (A : vstate) (c : bcond) (a b : absval) : option bool :=
  let '(k, neg) := c in
  let r := match k with
           | CK_eq => eval_eq A a b
           | CK_lt => cmp_lt A a b true
           | CK_ltu => cmp_lt A a b false
           end in
  match r with Some x => Some (xorb x neg) | None => None end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition aassume (A : vstate) (e : lin) : bool * vstate :=
  match add_constraint (vs_store A) e with
  | Some S' => (true, set_store A S')
  | None => (false, A)
  end.

Definition aassume2 (A : vstate) (e1 e2 : lin) : bool * vstate :=
  let '(ok1, A1) := aassume A e1 in
  let '(ok2, A2) := aassume A1 e2 in
  (ok1 && ok2, A2).

Definition ameet_cong (A : vstate) (s : sym) (m r : Z) : bool * vstate :=
  match store_add_cong (vs_store A) s m r with
  | Some S' => (true, set_store A S')
  | None => (false, set_store A (store_set_box (vs_store A) s (Some 1, Some 0)))
  end.

Definition asetbox (A : vstate) (s : sym) (b : itv) : vstate :=
  set_store A (store_set_box (vs_store A) s b).

Definition agetbox (A : vstate) (s : sym) : itv := store_get_box (vs_store A) s.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition negc (c : bcond) : bcond := (fst c, negb (snd c)).

Definition refine0 (A : vstate) (c : bcond) (a b : absval) : bool * vstate :=
  match a, b with
  | Some ea, Some eb =>
      let '(k, neg) := c in
      match k with
      | CK_eq =>
          let d := lsub ea eb in
          if lin_is_const d then (xorb (Z.eqb (lc d mod TWO64) 0) neg, A)
          else
            let bd := bnd A d in
            if itv_empty bd then (false, A) else
            match bd with
            | (Some lo, Some hi) =>
                if Z.leb lo (- TWO64) || Z.leb TWO64 hi then (true, A)
                else if negb neg then aassume2 A d (lneg d)
                else if Z.eqb lo 0 then aassume A (laddc (lneg d) 1)        (* [comment removed for export] *)
                else if Z.eqb hi 0 then aassume A (laddc d 1)               (* [comment removed for export] *)
                else (true, A)
            | _ => (true, A)
            end
      | _ =>
          let signed := match k with CK_lt => true | _ => false end in
          (* [comment removed for export] *)
          let ra := readings A a signed in
          let rb := readings A b signed in
          match ra, rb with
          | RZone _ _ ash, RZone _ _ bsh =>
              let d := lsub (laddc ea ash) (laddc eb bsh) in
              if negb neg then aassume A (laddc d 1)      (* [comment removed for export] *)
              else aassume A (lneg d)                     (* [comment removed for export] *)
          | RBot, (RBot | RZone _ _ _) | RZone _ _ _, RBot => (false, A)
          | RNone, RZone blo bhi bsh =>
              if signed then (true, A) else
              match mixed A a bhi with
              | Some (malo, mahi) =>
                  if Z.eqb bsh 0 then
                    (if negb neg then
                       (* [comment removed for export] *)
                       aassume2 A (lneg ea) (laddc (lsub ea eb) 1)
                     else (true, A))
                  else (true, A)
              | None => (true, A)
              end
          | RZone alo ahi ash, RNone =>
              if signed then (true, A) else
              match mixed A b ahi with
              | Some (mblo, mbhi) =>
                  if Z.eqb ash 0 then
                    (if neg then
                       (* [comment removed for export] *)
                       aassume2 A (lneg eb) (lsub eb ea)
                     else (true, A))
                  else (true, A)
              | None => (true, A)
              end
          | _, _ => (true, A)
          end
      end
  | _, _ => (true, A)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition point_of (i : itv) : option Z :=
  match i with (Some lo, Some hi) => if Z.eqb lo hi then Some lo else None | _ => None end.

Fixpoint fire_moddefs (A : vstate) (l : list (positive * (lin * Z))) : vstate :=
  match l with
  | [] => A
  | (r, _) :: t =>
      match pm_get r (vs_moddef A) with
      | None => fire_moddefs A t
      | Some (x, m) =>
          match point_of (agetbox A r) with
          | None => fire_moddefs A t
          | Some v =>
              let A1 := set_moddef A (pm_remove r (vs_moddef A)) in
              let A2 :=
                match lin_single x with
                | Some (s, k) =>
                    if Z.eqb (Z.abs k) 1 then snd (ameet_cong A1 s m ((k * (v - lc x)) mod m))
                    else A1
                | None => A1
                end in
              fire_moddefs A2 t
          end
      end
  end.

Fixpoint trigger (fuel : nat) (A : vstate) : vstate :=
  match fuel with
  | O => A
  | S fuel' =>
      (* [comment removed for export] *)
      let fired :=
        find (fun bk : positive * (ckind * lin * lin) =>
                match point_of (agetbox A (fst bk)) with Some _ => true | None => false end)
             (pm_elements (vs_conddef A)) in
      match fired with
      | Some (b, (k, x, y)) =>
          let v := match point_of (agetbox A b) with Some v => v | None => 0 end in
          let A1 := set_conddef A (pm_remove b (vs_conddef A)) in
          (* [comment removed for export] *)
          let c : bcond := (k, negb (Z.eqb v 1)) in
          let '(_, A2) := refine0 A1 c (Some x) (Some y) in
          trigger fuel' A2
      | None => fire_moddefs A (pm_elements (vs_moddef A))
      end
  end.

Definition trigger_fuel (A : vstate) : nat := S (pm_size (vs_conddef A)).

(* [comment removed for export] *)
Definition refine (A : vstate) (c : bcond) (a b : absval) : bool * vstate :=
  let '(ok, A1) := refine0 A c a b in
  (ok, match a, b with Some _, Some _ => trigger (trigger_fuel A1) A1 | _, _ => A1 end).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fdiv (a m : Z) : Z := Z.div a m.   (* [comment removed for export] *)

Definition azext (A : vstate) (v : absval) (nbits : Z) : absval * vstate :=
  let m := 2 ^ nbits in
  match v with
  | None => afresh A (Some 0, Some (m - 1))
  | Some e =>
      if lin_is_const e then (Some (lconst (Z.land (lc e) (m - 1))), A)
      else
        let b := lp_bounds (vs_store A) e in
        if itv_empty b then (Some e, A)
        else match b with
             | (Some lo, Some hi) =>
                 if Z.eqb (fdiv lo m) (fdiv hi m) then (Some (laddc e (- (fdiv lo m) * m)), A)
                 else match lin_low_bits (scong (vs_store A)) e nbits with
                      | Some r => (Some (lconst r), A)
                      | None => afresh A (Some 0, Some (m - 1))
                      end
             | _ => match lin_low_bits (scong (vs_store A)) e nbits with
                    | Some r => (Some (lconst r), A)
                    | None => afresh A (Some 0, Some (m - 1))
                    end
             end
  end.

Definition asext32 (A : vstate) (v : absval) : absval * vstate :=
  match v with
  | None => afresh A (Some (- TWO31), Some (TWO31 - 1))
  | Some e =>
      if lin_is_const e then
        (let x := Z.land (lc e) (TWO32 - 1) in
         (Some (lconst (if Z.leb TWO31 x then x - TWO32 else x)), A))
      else
        let b := lp_bounds (vs_store A) e in
        if itv_empty b then (Some e, A)
        else match b with
             | (Some lo, Some hi) =>
                 let q := fdiv (lo + TWO31) TWO32 in
                 if Z.eqb q (fdiv (hi + TWO31) TWO32) then (Some (laddc e (- q * TWO32)), A)
                 else afresh A (Some (- TWO31), Some (TWO31 - 1))
             | _ => afresh A (Some (- TWO31), Some (TWO31 - 1))
             end
  end.

Definition srange (n : Z) : itv := (Some (- 2 ^ (8 * n - 1)), Some (2 ^ (8 * n - 1) - 1)).
Definition urange (n : Z) : itv := (Some 0, Some (2 ^ (8 * n) - 1)).

(* [comment removed for export] *)
Definition areinterp (A : vstate) (v : lin) (n : Z) (signed : bool) : absval * vstate :=
  if Z.eqb n 8 then (Some v, A)
  else if signed then
    let half := 2 ^ (8 * n - 1) in
    let b := bnd A v in
    let dead := negb (lin_is_const v) && itv_empty b in
    match (if dead then (None, None) else b) with
    | (Some lo, Some hi) =>
        if Z.leb (- half) lo && Z.ltb hi half then (Some v, A)
        else if Z.leb half lo && Z.ltb hi (2 * half) then (Some (laddc v (- (2 * half))), A)
        else afresh A (srange n)
    | _ => afresh A (srange n)
    end
  else azext A (Some v) (8 * n).

(* [comment removed for export] *)
Definition atruncate (A : vstate) (v : lin) (n : Z) (signed : bool) : absval * vstate :=
  if signed then
    let half := 2 ^ (8 * n - 1) in
    let b := bnd A v in
    let dead := negb (lin_is_const v) && itv_empty b in
    match (if dead then (None, None) else b) with
    | (Some lo, Some hi) =>
        if Z.leb (- half) lo && Z.ltb hi half then (Some v, A) else afresh A (srange n)
    | _ => afresh A (srange n)
    end
  else azext A (Some v) (8 * n).

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive ares : Type :=
| AR (v : absval) (A : vstate)
| AFork (bsym : sym) (v0 v1 : absval) (blo : Z) (A : vstate).

(* [comment removed for export] *)
Definition mask01 (A : vstate) (v : absval) : option (sym * Z * Z * Z) :=
  match v with
  | None => None
  | Some e =>
      if lin_is_const e then None else
      match lin_single e with
      | None => None
      | Some (s, k) =>
          match agetbox A s with
          | (Some lo, Some hi) => if Z.eqb (hi - lo) 1 then Some (s, k * lo + lc e, k * hi + lc e, lo) else None
          | _ => None
          end
      end
  end.

Definition zm64 (z : Z) : Z := Z.land z M64.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition log2_exact (x : Z) : option Z :=
  if Z.ltb 0 x && Z.eqb x (2 ^ Z.log2 x) then Some (Z.log2 x) else None.
Definition is_pow2 (x : Z) : bool := match log2_exact x with Some _ => true | None => false end.
Definition is_lowmask (m : Z) : bool := is_pow2 (m + 1).          (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint terms_divisible (l : list term) (m : Z) : bool :=
  match l with [] => true | (_, k) :: t => Z.eqb (k mod m) 0 && terms_divisible t m end.
Definition ldivisible (e : lin) (m : Z) : bool := Z.eqb (lc e mod m) 0 && terms_divisible (lt e) m.

(* [comment removed for export] *)
Definition and_mask (A : vstate) (x : lin) (m : Z) : ares :=
  if is_lowmask m then
    let k1 := m + 1 in
    let b := lp_bounds (vs_store A) x in
    let inseg := match b with
                 | (Some lo, Some hi) => if itv_empty b then false else Z.eqb (fdiv lo k1) (fdiv hi k1)
                 | _ => false end in
    if inseg then
      match b with
      | (Some lo, _) => AR (Some (laddc x (- (fdiv lo k1) * k1))) A
      | _ => AR None A
      end
    else
      let '(cm, cr) := lin_cong (scong (vs_store A)) x in
      if (Z.eqb cm 0) || ((Z.ltb 0 cm) && Z.eqb (cm mod k1) 0) then AR (Some (lconst (cr mod k1))) A
      else
        let top := match b with
                   | (Some lo, Some hi) => if Z.ltb lo 0 then m else Z.min m hi
                   | _ => m end in
        let '(rs, A1) := fresh_sym A in
        let A2 := asetbox A1 rs (Some 0, Some top) in
        let A3 := if Z.ltb 1 cm && Z.eqb (k1 mod cm) 0 then snd (ameet_cong A2 rs cm cr) else A2 in
        let A4 := set_moddef A3 (pm_set rs (x, k1) (vs_moddef A3)) in
        AR (Some (lsym rs)) A4
  else
    let neg := TWO64 - m in
    if is_pow2 neg then
      (* [comment removed for export] *)
      let '(cm, cr) := lin_cong (scong (vs_store A)) x in
      if (Z.eqb cm 0) || ((Z.ltb 0 cm) && Z.eqb (cm mod neg) 0) then AR (Some (laddc x (- (cr mod neg)))) A
      else
        let b := lp_bounds (vs_store A) x in
        let qb := (match fst b with Some lo => Some (lo - (neg - 1)) | None => None end, snd b) in
        let '(q, A1) := fresh_sym A in
        let A2 := asetbox A1 q qb in
        let A3 := snd (ameet_cong A2 q neg 0) in
        let ql := lsym q in
        let A4 := snd (aassume A3 (lsub ql x)) in                      (* [comment removed for export] *)
        let A5 := snd (aassume A4 (laddc (lsub x ql) (- (neg - 1)))) in  (* [comment removed for export] *)
        AR (Some ql) A5
    else if Z.ltb m TWO63 then
      let b := lp_bounds (vs_store A) x in
      let top := match b with
                 | (Some lo, Some hi) => if Z.ltb lo 0 then m else Z.min m hi
                 | _ => m end in
      let '(v, A1) := afresh A (Some 0, Some top) in AR v A1
    else AR None A.

Definition and_const (A : vstate) (x : absval) (c : Z) : ares :=
  let m := zm64 c in
  if Z.eqb m 0 then AR (Some lzero) A
  else if Z.eqb m M64 then AR x A
  else match x with
       | None => if Z.ltb m TWO63 then (let '(v, A1) := afresh A (Some 0, Some m) in AR v A1) else AR None A
       | Some xe =>
           if lin_is_const xe then AR (Some (lconst (Z.land (lc xe) m))) A
           else and_mask A xe m
       end.

(* [comment removed for export] *)
Definition sel_and (A : vstate) (x y : absval) : option ares :=
  match mask01 A x, y with
  | Some (bsym, m0, m1, blo), Some _ =>
      let z0 := zm64 m0 in let z1 := zm64 m1 in
      if (Z.eqb z0 0 && Z.eqb z1 M64) || (Z.eqb z0 M64 && Z.eqb z1 0) then
        Some (AFork bsym (if Z.eqb z0 0 then Some lzero else y) (if Z.eqb z1 0 then Some lzero else y) blo A)
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition cap16 (m : Z) : Z := if Z.eqb m 0 || Z.ltb 65536 m then 65536 else m.

Definition bitcong_ok (m ma mb : Z) : bool :=
  Z.ltb 1 m && is_pow2 m && Z.eqb (ma mod m) 0 && Z.eqb (mb mod m) 0.

(* [comment removed for export] *)
Definition bitcong_mod (A : vstate) (ea eb : lin) : Z * Z * Z * bool :=
  let '(ma, ra) := lin_cong (scong (vs_store A)) ea in
  let '(mb, rb) := lin_cong (scong (vs_store A)) eb in
  let m := Z.min (cap16 ma) (cap16 mb) in
  (m, ra, rb, bitcong_ok m ma mb).

Definition abitcong (A : vstate) (v : absval) (ea eb : lin) (f : Z -> Z -> Z) : vstate :=
  match v with
  | Some r =>
      match lin_single r with
      | Some (s, k) =>
          if Z.eqb k 1 && Z.eqb (lc r) 0 then
            let '(m, ra, rb, ok) := bitcong_mod A ea eb in
            if ok then snd (ameet_cong A s m ((f (ra mod m) (rb mod m)) mod m)) else A
          else A
      | None => A
      end
  | None => A
  end.

Definition and_generic (A : vstate) (a b : absval) : ares :=
  match a, b with
  | Some ea, Some eb =>
      if (if inU A ea then inU A eb else false) then
        match snd (lp_bounds (vs_store A) ea), snd (lp_bounds (vs_store A) eb) with
        | Some ha, Some hb => let '(v, A1) := afresh A (Some 0, Some (Z.min ha hb)) in AR v (abitcong A1 v ea eb Z.land)
        | _, _ => AR None A
        end
      else AR None A
  | Some x, None | None, Some x =>
      if inU A x then
        match snd (lp_bounds (vs_store A) x) with
        | Some h => let '(v, A1) := afresh A (Some 0, Some h) in AR v A1
        | None => AR None A
        end
      else AR None A
  | None, None => AR None A
  end.

Definition const_of (v : absval) : option Z :=
  match v with Some e => if lin_is_const e then Some (lc e) else None | None => None end.

Definition do_and (A : vstate) (a b : absval) : ares :=
  match a, b with
  | None, None => AR None A
  | _, _ =>
      match const_of b with
      | Some cb => and_const A a cb
      | None =>
      match const_of a with
      | Some ca => and_const A b ca
      | None =>
        match sel_and A a b with
        | Some r => r
        | None =>
        match sel_and A b a with
        | Some r => r
        | None => and_generic A a b
        end end
      end end
  end.

(* [comment removed for export] *)
Definition next_pow2 (hi : Z) : Z := if Z.leb hi 0 then 1 else 2 ^ (Z.log2 hi + 1).

Definition sel_or (A : vstate) (x y : absval) : option ares :=
  match mask01 A x with
  | Some (bsym, m0, m1, blo) =>
      let z0 := zm64 m0 in let z1 := zm64 m1 in
      if (Z.eqb z0 0 && Z.eqb z1 M64) || (Z.eqb z0 M64 && Z.eqb z1 0) then
        Some (AFork bsym (if Z.eqb z0 0 then y else Some (lconst (-1)))
                         (if Z.eqb z1 0 then y else Some (lconst (-1))) blo A)
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition or_disjoint (A : vstate) (x y : lin) : option ares :=
  match bnd A y with
  | (Some lo, Some hi) =>
      if negb (lin_is_const y) && itv_empty (bnd A y) then None
      else if Z.leb 0 lo then (let k1 := next_pow2 hi in if ldivisible x k1 then Some (AR (Some (ladd x y)) A) else None)
      else None
  | _ => None
  end.

Definition or_generic (A : vstate) (ea eb : lin) : ares :=
  if (if inU A ea then inU A eb else false) then
    match lp_bounds (vs_store A) ea, lp_bounds (vs_store A) eb with
    | (Some la, Some ha), (Some lb, Some hb) =>
        let k1 := next_pow2 (Z.max ha hb) in
        let '(v, A1) := afresh A (Some (Z.max la lb), Some (k1 - 1)) in AR v (abitcong A1 v ea eb Z.lor)
    | _, _ => AR None A
    end
  else
    (* [comment removed for export] *)
    let '(m, ra, rb, ok) := bitcong_mod A ea eb in
    if ok then
      let '(s, A1) := fresh_sym A in
      AR (Some (lsym s)) (snd (ameet_cong A1 s m ((Z.lor (ra mod m) (rb mod m)) mod m)))
    else AR None A.

Definition do_or (A : vstate) (a b : absval) : ares :=
  match a, b with
  | Some ea, Some eb =>
      if lin_is_const eb && Z.eqb (zm64 (lc eb)) 0 then AR a A
      else if lin_is_const ea && Z.eqb (zm64 (lc ea)) 0 then AR b A
      else if lin_is_const ea && lin_is_const eb then AR (Some (lconst (zm64 (Z.lor (lc ea) (lc eb))))) A
      else
        match sel_or A a b with
        | Some r => r
        | None =>
        match sel_or A b a with
        | Some r => r
        | None =>
        match or_disjoint A ea eb with
        | Some r => r
        | None =>
        match or_disjoint A eb ea with
        | Some r => r
        | None => or_generic A ea eb
        end end end end
  | _, _ => AR None A
  end.

Definition xor_const (A : vstate) (x y : lin) : option (absval * vstate) :=
  if lin_is_const y then
    (if Z.eqb (zm64 (lc y)) 0 then Some (Some x, A)
     else if Z.eqb (zm64 (lc y)) M64 then Some (Some (lsub (lconst (-1)) x), A)
     else if lin_is_const x then Some (Some (lconst (zm64 (Z.lxor (lc x) (lc y)))), A)
     else None)
  else None.

Definition xor_generic (A : vstate) (ea eb : lin) : absval * vstate :=
  if lin_eqb ea eb then (Some lzero, A)
  else if (if inU A ea then inU A eb else false) then
    match lp_bounds (vs_store A) ea, lp_bounds (vs_store A) eb with
    | (_, Some ha), (_, Some hb) => afresh A (Some 0, Some (next_pow2 (Z.max ha hb) - 1))
    | _, _ => (None, A)
    end
  else (None, A).

Definition do_xor (A : vstate) (a b : absval) : absval * vstate :=
  match a, b with
  | Some ea, Some eb =>
      match xor_const A ea eb with
      | Some r => r
      | None =>
      match xor_const A eb ea with
      | Some r => r
      | None => xor_generic A ea eb
      end end
  | _, _ => (None, A)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ashr (A : vstate) (a : lin) (k : Z) (width : Z) : absval * vstate :=
  if Z.eqb k 0 then (Some a, A)
  else if lin_is_const a then (Some (lconst (Z.shiftr (lc a) k)), A)
  else
    let b := lp_bounds (vs_store A) a in
    let lo := match fst b with Some lo => if Z.ltb lo 0 then 0 else lo | None => 0 end in
    let hi := match snd b with Some hi => hi | None => 2 ^ width - 1 end in
    afresh A (Some (Z.shiftr lo k), Some (Z.shiftr hi k)).

Definition ashr_signed (A : vstate) (a : lin) (k : Z) : absval * vstate :=
  if Z.eqb k 0 then (Some a, A)
  else if lin_is_const a then (Some (lconst (Z.shiftr (lc a) k)), A)
  else
    match lp_bounds (vs_store A) a with
    | (Some lo, Some hi) => afresh A (Some (Z.shiftr lo k), Some (Z.shiftr hi k))
    | _ => afresh A (Some (- 2 ^ (63 - k)), Some (2 ^ (63 - k) - 1))
    end.

(* [comment removed for export] *)
Fixpoint terms_shiftr (l : list term) (k : Z) : list term :=
  match l with
  | [] => []
  | (s, c) :: t => (s, Z.shiftr c k) :: terms_shiftr t k
  end.
Definition lshiftr (e : lin) (k : Z) : lin := mkLin (Z.shiftr (lc e) k) (terms_shiftr (lt e) k).

Inductive shop : Type := SH_sll | SH_srl | SH_sra.

Definition s32range : itv := (Some (- TWO31), Some (TWO31 - 1)).

Definition do_shift (A : vstate) (a : absval) (kb : absval) (op : shop) (width : Z) : absval * vstate :=
  let kconst := match kb with Some e => if lin_is_const e then Some (lc e) else None | None => None end in
  match kconst with
  | None =>
      match op, a with
      | SH_srl, Some ea =>
          if inU A ea then
            match snd (lp_bounds (vs_store A) ea) with
            | Some h => if Z.eqb width 64 || Z.ltb h TWO31 then afresh A (Some 0, Some h)
                        else afresh A s32range   (* [comment removed for export] *)
            | None => if Z.eqb width 64 then (None, A) else afresh A s32range
            end
          else if Z.eqb width 64 then (None, A) else afresh A s32range
      | _, _ => if Z.eqb width 64 then (None, A) else afresh A s32range
      end
  | Some kc =>
      let k := Z.land kc (width - 1) in
      match a with
      | None =>
          match op with
          | SH_srl => if Z.eqb width 64 then afresh A (Some 0, Some (2 ^ (64 - k) - 1))
                      else if Z.ltb 0 k then afresh A (Some 0, Some (2 ^ (32 - k) - 1))
                      else afresh A s32range
          | SH_sra => afresh A (Some (- 2 ^ (width - 1 - k)), Some (2 ^ (width - 1 - k) - 1))
          | SH_sll => if Z.eqb width 64 then (None, A) else afresh A s32range
          end
      | Some ea =>
          if Z.eqb width 32 then
            match op with
            | SH_sll => asext32 A (Some (lscale (2 ^ k) ea))
            | SH_srl => let '(a32, A1) := azext A (Some ea) 32 in
                        match a32 with
                        | Some e32 => let '(r, A2) := ashr A1 e32 k 32 in asext32 A2 r
                        | None => afresh A1 s32range
                        end
            | SH_sra => let '(s32, A1) := asext32 A (Some ea) in
                        match s32 with
                        | Some e32 => ashr_signed A1 e32 k
                        | None => afresh A1 s32range
                        end
            end
          else
            match op with
            | SH_sll => (Some (lscale (2 ^ k) ea), A)
            | SH_srl =>
                if lin_is_const ea then (Some (lconst (Z.shiftr (zm64 (lc ea)) k)), A)
                else if ldivisible ea (2 ^ k) then azext A (Some (lshiftr ea k)) (64 - k)
                else if inU A ea then ashr A ea k 64
                else match readings A (Some ea) false with
                     | RZone lo hi _ => afresh A (Some (Z.shiftr lo k), Some (Z.shiftr hi k))
                     | _ => afresh A (Some 0, Some (2 ^ (64 - k) - 1))
                     end
            | SH_sra =>
                if lin_is_const ea then
                  (let v := zm64 (lc ea) in
                   let v := if Z.leb TWO63 v then v - TWO64 else v in
                   (Some (lconst (Z.shiftr v k)), A))
                else
                  let try_div :=
                    if ldivisible ea (2 ^ k) then
                      let q := lshiftr ea k in
                      match lp_bounds (vs_store A) q with
                      | (Some lo, Some hi) =>
                          let half := 2 ^ (63 - k) in
                          if Z.leb (- half) lo && Z.ltb hi half && negb (itv_empty (Some lo, Some hi)) then Some (Some q, A)
                          else None
                      | _ => None
                      end
                    else None in
                  match try_div with
                  | Some r => r
                  | None =>
                      (* [comment removed for export] *)
                      let sign63 :=
                        if Z.eqb k 63 && ldivisible ea (2 ^ k) then
                          match and_const A (Some (lshiftr ea k)) 1 with
                          | AR (Some r) A1 => Some (Some (lneg r), A1)
                          | _ => None
                          end
                        else None in
                      match sign63 with
                      | Some r => r
                      | None =>
                          if inS A ea then ashr_signed A ea k
                          else afresh A (Some (- 2 ^ (63 - k)), Some (2 ^ (63 - k) - 1))
                      end
                  end
            end
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition do_slt (A : vstate) (a b : absval) (signed : bool) : absval * vstate :=
  match cmp_lt A a b signed with
  | Some true => (Some (lconst 1), A)
  | Some false => (Some lzero, A)
  | None =>
      let '(bsym, A1) := fresh_sym A in
      let A2 := asetbox A1 bsym (Some 0, Some 1) in
      let A3 := match a, b with
                | Some ea, Some eb =>
                    set_conddef A2 (pm_set bsym ((if signed then CK_lt else CK_ltu), ea, eb) (vs_conddef A2))
                | _, _ => A2
                end in
      (Some (lsym bsym), A3)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive mop : Type := MO_mul | MO_mulh | MO_mulhsu | MO_mulhu | MO_div | MO_divu | MO_rem | MO_remu.

Definition do_muldiv (A : vstate) (op : mop) (a b : absval) (width : Z) : absval * vstate :=
  match op with
  | MO_mul =>
      match a, b with
      | Some ea, Some eb =>
          if lin_is_const ea then (Some (lscale (lc ea) eb), A)
          else if lin_is_const eb then (Some (lscale (lc eb) ea), A)
          else
            match lp_bounds (vs_store A) ea, lp_bounds (vs_store A) eb with
            | (Some la, Some ha), (Some lb, Some hb) =>
                let c1 := la * lb in let c2 := la * hb in let c3 := ha * lb in let c4 := ha * hb in
                afresh A (Some (Z.min (Z.min c1 c2) (Z.min c3 c4)), Some (Z.max (Z.max c1 c2) (Z.max c3 c4)))
            | _, _ => (None, A)
            end
      | _, _ => (None, A)
      end
  | MO_remu | MO_divu =>
      match a, b with
      | Some ea, Some eb =>
          if (if inU A ea then inU A eb else false) then
            let ba := bnd A ea in let bb := bnd A eb in
            match ba, bb with
            | (Some la, Some ha), (Some lb, Some hb) =>
                match op with
                | MO_remu =>
                    if Z.leb 1 lb then
                      (if lin_is_const ea && lin_is_const eb then (Some (lconst (lc ea mod lc eb)), A)
                       else if Z.ltb ha lb then (Some ea, A)
                       else
                         let top := Z.min ha (hb - 1) in
                         let '(r, A1) := fresh_sym A in
                         let A2 := asetbox A1 r (Some 0, Some top) in
                         let rl := lsym r in
                         let A3 := if lin_is_const eb then A2 else snd (aassume A2 (laddc (lsub rl eb) 1)) in
                         let A4 := if lin_is_const ea then A3 else snd (aassume A3 (lsub rl ea)) in
                         (Some rl, A4))
                    else
                      let top := if Z.leb 1 hb then Z.max ha (hb - 1) else ha in
                      afresh A (Some 0, Some top)
                | _ =>
                    if Z.leb 1 lb then
                      (if lin_is_const ea && lin_is_const eb then (Some (lconst (lc ea / lc eb)), A)
                       else afresh A (Some (la / hb), Some (ha / lb)))
                    else (None, A)
                end
            | _, _ => (None, A)
            end
          else (None, A)
      | None, Some eb =>
          match op with
          | MO_remu =>
              if inU A eb then
                match bnd A eb with
                | (Some lb, Some hb) =>
                    if Z.leb 1 lb then
                      let '(r, A1) := fresh_sym A in
                      let A2 := asetbox A1 r (Some 0, Some (hb - 1)) in
                      let A3 := if lin_is_const eb then A2 else snd (aassume A2 (laddc (lsub (lsym r) eb) 1)) in
                      (Some (lsym r), A3)
                    else (None, A)
                | _ => (None, A)
                end
              else (None, A)
          | _ => (None, A)
          end
      | _, _ => (None, A)
      end
  | MO_div | MO_rem =>
      match a, b with
      | Some ea, Some eb =>
          if (if inS A ea then inS A eb else false) then
            match bnd A ea, bnd A eb with
            | (Some la, Some ha), (Some lb, Some hb) =>
                if Z.leb 0 la && Z.leb 1 lb then
                  (if lin_is_const ea && lin_is_const eb then
                     (Some (lconst (match op with MO_div => lc ea / lc eb | _ => lc ea mod lc eb end)), A)
                   else match op with
                        | MO_div => afresh A (Some (la / hb), Some (ha / lb))
                        | _ => afresh A (Some 0, Some (Z.min ha (hb - 1)))
                        end)
                else (None, A)
            | _, _ => (None, A)
            end
          else (None, A)
      | _, _ => (None, A)
      end
  | MO_mulhu =>
      match a, b with
      | Some ea, Some eb =>
          if (if inU A ea then inU A eb else false) then
            match bnd A ea, bnd A eb with
            | (Some la, Some ha), (Some lb, Some hb) =>
                afresh A (Some (Z.shiftr (Z.max la 0 * Z.max lb 0) 64), Some (Z.shiftr (ha * hb) 64))
            | _, _ => (None, A)
            end
          else (None, A)
      | _, _ => (None, A)
      end
  | _ => (None, A)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zrange (lo : Z) (n : nat) : list Z :=
  match n with O => [] | S n' => lo :: zrange (lo + 1) n' end.

Definition enum_values (A : vstate) (e : lin) : option (list Z) :=
  if lin_is_const e then Some [zm64 (lc e)]
  else
    let vs := match lin_single e with
              | Some (s, k) => if Z.eqb k 1 then
                                 match pm_get s (vs_valset A) with
                                 | Some xs => Some (map (fun x => zm64 (x + lc e)) xs)
                                 | None => None
                                 end
                               else None
              | None => None
              end in
    match vs with
    | Some l => Some l
    | None =>
        match lp_bounds (vs_store A) e with
        | (Some lo, Some hi) =>
            if Z.leb (hi - lo) 64 && Z.leb lo hi then Some (map zm64 (zrange lo (Z.to_nat (hi - lo + 1)))) else None
        | _ => None
        end
    end.

Definition assume_eq (A : vstate) (e : lin) (c : Z) : bool * vstate :=
  let d := laddc e (- c) in
  if lin_is_const d then (Z.eqb (lc d) 0, A)
  else
    let '(ok, A1) := aassume2 A d (lneg d) in
    let A2 := match lin_single e with
              | Some (s, k) => if Z.eqb k 1 then
                                 match pm_get s (vs_valset A1) with
                                 | Some _ => set_valset A1 (pm_set s [c - lc e] (vs_valset A1))
                                 | None => A1
                                 end
                               else A1
              | None => A1
              end in
    (ok, A2).

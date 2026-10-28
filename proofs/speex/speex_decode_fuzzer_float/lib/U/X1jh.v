(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1rd X1oc X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Inductive parg : Type := PA_s (s : list Z) | PA_i (i : Z) | PA_u (u : Z) | PA_g (d : Z).

Definition is_digit (c : Z) : bool := (48 <=? c) && (c <=? 57).

Definition T_PTR : Z := 9.  Definition T_INT : Z := 10.  Definition T_UINT : Z := 11.  Definition T_DBL : Z := 25.

Definition FLAGMASK : Z := 75913.

Fixpoint digits_aux (fuel : nat) (base : Z) (dig : Z -> Z) (x : Z) (acc : list Z) : list Z :=
match fuel with
| O => acc
| S fuel' => if x =? 0 then acc else digits_aux fuel' base dig (x / base) (dig (x mod base) :: acc)
end.

Definition dec_digits (x : Z) : list Z := digits_aux 20 10 (fun v => 48 + v) x [].

Definition XDIGITS : list Z := [48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 65; 66; 67; 68; 69; 70].
Definition hex_digits (lower : Z) (x : Z) : list Z := digits_aux 16 16 (fun v => Z.lor (znth XDIGITS v) lower) x [].

Fixpoint lit_run (s : list Z) : list Z :=
match s with
| [] => []
| c :: s' => if (c =? 0) || (c =? 37) then [] else c :: lit_run s'
end.

Definition flag_bit (c : Z) : option Z :=
if (32 <=? c) && (c <? 64) && negb (Z.land FLAGMASK (Z.shiftl 1 (c - 32)) =? 0)
then Some (Z.shiftl 1 (c - 32)) else None.
Fixpoint parse_flags (s : list Z) (fl : Z) {struct s} : Z * list Z :=
match s with
| [] => (fl, s)
| c :: s' => match flag_bit c with
| Some b => parse_flags s' (Z.lor fl b)
| None => (fl, s)
end
end.

Fixpoint getint (s : list Z) (i : Z) {struct s} : option (Z * list Z) :=
match s with
| [] => Some (i, s)
| c :: s' => if is_digit c then
if (214748364 <? i) || (INT_MAX - 10 * i <? c - 48) then None
else getint s' (10 * i + (c - 48))
else Some (i, s)
end.

Definition conv_type (t : Z) : option Z :=
if t =? 115 then Some T_PTR
else if (t =? 100) || (t =? 105) then Some T_INT
else if (t =? 117) || (t =? 120) || (t =? 88) then Some T_UINT
else if (t =? 101) || (t =? 102) || (t =? 103) || (t =? 69) || (t =? 70) || (t =? 71)
then Some T_DBL
else None.

Record dir : Type := mkDir { d_fl : Z; d_w : Z; d_p : Z; d_xp : bool; d_t : Z; d_ty : Z }.

Definition parse_dir (s : list Z) : option (dir * list Z) :=
let positional := match s with
| c1 :: c2 :: _ => is_digit c1 && (c2 =? 36)
| [c1] => is_digit c1
| [] => false
end in
if positional then None else
let '(fl, s1) := parse_flags s 0 in
match s1 with
| [] => None
| c1 :: _ =>
if c1 =? 42 then None else
let? (w, s2) := getint s1 0 in
match s2 with
| [] => None
| c2 :: s2' =>
let pxs : option (Z * bool * list Z) :=
if c2 =? 46 then
match s2' with
| [] => None
| c3 :: _ => if c3 =? 42 then None
else let? (p, s3) := getint s2' 0 in Some (p, true, s3)
end
else Some (-1, false, s2) in
match pxs with
| None => None
| Some (p, xp, s3) =>
match s3 with
| [] => None
| t :: s4 => let? ty := conv_type t in Some (mkDir fl w p xp t ty, s4)
end
end
end
end.

Section PrintfModel.
Context {RCEIL : RunCeiling}.
Context {St : Type}.
Variable OUT : list Z -> M St unit.
Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.

Definition mpad (c w l fl : Z) : M St unit :=
if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l) then mret tt
else if 256 <=? w - l then munr
else OUT (zrepeat c (w - l)).

Definition conv_tail (cnt fl w p : Z) (prefix body : list Z) : M St Z :=
let pl := zlength prefix in
let n := zlength body in
let p := Z.max p n in
if INT_MAX - pl <? p then munr else
let w := Z.max w (pl + p) in
if INT_MAX - cnt <? w then munr else
mpad 32 w (pl + p) fl ;;;
OUT prefix ;;;
mpad 48 w (pl + p) (Z.lxor fl ZERO_PAD) ;;;
mpad 48 p n 0 ;;;
OUT body ;;;
mpad 32 w (pl + p) (Z.lxor fl LEFT_ADJ) ;;;
mret (cnt + w).

Definition conv_int (cnt fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) : M St Z :=
if xp && (p <? 0) then munr else
let fl := if xp then Z.land fl (Z.lnot ZERO_PAD) else fl in
if (argi =? 0) && (p =? 0) then conv_tail cnt fl w p prefix []
else conv_tail cnt fl w (Z.max p (zlength body + (if argi =? 0 then 1 else 0))) prefix body.

Definition conv (cnt : Z) (d : dir) (a : parg) : M St Z :=
let fl := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD) in
let w := d_w d in let p := d_p d in let xp := d_xp d in let t := d_t d in
match a with
| PA_s s =>
if negb (d_ty d =? T_PTR) then munr else

if (p <? 0) && (INT_MAX <=? zlength s) then munr else
let n := if p <? 0 then zlength s else Z.min (zlength s) p in
conv_tail cnt (Z.land fl (Z.lnot ZERO_PAD)) w n [] (firstn (Z.to_nat n) s)
| PA_i i =>
if negb (d_ty d =? T_INT) then munr else
let argi := i mod 2^64 in

let '(argi, prefix) :=
if INTMAX_MAX <? argi then ((- argi) mod 2^64, [45])
else if negb (Z.land fl MARK_POS =? 0) then (argi, [43])
else if negb (Z.land fl PAD_POS =? 0) then (argi, [32])
else (argi, []) in
conv_int cnt fl w p xp argi prefix (dec_digits argi)
| PA_u u =>
if negb (d_ty d =? T_UINT) then munr else
if t =? 117 then conv_int cnt fl w p xp u [] (dec_digits u)
else

let prefix := if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0)
then (if t =? 120 then [48; 120] else [48; 88]) else [] in
conv_int cnt fl w p xp u prefix (hex_digits (Z.land t 32) u)
| PA_g dd =>
if negb (d_ty d =? T_DBL) then munr else
if xp && (p <? 0) then munr else
if (1 <? w) || (2^20 <=? p) then munr else
r <- OUTFP (f128_of_d dd) w p fl t ;;
if (r <? 0) || (INT_MAX - cnt <? r) then munr else mret (cnt + r)
end.

Fixpoint printf_loop (fuel : nat) (s : list Z) (args : list parg) (cnt : Z) {struct fuel} : M St Z :=
match fuel with
| O => munr
| S fuel' =>
match s with
| [] => munr
| c :: _ =>
if c =? 0 then mret cnt else
let lit := lit_run s in
let l := zlength lit in
let s1 := skipn (Datatypes.length lit) s in
match s1 with
| [] => munr
| c1 :: s2 =>
if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end
then munr
else if 0 <? l then
(if INT_MAX - cnt <? l then munr
else OUT lit ;;; printf_loop fuel' s1 args (cnt + l))
else
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
OUT [] ;;;
cnt' <- conv cnt d a ;;
printf_loop fuel' s3 args' cnt'
| _, _ => munr
end
end
end
end.

Definition printf_model (fmt : list Z) (args : list parg) : M St Z :=
printf_loop (Datatypes.length fmt) fmt args 0.
End PrintfModel.

Arguments mpad {St} OUT _ _ _ _.
Arguments conv_tail {St} OUT _ _ _ _ _ _.
Arguments conv_int {St} OUT _ _ _ _ _ _ _ _.
Arguments conv {St} OUT OUTFP _ _ _.
Arguments printf_loop {St} OUT OUTFP _ _ _ _.
Arguments printf_model {St} OUT OUTFP _ _.

Fixpoint fp_calls (fuel : nat) (s : list Z) (args : list parg) {struct fuel} : list (Z * Z * Z * Z * Z) :=
match fuel with
| O => []
| S fuel' =>
match s with
| [] => []
| c :: _ =>
if c =? 0 then [] else
let lit := lit_run s in
let s1 := skipn (Datatypes.length lit) s in
if 0 <? zlength lit then fp_calls fuel' s1 args
else match s1 with
| _ :: s2 =>
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
match a with
| PA_g dd =>
let fl := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD) in
(f128_of_d dd, d_w d, d_p d, fl, d_t d) :: fp_calls fuel' s3 args'
| _ => fp_calls fuel' s3 args'
end
| _, _ => []
end
| _ => []
end
end
end.

Definition pass1_ok (fmt : list Z) : bool :=
let lit := lit_run fmt in
(zlength lit <=? INT_MAX) &&
match skipn (Datatypes.length lit) fmt with
| [] => false
| c1 :: s2 =>
if c1 =? 0 then true
else match s2 with
| [] => false
| c2 :: _ => negb (c2 =? 37) && match parse_dir s2 with Some _ => true | None => false end
end
end.

Definition pad_pieces (c w l fl : Z) : option (list (list Z)) :=
if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l) then Some []
else if 256 <=? w - l then None
else Some [zrepeat c (w - l)].

Definition tail_pieces (cnt fl w p : Z) (prefix body : list Z) : option (list (list Z) * Z) :=
let pl := zlength prefix in
let n := zlength body in
let p := Z.max p n in
if INT_MAX - pl <? p then None else
let w := Z.max w (pl + p) in
if INT_MAX - cnt <? w then None else
let? p1 := pad_pieces 32 w (pl + p) fl in
let? p2 := pad_pieces 48 w (pl + p) (Z.lxor fl ZERO_PAD) in
let? p3 := pad_pieces 48 p n 0 in
let? p4 := pad_pieces 32 w (pl + p) (Z.lxor fl LEFT_ADJ) in
Some (p1 ++ [prefix] ++ p2 ++ p3 ++ [body] ++ p4, cnt + w).

Definition int_pieces (cnt fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) : option (list (list Z) * Z) :=
if xp && (p <? 0) then None else
let fl := if xp then Z.land fl (Z.lnot ZERO_PAD) else fl in
if (argi =? 0) && (p =? 0) then tail_pieces cnt fl w p prefix []
else tail_pieces cnt fl w (Z.max p (zlength body + (if argi =? 0 then 1 else 0))) prefix body.

Definition conv_pieces (cnt : Z) (d : dir) (a : parg) : option (list (list Z) * Z) :=
let fl := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD) in
let w := d_w d in let p := d_p d in let xp := d_xp d in let t := d_t d in
match a with
| PA_s s =>
if negb (d_ty d =? T_PTR) then None else
if (p <? 0) && (INT_MAX <=? zlength s) then None else
let n := if p <? 0 then zlength s else Z.min (zlength s) p in
tail_pieces cnt (Z.land fl (Z.lnot ZERO_PAD)) w n [] (firstn (Z.to_nat n) s)
| PA_i i =>
if negb (d_ty d =? T_INT) then None else
let argi := i mod 2^64 in
let '(argi, prefix) :=
if INTMAX_MAX <? argi then ((- argi) mod 2^64, [45])
else if negb (Z.land fl MARK_POS =? 0) then (argi, [43])
else if negb (Z.land fl PAD_POS =? 0) then (argi, [32])
else (argi, []) in
int_pieces cnt fl w p xp argi prefix (dec_digits argi)
| PA_u u =>
if negb (d_ty d =? T_UINT) then None else
if t =? 117 then int_pieces cnt fl w p xp u [] (dec_digits u)
else
let prefix := if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0)
then (if t =? 120 then [48; 120] else [48; 88]) else [] in
int_pieces cnt fl w p xp u prefix (hex_digits (Z.land t 32) u)
| PA_g _ => None
end.

Fixpoint printf_pieces_loop (fuel : nat) (s : list Z) (args : list parg) (cnt : Z) {struct fuel}
: option (list (list Z) * Z) :=
match fuel with
| O => None
| S fuel' =>
match s with
| [] => None
| c :: _ =>
if c =? 0 then Some ([], cnt) else
let lit := lit_run s in
let l := zlength lit in
let s1 := skipn (Datatypes.length lit) s in
match s1 with
| [] => None
| c1 :: s2 =>
if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end then None
else if 0 <? l then
(if INT_MAX - cnt <? l then None
else let? (ps, r) := printf_pieces_loop fuel' s1 args (cnt + l) in Some (lit :: ps, r))
else
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
let? (ps1, cnt') := conv_pieces cnt d a in
let? (ps, r) := printf_pieces_loop fuel' s3 args' cnt' in
Some ([] :: ps1 ++ ps, r)
| _, _ => None
end
end
end
end.

Definition printf_pieces (fmt : list Z) (args : list parg) : option (list (list Z) * Z) :=
printf_pieces_loop (Datatypes.length fmt) fmt args 0.

Definition FMT_emit : list Z := [37; 100; 10; 0].
Definition FMT_usage : list Z := str "usage: %s INPUT" ++ [10; 0].
Definition FMT_too_big : list Z := str "cli: input >= %u bytes, refused" ++ [10; 0].
Definition FMT_cannot_open : list Z := str "cli: cannot open %s" ++ [10; 0].
Definition FMT_read_error : list Z := str "cli: read error on %s" ++ [10; 0].
Definition FMT_notify : list Z := str "notification: %s" ++ [10; 0].
Definition FMT_warning : list Z := str "warning: %s" ++ [10; 0].
Definition FMT_warning_int : list Z := str "warning: %s %d" ++ [10; 0].
Definition FMT_d : list Z := [37; 100; 0].
Definition A_FMT_emit : Z := 0x103e6.
Definition A_FMT_usage : Z := 0x10405.
Definition A_FMT_too_big : Z := 0x104d3.
Definition A_FMT_cannot_open : Z := 0x10546.
Definition A_FMT_read_error : Z := 0x1055b.
Definition A_FMT_notify : Z := 0x103f0.
Definition A_FMT_warning : Z := 0x106ae.
Definition A_FMT_warning_int : Z := 0x10436.

Example pieces_emit_ex0 : printf_pieces FMT_emit [PA_i 0] = Some (pieces_emit 0, 2).
Proof. vm_compute. reflexivity. Qed.
Example pieces_emit_ex1 : printf_pieces FMT_emit [PA_i 1] = Some (pieces_emit 1, 2).
Proof. vm_compute. reflexivity. Qed.
Example pieces_emit_exm : printf_pieces FMT_emit [PA_i (-2147483648)] = Some (pieces_emit (-2147483648), 12).
Proof. vm_compute. reflexivity. Qed.
Example pieces_usage_ex : printf_pieces FMT_usage [PA_s (str "prog")] = Some (pieces_usage (str "prog"), 18).
Proof. vm_compute. reflexivity. Qed.
Example pieces_cannot_open_ex : printf_pieces FMT_cannot_open [PA_s (str "f")] = Some (pieces_cannot_open (str "f"), 19).
Proof. vm_compute. reflexivity. Qed.
Example pieces_read_error_ex : printf_pieces FMT_read_error [PA_s (str "f")] = Some (pieces_read_error (str "f"), 21).
Proof. vm_compute. reflexivity. Qed.
Example pieces_too_big_ex : printf_pieces FMT_too_big [PA_u 67108864] = Some (pieces_too_big, 38).
Proof. vm_compute. reflexivity. Qed.
Example pieces_notify_ex : printf_pieces FMT_notify [PA_s (str "xy")] = Some (pieces_notify (str "xy"), 17).
Proof. vm_compute. reflexivity. Qed.
Example pieces_warning_ex : printf_pieces FMT_warning [PA_s (str "xy")] = Some (pieces_warning (str "xy"), 12).
Proof. vm_compute. reflexivity. Qed.
Example pieces_warning_int_ex0 : printf_pieces FMT_warning_int [PA_s (str "xy"); PA_i 0] = Some (pieces_warning_int (str "xy") 0, 14).
Proof. vm_compute. reflexivity. Qed.
Example pieces_warning_int_ex1 : printf_pieces FMT_warning_int [PA_s (str "xy"); PA_i (-305)] = Some (pieces_warning_int (str "xy") (-305), 17).
Proof. vm_compute. reflexivity. Qed.
Example pieces_d_ex1 : printf_pieces FMT_d [PA_i (-2147483648)] = Some ([[]; [45]; str "2147483648"], 11).
Proof. vm_compute. reflexivity. Qed.
Example pieces_d_ex2 : printf_pieces FMT_d [PA_i 0] = Some ([[]; []; [48]; []], 1).
Proof. vm_compute. reflexivity. Qed.
Example pass1_ok_ex : map pass1_ok [FMT_emit; FMT_usage; FMT_too_big; FMT_cannot_open; FMT_read_error; FMT_notify; FMT_warning; FMT_warning_int; FMT_d]
= repeat true 9.
Proof. vm_compute. reflexivity. Qed.
Example fp_calls_ex : map (fun f => fp_calls (Datatypes.length f) f [PA_s (str "xy"); PA_i 5])
[FMT_usage; FMT_too_big; FMT_cannot_open; FMT_read_error; FMT_notify; FMT_warning; FMT_warning_int]
= repeat [] 7.
Proof. vm_compute. reflexivity. Qed.

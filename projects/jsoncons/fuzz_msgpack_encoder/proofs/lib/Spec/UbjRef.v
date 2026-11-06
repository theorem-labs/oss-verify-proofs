(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition blen (p : list Z) : Z := Z.of_nat (length p).
Definition bat (p : list Z) (i : Z) : Z := nth (Z.to_nat i) p 0.
Definition slice (p : list Z) (i n : Z) : list Z := firstn (Z.to_nat n) (skipn (Z.to_nat i) p).
Fixpoint be_val (l : list Z) (acc : Z) : Z := match l with [] => acc | b :: t => be_val t (acc * 256 + b) end.
(* [comment removed for export] *)
Definition rd_be (p : list Z) (i k : Z) : Z := be_val (slice p i k) 0.
Definition sgn (k v : Z) : Z := if v <? 2 ^ (8 * k - 1) then v else v - 2 ^ (8 * k).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition utf8_trail (b : Z) : Z :=
  if b <? 192 then 0 else if b <? 224 then 1 else if b <? 240 then 2 else if b <? 248 then 3 else if b <? 252 then 4 else 5.
Definition is_cont (b : Z) : bool := (128 <=? b) && (b <? 192).
(* [comment removed for export] *)
Definition utf8_legal (l : list Z) : bool :=
  match l with
  | [] => false
  | b0 :: _ =>
      let n := Z.of_nat (length l) in
      if 4 <? n then false
      else
        (if n =? 4 then is_cont (nth 3 l 0) else true)
        && (if 3 <=? n then is_cont (nth 2 l 0) else true)
        && (if 2 <=? n then
              let b1 := nth 1 l 0 in
              is_cont b1 &&
              (if b0 =? 224 then 160 <=? b1
               else if b0 =? 237 then b1 <=? 159
               else if b0 =? 240 then 144 <=? b1
               else if b0 =? 244 then b1 <=? 143
               else true)
            else true)
        && negb ((128 <=? b0) && (b0 <? 194))
        && (b0 <=? 244)
  end.
Fixpoint utf8_valid_f (fuel : nat) (l : list Z) : bool :=
  match l with
  | [] => true
  | b0 :: _ =>
      match fuel with
      | O => false
      | S f =>
          let n := Z.to_nat (utf8_trail b0 + 1) in
          if (length l <? n)%nat then false
          else utf8_legal (firstn n l) && utf8_valid_f f (skipn n l)
      end
  end.
Definition utf8_valid (l : list Z) : bool := utf8_valid_f (length l) l.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive pmode := Mroot | Maccept | Marray | Miarray | Mtarray | Mkey | Mval | Mtkey | Mtval | Mikey | Mival.
(* [comment removed for export] *)
Record pstate := PS { ps_mode : pmode; ps_len : Z; ps_type : Z; ps_idx : Z }.
(* [comment removed for export] *)
Record eitem := EI { ei_kind : Z; ei_len : Z; ei_cnt : Z }.
Definition ei_indef (e : eitem) : bool := (ei_kind e =? 1) || (ei_kind e =? 3).

Record st := ST {
  s_stk : list pstate;    (* [comment removed for export] *)
  s_pos : Z;              (* [comment removed for export] *)
  s_more : bool;          (* [comment removed for export] *)
  s_done : bool;          (* [comment removed for export] *)
  s_halt : bool;          (* [comment removed for export] *)
  s_depth : Z;            (* [comment removed for export] *)
  s_ec : bool;            (* [comment removed for export] *)
  s_estk : list eitem;    (* [comment removed for export] *)
  s_edepth : Z;           (* [comment removed for export] *)
  s_lo : Z; s_hi : Z;     (* [comment removed for export] *)
  s_bad : bool            (* [comment removed for export] *)
}.

Definition w_stk v s := ST v (s_pos s) (s_more s) (s_done s) (s_halt s) (s_depth s) (s_ec s) (s_estk s) (s_edepth s) (s_lo s) (s_hi s) (s_bad s).
Definition w_pos v s := ST (s_stk s) v (s_more s) (s_done s) (s_halt s) (s_depth s) (s_ec s) (s_estk s) (s_edepth s) (s_lo s) (s_hi s) (s_bad s).
Definition w_more v s := ST (s_stk s) (s_pos s) v (s_done s) (s_halt s) (s_depth s) (s_ec s) (s_estk s) (s_edepth s) (s_lo s) (s_hi s) (s_bad s).
Definition w_done v s := ST (s_stk s) (s_pos s) (s_more s) v (s_halt s) (s_depth s) (s_ec s) (s_estk s) (s_edepth s) (s_lo s) (s_hi s) (s_bad s).
Definition w_halt v s := ST (s_stk s) (s_pos s) (s_more s) (s_done s) v (s_depth s) (s_ec s) (s_estk s) (s_edepth s) (s_lo s) (s_hi s) (s_bad s).
Definition w_depth v s := ST (s_stk s) (s_pos s) (s_more s) (s_done s) (s_halt s) v (s_ec s) (s_estk s) (s_edepth s) (s_lo s) (s_hi s) (s_bad s).
Definition w_ec v s := ST (s_stk s) (s_pos s) (s_more s) (s_done s) (s_halt s) (s_depth s) v (s_estk s) (s_edepth s) (s_lo s) (s_hi s) (s_bad s).
Definition w_estk v s := ST (s_stk s) (s_pos s) (s_more s) (s_done s) (s_halt s) (s_depth s) (s_ec s) v (s_edepth s) (s_lo s) (s_hi s) (s_bad s).
Definition w_edepth v s := ST (s_stk s) (s_pos s) (s_more s) (s_done s) (s_halt s) (s_depth s) (s_ec s) (s_estk s) v (s_lo s) (s_hi s) (s_bad s).
Definition w_out lo hi s := ST (s_stk s) (s_pos s) (s_more s) (s_done s) (s_halt s) (s_depth s) (s_ec s) (s_estk s) (s_edepth s) (s_lo s + lo) (s_hi s + hi) (s_bad s).
Definition w_bad s := ST (s_stk s) (s_pos s) (s_more s) (s_done s) (s_halt s) (s_depth s) (s_ec s) (s_estk s) (s_edepth s) (s_lo s) (s_hi s) true.

Definition MAX_ITEMS : Z := 16777216.   (* [comment removed for export] *)
Definition MAX_DEPTH : Z := 1024.

Definition init : st := ST [PS Mroot 0 0 0] 0 true false false 0 false [] 0 0 0 false.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pl_size (n : Z) : Z := if n <=? 255 then 2 else if n <=? 32767 then 3 else if n <=? 2147483647 then 5 else 9.
Definition INT64_MAX : Z := 9223372036854775807.
Definition e_put_length (n : Z) (s : st) : st :=
  if INT64_MAX <? n then w_bad s else w_out (pl_size n) (pl_size n) s.
(* [comment removed for export] *)
Definition TWO64 : Z := 18446744073709551616.
Definition e_end_value (s : st) : st :=
  match s_estk s with
  | [] => s
  | e :: r => w_estk (EI (ei_kind e) (ei_len e) ((ei_cnt e + 1) mod TWO64) :: r) s
  end.
(* [comment removed for export] *)
Definition e_scalar (lo hi : Z) (s : st) : st := e_end_value (w_out lo hi s).
(* [comment removed for export] *)
Definition e_begin_indef (kind : Z) (s : st) : st :=
  let s := w_edepth (s_edepth s + 1) s in
  if MAX_DEPTH <? s_edepth s then w_ec true s
  else w_out 1 1 (w_estk (EI kind 0 0 :: s_estk s) s).
(* [comment removed for export] *)
Definition e_begin_len (kind n : Z) (s : st) : st :=
  let s := w_edepth (s_edepth s + 1) s in
  if MAX_DEPTH <? s_edepth s then w_ec true s
  else e_put_length n (w_out 2 2 (w_estk (EI kind n 0 :: s_estk s) s)).
(* [comment removed for export] *)
Definition e_end (s : st) : st :=
  match s_estk s with
  | [] => w_bad s
  | e :: r =>
      let s := w_edepth (s_edepth s - 1) s in
      if ei_indef e then e_end_value (w_estk r (w_out 1 1 s))
      else if ei_cnt e <? ei_len e then w_ec true s
      else if ei_len e <? ei_cnt e then w_ec true s
      else e_end_value (w_estk r s)
  end.
(* [comment removed for export] *)
Definition e_key (n : Z) (s : st) : st :=
  let s := e_put_length n s in w_out n n s.
(* [comment removed for export] *)
Definition e_string (valid : bool) (n : Z) (s : st) : st :=
  let s := w_out 1 1 s in
  if valid then e_end_value (w_out n n (e_put_length n s)) else w_ec true s.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition r_fail (s : st) : st := w_more false (w_ec true s).
Definition top_upd (f : pstate -> pstate) (s : st) : st :=
  match s_stk s with [] => s | t :: r => w_stk (f t :: r) s end.
Definition ps_inc (t : pstate) : pstate := PS (ps_mode t) (ps_len t) (ps_type t) (ps_idx t + 1).
Definition ps_mode_set (m : pmode) (t : pstate) : pstate := PS m (ps_len t) (ps_type t) (ps_idx t).

(* [comment removed for export] *)
Definition int_width (t : Z) : Z :=
  if t =? 105 then 1 else if t =? 85 then 1 else if t =? 73 then 2 else if t =? 108 then 4 else if t =? 76 then 8 else 0.
Definition get_length (p : list Z) (pos : Z) : option (Z * Z) :=
  if blen p <=? pos then None
  else
    let t := bat p pos in
    let k := int_width t in
    if k =? 0 then None
    else if blen p <? pos + 1 + k then None
    else
      let v := if t =? 85 then rd_be p (pos + 1) k else sgn k (rd_be p (pos + 1) k) in
      if v <? 0 then None else Some (v, pos + 1 + k).

(* [comment removed for export] *)
Definition r_key (p : list Z) (s : st) : st :=
  match get_length p (s_pos s) with
  | None => r_fail s
  | Some (n, pos1) =>
      if s_ec s then r_fail (w_pos pos1 s)                 (* [comment removed for export] *)
      else if blen p <? pos1 + n then r_fail s
      else if utf8_valid (slice p pos1 n) then w_more true (e_key n (w_pos (pos1 + n) s))
      else r_fail s
  end.

(* [comment removed for export] *)
Definition r_num (p : list Z) (k lo hi : Z) (s : st) : st :=
  if blen p <? s_pos s + k then r_fail s
  else w_more true (e_scalar lo hi (w_pos (s_pos s + k) s)).

(* [comment removed for export] *)
Definition r_counted (p : list Z) (mode : pmode) (ty kind : Z) (s : st) : st :=
  match get_length p (s_pos s) with
  | None => r_fail s
  | Some (n, pos1) =>
      if s_ec s then w_pos pos1 s                          (* [comment removed for export] *)
      else if MAX_ITEMS <? n then r_fail s
      else w_more true (e_begin_len kind n (w_stk (PS mode n ty 0 :: s_stk s) (w_pos pos1 s)))
  end.

(* [comment removed for export] *)
Definition r_begin (p : list Z) (obj : bool) (s : st) : st :=
  let s := w_depth (s_depth s + 1) s in
  if MAX_DEPTH <? s_depth s then r_fail s
  else if blen p <=? s_pos s then r_fail s
  else
    let c := bat p (s_pos s) in
    if c =? 36 then                                   (* [comment removed for export] *)
      if blen p <=? s_pos s + 1 then r_fail s           (* [comment removed for export] *)
      else if blen p <=? s_pos s + 2 then r_fail s      (* [comment removed for export] *)
      else if bat p (s_pos s + 2) =? 35 then
        r_counted p (if obj then Mtkey else Mtarray) (bat p (s_pos s + 1)) (if obj then 0 else 2) (w_pos (s_pos s + 3) s)
      else r_fail s                                   (* [comment removed for export] *)
    else if c =? 35 then                              (* [comment removed for export] *)
      r_counted p (if obj then Mkey else Marray) 0 (if obj then 0 else 2) (w_pos (s_pos s + 1) s)
    else
      w_more true (e_begin_indef (if obj then 1 else 3) (w_stk (PS (if obj then Mikey else Miarray) 0 0 0 :: s_stk s) s)).

(* [comment removed for export] *)
Definition r_end (s : st) : st :=
  let s := w_depth (s_depth s - 1) s in
  let s := w_more true (e_end s) in
  w_stk (tl (s_stk s)) s.

(* [comment removed for export] *)
Definition r_value (p : list Z) (t : Z) (s : st) : st :=
  let fin (s : st) : st := if s_ec s then w_more false s else s in   (* [comment removed for export] *)
  if (t =? 90) || (t =? 84) || (t =? 70) then fin (w_more true (e_scalar 1 1 s))        (* [comment removed for export] *)
  else if t =? 78 then fin s                                                          (* [comment removed for export] *)
  else if t =? 105 then (let s' := r_num p 1 2 2 s in if s_more s' then fin s' else s')   (* [comment removed for export] *)
  else if t =? 85 then (let s' := r_num p 1 2 2 s in if s_more s' then fin s' else s')    (* [comment removed for export] *)
  else if t =? 73 then (let s' := r_num p 2 2 3 s in if s_more s' then fin s' else s')    (* [comment removed for export] *)
  else if t =? 108 then (let s' := r_num p 4 2 5 s in if s_more s' then fin s' else s')   (* [comment removed for export] *)
  else if t =? 76 then (let s' := r_num p 8 2 9 s in if s_more s' then fin s' else s')    (* [comment removed for export] *)
  else if t =? 100 then (let s' := r_num p 4 5 9 s in if s_more s' then fin s' else s')   (* [comment removed for export] *)
  else if t =? 68 then (let s' := r_num p 8 5 9 s in if s_more s' then fin s' else s')    (* [comment removed for export] *)
  else if t =? 67 then                                                                 (* [comment removed for export] *)
    if blen p <? s_pos s + 1 then r_fail s
    else if utf8_valid (slice p (s_pos s) 1) then fin (w_more true (e_string true 1 (w_pos (s_pos s + 1) s)))
    else r_fail (w_pos (s_pos s + 1) s)
  else if (t =? 83) || (t =? 72) then                                                  (* [comment removed for export] *)
    match get_length p (s_pos s) with
    | None => r_fail s
    | Some (n, pos1) =>
        if s_ec s then w_pos pos1 s                        (* [comment removed for export] *)
        else if blen p <? pos1 + n then r_fail s
        else
          let v := utf8_valid (slice p pos1 n) in
          if (t =? 83) && negb v then r_fail s
          else fin (w_more true (e_string v n (w_pos (pos1 + n) s)))
    end
  else if t =? 91 then fin (r_begin p false s)                                        (* [comment removed for export] *)
  else if t =? 123 then fin (r_begin p true s)                                        (* [comment removed for export] *)
  else fin (w_ec true s).                                                             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition r_tv (p : list Z) (s : st) : st :=
  if blen p <=? s_pos s then r_fail s
  else r_value p (bat p (s_pos s)) (w_pos (s_pos s + 1) s).

(* [comment removed for export] *)
Definition ret_if_ec (s : st) : st := if s_ec s then w_halt true s else s.

Definition halted (s : st) : bool := s_halt s || s_done s || negb (s_more s).

(* [comment removed for export] *)
Definition step (p : list Z) (s : st) : st :=
  if halted s then w_halt true s
  else
    match s_stk s with
    | [] => w_bad s                                    (* [comment removed for export] *)
    | t :: _ =>
        match ps_mode t with
        | Marray =>
            if ps_idx t <? ps_len t then ret_if_ec (r_tv p (top_upd ps_inc s)) else r_end s
        | Mtarray =>
            if ps_idx t <? ps_len t then ret_if_ec (r_value p (ps_type t) (top_upd ps_inc s)) else r_end s
        | Miarray =>
            if blen p <=? s_pos s then w_halt true (r_fail s)
            else if bat p (s_pos s) =? 93 then ret_if_ec (r_end (w_pos (s_pos s + 1) s))
            else if MAX_ITEMS <? ps_idx t + 1 then w_halt true (r_fail (top_upd ps_inc s))
            else ret_if_ec (r_tv p (top_upd ps_inc s))
        | Mkey =>
            if ps_idx t <? ps_len t then
              let s' := r_key p (top_upd ps_inc s) in
              if s_ec s' then w_halt true s' else top_upd (ps_mode_set Mval) s'
            else r_end s
        | Mval => ret_if_ec (r_tv p (top_upd (ps_mode_set Mkey) s))
        | Mtkey =>
            if ps_idx t <? ps_len t then
              let s' := r_key p (top_upd ps_inc s) in
              if s_ec s' then w_halt true s' else top_upd (ps_mode_set Mtval) s'
            else r_end s
        | Mtval => ret_if_ec (r_value p (ps_type t) (top_upd (ps_mode_set Mtkey) s))
        | Mikey =>
            if blen p <=? s_pos s then w_halt true (r_fail s)
            else if bat p (s_pos s) =? 125 then ret_if_ec (r_end (w_pos (s_pos s + 1) s))
            else if MAX_ITEMS <? ps_idx t + 1 then w_halt true (r_fail (top_upd ps_inc s))
            else
              let s' := r_key p (top_upd ps_inc s) in
              if s_ec s' then w_halt true s' else top_upd (ps_mode_set Mival) s'
        | Mival => ret_if_ec (r_tv p (top_upd (ps_mode_set Mikey) s))
        | Mroot => ret_if_ec (r_tv p (top_upd (ps_mode_set Maccept) s))
        | Maccept =>
            match s_stk s with
            | [_] => w_done true (w_more false (w_stk [] s))
            | _ => w_bad s                              (* [comment removed for export] *)
            end
        end
    end.

Fixpoint run (n : nat) (p : list Z) (s : st) : st :=
  match n with O => s | S k => run k p (step p s) end.

(* [comment removed for export] *)
Definition summary (n : nat) (p : list Z) : bool * bool * Z * Z * Z * bool :=
  let s := run n p init in (halted s, s_ec s, s_pos s, s_lo s, s_hi s, s_bad s).

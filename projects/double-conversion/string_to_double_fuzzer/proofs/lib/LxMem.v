(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LXS.
Open Scope Z_scope.

Module LXM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive tkind := TFresh | THull (lo hi : Z) | TAffine (c0 c1 : Z).
Record tfield := TF { tf_off : Z; tf_w : Z; tf_sx : bool; tf_kind : tkind }.
Record table := TB { tb_base : Z; tb_stride : Z; tb_count : Z; tb_fields : list tfield }.

Record uenv := UEnv {
  ue_segs : list Segment;
  ue_fr   : Z;
  ue_ro   : list (Z * Z);      (* [comment removed for export] *)
  ue_rw   : list (Z * Z);
  ue_nmax : Z;
  ue_tabs : list table;
  ue_cbd_pc : Z;               (* [comment removed for export] *)
  ue_cbd_fr : Z;               (* [comment removed for export] *)
  ue_scells : list (Z * sym)   (* [comment removed for export] *)
}.

Fixpoint scell_find (cs : list (Z * sym)) (a : Z) : option sym :=
  match cs with
  | [] => None
  | (b, x) :: r => if Z.eqb a b then Some x else scell_find r a
  end.

Definition in_ranges (a w : Z) (rs : list (Z * Z)) : bool :=
  existsb (fun r => (Z.leb (fst r) a &&& Z.leb (a + w) (snd r))%bool) rs.

(* [comment removed for export] *)
Definition img_byte (U : uenv) (a : Z) : option Z :=
  match memory_read (ue_segs U) (Z_to_bv 64 a) 1%N with
  | Some (b :: _) => Some (bv_unsigned b)
  | _ => None
  end.
Fixpoint img_bytes (U : uenv) (a : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match img_byte U a, img_bytes U (a + 1) n' with
            | Some b, Some r => Some (b :: r)
            | _, _ => None
            end
  end.
Fixpoint le_of_bytes (bs : list Z) : Z :=
  match bs with [] => 0 | b :: r => b + 256 * le_of_bytes r end.

(* [comment removed for export] *)
Definition ext_lit (sx : bool) (w : Z) (z : Z) : Z :=
  let u := z mod 2 ^ (8 * w) in
  if sx then (if Z.leb (2 ^ (8 * w - 1)) u then u - 2 ^ (8 * w) else u) else u.

(* [comment removed for export] *)
Definition load_from_cell (st : astate) (v : aval) (cw i w : Z) (sx : bool) : (aval * astate) :=
  match v with
  | LV l =>
      match is_const l with
      | Some z => (alit (ext_lit sx w (zbytes z i w)), st)
      | None =>
          if (Z.eqb i 0)%bool then
            if Z.eqb w 8 then (LV l, st)
            else if (Z.eqb cw w ||| Z.ltb w cw)%bool then
              (* [comment removed for export] *)
              let C := s_ctx st in
              if sx then (if in_range C l (- 2 ^ (8 * w - 1)) (2 ^ (8 * w - 1)) then (LV l, st)
                          else fresh_val st (Itv (Some (- 2 ^ (8 * w - 1))) (Some (2 ^ (8 * w - 1) - 1))))
              else (if in_range C l 0 (2 ^ (8 * w)) then (LV l, st)
                    else fresh_val st (Itv (Some 0) (Some (2 ^ (8 * w) - 1))))
            else fresh_val st (if sx then Itv (Some (- 2 ^ (8 * w - 1))) (Some (2 ^ (8 * w - 1) - 1)) else Itv (Some 0) (Some (2 ^ (8 * w) - 1)))
          else fresh_val st (if sx then Itv (Some (- 2 ^ (8 * w - 1))) (Some (2 ^ (8 * w - 1) - 1)) else Itv (Some 0) (Some (2 ^ (8 * w) - 1)))
      end
  | _ => fresh_val st (if sx then Itv (Some (- 2 ^ (8 * w - 1))) (Some (2 ^ (8 * w - 1) - 1)) else Itv (Some 0) (Some (2 ^ (8 * w) - 1)))
  end.

Definition unk_itv (sx : bool) (w : Z) : itv :=
  if Z.eqb w 8 then itop
  else if sx then Itv (Some (- 2 ^ (8 * w - 1))) (Some (2 ^ (8 * w - 1) - 1)) else Itv (Some 0) (Some (2 ^ (8 * w) - 1)).

(* [comment removed for export] *)
Fixpoint cells_find_cover (cs : list cell) (off w : Z) : option cell :=
  match cs with
  | [] => None
  | c :: r => if (Z.leb (c_off c) off &&& Z.leb (off + w) (c_off c + c_w c))%bool then Some c else cells_find_cover r off w
  end.

Definition load_cells (st : astate) (cs : list cell) (off w : Z) (sx : bool) : option (aval * astate) :=
  match cells_find_cover cs off w with
  | Some c => Some (load_from_cell st (c_val c) (c_w c) (off - c_off c) w sx)
  | None => None
  end.

(* [comment removed for export] *)
Definition in_window (U : uenv) (off w : Z) : bool := (Z.leb (- ue_fr U) off &&& Z.leb (off + w) 0)%bool.

Definition arr_find (ars : list arr) (C : ctx) (off : lin) (w : Z) : option arr :=
  find (fun a => (entails C (laddc off (- ar_lo a)) None &&& entails C (laddc (lneg off) (ar_hi a - w)) None)%bool) ars.

(* [comment removed for export] *)
Definition fact_itv (f : afact) (is_first : bool) : itv :=
  if is_first then imeet (af_first f) (Itv (Some (af_blo f)) (Some (af_bhi f))) else Itv (Some (af_blo f)) (Some (af_bhi f)).
Definition lin_eq_ent (C : ctx) (a b : lin) : bool :=
  (leqb a b ||| (entails C (lsub a b) None &&& entails C (lsub b a) None))%bool.

Definition load_stack_lit (U : uenv) (st : astate) (off w : Z) (sx : bool) : option (aval * astate) :=
  if negb (in_window U off w) then None else
  match load_cells st (s_stk st) off w sx with
  | Some r => Some r
  | None =>
      if cells_any_overlap (s_stk st) off w then
        (* [comment removed for export] *)
        Some (fresh_val st (unk_itv sx w))
      else
        (* [comment removed for export] *)
        match arr_find (s_arrs st) (s_ctx st) (lconst off) w with
        | Some a =>
            match ar_fact a, Z.eqb w 1 with
            | Some f, true =>
                if entails (s_ctx st) (laddc (lsub (af_len f) (lconst off)) (ar_lo a - 1)) None  (* [comment removed for export] *)
                then Some (fresh_val st (fact_itv f (Z.eqb off (ar_lo a))))  (* [comment removed for export] *)
                else Some (fresh_val st (unk_itv sx w))
            | _, _ => Some (fresh_val st (unk_itv sx w))
            end
        | None => Some (fresh_val st (unk_itv sx w))
        end
  end.

Definition load_stack_sym (U : uenv) (st : astate) (off : lin) (w : Z) (sx : bool) : option (aval * astate) :=
  match arr_find (s_arrs st) (s_ctx st) off w with
  | Some a =>
      if negb (in_window U (ar_lo a) (ar_hi a - ar_lo a)) then None else
      match ar_fact a, Z.eqb w 1 with
      | Some f, true =>
          (* [comment removed for export] *)
          if entails (s_ctx st) (laddc (lsub (af_len f) off) (ar_lo a - 1)) None
          then Some (fresh_val st (fact_itv f (lin_eq_ent (s_ctx st) off (lconst (ar_lo a)))))
          else Some (fresh_val st (unk_itv sx w))
      | _, _ => Some (fresh_val st (unk_itv sx w))
      end
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint pcache_find (pc : list (lin * Z * sym)) (off : lin) (sx : Z) : option sym :=
  match pc with
  | [] => None
  | (o, s, x) :: r => if (leqb o off &&& Z.eqb s sx)%bool then Some x else pcache_find r off sx
  end.
Fixpoint pay_find (C : ctx) (ps : list (lin * itv)) (off : lin) : option itv :=
  match ps with
  | [] => None
  | (o, i) :: r => if lin_eq_ent C o off then Some i else pay_find C r off
  end.
(* [comment removed for export] *)
Fixpoint pay_split (C : ctx) (ps : list (lin * itv)) (off : lin) : option lin :=
  match ps with
  | [] => None
  | (p, _) :: r => if (entails C (lsub p off) None &&& negb (entails C (laddc (lsub p off) (-1)) None))%bool
                   then Some p else pay_split C r off
  end.
Definition itv_meet_byte (sx : bool) (i : itv) : itv :=
  if sx then (match ilo i, ihi i with
              | Some lo, Some hi => if (Z.leb 0 lo &&& Z.leb hi 127)%bool then i else Itv (Some (-128)) (Some 127)
              | _, _ => Itv (Some (-128)) (Some 127) end)
  else imeet i (Itv (Some 0) (Some 255)).

Inductive lpres := LPOk (v : aval) (st : astate) | LPSplit (off p : lin) | LPFail.

Definition load_pay (U : uenv) (st : astate) (off : lin) (w : Z) (sx : bool) : lpres :=
  if negb (Z.eqb w 1) then LPFail else
  let C := s_ctx st in
  if negb (entails C off None &&& entails C (laddc (lsub (lvar SYM_N) off) (-1)) None)%bool then LPFail   (* [comment removed for export] *)
  else
    let sxz := (if sx then 1 else 0) in
    match pcache_find (s_pcache st) off sxz with
    | Some x => LPOk (LV (lvar x)) st
    | None =>
        match pay_find C (s_pay st) off with
        | Some i =>
            let (x, st1) := fresh st (itv_meet_byte sx i) in
            LPOk (LV (lvar x)) (set_pcache st1 ((off, sxz, x) :: s_pcache st1))
        | None =>
            match pay_split C (s_pay st) off with
            | Some p => LPSplit off p
            | None =>
                let (x, st1) := fresh st (if sx then Itv (Some (-128)) (Some 127) else Itv (Some 0) (Some 255)) in
                LPOk (LV (lvar x)) (set_pcache st1 ((off, sxz, x) :: s_pcache st1))
            end
        end
    end.

(* [comment removed for export] *)
Fixpoint bm_get (bm : list (Z * Z)) (a : Z) : option Z :=
  match bm with
  | [] => None
  | (x, b) :: r => if Z.ltb a x then None else if Z.eqb a x then Some b else bm_get r a
  end.
Fixpoint bm_set (bm : list (Z * Z)) (a b : Z) : list (Z * Z) :=
  match bm with
  | [] => [(a, b)]
  | (x, y) :: r => if Z.ltb a x then (a, b) :: bm else if Z.eqb a x then (a, b) :: r else (x, y) :: bm_set r a b
  end.
Fixpoint bm_set_bytes (bm : list (Z * Z)) (a : Z) (z : Z) (n : nat) : list (Z * Z) :=
  match n with
  | O => bm
  | S n' => bm_set_bytes (bm_set bm a (z mod 256)) (a + 1) (z / 256) n'
  end.
(* [comment removed for export] *)
Fixpoint abs_bytes (U : uenv) (bm : list (Z * Z)) (a : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' =>
      match (match bm_get bm a with Some b => Some b | None => img_byte U a end), abs_bytes U bm (a + 1) n' with
      | Some b, Some r => Some (b :: r)
      | _, _ => None
      end
  end.

(* [comment removed for export] *)
Definition load_abs (U : uenv) (st : astate) (a w : Z) (sx : bool) : option (aval * astate) :=
  match scell_find (ue_scells U) a with
  | Some x => if (Z.eqb w 8 &&& Nat.ltb x (s_next st))%bool then Some (LV (lvar x), st) else None   (* [comment removed for export] *)
  | None =>
  if in_ranges a w (ue_rw U) then
    match abs_bytes U (s_abs st) a (Z.to_nat w) with
    | Some bs => Some (alit (ext_lit sx w (le_of_bytes bs)), st)
    | None => None
    end
  else if in_ranges a w (ue_ro U) then
    match img_bytes U a (Z.to_nat w) with
    | Some bs => Some (alit (ext_lit sx w (le_of_bytes bs)), st)
    | None => None
    end
  else None
  end.

(* [comment removed for export] *)
Definition field_val (U : uenv) (a w : Z) (sx : bool) : option Z :=
  match img_bytes U a (Z.to_nat w) with Some bs => Some (ext_lit sx w (le_of_bytes bs)) | None => None end.
Fixpoint rows_ok (U : uenv) (t : table) (f : tfield) (i : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      (match field_val U (tb_base t + tb_stride t * i + tf_off f) (tf_w f) (tf_sx f), tf_kind f with
       | Some _, TFresh => true
       | Some v, THull lo hi => (Z.leb lo v &&& Z.leb v hi)%bool
       | Some v, TAffine c0 c1 => Z.eqb v (c0 + c1 * i)
       | None, _ => false
       end) &&& rows_ok U t f (i + 1) n'
  end.
Definition table_validb (U : uenv) (t : table) : bool :=
  (Z.ltb 0 (tb_stride t) &&& Z.ltb 0 (tb_count t)
   &&& in_ranges (tb_base t) (tb_stride t * tb_count t) (ue_ro U)
   &&& forallb (fun f => Z.ltb 0 (tf_w f) &&& Z.leb (tf_w f) 8 &&& Z.leb 0 (tf_off f) &&& Z.leb (tf_off f + tf_w f) (tb_stride t)
                        &&& rows_ok U t f 0 (Z.to_nat (tb_count t))) (tb_fields t))%bool.
Definition tables_validb (U : uenv) : bool := forallb (table_validb U) (ue_tabs U).

Fixpoint find_field (U : uenv) (st : astate) (t : table) (fs : list tfield) (l : lin) (w : Z) (sx : bool) : option (aval * astate) :=
  match fs with
  | [] => None
  | f :: r =>
      let here :=
        if (Z.eqb (tf_w f) w &&& (match tf_kind f with TFresh => true | _ => Bool.eqb (tf_sx f) sx end))%bool then
          let rr := laddc l (- (tb_base t + tf_off f)) in
          if ldivisible rr (tb_stride t) then
            let idx := ldiv rr (tb_stride t) in
            let C := s_ctx st in
            if (entails C idx None &&& entails C (laddc (lneg idx) (tb_count t - 1)) None)%bool then
              Some (match tf_kind f with
                    | TFresh => fresh_val st (unk_itv sx w)
                    | THull lo hi => fresh_val st (Itv (Some lo) (Some hi))
                    | TAffine c0 c1 => (LV (laddc (lscale c1 idx) c0), st)
                    end)
            else None
          else None
        else None in
      match here with Some r => Some r | None => find_field U st t r l w sx end
  end.
Fixpoint find_table (U : uenv) (st : astate) (ts : list table) (l : lin) (w : Z) (sx : bool) : option (aval * astate) :=
  match ts with
  | [] => None
  | t :: r => match find_field U st t (tb_fields t) l w sx with Some x => Some x | None => find_table U st r l w sx end
  end.
Definition load_table (U : uenv) (st : astate) (l : lin) (w : Z) (sx : bool) : option (aval * astate) :=
  find_table U st (ue_tabs U) l w sx.

(* [comment removed for export] *)
Inductive ldres := LDOk (v : aval) (st : astate) | LDSplit (off p : lin) | LDFail.
Definition do_load (U : uenv) (st : astate) (av : aval) (w : Z) (sx : bool) : ldres :=
  match classify av with
  | Some (AStk off) => match load_stack_lit U st off w sx with Some (v, st') => LDOk v st' | None => LDFail end
  | Some (AStkSym off) => match load_stack_sym U st off w sx with Some (v, st') => LDOk v st' | None => LDFail end
  | Some (APay off) => match load_pay U st off w sx with LPOk v st' => LDOk v st' | LPSplit o p => LDSplit o p | LPFail => LDFail end
  | Some (AAbs a) => match load_abs U st a w sx with Some (v, st') => LDOk v st' | None => LDFail end
  | None =>
      match av with
      | LV l => match load_table U st l w sx with Some (v, st') => LDOk v st' | None => LDFail end
      | _ => LDFail
      end
  end.

(* [comment removed for export] *)
Definition aval_in (C : ctx) (v : aval) (lo hi : Z) : bool :=   (* [comment removed for export] *)
  match v with
  | LV l => (entails C (laddc l (- lo)) None &&& entails C (laddc (lneg l) hi) None)%bool
  | _ => false
  end.

(* [comment removed for export] *)
Definition ijoin_if (b : bool) (i j : itv) : itv := if b then ijoin i j else j.

Fixpoint arrs_touch (ars : list arr) (C : ctx) (off : lin) (w : Z) (v : aval) : option (list arr) :=
  (* [comment removed for export] *)
  match ars with
  | [] => None
  | a :: r =>
      if (entails C (laddc off (- ar_lo a)) None &&& entails C (laddc (lneg off) (ar_hi a - w)) None)%bool then
        let a' :=
          match ar_fact a with
          | None => a
          | Some f =>
              if negb (Z.eqb w 1) then Arr (ar_lo a) (ar_hi a) None
              else if aval_in C v (af_blo f) (af_bhi f) then
                (* [comment removed for export] *)
                if lin_eq_ent C off (laddc (af_len f) (ar_lo a)) then
                  (* [comment removed for export] *)
                  let first' := if entails C (laddc (af_len f) (-1)) None then af_first f
                                else match v with LV l => ijoin_if (negb (leqb (af_len f) (lconst 0))) (af_first f) (lrange C l) | _ => itop end in
                  Arr (ar_lo a) (ar_hi a) (Some (AFact (laddc (af_len f) 1) (af_blo f) (af_bhi f) first'))
                else
                  (* [comment removed for export] *)
                  if entails C (laddc off (- ar_lo a - 1)) None then a
                  else Arr (ar_lo a) (ar_hi a) (Some (AFact (af_len f) (af_blo f) (af_bhi f)
                                                    (match v with LV l => ijoin (af_first f) (lrange C l) | _ => itop end)))
              else
                (* [comment removed for export] *)
                if entails C (lsub (laddc off (- ar_lo a)) (af_len f)) None then a else Arr (ar_lo a) (ar_hi a) None
          end in
        Some (a' :: r)
      else match arrs_touch r C off w v with Some r' => Some (a :: r') | None => None end
  end.

Definition arrs_overlap_lit (ars : list arr) (off w : Z) : bool :=
  existsb (fun a => overlaps (ar_lo a) (ar_hi a - ar_lo a) off w) ars.

Definition store_stack_lit (U : uenv) (st : astate) (off w : Z) (v : aval) : option astate :=
  if negb (in_window U off w) then None else
  if arrs_overlap_lit (s_arrs st) off w then
    (* [comment removed for export] *)
    match arrs_touch (s_arrs st) (s_ctx st) (lconst off) w v with
    | Some ars' => Some (set_arrs (set_stk st (cells_kill (s_stk st) off w)) ars')
    | None => None
    end
  else Some (set_stk st (cells_store (s_stk st) off w v)).

Definition store_stack_sym (U : uenv) (st : astate) (off : lin) (w : Z) (v : aval) : option astate :=
  match arrs_touch (s_arrs st) (s_ctx st) off w v with
  | Some ars' =>
      (* [comment removed for export] *)
      match arr_find (s_arrs st) (s_ctx st) off w with
      | Some a => if in_window U (ar_lo a) (ar_hi a - ar_lo a) then Some (set_arrs st ars') else None
      | None => None
      end
  | None => None
  end.

(* [comment removed for export] *)
Definition store_abs (U : uenv) (st : astate) (a w : Z) (v : aval) : option astate :=
  if in_ranges a w (ue_rw U) then
    match aval_lit v with
    | Some z => Some (set_pay (set_pcache (set_abs st (bm_set_bytes (s_abs st) a (z mod two64z) (Z.to_nat w))) []) [])
    | None => None     (* [comment removed for export] *)
    end
  else None.

Definition do_store (U : uenv) (st : astate) (av : aval) (w : Z) (v : aval) : option astate :=
  match classify av with
  | Some (AStk off) => store_stack_lit U st off w v
  | Some (AStkSym off) => store_stack_sym U st off w v
  | Some (APay _) => None
  | Some (AAbs a) => store_abs U st a w v
  | None => None
  end.

(* [comment removed for export] *)
Definition declare_array (U : uenv) (st : astate) (lo hi : Z) : option astate :=
  if negb (in_window U lo (hi - lo)) then None else
  let stk' := cells_kill (s_stk st) lo (hi - lo) in
  let ars' := filter (fun a => negb (overlaps (ar_lo a) (ar_hi a - ar_lo a) lo (hi - lo))) (s_arrs st) in
  Some (set_arrs (set_stk st stk') (Arr lo hi (Some (AFact (lconst 0) 48 57 (Itv (Some 48) (Some 57)))) :: ars')).
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition drop_below (st : astate) (spoff : Z) : astate :=
  set_arrs (set_stk st (cells_drop_below (s_stk st) spoff))
           (filter (fun a => negb (Z.leb (ar_hi a) spoff)) (s_arrs st)).

End LXM.

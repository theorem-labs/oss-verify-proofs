(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LaState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LAS.
Open Scope Z_scope.

Module LAM.

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
  (* [comment removed for export] *)
  ue_rt   : list (Z * Z);      (* [comment removed for export] *)
  ue_gsh  : list (Z * Z);      (* [comment removed for export] *)
  ue_sp32 : Z;                 (* [comment removed for export] *)
  ue_tp   : Z;                 (* [comment removed for export] *)
  ue_malloc : list (Z * Z);    (* [comment removed for export] *)
  ue_free5 : Z;                (* [comment removed for export] *)
  ue_memset : Z;               (* [comment removed for export] *)
  ue_malloc_fr : Z;            (* [comment removed for export] *)
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
Definition ro_clear (U : uenv) (a w : Z) : bool :=
  forallb (fun r => (Z.leb (snd r) a ||| Z.leb (a + w) (fst r))%bool) (ue_ro U).

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
Definition in_win (lo hi : Z) (off w : Z) : bool := (Z.leb lo off &&& Z.leb (off + w) hi)%bool.
Definition in_window (U : uenv) (off w : Z) : bool := in_win (- ue_fr U) 0 off w.

Definition arr_find (ars : list arr) (C : ctx) (off : lin) (w : Z) : option arr :=
  find (fun a => (entails C (laddc off (- ar_lo a)) None &&& entails C (laddc (lneg off) (ar_hi a - w)) None)%bool) ars.

(* [comment removed for export] *)
Definition fact_itv (f : afact) (is_first : bool) : itv :=
  if is_first then imeet (af_first f) (Itv (Some (af_blo f)) (Some (af_bhi f))) else Itv (Some (af_blo f)) (Some (af_bhi f)).
Definition lin_eq_ent (C : ctx) (a b : lin) : bool :=
  (leqb a b ||| (entails C (lsub a b) None &&& entails C (lsub b a) None))%bool.

Definition load_space_lit (lo hi : Z) (cs : list cell) (ars : list arr) (st : astate) (off w : Z) (sx : bool) : option (aval * astate) :=
  if negb (in_win lo hi off w) then None else
  match load_cells st cs off w sx with
  | Some r => Some r
  | None =>
      if cells_any_overlap cs off w then
        (* [comment removed for export] *)
        Some (fresh_val st (unk_itv sx w))
      else
        (* [comment removed for export] *)
        match arr_find ars (s_ctx st) (lconst off) w with
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

Definition load_space_sym (lo hi : Z) (ars : list arr) (st : astate) (off : lin) (w : Z) (sx : bool) : option (aval * astate) :=
  match arr_find ars (s_ctx st) off w with
  | Some a =>
      if negb (in_win lo hi (ar_lo a) (ar_hi a - ar_lo a)) then None else
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

Definition load_stack_lit (U : uenv) (st : astate) (off w : Z) (sx : bool) : option (aval * astate) :=
  load_space_lit (- ue_fr U) 0 (s_stk st) (s_arrs st) st off w sx.
Definition load_stack_sym (U : uenv) (st : astate) (off : lin) (w : Z) (sx : bool) : option (aval * astate) :=
  load_space_sym (- ue_fr U) 0 (s_arrs st) st off w sx.
Definition load_frame_lit (st : astate) (i : nat) (off w : Z) (sx : bool) : option (aval * astate) :=
  match nth_frame (s_frames st) i with
  | Some f => load_space_lit 0 (f_size f) (f_cells f) (f_arrs f) st off w sx
  | None => None
  end.
Definition load_frame_sym (st : astate) (i : nat) (off : lin) (w : Z) (sx : bool) : option (aval * astate) :=
  match nth_frame (s_frames st) i with
  | Some f => load_space_sym 0 (f_size f) (f_arrs f) st off w sx
  | None => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint list_bytes (bs : list Z) (t : nat) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match nth_error bs t, list_bytes bs (S t) n' with
            | Some b, Some r => Some (b :: r)
            | _, _ => None
            end
  end.
(* [comment removed for export] *)
Fixpoint list_const_on (bs : list Z) (tlo : nat) (n : nat) (v : Z) : bool :=
  match n with
  | O => true
  | S n' => (match nth_error bs tlo with Some b => Z.eqb b v | None => false end &&& list_const_on bs (S tlo) n' v)%bool
  end.
(* [comment removed for export] *)
Fixpoint list_run (bs : list Z) (tlo : nat) (n : nat) (v : Z) : nat :=
  match n with
  | O => O
  | S n' => match nth_error bs tlo with
            | Some b => if Z.eqb b v then S (list_run bs (S tlo) n' v) else O
            | None => O
            end
  end.

Inductive shres := SHOk (v : aval) (st : astate) | SHSplit (l : lin) | SHFail.

(* [comment removed for export] *)
Definition load_shframe (st : astate) (i : nat) (t : lin) (w : Z) (sx : bool) : shres :=
  match nth_frame (s_frames st) i with
  | None => SHFail
  | Some f =>
      match is_const t with
      | Some c =>
          if (Z.leb 0 c &&& Z.leb (c + w) (f_shn f))%bool then
            match list_bytes (f_sh f) (Z.to_nat c) (Z.to_nat w) with
            | Some bs => SHOk (alit (ext_lit sx w (le_of_bytes bs))) st
            | None => SHFail
            end
          else SHFail
      | None =>
          if negb (Z.eqb w 1) then SHFail else
          match lrange (s_ctx st) t with
          | Itv (Some tlo) (Some thi) =>
              if (Z.leb 0 tlo &&& Z.leb tlo thi &&& Z.ltb thi (f_shn f))%bool then
                match nth_error (f_sh f) (Z.to_nat tlo) with
                | Some v =>
                    let run := list_run (f_sh f) (Z.to_nat tlo) (Z.to_nat (thi - tlo + 1)) v in
                    if Nat.eqb run (Z.to_nat (thi - tlo + 1)) then SHOk (alit (ext_lit sx 1 v)) st
                    else SHSplit (laddc (lneg t) (tlo + Z.of_nat run - 1))      (* [comment removed for export] *)
                | None => SHFail
                end
              else SHFail
          | _ => SHFail
          end
      end
  end.

(* [comment removed for export] *)
Definition ent_scales : list Z := [2; 4; 8; 16; 32; 64].
Definition ent_scaled (C : ctx) (l : lin) : bool :=
  existsb (fun f => lshare f l &&& existsb (fun k => itv_nonneg (litv (cb C) (lsub l (lscale k f)))) ent_scales) (cfacts C).
Definition entails_sc (C : ctx) (l : lin) : bool := entails C l None ||| ent_scaled C l.

(* [comment removed for export] *)
Definition load_shstack (U : uenv) (st : astate) (t : lin) (w : Z) : shres :=
  let C := s_ctx st in
  if (entails_sc C (laddc (lscale 8 t) (ue_fr U - ue_sp32 U)) &&& entails_sc C (lscale (-1) (laddc t w)))%bool
  then SHOk (alit 0) st else SHFail.

(* [comment removed for export] *)
Definition load_shpay (st : astate) (t : lin) (w : Z) : shres :=
  if negb (Z.eqb w 1) then SHFail else
  let C := s_ctx st in
  if negb (entails C t None &&& entails C (laddc (lsub (lvar SYM_N) (lscale 8 t)) (-1)) None)%bool then SHFail
  else
    let full := laddc (lsub (lvar SYM_N) (lscale 8 t)) (-8) in          (* [comment removed for export] *)
    if entails C full None then SHOk (alit 0) st
    else if entails C (laddc (lsub (lscale 8 t) (lvar SYM_N)) 7) None   (* [comment removed for export] *)
         then SHOk (LV (lsub (lvar SYM_N) (lscale 8 t))) st
    else SHSplit full.

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
Fixpoint bm_bytes (bm : list (Z * Z)) (a : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match bm_get bm a, bm_bytes bm (a + 1) n' with
            | Some b, Some r => Some (b :: r)
            | _, _ => None
            end
  end.
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
  else match bm_bytes (ue_rt U) a (Z.to_nat w) with
       | Some bs => Some (alit (ext_lit sx w (le_of_bytes bs)), st)
       | None =>
           match bm_bytes (ue_gsh U) a (Z.to_nat w) with
           | Some bs => Some (alit (ext_lit sx w (le_of_bytes bs)), st)
           | None => None
           end
       end
  end.

(* [comment removed for export] *)
Fixpoint bm_const_on (bm : list (Z * Z)) (a : Z) (n : nat) (v : Z) : bool :=
  match n with
  | O => true
  | S n' => (match bm_get bm a with Some b => Z.eqb b v | None => false end &&& bm_const_on bm (a + 1) n' v)%bool
  end.
(* [comment removed for export] *)
Definition e2_scales : list Z := [1; 2; 4; 8].
Definition e2_bounds (C : ctx) (l f : lin) (acc : itv) : itv :=
  if lshare f l then
    fold_left (fun a k => imeet a (Itv (ilo (litv (cb C) (lsub l (lscale k f)))) (ihi (litv (cb C) (ladd l (lscale k f))))))
              e2_scales acc
  else acc.
Definition lrange2 (C : ctx) (l : lin) : itv := fold_left (fun a f => e2_bounds C l f a) (cfacts C) (lrange C l).

(* [comment removed for export] *)
Fixpoint bm_run (bm : list (Z * Z)) (a : Z) (n : nat) (v : Z) : nat :=
  match n with
  | O => O
  | S n' => match bm_get bm a with Some b => if Z.eqb b v then S (bm_run bm (a + 1) n' v) else O | None => O end
  end.
(* [comment removed for export] *)
Definition load_gsh_sym (U : uenv) (st : astate) (l : lin) (w : Z) (sx : bool) : shres :=
  if negb (Z.eqb w 1) then SHFail else
  match lrange2 (s_ctx st) l with
  | Itv (Some lo) (Some hi) =>
      if (Z.leb lo hi &&& Z.leb (hi - lo) 4096)%bool then
        match bm_get (ue_gsh U) lo with
        | Some v => if bm_const_on (ue_gsh U) lo (Z.to_nat (hi - lo + 1)) v then SHOk (alit (ext_lit sx 1 v)) st
                    else SHSplit (laddc (lneg l) (lo + Z.of_nat (bm_run (ue_gsh U) lo (Z.to_nat (hi - lo + 1)) v) - 1))
        | None => SHFail
        end
      else SHFail
  | _ => SHFail
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
Fixpoint table_span_in (C : ctx) (ts : list table) (l : lin) : option (Z * Z) :=
  match ts with
  | [] => None
  | t :: rest =>
      let here :=
        if Z.ltb 0 (tb_stride t) then
          let rr := laddc l (- tb_base t) in
          let off := (lc rr) mod (tb_stride t) in
          let rr' := laddc rr (- off) in
          if ldivisible rr' (tb_stride t) then
            let idx := ldiv rr' (tb_stride t) in
            if (entails C idx None &&& entails C (laddc (lneg idx) (tb_count t - 1)) None)%bool
            then Some (tb_base t + off, tb_base t + off + tb_stride t * (tb_count t - 1)) else None
          else None
        else None in
      match here with Some sp => Some sp | None => table_span_in C rest l end
  end.
Definition table_span (U : uenv) (C : ctx) (l : lin) : option (Z * Z) := table_span_in C (ue_tabs U) l.

(* [comment removed for export] *)
Inductive ldres := LDOk (v : aval) (st : astate) | LDSplit (off p : lin) | LDSplitLin (l : lin) | LDFail.
(* [comment removed for export] *)
Definition of_sh (r : shres) : ldres :=
  match r with SHOk v st => LDOk v st | SHSplit l => LDSplitLin l | SHFail => LDFail end.
Definition do_load (U : uenv) (st : astate) (av : aval) (w : Z) (sx : bool) : ldres :=
  match classify (s_frames st) av with
  | Some (AStk off) => match load_stack_lit U st off w sx with Some (v, st') => LDOk v st' | None => LDFail end
  | Some (AStkSym off) => match load_stack_sym U st off w sx with Some (v, st') => LDOk v st' | None => LDFail end
  | Some (APay off) => match load_pay U st off w sx with LPOk v st' => LDOk v st' | LPSplit o p => LDSplit o p | LPFail => LDFail end
  | Some (AAbs a) => match load_abs U st a w sx with Some (v, st') => LDOk v st' | None => LDFail end
  | Some (AFrm i off) => match load_frame_lit st i off w sx with Some (v, st') => LDOk v st' | None => LDFail end
  | Some (AFrmSym i off) => match load_frame_sym st i off w sx with Some (v, st') => LDOk v st' | None => LDFail end
  | Some (AShFrm i t) => of_sh (load_shframe st i t w sx)
  | Some (AShStk t) => of_sh (load_shstack U st t w)
  | Some (AShPay t) => of_sh (load_shpay st t w)
  | Some (AFlag _) => LDFail
  | None =>
      match av with
      | LV l => match load_table U st l w sx with
                | Some (v, st') => LDOk v st'
                | None => match load_gsh_sym U st l w sx with
                          | SHOk v st' => LDOk v st'
                          | SHSplit l' => LDSplitLin l'
                          | SHFail => (* [comment removed for export] *)
                              of_sh (load_shstack U st (lsub (laddc l (- SHB)) (lscale 4 (lvar SYM_S32))) w)
                          end
                end
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

(* [comment removed for export] *)
Definition store_space_lit (lo hi : Z) (cs : list cell) (ars : list arr) (C : ctx) (off w : Z) (v : aval) : option (list cell * list arr) :=
  if negb (in_win lo hi off w) then None else
  if arrs_overlap_lit ars off w then
    (* [comment removed for export] *)
    match arrs_touch ars C (lconst off) w v with
    | Some ars' => Some (cells_kill cs off w, ars')
    | None => None
    end
  else Some (cells_store cs off w v, ars).

Definition store_space_sym (lo hi : Z) (cs : list cell) (ars : list arr) (C : ctx) (off : lin) (w : Z) (v : aval) : option (list cell * list arr) :=
  match arrs_touch ars C off w v with
  | Some ars' =>
      (* [comment removed for export] *)
      match arr_find ars C off w with
      | Some a => if in_win lo hi (ar_lo a) (ar_hi a - ar_lo a) then Some (cs, ars') else None
      | None => None
      end
  | None => None
  end.

Definition store_stack_lit (U : uenv) (st : astate) (off w : Z) (v : aval) : option astate :=
  match store_space_lit (- ue_fr U) 0 (s_stk st) (s_arrs st) (s_ctx st) off w v with
  | Some (cs, ars) => Some (set_arrs (set_stk st cs) ars)
  | None => None
  end.
Definition store_stack_sym (U : uenv) (st : astate) (off : lin) (w : Z) (v : aval) : option astate :=
  match store_space_sym (- ue_fr U) 0 (s_stk st) (s_arrs st) (s_ctx st) off w v with
  | Some (cs, ars) => Some (set_arrs (set_stk st cs) ars)
  | None => None
  end.
Definition frame_set_space (f : frame) (cs : list cell) (ars : list arr) : frame :=
  Frame (f_sym f) (f_cls f) cs ars (f_sh f) (f_flag f).
Definition store_frame_lit (st : astate) (i : nat) (off w : Z) (v : aval) : option astate :=
  match nth_frame (s_frames st) i with
  | Some f => match store_space_lit 0 (f_size f) (f_cells f) (f_arrs f) (s_ctx st) off w v with
              | Some (cs, ars) => Some (set_frames st (upd_frame (s_frames st) i (frame_set_space f cs ars)))
              | None => None
              end
  | None => None
  end.
Definition store_frame_sym (st : astate) (i : nat) (off : lin) (w : Z) (v : aval) : option astate :=
  match nth_frame (s_frames st) i with
  | Some f => match store_space_sym 0 (f_size f) (f_cells f) (f_arrs f) (s_ctx st) off w v with
              | Some (cs, ars) => Some (set_frames st (upd_frame (s_frames st) i (frame_set_space f cs ars)))
              | None => None
              end
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint list_set_bytes (bs : list Z) (t : nat) (z : Z) (n : nat) : list Z :=
  match n with
  | O => bs
  | S n' => list_set_bytes (list_set bs t (z mod 256)) (S t) (z / 256) n'
  end.
Definition store_shframe (st : astate) (i : nat) (t : lin) (w : Z) (v : aval) : option astate :=
  match nth_frame (s_frames st) i, is_const t, aval_lit v with
  | Some f, Some c, Some z =>
      if (Z.leb 0 c &&& Z.leb (c + w) (f_shn f))%bool then
        Some (set_frames st (upd_frame (s_frames st) i
               (Frame (f_sym f) (f_cls f) (f_cells f) (f_arrs f) (list_set_bytes (f_sh f) (Z.to_nat c) (z mod two64z) (Z.to_nat w)) (f_flag f))))
      else None
  | _, _, _ => None
  end.

(* [comment removed for export] *)
Definition store_flag (st : astate) (i : nat) (w : Z) (v : aval) : option astate :=
  match aval_lit v with
  | Some 0 => if (Z.eqb w 1 &&& Nat.eqb (S i) (length (s_frames st)))%bool then Some (set_frames st (del_frame (s_frames st) i)) else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition store_abs (U : uenv) (st : astate) (a w : Z) (v : aval) : option astate :=
  if (in_ranges a w (ue_rw U) &&& ro_clear U a w)%bool then
    match aval_lit v with
    | Some z => Some (set_pay (set_pcache (set_abs st (bm_set_bytes (s_abs st) a (z mod two64z) (Z.to_nat w))) []) [])
    | None => None     (* [comment removed for export] *)
    end
  else None.

Definition do_store (U : uenv) (st : astate) (av : aval) (w : Z) (v : aval) : option astate :=
  match classify (s_frames st) av with
  | Some (AStk off) => store_stack_lit U st off w v
  | Some (AStkSym off) => store_stack_sym U st off w v
  | Some (APay _) => None
  | Some (AAbs a) => store_abs U st a w v
  | Some (AFrm i off) => store_frame_lit st i off w v
  | Some (AFrmSym i off) => store_frame_sym st i off w v
  | Some (AShFrm i t) => store_shframe st i t w v
  | Some (AShStk _) => None
  | Some (AShPay _) => None
  | Some (AFlag i) => store_flag st i w v
  | None => None
  end.

(* [comment removed for export] *)
Definition declare_space_array (cs : list cell) (ars : list arr) (lo hi : Z) : (list cell * list arr) :=
  (cells_kill cs lo (hi - lo),
   Arr lo hi (Some (AFact (lconst 0) 48 57 (Itv (Some 48) (Some 57)))) :: filter (fun a => negb (overlaps (ar_lo a) (ar_hi a - ar_lo a) lo (hi - lo))) ars).
Definition declare_array (U : uenv) (st : astate) (lo hi : Z) : option astate :=
  if negb (in_window U lo (hi - lo)) then None else
  let (cs, ars) := declare_space_array (s_stk st) (s_arrs st) lo hi in Some (set_arrs (set_stk st cs) ars).
(* [comment removed for export] *)
Definition declare_frame_array (st : astate) (i : nat) (lo hi : Z) : option astate :=
  match nth_frame (s_frames st) i with
  | Some f => if negb (in_win 0 (f_size f) lo (hi - lo)) then None else
              let (cs, ars) := declare_space_array (f_cells f) (f_arrs f) lo hi in
              Some (set_frames st (upd_frame (s_frames st) i (frame_set_space f cs ars)))
  | None => None
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition drop_below (st : astate) (spoff : Z) : astate :=
  set_arrs (set_stk st (cells_drop_below (s_stk st) spoff))
           (filter (fun a => negb (Z.leb (ar_hi a) spoff)) (s_arrs st)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint fill_cells (cs : list cell) (off : Z) (n : nat) (c : Z) (fuel : nat) : list cell :=
  match fuel with
  | O => cs
  | S fuel' =>
      if Nat.eqb n 0 then cs else
      let w := (if Nat.leb 8 n then 8 else if Nat.leb 4 n then 4 else if Nat.leb 2 n then 2 else 1)%nat in
      let z := c * (match w with 8%nat => 0x0101010101010101 | 4%nat => 0x01010101 | 2%nat => 0x0101 | _ => 1 end) in
      fill_cells (cells_store cs off (Z.of_nat w) (alit z)) (off + Z.of_nat w) (n - w)%nat c fuel'
  end.
Definition memset_space (lo hi : Z) (cs : list cell) (ars : list arr) (off : Z) (n : Z) (c : Z) : option (list cell * list arr) :=
  if negb (in_win lo hi off n) then None else
  if arrs_overlap_lit ars off n then None
  else Some (fill_cells (cells_kill cs off n) off (Z.to_nat n) c (Z.to_nat n), ars).
Fixpoint list_fill (bs : list Z) (t : nat) (n : nat) (c : Z) : list Z :=
  match n with O => bs | S n' => list_fill (list_set bs t c) (S t) n' c end.

End LAM.


(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition u64 (x : Z) : Z := x mod 2^64.
Definition u16 (x : Z) : Z := x mod 2^16.

Definition ZSTD_error_srcSize_wrong : Z := 72.
Definition ZSTD_error_maxSymbolValue_tooLarge : Z := 46.

Definition FSE_MAX_SYMBOL_VALUE : Z := 255.

(* [comment removed for export] *)
Definition readLE64 (buf : list Z) (p : Z) : res Z :=
  if (0 <=? p) && (p + 8 <=? Zlength buf) then
    Ok (Znth p buf + 2^8 * Znth (p+1) buf + 2^16 * Znth (p+2) buf + 2^24 * Znth (p+3) buf
        + 2^32 * Znth (p+4) buf + 2^40 * Znth (p+5) buf + 2^48 * Znth (p+6) buf + 2^56 * Znth (p+7) buf)
  else Ub.

(* [comment removed for export] *)
Definition oload (l : list (option Z)) (i : Z) : res Z :=
  if (0 <=? i) && (i <? Zlength l) then
    match nth (Z.to_nat i) l None with Some v => Ok v | None => Ub end
  else Ub.
Fixpoint oupd_nat (n : nat) (v : Z) (l : list (option Z)) : list (option Z) :=
  match l, n with
  | [], _ => []
  | _ :: t, O => Some v :: t
  | h :: t, S n' => h :: oupd_nat n' v t
  end.
Definition ostore (l : list (option Z)) (i v : Z) : res (list (option Z)) :=
  if (0 <=? i) && (i <? Zlength l) then Ok (oupd_nat (Z.to_nat i) v l) else Ub.

(* [comment removed for export] *)
Definition bit_mask (nbBits : Z) : res Z :=
  if (0 <=? nbBits) && (nbBits <? 32) then Ok (2^nbBits - 1) else Ub.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive dstatus := Unfinished | EndOfBuffer | Completed | Overflow.

Definition dstatus_eqb (a b : dstatus) : bool :=
  match a, b with
  | Unfinished, Unfinished | EndOfBuffer, EndOfBuffer | Completed, Completed | Overflow, Overflow => true
  | _, _ => false
  end.

(* [comment removed for export] *)
Record bitD := mkBD {
  bd_cont : Z;        (* [comment removed for export] *)
  bd_bits : Z;        (* [comment removed for export] *)
  bd_ptr  : Z;
  bd_zero : bool
}.

Section BitStream.
  Variable src : list Z.
  Let srcSize : Z := Zlength src.

  (* [comment removed for export] *)
  Definition add_byte (k sh : Z) (acc : res Z) : res Z :=
    let! a := acc in
    if k <? srcSize then let! b := load src k in Ok (a + b * 2^sh) else Ok a.

  Definition init_dstream : res bitD :=
    if srcSize <? 1 then Err ZSTD_error_srcSize_wrong
    else if 8 <=? srcSize then
      let p := srcSize - 8 in
      let! c := readLE64 src p in
      let! lastByte := load src (srcSize - 1) in
      if lastByte =? 0 then Err ZSTD_error_GENERIC
      else let! hb := highbit32 lastByte in
           Ok (mkBD c (8 - hb) p false)
    else
      let! b0 := load src 0 in
      (* [comment removed for export] *)
      let! c := add_byte 1 8 (add_byte 2 16 (add_byte 3 24 (add_byte 4 32 (add_byte 5 40 (add_byte 6 48 (Ok b0)))))) in
      let! lastByte := load src (srcSize - 1) in
      if lastByte =? 0 then Err ZSTD_error_corruption_detected
      else let! hb := highbit32 lastByte in
           Ok (mkBD c (8 - hb + (8 - srcSize) * 8) 0 false).

  (* [comment removed for export] *)
  Definition look_bits (d : bitD) (nbBits : Z) : res Z :=
    let! m := bit_mask nbBits in
    let sh := (u32 (64 - bd_bits d - nbBits)) mod 64 in
    Ok (Z.land (Z.shiftr (bd_cont d) sh) m).

  (* [comment removed for export] *)
  Definition look_bits_fast (d : bitD) (nbBits : Z) : Z :=
    Z.shiftr (u64 (Z.shiftl (bd_cont d) ((u32 (bd_bits d)) mod 64))) ((u32 (64 - nbBits)) mod 64).

  Definition skip_bits (d : bitD) (nbBits : Z) : bitD :=
    mkBD (bd_cont d) (u32 (bd_bits d + nbBits)) (bd_ptr d) (bd_zero d).

  Definition read_bits (d : bitD) (nbBits : Z) : res (Z * bitD) :=
    let! v := look_bits d nbBits in Ok (v, skip_bits d nbBits).

  Definition read_bits_fast (d : bitD) (nbBits : Z) : Z * bitD :=
    (look_bits_fast d nbBits, skip_bits d nbBits).

  (* [comment removed for export] *)
  Definition reload_dstream (d : bitD) : res (dstatus * bitD) :=
    if 64 <? bd_bits d then Ok (Overflow, mkBD (bd_cont d) (bd_bits d) (bd_ptr d) true)
    else if 8 <=? bd_ptr d then
      (* [comment removed for export] *)
      let p := bd_ptr d - Z.shiftr (bd_bits d) 3 in
      let! c := readLE64 src p in
      Ok (Unfinished, mkBD c (Z.land (bd_bits d) 7) p false)
    else if bd_ptr d =? 0 then
      Ok ((if bd_bits d <? 64 then EndOfBuffer else Completed), d)
    else
      let nb := Z.shiftr (bd_bits d) 3 in
      let '(nb', result) := (if bd_ptr d - nb <? 0 then (bd_ptr d, EndOfBuffer) else (nb, Unfinished)) in
      let p := bd_ptr d - nb' in
      let! c := readLE64 src p in
      Ok (result, mkBD c (bd_bits d - nb' * 8) p false).
End BitStream.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record dcell := mkDC { dc_newState : Z; dc_symbol : Z; dc_nbBits : Z }.
Record dtable := mkDT { dt_tableLog : Z; dt_fastMode : Z; dt_cells : list dcell }.

(* [comment removed for export] *)
Definition table_step (tableSize : Z) : Z := Z.shiftr tableSize 1 + Z.shiftr tableSize 3 + 3.

(* [comment removed for export] *)
Definition FSE_BUILD_DTABLE_WKSP_SIZE (tableLog maxSV : Z) : Z := 2 * (maxSV + 1) + 2^tableLog + 8.
Definition FSE_DTABLE_SIZE (tableLog : Z) : Z := (1 + 2^tableLog) * 4.
Definition FSE_DECOMPRESS_WKSP_SIZE (tableLog maxSV : Z) : Z :=
  ((1 + 2^tableLog) + 1 + (FSE_BUILD_DTABLE_WKSP_SIZE tableLog maxSV + 3) / 4 + (FSE_MAX_SYMBOL_VALUE + 1) / 2 + 1) * 4.

Section Build.
  Variable nc : list Z.            (* [comment removed for export] *)
  Variable maxSV : Z.
  Variable tableLog : Z.
  Let maxSV1 : Z := maxSV + 1.
  Let tableSize : Z := 2^tableLog.

  (* [comment removed for export] *)
  Fixpoint lowprob_loop (fuel : nat) (s : Z) (syms : list (option Z)) (snext : list Z) (hT : Z) (fm : Z)
    : res (list (option Z) * list Z * Z * Z) :=
    match fuel with
    | O => Ok (syms, snext, hT, fm)
    | S f =>
      let! c := load nc s in
      if c =? -1 then
        let! syms' := ostore syms hT s in
        lowprob_loop f (s + 1) syms' (snext ++ [1]) (u32 (hT - 1)) fm
      else
        let largeLimit := to_short (2^(tableLog - 1)) in
        let fm' := (if largeLimit <=? c then 0 else fm) in
        lowprob_loop f (s + 1) syms (snext ++ [u16 c]) hT fm'
    end.

  (* [comment removed for export] *)
  Fixpoint write8 (k : nat) (spread : list (option Z)) (p : Z) (b : Z) : res (list (option Z)) :=
    match k with
    | O => Ok spread
    | S k' => let! sp1 := ostore spread p b in write8 k' sp1 (p + 1) b
    end.

  (* [comment removed for export] *)
  Fixpoint spread_inner (fuel : nat) (spread : list (option Z)) (pos i n s : Z) : res (list (option Z)) :=
    match fuel with
    | O => NoFuel
    | S f =>
      if i <? n then
        let! sp1 := write8 8 spread (pos + i) s in
        spread_inner f sp1 pos (i + 8) n s
      else Ok spread
    end.

  (* [comment removed for export] *)
  Fixpoint spread_loop (fuel : nat) (s : Z) (spread : list (option Z)) (pos : Z) : res (list (option Z)) :=
    match fuel with
    | O => Ok spread
    | S f =>
      let! n := load nc s in
      let! sp1 := write8 8 spread pos (to_byte s) in
      let! sp2 := spread_inner (S (Z.to_nat n)) sp1 pos 8 n (to_byte s) in
      spread_loop f (s + 1) sp2 (u64 (pos + n))
    end.

  (* [comment removed for export] *)
  Fixpoint place_loop (fuel : nat) (s : Z) (spread : list (option Z)) (syms : list (option Z)) (position : Z)
    : res (list (option Z) * Z) :=
    match fuel with
    | O => Ok (syms, position)
    | S f =>
      let mask := tableSize - 1 in
      let step := table_step tableSize in
      let! b0 := oload spread s in
      let! syms1 := ostore syms (Z.land position mask) b0 in
      let! b1 := oload spread (s + 1) in
      let! syms2 := ostore syms1 (Z.land (position + step) mask) b1 in
      place_loop f (s + 2) spread syms2 (Z.land (position + 2 * step) mask)
    end.

  (* [comment removed for export] *)
  Fixpoint skip_loop (fuel : nat) (position hT : Z) : res Z :=
    match fuel with
    | O => NoFuel
    | S f =>
      if hT <? position then skip_loop f (Z.land (position + table_step tableSize) (tableSize - 1)) hT
      else Ok position
    end.

  (* [comment removed for export] *)
  Fixpoint sym_loop (fuel : nat) (i n s : Z) (syms : list (option Z)) (position hT : Z) : res (list (option Z) * Z) :=
    match fuel with
    | O => NoFuel
    | S f =>
      if i <? n then
        let! syms1 := ostore syms position s in
        let! p1 := skip_loop (S (Z.to_nat tableSize)) (Z.land (position + table_step tableSize) (tableSize - 1)) hT in
        sym_loop f (i + 1) n s syms1 p1 hT
      else Ok (syms, position)
    end.

  Fixpoint gen_loop (fuel : nat) (s : Z) (syms : list (option Z)) (position hT : Z) : res (list (option Z) * Z) :=
    match fuel with
    | O => Ok (syms, position)
    | S f =>
      let! n := load nc s in
      let! r := sym_loop (S (Z.to_nat n)) 0 n s syms position hT in
      let '(syms1, p1) := r in
      gen_loop f (s + 1) syms1 p1 hT
    end.

  (* [comment removed for export] *)
  Fixpoint build_loop (fuel : nat) (u : Z) (syms : list (option Z)) (snext : list Z) (acc : list dcell)
    : res (list dcell) :=
    match fuel with
    | O => Ok acc
    | S f =>
      let! sym := oload syms u in
      let! next := load snext sym in
      let! snext' := store snext sym (u16 (next + 1)) in
      let! hb := highbit32 next in
      let nbBits := to_byte (tableLog - hb) in
      let! sh := shl32 next nbBits in
      let newState := u16 (sh - tableSize) in
      build_loop f (u + 1) syms snext' (acc ++ [mkDC newState sym nbBits])
    end.

  (* [comment removed for export] *)
  Definition build_dtable (wkspSize : Z) : res dtable :=
    let! _ := assert ((0 <=? tableLog) && (tableLog <? 32)) in     (* [comment removed for export] *)
    if wkspSize <? FSE_BUILD_DTABLE_WKSP_SIZE tableLog maxSV then Err ZSTD_error_maxSymbolValue_tooLarge
    else if FSE_MAX_SYMBOL_VALUE <? maxSV then Err ZSTD_error_maxSymbolValue_tooLarge
    else if FSE_MAX_TABLELOG <? tableLog then Err ZSTD_error_tableLog_tooLarge
    else
      let! _ := assert (1 <=? tableLog) in                           (* [comment removed for export] *)
      let syms0 := repeat None (Z.to_nat tableSize) in
      let! r := lowprob_loop (Z.to_nat maxSV1) 0 syms0 [] (tableSize - 1) 1 in
      let '(syms1, snext, hT, fastMode) := r in
      let! r2 :=
        (if hT =? tableSize - 1 then
           let spread0 := repeat None (Z.to_nat (tableSize + 8)) in
           let! spread := spread_loop (Z.to_nat maxSV1) 0 spread0 0 in
           place_loop (Z.to_nat (tableSize / 2)) 0 spread syms1 0
         else gen_loop (Z.to_nat maxSV1) 0 syms1 0 hT) in
      let '(syms2, position) := r2 in
      if negb (hT =? tableSize - 1) && negb (position =? 0) then Err ZSTD_error_GENERIC
      else
        let! cells := build_loop (Z.to_nat tableSize) 0 syms2 snext [] in
        Ok (mkDT tableLog fastMode cells).
End Build.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Decode.
  Variable src : list Z.        (* [comment removed for export] *)
  Variable dt : dtable.
  Variable maxDstSize : Z.
  Variable fast : bool.
  Let tableSize : Z := Zlength (dt_cells dt).

  Definition cell (state : Z) : res dcell :=
    if (0 <=? state) && (state <? tableSize) then Ok (nth (Z.to_nat state) (dt_cells dt) (mkDC 0 0 0)) else Ub.

  (* [comment removed for export] *)
  Definition decode_sym (state : Z) (d : bitD) : res (Z * Z * bitD) :=
    let! c := cell state in
    let! rb := (if fast then Ok (read_bits_fast d (dc_nbBits c)) else read_bits d (dc_nbBits c)) in
    let '(lowBits, d') := rb in
    Ok (dc_symbol c, dc_newState c + lowBits, d').

  (* [comment removed for export] *)
  Record dec := mkDec { de_out : list Z; de_s1 : Z; de_s2 : Z; de_bd : bitD }.

  (* [comment removed for export] *)
  Fixpoint main_loop (fuel : nat) (x : dec) : res dec :=
    match fuel with
    | O => NoFuel
    | S f =>
      let! r := reload_dstream src (de_bd x) in
      let '(st, d0) := r in
      if dstatus_eqb st Unfinished && (Zlength (de_out x) <? maxDstSize - 3) then
        let! q1 := decode_sym (de_s1 x) d0 in let '(o0, s1a, d1) := q1 in
        let! q2 := decode_sym (de_s2 x) d1 in let '(o1, s2a, d2) := q2 in
        let! q3 := decode_sym s1a d2 in let '(o2, s1b, d3) := q3 in
        let! q4 := decode_sym s2a d3 in let '(o3, s2b, d4) := q4 in
        main_loop f (mkDec (de_out x ++ [o0; o1; o2; o3]) s1b s2b d4)
      else Ok (mkDec (de_out x) (de_s1 x) (de_s2 x) d0)
    end.

  (* [comment removed for export] *)
  Fixpoint tail_loop (fuel : nat) (x : dec) : res (list Z) :=
    match fuel with
    | O => NoFuel
    | S f =>
      if maxDstSize - 2 <? Zlength (de_out x) then Err ZSTD_error_dstSize_tooSmall
      else
        let! q1 := decode_sym (de_s1 x) (de_bd x) in let '(o0, s1a, d1) := q1 in
        let! r1 := reload_dstream src d1 in let '(st1, d1r) := r1 in
        if dstatus_eqb st1 Overflow then
          let! q2 := decode_sym (de_s2 x) d1r in let '(o1, _, _) := q2 in
          Ok (de_out x ++ [o0; o1])
        else
          let out1 := de_out x ++ [o0] in
          if maxDstSize - 2 <? Zlength out1 then Err ZSTD_error_dstSize_tooSmall
          else
            let! q2 := decode_sym (de_s2 x) d1r in let '(o1, s2a, d2) := q2 in
            let! r2 := reload_dstream src d2 in let '(st2, d2r) := r2 in
            if dstatus_eqb st2 Overflow then
              let! q3 := decode_sym s1a d2r in let '(o2, _, _) := q3 in
              Ok (out1 ++ [o1; o2])
            else tail_loop f (mkDec (out1 ++ [o1]) s1a s2a d2r)
    end.

  Definition decompress_usingDTable : res (list Z) :=
    let! d0 := init_dstream src in
    (* [comment removed for export] *)
    let! rb1 := read_bits d0 (dt_tableLog dt) in let '(st1, d1) := rb1 in
    let! r1 := reload_dstream src d1 in let '(_, d1r) := r1 in
    let! rb2 := read_bits d1r (dt_tableLog dt) in let '(st2, d2) := rb2 in
    let! r2 := reload_dstream src d2 in let '(_, d2r) := r2 in
    let! r3 := reload_dstream src d2r in let '(st, d3) := r3 in
    if dstatus_eqb st Overflow then Err ZSTD_error_corruption_detected
    else
      (* [comment removed for export] *)
      let! x := main_loop (S (Z.to_nat maxDstSize)) (mkDec [] st1 st2 d3) in
      tail_loop (S (Z.to_nat maxDstSize)) x.
End Decode.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fse_decompress_wksp (nc0 : list Z) (dstCapacity : Z) (src : list Z) (maxLog wkspSize : Z)
  : res (list Z) :=
  if wkspSize <? 512 then Err ZSTD_error_GENERIC
  else
    let! r := read_ncount nc0 FSE_MAX_SYMBOL_VALUE src in
    let '(nc, maxSV, tableLog, ncl) := r in
    if maxLog <? tableLog then Err ZSTD_error_tableLog_tooLarge
    else if wkspSize <? FSE_DECOMPRESS_WKSP_SIZE tableLog maxSV then Err ZSTD_error_tableLog_tooLarge
    else
      let! _ := assert ((0 <=? ncl) && (ncl <=? Zlength src)) in
      let wksp' := wkspSize - 512 - FSE_DTABLE_SIZE tableLog in
      let! dt := build_dtable nc maxSV tableLog wksp' in
      decompress_usingDTable (skipn (Z.to_nat ncl) src) dt dstCapacity (negb (dt_fastMode dt =? 0)).

(* [comment removed for export] *)
Definition HUF_READ_STATS_WORKSPACE_SIZE : Z := FSE_DECOMPRESS_WKSP_SIZE 6 (12 - 1).
Definition huf_fse_weights (fsePart : list Z) : res (list Z) :=
  fse_decompress_wksp (repeat 0 256) 255 fsePart 6 HUF_READ_STATS_WORKSPACE_SIZE.

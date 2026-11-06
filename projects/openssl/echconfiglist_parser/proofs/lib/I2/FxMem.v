(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import W64 ITrie FxState.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope uint63_scope.

(* [comment removed for export] *)
Definition nib (c : int) : option int :=
  if (48 <=? c) && (c <=? 57) then Some (c - 48)
  else if (97 <=? c) && (c <=? 102) then Some (c - 87)
  else None.

Definition hex_byte (s : string) (o : int) : option int :=
  let i := o << 1 in
  if (o <? 2305843009213693952) && (i + 1 <? PrimString.length s) then   (* [comment removed for export] *)
    match nib (PrimString.get s i), nib (PrimString.get s (i + 1)) with
    | Some h, Some l => Some ((h << 4) lor l)
    | _, _ => None
    end
  else None.

Definition hex_cell (s : string) (o : int) : option w64 :=
  match hex_byte s o, hex_byte s (o + 1), hex_byte s (o + 2), hex_byte s (o + 3),
        hex_byte s (o + 4), hex_byte s (o + 5), hex_byte s (o + 6), hex_byte s (o + 7) with
  | Some b0, Some b1, Some b2, Some b3, Some b4, Some b5, Some b6, Some b7 =>
      Some (w_of_bytes8 b0 b1 b2 b3 b4 b5 b6 b7)
  | _, _, _, _, _, _, _, _ => None
  end.

Fixpoint find_seg (im : fimage) (a : int) : option fseg :=
  match im with
  | [] => None
  | sg :: r => if (sg_base sg <=? a) && (a <? sg_base sg + sg_size sg) then Some sg else find_seg r a
  end.

Section WithImage.
Variable IM : fimage.

Definition image_cell (a8 : int) : option fval :=
  match find_seg IM a8 with
  | Some sg => match hex_cell (sg_hex sg) (a8 - sg_base sg) with
               | Some w => Some (FV 0 w)
               | None => None
               end
  | None => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition page_in_region (rg : region) (pn : int) : bool :=
  (pn <? 1125899906842624) && (rg_lo rg <=? (pn << 12))
  && ((pn << 12) <? rg_len rg)
  && (rg_len rg <=? 4611686018427387904).
Definition page_at (rg : region) (t pn : int) : option page :=
  match iget pn (rg_pages rg) with
  | Some p => Some p
  | None =>
      match (if t =? 0 then find_seg IM (pn << 12) else None) with
      | Some sg => Some (PG (sg_wr sg) PKImage iempty)
      | None =>
          match rg_dflt rg with
          | Some k => if page_in_region rg pn then Some (PG true k iempty) else None
          | None => None
          end
      end
  end.

(* [comment removed for export] *)
Definition cell_at (p : page) (pn ci : int) : option fval :=
  match iget ci (pg_cells p) with
  | Some (CV v) => Some v
  | Some CU => None
  | Some (CB _) => None
  | None =>
      match pg_kind p with
      | PKZero => Some fv0
      | PKUnk => None
      | PKImage => image_cell ((pn << 12) + (ci << 3))
      end
  end.

Definition msz_int (sz : msize) : int :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

Definition off_bound : int := 4611686018427387904.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition in_region (rg : region) (off n : int) : bool :=
  (off <? off_bound) && (rg_len rg <=? off_bound) && (rg_lo rg <=? off) && (off + n <=? rg_len rg).

Definition ext_load (sz : msize) (sgn : bool) (raw : w64) : w64 :=
  match sz, sgn with
  | SZ1, true => w_sext8 raw | SZ2, true => w_sext16 raw | SZ4, true => w_sext32 raw
  | _, _ => raw
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition slots_of_val (c : fval) : slots :=
  match c with
  | FV t w =>
      if t =? 0 then SL (SK (w_byte 0 w)) (SK (w_byte 1 w)) (SK (w_byte 2 w)) (SK (w_byte 3 w))
                        (SK (w_byte 4 w)) (SK (w_byte 5 w)) (SK (w_byte 6 w)) (SK (w_byte 7 w))
      else SL (SV c 0) (SV c 1) (SV c 2) (SV c 3) (SV c 4) (SV c 5) (SV c 6) (SV c 7)
  end.
Definition slots_unk : slots := SL SU SU SU SU SU SU SU SU.

(* [comment removed for export] *)
Definition slots_at (p : page) (pn ci : int) : slots :=
  match iget ci (pg_cells p) with
  | Some (CB sl) => sl
  | _ => match cell_at p pn ci with Some c => slots_of_val c | None => slots_unk end
  end.

(* [comment removed for export] *)
Definition vslot (v : fval) (j : int) : slot :=
  match v with FV t w => if t =? 0 then SK (w_byte j w) else SV v j end.

(* [comment removed for export] *)
Definition store_slots (bi n : int) (v : fval) (s : slots) : slots :=
  let f (j : int) (old : slot) := if (bi <=? j) && (j <? bi + n) then vslot v (j - bi) else old in
  SL (f 0 (sl0 s)) (f 1 (sl1 s)) (f 2 (sl2 s)) (f 3 (sl3 s))
     (f 4 (sl4 s)) (f 5 (sl5 s)) (f 6 (sl6 s)) (f 7 (sl7 s)).

Definition fv_eqb (a b : fval) : bool := (vtag a =? vtag b) && w_eqb (vw a) (vw b).

(* [comment removed for export] *)
Definition norm_slots (s : slots) : cell :=
  match s with
  | SL (SK b0) (SK b1) (SK b2) (SK b3) (SK b4) (SK b5) (SK b6) (SK b7) =>
      CV (FV 0 (w_of_bytes8 (b0 land 255) (b1 land 255) (b2 land 255) (b3 land 255)
                            (b4 land 255) (b5 land 255) (b6 land 255) (b7 land 255)))
  | SL (SV v0 j0) (SV v1 j1) (SV v2 j2) (SV v3 j3) (SV v4 j4) (SV v5 j5) (SV v6 j6) (SV v7 j7) =>
      if (j0 =? 0) && (j1 =? 1) && (j2 =? 2) && (j3 =? 3)
         && fv_eqb v0 v1 && fv_eqb v0 v2 && fv_eqb v0 v3
         && fv_eqb v4 v5 && fv_eqb v4 v6 && fv_eqb v4 v7
      then
        if (j4 =? 4) && (j5 =? 5) && (j6 =? 6) && (j7 =? 7) && fv_eqb v0 v4 then CV v0
        else if (j4 =? 0) && (j5 =? 1) && (j6 =? 2) && (j7 =? 3)
                && (vkind (vtag v0) =? K_LO) && (vkind (vtag v4) =? K_HI)
                && (vbase (vtag v0) =? vbase (vtag v4)) && w_eqb (vw v0) (vw v4)
             then CV (FV (vbase (vtag v0)) (vw v0))
             else CB s
      else CB s
  | _ => CB s
  end.

(* [comment removed for export] *)
Definition store_cell (p : page) (pn ci bi n : int) (v : fval) : cell :=
  norm_slots (store_slots bi n v (slots_at p pn ci)).

Definition is_sk (s : slot) : bool := match s with SK _ => true | _ => false end.
Definition skb (s : slot) : int := match s with SK b => b land 255 | _ => 0 end.
Definition w_of_sk (s : slots) : w64 :=
  w_of_bytes8 (skb (sl0 s)) (skb (sl1 s)) (skb (sl2 s)) (skb (sl3 s))
              (skb (sl4 s)) (skb (sl5 s)) (skb (sl6 s)) (skb (sl7 s)).
Definition all_sk (bi n : int) (s : slots) : bool :=
  let g (j : int) (x : slot) := (j <? bi) || (bi + n <=? j) || is_sk x in
  g 0 (sl0 s) && g 1 (sl1 s) && g 2 (sl2 s) && g 3 (sl3 s)
  && g 4 (sl4 s) && g 5 (sl5 s) && g 6 (sl6 s) && g 7 (sl7 s).

(* [comment removed for export] *)
Definition load_lo (v : fval) : option fval :=
  match v with
  | FV t w =>
      let k := vkind t in
      if k =? 0 then (if t =? 0 then Some (FV 0 (w_sext32 w)) else Some (FV (ktag K_LO t) w))
      else if k =? 1 then Some (FV (ktag K_NLO (vbase t)) w)
      else if (k =? 2) || (k =? 3) || (k =? 4) then Some v
      else None
  end.
(* [comment removed for export] *)
Definition load_hi (v : fval) : option fval :=
  match v with
  | FV t w => if (vkind t =? 0) && negb (t =? 0) then Some (FV (ktag K_HI t) w) else None
  end.

Definition load_slots (sz : msize) (sgn : bool) (bi : int) (s : slots) : option fval :=
  let n := msz_int sz in
  if all_sk bi n s then Some (FV 0 (ext_load sz sgn (w_extract bi n (w_of_sk s))))
  else
    match sz, sgn with
    | SZ4, true =>
        match sget bi s, sget (bi + 1) s, sget (bi + 2) s, sget (bi + 3) s with
        | SV v0 j0, SV v1 j1, SV v2 j2, SV v3 j3 =>
            if fv_eqb v0 v1 && fv_eqb v0 v2 && fv_eqb v0 v3 then
              if (j0 =? 0) && (j1 =? 1) && (j2 =? 2) && (j3 =? 3) then load_lo v0
              else if (j0 =? 4) && (j1 =? 5) && (j2 =? 6) && (j3 =? 7) then load_hi v0
              else None
            else None
        | _, _, _, _ => None
        end
    | _, _ => None
    end.

(* [comment removed for export] *)
Definition resolve_slot (M : itrie region) (s : slot) : slot :=
  match s with
  | SV (FV t (W64 top off)) j =>
      if (t <? kind_lim) && (j <=? 7) then
        match iget t M with
        | Some rg =>
            (* [comment removed for export] *)
            if ((j + 1) << 3) <=? rg_align rg then SK (w_byte j (W64 top off))
            else
              (* [comment removed for export] *)
              let a := rg_clo rg + off in
              let b := rg_chi rg + off in
              if ((top land 1) =? 0) && (off <? off_bound)
                 && (rg_chi rg <? off_bound) && (rg_clo rg <=? rg_chi rg) && ((a >> (j << 3)) =? (b >> (j << 3)))
              then SK ((a >> (j << 3)) land 255) else s
        | None => s
        end
      else s
  | _ => s
  end.
Definition resolve_slots (M : itrie region) (s : slots) : slots :=
  SL (resolve_slot M (sl0 s)) (resolve_slot M (sl1 s)) (resolve_slot M (sl2 s)) (resolve_slot M (sl3 s))
     (resolve_slot M (sl4 s)) (resolve_slot M (sl5 s)) (resolve_slot M (sl6 s)) (resolve_slot M (sl7 s)).

(* [comment removed for export] *)
Definition b5_nonzero (M : itrie region) (b : int) (w : w64) : bool :=
  match w with
  | W64 top off =>
    match iget b M with
    | Some rg => ((top land 1) =? 0) && (off <? off_bound) && (rg_chi rg <? off_bound)
                 && (1099511627776 <=? rg_clo rg + off)            (* [comment removed for export] *)
                 && (rg_chi rg + off <? 281474976710656)           (* [comment removed for export] *)
    | None => false
    end
  end.

(* [comment removed for export] *)
Definition load_slots2 (M : itrie region) (sz : msize) (sgn : bool) (bi : int) (s : slots) : option fval :=
  match load_slots sz sgn bi s with
  | Some v => Some v
  | None =>
      let n := msz_int sz in
      let s' := resolve_slots M s in
      if all_sk bi n s' then Some (FV 0 (ext_load sz sgn (w_extract bi n (w_of_sk s'))))
      else
        match sz, sgn with
        | SZ1, false =>
            match sget bi s with
            | SV (FV t w) j => if (j =? 5) && (t <? kind_lim) && b5_nonzero M t w
                               then Some (FV (ktag K_B5 t) w) else None
            | _ => None
            end
        | _, _ => None
        end
  end.

(* [comment removed for export] *)
Definition fm_load (M : itrie region) (a : fval) (sz : msize) (sgn : bool) : option fval :=
  match a with
  | FV t (W64 top off) =>
    if negb ((top land 1) =? 0) then None else
    let bi := off land 7 in
    let n := msz_int sz in
    if negb (bi + n <=? 8) then None else
    match iget t M with
    | None => None
    | Some rg =>
      if negb (in_region rg off n) then None else
      let pn := off >> 12 in
      match page_at rg t pn with
      | None => None
      | Some p =>
        let ci := (off land 4095) >> 3 in
        match cell_at p pn ci with
        | Some c =>
          match sz with
          | SZ8 => Some c
          | _ => if vtag c =? 0 then Some (FV 0 (ext_load sz sgn (w_extract bi n (vw c))))
                 else load_slots2 M sz sgn bi (slots_of_val c)
          end
        | None =>
          match iget ci (pg_cells p) with
          | Some (CB sl) => load_slots2 M sz sgn bi sl
          | _ => None
          end
        end
      end
    end
  end.

(* [comment removed for export] *)
Definition fm_store (M : itrie region) (a : fval) (sz : msize) (v : fval) : option (itrie region) :=
  match a with
  | FV t (W64 top off) =>
    if negb ((top land 1) =? 0) then None else
    let bi := off land 7 in
    let n := msz_int sz in
    if negb (bi + n <=? 8) then None else
    match iget t M with
    | None => None
    | Some rg =>
      if negb (in_region rg off n) then None else
      let pn := off >> 12 in
      match page_at rg t pn with
      | None => None
      | Some p =>
        if negb (pg_wr p) then None else
        let ci := (off land 4095) >> 3 in
        let newc : cell :=
          match sz with
          | SZ8 => CV v
          | _ => match cell_at p pn ci with
                 | Some c => if (vtag c =? 0) && (vtag v =? 0)
                             then CV (FV 0 (w_insert bi n (vw c) (vw v)))
                             else store_cell p pn ci bi n v
                 | None => store_cell p pn ci bi n v
                 end
          end in
        let p' := PG true (pg_kind p) (iset ci newc (pg_cells p)) in
        Some (iset t (RGK (rg_lo rg) (rg_len rg) (rg_align rg) (rg_dflt rg) (iset pn p' (rg_pages rg))
                          (rg_clo rg) (rg_chi rg) (rg_kind rg)) M)
      end
    end
  end.
End WithImage.

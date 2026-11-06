(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Uint63 PrimString.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxInstr FxState FxMem FxExec FxImage FxHandoff I2Image.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope uint63_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record i2consts : Type := I2K {
  c_malloc : int; c_free : int; c_realloc : int; c_aalloc : int;   (* [comment removed for export] *)
  c_stack : int;      (* [comment removed for export] *)
  c_mstack : int;     (* [comment removed for export] *)
  c_errcell : int;    (* [comment removed for export] *)
  c_errbi : int;      (* [comment removed for export] *)
  c_tra : int;        (* [comment removed for export] *)
  c_cost : int; c_cnt : int; c_big : int;   (* [comment removed for export] *)
  c_xw : list int;    (* [comment removed for export] *)
  c_ro : list (int * cell);     (* [comment removed for export] *)
  c_rb : list int }.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ro_bytes (K : i2consts) : list int :=
  flat_map (fun kc : int * cell => map (fun j => fst kc + j) [0; 1; 2; 3; 4; 5; 6; 7]) (c_ro K) ++ c_rb K.
Definition ro_of (K : i2consts) : itrie unit :=
  fold_right (fun b acc => iset b tt acc) iempty (ro_bytes K).

(* [comment removed for export] *)
(* [comment removed for export] *)
Record i2st : Type := I2S {
  i_F : fstate;               (* [comment removed for export] *)
  i_n : int;                  (* [comment removed for export] *)
  i_blk : list (int * int);   (* [comment removed for export] *)
  i_cost : int; i_cnt : int; i_big : int;   (* [comment removed for export] *)
  i_nm : int; i_nf : int; i_nr : int; i_na : int }.  (* [comment removed for export] *)

Inductive i2res : Type := Done (st : i2st) | Rej (code : int) (st : i2st).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition two32 : int := 4294967296.
Definition two59 : int := 576460752303423488.
Definition BIGB : int := 2028.
Definition big1 (n : int) : int := if BIGB <? n then 1 else 0.
Definition RMMAP_THRESHOLD : int := 131052.

(* [comment removed for export] *)
Definition conc63 (v : fval) : option int :=
  match v with FV t (W64 top lo) => if (t =? 0) && (top =? 0) then Some lo else None end.

(* [comment removed for export] *)
Definition base_tag (v : fval) : option int :=
  match v with FV t (W64 top lo) => if negb (t =? 0) && (top =? 0) && (lo =? 0) then Some t else None end.

Fixpoint bsize_of (t : int) (l : list (int * int)) : option int :=
  match l with
  | [] => None
  | (t', n) :: r => if t' =? t then Some n else bsize_of t r
  end.
Fixpoint bremove (t : int) (l : list (int * int)) : list (int * int) :=
  match l with
  | [] => []
  | (t', n) :: r => if t' =? t then r else (t', n) :: bremove t r
  end.

(* [comment removed for export] *)
Definition call_sp (K : i2consts) (F : fstate) : option int :=
  match rget F 2 with
  | FV t (W64 top off) =>
      if (t =? 1) && (top =? 0) && (c_mstack K <=? off) && (off <=? c_stack K) && ((off land 15) =? 0)
      then Some off else None
  end.

(* [comment removed for export] *)
Definition call_link (F : fstate) : option int :=
  match conc63 (rget F 1) with
  | Some l => if ((l land 1) =? 0) && (l <? 4611686018427387900) then Some l else None
  | None => None
  end.

(* [comment removed for export] *)
Definition err_page_ok (K : i2consts) (M : itrie region) : bool :=
  match iget 0 M with
  | Some rg0 =>
      in_region rg0 (c_errcell K) 8 &&
      match iget (c_errcell K >> 12) (rg_pages rg0) with
      | Some p => pg_wr p
      | None => false
      end
  | None => false
  end.

(* [comment removed for export] *)
Definition err_slot (K : i2consts) (te j : int) : slot :=
  if (c_errbi K <=? j) && (j <? c_errbi K + 4) then SV (FV te w_zero) (j - c_errbi K) else SU.
Definition err_cell (K : i2consts) (te : int) : cell :=
  CB (SL (err_slot K te 0) (err_slot K te 1) (err_slot K te 2) (err_slot K te 3)
         (err_slot K te 4) (err_slot K te 5) (err_slot K te 6) (err_slot K te 7)).
Definition set_errno (K : i2consts) (te : int) (M : itrie region) : option (itrie region) :=
  match iget 0 M with
  | Some rg0 =>
      let pn := c_errcell K >> 12 in
      let ci := (c_errcell K land 4095) >> 3 in
      match iget pn (rg_pages rg0) with
      | Some p =>
          if pg_wr p then
            let p' := PG true (pg_kind p) (iset ci (err_cell K te) (pg_cells p)) in
            Some (iset 0 (RGK (rg_lo rg0) (rg_len rg0) (rg_align rg0) (rg_dflt rg0) (iset pn p' (rg_pages rg0))
                              (rg_clo rg0) (rg_chi rg0) (rg_kind rg0)) M)
          else None
      | None => None
      end
  | None => None
  end.

(* [comment removed for export] *)
Definition keep_cells_ge (ci0 : int) (cells : itrie cell) : itrie cell :=
  iof_list (map (fun kc : int * cell => (fst kc, snd kc)) (List.filter (fun kc => ci0 <=? fst kc) (ielements cells))).
Definition drop_page (pn0 ci0 : int) (pp : int * page) : page :=
  if fst pp =? pn0 then PG (pg_wr (snd pp)) (pg_kind (snd pp)) (keep_cells_ge ci0 (pg_cells (snd pp))) else snd pp.
Definition drop_below (off : int) (rg : region) : region :=
  let pn0 := off >> 12 in
  let ci0 := (off land 4095) >> 3 in
  let pages' := iof_list (map (fun pp : int * page => (fst pp, drop_page pn0 ci0 pp))
                               (List.filter (fun pp => pn0 <=? fst pp) (ielements (rg_pages rg)))) in
  RGK (rg_lo rg) (rg_len rg) (rg_align rg) (rg_dflt rg) pages' (rg_clo rg) (rg_chi rg) (rg_kind rg).
Definition drop_stack (off : int) (M : itrie region) : option (itrie region) :=
  match iget 1 M with
  | Some rg1 => Some (iset 1 (drop_below off rg1) M)
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint clobber (rs : list int) (t0 : int) (regs : itrie fval) : itrie fval :=
  match rs with
  | [] => regs
  | r :: rs' => clobber rs' (t0 + 1) (iset r (FV t0 w_zero) regs)
  end.
(* [comment removed for export] *)
Definition clob14 : list int := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].
(* [comment removed for export] *)
Definition clob15 : list int := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

(* [comment removed for export] *)
Definition blk_region (n al : int) (pages : itrie page) : region :=
  RGK 0 n al (Some PKUnk) pages clo_dflt chi_dflt RK_plain.

(* [comment removed for export] *)
Definition c_tp (K : i2consts) : int := c_errcell K + c_errbi K + 164.
Definition tp_ok (K : i2consts) (F : fstate) : bool :=
  match conc63 (rget F 4) with Some v => v =? c_tp K | None => false end.
Definition resv_none (F : fstate) : bool := match f_resv F with None => true | Some _ => false end.

(* [comment removed for export] *)
Definition call_ok (K : i2consts) (st : i2st) : option (int * int) :=
  let F := i_F st in
  match call_sp K F, call_link F with
  | Some off, Some l =>
      if tp_ok K F && resv_none F && err_page_ok K (f_mem F) && (i_n st <? two59) && (2 <=? i_n st)
      then Some (off, l) else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition ret_of (l : int) : int := (l >> 1) << 1.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_malloc (K : i2consts) (st : i2st) : option i2st :=
  let F := i_F st in
  match call_ok K st, conc63 (rget F 10) with
  | Some (off, l), Some n =>
      if (1 <=? n) && (n <? two32)
         && (i_cost st + n <=? c_cost K) && (i_cost st <=? c_cost K) && (n <=? c_cost K)
         && (i_cnt st + 1 <=? c_cnt K) && (i_cnt st <=? c_cnt K)
         && (i_big st + big1 n <=? c_big K) && (i_big st <=? c_big K)
      then
        let t := i_n st in
        match drop_stack off (f_mem F) with
        | Some M1 =>
            match set_errno K (t + 15) (iset t (blk_region n 4 iempty) M1) with
            | Some M2 =>
                let regs := iset 10 (FV t w_zero) (clobber clob14 (t + 1) (f_regs F)) in
                Some (I2S (FS (ret_of l) regs M2 None) (t + 16) ((t, n) :: i_blk st)
                          (i_cost st + n) (i_cnt st + 1) (i_big st + big1 n)
                          (i_nm st + 1) (i_nf st) (i_nr st) (i_na st))
            | None => None
            end
        | None => None
        end
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_free (K : i2consts) (st : i2st) : option i2st :=
  let F := i_F st in
  match call_ok K st, base_tag (rget F 10) with
  | Some (off, l), Some tb =>
      match bsize_of tb (i_blk st), iget tb (f_mem F) with
      | Some n, Some _ =>
          if (n <=? i_cost st) && (1 <=? i_cnt st) && (big1 n <=? i_big st) && (2 <=? tb) then
            let t := i_n st in
            match drop_stack off (iremove tb (f_mem F)) with
            | Some M1 =>
                match set_errno K (t + 15) M1 with
                | Some M2 =>
                    let regs := clobber clob15 t (f_regs F) in
                    Some (I2S (FS (ret_of l) regs M2 None) (t + 16) (bremove tb (i_blk st))
                              (i_cost st - n) (i_cnt st - 1) (i_big st - big1 n)
                              (i_nm st) (i_nf st + 1) (i_nr st) (i_na st))
                | None => None
                end
            | None => None
            end
          else None
      | _, _ => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_free_null (K : i2consts) (st : i2st) : option i2st :=
  let F := i_F st in
  match call_link F, conc63 (rget F 10) with
  | Some l, Some z =>
      if (z =? 0) && resv_none F then
        Some (I2S (FS (ret_of l) (f_regs F) (f_mem F) (f_resv F)) (i_n st) (i_blk st)
                  (i_cost st) (i_cnt st) (i_big st) (i_nm st) (i_nf st + 1) (i_nr st) (i_na st))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition keep_cell (c : cell) : bool := match c with CV _ => true | CB _ => true | CU => false end.
Definition copy_page (k : int) (pp : int * page) : page :=
  PG true PKUnk (iof_list (map (fun kc : int * cell => (fst kc, snd kc))
                               (List.filter (fun kc => ((fst pp << 12) + (fst kc << 3) + 8 <=? k) && (fst kc <? 512) && keep_cell (snd kc))
                                       (ielements (pg_cells (snd pp)))))).
(* [comment removed for export] *)
Definition copy_prefix (k n' : int) (rg : region) : itrie page :=
  iof_list (map (fun pp : int * page => (fst pp, copy_page k pp))
                (List.filter (fun pp : int * page => ((fst pp << 12) + 8 <=? k) && page_in_region (blk_region n' 4 iempty) (fst pp))
                             (ielements (rg_pages rg)))).

(* [comment removed for export] *)
Definition node_realloc (K : i2consts) (st : i2st) : option i2st :=
  let F := i_F st in
  match call_ok K st, base_tag (rget F 10), conc63 (rget F 11) with
  | Some (off, l), Some tb, Some n' =>
      match bsize_of tb (i_blk st), iget tb (f_mem F) with
      | Some n, Some rgb =>
          if (1 <=? n') && (n' <? RMMAP_THRESHOLD) && (2 <=? tb)
             && (i_cost st + n' <=? c_cost K) && (i_cost st <=? c_cost K) && (n' <=? c_cost K)
             && (i_cnt st + 1 <=? c_cnt K) && (i_cnt st <=? c_cnt K)
             && (i_big st + big1 n' <=? c_big K) && (i_big st <=? c_big K)
             && (n <=? i_cost st + n') && (big1 n <=? i_big st + big1 n')
          then
            let t := i_n st in
            let k := if n <? n' then n else n' in
            let rgn := blk_region n' 4 (copy_prefix k n' rgb) in
            match drop_stack off (iset t rgn (iremove tb (f_mem F))) with
            | Some M1 =>
                match set_errno K (t + 15) M1 with
                | Some M2 =>
                    let regs := iset 10 (FV t w_zero) (clobber clob14 (t + 1) (f_regs F)) in
                    Some (I2S (FS (ret_of l) regs M2 None) (t + 16) ((t, n') :: bremove tb (i_blk st))
                              (i_cost st + n' - n) (i_cnt st) (i_big st + big1 n' - big1 n)
                              (i_nm st) (i_nf st) (i_nr st + 1) (i_na st))
                | None => None
                end
            | None => None
            end
          else None
      | _, _ => None
      end
  | _, _, _ => None
  end.

(* [comment removed for export] *)
Definition log2_al (al : int) : option int :=
  if al =? 16 then Some 4 else if al =? 32 then Some 5 else if al =? 64 then Some 6 else None.
Definition node_aalloc (K : i2consts) (st : i2st) : option i2st :=
  let F := i_F st in
  match call_ok K st, conc63 (rget F 10), conc63 (rget F 11) with
  | Some (off, l), Some al, Some n =>
      match log2_al al with
      | Some lg =>
          if (1 <=? n) && (n + al <? RMMAP_THRESHOLD) && (n <=? c_cost K)
             && (i_cost st + n + al <=? c_cost K) && (i_cost st <=? c_cost K)
             && (i_cnt st + 1 <=? c_cnt K) && (i_cnt st <=? c_cnt K)
             && (i_big st + big1 (n + al) <=? c_big K) && (i_big st <=? c_big K)
          then
            let t := i_n st in
            match drop_stack off (f_mem F) with
            | Some M1 =>
                match set_errno K (t + 15) (iset t (blk_region n lg iempty) M1) with
                | Some M2 =>
                    let regs := iset 10 (FV t w_zero) (clobber clob14 (t + 1) (f_regs F)) in
                    Some (I2S (FS (ret_of l) regs M2 None) (t + 16) ((t, n) :: i_blk st)
                              (i_cost st + n) (i_cnt st + 1) (i_big st + big1 n)
                              (i_nm st) (i_nf st) (i_nr st) (i_na st + 1))
                | None => None
                end
            | None => None
            end
          else None
      | None => None
      end
  | _, _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_final (K : i2consts) (code : itrie finstr) (F : fstate) : bool :=
  match iget (f_pc F) code with
  | Some (FJalr rd rs1 imm _) =>
      (rd =? 0) && (rs1 =? 1) && w_eqb imm w_zero
      && fval_eqb (rget F 1) (FV (c_tra K) w_zero)
      && fval_eqb (rget F 2) (FV 1 (W64 0 (c_stack K)))
      && resv_none F
  | _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition no_bp : int := 1.     (* [comment removed for export] *)

Section Drive.
Variable IM : fimage.
Variable code : itrie finstr.
Variable K : i2consts.
Let RO := ro_of K.

Definition with_F (st : i2st) (F : fstate) : i2st :=
  I2S F (i_n st) (i_blk st) (i_cost st) (i_cnt st) (i_big st) (i_nm st) (i_nf st) (i_nr st) (i_na st).

Definition bindn (code' : int) (st : i2st) (o : option i2st) (k : i2st -> i2res) : i2res :=
  match o with Some st' => k st' | None => Rej code' st end.

(* [comment removed for export] *)
Definition node_at (st : i2st) : option i2st :=
  let pc := f_pc (i_F st) in
  if pc =? 0 then None
  else if pc =? c_malloc K then node_malloc K st
  else if pc =? c_free K then
         match conc63 (rget (i_F st) 10) with
         | Some _ => node_free_null K st
         | None => node_free K st
         end
  else if pc =? c_realloc K then node_realloc K st
  else if pc =? c_aalloc K then node_aalloc K st
  else None.

Fixpoint i2_run (fuel : nat) (st : i2st) : i2res :=
  match fuel with
  | O => Rej 90 st
  | S fuel' =>
      match fx_run IM code RO no_bp 40 (i_F st) with
      | (F', r, _) =>
          let st' := with_F st F' in
          match r with
          | SStuck c =>
              if c =? 1 then bindn 10 st' (node_at st') (i2_run fuel')
              else if c =? 2 then (if is_final K code F' then Done st' else Rej 2 st')
              else Rej (100 + c) st'
          | SEcall => Rej 3 st'
          | SBreak => Rej 4 st'
          | SFuel => Rej 5 st'
          end
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition slot_eqb (a b : slot) : bool :=
  match a, b with
  | SK x, SK y => x =? y
  | SV u i, SV v j => fval_eqb u v && (i =? j)
  | SU, SU => true
  | _, _ => false
  end.
Definition cell_eqb (a b : cell) : bool :=
  match a, b with
  | CV u, CV v => fval_eqb u v
  | CB x, CB y => slot_eqb (sl0 x) (sl0 y) && slot_eqb (sl1 x) (sl1 y) && slot_eqb (sl2 x) (sl2 y) && slot_eqb (sl3 x) (sl3 y)
                  && slot_eqb (sl4 x) (sl4 y) && slot_eqb (sl5 x) (sl5 y) && slot_eqb (sl6 x) (sl6 y) && slot_eqb (sl7 x) (sl7 y)
  | _, _ => false
  end.
Fixpoint ro_lookup (a : int) (l : list (int * cell)) : option cell :=
  match l with
  | [] => None
  | (a', c) :: r => if a' =? a then Some c else ro_lookup a r
  end.
Definition cell0_ok (a : int) (c : cell) : bool :=
  existsb (fun x => x =? a) (c_xw K)
  || (a =? c_errcell K)
  || match ro_lookup a (c_ro K) with Some c' => cell_eqb c c' | None => false end.
Definition xw_ok (F : fstate) : bool :=
  match iget 0 (f_mem F) with
  | Some rg0 =>
      forallb (fun pp : int * page =>
                 (fst pp <? 1024) &&
                 forallb (fun kc : int * cell => (fst kc <? 512) && cell0_ok ((fst pp << 12) + (fst kc << 3)) (snd kc))
                         (ielements (pg_cells (snd pp))))
              (ielements (rg_pages rg0))
  | None => false
  end.

(* [comment removed for export] *)
Inductive xval : Type :=
| XAny                        (* [comment removed for export] *)
| XW (w : w64)                (* [comment removed for export] *)
| XV (v : fval)               (* [comment removed for export] *)
| XNew (idx off : int)        (* [comment removed for export] *)
| XBytes (mask : int) (w : w64). (* [comment removed for export] *)

Record export : Type := XP {
  x_regs : list (int * xval);          (* [comment removed for export] *)
  x_cells : list (int * xval);         (* [comment removed for export] *)
  x_bcells : list (int * int * xval);  (* [comment removed for export] *)
  x_nblk : int;                        (* [comment removed for export] *)
  x_sizes : list int;                  (* [comment removed for export] *)
  x_errno : option int }.              (* [comment removed for export] *)

Definition blocks_old_first (st : i2st) : list (int * int) := rev (i_blk st).

Definition mask_bit (mask j : int) : bool := ((mask >> j) land 1) =? 1.
Definition bytes_match (mask : int) (w w' : w64) : bool :=
  forallb (fun j => negb (mask_bit mask j) || (w_byte j w' =? w_byte j w)) [0; 1; 2; 3; 4; 5; 6; 7].
Definition xval_ok (st : i2st) (v : fval) (x : xval) : bool :=
  match x with
  | XAny => true
  | XW w => fval_eqb v (FV 0 w)
  | XV u => fval_eqb v u
  | XNew idx off =>
      match nth_error (blocks_old_first st) (Z.to_nat (to_Z idx)) with
      | Some (t, _) => fval_eqb v (FV t (W64 0 off))
      | None => false
      end
  | XBytes mask w => match v with FV t w' => (t =? 0) && bytes_match mask w w' end
  end.
(* [comment removed for export] *)
Definition slots_match (mask : int) (w : w64) (sl : slots) : bool :=
  forallb (fun j => negb (mask_bit mask j) || match sget j sl with SK b => (b land 255) =? w_byte j w | _ => false end)
          [0; 1; 2; 3; 4; 5; 6; 7].

(* [comment removed for export] *)
Definition cell_of (M : itrie region) (t off : int) : option fval :=
  match iget t M with
  | Some rg =>
      match iget (off >> 12) (rg_pages rg) with
      | Some p => match iget ((off land 4095) >> 3) (pg_cells p) with Some (CV v) => Some v | _ => None end
      | None => None
      end
  | None => None
  end.

(* [comment removed for export] *)
Definition cell_raw (M : itrie region) (t off : int) : option cell :=
  match iget t M with
  | Some rg => match iget (off >> 12) (rg_pages rg) with Some p => iget ((off land 4095) >> 3) (pg_cells p) | None => None end
  | None => None
  end.

Definition xcell_ok (st : i2st) (t off : int) (x : xval) : bool :=
  match x with
  | XAny => true
  | XBytes mask w =>
      match cell_raw (f_mem (i_F st)) t off with
      | Some (CV v) => xval_ok st v x
      | Some (CB sl) => slots_match mask w sl
      | _ => false
      end
  | _ => match cell_of (f_mem (i_F st)) t off with Some v => xval_ok st v x | None => false end
  end.

Fixpoint list_int_eqb (a b : list int) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && list_int_eqb a' b'
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition errno_slot_is (t : int) (j : int) (s : slot) : bool :=
  match s with
  | SV (FV t' w) j' => (j' =? j) && w_eqb w w_zero && ((t' =? t) || (t' =? ktag K_LO t))
  | _ => false
  end.
Definition errno_is (st : i2st) (t : int) : bool :=
  match iget 0 (f_mem (i_F st)) with
  | Some rg =>
      match iget (c_errcell K >> 12) (rg_pages rg) with
      | Some p =>
          match iget ((c_errcell K land 4095) >> 3) (pg_cells p) with
          | Some (CB sl) => errno_slot_is t 0 (sget (c_errbi K + 0) sl) && errno_slot_is t 1 (sget (c_errbi K + 1) sl)
                            && errno_slot_is t 2 (sget (c_errbi K + 2) sl) && errno_slot_is t 3 (sget (c_errbi K + 3) sl)
          | _ => false
          end
      | None => false
      end
  | None => false
  end.

(* [comment removed for export] *)
Definition xb_inb (n off : int) (x : xval) : bool :=
  match x with
  | XAny => true
  | XBytes mask _ => (off <? n) && forallb (fun j => negb (mask_bit mask j) || (off + j <? n)) [0; 1; 2; 3; 4; 5; 6; 7]%uint63
  | _ => (8 <=? n) && (off <=? n - 8)
  end.

Definition export_ok (st : i2st) (X : export) : bool :=
  forallb (fun rx : int * xval => xval_ok st (rget (i_F st) (fst rx)) (snd rx)) (x_regs X)
  && forallb (fun cx : int * xval => ((fst cx land 7) =? 0) && xcell_ok st 0 (fst cx) (snd cx)) (x_cells X)
  && forallb (fun bx : int * int * xval =>
                match nth_error (blocks_old_first st) (Z.to_nat (to_Z (fst (fst bx)))) with
                | Some (t, n) => ((snd (fst bx) land 7) =? 0) && xb_inb n (snd (fst bx)) (snd bx)
                                 && xcell_ok st t (snd (fst bx)) (snd bx)
                | None => false
                end) (x_bcells X)
  && (of_Z (Z.of_nat (length (i_blk st))) =? x_nblk X)
  && list_int_eqb (map snd (blocks_old_first st)) (x_sizes X)
  && match x_errno X with None => true | Some t => errno_is st t end.

(* [comment removed for export] *)
Definition start_ok (st : i2st) : bool :=
  (2 <=? i_n st) && (i_n st <? two59)
  && (i_cost st =? 0) && (i_cnt st =? 0) && (i_big st =? 0)
  && forallb (fun tn : int * int => (2 <=? fst tn) && (fst tn <? i_n st)
                                    && match iget (fst tn) (f_mem (i_F st)) with Some _ => true | None => false end)
             (i_blk st)
  && err_page_ok K (f_mem (i_F st))
  && resv_none (i_F st).

Definition i2_check (fuel : nat) (st0 : i2st) (X : export) : bool :=
  start_ok st0 &&
  match i2_run fuel st0 with
  | Done st' => xw_ok (i_F st') && export_ok st' X
  | Rej _ _ => false
  end.

(* [comment removed for export] *)
Definition i2_diag (fuel : nat) (st0 : i2st) :=
  let '(code', st) := match i2_run fuel st0 with Done st => (0%uint63, st) | Rej c st => (c, st) end in
  (code', f_pc (i_F st), rget (i_F st) 10, rget (i_F st) 11, rget (i_F st) 2, rget (i_F st) 1,
   (i_nm st, i_nf st, i_nr st, i_na st), List.length (i_blk st), xw_ok (i_F st), start_ok st0, i_n st).
End Drive.

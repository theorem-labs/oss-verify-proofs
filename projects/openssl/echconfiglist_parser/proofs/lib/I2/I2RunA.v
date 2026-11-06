(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Uint63 PrimString.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import W64 ITrie FxInstr FxState FxMem FxExec FxImage FxHandoff FxHandoff2 I2Image I2Run.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope uint63_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record i2aconsts : Type := I2KA {
  ka_K : i2consts;              (* [comment removed for export] *)
  ka_malloc : list int; ka_free : list int; ka_realloc : list int; ka_memalign : int;
  ka_fsm : list (int * int);    (* [comment removed for export] *)
  ka_memset : int; ka_memcpy : list int; ka_memmove : int; ka_strlen : int;
  ka_fstack : int;              (* [comment removed for export] *)
  ka_istack : int;              (* [comment removed for export] *)
  ka_fsmax : int;               (* [comment removed for export] *)
  ka_sh0lo : int; ka_sh0len : int;      (* [comment removed for export] *)
  ka_sh0 : list (int * cell);           (* [comment removed for export] *)
  (* [comment removed for export] *)
  ka_ts0 : int;                         (* [comment removed for export] *)
  ka_pc0m : int; ka_pc0f : int; ka_pc0r : int; ka_pc0a : int;   (* [comment removed for export] *)
  ka_pfc : list (int * list int);       (* [comment removed for export] *)
  ka_pfo : list (int * list int);       (* [comment removed for export] *)
  ka_costs : list (int * int * int)     (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Record i2ast : Type := I2AS {
  a_F : fstate; a_n : int; a_blk : list (int * int); a_ff : list (int * int);
  a_cost : int; a_cnt : int; a_nodes : int;
  a_cs : list (int * int * int) }.     (* [comment removed for export] *)

Inductive i2ares : Type := ADone (st : i2ast) | ARej (code : int) (st : i2ast).

(* [comment removed for export] *)
Definition st_of (st : i2ast) : i2st := I2S (a_F st) (a_n st) (a_blk st) (a_cost st) (a_cnt st) 0 0 0 0 0.

Fixpoint list_eqb (a b : list int) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && list_eqb a' b'
  | _, _ => false
  end.
Definition inpf (pc0 : int) (ras : list int) (l : list (int * list int)) : bool :=
  existsb (fun e : int * list int => (fst e =? pc0) && list_eqb ras (snd e)) l.

Definition inl (x : int) (l : list int) : bool := existsb (fun y => y =? x) l.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sh_byte (n s : int) : int := if (s + 1) * 8 <=? n then 0 else n - s * 8.
Definition sh_slot (n nsh s : int) : slot := if s <? nsh then SK (sh_byte n s) else SU.
Definition sh_cell (n ci : int) : cell :=
  let nsh := (n + 7) >> 3 in
  if (ci + 1) * 8 <=? (n >> 3) then CV (FV 0 w_zero)
  else CB (SL (sh_slot n nsh (ci * 8)) (sh_slot n nsh (ci * 8 + 1)) (sh_slot n nsh (ci * 8 + 2)) (sh_slot n nsh (ci * 8 + 3))
             (sh_slot n nsh (ci * 8 + 4)) (sh_slot n nsh (ci * 8 + 5)) (sh_slot n nsh (ci * 8 + 6)) (sh_slot n nsh (ci * 8 + 7))).
Definition sh_cells (n : int) : itrie cell :=
  let ncells := (((n + 7) >> 3) + 7) >> 3 in
  iof_list (map (fun ci => (ci, sh_cell n ci)) (iseq (Z.to_nat (to_Z ncells)))).
(* [comment removed for export] *)
Definition sh_region (wr : bool) (p n : int) : region :=
  RGK 0 ((n + 7) >> 3) 0 (if wr then Some PKUnk else None) (iset 0 (PG wr PKUnk (sh_cells n)) iempty) clo_dflt chi_dflt (RK_shadow p).

(* [comment removed for export] *)
Definition fsz (k : int) : int := 64 << k.
Definition ff_region (k : int) (spv flagv : fval) : region :=
  let ncell := fsz k >> 3 in
  RGK 0 (fsz k) (6 + k) (Some PKUnk)
      (iset 0 (PG true PKUnk (iset (ncell - 1) (CV flagv) (iset 3 (CV spv) iempty))) iempty) clo_dflt chi_dflt RK_plain.
(* [comment removed for export] *)
Definition flag_region : region :=
  RGK 0 1 0 None (iset 0 (PG false PKUnk (iset 0 (CB (SL (SK 1) SU SU SU SU SU SU SU)) iempty)) iempty) clo_dflt chi_dflt RK_plain.

(* [comment removed for export] *)
Definition abs_pages (cells : list (int * cell)) : itrie page :=
  fold_right (fun ac acc =>
                let pn := fst ac >> 12 in let ci := (fst ac land 4095) >> 3 in
                let p := match iget pn acc with Some p => p | None => PG false PKUnk iempty end in
                iset pn (PG false PKUnk (iset ci (snd ac) (pg_cells p))) acc) iempty cells.
Definition abs_region (lo len : int) (cells : list (int * cell)) : region :=
  RGK lo len 0 None (abs_pages cells) 0 0 RK_plain.
Definition a_start (A : i2aconsts) (st : i2ast) : i2ast :=
  let F := a_F st in
  let M := iset 3 (abs_region (ka_sh0lo A) (ka_sh0len A) (ka_sh0 A)) (iset 2 (sh_region false 1 (c_stack (ka_K A))) (f_mem F)) in
  I2AS (FS (f_pc F) (f_regs F) M (f_resv F)) (a_n st) (a_blk st) (a_ff st) (a_cost st) (a_cnt st) (a_nodes st) (ka_costs A).

(* [comment removed for export] *)
Definition slot_eqb (a b : slot) : bool :=
  match a, b with
  | SK x, SK y => x =? y
  | SV v j, SV v' j' => fval_eqb v v' && (j =? j')
  | SU, SU => true
  | _, _ => false
  end.
Definition slots_eqb (a b : slots) : bool :=
  slot_eqb (sl0 a) (sl0 b) && slot_eqb (sl1 a) (sl1 b) && slot_eqb (sl2 a) (sl2 b) && slot_eqb (sl3 a) (sl3 b)
  && slot_eqb (sl4 a) (sl4 b) && slot_eqb (sl5 a) (sl5 b) && slot_eqb (sl6 a) (sl6 b) && slot_eqb (sl7 a) (sl7 b).
Definition cell_eqb (a b : cell) : bool :=
  match a, b with
  | CV v, CV v' => fval_eqb v v'
  | CU, CU => true
  | CB s, CB s' => slots_eqb s s'
  | _, _ => false
  end.
Definition ro_okb (K : i2consts) (M : itrie region) : bool :=
  match iget 0 M with
  | Some rg0 =>
      forallb (fun ac : int * cell =>
                 match iget (fst ac >> 12) (rg_pages rg0) with
                 | Some p => match iget ((fst ac land 4095) >> 3) (pg_cells p) with Some c => cell_eqb c (snd ac) | None => false end
                 | None => false
                 end) (c_ro K)
  | None => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition byte_at (IM : fimage) (M : itrie region) (t off : int) : slot :=
  if t =? 0 then
    match image_cell IM ((off >> 3) << 3) with Some (FV _ w) => SK (w_byte (off land 7) w) | None => SU end
  else
    match iget t M with
    | Some rg =>
        match iget (off >> 12) (rg_pages rg) with
        | Some p =>
            match iget ((off land 4095) >> 3) (pg_cells p) with
            | Some (CV v) => vslot v (off land 7)
            | Some (CB sl) => sget (off land 7) sl
            | _ => SU
            end
        | None => SU
        end
    | None => SU
    end.

(* [comment removed for export] *)
Definition set_slot (j : int) (s : slot) (sl : slots) : slots :=
  let f (i : int) (old : slot) := if i =? j then s else old in
  SL (f 0 (sl0 sl)) (f 1 (sl1 sl)) (f 2 (sl2 sl)) (f 3 (sl3 sl)) (f 4 (sl4 sl)) (f 5 (sl5 sl)) (f 6 (sl6 sl)) (f 7 (sl7 sl)).
Definition cur_slots (p : page) (ci : int) : slots :=
  match iget ci (pg_cells p) with
  | Some (CV v) => slots_of_val v
  | Some (CB sl) => sl
  | _ => slots_unk
  end.
Definition write_byte (M : itrie region) (t off : int) (s : slot) : option (itrie region) :=
  match iget t M with
  | Some rg =>
      let pn := off >> 12 in let ci := (off land 4095) >> 3 in
      let p := match iget pn (rg_pages rg) with Some p => p | None => PG true PKUnk iempty end in
      if pg_wr p then
        let c' := norm_slots (set_slot (off land 7) s (cur_slots p ci)) in
        let p' := PG true (pg_kind p) (iset ci c' (pg_cells p)) in
        Some (iset t (RGK (rg_lo rg) (rg_len rg) (rg_align rg) (rg_dflt rg) (iset pn p' (rg_pages rg)) (rg_clo rg) (rg_chi rg) (rg_kind rg)) M)
      else None
  | None => None
  end.
(* [comment removed for export] *)
Fixpoint fill_bytes (fuel : nat) (M : itrie region) (t off c : int) : option (itrie region) :=
  match fuel with
  | O => Some M
  | S f' => match write_byte M t off (SK c) with Some M' => fill_bytes f' M' t (off + 1) c | None => None end
  end.
(* [comment removed for export] *)
Fixpoint copy_bytes (IM : fimage) (fuel : nat) (M : itrie region) (td doff ts soff : int) : option (itrie region) :=
  match fuel with
  | O => Some M
  | S f' =>
      match byte_at IM M ts soff with
      | SU => None
      | s => match write_byte M td doff s with Some M' => copy_bytes IM f' M' td (doff + 1) ts (soff + 1) | None => None end
      end
  end.
(* [comment removed for export] *)
Fixpoint scan_strlen (IM : fimage) (fuel : nat) (M : itrie region) (t off acc : int) : option int :=
  match fuel with
  | O => None
  | S f' =>
      match byte_at IM M t off with
      | SK b => if (b land 255) =? 0 then Some acc else scan_strlen IM f' M t (off + 1) (acc + 1)
      | _ => None
      end
  end.

(* [comment removed for export] *)
Definition ptr_arg (M : itrie region) (v : fval) (n : int) : option (int * int) :=
  match v with
  | FV t (W64 top off) =>
      if (top =? 0) && negb (t =? 0) then
        match iget t M with
        | Some rg => if (rg_lo rg <=? off) && (to_Z off + to_Z n <=? to_Z (rg_len rg))%Z && (n <=? rg_len rg) then Some (t, off) else None   (* [comment removed for export] *)
        | None => None
        end
      else None
  end.
(* [comment removed for export] *)
Definition src_arg (M : itrie region) (v : fval) (n : int) : option (int * int) :=
  match v with
  | FV t (W64 top off) => if (t =? 0) && (top =? 0) then Some (0, off) else ptr_arg M v n
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition call_sp_n (K : i2consts) (stack : int) (F : fstate) : option int :=
  match rget F 2 with
  | FV t (W64 top off) =>
      if (t =? 1) && (top =? 0) && (stack <=? off) && (off <=? c_stack K) && ((off land 15) =? 0) then Some off else None
  end.
Definition call_okn (K : i2consts) (stack : int) (st : i2ast) : option (int * int) :=
  let F := a_F st in
  match call_sp_n K stack F, call_link F with
  | Some off, Some l =>
      if tp_ok K F && resv_none F && err_page_ok K (f_mem F) && (a_n st <? two59) && (2 <=? a_n st) then Some (off, l) else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition two46 : int := 70368744177664.
Definition cell1v (M : itrie region) (off : int) : option fval :=
  match iget 1 M with
  | Some rg =>
      match iget (off >> 12) (rg_pages rg) with
      | Some p => match iget ((off land 4095) >> 3) (pg_cells p) with Some (CV v) => Some v | _ => None end
      | None => None
      end
  | None => None
  end.
Fixpoint chain_walk (fuel : nat) (K : i2consts) (ts0 : int) (M : itrie region) (blk : list (int * int))
         (cur : fval) (ras : list int) : option (bool * list int) :=
  match fuel with
  | O => None
  | S f =>
      match cur with
      | FV t (W64 top off) =>
          if negb (top =? 0) then None
          else if t =? 1 then
            if ((off land 15) =? 0) && (16 <=? off) && (off <=? c_stack K) then
              match cell1v M (off - 16), cell1v M (off - 8) with
              | Some prev, Some rav =>
                  if off =? c_stack K then
                    (if fval_eqb prev (FV ts0 w_zero) && fval_eqb rav (FV (c_tra K) w_zero) then Some (true, ras) else None)
                  else
                    match rav, prev with
                    | FV tr (W64 rtop ra), FV tp (W64 _ poff) =>
                        if (tr =? 0) && (rtop =? 0) && (negb (tp =? 1) || (off <? poff))
                        then chain_walk f K ts0 M blk prev (ras ++ [ra])
                        else None
                    end
              | _, _ => None
              end
            else None
          else if t =? 0 then (if (off <? two46) || negb ((off land 7) =? 0) then Some (false, ras) else None)
          else match bsize_of t blk with
               | Some n => if off <=? n then Some (false, ras) else None
               | None => None
               end
      end
  end.
(* [comment removed for export] *)
Definition chain_okb (A : i2aconsts) (st : i2ast) (pc0 : int) (l : int) : bool :=
  match chain_walk 64 (ka_K A) (ka_ts0 A) (f_mem (a_F st)) (a_blk st) (rget (a_F st) 8) [l] with
  | Some (true, ras) => inpf pc0 ras (ka_pfo A)
  | Some (false, ras) => inpf pc0 ras (ka_pfc A)
  | None => false
  end.
(* [comment removed for export] *)
Definition chain_anyb (A : i2aconsts) (st : i2ast) (l : int) : bool :=
  match chain_walk 64 (ka_K A) (ka_ts0 A) (f_mem (a_F st)) (a_blk st) (rget (a_F st) 8) [l] with
  | Some _ => true
  | None => false
  end.

(* [comment removed for export] *)
Definition pop_cost (k a b : int) (cs : list (int * int * int)) : option (list (int * int * int)) :=
  match cs with
  | (k', a', b') :: r => if (k' =? k) && (a' =? a) && (b' =? b) then Some r else None
  | [] => None
  end.

(* [comment removed for export] *)
Definition sh_loc (t x : int) : int * int :=
  if t =? 0 then (3, (x >> 3) + shadow_K) else if t =? 1 then (2, x >> 3) else (t + 1, x >> 3).
Definition slot_byte (sl : slot) : option int := match sl with SK b => Some (b land 255) | _ => None end.
Fixpoint acc_bytes (IM : fimage) (fuel : nat) (M : itrie region) (t x : int) : bool :=
  match fuel with
  | O => true
  | S f =>
      let (ts, os) := sh_loc t x in
      match slot_byte (byte_at IM M ts os) with
      | Some b => ((b =? 0) || (((x land 7) + 1 <=? b) && (b <=? 7))) && acc_bytes IM f M t (x + 1)
      | None => false
      end
  end.
(* [comment removed for export] *)
Definition is_objb (st : i2ast) (t : int) : bool :=
  existsb (fun tn : int * int => fst tn =? t) (a_blk st) || existsb (fun tk : int * int => fst tk =? t) (a_ff st).
(* [comment removed for export] *)
Definition img_lo (A : i2aconsts) : Z := ((to_Z (ka_sh0lo A) - to_Z shadow_K) * 8)%Z.
Definition img_hi (A : i2aconsts) : Z := ((to_Z (ka_sh0len A) - to_Z shadow_K) * 8)%Z.
Definition loc_okb (A : i2aconsts) (st : i2ast) (src : bool) (t off n : int) : bool :=
  let K := ka_K A in
  let F := a_F st in
  if t =? 0 then src && (img_lo A + 64 <=? to_Z off)%Z && (to_Z off + to_Z n + 64 <=? img_hi A)%Z
  else if t =? 1 then
    match rget F 2, iget 1 (f_mem F) with
    | FV ts (W64 _ spo), Some rg1 => (ts =? 1) && (spo <=? off) && (rg_lo rg1 + 64 <=? off) && (off + n + 64 <=? c_stack K)
    | _, _ => false
    end
  else is_objb st t.
Definition range_okb (IM : fimage) (A : i2aconsts) (st : i2ast) (src : bool) (t off n : int) : bool :=
  loc_okb A st src t off n && acc_bytes IM (Z.to_nat (to_Z n)) (f_mem (a_F st)) t off.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Nodes.
Variable IM : fimage.
Variable A : i2aconsts.
Let K := ka_K A.

Definition mk (st : i2ast) (F : fstate) (n : int) (blk ff : list (int * int)) (cost cnt : int) : i2ast :=
  I2AS F n blk ff cost cnt (a_nodes st + 1) (a_cs st).
Definition mkc (st : i2ast) (F : fstate) (n : int) (blk ff : list (int * int)) (cost cnt : int) (cs : list (int * int * int)) : i2ast :=
  I2AS F n blk ff cost cnt (a_nodes st + 1) cs.

(* [comment removed for export] *)
Definition anode_malloc (st : i2ast) : option i2ast :=
  let F := a_F st in
  match call_okn K (c_mstack K) st, conc63 (rget F 10) with
  | Some (off, l), Some n =>
      match pop_cost 0 n 0 (a_cs st) with
      | Some cs =>
      if (1 <=? n) && (n <=? 32768)
         && (a_cost st + n <=? c_cost K) && (a_cost st <=? c_cost K) && (n <=? c_cost K)
         && (a_cnt st + 1 <=? c_cnt K) && (a_cnt st <=? c_cnt K)
         && chain_okb A st (ka_pc0m A) l && ro_okb K (f_mem F)
      then
        let t := a_n st in
        match drop_stack off (f_mem F) with
        | Some M1 =>
            match set_errno K (t + 16) (iset (t + 1) (sh_region false t n) (iset t (blk_region n 4 iempty) M1)) with
            | Some M2 =>
                let regs := iset 10 (FV t w_zero) (clobber clob14 (t + 2) (f_regs F)) in
                Some (mkc st (FS (ret_of l) regs M2 None) (t + 17) ((t, n) :: a_blk st) (a_ff st) (a_cost st + n) (a_cnt st + 1) cs)
            | None => None
            end
        | None => None
        end
      else None
      | None => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition anode_free (st : i2ast) : option i2ast :=
  let F := a_F st in
  match call_okn K (c_mstack K) st, base_tag (rget F 10) with
  | Some (off, l), Some tb =>
      match bsize_of tb (a_blk st), iget tb (f_mem F), iget (tb + 1) (f_mem F) with
      | Some n, Some _, Some _ =>
          match pop_cost 1 n 0 (a_cs st) with
          | Some cs =>
          if (n <=? a_cost st) && (1 <=? a_cnt st) && (4 <=? tb) && chain_okb A st (ka_pc0f A) l && ro_okb K (f_mem F) then
            let t := a_n st in
            match drop_stack off (iremove (tb + 1) (iremove tb (f_mem F))) with
            | Some M1 =>
                match set_errno K (t + 15) M1 with
                | Some M2 =>
                    Some (mkc st (FS (ret_of l) (clobber clob15 t (f_regs F)) M2 None) (t + 16) (bremove tb (a_blk st)) (a_ff st)
                              (a_cost st - n) (a_cnt st - 1) cs)
                | None => None
                end
            | None => None
            end
          else None
          | None => None
          end
      | _, _, _ => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition anode_free_null (st : i2ast) : option i2ast :=
  let F := a_F st in
  match call_okn K (c_mstack K) st, conc63 (rget F 10) with
  | Some (off, l), Some z =>
      match pop_cost 1 0 0 (a_cs st) with
      | Some cs =>
          if (z =? 0) && chain_anyb A st l && ro_okb K (f_mem F) then
            let t := a_n st in
            match drop_stack off (f_mem F) with
            | Some M1 =>
                match set_errno K (t + 15) M1 with
                | Some M2 => Some (mkc st (FS (ret_of l) (clobber clob15 t (f_regs F)) M2 None) (t + 16) (a_blk st) (a_ff st) (a_cost st) (a_cnt st) cs)
                | None => None
                end
            | None => None
            end
          else None
      | None => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition anode_realloc (st : i2ast) : option i2ast :=
  let F := a_F st in
  match call_okn K (c_mstack K) st, base_tag (rget F 10), conc63 (rget F 11) with
  | Some (off, l), Some tb, Some n' =>
      match bsize_of tb (a_blk st), iget tb (f_mem F), iget (tb + 1) (f_mem F) with
      | Some n, Some rgb, Some _ =>
          match pop_cost 2 n n' (a_cs st) with
          | Some cs =>
          if (1 <=? n') && (n' <=? 32768) && (n <=? 32768) && (4 <=? tb)
             && (a_cost st + n' <=? c_cost K) && (a_cost st <=? c_cost K) && (n' <=? c_cost K)
             && (a_cnt st + 1 <=? c_cnt K) && (a_cnt st <=? c_cnt K) && (n <=? a_cost st + n')
             && chain_okb A st (ka_pc0r A) l && ro_okb K (f_mem F)
          then
            let t := a_n st in
            let k := if n <? n' then n else n' in
            let rgn := blk_region n' 4 (copy_prefix k n' rgb) in
            match drop_stack off (iset (t + 1) (sh_region false t n') (iset t rgn (iremove (tb + 1) (iremove tb (f_mem F))))) with
            | Some M1 =>
                match set_errno K (t + 16) M1 with
                | Some M2 =>
                    let regs := iset 10 (FV t w_zero) (clobber clob14 (t + 2) (f_regs F)) in
                    Some (mkc st (FS (ret_of l) regs M2 None) (t + 17) ((t, n') :: bremove tb (a_blk st)) (a_ff st)
                              (a_cost st + n' - n) (a_cnt st) cs)
                | None => None
                end
            | None => None
            end
          else None
          | None => None
          end
      | _, _, _ => None
      end
  | _, _, _ => None
  end.

Definition write_cell (M : itrie region) (t off : int) (v : fval) : option (itrie region) :=
  match iget t M with
  | Some rg =>
      let pn := off >> 12 in let ci := (off land 4095) >> 3 in
      let p := match iget pn (rg_pages rg) with Some p => p | None => PG true PKUnk iempty end in
      if pg_wr p && (off + 8 <=? rg_len rg) then
        Some (iset t (RGK (rg_lo rg) (rg_len rg) (rg_align rg) (rg_dflt rg) (iset pn (PG true (pg_kind p) (iset ci (CV v) (pg_cells p))) (rg_pages rg))
                     (rg_clo rg) (rg_chi rg) (rg_kind rg)) M)
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition anode_memalign (st : i2ast) : option i2ast :=
  let F := a_F st in
  match call_okn K (c_mstack K) st, ptr_arg (f_mem F) (rget F 10) 8, conc63 (rget F 11), conc63 (rget F 12) with
  | Some (off, l), Some (tm, offm), Some al, Some n =>
      match log2_al al, pop_cost 3 al n (a_cs st) with
      | Some lg, Some cs =>
          if (1 <=? n) && (n <=? 32768) && ((offm land 7) =? 0) && (n <=? c_cost K)
             && (al =? 64) && (n =? 32768)                                  (* [comment removed for export] *)
             && (a_cost st + n + al <=? c_cost K) && (a_cost st <=? c_cost K)
             && (a_cnt st + 1 <=? c_cnt K) && (a_cnt st <=? c_cnt K)
             && loc_okb A st false tm offm 8
             && chain_okb A st (ka_pc0a A) l && ro_okb K (f_mem F)
          then
            let t := a_n st in
            match drop_stack off (f_mem F) with
            | Some M1 =>
                match write_cell M1 tm offm (FV t w_zero) with
                | Some M1' =>
                    match set_errno K (t + 16) (iset (t + 1) (sh_region false t n) (iset t (blk_region n lg iempty) M1')) with
                    | Some M2 =>
                        let regs := iset 10 (FV 0 w_zero) (clobber clob14 (t + 2) (f_regs F)) in
                        Some (mkc st (FS (ret_of l) regs M2 None) (t + 17) ((t, n) :: a_blk st) (a_ff st) (a_cost st + n) (a_cnt st + 1) cs)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
          else None
      | _, _ => None
      end
  | _, _, _, _ => None
  end.

(* [comment removed for export] *)
Definition anode_fsmalloc (k : int) (st : i2ast) : option i2ast :=
  let F := a_F st in
  match call_okn K (ka_fstack A) st with
  | Some (off, l) =>
      if (k <=? 6) && (of_Z (Z.of_nat (length (a_ff st))) <? ka_fsmax A) then
        let t := a_n st in
        let M1 := iset (t + 2) flag_region (iset t (ff_region k (rget F 2) (FV (t + 2) w_zero)) (f_mem F)) in
        (* [comment removed for export] *)
        let M1' := iset (t + 1) (sh_region true t (fsz k)) M1 in
        match drop_stack off M1' with
        | Some M2 =>
            let regs := iset 10 (FV t w_zero) (clobber clob14 (t + 3) (f_regs F)) in
            Some (mk st (FS (ret_of l) regs M2 None) (t + 17) (a_blk st) ((t, k) :: a_ff st) (a_cost st) (a_cnt st))
        | None => None
        end
      else None
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint ff_remove (t : int) (l : list (int * int)) : list (int * int) :=
  match l with [] => [] | (t', k) :: r => if t' =? t then r else (t', k) :: ff_remove t r end.
Definition anode_fsfree (code : itrie finstr) (st : i2ast) : option i2ast :=
  let F := a_F st in
  match iget (f_pc F) code with
  | Some (FStore sz rs1 rs2 imm) =>
      match fv_alu (f_mem F) ALU_ADD (rget F rs1) (FV 0 imm), conc63 (rget F rs2) with
      | Some (FV ft (W64 top o)), Some z =>
          if (top =? 0) && (o =? 0) && (z =? 0) && (msz_int sz =? 1) && (3 <=? ft)
             && existsb (fun tk : int * int => fst tk + 2 =? ft) (a_ff st) && resv_none F
          then
            let t := ft - 2 in
            let M' := iremove (t + 2) (iremove (t + 1) (iremove t (f_mem F))) in
            Some (mk st (FS (f_pc F + 4) (f_regs F) M' None) (a_n st) (a_blk st) (ff_remove t (a_ff st)) (a_cost st) (a_cnt st))
          else None
      | _, _ => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition anode_memset (st : i2ast) : option i2ast :=
  let F := a_F st in
  match call_okn K (ka_istack A) st, conc63 (rget F 11), conc63 (rget F 12) with
  | Some (off, l), Some c, Some n =>
      if (n <=? 65536) && (c <=? 255) then
        match ptr_arg (f_mem F) (rget F 10) n with
        | Some (t, o) =>
            if range_okb IM A st false t o n then
            match drop_stack off (f_mem F) with
            | Some M1 =>
                match fill_bytes (Z.to_nat (to_Z n)) M1 t o (c land 255) with
                | Some M2 =>
                    let tn := a_n st in
                    let regs := iset 10 (rget F 10) (clobber clob14 tn (f_regs F)) in
                    Some (mk st (FS (ret_of l) regs M2 None) (tn + 14) (a_blk st) (a_ff st) (a_cost st) (a_cnt st))
                | None => None
                end
            | None => None
            end
            else None
        | None => None
        end
      else None
  | _, _, _ => None
  end.

(* [comment removed for export] *)
Definition anode_memcpy (st : i2ast) : option i2ast :=
  let F := a_F st in
  match call_okn K (ka_istack A) st, conc63 (rget F 12) with
  | Some (off, l), Some n =>
      if n <=? 65536 then
        match ptr_arg (f_mem F) (rget F 10) n, src_arg (f_mem F) (rget F 11) n with
        | Some (td, od), Some (ts, os) =>
            if range_okb IM A st false td od n && range_okb IM A st true ts os n
               && (negb (td =? ts) || (od + n <=? os) || (os + n <=? od)) then
            match drop_stack off (f_mem F) with
            | Some M1 =>
                match copy_bytes IM (Z.to_nat (to_Z n)) M1 td od ts os with
                | Some M2 =>
                    let tn := a_n st in
                    let regs := iset 10 (rget F 10) (clobber clob14 tn (f_regs F)) in
                    Some (mk st (FS (ret_of l) regs M2 None) (tn + 14) (a_blk st) (a_ff st) (a_cost st) (a_cnt st))
                | None => None
                end
            | None => None
            end
            else None
        | _, _ => None
        end
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition strlen_span (o len : int) : int := (((o + len + 8) >> 3) << 3) - o.
Definition anode_strlen (st : i2ast) : option i2ast :=
  let F := a_F st in
  match call_okn K (ka_istack A) st, src_arg (f_mem F) (rget F 10) 1 with
  | Some (off, l), Some (t, o) =>
      match scan_strlen IM 4096 (f_mem F) t o 0 with
      | Some len =>
          match src_arg (f_mem F) (rget F 10) (strlen_span o len) with
          | Some _ =>
              if range_okb IM A st true t o (len + 1) then
              match drop_stack off (f_mem F) with
              | Some M1 =>
                  let tn := a_n st in
                  let regs := iset 10 (FV 0 (W64 0 len)) (clobber clob14 tn (f_regs F)) in
                  Some (mk st (FS (ret_of l) regs M1 None) (tn + 14) (a_blk st) (a_ff st) (a_cost st) (a_cnt st))
              | None => None
              end
              else None
          | None => None
          end
      | None => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable code : itrie finstr.
Let RO := ro_of K.

Definition awith_F (st : i2ast) (F : fstate) : i2ast := I2AS F (a_n st) (a_blk st) (a_ff st) (a_cost st) (a_cnt st) (a_nodes st) (a_cs st).
Definition abindn (code' : int) (st : i2ast) (o : option i2ast) (k : i2ast -> i2ares) : i2ares :=
  match o with Some st' => k st' | None => ARej code' st end.

Fixpoint fsm_class (pc : int) (l : list (int * int)) : option int :=
  match l with [] => None | (p, k) :: r => if p =? pc then Some k else fsm_class pc r end.

(* [comment removed for export] *)
Definition anode_at (st : i2ast) : option i2ast :=
  let pc := f_pc (a_F st) in
  if pc =? 0 then None
  else if inl pc (ka_malloc A) then anode_malloc st
  else if inl pc (ka_free A) then
         match conc63 (rget (a_F st) 10) with Some _ => anode_free_null st | None => anode_free st end
  else if inl pc (ka_realloc A) then anode_realloc st
  else if pc =? ka_memalign A then anode_memalign st
  else if pc =? ka_memset A then anode_memset st
  else if inl pc (ka_memcpy A) then anode_memcpy st
  else if pc =? ka_memmove A then anode_memcpy st
  else if pc =? ka_strlen A then anode_strlen st
  else match fsm_class pc (ka_fsm A) with Some k => anode_fsmalloc k st | None => None end.

Fixpoint i2a_run (fuel : nat) (st : i2ast) : i2ares :=
  match fuel with
  | O => ARej 90 st
  | S fuel' =>
      match fx_run IM code RO no_bp 40 (a_F st) with
      | (F', r, _) =>
          let st' := awith_F st F' in
          match r with
          | SStuck c =>
              if c =? 1 then abindn 10 st' (anode_at st') (i2a_run fuel')
              else if c =? 2 then (if is_final K code F' then ADone st' else ARej 2 st')
              else if c =? 5 then abindn 11 st' (anode_fsfree code st') (i2a_run fuel')
              else ARej (100 + c) st'
          | SEcall => ARej 3 st'
          | SBreak => ARej 4 st'
          | SFuel => ARej 5 st'
          end
      end
  end.

(* [comment removed for export] *)
Definition xw_okA (F : fstate) : bool :=
  match iget 0 (f_mem F) with
  | Some rg0 =>
      forallb (fun pp : int * page =>
                 (fst pp <? 4096) &&
                 forallb (fun kc : int * cell => (fst kc <? 512) && cell0_ok K ((fst pp << 12) + (fst kc << 3)) (snd kc))
                         (ielements (pg_cells (snd pp))))
              (ielements (rg_pages rg0))
  | None => false
  end.

Definition i2a_check (fuel : nat) (st0 : i2ast) (X : export) : bool :=
  start_ok K (st_of st0) && match a_ff st0 with [] => true | _ => false end &&
  match i2a_run fuel st0 with
  | ADone st' => xw_okA (a_F st') && export_ok K (st_of st') X && match a_ff st' with [] => true | _ => false end
                 && match a_cs st' with [] => true | _ => false end
  | ARej _ _ => false
  end.

(* [comment removed for export] *)
Definition i2a_diag (fuel : nat) (st0 : i2ast) :=
  let '(code', st) := match i2a_run fuel st0 with ADone st => (0%uint63, st) | ARej c st => (c, st) end in
  (code', f_pc (a_F st), rget (a_F st) 10, rget (a_F st) 11, rget (a_F st) 12, rget (a_F st) 2, rget (a_F st) 1,
   a_nodes st, List.length (a_blk st), List.length (a_ff st), xw_okA (a_F st), a_n st, List.length (a_cs st)).
End Nodes.

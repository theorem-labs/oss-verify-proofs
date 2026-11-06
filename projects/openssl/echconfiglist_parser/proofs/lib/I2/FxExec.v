(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import W64 ITrie FxState FxMem FxInstr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope uint63_scope.

(* [comment removed for export] *)

Definition w_ones : w64 := W64 1 9223372036854775807.
Definition w_is0 (w : w64) : bool := w_eqb w w_zero.
(* [comment removed for export] *)
Definition w_high (w : w64) : bool := negb (w_fits63 w).

(* [comment removed for export] *)
Definition fv_inb (M : itrie region) (v : fval) : bool :=
  match v with
  | FV t (W64 top off) =>
    match iget t M with
    | Some rg => ((top land 1) =? 0) && (rg_lo rg <=? off) && (off <=? rg_len rg) && (rg_len rg <=? off_bound)
    | None => false
    end
  end.

(* [comment removed for export] *)
Definition fv_nonzero (M : itrie region) (v : fval) : option bool :=
  match v with
  | FV t w =>
    if t =? 0 then Some (negb (w_eqb w w_zero))
    else if fv_inb M v then Some true
    else if (vkind t =? 1) && w_high w then
      match iget (vbase t) M with Some _ => Some true | None => None end
    else if (vkind t =? 5) && b5_nonzero M (vbase t) w then Some true
    else None
  end.

Definition fv_branch0 (M : itrie region) (c : branch_cond) (a b : fval) : option bool :=
  if (vtag a =? 0) && (vtag b =? 0) then Some (w_branch c (vw a) (vw b))
  else if vtag a =? vtag b then
    if w_eqb (vw a) (vw b) then Some (w_branch c (vw a) (vw b))          (* [comment removed for export] *)
    else match c with
         | BC_EQ | BC_NE => if is_linear (vtag a) then Some (w_branch c (vw a) (vw b)) else None
         | _ => if fv_inb M a && fv_inb M b then Some (w_branch c (vw a) (vw b)) else None
         end
  else
    (* [comment removed for export] *)
    let ptr_vs_high (p k : fval) := (vtag k =? 0) && w_high (vw k) && fv_inb M p in
    match c with
    | BC_EQ | BC_NE =>
        let nz (x y : fval) :=   (* [comment removed for export] *)
          if (vtag y =? 0) && w_eqb (vw y) w_zero then fv_nonzero M x else None in
        match (if vtag a =? 0 then nz b a else nz a b) with
        | Some true => Some (match c with BC_EQ => false | _ => true end)
        | _ => if ptr_vs_high a b || ptr_vs_high b a
               then Some (match c with BC_EQ => false | _ => true end) else None
        end
    | BC_LTU => if ptr_vs_high a b then Some true else if ptr_vs_high b a then Some false else None
    | BC_GEU => if ptr_vs_high a b then Some false else if ptr_vs_high b a then Some true else None
    | _ => None
    end.

(* [comment removed for export] *)
Definition base_align (M : itrie region) (t : int) : int :=
  match iget (vbase t) M with Some rg => rg_align rg | None => 0 end.

(* [comment removed for export] *)
Definition fv_and (M : itrie region) (a : fval) (m : w64) : option fval :=
  let t := vtag a in
  let al := base_align M t in
  if negb (al <=? 62) then None else
  let A := W64 0 ((1 << al) - 1) in
  if is_linear t then
    if w_eqb (w_alu ALU_AND m A) m then Some (FV 0 (w_alu ALU_AND (vw a) m))
    else let nm := w_alu ALU_XOR m w_ones in
         if w_eqb (w_alu ALU_AND nm A) nm then Some (FV t (w_alu ALU_AND (vw a) m)) else None
  else if ((vkind t =? 2) || (vkind t =? 4)) && w_eqb (w_alu ALU_AND m A) m && w_ltu m (W64 0 2147483648)
  then Some (FV 0 (w_alu ALU_AND (vw a) m))
  else None.

Definition fv_alu0 (M : itrie region) (op : aluop) (a b : fval) : option fval :=
  let ta := vtag a in
  let tb := vtag b in
  match op with
  | ALU_ADD =>
      if tb =? 0 then
        (if is_linear ta then Some (FV ta (w_add (vw a) (vw b)))
         else if w_is0 (vw b) then Some a else None)
      else if ta =? 0 then
        (if is_linear tb then Some (FV tb (w_add (vw a) (vw b)))
         else if w_is0 (vw a) then Some b else None)
      else if is_linear ta && (tb =? neg_tag ta) then Some (FV 0 (w_add (vw a) (vw b)))   (* [comment removed for export] *)
      else None
  | ALU_SUB =>
      if tb =? 0 then
        (if is_linear ta then Some (FV ta (w_sub (vw a) (vw b)))
         else if w_is0 (vw b) then Some a else None)
      else if ta =? tb then
        (if is_linear ta then Some (FV 0 (w_sub (vw a) (vw b)))
         else if w_eqb (vw a) (vw b) then Some (FV 0 w_zero) else None)
      else if (ta =? 0) && is_linear tb then Some (FV (neg_tag tb) (w_sub (vw a) (vw b)))   (* [comment removed for export] *)
      else None
  | ALU_XOR =>
      if (ta =? 0) && (tb =? 0) then Some (FV 0 (w_alu op (vw a) (vw b)))
      else if ta =? tb then (if w_eqb (vw a) (vw b) then Some (FV 0 w_zero) else None)
      else if tb =? 0 then
        (if w_is0 (vw b) then Some a
         else if is_linear ta && w_eqb (vw b) w_ones then Some (FV (neg_tag ta) (w_alu ALU_XOR (vw a) w_ones))
         else None)
      else if ta =? 0 then
        (if w_is0 (vw a) then Some b
         else if is_linear tb && w_eqb (vw a) w_ones then Some (FV (neg_tag tb) (w_alu ALU_XOR (vw b) w_ones))
         else None)
      else None
  | ALU_OR =>
      if (ta =? 0) && (tb =? 0) then Some (FV 0 (w_alu op (vw a) (vw b)))
      else if (tb =? 0) && w_is0 (vw b) then Some a
      else if (ta =? 0) && w_is0 (vw a) then Some b
      else None
  | ALU_AND =>
      if (ta =? 0) && (tb =? 0) then Some (FV 0 (w_alu op (vw a) (vw b)))
      else if tb =? 0 then fv_and M a (vw b)
      else if ta =? 0 then fv_and M b (vw a)
      else None
  | ALU_SLTU =>
      if (ta =? 0) && (tb =? 0) then Some (FV 0 (w_alu op (vw a) (vw b)))
      else if (ta =? 0) && w_eqb (vw a) w_zero then            (* [comment removed for export] *)
        match fv_nonzero M b with Some true => Some (FV 0 w_one) | _ => None end
      else if (tb =? 0) && w_eqb (vw b) w_one then             (* [comment removed for export] *)
        match fv_nonzero M a with Some true => Some (FV 0 w_zero) | _ => None end
      else if (ta =? tb) && fv_inb M a && fv_inb M b then Some (FV 0 (w_alu op (vw a) (vw b)))
      else if (tb =? 0) && w_high (vw b) && fv_inb M a then Some (FV 0 w_one)     (* [comment removed for export] *)
      else if (ta =? 0) && w_high (vw a) && fv_inb M b then Some (FV 0 w_zero)
      else None
  | _ =>
      if (ta =? 0) && (tb =? 0) then Some (FV 0 (w_alu op (vw a) (vw b))) else None
  end.

(* [comment removed for export] *)
Definition w_not (w : w64) : w64 := w_xor w w_ones.

Definition ptr_ival (M : itrie region) (t : int) (w : w64) : option (int * int) :=
  if fv_inb M (FV t w) then
    match iget t M, w with
    | Some rg, W64 _ off =>
        Some (if rg_clo rg <? off_bound then rg_clo rg + off else off,
              if rg_chi rg <? off_bound then rg_chi rg + off else 9223372036854775807)
    | _, _ => None
    end
  else None.

Definition fv_ival (M : itrie region) (v : fval) : option (w64 * w64) :=
  match v with
  | FV t w =>
    if t =? 0 then Some (w, w)
    else if is_plain t then
      match ptr_ival M t w with Some (lo, hi) => Some (W64 0 lo, W64 0 hi) | None => None end
    else if vkind t =? 1 then
      match ptr_ival M (vbase t) (w_not w) with
      | Some (lo, hi) => Some (w_not (W64 0 hi), w_not (W64 0 lo))
      | None => None
      end
    else None
  end.

(* [comment removed for export] *)
Definition fv_ltu_iv (M : itrie region) (a b : fval) : option bool :=
  match fv_ival M a, fv_ival M b with
  | Some (la, ha), Some (lb, hb) =>
      if w_ltu ha lb then Some true
      else if w_ltu la hb then None else Some false
  | _, _ => None
  end.

Definition fv_branch_iv (M : itrie region) (c : branch_cond) (a b : fval) : option bool :=
  let apart := match fv_ltu_iv M a b with
               | Some true => true
               | _ => match fv_ltu_iv M b a with Some true => true | _ => false end
               end in
  match c with
  | BC_LTU => fv_ltu_iv M a b
  | BC_GEU => option_map negb (fv_ltu_iv M a b)
  | BC_EQ => if apart then Some false else None
  | BC_NE => if apart then Some true else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition fv_pg_nonzero (M : itrie region) (v : fval) : bool :=
  match v with
  | FV t w =>
      if vkind t =? 6 then
        match fv_ival M (FV (vbase t) w) with
        | Some (lo, _) => w_ltu (W64 0 4095) lo
        | None => false
        end
      else false
  end.

(* [comment removed for export] *)
Definition fv_branch_pg (M : itrie region) (c : branch_cond) (a b : fval) : option bool :=
  let z (y : fval) := (vtag y =? 0) && w_eqb (vw y) w_zero in
  if (fv_pg_nonzero M a && z b) || (fv_pg_nonzero M b && z a) then
    match c with BC_EQ => Some false | BC_NE => Some true | _ => None end
  else None.

(* [comment removed for export] *)
Definition fv_inb_s (M : itrie region) (v : fval) : option region :=
  match v with
  | FV t (W64 top off) =>
    match iget t M with
    | Some rg => if ((top land 1) =? 0) && (rg_lo rg <=? off) && (off <? rg_len rg) && (rg_len rg <=? off_bound)
                 then Some rg else None
    | None => None
    end
  end.

(* [comment removed for export] *)
Definition rg_not_below (ra rb : region) : bool :=
  (rg_clo ra <? off_bound) && (rg_chi rb <? off_bound) && (rg_chi rb + rg_lo rb <? rg_clo ra + rg_len ra).

Definition fv_branch_sep (M : itrie region) (c : branch_cond) (a b : fval) : option bool :=
  if vtag a =? vtag b then None else
  match fv_inb_s M a, fv_inb_s M b with
  | Some ra, Some rb =>
      match c with
      | BC_EQ => Some false
      | BC_NE => Some true
      | BC_LTU => if rg_not_below ra rb then Some false            (* [comment removed for export] *)
                  else if rg_not_below rb ra then Some true else None
      | BC_GEU => if rg_not_below ra rb then Some true
                  else if rg_not_below rb ra then Some false else None
      | _ => None
      end
  | _, _ => None
  end.

Definition fv_branch (M : itrie region) (c : branch_cond) (a b : fval) : option bool :=
  match fv_branch0 M c a b with
  | Some r => Some r
  | None => match fv_branch_iv M c a b with
            | Some r => Some r
            | None => match fv_branch_pg M c a b with
                      | Some r => Some r
                      | None => fv_branch_sep M c a b
                      end
            end
  end.

(* [comment removed for export] *)
Definition fv_shadow (M : itrie region) (a b : fval) : option fval :=
  match a, b with
  | FV t w, FV tb wb =>
      if (tb =? 0) && w_eqb wb (W64 0 3) && fv_inb M a then
        match iget t M, iget (t + 1) M with
        | Some rg, Some rg' =>
            match rg_kind rg' with
            | RK_shadow p =>
                if (p =? t) && (3 <=? rg_align rg) && (rg_align rg <? 64)
                then Some (FV (t + 1) (w_sub (w_srl w (W64 0 3)) (W64 0 shadow_K)))
                else None
            | RK_plain => None
            end
        | _, _ => None
        end
      else None
  end.

(* [comment removed for export] *)
Definition fv_pg (a : fval) (wb : w64) : option fval :=
  match a with
  | FV t w => if is_plain t && negb (t =? 0) && w_eqb wb (W64 0 12) then Some (FV (ktag K_PG t) w) else None
  end.
Definition fv_srl (M : itrie region) (a b : fval) : option fval :=
  match b with
  | FV tb wb =>
      if tb =? 0 then
        match fv_ival M a with
        | Some (lo, hi) => if w_eqb (w_srl lo wb) (w_srl hi wb) then Some (FV 0 (w_srl lo wb)) else fv_pg a wb
        | None => fv_pg a wb
        end
      else None
  end.

(* [comment removed for export] *)
Definition fv_sl3 (a b : fval) : option fval :=
  match a, b with
  | FV t w, FV tb wb =>
      if is_plain t && negb (t =? 0) && (tb =? 0) && w_eqb wb (W64 0 3) then Some (FV (ktag K_SL3 t) w) else None
  end.

Definition fv_alu (M : itrie region) (op : aluop) (a b : fval) : option fval :=
  match fv_alu0 M op a b with
  | Some v => Some v
  | None =>
      match op with
      | ALU_SLTU => match fv_ltu_iv M a b with
                    | Some r => Some (FV 0 (if r then w_one else w_zero))
                    | None => None
                    end
      | ALU_SRL => match fv_shadow M a b with
                   | Some v => Some v
                   | None => fv_srl M a b
                   end
      | ALU_SLL => fv_sl3 a b
      | _ => None
      end
  end.

Definition fv_conc2 (f : w64 -> w64 -> w64) (a b : fval) : option fval :=
  if (vtag a =? 0) && (vtag b =? 0) then Some (FV 0 (f (vw a) (vw b))) else None.

(* [comment removed for export] *)
Definition k32 (t : int) : option int :=
  let k := vkind t in
  if k =? 0 then Some (ktag K_LO t)
  else if k =? 1 then Some (ktag K_NLO (vbase t))
  else if (k =? 2) || (k =? 4) then Some t
  else None.

(* [comment removed for export] *)
Definition fv_alu32 (op : aluop) (a b : fval) : option fval :=
  let ta := vtag a in
  let tb := vtag b in
  if (ta =? 0) && (tb =? 0) then Some (FV 0 (w_alu32 op (vw a) (vw b)))
  else match op with
  | ALU_ADD =>
      if tb =? 0 then match k32 ta with Some t' => Some (FV t' (w_add (vw a) (vw b))) | None => None end
      else if ta =? 0 then match k32 tb with Some t' => Some (FV t' (w_add (vw a) (vw b))) | None => None end
      else None
  | ALU_SUB =>
      if tb =? 0 then match k32 ta with Some t' => Some (FV t' (w_sub (vw a) (vw b))) | None => None end
      else if (ta =? tb) && is_linear ta then Some (FV 0 (w_alu32 ALU_SUB (vw a) (vw b)))
      else if (ta =? 0) && is_linear tb then
        match k32 (neg_tag tb) with Some t' => Some (FV t' (w_sub (vw a) (vw b))) | None => None end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition fv_sh32 (M : itrie region) (op : aluop) (a b : fval) : option fval :=
  match op with
  | ALU_SLL | ALU_SRL | ALU_SRA =>
      match b with
      | FV tb (W64 _ lo) =>
          if (vtag a =? 0) && (vkind tb =? K_SL3) && (2 <=? base_align M tb) && (base_align M tb <=? 62)
          then Some (FV 0 (w_alu32 op (vw a) (W64 0 ((lo land 3) << 3))))
          else None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition fv_jalr (v : fval) (imm : w64) : option int :=
  match v with
  | FV t w =>
      if t =? 0 then
        match w_jalr_target w imm with
        | W64 top lo => if ((top land 1) =? 0) && (lo <? 4611686018427387904) then Some lo else None
        end
      else None
  end.

Inductive fres : Type :=
| FNext (s : fstate)
| FEcallAt
| FStuck (code : int).

Definition awidth_sz (wd : awidth) : msize := match wd with AW => SZ4 | AD => SZ8 end.
Definition awidth_mask (wd : awidth) : int := match wd with AW => 3 | AD => 7 end.

Section WithImage.
Variable IM : fimage.
Variable code : itrie finstr.
(* [comment removed for export] *)
Variable RO : itrie unit.

Definition aligned_for (wd : awidth) (a : fval) (M : itrie region) : bool :=
  (* [comment removed for export] *)
  match a with
  | FV t (W64 _ off) =>
      ((off land awidth_mask wd) =? 0) &&
      (if t =? 0 then true else match iget t M with Some rg => 3 <=? rg_align rg | None => false end)
  end.

Definition resv_eqb (r : option fval) (a : fval) : option bool :=
  match r with
  | None => Some false
  | Some r => if vtag r =? vtag a
              then (if w_eqb (vw r) (vw a) then Some true else if is_linear (vtag a) then Some false else None)
              else None
  end.

(* [comment removed for export] *)
Definition resv_after_store (r : option fval) (a : fval) : option (option fval) :=
  match r with
  | None => Some None
  | Some rv => match resv_eqb r a with
               | Some true => Some None
               | Some false => Some (Some rv)
               | None => None
               end
  end.

(* [comment removed for export] *)
Definition is_abs (rg : region) : bool := (rg_clo rg =? 0) && (rg_chi rg =? 0).

Definition abs_find (M : itrie region) (off n : int) : option int :=
  match List.find (fun kv => is_abs (snd kv) && in_region (snd kv) off n) (ielements M) with
  | Some kv => Some (fst kv)
  | None => None
  end.

(* [comment removed for export] *)
Definition abs_addr (M : itrie region) (a : fval) (n : int) : fval :=
  match a with
  | FV t (W64 top off) =>
      if t =? 0 then
        match abs_find M off n with
        | Some t' =>
            match iget t' M with
            | Some rg => if is_abs rg && (t' <? kind_lim) then FV t' (W64 top off) else a
            | None => a
            end
        | None => a
        end
      else a
  end.

Definition fm_load_abs (M : itrie region) (a : fval) (sz : msize) (sgn : bool) : option fval :=
  match fm_load IM M a sz sgn with
  | Some v => Some v
  | None => if vtag a =? 0 then fm_load IM M (abs_addr M a (msz_int sz)) sz sgn else None
  end.

(* [comment removed for export] *)
Fixpoint ro_hitn (n : nat) (off : int) : bool :=
  match n with
  | O => false
  | S n' => match iget off RO with Some _ => true | None => ro_hitn n' (off + 1) end
  end.
Definition msz_cnt (sz : msize) : nat :=
  match sz with SZ1 => 1%nat | SZ2 => 2%nat | SZ4 => 4%nat | SZ8 => 8%nat end.
Definition ro_hit (a : fval) (sz : msize) : bool :=
  match a with
  | FV t (W64 _ off) => if t =? 0 then ro_hitn (msz_cnt sz) off else false
  end.

Definition fm_store_abs (M : itrie region) (a : fval) (sz : msize) (v : fval) : option (itrie region) :=
  if ro_hit a sz then None else
  match fm_store IM M a sz v with
  | Some M' => Some M'
  | None => if vtag a =? 0 then fm_store IM M (abs_addr M a (msz_int sz)) sz v else None
  end.

Definition fx_step (s : fstate) : fres :=
  let pc := f_pc s in
  match iget pc code with
  | None => FStuck 1
  | Some i =>
    let npc := pc + 4 in
    let M := f_mem s in
    match i with
    | FLi rd v => FNext (rset s rd (FV 0 v) npc)
    | FJal rd tgt link => FNext (rset s rd (FV 0 link) tgt)
    | FJalr rd rs1 imm link =>
        match fv_jalr (rget s rs1) imm with
        | Some tpc => FNext (rset s rd (FV 0 link) tpc)
        | None => FStuck 2
        end
    | FBranch c rs1 rs2 tgt n =>
        match fv_branch M c (rget s rs1) (rget s rs2) with
        | Some b => FNext (set_pc s (if b then tgt else n))
        | None => FStuck 3
        end
    | FLoad sz sgn rd rs1 imm =>
        match fv_alu M ALU_ADD (rget s rs1) (FV 0 imm) with
        | Some a => match fm_load_abs M a sz sgn with
                    | Some v => FNext (rset s rd v npc)
                    | None => FStuck 4
                    end
        | None => FStuck 4
        end
    | FStore sz rs1 rs2 imm =>
        match fv_alu M ALU_ADD (rget s rs1) (FV 0 imm) with
        | Some a =>
            match fm_store_abs M a sz (rget s rs2), resv_after_store (f_resv s) a with
            | Some M', Some r' => FNext (FS npc (f_regs s) M' r')
            | _, _ => FStuck 5
            end
        | None => FStuck 5
        end
    | FOpImm op rd rs1 imm =>
        match fv_alu M op (rget s rs1) (FV 0 imm) with
        | Some v => FNext (rset s rd v npc) | None => FStuck 6 end
    | FOp op rd rs1 rs2 =>
        match fv_alu M op (rget s rs1) (rget s rs2) with
        | Some v => FNext (rset s rd v npc) | None => FStuck 7 end
    | FOpImm32 op rd rs1 imm =>
        match fv_alu32 op (rget s rs1) (FV 0 imm) with
        | Some v => FNext (rset s rd v npc) | None => FStuck 8 end
    | FOp32 op rd rs1 rs2 =>
        match fv_alu32 op (rget s rs1) (rget s rs2) with
        | Some v => FNext (rset s rd v npc)
        | None => match fv_sh32 M op (rget s rs1) (rget s rs2) with
                  | Some v => FNext (rset s rd v npc) | None => FStuck 9 end
        end
    | FMul op rd rs1 rs2 =>
        match fv_conc2 (w_muldiv op) (rget s rs1) (rget s rs2) with
        | Some v => FNext (rset s rd v npc) | None => FStuck 10 end
    | FMul32 op rd rs1 rs2 =>
        match fv_conc2 (w_muldiv32 op) (rget s rs1) (rget s rs2) with
        | Some v => FNext (rset s rd v npc) | None => FStuck 11 end
    | FLr wd rd rs1 =>
        let a := rget s rs1 in
        if negb (aligned_for wd a M) then FStuck 12 else
        match fm_load_abs M a (awidth_sz wd) true with
        | Some v => let s' := rset s rd v npc in FNext (FS npc (f_regs s') (f_mem s') (Some a))
        | None => FStuck 12
        end
    | FSc wd rd rs1 rs2 =>
        let a := rget s rs1 in
        if negb (aligned_for wd a M) then FStuck 13 else
        match resv_eqb (f_resv s) a with
        | Some true =>
            match fm_store_abs M a (awidth_sz wd) (rget s rs2) with
            | Some M' => let s' := rset s rd (FV 0 w_zero) npc in FNext (FS npc (f_regs s') M' None)
            | None => FStuck 13
            end
        | Some false => let s' := rset s rd (FV 0 w_one) npc in FNext (FS npc (f_regs s') M None)
        | None => FStuck 13
        end
    | FAmo op wd rd rs1 rs2 =>
        let a := rget s rs1 in
        if negb (aligned_for wd a M) then FStuck 14 else
        match fm_load_abs M a (awidth_sz wd) true with
        | Some old =>
            let src := rget s rs2 in
            match (if (vtag old =? 0) && (vtag src =? 0)
                   then Some (FV 0 (match wd with AD => w_amo op (vw old) (vw src) | AW => w_amo32 op (vw old) (vw src) end))
                   else match op with AMO_SWAP => Some src | _ => None end),
                  resv_after_store (f_resv s) a with
            | Some nv, Some r' =>
                match fm_store_abs M a (awidth_sz wd) nv with
                | Some M' => let s' := rset s rd old npc in FNext (FS npc (f_regs s') M' r')
                | None => FStuck 14
                end
            | _, _ => FStuck 14
            end
        | None => FStuck 14
        end
    | FNop => FNext (set_pc s npc)
    | FEcall => FEcallAt
    end
  end.

(* [comment removed for export] *)
Inductive stop : Set := SFuel | SEcall | SBreak | SStuck (code : int).
Definition stop_is_fuel (r : stop) : bool := match r with SFuel => true | _ => false end.

(* [comment removed for export] *)
Fixpoint fx_run (bp : int) (k : nat) (s : fstate) : fstate * stop * int :=
  match k with
  | O => if f_pc s =? bp then (s, SBreak, 0) else
         match fx_step s with
         | FNext s' => (s', SFuel, 1)
         | FEcallAt => (s, SEcall, 0)
         | FStuck c => (s, SStuck c, 0)
         end
  | S k' =>
      match fx_run bp k' s with
      | (s1, r1, n1) =>
          if stop_is_fuel r1 then
            match fx_run bp k' s1 with
            | (s2, r2, n2) => (s2, r2, n1 + n2)
            end
          else (s1, r1, n1)
      end
  end.
End WithImage.

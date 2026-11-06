(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool String.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VAbs VStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition msize_z (sz : msize) : Z := match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint rom_read (rom : pmap Z) (a : Z) (n : nat) : option Z :=
  match n with
  | O => Some 0
  | S n' =>
      match (if Z.ltb 0 a then pm_get (Z.to_pos a) rom else None), rom_read rom (a + 1) n' with
      | Some b, Some rest => Some (b + 256 * rest)
      | _, _ => None
      end
  end.

Definition sign_adjust (signed : bool) (n : Z) (v : Z) : Z :=
  if signed && Z.leb (2 ^ (8 * n - 1)) v then v - 2 ^ (8 * n) else v.

(* [comment removed for export] *)
Definition in_ranges (l : list (Z * Z)) (a n : Z) : bool :=
  existsb (fun r : Z * Z => Z.leb (fst r) a && Z.leb (a + n) (snd r)) l.

(* [comment removed for export] *)
Definition in_cells (l : list (Z * Z)) (a n : Z) : bool :=
  existsb (fun c : Z * Z => Z.leb (fst c) a && Z.leb (a + n) (fst c + snd c)) l.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive region : Type :=
| RStack (off : lin) (lo hi : Z)       (* [comment removed for export] *)
| RData (off : lin)                    (* [comment removed for export] *)
| RImg (lo hi : Z).                    (* [comment removed for export] *)

Inductive cres : Type :=
| COk (r : region)
| CDead                                 (* [comment removed for export] *)
| CFail (msg : string).

Definition classify (P : vparams) (A : vstate) (addr : lin) (n : Z) (is_store : bool) : cres :=
  let cs := lcoef addr SP0 in let cd := lcoef addr DATA in
  if Z.eqb cs 1 && Z.eqb cd 0 then
    let off := lsub addr (lsym SP0) in
    (* [comment removed for export] *)
    if negb (qge A off (- vp_frame P)) then
      (if bnd_dead A off then CDead else CFail "stack access below window")
    else if negb (qle A off (- n)) then
      (if bnd_dead A off then CDead else CFail "stack access above sp0")
    else
      let b := bnd A off in
      match b with
      | (Some lo, Some hi) =>
          if itv_empty b then CDead
          else if is_store && negb (in_ranges (vp_wstack P) lo (hi - lo + n)) then CFail "store outside unit write set"
          else COk (RStack off lo hi)
      | _ => CFail "stack offset unbounded"   (* [comment removed for export] *)
      end
  else if Z.eqb cd 1 && Z.eqb cs 0 then
    (if is_store then CFail "store into DATA" else
     let off := lsub addr (lsym DATA) in
     if negb (qge A off 0) then (if bnd_dead A off then CDead else CFail "DATA access with negative offset")
     else if negb (qle A (lsub (laddc off n) (lsym SIZE)) 0) then
            (if bnd_dead A off then CDead else CFail "DATA access not below Size")
     else COk (RData off))
  else if negb (Z.eqb cs 0 && Z.eqb cd 0) then CFail "mixed SP0/DATA address"
  else
    let b := bnd A addr in
    if negb (lin_is_const addr) && itv_empty b then CDead else
    match b with
    | (Some lo, Some hi) =>
        if is_store then
          (if in_cells (vp_wcells P) lo (hi - lo + n) then COk (RImg lo hi) else CFail "store outside writable cells")
        else
          (if in_ranges (vp_segs P) lo (hi - lo + n) then COk (RImg lo hi) else CFail "load outside image ranges")
    | _ => CFail "unbounded absolute address"
    end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition const_slice (c : Z) (w shift n : Z) : Z :=
  Z.land (Z.shiftr (Z.land c (2 ^ (8 * w) - 1)) (8 * shift)) (2 ^ (8 * n) - 1).

Definition range_of (signed : bool) (n : Z) : itv := if signed then srange n else urange n.

Definition fresh_loaded (A : vstate) (n : Z) (signed : bool) : absval * vstate :=
  if Z.eqb n 8 then (None, A) else afresh A (range_of signed n).

(* [comment removed for export] *)
Definition table_values (P : vparams) (A : vstate) (addr : lin) (n : Z) (signed : bool) : option (list Z) :=
  match lin_single addr with
  | None => None
  | Some (s, k) =>
      match lp_bounds (vs_store A) (lsym s) with
      | (Some sl, Some sh) =>
          if Z.ltb 4096 (sh - sl) || Z.ltb sh sl then None else
          let cand := match pm_get s (vs_valset A) with
                      | Some vs => List.filter (fun x => Z.leb sl x && Z.leb x sh) vs
                      | None => zrange sl (Z.to_nat (sh - sl + 1))
                      end in
          match cand with
          | [] => None
          | _ =>
              let vals := map (fun x => match rom_read (vp_rom P) (lc addr + k * x) (Z.to_nat n) with
                                        | Some v => Some (sign_adjust signed n v) | None => None end) cand in
              if existsb (fun o => match o with None => true | Some _ => false end) vals then None
              else Some (map (fun o => match o with Some v => v | None => 0 end) vals)
          end
      | _ => None
      end
  end.

Fixpoint list_min (l : list Z) (m : Z) : Z := match l with [] => m | x :: t => list_min t (Z.min m x) end.
Fixpoint list_max (l : list Z) (m : Z) : Z := match l with [] => m | x :: t => list_max t (Z.max m x) end.
Fixpoint all_eq (l : list Z) (v : Z) : bool := match l with [] => true | x :: t => Z.eqb x v && all_eq t v end.

(* [comment removed for export] *)
Fixpoint zinsert (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | y :: t => match Z.compare x y with Lt => x :: l | Eq => l | Gt => y :: zinsert x t end
  end.
Definition zsort_dedup (l : list Z) : list Z := fold_right zinsert [] l.

(* [comment removed for export] *)
Definition const_cover (m : cellmap) (lo n : Z) : option Z :=
  match find (fun e : Z * cell =>
                match e with
                | (o2, (w2, Some v2)) => Z.leb o2 lo && Z.leb (lo + n) (o2 + w2) && lin_is_const v2
                | _ => false
                end) (cm_overlapping m lo (lo + n)) with
  | Some (o2, (w2, Some v2)) => Some (const_slice (lc v2) w2 (lo - o2) n)
  | _ => None
  end.

(* [comment removed for export] *)
Definition range_step (A : vstate) (off : lin) (lo n : Z) : Z :=
  let '(m0, r) := lin_cong (scong (vs_store A)) off in
  let m := if Z.eqb m0 0 then TWO64 else m0 in
  let step := if Z.ltb 1 m && Z.leb m n && Z.eqb ((lo - r) mod m) 0 then m else 1 in
  if Z.eqb (m mod n) 0 && Z.eqb ((lo - r) mod n) 0 && Z.ltb 1 n then n else step.

Fixpoint range_vals (m : cellmap) (o step n : Z) (signed : bool) (k : nat) : option (list Z) :=
  match k with
  | O => Some []
  | S k' =>
      match const_cover m o n, range_vals m (o + step) step n signed k' with
      | Some v, Some rest => Some (sign_adjust signed n v :: rest)
      | _, _ => None
      end
  end.

Definition range_load (A : vstate) (off : lin) (lo hi n : Z) (signed : bool) : option (list Z) :=
  let step := range_step A off lo n in
  range_vals (vs_slots A) lo step n signed (S (Z.to_nat ((hi - lo) / step))).

(* [comment removed for export] *)
Definition fresh_valset (A : vstate) (v0 : Z) (rest : list Z) (record : bool) : absval * vstate :=
  let mn := list_min rest v0 in let mx := list_max rest v0 in
  let '(s, A1) := fresh_sym A in
  let A2 := asetbox A1 s (Some mn, Some mx) in
  let A3 := if record then set_valset A2 (pm_set s (zsort_dedup (v0 :: rest)) (vs_valset A2)) else A2 in
  (Some (lsym s), A3).

Definition load_val (P : vparams) (A : vstate) (r : region) (addr : lin) (n : Z) (signed : bool) : absval * vstate :=
  match r with
  | RStack off lo hi =>
      if Z.eqb lo hi then
        match cm_get (vs_slots A) lo with
        | Some (w, Some v) =>
            if Z.eqb w n then areinterp A v n signed
            else if Z.ltb n w then atruncate A v n signed
            else fresh_loaded A n signed
        | _ =>
            (* [comment removed for export] *)
            match const_cover (vs_slots A) lo n with
            | Some v => (Some (lconst (sign_adjust signed n v)), A)
            | None => fresh_loaded A n signed
            end
        end
      else if Z.leb (hi - lo) 64 then
        match range_load A off lo hi n signed with
        | Some (v0 :: rest) =>
            if all_eq rest v0 then (Some (lconst v0), A) else fresh_valset A v0 rest true
        | _ => fresh_loaded A n signed
        end
      else fresh_loaded A n signed
  | RData _ => fresh_loaded A n signed
  | RImg lo hi =>
      if Z.eqb lo hi then
        match cm_get (vs_globs A) lo with
        | Some (w, Some v) => if Z.eqb w n then areinterp A v n signed else fresh_loaded A n signed
        | Some (_, None) => fresh_loaded A n signed
        | None =>
            match cm_overlapping (vs_globs A) lo (lo + n) with
            | [] =>
                if in_ranges (vp_pristine P) lo n then
                  match rom_read (vp_rom P) lo (Z.to_nat n) with
                  | Some v => (Some (lconst (sign_adjust signed n v)), A)
                  | None => fresh_loaded A n signed
                  end
                else fresh_loaded A n signed
            | _ => fresh_loaded A n signed
            end
        end
      else
        if in_ranges (vp_pristine P) lo (hi - lo + n) then
          match table_values P A addr n signed with
          | Some [v0] => (Some (lconst v0), A)
          | Some (v0 :: rest) => fresh_valset A v0 rest (Nat.leb (S (length rest)) 128)
          | _ => fresh_loaded A n signed
          end
        else fresh_loaded A n signed
  end.

Definition addr_of (A : vstate) (rs1 : Z) (imm : Z) : option lin :=
  match get_reg A rs1 with
  | Some e => Some (anorm A (laddc e imm))
  | None => None
  end.

Definition x_load (P : vparams) (A : vstate) (sz : msize) (signed : bool) (rd rs1 : Z) (imm : Z) : vresult :=
  let n := msize_z sz in
  match sz, signed with
  | SZ8, false => VR_fail "ld: unexpected unsigned form"
  | _, _ =>
  match addr_of A rs1 imm with
  | None => VR_fail "load via Top address"
  | Some addr =>
      match classify P A addr n false with
      | CDead => VR_next []
      | CFail m => VR_fail m
      | COk r => let '(v, A1) := load_val P A r addr n signed in one (finish A1 rd v)
      end
  end end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_zero_byte (A : vstate) (v : absval) : bool :=
  match v with
  | None => false
  | Some e => if lin_is_const e then Z.eqb (Z.land (lc e) 255) 0
              else match bnd A e with (Some lo, Some hi) => Z.eqb lo 0 && Z.eqb hi 0 | _ => false end
  end.

Definition is_zero_val (A : vstate) (v : absval) : bool :=
  match v with
  | None => false
  | Some e => if lin_is_const e then Z.eqb (zm64 (lc e)) 0
              else match bnd A e with (Some lo, Some hi) => Z.eqb lo 0 && Z.eqb hi 0 | _ => false end
  end.

(* [comment removed for export] *)
Definition kill_nul (A : vstate) (lo hi : Z) (v : absval) : vstate :=
  match vs_nul A with
  | [] => A
  | _ => if is_zero_val A v then A
         else set_nul A (List.filter (fun r : Z * Z => Z.ltb (snd r) lo || Z.ltb hi (fst r)) (vs_nul A))
  end.

Definition nul_min (l : list (Z * Z)) : list (Z * Z) :=
  List.filter (fun r => negb (existsb (fun q : Z * Z => negb (Z.eqb (fst q) (fst r) && Z.eqb (snd q) (snd r))
                                                 && Z.leb (fst r) (fst q) && Z.leb (snd q) (snd r)) l)) l.

Definition add_nul (A : vstate) (lo hi : Z) : vstate := set_nul A (nul_min ((lo, hi) :: vs_nul A)).

Definition do_store (A : vstate) (r : region) (n : Z) (v : absval) : option vstate :=
  match r with
  | RStack off lo hi =>
      let A1 :=
        if Z.eqb lo hi then
          let sl := cm_kill (vs_slots A) lo (lo + n) in
          let sl' := match v with Some e => cm_set sl lo (n, Some e) | None => sl end in
          kill_nul (set_slots A sl') lo (lo + n - 1) v
        else
          kill_nul (set_slots A (cm_kill (vs_slots A) lo (hi + n))) lo (hi + n - 1) v in
      Some (if Z.eqb n 1 && is_zero_byte A1 v then add_nul A1 lo hi else A1)
  | RImg lo hi =>
      if Z.eqb lo hi then
        Some (set_globs A (cm_set (cm_kill (vs_globs A) lo (lo + n)) lo (n, v)))
      else Some (set_globs A (cm_kill (vs_globs A) lo (hi + n)))
  | RData _ => None
  end.

Definition x_store (P : vparams) (A : vstate) (sz : msize) (rs1 rs2 : Z) (imm : Z) : vresult :=
  let n := msize_z sz in
  match addr_of A rs1 imm with
  | None => VR_fail "store via Top address"
  | Some addr =>
      match classify P A addr n true with
      | CDead => VR_next []
      | CFail m => VR_fail m
      | COk r =>
          match do_store A r n (get_reg A rs2) with
          | Some A1 => one (set_pc A1 (npc_of A))
          | None => VR_fail "store to DATA"
          end
      end
  end.

(* [comment removed for export] *)
Definition vstep (P : vparams) (A : vstate) (i : instr) : vresult :=
  vstep_core (x_load P) (x_store P) A i.

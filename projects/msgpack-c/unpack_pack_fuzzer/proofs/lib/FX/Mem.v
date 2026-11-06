(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val.
Open Scope Z_scope.
Unset Lia Cache.

Module Mem.

Record cell := Cell { c_idx : int; c_w : int; c_v : sv }.
Definition slot := list cell.

Record gran := Gran { g_dirty : bool; g_cells : slot }.

Inductive bg : Type :=
| BGNone
| BGZero
| BGImage
| BGUnk
| BGBlob (j : int) (shift : int).

Record region := Region {
  rg_lo : int;
  rg_hi : sv;
  rg_w : bool;
  rg_bg : bg;
  rg_cells : IMap.t gran
}.

Definition okey (o : w64) : option int :=
  if wt o then (if PrimInt63.leb bit62i (wl o) then Some (wl o) else None)
  else (if PrimInt63.ltb (wl o) bit62i then Some (wl o) else None).

Definition keyZ (i : int) : Z := if PrimInt63.ltb i bit62i then to_Z i else to_Z i - two63.

Definition kltb (a b : int) : bool := PrimInt63.ltb (PrimInt63.lxor a bit62i) (PrimInt63.lxor b bit62i).
Definition kleb (a b : int) : bool := negb (kltb b a).

Definition hi3 : int := 8070450532247928832%uint63.

Definition granule (i : int) : int :=
  let q := PrimInt63.lsr i 3%uint63 in
  if PrimInt63.ltb i bit62i then q else PrimInt63.lor q hi3.
Definition gidx (i : int) : int := PrimInt63.land i 7%uint63.

Fixpoint overlapping (s : slot) (i w : int) : list cell :=
  match s with
  | [] => []
  | c :: s' =>
      let ce := PrimInt63.add (c_idx c) (c_w c) in
      let e := PrimInt63.add i w in
      if PrimInt63.leb ce i then overlapping s' i w
      else if PrimInt63.leb e (c_idx c) then []
      else c :: overlapping s' i w
  end.

Fixpoint cut (s : slot) (i w : int) : slot :=
  match s with
  | [] => []
  | c :: s' =>
      let ci := c_idx c in let cw := c_w c in
      let ce := PrimInt63.add ci cw in
      let e := PrimInt63.add i w in
      if PrimInt63.leb ce i then c :: cut s' i w
      else if PrimInt63.leb e ci then c :: s'
      else
        let left := if PrimInt63.ltb ci i
                    then [Cell ci (PrimInt63.sub i ci) (sv_ext false 0%uint63 (PrimInt63.sub i ci) (c_v c))]
                    else [] in
        let right := if PrimInt63.ltb e ce
                     then [Cell e (PrimInt63.sub ce e)
                             (sv_ext false (PrimInt63.sub e ci) (PrimInt63.sub ce e) (c_v c))]
                     else [] in
        left ++ right ++ cut s' i w
  end.

Fixpoint insert_sorted (c : cell) (s : slot) : slot :=
  match s with
  | [] => [c]
  | c' :: s' => if PrimInt63.ltb (c_idx c) (c_idx c') then c :: s else c' :: insert_sorted c s'
  end.

Definition slot_store (s : slot) (i w : int) (v : sv) : slot :=
  insert_sorted (Cell i w v) (cut s i w).

Section WithSegs.
Variable segs : list Segment.

Fixpoint img_bytes (a : Z) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' =>
      match memory_read segs (Z_to_bv 64 a) 1 with
      | Some (b :: _) =>
          match img_bytes (a + 1) n' with
          | Some bs => Some (b :: bs)
          | None => None
          end
      | _ => None
      end
  end.

Fixpoint bytes_to_int (bs : list byte) : int :=
  match bs with
  | [] => 0%uint63
  | b :: bs' => PrimInt63.lor (of_Z (bv_unsigned b)) (PrimInt63.lsl (bytes_to_int bs') 8%uint63)
  end.

Definition bytes_to_w64 (bs : list byte) : w64 :=
  match bs with
  | [b0;b1;b2;b3;b4;b5;b6;b7] =>
      let lo7 := bytes_to_int [b0;b1;b2;b3;b4;b5;b6] in
      let top := Z.leb 128 (bv_unsigned b7) in
      let b7l := of_Z (Z.land (bv_unsigned b7) 127) in
      W64 top (PrimInt63.lor lo7 (PrimInt63.lsl b7l 56%uint63))
  | _ => W64 false (bytes_to_int bs)
  end.

Definition two62Z : Z := 4611686018427387904.
Definition abs_readable (a : Z) (n : Z) : bool :=
  Z.ltb (a + n) two62Z &&
  match img_bytes a (Z.to_nat n) with Some _ => true | None => false end.
Fixpoint abs_writable_bytes (a : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match find_segment segs a 1 with
      | Some seg => seg_writable seg && seg_readable seg &&
                    match segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg))) with
                    | Some _ => true | None => false end
      | None => false
      end && abs_writable_bytes (a + 1) n'
  end.
Definition abs_writable (a : Z) (n : Z) : bool := Z.ltb (a + n) two62Z && abs_writable_bytes a (Z.to_nat n).

Definition bg_value (k : int) (r : region) (o : int) (w : int) : option sv :=
  match rg_bg r with
  | BGNone => None
  | BGZero => Some (VL wzero)
  | BGImage =>
      if PrimInt63.ltb o bit62i then
        match img_bytes (to_Z o) (Z.to_nat (to_Z w)) with
        | Some bs => Some (VL (bytes_to_w64 bs))
        | None => None
        end
      else None
  | BGUnk => Some (VBg false k (W64 (negb (PrimInt63.ltb o bit62i)) o) w)

  | BGBlob j shift =>
      if PrimInt63.ltb o bit62i && PrimInt63.leb shift o && PrimInt63.ltb shift bit62i
      then Some (VBlob false j (vlit (PrimInt63.sub o shift)) w)
      else None
  end.

Definition rotab := IMap.t (w64 * bool).

Definition wok_b (w : int) : bool :=
  PrimInt63.eqb w 1%uint63 || PrimInt63.eqb w 2%uint63 || PrimInt63.eqb w 4%uint63 || PrimInt63.eqb w 8%uint63.

Definition rot_find (rot : rotab) (o w : int) : option (w64 * bool) :=
  if PrimInt63.ltb o bit62i && PrimInt63.leb w 8%uint63 && PrimInt63.leb (PrimInt63.add (gidx o) w) 8%uint63
  then IMap.find (granule o) rot else None.

Definition rot_lookup (rot : rotab) (o w : int) : option w64 :=
  if wok_b w then
    match rot_find rot o w with Some (wd, _) => Some (wext false (gidx o) w wd) | None => None end
  else None.
Definition abs_readable_r (rot : rotab) (o w : int) : bool :=
  match rot_find rot o w with Some _ => true | None => abs_readable (to_Z o) (to_Z w) end.
Definition abs_writable_r (rot : rotab) (o w : int) : bool :=
  match rot_find rot o w with Some (_, true) => true | _ => abs_writable (to_Z o) (to_Z w) end.
Definition bg_value_r (rot : rotab) (k : int) (r : region) (o : int) (w : int) : option sv :=
  match rg_bg r with
  | BGImage => match rot_lookup rot o w with
               | Some wd => Some (VL wd)
               | None => bg_value k r o w
               end
  | _ => bg_value k r o w
  end.

Fixpoint build_rot (gs : list int) (acc : rotab) : rotab :=
  match gs with
  | [] => acc
  | g :: gs' =>
      let a := 8 * to_Z g in
      let acc' := match img_bytes a 8 with
                  | Some bs => if Z.ltb (a + 8) two62Z then IMap.add g (bytes_to_w64 bs, abs_writable a 8) acc else acc
                  | None => acc
                  end in
      build_rot gs' acc'
  end.

Fixpoint gkeys_from (g : int) (n : nat) : list int :=
  match n with O => [] | S n' => g :: gkeys_from (PrimInt63.add g 1%uint63) n' end.

Definition assemble (base : option sv) (cs : list cell) (i w : int) : option sv :=

  let fix go (cs : list cell) (pos : int) (acc : option sv) (tiled : bool) : option sv :=
    match cs with
    | [] => if tiled && negb (PrimInt63.eqb pos (PrimInt63.add i w)) then None else acc
    | c :: cs' =>
        let ci := c_idx c in let cw := c_w c in
        let lo := if PrimInt63.ltb ci i then i else ci in
        let hi := let ce := PrimInt63.add ci cw in let e := PrimInt63.add i w in
                  if PrimInt63.ltb ce e then ce else e in
        if tiled && negb (PrimInt63.eqb lo pos) then None else
        let piece := sv_ext false (PrimInt63.sub lo ci) (PrimInt63.sub hi lo) (c_v c) in
        let acc' := match acc with
                    | Some a => Some (sv_ins (PrimInt63.sub lo i) (PrimInt63.sub hi lo) a piece)
                    | None => None
                    end in
        go cs' hi acc' tiled
    end in
  match base with
  | Some b => go cs i (Some b) false
  | None => go cs i (Some (VL wzero)) true
  end.

Definition region_load1 (k : int) (r : region) (o : int) (w : int) (sx : bool) : option sv :=
  let g := granule o in let i := gidx o in
  let '(dirty, s) := match IMap.find g (rg_cells r) with Some (Gran d s) => (d, s) | None => (false, []) end in
  let bgv := if dirty then None else bg_value k r o w in
  match overlapping s i w with
  | [] => match bgv with
          | Some v => Some (sv_ext sx 0%uint63 w v)
          | None => None
          end
  | [c] =>
      if PrimInt63.leb (c_idx c) i && PrimInt63.leb (PrimInt63.add i w) (PrimInt63.add (c_idx c) (c_w c))
      then Some (sv_ext sx (PrimInt63.sub i (c_idx c)) w (c_v c))
      else
        match assemble bgv [c] i w with
        | Some v => Some (sv_ext sx 0%uint63 w v)
        | None => None
        end
  | cs =>
      match assemble bgv cs i w with
      | Some v => Some (sv_ext sx 0%uint63 w v)
      | None => None
      end
  end.

Definition region_load1_r (rot : rotab) (k : int) (r : region) (o : int) (w : int) (sx : bool) : option sv :=
  let g := granule o in let i := gidx o in
  let '(dirty, s) := match IMap.find g (rg_cells r) with Some (Gran d s) => (d, s) | None => (false, []) end in
  let bgv := if dirty then None else bg_value_r rot k r o w in
  match overlapping s i w with
  | [] => match bgv with
          | Some v => Some (sv_ext sx 0%uint63 w v)
          | None => None
          end
  | [c] =>
      if PrimInt63.leb (c_idx c) i && PrimInt63.leb (PrimInt63.add i w) (PrimInt63.add (c_idx c) (c_w c))
      then Some (sv_ext sx (PrimInt63.sub i (c_idx c)) w (c_v c))
      else
        match assemble bgv [c] i w with
        | Some v => Some (sv_ext sx 0%uint63 w v)
        | None => None
        end
  | cs =>
      match assemble bgv cs i w with
      | Some v => Some (sv_ext sx 0%uint63 w v)
      | None => None
      end
  end.

Definition region_store1 (r : region) (o : int) (w : int) (v : sv) : region :=
  let g := granule o in let i := gidx o in
  let '(dirty, s) := match IMap.find g (rg_cells r) with Some (Gran d s) => (d, s) | None => (false, []) end in
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r) (IMap.add g (Gran dirty (slot_store s i w v)) (rg_cells r)).

Definition in_granule (o w : int) : bool := PrimInt63.leb (PrimInt63.add (gidx o) w) 8%uint63.

Definition region_load (k : int) (r : region) (o : int) (w : int) (sx : bool) : option sv :=
  if in_granule o w then region_load1 k r o w sx
  else
    let w1 := PrimInt63.sub 8%uint63 (gidx o) in
    let w2 := PrimInt63.sub w w1 in
    match region_load1 k r o w1 false, region_load1 k r (PrimInt63.add o w1) w2 false with
    | Some lo, Some hi => Some (sv_ext sx 0%uint63 w (sv_ins w1 w2 lo hi))
    | _, _ => None
    end.

Definition region_load_r (rot : rotab) (k : int) (r : region) (o : int) (w : int) (sx : bool) : option sv :=
  if in_granule o w then region_load1_r rot k r o w sx
  else
    let w1 := PrimInt63.sub 8%uint63 (gidx o) in
    let w2 := PrimInt63.sub w w1 in
    match region_load1_r rot k r o w1 false, region_load1_r rot k r (PrimInt63.add o w1) w2 false with
    | Some lo, Some hi => Some (sv_ext sx 0%uint63 w (sv_ins w1 w2 lo hi))
    | _, _ => None
    end.

Definition region_store (r : region) (o : int) (w : int) (v : sv) : region :=
  if in_granule o w then region_store1 r o w v
  else
    let w1 := PrimInt63.sub 8%uint63 (gidx o) in
    let w2 := PrimInt63.sub w w1 in
    region_store1 (region_store1 r o w1 v) (PrimInt63.add o w1) w2 (sv_ext false w1 w2 v).

Fixpoint dirty_range (glo : int) (n : nat) (m : IMap.t gran) : IMap.t gran :=
  match n with
  | O => m
  | S n' => dirty_range (PrimInt63.add glo 1%uint63) n' (IMap.add glo (Gran true []) m)
  end.

Definition is_bgnone (b : bg) : bool := match b with BGNone => true | _ => false end.

Definition region_forget (r : region) (glo ghi : int) : region :=
  if is_bgnone (rg_bg r) then
    Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r) (IMap.remove_range glo ghi (rg_cells r))
  else
  let gs := IMap.find_range glo ghi (rg_cells r) in
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r)
         (fold_left (fun m kv => IMap.add (fst kv) (Gran true []) m) gs (rg_cells r)).

End WithSegs.
End Mem.

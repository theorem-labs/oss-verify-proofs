(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition HS_WORDS_Z : list Z := [
  0x00200613; 0x14c5ea63; 0x00100613; 0x00100693; 0x00c0006f; 0x00160613; 0x12b60c63; 0x00461713;
  0x00e50733; 0x00072703; 0x00060893; 0xfff88793; 0x0017d813; 0x00481293; 0x005502b3; 0x0002a303;
  0xfce37ae3; 0x0002b303; 0x00489893; 0x011508b3; 0x0048a383; 0x0068b023; 0x0082b303; 0x0088be03;
  0x0068b423; 0x00e2a023; 0x0072a223; 0x01c2b423; 0x00080893; 0xfaf6ece3; 0xf9dff06f; 0x00000613;
  0x00459693; 0x00d506b3; 0x0006b703; 0x0086b783; 0x00053803; 0x00853883; 0x00e53023; 0x00f53423;
  0x0106b023; 0x0116b423; 0x00000693; 0x00161793; 0x00178813; 0x00461713; 0x00b86a63; 0x00278793;
  0x02b7ea63; 0x04c69c63; 0x0880006f; 0x00e506b3; 0x00481893; 0x011508b3; 0x0006a683; 0x0008a883;
  0x0116e463; 0x00060813; 0x00080693; 0x00278793; 0xfcb7fae3; 0x00469813; 0x00479893; 0x01050833;
  0x011508b3; 0x00082803; 0x0008a883; 0x01186463; 0x00068793; 0x00078693; 0x02c78c63; 0x00469613;
  0x00c50633; 0x00063783; 0x00e50733; 0x00073803; 0x00873883; 0x00f73023; 0x00863783; 0x00f73423;
  0x01063023; 0x01163423; 0x00068613; 0xf6b6e0e3; 0xfff58593; 0xf20594e3; 0x00008067
].

Definition HS_WORDS : list (bv 32) := map (Z_to_bv 32) HS_WORDS_Z.

Definition HS_CODE : list instr := [
  OpImm ALU_ADD 12 0 2;
  Branch BC_LTU 11 12 340;
  OpImm ALU_ADD 12 0 1;
  OpImm ALU_ADD 13 0 1;
  Jal 0 12;
  OpImm ALU_ADD 12 12 1;
  Branch BC_EQ 12 11 312;
  ShiftImm ALU_SLL 14 12 4;
  Op ALU_ADD 14 10 14;
  (Load SZ4 true 14 14 0);
  OpImm ALU_ADD 17 12 0;
  OpImm ALU_ADD 15 17 4095;
  ShiftImm ALU_SRL 16 15 1;
  ShiftImm ALU_SLL 5 16 4;
  Op ALU_ADD 5 10 5;
  (Load SZ4 true 6 5 0);
  Branch BC_GEU 6 14 8148;
  (Load SZ8 true 6 5 0);
  ShiftImm ALU_SLL 17 17 4;
  Op ALU_ADD 17 10 17;
  (Load SZ4 true 7 17 4);
  Store SZ8 17 6 0;
  (Load SZ8 true 6 5 8);
  (Load SZ8 true 28 17 8);
  Store SZ8 17 6 8;
  Store SZ4 5 14 0;
  Store SZ4 5 7 4;
  Store SZ8 5 28 8;
  OpImm ALU_ADD 17 16 0;
  Branch BC_LTU 13 15 8120;
  Jal 0 2097052;
  OpImm ALU_ADD 12 0 0;
  ShiftImm ALU_SLL 13 11 4;
  Op ALU_ADD 13 10 13;
  (Load SZ8 true 14 13 0);
  (Load SZ8 true 15 13 8);
  (Load SZ8 true 16 10 0);
  (Load SZ8 true 17 10 8);
  Store SZ8 10 14 0;
  Store SZ8 10 15 8;
  Store SZ8 13 16 0;
  Store SZ8 13 17 8;
  OpImm ALU_ADD 13 0 0;
  ShiftImm ALU_SLL 15 12 1;
  OpImm ALU_ADD 16 15 1;
  ShiftImm ALU_SLL 14 12 4;
  Branch BC_LTU 16 11 20;
  OpImm ALU_ADD 15 15 2;
  Branch BC_LTU 15 11 52;
  Branch BC_NE 13 12 88;
  Jal 0 136;
  Op ALU_ADD 13 10 14;
  ShiftImm ALU_SLL 17 16 4;
  Op ALU_ADD 17 10 17;
  (Load SZ4 true 13 13 0);
  (Load SZ4 true 17 17 0);
  Branch BC_LTU 13 17 8;
  OpImm ALU_ADD 16 12 0;
  OpImm ALU_ADD 13 16 0;
  OpImm ALU_ADD 15 15 2;
  Branch BC_GEU 15 11 8148;
  ShiftImm ALU_SLL 16 13 4;
  ShiftImm ALU_SLL 17 15 4;
  Op ALU_ADD 16 10 16;
  Op ALU_ADD 17 10 17;
  (Load SZ4 true 16 16 0);
  (Load SZ4 true 17 17 0);
  Branch BC_LTU 16 17 8;
  OpImm ALU_ADD 15 13 0;
  OpImm ALU_ADD 13 15 0;
  Branch BC_EQ 15 12 56;
  ShiftImm ALU_SLL 12 13 4;
  Op ALU_ADD 12 10 12;
  (Load SZ8 true 15 12 0);
  Op ALU_ADD 14 10 14;
  (Load SZ8 true 16 14 0);
  (Load SZ8 true 17 14 8);
  Store SZ8 14 15 0;
  (Load SZ8 true 15 12 8);
  Store SZ8 14 15 8;
  Store SZ8 12 16 0;
  Store SZ8 12 17 8;
  OpImm ALU_ADD 12 13 0;
  Branch BC_LTU 13 11 8032;
  OpImm ALU_ADD 11 11 4095;
  Branch BC_NE 11 0 7976;
  Jalr 0 1 0].

Definition HS_N : nat := 87.

Definition rk (r : reg) : positive := Z.to_pos (bv_unsigned r + 1).

Inductive zi : Type :=
| ZAddi (rd rs : positive) (im : Z) | ZSlli (rd rs : positive) (sh : Z) | ZSrli (rd rs : positive) (sh : Z)
| ZAdd (rd r1 r2 : positive) | ZLw (rd rs : positive) (im : Z) | ZLd (rd rs : positive) (im : Z)
| ZSw (r1 r2 : positive) (im : Z) | ZSd (r1 r2 : positive) (im : Z)
| ZBltu (r1 r2 : positive) (im : Z) | ZBgeu (r1 r2 : positive) (im : Z)
| ZBeq (r1 r2 : positive) (im : Z) | ZBne (r1 r2 : positive) (im : Z)
| ZJ (im : Z) | ZJr (rs : positive) (im : Z) | ZBad.

Definition tozi (i : instr) : zi :=
  match i with
  | OpImm ALU_ADD rd rs imm => ZAddi (rk rd) (rk rs) (bv_signed imm)
  | ShiftImm ALU_SLL rd rs sh => ZSlli (rk rd) (rk rs) (bv_unsigned sh)
  | ShiftImm ALU_SRL rd rs sh => ZSrli (rk rd) (rk rs) (bv_unsigned sh)
  | Op ALU_ADD rd r1 r2 => ZAdd (rk rd) (rk r1) (rk r2)
  | Load SZ4 true rd rs imm => ZLw (rk rd) (rk rs) (bv_signed imm)
  | Load SZ8 true rd rs imm => ZLd (rk rd) (rk rs) (bv_signed imm)
  | Store SZ4 r1 r2 imm => ZSw (rk r1) (rk r2) (bv_signed imm)
  | Store SZ8 r1 r2 imm => ZSd (rk r1) (rk r2) (bv_signed imm)
  | Branch BC_LTU r1 r2 imm => ZBltu (rk r1) (rk r2) (bv_signed imm)
  | Branch BC_GEU r1 r2 imm => ZBgeu (rk r1) (rk r2) (bv_signed imm)
  | Branch BC_EQ r1 r2 imm => ZBeq (rk r1) (rk r2) (bv_signed imm)
  | Branch BC_NE r1 r2 imm => ZBne (rk r1) (rk r2) (bv_signed imm)
  | Jal rd imm => if bv_eqb rd 0 then ZJ (bv_signed imm) else ZBad
  | Jalr rd rs imm => if bv_eqb rd 0 then ZJr (rk rs) (bv_signed imm) else ZBad
  | _ => ZBad
  end.

Fixpoint mkzt (l : list zi) (k : positive) (t : tree zi) : tree zi :=
  match l with [] => t | i :: r => mkzt r (Pos.succ k) (tset k i t) end.

Definition ZT : tree zi := Eval vm_compute in mkzt (map tozi HS_CODE) 1 TEmpty.
Lemma ZT_eq : ZT = mkzt (map tozi HS_CODE) 1 TEmpty. Proof. vm_compute. reflexivity. Qed.

Record zst : Type := ZS { z_pc : Z; z_regs : tree Z; z_tbl : list (list Z) }.

Definition zg (m : tree Z) (k : positive) : option Z := match k with xH => Some 0 | _ => tget k m end.
Definition zset (m : tree Z) (k : positive) (v : Z) : tree Z := match k with xH => m | _ => tset k v m end.

Definition hs_two64 : Z := 18446744073709551616.
Definition hs_m32 : Z := 4294967296.

Definition w64 (z : Z) : Z := if Z.ltb z 0 then z + hs_two64 else if Z.leb hs_two64 z then z - hs_two64 else z.

Definition sx32 (v : Z) : Z := if Z.leb 2147483648 v then v + (hs_two64 - hs_m32) else v.

Fixpoint le (bs : list Z) : Z := match bs with [] => 0 | b :: t => Z.lor b (Z.shiftl (le t) 8) end.
Fixpoint tole (n : nat) (z : Z) : list Z := match n with O => [] | S n' => Z.land z 255 :: tole n' (Z.shiftr z 8) end.

Definition zld (T : Z) (tbl : list (list Z)) (a : Z) (n : nat) : option (list Z) :=
  let d := a - T in let r := d / 16 in let o := d mod 16 in
  if (Z.leb 0 d && Z.ltb r (Z.of_nat (length tbl)) && Z.leb (o + Z.of_nat n) 16)%bool
  then Some (firstn n (skipn (Z.to_nat o) (nth (Z.to_nat r) tbl []))) else None.

Fixpoint lupd {A} (l : list A) (r : nat) (f : A -> A) : list A :=
  match l, r with
  | [], _ => []
  | h :: t, O => f h :: t
  | h :: t, S r' => h :: lupd t r' f
  end.

Definition splice (o : nat) (bs rec : list Z) : list Z := firstn o rec ++ bs ++ skipn (o + length bs) rec.

Definition zstt (T : Z) (tbl : list (list Z)) (a : Z) (bs : list Z) : option (list (list Z)) :=
  let d := a - T in let r := d / 16 in let o := d mod 16 in
  if (Z.leb 0 d && Z.ltb r (Z.of_nat (length tbl)) && Z.leb (o + Z.of_nat (length bs)) 16)%bool
  then Some (lupd tbl (Z.to_nat r) (splice (Z.to_nat o) bs)) else None.

Definition zexec (T : Z) (i : zi) (st : zst) : option zst :=
  let pc := z_pc st in let m := z_regs st in let tbl := z_tbl st in
  let npc := w64 (pc + 4) in
  match i with
  | ZAddi rd rs im => match zg m rs with Some x => Some (ZS npc (zset m rd (w64 (x + im))) tbl) | None => None end
  | ZSlli rd rs sh => match zg m rs with Some x => Some (ZS npc (zset m rd (Z.land (Z.shiftl x sh) (hs_two64 - 1))) tbl) | None => None end
  | ZSrli rd rs sh => match zg m rs with Some x => Some (ZS npc (zset m rd (Z.shiftr x sh)) tbl) | None => None end
  | ZAdd rd r1 r2 =>
      match zg m r1, zg m r2 with Some x, Some y => Some (ZS npc (zset m rd (w64 (x + y))) tbl) | _, _ => None end
  | ZLw rd rs im =>
      match zg m rs with
      | Some x => match zld T tbl (w64 (x + im)) 4 with
                  | Some bs => Some (ZS npc (zset m rd (sx32 (le bs))) tbl) | None => None end
      | None => None end
  | ZLd rd rs im =>
      match zg m rs with
      | Some x => match zld T tbl (w64 (x + im)) 8 with
                  | Some bs => Some (ZS npc (zset m rd (le bs)) tbl) | None => None end
      | None => None end
  | ZSw r1 r2 im =>
      match zg m r1, zg m r2 with
      | Some x, Some y => match zstt T tbl (w64 (x + im)) (tole 4 y) with
                          | Some tbl' => Some (ZS npc m tbl') | None => None end
      | _, _ => None end
  | ZSd r1 r2 im =>
      match zg m r1, zg m r2 with
      | Some x, Some y => match zstt T tbl (w64 (x + im)) (tole 8 y) with
                          | Some tbl' => Some (ZS npc m tbl') | None => None end
      | _, _ => None end
  | ZBltu r1 r2 im => match zg m r1, zg m r2 with
      | Some x, Some y => Some (ZS (if Z.ltb x y then w64 (pc + im) else npc) m tbl) | _, _ => None end
  | ZBgeu r1 r2 im => match zg m r1, zg m r2 with
      | Some x, Some y => Some (ZS (if Z.ltb x y then npc else w64 (pc + im)) m tbl) | _, _ => None end
  | ZBeq r1 r2 im => match zg m r1, zg m r2 with
      | Some x, Some y => Some (ZS (if Z.eqb x y then w64 (pc + im) else npc) m tbl) | _, _ => None end
  | ZBne r1 r2 im => match zg m r1, zg m r2 with
      | Some x, Some y => Some (ZS (if Z.eqb x y then npc else w64 (pc + im)) m tbl) | _, _ => None end
  | ZJ im => Some (ZS (w64 (pc + im)) m tbl)
  | ZJr rs im => match zg m rs with Some x => Some (ZS (w64 (Z.land (x + im) (-2))) m tbl) | None => None end
  | ZBad => None
  end.

Definition zfetch (p : Z) (pc : Z) : option zi :=
  let off := pc - p in
  if (Z.leb 0 off && Z.eqb (off mod 4) 0)%bool then tget (Z.to_pos (off / 4 + 1)) ZT else None.

Inductive hres : Type := HDone (st : zst) | HMore (st : zst) | HFail.

Fixpoint hs_steps (p T : Z) (fuel : nat) (st : zst) : hres :=
  match fuel with
  | O => HMore st
  | S f =>
      match zfetch p (z_pc st) with
      | Some i => match zexec T i st with Some st' => hs_steps p T f st' | None => HFail end
      | None => HDone st
      end
  end.

Definition HS_CHUNK : nat := 1024.

Fixpoint hs_run (p T : Z) (fuel : nat) (st : zst) : option zst :=
  match fuel with
  | O => None
  | S f => match hs_steps p T HS_CHUNK st with
           | HDone st' => Some st'
           | HMore st' => hs_run p T f st'
           | HFail => None
           end
  end.

Definition hs_regs0 (ret T n : Z) : tree Z := tset 12 n (tset 11 T (tset 2 ret TEmpty)).

Fixpoint chunk16 (n : nat) (l : list Z) : list (list Z) :=
  match n with O => [] | S n' => firstn 16 l :: chunk16 n' (skipn 16 l) end.

Definition HS_DSTS : list nat := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28]%nat.

Definition hs_words (tbl : list (list Z)) : list Z := concat (map (fun rec => [le (firstn 8 rec); le (firstn 8 (skipn 8 rec))]) tbl).

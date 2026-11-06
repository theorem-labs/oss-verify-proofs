(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxNum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rkey (r : reg) : positive := bv_key r.

Inductive xi : Type :=
| XAluI (op : aluop) (rd rs : positive) (imm : Z)      (* [comment removed for export] *)
| XAlu (op : aluop) (rd rs1 rs2 : positive)
| XAluIW (op : aluop) (rd rs : positive) (imm : Z)     (* [comment removed for export] *)
| XAluW (op : aluop) (rd rs1 rs2 : positive)
| XMul (op : mulop) (rd rs1 rs2 : positive)
| XMulW (op : mulop) (rd rs1 rs2 : positive)
| XLi (rd : positive) (v : Z)                          (* [comment removed for export] *)
| XJal (rd : positive) (tgt link : Z)
| XJalr (rd rs : positive) (imm link : Z)
| XBr (c : branch_cond) (rs1 rs2 : positive) (tgt : Z)
| XLd (sz : msize) (sg : bool) (rd rs : positive) (imm : Z)
| XSt (sz : msize) (rs1 rs2 : positive) (imm : Z)
| XFence
| XLr (wd : awidth) (rd rs : positive)                       (* [comment removed for export] *)
| XSc (wd : awidth) (rd rs1 rs2 : positive)                  (* [comment removed for export] *)
| XAmo (op : amoop) (wd : awidth) (rd rs1 rs2 : positive)    (* [comment removed for export] *)
| XFLd (fmt : ffmt) (rs : positive) (imm : Z)                (* [comment removed for export] *)
| XFSt (fmt : ffmt) (rs : positive) (imm : Z)                (* [comment removed for export] *)
| XFInt (rd : positive) (cmp : bool)                         (* [comment removed for export] *)
| XFOp                                                       (* [comment removed for export] *)
| XEcall
| XOther.

(* [comment removed for export] *)
Definition rm_okb (rm : bv 3) : bool := (Z.leb (bv_unsigned rm) 4 || Z.eqb (bv_unsigned rm) 7)%bool.
Definition fcvt_x (dst src : fcvt_ty) (rd : positive) : xi :=
  match dst with
  | FC_S | FC_D => XFOp
  | _ => match src with FC_S | FC_D => XFInt rd false | _ => XOther end
  end.

Definition xlate (pc : Z) (i : instr) : xi :=
  match i with
  | OpImm op rd rs imm => XAluI op (rkey rd) (rkey rs) (bv_unsigned (sext 64 imm))
  | ShiftImm op rd rs sh => XAluI op (rkey rd) (rkey rs) (bv_unsigned (zext 64 sh))
  | Op op rd rs1 rs2 => XAlu op (rkey rd) (rkey rs1) (rkey rs2)
  | OpImm32 rd rs imm => XAluIW ALU_ADD (rkey rd) (rkey rs) (bv_unsigned (sext 32 imm))
  | ShiftImm32 op rd rs sh => XAluIW op (rkey rd) (rkey rs) (bv_unsigned (zext 32 sh))
  | Op32 op rd rs1 rs2 => XAluW op (rkey rd) (rkey rs1) (rkey rs2)
  | Mul op rd rs1 rs2 => XMul op (rkey rd) (rkey rs1) (rkey rs2)
  | Mul32 op rd rs1 rs2 => XMulW op (rkey rd) (rkey rs1) (rkey rs2)
  | Lui rd imm => XLi (rkey rd) (bv_unsigned (sext 64 (bv_concat 32 imm (Z_to_bv 12 0))))
  | Auipc rd imm => XLi (rkey rd) (bv_unsigned (Z_to_bv 64 pc + sext 64 (bv_concat 32 imm (Z_to_bv 12 0))))
  | Jal rd imm => XJal (rkey rd) (bv_unsigned (Z_to_bv 64 pc + sext 64 imm)) (bv_unsigned (Z_to_bv 64 pc + Z_to_bv 64 4))
  | Jalr rd rs imm => XJalr (rkey rd) (rkey rs) (bv_unsigned (sext 64 imm)) (bv_unsigned (Z_to_bv 64 pc + Z_to_bv 64 4))
  | Branch c rs1 rs2 imm => XBr c (rkey rs1) (rkey rs2) (bv_unsigned (Z_to_bv 64 pc + sext 64 imm))
  | Load sz sg rd rs imm => XLd sz sg (rkey rd) (rkey rs) (bv_unsigned (sext 64 imm))
  | Store sz rs1 rs2 imm => XSt sz (rkey rs1) (rkey rs2) (bv_unsigned (sext 64 imm))
  | Fence _ _ _ _ _ | FenceI _ _ _ => XFence
  | Lr wd _ _ rd rs => XLr wd (rkey rd) (rkey rs)
  | Sc wd _ _ rd rs1 rs2 => XSc wd (rkey rd) (rkey rs1) (rkey rs2)
  | Amo op wd _ _ rd rs1 rs2 =>
      match op with AMO_ADD | AMO_SWAP => XAmo op wd (rkey rd) (rkey rs1) (rkey rs2) | _ => XOther end
  | FLoad fmt _ rs imm => XFLd fmt (rkey rs) (bv_unsigned (sext 64 imm))
  | FStore fmt rs1 _ imm => XFSt fmt (rkey rs1) (bv_unsigned (sext 64 imm))
  | Fmv FMV_X_F _ rd _ => XFInt (rkey rd) false
  | Fmv FMV_F_X _ _ _ => XFOp
  | Fsgnj _ _ _ _ _ => XFOp
  | Fari _ _ _ _ _ rm => if rm_okb rm then XFOp else XOther
  | Fcmp _ _ rd _ _ => XFInt (rkey rd) true
  | Fcvt dst src rd _ rm => if rm_okb rm then fcvt_x dst src (rkey rd) else XOther
  | _ => XOther
  end.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition xentry (pc : Z) : xi :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | None => XOther
  | Some w =>
      if is_ecall w then XEcall else
      match decode_any w with
      | Some (i, sz) => if Z.eqb sz 4 then xlate pc i else XOther
      | None => XOther
      end
  end.

Fixpoint mk_tbl_acc (n : nat) (pc : Z) (t : tree xi) : tree xi :=
  match n with
  | O => t
  | S n' => mk_tbl_acc n' (pc + 4) (match pc with Zpos p => tset p (xentry pc) t | _ => t end)
  end.
(* [comment removed for export] *)
Definition mk_tbl (lo : Z) (n : nat) : tree xi := mk_tbl_acc n lo TEmpty.
Fixpoint mk_tbl_ranges_acc (rs : list (Z * nat)) (t : tree xi) : tree xi :=
  match rs with [] => t | (lo, n) :: rs' => mk_tbl_ranges_acc rs' (mk_tbl_acc n lo t) end.
Definition mk_tbl_ranges (rs : list (Z * nat)) : tree xi := mk_tbl_ranges_acc rs TEmpty.
End WithSegs.

Definition tlookup (t : tree xi) (pc : Z) : xi :=
  match pc with Zpos p => match tget p t with Some x => x | None => XOther end | _ => XOther end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lc0 : lin := LIN 0 [].
Definition rget (R : tree lin) (k : positive) : lin :=
  match k with xH => lc0 | _ => match tget k R with Some l => l | None => lc0 end end.
Definition rset (R : tree lin) (k : positive) (l : lin) : tree lin :=
  match k with xH => R | _ => tset k l R end.

(* [comment removed for export] *)
Inductive bval : Type := BK (b : Z) | BV (l : lin) (j : Z).
(* [comment removed for export] *)
Inductive rkind : Type := RW | RO | RZ | RI | RT.
(* [comment removed for export] *)
Record region : Type := RG { rg_base : lin; rg_size : lin; rg_kind : rkind; rg_cont : tree bval }.
(* [comment removed for export] *)
Definition RGz (b : lin) (n : Z) (k : rkind) (c : tree bval) : region := RG b (lconst n) k c.

(* [comment removed for export] *)
Inductive fact : Type :=
| FCond (c : branch_cond) (a b : lin) (tk : bool)
| FRange (l : lin) (lo hi : Z)
| FMod (l : lin) (k r : Z)           (* [comment removed for export] *)
| FBits (l : lin) (m v : Z)           (* [comment removed for export] *)
| FByte (x v : lin) (j : Z)           (* [comment removed for export] *)
| FBytes (x : lin) (bs : list (lin * Z)).  (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive rsv : Type := RNone | RAt (l : lin) | RUnk.

Record sst : Type := SST {
  s_pc : Z;
  s_regs : tree lin;
  s_rgs : list region;
  s_facts : list fact;
  s_next : positive;      (* [comment removed for export] *)
  s_resv : rsv
}.
Definition with_pc (s : sst) (npc : Z) : sst := SST npc (s_regs s) (s_rgs s) (s_facts s) (s_next s) (s_resv s).
Definition with_resv (s : sst) (r : rsv) : sst := SST (s_pc s) (s_regs s) (s_rgs s) (s_facts s) (s_next s) r.

Definition okey (o : Z) : positive := Z.to_pos (o + 1).
Definition nbytes (sz : msize) : nat := match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

(* [comment removed for export] *)
Local Notation "a &&& b" := (if a then b else false) (at level 40, left associativity).
Local Notation "a ||| b" := (if a then true else b) (at level 50, left associativity).
(* [comment removed for export] *)
Fixpoint terms_eqb (x y : list (positive * Z)) : bool :=
  match x, y with
  | [], [] => true
  | (p, k) :: x', (q, k') :: y' => Pos.eqb p q &&& Z.eqb k k' &&& terms_eqb x' y'
  | _, _ => false
  end.
Definition lin_eqb (a b : lin) : bool := Z.eqb (l_c a) (l_c b) &&& terms_eqb (l_t a) (l_t b).
(* [comment removed for export] *)
Definition bc_eqb (a b : branch_cond) : bool :=
  match a, b with
  | BC_EQ, BC_EQ | BC_NE, BC_NE | BC_LT, BC_LT | BC_GE, BC_GE | BC_LTU, BC_LTU | BC_GEU, BC_GEU => true
  | _, _ => false
  end.
(* [comment removed for export] *)
Fixpoint lzs_eqb (a b : list (lin * Z)) : bool :=
  match a, b with
  | [], [] => true
  | (x, j) :: a', (y, k) :: b' => lin_eqb x y &&& Z.eqb j k &&& lzs_eqb a' b'
  | _, _ => false
  end.
Definition fact_eqb (f g : fact) : bool :=
  match f, g with
  | FCond c a b tk, FCond c' a' b' tk' => bc_eqb c c' &&& lin_eqb a a' &&& lin_eqb b b' &&& Bool.eqb tk tk'
  | FRange l lo hi, FRange l' lo' hi' => lin_eqb l l' &&& Z.eqb lo lo' &&& Z.eqb hi hi'
  | FMod l k r, FMod l' k' r' => lin_eqb l l' &&& Z.eqb k k' &&& Z.eqb r r'
  | FBits l m v, FBits l' m' v' => lin_eqb l l' &&& Z.eqb m m' &&& Z.eqb v v'
  | FByte x v j, FByte x' v' j' => lin_eqb x x' &&& lin_eqb v v' &&& Z.eqb j j'
  | FBytes x bs, FBytes x' bs' => lin_eqb x x' &&& lzs_eqb bs bs'
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition lin_off (a b : lin) : option Z :=
  if terms_eqb (l_t a) (l_t b) then Some (w64 (l_c a - l_c b)) else None.
Fixpoint upd_nth (rgs : list region) (i : nat) (R : region) : list region :=
  match rgs, i with
  | [], _ => []
  | _ :: rs, O => R :: rs
  | R0 :: rs, S i' => R0 :: upd_nth rs i' R
  end.

(* [comment removed for export] *)
Fixpoint get_bytes (t : tree bval) (o : Z) (n : nat) : option (list bval) :=
  match n with
  | O => Some []
  | S n' => match tget (okey o) t with
            | Some v => match get_bytes t (o + 1) n' with Some r => Some (v :: r) | None => None end
            | None => None
            end
  end.
Fixpoint put_bytes (t : tree bval) (o : Z) (l : list bval) : tree bval :=
  match l with [] => t | v :: l' => put_bytes (tset (okey o) v t) (o + 1) l' end.

(* [comment removed for export] *)
Fixpoint get_bytes_z (t : tree bval) (o : Z) (n : nat) : list bval :=
  match n with
  | O => []
  | S n' => (match tget (okey o) t with Some v => v | None => BK 0 end) :: get_bytes_z t (o + 1) n'
  end.
(* [comment removed for export] *)
Fixpoint all_bk (l : list bval) : option (list Z) :=
  match l with [] => Some [] | BK b :: l' => match all_bk l' with Some r => Some (b :: r) | None => None end | _ => None end.
(* [comment removed for export] *)
Fixpoint is_bv_of (v : lin) (j : Z) (l : list bval) : bool :=
  match l with
  | [] => true
  | BV v' j' :: l' => (lin_eqb v v' && Z.eqb j j' && is_bv_of v (j + 1) l')%bool
  | _ => false
  end.

(* [comment removed for export] *)
Definition ld_word (sz : msize) (sg : bool) (bs : list byte) : word :=
  let v := le_bytes_to_word bs in
  match sz with
  | SZ1 => if sg then sext 64 (bv_extract 0 8 v) else zext 64 (bv_extract 0 8 v)
  | SZ2 => if sg then sext 64 (bv_extract 0 16 v) else zext 64 (bv_extract 0 16 v)
  | SZ4 => if sg then sext 64 (bv_extract 0 32 v) else zext 64 (bv_extract 0 32 v)
  | SZ8 => bv_extract 0 64 v
  end.

(* [comment removed for export] *)
Fixpoint st_bytes (v : lin) (z : option Z) (j : Z) (n : nat) : list bval :=
  match n with
  | O => []
  | S n' => (match z with Some c => BK (Z.land (Z.shiftr c (8 * j)) 255) | None => BV v j end) :: st_bytes v z (j + 1) n'
  end.

(* [comment removed for export] *)
Definition wkey (a : Z) : positive := Z.to_pos (Z.shiftr a 3 + 1).
(* [comment removed for export] *)
Fixpoint img_bytes (img : tree Z) (a : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match tget (wkey a) img with
            | Some w => match img_bytes img (a + 1) n' with
                        | Some r => Some (Z.land (Z.shiftr w (8 * Z.land a 7)) 255 :: r)
                        | None => None
                        end
            | None => None
            end
  end.

(* [comment removed for export] *)
Fixpoint get_bytes_i (img : tree Z) (t : tree bval) (A o : Z) (n : nat) : option (list bval) :=
  match n with
  | O => Some []
  | S n' =>
      match (match tget (okey o) t with
             | Some v => Some v
             | None => match img_bytes img (A + o) 1 with Some [b] => Some (BK b) | _ => None end
             end) with
      | Some v => match get_bytes_i img t A (o + 1) n' with Some r => Some (v :: r) | None => None end
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition T63 : Z := 9223372036854775808.
Definition sgn64 (x : Z) : Z := if Z.ltb x T63 then x else x - two64.
Definition alu_z (op : aluop) (x y : Z) : Z :=
  match op with
  | ALU_ADD => w64 (x + y)
  | ALU_SUB => w64 (x - y)
  | ALU_AND => Z.land x y
  | ALU_OR => Z.lor x y
  | ALU_XOR => Z.lxor x y
  | ALU_SLL => w64 (Z.shiftl x (Z.land y 63))
  | ALU_SRL => Z.shiftr x (Z.land y 63)
  | ALU_SLTU => if Z.ltb x y then 1 else 0
  | ALU_SLT => if Z.ltb (sgn64 x) (sgn64 y) then 1 else 0
  | _ => bv_unsigned (alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y))
  end.
Definition br_z (c : branch_cond) (x y : Z) : bool :=
  match c with
  | BC_EQ => Z.eqb x y | BC_NE => negb (Z.eqb x y)
  | BC_LTU => Z.ltb x y | BC_GEU => negb (Z.ltb x y)
  | BC_LT => Z.ltb (sgn64 x) (sgn64 y) | BC_GE => negb (Z.ltb (sgn64 x) (sgn64 y))
  end.

(* [comment removed for export] *)
Definition iv_top : Z * Z := (0, M64).
Definition iv_meet (a b : Z * Z) : Z * Z := (Z.max (fst a) (fst b), Z.min (snd a) (snd b)).
Definition iv_add (a b : Z * Z) : Z * Z := (fst a + fst b, snd a + snd b).
Definition iv_scale (k : Z) (a : Z * Z) : Z * Z := if Z.leb 0 k then (k * fst a, k * snd a) else (k * snd a, k * fst a).
Definition nowrap (a : Z * Z) : bool := (Z.leb 0 (fst a) && Z.leb (snd a) M64)%bool.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bits_iv (m v : Z) : Z * Z := (v, Z.land (Z.lnot (Z.land m (Z.lnot v))) M64).
Fixpoint var_range (fs : list fact) (x : positive) : Z * Z :=
  match fs with
  | [] => (0, M64)
  | FRange (LIN 0 [(y, 1)]) lo hi :: fs' => if Pos.eqb x y then iv_meet (lo, hi) (var_range fs' x) else var_range fs' x
  | FBits (LIN 0 [(y, 1)]) m v :: fs' => if (Pos.eqb x y && Z.leb 0 m)%bool then iv_meet (bits_iv m v) (var_range fs' x) else var_range fs' x
  | _ :: fs' => var_range fs' x
  end.
(* [comment removed for export] *)
Definition ne_c (c : branch_cond) (tk : bool) : bool := match c, tk with BC_NE, true | BC_EQ, false => true | _, _ => false end.
(* [comment removed for export] *)
Definition occ (y : positive) (t : list (positive * Z)) : bool := existsb (fun '(z, _) => Pos.eqb y z) t.
Definition ne_pre (l a b : lin) : bool :=
  (forallb (fun '(y, _) => (occ y (l_t a) || occ y (l_t b))%bool) (l_t l) &&
   (* [comment removed for export] *)
   forallb (fun '(y, _) => (occ y (l_t b) || occ y (l_t l))%bool) (l_t a) &&
   forallb (fun '(y, _) => (occ y (l_t a) || occ y (l_t l))%bool) (l_t b))%bool.
Fixpoint ne_refine (fs : list fact) (l : lin) (acc : Z * Z) : Z * Z :=
  match fs with
  | [] => acc
  | FCond c a b tk :: fs' =>
      if (ne_c c tk && ne_pre l a b)%bool then
        let ba := if terms_eqb (l_t l) (l_t (lsub b a)) then lsub b a else lsub a b in
        if terms_eqb (l_t l) (l_t ba) then
          let z := w64 (l_c l - l_c ba) in     (* [comment removed for export] *)
          let acc' := if Z.eqb (fst acc) z then (fst acc + 1, snd acc)
                      else if Z.eqb (snd acc) z then (fst acc, snd acc - 1) else acc in
          ne_refine fs' l acc'
        else ne_refine fs' l acc
      else ne_refine fs' l acc
  | _ :: fs' => ne_refine fs' l acc
  end.
(* [comment removed for export] *)
Fixpoint ne_fix (k : nat) (fs : list fact) (l : lin) (acc : Z * Z) : Z * Z :=
  match k with
  | O => acc
  | S k' => let acc' := ne_refine fs l acc in
            if (Z.eqb (fst acc') (fst acc) && Z.eqb (snd acc') (snd acc))%bool then acc' else ne_fix k' fs l acc'
  end.
(* [comment removed for export] *)
Fixpoint ne_fixl (k : list fact) (fs : list fact) (l : lin) (acc : Z * Z) : Z * Z :=
  match k with
  | [] => acc
  | _ :: k' => let acc' := ne_refine fs l acc in
               if (Z.eqb (fst acc') (fst acc) && Z.eqb (snd acc') (snd acc))%bool then acc' else ne_fixl k' fs l acc'
  end.
Definition ne_refine' (fs : list fact) (l : lin) (acc : Z * Z) : Z * Z := ne_fixl fs fs l acc.
(* [comment removed for export] *)
Definition var_range' (fs : list fact) (x : positive) : Z * Z := ne_refine' fs (lvar x) (var_range fs x).
Fixpoint t_iv (fs : list fact) (t : list (positive * Z)) : Z * Z :=
  match t with [] => (0, 0) | (x, k) :: t' => iv_add (iv_scale (sgn64 k) (var_range' fs x)) (t_iv fs t') end.
(* [comment removed for export] *)
Definition l_iv (fs : list fact) (l : lin) : Z * Z := iv_add (sgn64 (l_c l), sgn64 (l_c l)) (t_iv fs (l_t l)).
(* [comment removed for export] *)
Definition wrap_iv (a : Z * Z) : Z * Z :=
  if nowrap a then a else let b := (fst a + two64, snd a + two64) in if nowrap b then b else iv_top.
Definition base_range (fs : list fact) (l : lin) : Z * Z := wrap_iv (l_iv fs l).
(* [comment removed for export] *)
Definition window (a b : Z * Z) : bool := Z.ltb (Z.max (snd a) (snd b) - Z.min (fst a) (fst b)) two64.
(* [comment removed for export] *)
Definition meet_win (acc c : Z * Z) : Z * Z :=
  if window acc c then iv_meet acc c
  (* [comment removed for export] *)
  else if Z.ltb (snd c - fst c) (snd acc - fst acc) then c else acc.
(* [comment removed for export] *)
Fixpoint frange_same (fs : list fact) (l : lin) (acc : Z * Z) : Z * Z :=
  match fs with
  | [] => acc
  | FRange g lo hi :: fs' =>
      if terms_eqb (l_t g) (l_t l) then
        let d := sgn64 (w64 (l_c l - l_c g)) in frange_same fs' l (meet_win acc (lo + d, hi + d))
      else frange_same fs' l acc
  | _ :: fs' => frange_same fs' l acc
  end.
(* [comment removed for export] *)
Fixpoint ne_int (fs : list fact) (l : lin) (acc : Z * Z) : Z * Z :=
  match fs with
  | [] => acc
  | FCond c a b tk :: fs' =>
      if (ne_c c tk && ne_pre l a b)%bool then
        let ba := if terms_eqb (l_t l) (l_t (lsub b a)) then lsub b a else lsub a b in
        if terms_eqb (l_t l) (l_t ba) then
          let z := w64 (l_c l - l_c ba) in
          let acc' := if Z.eqb (w64 (fst acc)) z then (fst acc + 1, snd acc)
                      else if Z.eqb (w64 (snd acc)) z then (fst acc, snd acc - 1) else acc in
          ne_int fs' l acc'
        else ne_int fs' l acc
      else ne_int fs' l acc
  | _ :: fs' => ne_int fs' l acc
  end.
Fixpoint ne_int_fix (k : nat) (fs : list fact) (l : lin) (acc : Z * Z) : Z * Z :=
  match k with
  | O => acc
  | S k' => let acc' := ne_int fs l acc in
            if (Z.eqb (fst acc') (fst acc) && Z.eqb (snd acc') (snd acc))%bool then acc' else ne_int_fix k' fs l acc'
  end.
Fixpoint ne_int_fixl (k : list fact) (fs : list fact) (l : lin) (acc : Z * Z) : Z * Z :=
  match k with
  | [] => acc
  | _ :: k' => let acc' := ne_int fs l acc in
               if (Z.eqb (fst acc') (fst acc) && Z.eqb (snd acc') (snd acc))%bool then acc' else ne_int_fixl k' fs l acc'
  end.
(* [comment removed for export] *)
Definition srange (fs : list fact) (l : lin) : Z * Z :=
  let v := frange_same fs l (l_iv fs l) in if nowrap v then wrap_iv v else wrap_iv (ne_int_fixl fs fs l v).
(* [comment removed for export] *)
Definition sgn_const_lt (a b : lin) : option (lin * Z * Z) :=     (* [comment removed for export] *)
  match is_const b, is_const a with
  | Some c, _ => Some (laddc a T63, 0, sgn64 c - 1 + T63)
  | None, Some c => Some (laddc b T63, sgn64 c + 1 + T63, M64)
  | None, None => None
  end.
Definition sgn_const_ge (a b : lin) : option (lin * Z * Z) :=     (* [comment removed for export] *)
  match is_const b, is_const a with
  | Some c, _ => Some (laddc a T63, sgn64 c + T63, M64)
  | None, Some c => Some (laddc b T63, 0, sgn64 c + T63)
  | None, None => None
  end.
(* [comment removed for export] *)
Definition fact_g (fs : list fact) (f : fact) : option (lin * Z * Z) :=
  match f with
  | FRange g lo hi => Some (g, lo, hi)
  | FMod _ _ _ | FBits _ _ _ | FByte _ _ _ | FBytes _ _ => None
  | FCond c a b tk =>
      let ra := base_range fs a in let rb := base_range fs b in
      match c, tk with
      | BC_LTU, true | BC_GEU, false => Some (lsub b a, 1, snd rb - fst ra)
      | BC_LTU, false | BC_GEU, true => Some (lsub a b, 0, snd ra - fst rb)
      | BC_EQ, true | BC_NE, false => Some (lsub b a, 0, 0)
      | BC_LT, true | BC_GE, false =>
          let sa := srange fs a in let sb := srange fs b in
          if (Z.ltb (snd sa) T63 && Z.ltb (snd sb) T63)%bool then Some (lsub b a, 1, snd sb - fst sa) else sgn_const_lt a b
      | BC_LT, false | BC_GE, true =>
          let sa := srange fs a in let sb := srange fs b in
          if (Z.ltb (snd sa) T63 && Z.ltb (snd sb) T63)%bool then Some (lsub a b, 0, snd sa - fst sb) else sgn_const_ge a b
      | _, _ => None
      end
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shares (t u : list (positive * Z)) : bool := existsb (fun '(x, _) => existsb (fun '(y, _) => Pos.eqb x y) u) t.
Definition rel_ok (l : lin) (f : fact) : bool :=
  match f with
  | FRange (LIN 0 [(_, 1)]) _ _ => false
  | FRange g _ _ => shares (l_t l) (l_t g)
  | FCond _ a b _ => (shares (l_t l) (l_t a) || shares (l_t l) (l_t b))%bool
  | _ => false
  end.
Fixpoint rel_iv (fs all : list fact) (l : lin) (acc : Z * Z) : Z * Z :=
  match fs with
  | [] => acc
  | f :: fs' =>
      if rel_ok l f then
      match fact_g all f with
      | Some (g, lo, hi) =>
          let r1 := l_iv all (lsub l g) in
          let r2 := l_iv all (ladd l g) in
          rel_iv fs' all l (meet_win (meet_win acc (lo + fst r1, hi + snd r1)) (fst r2 - hi, snd r2 - lo))
      | None => rel_iv fs' all l acc
      end
      else rel_iv fs' all l acc
  end.
(* [comment removed for export] *)
Fixpoint ctz_f (fuel : nat) (z : Z) : Z :=
  match fuel with O => 0 | S f => if Z.eqb (Z.land z 1) 0 then 1 + ctz_f f (Z.shiftr z 1) else 0 end.
Definition ctz64 (z : Z) : Z := if Z.eqb (w64 z) 0 then 64 else ctz_f 64 (w64 z).
Fixpoint var_align (fs : list fact) (x : positive) : Z :=
  match fs with
  | [] => 0
  | FMod (LIN 0 [(y, 1)]) k 0 :: fs' => if Pos.eqb x y then Z.max (Z.min k 64) (var_align fs' x) else var_align fs' x
  | _ :: fs' => var_align fs' x
  end.
Fixpoint t_align (fs : list fact) (t : list (positive * Z)) : Z :=
  match t with [] => 64 | (x, k) :: t' => Z.min (Z.min (ctz64 k + var_align fs x) 64) (t_align fs t') end.
Definition lalign (fs : list fact) (l : lin) : Z := Z.min (ctz64 (l_c l)) (t_align fs (l_t l)).
(* [comment removed for export] *)
Fixpoint var_lowb (fs : list fact) (x : positive) (k : Z) : option Z :=
  match fs with
  | [] => None
  | FMod (LIN 0 [(y, 1)]) k' r :: fs' => if (Pos.eqb x y && Z.leb k k' && Z.leb k' 64)%bool then Some (Z.land r (Z.ones k)) else var_lowb fs' x k
  | _ :: fs' => var_lowb fs' x k
  end.
Fixpoint t_lowb (fs : list fact) (t : list (positive * Z)) (k : Z) : option Z :=
  match t with
  | [] => Some 0
  | (x, c) :: t' =>
      match t_lowb fs t' k with
      | Some r => if Z.eqb (Z.land c (Z.ones k)) 0 then Some r
                  else match var_lowb fs x (k - Z.min (ctz64 c) k) with Some rx => Some (Z.land (c * rx + r) (Z.ones k)) | None => None end
      | None => None
      end
  end.
Definition lowb (fs : list fact) (l : lin) (k : Z) : option Z :=
  if (Z.leb 0 k && Z.leb k 64)%bool then
    match t_lowb fs (l_t l) k with Some r => Some (Z.land (l_c l + r) (Z.ones k)) | None => None end
  else None.
(* [comment removed for export] *)
Definition lowb2 (fs : list fact) (a b : lin) : option (Z * Z * Z) :=
  let fix go (ks : list Z) := match ks with
    | [] => None
    | k :: ks' => match lowb fs a k, lowb fs b k with Some ra, Some rb => Some (k, ra, rb) | _, _ => go ks' end
    end in go [16; 12; 8; 4; 3; 2; 1].
(* [comment removed for export] *)
Definition tn_top : Z * Z := (0, 0).
Definition tn_join (a b : Z * Z) : Z * Z := (Z.lor (fst a) (fst b), Z.lor (snd a) (snd b)).
Definition tn_and (a b : Z * Z) : Z * Z :=
  let '(m1, v1) := a in let '(m2, v2) := b in
  let ones := Z.land v1 v2 in let zeros := Z.lor (Z.lxor v1 m1) (Z.lxor v2 m2) in (Z.lor ones zeros, ones).
Definition tn_or (a b : Z * Z) : Z * Z :=
  let '(m1, v1) := a in let '(m2, v2) := b in
  let ones := Z.lor v1 v2 in let zeros := Z.land (Z.lxor v1 m1) (Z.lxor v2 m2) in (Z.lor ones zeros, ones).
Definition tn_xor (a b : Z * Z) : Z * Z :=
  let '(m1, v1) := a in let '(m2, v2) := b in let m := Z.land m1 m2 in (m, Z.land (Z.lxor v1 v2) m).
Definition tn_srl (k : Z) (a : Z * Z) : Z * Z :=
  let '(m1, v1) := a in (Z.lor (Z.shiftr m1 k) (Z.lxor (Z.ones 64) (Z.shiftr (Z.ones 64) k)), Z.shiftr v1 k).
Definition tn_sll (k : Z) (a : Z * Z) : Z * Z :=
  let '(m1, v1) := a in (Z.lor (Z.land (Z.shiftl m1 k) (Z.ones 64)) (Z.ones k), Z.land (Z.shiftl v1 k) (Z.ones 64)).
(* [comment removed for export] *)
Definition tn_range (lo hi : Z) : Z * Z :=
  let j := if Z.eqb lo hi then 0 else Z.log2 (Z.lxor lo hi) + 1 in
  let m := Z.land (Z.ones 64) (Z.lnot (Z.ones j)) in (m, Z.land lo m).
Fixpoint var_bits (fs : list fact) (x : positive) : Z * Z :=
  match fs with
  | [] => tn_top
  | FBits (LIN 0 [(y, 1)]) m v :: fs' => if Pos.eqb x y then tn_join (m, v) (var_bits fs' x) else var_bits fs' x
  | _ :: fs' => var_bits fs' x
  end.
Definition tn_low (fs : list fact) (l : lin) : Z * Z :=
  let fix go (ks : list Z) := match ks with [] => tn_top | k :: ks' => match lowb fs l k with Some r => (Z.ones k, r) | None => go ks' end end in
  go [64; 32; 16; 12; 8; 4; 3; 2; 1].
(* [comment removed for export] *)
Definition align_iv (a : Z) (r : Z * Z) : Z * Z :=
  let m := 2 ^ a in ((fst r + m - 1) / m * m, snd r / m * m).

(* [comment removed for export] *)
Definition round_to (k r : Z) (v : Z * Z) : Z * Z :=
  let m := 2 ^ k in (fst v + ((r - fst v) mod m), snd v - ((snd v - r) mod m)).
Definition lround (fs : list fact) (l : lin) (v : Z * Z) : Z * Z :=
  if nowrap v then v else match lowb fs l 8 with Some r => round_to 8 r v | None => v end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rel_base (fs : list fact) (l : lin) : Z * Z := frange_same fs l (ne_int fs l (rel_iv fs fs l (l_iv fs l))).
(* [comment removed for export] *)
Definition rel_ok3 (ta : list (positive * Z)) (f : fact) : bool :=
  match f with
  | FRange (LIN 0 [(_, 1)]) _ _ => false
  | FRange g _ _ => shares ta (l_t g)
  | FCond _ a b _ => (shares ta (l_t a) || shares ta (l_t b))%bool
  | _ => false
  end.
Fixpoint rel_iv2 (fs all : list fact) (ta : list (positive * Z)) (l : lin) (acc : Z * Z) : Z * Z :=
  match fs with
  | [] => acc
  | f :: fs' =>
      if rel_ok3 ta f then
      match fact_g all f with
      | Some (g, lo0, hi0) =>
          (* [comment removed for export] *)
          let '(lo, hi) := ne_int_fixl all all g (lo0, hi0) in
          let d1 := lsub l g in let d2 := ladd l g in
          let r1 := rel_base all d1 in
          let r2 := rel_base all d2 in
          rel_iv2 fs' all ta l (meet_win (meet_win acc (lo + fst r1, hi + snd r1)) (fst r2 - hi, snd r2 - lo))
      | None => rel_iv2 fs' all ta l acc
      end
      else rel_iv2 fs' all ta l acc
  end.
Definition irange0 (fs : list fact) (l : lin) : Z * Z :=
  let v := ne_int_fixl fs fs l (lround fs l (rel_iv fs fs l (l_iv fs l))) in
  let r := ne_refine' fs l (wrap_iv v) in
  let a := lalign fs l in if Z.ltb 0 a then align_iv a r else r.
(* [comment removed for export] *)
Definition ldiv8 (l : lin) : option lin :=
  if (Z.eqb (Z.rem (sgn64 (l_c l)) 8) 0 && forallb (fun '(_, c) => Z.eqb (Z.rem (sgn64 c) 8) 0) (l_t l))%bool
  then Some (LIN (w64 (Z.quot (sgn64 (l_c l)) 8)) (List.map (fun '(x, c) => (x, w64 (Z.quot (sgn64 c) 8))) (l_t l))) else None.
(* [comment removed for export] *)
Definition irange_ref (fs : list fact) (l : lin) : Z * Z :=
  match is_const l with
  | Some c => (c, c)
  | None => let r := irange0 fs l in
            if Z.eqb (snd r) (fst r) then r else
            match ldiv8 l with
            | Some l' => let r' := irange0 fs l' in
                         if (Z.leb 0 (fst r') && Z.ltb (8 * snd r') two64)%bool then iv_meet r (8 * fst r', 8 * snd r') else r
            | None => r
            end
  end.
(* [comment removed for export] *)
Definition vr_get (t : tree (Z * Z)) (x : positive) : Z * Z := match tget x t with Some r => r | None => (0, M64) end.
Fixpoint vr_tbl (fs : list fact) : tree (Z * Z) :=
  match fs with
  | [] => TEmpty
  | FRange (LIN 0 [(y, 1)]) lo hi :: fs' => let t := vr_tbl fs' in tset y (iv_meet (lo, hi) (vr_get t y)) t
  | FBits (LIN 0 [(y, 1)]) m v :: fs' => if Z.leb 0 m then (let t := vr_tbl fs' in tset y (iv_meet (bits_iv m v) (vr_get t y)) t) else vr_tbl fs'
  | _ :: fs' => vr_tbl fs'
  end.
Definition is_ne (f : fact) : bool := match f with FCond c _ _ tk => ne_c c tk | _ => false end.
Definition ne_sub (fs : list fact) : list fact := List.filter is_ne fs.
Section F.
Variables (vt : tree (Z * Z)) (ne all : list fact).
Definition var_rangeF (x : positive) : Z * Z := ne_fixl all ne (lvar x) (vr_get vt x).
Fixpoint t_ivF (t : list (positive * Z)) : Z * Z :=
  match t with [] => (0, 0) | (x, k) :: t' => iv_add (iv_scale (sgn64 k) (var_rangeF x)) (t_ivF t') end.
Definition l_ivF (l : lin) : Z * Z := iv_add (sgn64 (l_c l), sgn64 (l_c l)) (t_ivF (l_t l)).
Definition base_rangeF (l : lin) : Z * Z := wrap_iv (l_ivF l).
Definition srangeF (l : lin) : Z * Z :=
  let v := frange_same all l (l_ivF l) in if nowrap v then wrap_iv v else wrap_iv (ne_int_fixl all ne l v).
Definition fact_gF (f : fact) : option (lin * Z * Z) :=
  match f with
  | FRange g lo hi => Some (g, lo, hi)
  | FMod _ _ _ | FBits _ _ _ | FByte _ _ _ | FBytes _ _ => None
  | FCond c a b tk =>
      let ra := base_rangeF a in let rb := base_rangeF b in
      match c, tk with
      | BC_LTU, true | BC_GEU, false => Some (lsub b a, 1, snd rb - fst ra)
      | BC_LTU, false | BC_GEU, true => Some (lsub a b, 0, snd ra - fst rb)
      | BC_EQ, true | BC_NE, false => Some (lsub b a, 0, 0)
      | BC_LT, true | BC_GE, false =>
          let sa := srangeF a in let sb := srangeF b in
          if (Z.ltb (snd sa) T63 && Z.ltb (snd sb) T63)%bool then Some (lsub b a, 1, snd sb - fst sa) else sgn_const_lt a b
      | BC_LT, false | BC_GE, true =>
          let sa := srangeF a in let sb := srangeF b in
          if (Z.ltb (snd sa) T63 && Z.ltb (snd sb) T63)%bool then Some (lsub a b, 0, snd sa - fst sb) else sgn_const_ge a b
      | _, _ => None
      end
  end.
Fixpoint rel_ivF (fs : list fact) (l : lin) (acc : Z * Z) : Z * Z :=
  match fs with
  | [] => acc
  | f :: fs' =>
      if rel_ok l f then
      match fact_gF f with
      | Some (g, lo, hi) =>
          let r1 := l_ivF (lsub l g) in
          let r2 := l_ivF (ladd l g) in
          rel_ivF fs' l (meet_win (meet_win acc (lo + fst r1, hi + snd r1)) (fst r2 - hi, snd r2 - lo))
      | None => rel_ivF fs' l acc
      end
      else rel_ivF fs' l acc
  end.
Definition irange0F (l : lin) : Z * Z :=
  let v := ne_int_fixl all ne l (lround all l (rel_ivF all l (l_ivF l))) in
  let r := ne_fixl all ne l (wrap_iv v) in
  let a := lalign all l in if Z.ltb 0 a then align_iv a r else r.
End F.
Fixpoint longer (n : nat) (fs : list fact) : bool :=
  match n with O => true | S n' => match fs with [] => false | _ :: r => longer n' r end end.
Definition IR_FAST_MIN : nat := 40.
(* [comment removed for export] *)
Module IrN.
(* [comment removed for export] *)
Fixpoint occN (x : positive) (u : list (positive * Z)) : bool := match u with [] => false | (y, _) :: u' => if Pos.eqb x y then true else occN x u' end.
Fixpoint sharesN (t u : list (positive * Z)) : bool := match t with [] => false | (x, _) :: t' => if occN x u then true else sharesN t' u end.
Definition rel_okN (l : lin) (f : fact) : bool :=
  match f with
  | FRange (LIN 0 [(_, 1)]) _ _ => false
  | FRange g _ _ => sharesN (l_t l) (l_t g)
  | FCond _ a b _ => if sharesN (l_t l) (l_t a) then true else sharesN (l_t l) (l_t b)
  | _ => false
  end.
(* [comment removed for export] *)
Definition is_bare (f : fact) : bool := match f with FRange (LIN 0 [(_, 1)]) _ _ => true | FBits (LIN 0 [(_, 1)]) _ _ => true | _ => false end.
Definition is_modb (f : fact) : bool := match f with FMod (LIN 0 [(_, 1)]) _ _ => true | _ => false end.
Section N.
Variables (ne all bfs mfs : list fact).
Definition vrangeN (x : positive) : Z * Z := ne_fixl all ne (lvar x) (var_range bfs x).
Fixpoint t_ivN (t : list (positive * Z)) : Z * Z :=
  match t with [] => (0, 0) | (x, k) :: t' => iv_add (iv_scale (sgn64 k) (vrangeN x)) (t_ivN t') end.
Definition l_ivN (l : lin) : Z * Z := iv_add (sgn64 (l_c l), sgn64 (l_c l)) (t_ivN (l_t l)).
Definition base_rangeN (l : lin) : Z * Z := wrap_iv (l_ivN l).
Definition srangeN (l : lin) : Z * Z :=
  let v := frange_same all l (l_ivN l) in if nowrap v then wrap_iv v else wrap_iv (ne_int_fixl all ne l v).
Definition fact_gN (f : fact) : option (lin * Z * Z) :=
  match f with
  | FRange g lo hi => Some (g, lo, hi)
  | FMod _ _ _ | FBits _ _ _ | FByte _ _ _ | FBytes _ _ => None
  | FCond c a b tk =>
      let ra := base_rangeN a in let rb := base_rangeN b in
      match c, tk with
      | BC_LTU, true | BC_GEU, false => Some (lsub b a, 1, snd rb - fst ra)
      | BC_LTU, false | BC_GEU, true => Some (lsub a b, 0, snd ra - fst rb)
      | BC_EQ, true | BC_NE, false => Some (lsub b a, 0, 0)
      | BC_LT, true | BC_GE, false =>
          let sa := srangeN a in let sb := srangeN b in
          if (Z.ltb (snd sa) T63 && Z.ltb (snd sb) T63)%bool then Some (lsub b a, 1, snd sb - fst sa) else sgn_const_lt a b
      | BC_LT, false | BC_GE, true =>
          let sa := srangeN a in let sb := srangeN b in
          if (Z.ltb (snd sa) T63 && Z.ltb (snd sb) T63)%bool then Some (lsub a b, 0, snd sa - fst sb) else sgn_const_ge a b
      | _, _ => None
      end
  end.
Fixpoint rel_ivN (fs : list fact) (l : lin) (acc : Z * Z) : Z * Z :=
  match fs with
  | [] => acc
  | f :: fs' =>
      if rel_okN l f then
      match fact_gN f with
      | Some (g, lo, hi) =>
          let r1 := l_ivN (lsub l g) in
          let r2 := l_ivN (ladd l g) in
          rel_ivN fs' l (meet_win (meet_win acc (lo + fst r1, hi + snd r1)) (fst r2 - hi, snd r2 - lo))
      | None => rel_ivN fs' l acc
      end
      else rel_ivN fs' l acc
  end.
(* [comment removed for export] *)
Definition get_ve (T : tree ventry) (x : positive) : option (tree ventry * ventry) :=
  match tget x T with
  | Some e => Some (T, e)
  | None => match mk_ve (vrangeN x) with Some e => Some (tset x e T, e) | None => None end
  end.
Fixpoint conv_t (T : tree ventry) (t : list (positive * Z)) : option (tree ventry * list cterm) :=
  match t with
  | [] => Some (T, [])
  | (x, k) :: t' =>
      match k2c k with
      | None => None
      | Some c =>
          match get_ve T x with
          | None => None
          | Some (T1, e) => match conv_t T1 t' with Some (T2, r) => Some (T2, CT x c e :: r) | None => None end
          end
      end
  end.
Definition conv_l (T : tree ventry) (l : lin) : option (tree ventry * clin) :=
  match k2c (l_c l) with
  | None => None
  | Some c => match conv_t T (l_t l) with Some (T', t) => Some (T', CL c t) | None => None end
  end.
Definition wstep (T : tree ventry) (cl : clin) (g : lin) (lo hi : Z) (acc : wiv) : option (tree ventry * wiv) :=
  match conv_l T g with
  | None => None
  | Some (T', cg) =>
      match z2w lo, z2w hi with
      | Some (loa, lob), Some (hia, hib) => match wstep_iv cl cg loa lob hia hib acc with Some acc' => Some (T', acc') | None => None end
      | _, _ => None
      end
  end.
Fixpoint rel_N (l : lin) (cl : clin) (fs : list fact) (T : tree ventry) (acc : wiv) : Z * Z :=
  match fs with
  | [] => wiv2z acc
  | f :: fs' =>
      if rel_okN l f then
      match fact_gN f with
      | Some (g, lo, hi) =>
          match wstep T cl g lo hi acc with
          | Some (T', acc') => rel_N l cl fs' T' acc'
          | None => rel_ivN fs l (wiv2z acc)
          end
      | None => rel_N l cl fs' T acc
      end
      else rel_N l cl fs' T acc
  end.
Definition rel_topN (l : lin) : Z * Z :=
  match conv_l TEmpty l with
  | Some (T, cl) => match cl_iv cl with Some acc => rel_N l cl all T acc | None => rel_ivN all l (l_ivN l) end
  | None => rel_ivN all l (l_ivN l)
  end.
Definition irange0N (l : lin) : Z * Z :=
  let v := ne_int_fixl all ne l (lround mfs l (rel_topN l)) in
  let r := ne_fixl all ne l (wrap_iv v) in
  let a := lalign mfs l in if Z.ltb 0 a then align_iv a r else r.
(* [comment removed for export] *)
Inductive cand : Type :=
| CDZ (g : lin) (lo hi : Z)
| CDN (g : lin) (lo hi : Z) (cg : clin) (loa lob hia hib : PrimInt63.int).
Definition cand_of (T : tree ventry) (g : lin) (lo hi : Z) : tree ventry * cand :=
  match conv_l T g with
  | Some (T1, cg) =>
      match z2w lo, z2w hi with
      | Some (loa, lob), Some (hia, hib) => (T1, CDN g lo hi cg loa lob hia hib)
      | _, _ => (T1, CDZ g lo hi)
      end
  | None => (T, CDZ g lo hi)
  end.
Fixpoint prep (l : lin) (fs : list fact) (T : tree ventry) : tree ventry * list cand :=
  match fs with
  | [] => (T, [])
  | f :: fs' =>
      if rel_okN l f then
        match fact_gN f with
        | Some (g, lo, hi) => let '(T1, c) := cand_of T g lo hi in let '(T2, cs) := prep l fs' T1 in (T2, c :: cs)
        | None => prep l fs' T
        end
      else prep l fs' T
  end.
(* [comment removed for export] *)
Definition zstep (l g : lin) (lo hi : Z) (acc : Z * Z) : Z * Z :=
  let r1 := l_ivN (lsub l g) in let r2 := l_ivN (ladd l g) in
  meet_win (meet_win acc (lo + fst r1, hi + snd r1)) (fst r2 - hi, snd r2 - lo).
Fixpoint rel_ivC (l : lin) (cs : list cand) (acc : Z * Z) : Z * Z :=
  match cs with
  | [] => acc
  | CDZ g lo hi :: cs' => rel_ivC l cs' (zstep l g lo hi acc)
  | CDN g lo hi _ _ _ _ _ :: cs' => rel_ivC l cs' (zstep l g lo hi acc)
  end.
Fixpoint rel_P (l : lin) (cl : clin) (cs : list cand) (acc : wiv) : Z * Z :=
  match cs with
  | [] => wiv2z acc
  | CDZ _ _ _ :: _ => rel_ivC l cs (wiv2z acc)
  | CDN _ _ _ cg loa lob hia hib :: cs' =>
      match wstep_iv cl cg loa lob hia hib acc with
      | Some acc' => rel_P l cl cs' acc'
      | None => rel_ivC l cs (wiv2z acc)
      end
  end.
Definition rel_topP (T : tree ventry) (cs : list cand) (l : lin) : Z * Z :=
  match conv_l T l with
  | Some (_, cl) => match cl_iv cl with Some acc => rel_P l cl cs acc | None => rel_ivC l cs (l_ivN l) end
  | None => rel_ivC l cs (l_ivN l)
  end.
Definition irange0P (T : tree ventry) (cs : list cand) (l : lin) : Z * Z :=
  let v := ne_int_fixl all ne l (lround mfs l (rel_topP T cs l)) in
  let r := ne_fixl all ne l (wrap_iv v) in
  let a := lalign mfs l in if Z.ltb 0 a then align_iv a r else r.
(* [comment removed for export] *)
Definition prepL (l : lin) : tree ventry * list cand :=
  prep l all (match conv_t TEmpty (l_t l) with Some (T, _) => T | None => TEmpty end).
(* [comment removed for export] *)
Fixpoint touch (t : list (positive * Z)) (Sv : tree unit) (L : list positive) : tree unit * list positive :=
  match t with
  | [] => (Sv, L)
  | (x, _) :: t' => match tget x Sv with Some _ => touch t' Sv L | None => touch t' (tset x tt Sv) (x :: L) end
  end.
Fixpoint prep0 (l : lin) (fs : list fact) (Sv : tree unit) (L : list positive) : tree unit * list positive * list (lin * Z * Z) :=
  match fs with
  | [] => (Sv, L, [])
  | f :: fs' =>
      if rel_okN l f then
        match fact_gN f with
        | Some (g, lo, hi) => let '(Sv1, L1) := touch (l_t g) Sv L in let '(Sv2, L2, r) := prep0 l fs' Sv1 L1 in (Sv2, L2, (g, lo, hi) :: r)
        | None => prep0 l fs' Sv L
        end
      else prep0 l fs' Sv L
  end.
Fixpoint mk_tbl (Zt : tree (Z * Z)) (L : list positive) (T : tree ventry) : tree ventry :=
  match L with
  | [] => T
  | x :: L' => match mk_ve (ne_fixl all ne (lvar x) (vr_get Zt x)) with Some e => mk_tbl Zt L' (tset x e T) | None => mk_tbl Zt L' T end
  end.
Fixpoint conv_cands (T : tree ventry) (raw : list (lin * Z * Z)) : tree ventry * list cand :=
  match raw with
  | [] => (T, [])
  | (g, lo, hi) :: raw' => let '(T1, c) := cand_of T g lo hi in let '(T2, cs) := conv_cands T1 raw' in (T2, c :: cs)
  end.
End N.
Fixpoint vr_tblS (Sv : tree unit) (fs : list fact) : tree (Z * Z) :=
  match fs with
  | [] => TEmpty
  | FRange (LIN 0 [(y, 1)]) lo hi :: fs' =>
      let t := vr_tblS Sv fs' in match tget y Sv with Some _ => tset y (iv_meet (lo, hi) (vr_get t y)) t | None => t end
  | FBits (LIN 0 [(y, 1)]) m v :: fs' =>
      let t := vr_tblS Sv fs' in match tget y Sv with Some _ => if Z.leb 0 m then tset y (iv_meet (bits_iv m v) (vr_get t y)) t else t | None => t end
  | _ :: fs' => vr_tblS Sv fs'
  end.
Definition prepS (ne all bfs : list fact) (l : lin) : tree ventry * list cand :=
  let '(Sv0, L0) := touch (l_t l) TEmpty [] in
  let '(Sv, L, raw) := prep0 ne all bfs l all Sv0 L0 in
  conv_cands ne all bfs (mk_tbl ne all (vr_tblS Sv bfs) L TEmpty) raw.
End IrN.
(* [comment removed for export] *)
Definition IR_NUM_MIN : nat := 16.
Definition irange (fs : list fact) (l : lin) : Z * Z :=
  match is_const l with
  | Some c => (c, c)
  | None =>
      if longer IR_NUM_MIN fs then
        let ne := ne_sub fs in let bfs := List.filter IrN.is_bare fs in let mfs := List.filter IrN.is_modb fs in
        let '(T, cs) := IrN.prepS ne fs bfs l in
        let r := IrN.irange0P ne fs bfs mfs T cs l in
        if Z.eqb (snd r) (fst r) then r else
        match ldiv8 l with
        | Some l' => let r' := IrN.irange0P ne fs bfs mfs T cs l' in
                     if (Z.leb 0 (fst r') && Z.ltb (8 * snd r') two64)%bool then iv_meet r (8 * fst r', 8 * snd r') else r
        | None => r
        end
      else
        let r := irange0 fs l in
        if Z.eqb (snd r) (fst r) then r else
        match ldiv8 l with
        | Some l' => let r' := irange0 fs l' in
                     if (Z.leb 0 (fst r') && Z.ltb (8 * snd r') two64)%bool then iv_meet r (8 * fst r', 8 * snd r') else r
        | None => r
        end
  end.
(* [comment removed for export] *)
Definition pow2_neg (c : Z) : option Z :=
  let d := two64 - c in
  if (Z.ltb 1 d && Z.leb d 65536)%bool then let k := Z.log2 d in if Z.eqb d (2 ^ k) then Some k else None else None.
Fixpoint tcoef (t : list (positive * Z)) (q : positive) : Z :=
  match t with [] => 0 | (x, c) :: t' => if Pos.eqb x q then c else tcoef t' q end.
Definition srl_one (fs : list fact) (l g : lin) (lo hi : Z) (q : positive) (k : Z) (acc : Z * Z) : Z * Z :=
  let cl := tcoef (l_t l) q in
  let c := if Z.eqb cl 1 then 1 else if Z.eqb cl M64 then -1 else 0 in
  if Z.eqb c 0 then acc else
  let m := ladd (lscale (2 ^ k) l) (lscale c g) in
  let wm := rel_iv2 fs fs (l_t m) m (rel_base fs m) in
  let z := if Z.eqb c 1 then (fst wm - hi, snd wm - lo) else (fst wm + lo, snd wm + hi) in
  let w' := ((fst z + 2 ^ k - 1) / 2 ^ k, snd z / 2 ^ k) in
  if Z.ltb (Z.max (snd acc) (snd w') - Z.min (fst acc) (fst w')) (2 ^ (64 - k)) then iv_meet acc w' else acc.
Fixpoint srl_terms (fs : list fact) (l g : lin) (lo hi : Z) (t : list (positive * Z)) (acc : Z * Z) : Z * Z :=
  match t with
  | [] => acc
  | (q, cq) :: t' => match pow2_neg cq with
                     | Some k => srl_terms fs l g lo hi t' (srl_one fs l g lo hi q k acc)
                     | None => srl_terms fs l g lo hi t' acc
                     end
  end.
Fixpoint srl_iv (fs all : list fact) (l : lin) (acc : Z * Z) : Z * Z :=
  match fs with
  | [] => acc
  | FRange g lo hi :: fs' => if shares (l_t l) (l_t g) then srl_iv fs' all l (srl_terms all l g lo hi (l_t g) acc) else srl_iv fs' all l acc
  | FCond c a b tk :: fs' =>
      if (shares (l_t l) (l_t a) || shares (l_t l) (l_t b))%bool then
        match fact_g all (FCond c a b tk) with
        | Some (g, lo, hi) => srl_iv fs' all l (srl_terms all l g lo hi (l_t g) acc)
        | None => srl_iv fs' all l acc
        end
      else srl_iv fs' all l acc
  | _ :: fs' => srl_iv fs' all l acc
  end.
(* [comment removed for export] *)
Definition irange_x_ref (fs : list fact) (l : lin) : Z * Z :=
  match is_const l with
  | Some c => (c, c)
  | None => let v := ne_int_fixl fs fs l (lround fs l (srl_iv fs fs l (rel_iv2 fs fs (l_t l) l (rel_iv fs fs l (l_iv fs l))))) in
            let r := ne_refine' fs l (wrap_iv v) in
            let a := lalign fs l in if Z.ltb 0 a then align_iv a r else r
  end.
Section F2.
Variables (vt : tree (Z * Z)) (ne all : list fact).
(* [comment removed for export] *)
Definition rel_baseF (l : lin) : Z * Z := frange_same all l (ne_int ne l (rel_ivF vt ne all all l (l_ivF vt ne all l))).
Fixpoint rel_iv2F (fs : list fact) (ta : list (positive * Z)) (l : lin) (acc : Z * Z) : Z * Z :=
  match fs with
  | [] => acc
  | f :: fs' =>
      if rel_ok3 ta f then
      match fact_gF vt ne all f with
      | Some (g, lo0, hi0) =>
          let '(lo, hi) := ne_int_fixl all ne g (lo0, hi0) in
          let d1 := lsub l g in let d2 := ladd l g in
          let r1 := rel_baseF d1 in
          let r2 := rel_baseF d2 in
          rel_iv2F fs' ta l (meet_win (meet_win acc (lo + fst r1, hi + snd r1)) (fst r2 - hi, snd r2 - lo))
      | None => rel_iv2F fs' ta l acc
      end
      else rel_iv2F fs' ta l acc
  end.
Definition srl_oneF (l g : lin) (lo hi : Z) (q : positive) (k : Z) (acc : Z * Z) : Z * Z :=
  let cl := tcoef (l_t l) q in
  let c := if Z.eqb cl 1 then 1 else if Z.eqb cl M64 then -1 else 0 in
  if Z.eqb c 0 then acc else
  let m := ladd (lscale (2 ^ k) l) (lscale c g) in
  let wm := rel_iv2F all (l_t m) m (rel_baseF m) in
  let z := if Z.eqb c 1 then (fst wm - hi, snd wm - lo) else (fst wm + lo, snd wm + hi) in
  let w' := ((fst z + 2 ^ k - 1) / 2 ^ k, snd z / 2 ^ k) in
  if Z.ltb (Z.max (snd acc) (snd w') - Z.min (fst acc) (fst w')) (2 ^ (64 - k)) then iv_meet acc w' else acc.
Fixpoint srl_termsF (l g : lin) (lo hi : Z) (t : list (positive * Z)) (acc : Z * Z) : Z * Z :=
  match t with
  | [] => acc
  | (q, cq) :: t' => match pow2_neg cq with
                     | Some k => srl_termsF l g lo hi t' (srl_oneF l g lo hi q k acc)
                     | None => srl_termsF l g lo hi t' acc
                     end
  end.
Fixpoint srl_ivF (fs : list fact) (l : lin) (acc : Z * Z) : Z * Z :=
  match fs with
  | [] => acc
  | FRange g lo hi :: fs' => if shares (l_t l) (l_t g) then srl_ivF fs' l (srl_termsF l g lo hi (l_t g) acc) else srl_ivF fs' l acc
  | FCond c a b tk :: fs' =>
      if (shares (l_t l) (l_t a) || shares (l_t l) (l_t b))%bool then
        match fact_gF vt ne all (FCond c a b tk) with
        | Some (g, lo, hi) => srl_ivF fs' l (srl_termsF l g lo hi (l_t g) acc)
        | None => srl_ivF fs' l acc
        end
      else srl_ivF fs' l acc
  | _ :: fs' => srl_ivF fs' l acc
  end.
Definition irange_x0F (l : lin) : Z * Z :=
  let v := ne_int_fixl all ne l (lround all l (srl_ivF all l (rel_iv2F all (l_t l) l (rel_ivF vt ne all all l (l_ivF vt ne all l))))) in
  let r := ne_fixl all ne l (wrap_iv v) in
  let a := lalign all l in if Z.ltb 0 a then align_iv a r else r.
End F2.
(* [comment removed for export] *)
Module IrX.
Section X.
Variables (ne all bfs mfs : list fact).
Fixpoint rel_NT (l : lin) (cl : clin) (fs : list fact) (T : tree ventry) (acc : wiv) : tree ventry * (Z * Z) :=
  match fs with
  | [] => (T, wiv2z acc)
  | f :: fs' =>
      if IrN.rel_okN l f then
      match IrN.fact_gN ne all bfs f with
      | Some (g, lo, hi) =>
          match IrN.wstep ne all bfs T cl g lo hi acc with
          | Some (T', acc') => rel_NT l cl fs' T' acc'
          | None => (T, IrN.rel_ivN ne all bfs fs l (wiv2z acc))
          end
      | None => rel_NT l cl fs' T acc
      end
      else rel_NT l cl fs' T acc
  end.
Definition rel_topT (T : tree ventry) (l : lin) : tree ventry * (Z * Z) :=
  match IrN.conv_l ne all bfs T l with
  | Some (T1, cl) => match cl_iv cl with Some acc => rel_NT l cl all T1 acc | None => (T1, IrN.rel_ivN ne all bfs all l (IrN.l_ivN ne all bfs l)) end
  | None => (T, IrN.rel_ivN ne all bfs all l (IrN.l_ivN ne all bfs l))
  end.
Definition rel_baseT (T : tree ventry) (d : lin) : tree ventry * (Z * Z) :=
  let '(T1, r) := rel_topT T d in (T1, frange_same all d (ne_int ne d r)).
Fixpoint rel_iv2T (fs : list fact) (ta : list (positive * Z)) (l : lin) (T : tree ventry) (acc : Z * Z) : tree ventry * (Z * Z) :=
  match fs with
  | [] => (T, acc)
  | f :: fs' =>
      if rel_ok3 ta f then
      match IrN.fact_gN ne all bfs f with
      | Some (g, lo0, hi0) =>
          let '(lo, hi) := ne_int_fixl all ne g (lo0, hi0) in
          let '(T1, r1) := rel_baseT T (lsub l g) in
          let '(T2, r2) := rel_baseT T1 (ladd l g) in
          rel_iv2T fs' ta l T2 (meet_win (meet_win acc (lo + fst r1, hi + snd r1)) (fst r2 - hi, snd r2 - lo))
      | None => rel_iv2T fs' ta l T acc
      end
      else rel_iv2T fs' ta l T acc
  end.
Definition srl_oneT (T : tree ventry) (l g : lin) (lo hi : Z) (q : positive) (k : Z) (acc : Z * Z) : tree ventry * (Z * Z) :=
  let cl := tcoef (l_t l) q in
  let c := if Z.eqb cl 1 then 1 else if Z.eqb cl M64 then -1 else 0 in
  if Z.eqb c 0 then (T, acc) else
  let m := ladd (lscale (2 ^ k) l) (lscale c g) in
  let '(T1, b) := rel_baseT T m in
  let '(T2, wm) := rel_iv2T all (l_t m) m T1 b in
  let z := if Z.eqb c 1 then (fst wm - hi, snd wm - lo) else (fst wm + lo, snd wm + hi) in
  let w' := ((fst z + 2 ^ k - 1) / 2 ^ k, snd z / 2 ^ k) in
  (T2, if Z.ltb (Z.max (snd acc) (snd w') - Z.min (fst acc) (fst w')) (2 ^ (64 - k)) then iv_meet acc w' else acc).
Fixpoint srl_termsT (T : tree ventry) (l g : lin) (lo hi : Z) (t : list (positive * Z)) (acc : Z * Z) : tree ventry * (Z * Z) :=
  match t with
  | [] => (T, acc)
  | (q, cq) :: t' => match pow2_neg cq with
                     | Some k => let '(T1, a1) := srl_oneT T l g lo hi q k acc in srl_termsT T1 l g lo hi t' a1
                     | None => srl_termsT T l g lo hi t' acc
                     end
  end.
Fixpoint srl_ivT (fs : list fact) (l : lin) (T : tree ventry) (acc : Z * Z) : tree ventry * (Z * Z) :=
  match fs with
  | [] => (T, acc)
  | FRange g lo hi :: fs' => if IrN.sharesN (l_t l) (l_t g) then let '(T1, a1) := srl_termsT T l g lo hi (l_t g) acc in srl_ivT fs' l T1 a1 else srl_ivT fs' l T acc
  | FCond c a b tk :: fs' =>
      if (if IrN.sharesN (l_t l) (l_t a) then true else IrN.sharesN (l_t l) (l_t b)) then
        match IrN.fact_gN ne all bfs (FCond c a b tk) with
        | Some (g, lo, hi) => let '(T1, a1) := srl_termsT T l g lo hi (l_t g) acc in srl_ivT fs' l T1 a1
        | None => srl_ivT fs' l T acc
        end
      else srl_ivT fs' l T acc
  | _ :: fs' => srl_ivT fs' l T acc
  end.
Definition irange_x0N (l : lin) : Z * Z :=
  let '(T1, a0) := rel_topT TEmpty l in
  let '(T2, a1) := rel_iv2T all (l_t l) l T1 a0 in
  let '(_, a2) := srl_ivT all l T2 a1 in
  let v := ne_int_fixl all ne l (lround mfs l a2) in
  let r := ne_fixl all ne l (wrap_iv v) in
  let a := lalign mfs l in if Z.ltb 0 a then align_iv a r else r.
End X.
End IrX.
Definition irange_x (fs : list fact) (l : lin) : Z * Z :=
  match is_const l with
  | Some c => (c, c)
  | None => if longer IR_FAST_MIN fs then IrX.irange_x0N (ne_sub fs) fs (List.filter IrN.is_bare fs) (List.filter IrN.is_modb fs) l
            else let v := ne_int_fixl fs fs l (lround fs l (srl_iv fs fs l (rel_iv2 fs fs (l_t l) l (rel_iv fs fs l (l_iv fs l))))) in
                 let r := ne_refine' fs l (wrap_iv v) in
                 let a := lalign fs l in if Z.ltb 0 a then align_iv a r else r
  end.


(* [comment removed for export] *)
Definition tn_of (fs : list fact) (l : lin) : Z * Z :=
  match is_const l with
  | Some c => (Z.ones 64, c)
  | None =>
      let '(lo, hi) := irange fs l in
      let t1 := tn_join (tn_range (Z.max 0 lo) (Z.min (Z.ones 64) hi)) (tn_low fs l) in
      match l with LIN 0 [(x, 1)] => tn_join t1 (var_bits fs x) | _ => t1 end
  end.
Definition tn_alu (fs : list fact) (op : aluop) (a b : lin) : option (Z * Z) :=
  match op with
  | ALU_AND => Some (tn_and (tn_of fs a) (tn_of fs b))
  | ALU_OR => Some (tn_or (tn_of fs a) (tn_of fs b))
  | ALU_XOR => Some (tn_xor (tn_of fs a) (tn_of fs b))
  | ALU_SRL => match is_const b with Some k => Some (tn_srl (Z.land k 63) (tn_of fs a)) | None => None end
  | ALU_SLL => match is_const b with Some k => Some (tn_sll (Z.land k 63) (tn_of fs a)) | None => None end
  | _ => None
  end.

(* [comment removed for export] *)
Definition size_lo (fs : list fact) (R : region) : Z :=
  match is_const (rg_size R) with Some c => c | None => fst (irange fs (rg_size R)) end.
(* [comment removed for export] *)
Definition rg_off (fs : list fact) (R : region) (a : lin) (w : Z) : option Z :=
  match lin_off a (rg_base R) with
  | Some o => if (Z.leb 0 o && Z.leb (o + w) (size_lo fs R))%bool then Some o else None
  | None => None
  end.
(* [comment removed for export] *)
Fixpoint find_rg (fs : list fact) (rgs : list region) (a : lin) (w : Z) (i : nat) : option (nat * region * Z) :=
  match rgs with
  | [] => None
  | R :: rs => match rg_off fs R a w with Some o => Some (i, R, o) | None => find_rg fs rs a w (S i) end
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rel_in (fs : list fact) (R : region) (a : lin) (w hi : Z) : bool :=
  let '(dlo, dhi) := irange fs (lsub (rg_size R) (lsub a (rg_base R))) in
  Z.leb w dlo &&& Z.ltb dhi 4611686018427387904 &&& Z.ltb hi 4611686018427387904 &&&
   Z.ltb (snd (irange fs (rg_size R))) 4611686018427387904.
Definition rg_off_sym (fs : list fact) (R : region) (a : lin) (w : Z) : option (Z * Z) :=
  let '(lo, hi) := irange fs (lsub a (rg_base R)) in
  if Z.leb 0 lo then
    if Z.leb (hi + w) (size_lo fs R) then Some (lo, hi)
    else if rel_in fs R a w hi then Some (lo, hi) else None
  else None.
(* [comment removed for export] *)
Definition rg_cz (R : region) : option (Z * Z) :=
  match is_const (rg_base R), is_const (rg_size R) with Some c, Some z => Some (c, z) | _, _ => None end.
Fixpoint find_rg_c (win : Z * Z) (w : Z) (rgs : list region) (i : nat) : option (nat * region * (Z * Z)) :=
  match rgs with
  | [] => None
  | R :: rs => match rg_cz R with
               | Some (c, z) => if (Z.leb c (fst win) && Z.leb (snd win + w) (c + z))%bool then Some (i, R, (fst win - c, snd win - c))
                                else find_rg_c win w rs (S i)
               | None => find_rg_c win w rs (S i)
               end
  end.
Fixpoint find_rg_sym1 (fs : list fact) (rgs : list region) (a : lin) (w : Z) (i : nat) : option (nat * region * (Z * Z)) :=
  match rgs with
  | [] => None
  | R :: rs => match rg_cz R with
               | Some _ => find_rg_sym1 fs rs a w (S i)
               | None => match rg_off_sym fs R a w with Some r => Some (i, R, r) | None => find_rg_sym1 fs rs a w (S i) end
               end
  end.
(* [comment removed for export] *)
Definition rel_inx (fs : list fact) (R : region) (a : lin) (w hi : Z) : bool :=
  let '(dlo, dhi) := irange_x fs (lsub (rg_size R) (lsub a (rg_base R))) in
  Z.leb w dlo &&& Z.ltb dhi 4611686018427387904 &&& Z.ltb hi 4611686018427387904 &&&
   Z.ltb (snd (irange_x fs (rg_size R))) 4611686018427387904.
Definition rg_off_symx (fs : list fact) (R : region) (a : lin) (w : Z) : option (Z * Z) :=
  let '(lo, hi) := irange_x fs (lsub a (rg_base R)) in
  if Z.leb 0 lo then
    if Z.leb (hi + w) (size_lo fs R) then Some (lo, hi)
    else if rel_inx fs R a w hi then Some (lo, hi) else None
  else None.
Fixpoint find_rg_symx (fs : list fact) (rgs : list region) (a : lin) (w : Z) (i : nat) : option (nat * region * (Z * Z)) :=
  match rgs with
  | [] => None
  | R :: rs => match rg_cz R with
               | Some _ => find_rg_symx fs rs a w (S i)
               | None => match rg_off_symx fs R a w with Some r => Some (i, R, r) | None => find_rg_symx fs rs a w (S i) end
               end
  end.
(* [comment removed for export] *)
Fixpoint find_rg_sym1a (fs : list fact) (rgs : list region) (a : lin) (w : Z) (i : nat) : option (nat * region * (Z * Z)) :=
  match rgs with
  | [] => None
  | R :: rs => match rg_off_sym fs R a w with Some r => Some (i, R, r) | None => find_rg_sym1a fs rs a w (S i) end
  end.
Fixpoint find_rg_symxa (fs : list fact) (rgs : list region) (a : lin) (w : Z) (i : nat) : option (nat * region * (Z * Z)) :=
  match rgs with
  | [] => None
  | R :: rs => match rg_off_symx fs R a w with Some r => Some (i, R, r) | None => find_rg_symxa fs rs a w (S i) end
  end.
(* [comment removed for export] *)
Definition find_rg_sym_ref (fs : list fact) (rgs : list region) (a : lin) (w : Z) (i : nat) : option (nat * region * (Z * Z)) :=
  match find_rg_c (irange fs a) w rgs i with
  | Some r => Some r
  | None => match find_rg_sym1 fs rgs a w i with
            | Some r => Some r
            | None => match find_rg_c (irange_x fs a) w rgs i with
                      | Some r => Some r
                      | None => match find_rg_symx fs rgs a w i with
                                | Some r => Some r
                                | None => match find_rg_sym1a fs rgs a w i with Some r => Some r | None => find_rg_symxa fs rgs a w i end
                                end
                      end
            end
  end.
(* [comment removed for export] *)
Definition rg_pick (a : lin) (c : bool) (R : region) : bool :=
  match rg_cz R with Some _ => false | None => if shares (l_t a) (l_t (rg_base R)) then c else negb c end.
Fixpoint find_rg_symP (p : region -> bool) (fs : list fact) (rgs : list region) (a : lin) (w : Z) (i : nat) : option (nat * region * (Z * Z)) :=
  match rgs with
  | [] => None
  | R :: rs => if p R then match rg_off_sym fs R a w with Some r => Some (i, R, r) | None => find_rg_symP p fs rs a w (S i) end
               else find_rg_symP p fs rs a w (S i)
  end.
Fixpoint find_rg_symxP (p : region -> bool) (fs : list fact) (rgs : list region) (a : lin) (w : Z) (i : nat) : option (nat * region * (Z * Z)) :=
  match rgs with
  | [] => None
  | R :: rs => if p R then match rg_off_symx fs R a w with Some r => Some (i, R, r) | None => find_rg_symxP p fs rs a w (S i) end
               else find_rg_symxP p fs rs a w (S i)
  end.
Definition find_rg_sym (fs : list fact) (rgs : list region) (a : lin) (w : Z) (i : nat) : option (nat * region * (Z * Z)) :=
  match find_rg_c (irange fs a) w rgs i with
  | Some r => Some r
  | None =>
  match find_rg_symP (rg_pick a true) fs rgs a w i with
  | Some r => Some r
  | None =>
  match find_rg_symP (rg_pick a false) fs rgs a w i with
  | Some r => Some r
  | None =>
  match find_rg_c (irange_x fs a) w rgs i with
  | Some r => Some r
  | None =>
  match find_rg_symxP (rg_pick a true) fs rgs a w i with
  | Some r => Some r
  | None =>
  match find_rg_symxP (rg_pick a false) fs rgs a w i with
  | Some r => Some r
  | None => match find_rg_sym1a fs rgs a w i with Some r => Some r | None => find_rg_symxa fs rgs a w i end
  end end end end end end.

(* [comment removed for export] *)
Fixpoint tfilter_acc {A} (f : positive -> bool) (t : tree A) (k : positive -> positive) : tree A :=
  match t with
  | TEmpty => TEmpty
  | TNode l v r => TNode (tfilter_acc f l (fun p => k (xO p)))
                         (match v with Some x => if f (k xH) then Some x else None | None => None end)
                         (tfilter_acc f r (fun p => k (xI p)))
  end.
Definition tfilter {A} (f : positive -> bool) (t : tree A) : tree A := tfilter_acc f t (fun p => p).
(* [comment removed for export] *)
Definition havoc_range (t : tree bval) (lo hi : Z) : tree bval :=
  tfilter (fun p => negb (Z.leb lo (Zpos p - 1) && Z.ltb (Zpos p - 1) hi)) t.
(* [comment removed for export] *)
Fixpoint tall {A} (f : A -> bool) (t : tree A) : bool :=
  match t with TEmpty => true | TNode l v r => match v with Some x => f x | None => true end &&& tall f l &&& tall f r end.
Definition is_bk0 (v : bval) : bool := match v with BK 0 => true | _ => false end.
(* [comment removed for export] *)
Fixpoint tclr {A} (p : positive) (t : tree A) : tree A :=
  match t with
  | TEmpty => TEmpty
  | TNode l v r => match p with xH => TNode l None r | xO q => TNode (tclr q l) v r | xI q => TNode l v (tclr q r) end
  end.
(* [comment removed for export] *)
Fixpoint put_bytes_z (t : tree bval) (o : Z) (l : list bval) : tree bval :=
  match l with [] => t | v :: l' => put_bytes_z (if is_bk0 v then tclr (okey o) t else tset (okey o) v t) (o + 1) l' end.
(* [comment removed for export] *)
Definition range_zero (t : tree bval) (lo hi : Z) : bool :=
  tall is_bk0 (tfilter (fun p => (Z.leb lo (Zpos p - 1) && Z.ltb (Zpos p - 1) hi)%bool) t).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint tdivb (k : Z) (t : list (positive * Z)) : bool :=
  match t with [] => true | (_, c) :: t' => (Z.eqb (Z.land c (Z.ones k)) 0 && tdivb k t')%bool end.
(* [comment removed for export] *)
Fixpoint tdiv2 (k : Z) (t : list (positive * Z)) : option (list (positive * Z)) :=
  match t with
  | [] => Some []
  | (x, c) :: t' =>
      let v := sgn64 c in
      if Z.eqb (Z.land v (Z.ones k)) 0 then
        match tdiv2 k t' with Some r => Some ((x, w64 (Z.shiftr v k)) :: r) | None => None end
      else None
  end.
(* [comment removed for export] *)
Fixpoint tsplit (k : Z) (t : list (positive * Z)) : list (positive * Z) * list (positive * Z) :=
  match t with
  | [] => ([], [])
  | (x, c) :: t' => let '(d, r) := tsplit k t' in
                    if Z.eqb (Z.land c (Z.ones k)) 0 then ((x, c) :: d, r) else (d, (x, c) :: r)
  end.
(* [comment removed for export] *)
Definition win (fs : list fact) (k : Z) (l : lin) : option (list (positive * Z) * list (positive * Z) * Z) :=
  let '(dt, rt) := tsplit k (l_t l) in
  match rt with
  | [] => Some (dt, rt, Z.shiftr (sgn64 (l_c l)) k)
  | _ =>
      let R := LIN (l_c l) rt in
      if nowrap (l_iv fs R) then
        let '(lo, hi) := irange fs R in
        let t := Z.shiftr lo k in if Z.eqb t (Z.shiftr hi k) then Some (dt, rt, t) else None
      else None
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint t_riv (fs : list fact) (t : list (positive * Z)) : Z * Z :=
  match t with
  | [] => (0, 0)
  | (y, k) :: t' => iv_add (iv_scale (sgn64 k) (rel_iv fs fs (lvar y) (l_iv fs (lvar y)))) (t_riv fs t')
  end.
(* [comment removed for export] *)
Fixpoint t_rivN (ne all bfs : list fact) (t : list (positive * Z)) : Z * Z :=
  match t with [] => (0, 0) | (y, k) :: t' => iv_add (iv_scale (sgn64 k) (IrN.rel_topN ne all bfs (lvar y))) (t_rivN ne all bfs t') end.
Definition t_rivQ (fs : list fact) (t : list (positive * Z)) : Z * Z :=
  if longer IR_NUM_MIN fs then t_rivN (ne_sub fs) fs (List.filter IrN.is_bare fs) t else t_riv fs t.
Definition srl_shift (fs : list fact) (k : Z) (a : lin) : option lin :=
  let iv := l_iv fs a in let K := Z.shiftr (fst iv) 64 in
  if Z.eqb K (Z.shiftr (snd iv) 64) then
    match tdiv2 k (l_t a) with
    | Some dt' => Some (LIN (w64 (Z.shiftr (sgn64 (l_c a) - K * two64) k)) dt')
    | None => None
    end
  else None.
(* [comment removed for export] *)
Definition srl_shift_r (fs : list fact) (k : Z) (a : lin) : option lin :=
  let iv := iv_add (sgn64 (l_c a), sgn64 (l_c a)) (t_rivQ fs (l_t a)) in
  let K := Z.shiftr (fst iv) 64 in
  if Z.eqb K (Z.shiftr (snd iv) 64) then
    match tdiv2 k (l_t a) with
    | Some dt' => Some (LIN (w64 (Z.shiftr (sgn64 (l_c a) - K * two64) k)) dt')
    | None => None
    end
  else None.
(* [comment removed for export] *)
Definition srl_lin (fs : list fact) (k : Z) (a : lin) : option lin :=
  if nowrap (l_iv fs a) then
    match win fs k a with
    | Some (dt, _, t) => match tdiv2 k dt with Some dt' => Some (LIN (w64 t) dt') | None => None end
    | None => None
    end
  else match srl_shift fs k a with Some l => Some l | None => srl_shift_r fs k a end.
(* [comment removed for export] *)
Definition and_lin (fs : list fact) (m : Z) (a : lin) : option lin :=
  let k := ctz64 (m + 1) in
  if Z.eqb m (Z.ones k) then
    match win fs k a with Some (_, rt, t) => Some (LIN (w64 (l_c a - 2 ^ k * t)) rt) | None => None end
  else
    let k' := ctz64 m in
    if Z.eqb m (w64 (- 2 ^ k')) then
      match win fs k' a with Some (dt, _, t) => Some (LIN (w64 (2 ^ k' * t)) dt) | None => None end
    else None.
(* [comment removed for export] *)
Definition and_low (fs : list fact) (m : Z) (a : lin) : option lin :=
  let k := Z.log2 m + 1 in
  if (Z.leb 1 m && Z.leb k 64)%bool then match lowb fs a k with Some r => Some (lconst (Z.land r m)) | None => None end else None.
(* [comment removed for export] *)
Definition and_hi (fs : list fact) (m : Z) (a : lin) : option lin :=
  let k := ctz64 m in
  if (Z.eqb m (w64 (- 2 ^ k)) && Z.leb 1 k && Z.leb k 63)%bool then
    match lowb fs a k with Some r => Some (laddc a (- r)) | None => None end
  else None.
Definition and_lowhi (fs : list fact) (m : Z) (a : lin) : option lin :=
  match and_low fs m a with Some l => Some l | None => and_hi fs m a end.
(* [comment removed for export] *)
Definition and_band (fs : list fact) (m : Z) (a : lin) : option lin :=
  let k := ctz64 m in let j := Z.log2 (m + 2 ^ k) in
  if Z.ltb 0 k &&& Z.ltb k j &&& Z.ltb j 64 &&& Z.eqb m (2 ^ j - 2 ^ k) &&& Z.ltb (snd (irange fs a)) (2 ^ j)
  then match and_lin fs (w64 (- 2 ^ k)) a with Some l => Some l | None => and_lowhi fs (w64 (- 2 ^ k)) a end
  else None.
Definition and_lin3 (fs : list fact) (m : Z) (a : lin) : option lin :=
  match and_lin fs m a with Some l => Some l | None => match and_lowhi fs m a with Some l => Some l | None => and_band fs m a end end.
(* [comment removed for export] *)
Definition or_go (fs : list fact) (x y : lin) : option lin :=
  let r := irange fs y in
  let k := Z.log2 (snd r) + 1 in
  if (Z.leb 0 (fst r) && Z.leb 1 k && Z.leb k 63)%bool then
    match lowb fs x k with Some r0 => if Z.eqb r0 0 then Some (ladd x y) else None | None => None end
  else None.
Definition or_lin (fs : list fact) (a b : lin) : option lin := match or_go fs a b with Some l => Some l | None => or_go fs b a end.
(* [comment removed for export] *)
Definition or_ones (fs : list fact) (m : Z) (a : lin) : option lin :=
  if (Z.leb 0 m && Z.ltb m two64)%bool then match and_lin fs m a with Some l => Some (laddc (lsub a l) m) | None => None end else None.
Definition or_lin2 (fs : list fact) (a b : lin) : option lin :=
  match is_const b with
  | Some m => match or_ones fs m a with Some l => Some l | None => or_lin fs a b end
  | None => match is_const a with
            | Some m => match or_ones fs m b with Some l => Some l | None => or_lin fs a b end
            | None => or_lin fs a b
            end
  end.
(* [comment removed for export] *)
Definition xor_low (fs : list fact) (m : Z) (a : lin) : option lin :=
  let k := Z.log2 m + 1 in
  if (Z.leb 1 m && Z.leb k 63)%bool then
    match and_lin3 fs (Z.ones k) a with
    | Some la => match is_const la with Some r => Some (laddc (lsub a la) (Z.lxor r m)) | None => None end
    | None => None
    end
  else None.
Definition ev_alu_lin (fs : list fact) (op : aluop) (a b : lin) : option lin :=
      match op, is_const b, is_const a with
      | ALU_ADD, _, _ => Some (ladd a b)
      | ALU_SUB, _, _ => Some (lsub a b)
      | ALU_SLL, Some k, _ => Some (lscale (2 ^ Z.land k 63) a)
      | ALU_SRL, Some k, _ => srl_lin fs (Z.land k 63) a
      | ALU_AND, Some m, _ => and_lin3 fs m a
      | ALU_AND, None, Some m => and_lin3 fs m b
      | ALU_XOR, Some m, _ => if Z.eqb m M64 then Some (lsub (lconst M64) a) else xor_low fs m a
      | ALU_XOR, None, Some m => if Z.eqb m M64 then Some (lsub (lconst M64) b) else xor_low fs m b
      | ALU_XOR, None, None => if lin_eqb a b then Some (lconst 0) else None     (* [comment removed for export] *)
      | ALU_OR, _, _ => or_lin2 fs a b
      | _, _, _ => None
      end.

(* [comment removed for export] *)
Definition bits_facts (fs : list fact) (op : aluop) (a b : lin) (x : lin) : list fact :=
  match lowb2 fs a b with
  | Some (k, ra, rb) =>
      match op with
      | ALU_AND => [FMod x k (Z.land ra rb)]
      | ALU_OR => [FMod x k (Z.lor ra rb)]
      | ALU_XOR => [FMod x k (Z.lxor ra rb)]
      | _ => []
      end
  | None => []
  end.
(* [comment removed for export] *)
Fixpoint cands_t (k : Z) (t : list (positive * Z)) (acc : list positive) : list positive :=
  match t with
  | [] => acc
  | (y, c) :: t' => if (Z.eqb c (2 ^ k) || Z.eqb c (two64 - 2 ^ k))%bool
                    then cands_t k t' (if existsb (Pos.eqb y) acc then acc else y :: acc) else cands_t k t' acc
  end.
Fixpoint srl_cands (k : Z) (ta : list (positive * Z)) (fs : list fact) (acc : list positive) : list positive :=
  match fs with
  | [] => acc
  | FRange g lo hi :: fs' =>
      (* [comment removed for export] *)
      if (Z.eqb lo 0 && Z.eqb hi (2 ^ k - 1))%bool then srl_cands k ta fs' acc else srl_cands k ta fs' (cands_t k (l_t g) acc)
  | FCond _ a b _ :: fs' => srl_cands k ta fs' (cands_t k (l_t b) (cands_t k (l_t a) acc))
  | _ :: fs' => srl_cands k ta fs' acc
  end.
Definition T62 : Z := 4611686018427387904.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition srl_ok0 (w : Z * Z) : bool := Z.leb 0 (fst w) &&& Z.ltb (snd w) T62.
Definition srl_possible (w : Z * Z) : bool :=
  let lo := fst w in let hi := snd w in
  Z.ltb lo (- two64) ||| Z.leb (two64 + two64) hi |||
  (Z.ltb lo T62 &&& Z.leb 0 hi) ||| (Z.ltb lo (two64 + T62) &&& Z.leb two64 hi) ||| (Z.ltb lo (- two64 + T62) &&& Z.leb (- two64) hi).
Definition srl_skip (wl : Z * Z) : bool := srl_ok0 wl &&& Z.ltb 0 (snd wl).
(* [comment removed for export] *)
Definition link_terms (f : fact) : list (positive * Z) :=
  match f with
  | FRange g _ _ => match l_t g with [_] => [] | t => t end
  | FCond _ a b _ => l_t a ++ l_t b
  | _ => []
  end.
Definition srl_v1 (fs : list fact) (ta : list (positive * Z)) : list (positive * Z) :=
  ta ++ List.flat_map (fun f => let t := link_terms f in if shares ta t then t else []) fs.
Fixpoint srl_near (fs : list fact) (v1 : list (positive * Z)) (y : positive) : bool :=
  match fs with
  | [] => false
  | f :: r => let t := link_terms f in if occ y t then (if shares v1 t then true else srl_near r v1 y) else srl_near r v1 y
  end.
Definition srl_win (fs : list fact) (ta : list (positive * Z)) (d : lin) : Z * Z :=
  let w0 := frange_same fs d (l_iv fs d) in
  if (srl_ok0 w0 ||| negb (srl_possible w0)) then w0 else rel_iv2 fs fs ta d (rel_base fs d).
Definition srl_one_fact (fs : list fact) (k : Z) (a x : lin) (y : positive) : list fact :=
  let Y := lvar y in let pk := 2 ^ k in let yr := var_range' fs y in
  let dl := lsub a (lscale pk Y) in let du := lsub (lscale pk Y) a in
  let wl := srl_win fs (l_t a) dl in
  (if (Z.leb 0 (fst wl) && Z.ltb (snd wl) T62 && Z.leb 0 (fst yr) && Z.ltb (pk * snd yr + snd wl) two64)%bool
   then [FRange (lsub x Y) (Z.shiftr (fst wl) k) (Z.shiftr (snd wl) k)] else []) ++
  (if srl_skip wl then [] else
   let wu := srl_win fs (l_t a) du in
   if (Z.leb 0 (fst wu) && Z.ltb (snd wu) T62 && Z.leb (snd wu) (pk * fst yr) && Z.ltb (pk * snd yr) two64)%bool
   then [FRange (lsub Y x) ((fst wu + pk - 1) / pk) ((snd wu + pk - 1) / pk)] else []).
(* [comment removed for export] *)
Definition srl_div (fs : list fact) (k : Z) (a x : lin) : list fact :=
  let pk := 2 ^ k in
  let td := List.filter (fun p => (Z.eqb (snd p mod pk) 0 && Z.ltb (snd p) 4611686018427387904)%bool) (l_t a) in
  let tr := List.filter (fun p => negb (Z.eqb (snd p mod pk) 0 && Z.ltb (snd p) 4611686018427387904)%bool) (l_t a) in
  let D := LIN 0 (List.map (fun p => (fst p, snd p / pk)) td) in
  let R := LIN (l_c a) tr in
  match td with
  | [] => []
  | _ => if (Z.ltb 0 k && Z.ltb k 64 && lin_eqb a (ladd (lscale pk D) R))%bool then
           let r := irange fs R in let d := irange fs D in
           if (Z.leb 0 (fst r) && Z.leb 0 (fst d) && Z.ltb (snd d * pk + snd r) two64)%bool
           then [FRange (lsub x D) (Z.shiftr (fst r) k) (Z.shiftr (snd r) k)] else []
         else []
  end.
Definition srl_facts_ref (fs : list fact) (k : Z) (a x : lin) : list fact :=
  if (Z.ltb 0 k && Z.ltb k 64)%bool then List.concat (List.map (srl_one_fact fs k a x) (List.filter (srl_near fs (srl_v1 fs (l_t a))) (srl_cands k (l_t a) fs []))) else [].
(* [comment removed for export] *)
Section SF.
Variables (vt : tree (Z * Z)) (ne all : list fact).
Definition srl_winF (ta : list (positive * Z)) (d : lin) : Z * Z :=
  let w0 := frange_same all d (l_ivF vt ne all d) in
  if (srl_ok0 w0 ||| negb (srl_possible w0)) then w0 else rel_iv2F vt ne all all ta d (rel_baseF vt ne all d).
Definition srl_one_factF (k : Z) (a x : lin) (y : positive) : list fact :=
  let Y := lvar y in let pk := 2 ^ k in let yr := var_rangeF vt ne all y in
  let dl := lsub a (lscale pk Y) in let du := lsub (lscale pk Y) a in
  let wl := srl_winF (l_t a) dl in
  (if (Z.leb 0 (fst wl) && Z.ltb (snd wl) T62 && Z.leb 0 (fst yr) && Z.ltb (pk * snd yr + snd wl) two64)%bool
   then [FRange (lsub x Y) (Z.shiftr (fst wl) k) (Z.shiftr (snd wl) k)] else []) ++
  (if srl_skip wl then [] else
   let wu := srl_winF (l_t a) du in
   if (Z.leb 0 (fst wu) && Z.ltb (snd wu) T62 && Z.leb (snd wu) (pk * fst yr) && Z.ltb (pk * snd yr) two64)%bool
   then [FRange (lsub Y x) ((fst wu + pk - 1) / pk) ((snd wu + pk - 1) / pk)] else []).
End SF.
Definition srl_facts (fs : list fact) (k : Z) (a x : lin) : list fact :=
  if (Z.ltb 0 k && Z.ltb k 64)%bool then
    (if longer IR_FAST_MIN fs then let vt := vr_tbl fs in let ne := ne_sub fs in
       List.concat (List.map (srl_one_factF vt ne fs k a x) (List.filter (srl_near fs (srl_v1 fs (l_t a))) (srl_cands k (l_t a) fs [])))
     else List.concat (List.map (srl_one_fact fs k a x) (List.filter (srl_near fs (srl_v1 fs (l_t a))) (srl_cands k (l_t a) fs []))))
  else [].
(* [comment removed for export] *)
Definition and_def (fs : list fact) (a : lin) (m : Z) (x : lin) : list fact :=
  let k := ctz64 m in
  let j := Z.log2 (m + 2 ^ k) in
  if Z.ltb 0 k &&& Z.leb k 16 &&&
      (Z.eqb m (w64 (- 2 ^ k)) ||| (Z.ltb k j &&& Z.ltb j 64 &&& Z.eqb m (2 ^ j - 2 ^ k) &&& Z.ltb (snd (irange fs a)) (2 ^ j)))
  then [FRange (lsub a x) 0 (2 ^ k - 1)] else [].
(* [comment removed for export] *)
Definition xor_nz (fs : list fact) (a b x : lin) : list fact := if Z.leb 1 (fst (irange fs (lsub a b))) then [FRange x 1 M64] else [].
Definition res_facts (fs : list fact) (op : aluop) (a b : lin) (x : lin) : list fact :=
  match op with
  | ALU_SLT | ALU_SLTU => [FRange x 0 1]
  | ALU_AND =>
      (match is_const b, is_const a with
       | Some m, _ => [FRange x 0 m; FMod x (ctz64 m) 0] ++ and_def fs a m x
       | None, Some m => [FRange x 0 m; FMod x (ctz64 m) 0] ++ and_def fs b m x
       | None, None => []
       end) ++ bits_facts fs op a b x
  | ALU_OR => bits_facts fs op a b x
  | ALU_XOR => xor_nz fs a b x ++ bits_facts fs op a b x
  | ALU_SRL => match is_const b with
               | Some kb => let k := Z.land kb 63 in let ia := irange fs a in
                            FRange x (Z.shiftr (fst ia) k) (Z.shiftr (snd ia) k) :: FRange (lsub a (lscale (2 ^ k) x)) 0 (2 ^ k - 1) ::
                            srl_div fs k a x ++ srl_facts fs k a x
               | None => [] end
  | _ => []
  end ++ match tn_alu fs op a b with Some (m, v) => if Z.eqb m 0 then [] else [FBits x m v] | None => [] end.
Definition nofacts (x : lin) : list fact := [].
Definition bit_facts (x : lin) : list fact := [FRange x 0 1].
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sext32_1 (fs : list fact) (r : lin) : bool :=
  let iv := iv_add (sgn64 (l_c r), sgn64 (l_c r)) (t_rivQ fs (l_t r)) in
  (Z.leb (-2147483648) (fst iv) && Z.ltb (snd iv) 2147483648)%bool.
Definition sext32_ok (fs : list fact) (r : lin) : bool :=
  let iv := l_iv fs r in
  (Z.leb (-2147483648) (fst iv) &&& Z.ltb (snd iv) 2147483648) |||
  (let ir := irange fs r in Z.ltb (snd ir) 2147483648 ||| Z.leb (two64 - 2147483648) (fst ir)) ||| sext32_1 fs r.
(* [comment removed for export] *)
Definition sx32 (z : Z) : Z := let z' := z mod 4294967296 in if Z.leb 2147483648 z' then z' - 4294967296 else z'.
(* [comment removed for export] *)
Definition nw32 (r : lin) : lin := LIN (w64 (sx32 (l_c r))) (l_t r).
(* [comment removed for export] *)
Definition lin_w (op : aluop) (a b : lin) : option lin :=
  match op with
  | ALU_ADD => Some (nw32 (ladd a b))
  | ALU_SUB => Some (nw32 (lsub a b))
  | ALU_SLL => match is_const b with Some k => Some (nw32 (lscale (2 ^ Z.land k 31) a)) | None => None end
  | _ => None
  end.
Definition ev_aluw0 (fs : list fact) (op : aluop) (a b : lin) : option lin :=
  match is_const a, is_const b with
  | Some x, Some y => Some (lconst (bv_unsigned (sext 64 (alu32 op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))))))
  | _, _ => match lin_w op a b with
            | Some r => if sext32_ok fs r then Some r else None
            | None => None
            end
  end.
Definition ev_mul (op : mulop) (a b : lin) : option lin :=
  match is_const a, is_const b with
  | Some x, Some y => Some (lconst (bv_unsigned (mul_div op (Z_to_bv 64 x) (Z_to_bv 64 y))))
  | None, Some y => match op with M_MUL => Some (lscale y a) | _ => None end
  | Some x, None => match op with M_MUL => Some (lscale x b) | _ => None end
  | None, None => None
  end.
(* [comment removed for export] *)
Definition mul_facts (fs : list fact) (op : mulop) (a b : lin) (x : lin) : list fact :=
  match op with
  | M_MULHU => [FRange x 0 (Z.shiftr (snd (irange fs a) * snd (irange fs b)) 64)]
  (* [comment removed for export] *)
  | M_MULH => let ra := snd (irange fs a) in let rb := snd (irange fs b) in
              if (Z.ltb ra 9223372036854775808 && Z.ltb rb 9223372036854775808)%bool then [FRange x 0 (Z.shiftr (ra * rb) 64)] else []
  | _ => []
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sra_w_facts (fs : list fact) (op : aluop) (a b : lin) (x : lin) : list fact :=
  match op, is_const b with
  | ALU_SRA, Some kb =>
      let k := Z.land kb 31 in let iv := l_iv fs a in
      if (Z.leb (- 2147483648) (fst iv) && Z.ltb (snd iv) 2147483648)%bool
      then [FRange (laddc x (- Z.shiftr (fst iv) k)) 0 (Z.shiftr (snd iv) k - Z.shiftr (fst iv) k)]
      else []
  | _, _ => []
  end.
Definition w_facts (fs : list fact) (op : aluop) (a b : lin) (x : lin) : list fact :=
  match lin_w op a b with
  | Some r => let k := Z.min 32 (lalign fs r) in if Z.ltb 0 k then [FMod x k 0] else []
  | None => []
  end ++ sra_w_facts fs op a b x.
(* [comment removed for export] *)
Definition ev_mulf (fs : list fact) (op : mulop) (a b : lin) : option lin :=
  match op, is_const b, is_const a with
  | M_REMU, Some m, None =>
      let k := ctz64 m in
      if (Z.eqb m (2 ^ k) && Z.leb k 63)%bool then match lowb fs a k with Some r => Some (lconst r) | None => None end else None
  | M_DIVU, Some m, None =>
      let k := ctz64 m in if (Z.eqb m (2 ^ k) && Z.leb k 63)%bool then srl_lin fs k a else None
  | _, _, _ => ev_mul op a b
  end.
Definition ev_mulw (fs : list fact) (op : mulop) (a b : lin) : option lin :=
  match is_const a, is_const b with
  | Some x, Some y => Some (lconst (bv_unsigned (sext 64 (mul_div op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))))))
  | _, _ => match op with
            | M_MUL => match ev_mul M_MUL a b with
                       | Some r => if sext32_ok fs r then Some r else None
                       | None => None
                       end
            | _ => None
            end
  end.
(* [comment removed for export] *)
Fixpoint fcond_lookup (fs : list fact) (c : branch_cond) (a b : lin) : option bool :=
  match fs with
  | [] => None
  | FCond c' a' b' tk :: fs' =>
      if (match c, c' with
          | BC_EQ, BC_EQ | BC_NE, BC_NE | BC_LT, BC_LT | BC_GE, BC_GE | BC_LTU, BC_LTU | BC_GEU, BC_GEU => true
          | _, _ => false end && lin_eqb a a' && lin_eqb b b')%bool
      then Some tk else fcond_lookup fs' c a b
  | _ :: fs' => fcond_lookup fs' c a b
  end.
(* [comment removed for export] *)
Definition ltu_by_range (fs : list fact) (a b : lin) : option bool :=
  let '(alo, ahi) := irange fs a in let '(blo, bhi) := irange fs b in
  if Z.ltb ahi blo then Some true else if Z.leb bhi alo then Some false else
  let '(lo1, hi1) := irange fs (lsub b a) in
  if (Z.leb 1 lo1 && Z.ltb (hi1 + ahi) two64)%bool then Some true else
  let '(lo2, hi2) := irange fs (lsub a b) in
  if Z.ltb (hi2 + bhi) two64 then Some false else None.
Definition eq_by_range (fs : list fact) (a b : lin) : option bool :=
  let '(lo, hi) := irange fs (lsub b a) in
  if (Z.eqb lo 0 && Z.eqb hi 0)%bool then Some true else if (Z.leb 1 lo && Z.leb hi M64)%bool then Some false else
  let '(lo', hi') := irange fs (lsub a b) in
  if (Z.leb 1 lo' && Z.leb hi' M64)%bool then Some false else None.
(* [comment removed for export] *)
Definition nonneg2 (fs : list fact) (a b : lin) : bool := Z.ltb (snd (irange fs a)) T63 &&& Z.ltb (snd (irange fs b)) T63.
(* [comment removed for export] *)
Definition swin (fs : list fact) (l : lin) : Z * Z := ne_int_fixl fs fs l (lround fs l (rel_iv fs fs l (l_iv fs l))).
Definition sfit (w : Z * Z) : bool := (Z.leb (- T63) (fst w) && Z.ltb (snd w) T63)%bool.
Definition lts_by_win (fs : list fact) (a b : lin) : option bool :=
  let wa := swin fs a in let wb := swin fs b in
  if (sfit wa && sfit wb)%bool then
    if Z.ltb (snd wa) (fst wb) then Some true
    else if Z.leb (snd wb) (fst wa) then Some false
    else let wd := swin fs (lsub a b) in
         if (sfit wd && sfit (fst wa - snd wb, snd wa - fst wb))%bool then
           if Z.ltb (snd wd) 0 then Some true else if Z.leb 0 (fst wd) then Some false else None
         else None
  else None.
Definition ev_br_known (fs : list fact) (c : branch_cond) (a b : lin) : option bool :=
  match fcond_lookup fs c a b with
  | Some tk => Some tk
  | None =>
      match c with
      | BC_LTU => ltu_by_range fs a b
      | BC_GEU => match ltu_by_range fs a b with Some v => Some (negb v) | None => None end
      | BC_EQ => eq_by_range fs a b
      | BC_NE => match eq_by_range fs a b with Some v => Some (negb v) | None => None end
      | BC_LT => if nonneg2 fs a b then ltu_by_range fs a b else lts_by_win fs a b
      | BC_GE => if nonneg2 fs a b then match ltu_by_range fs a b with Some v => Some (negb v) | None => None end
                 else match lts_by_win fs a b with Some v => Some (negb v) | None => None end
      end
  end.
Definition ev_br_sym (fs : list fact) (c : branch_cond) (a b : lin) : option bool :=
  match c with
  | BC_EQ => match lin_off a b with Some d => if Z.eqb d 0 then Some true else ev_br_known fs c a b | None => ev_br_known fs c a b end
  | BC_NE => match lin_off a b with Some d => if Z.eqb d 0 then Some false else ev_br_known fs c a b | None => ev_br_known fs c a b end
  | _ => ev_br_known fs c a b
  end.
Definition ev_br (fs : list fact) (c : branch_cond) (a b : lin) : option bool :=
  match is_const a, is_const b with
  | Some x, Some y => Some (br_z c x y)
  | _, _ => ev_br_sym fs c a b
  end.

(* [comment removed for export] *)
Definition ev_alu0 (fs : list fact) (op : aluop) (a b : lin) : option lin :=
  match is_const a, is_const b with
  | Some x, Some y => Some (LIN (alu_z op x y) [])
  | _, _ =>
      match op with
      | ALU_SLTU => match ev_br fs BC_LTU a b with Some t => Some (lconst (if t then 1 else 0)) | None => None end
      | ALU_SLT => match ev_br fs BC_LT a b with Some t => Some (lconst (if t then 1 else 0)) | None => None end
      | _ =>
      match ev_alu_lin fs op a b with
      | Some l => Some l
      | None => match tn_alu fs op a b with
                | Some (m, v) => if Z.eqb m (Z.ones 64) then Some (lconst v) else None
                | None => None
                end
      end
      end
  end.

(* [comment removed for export] *)
Definition shift_op (op : aluop) : bool := match op with ALU_SLL | ALU_SRL | ALU_SRA => true | _ => false end.
Definition sh_amt (fs : list fact) (op : aluop) (k : Z) (b : lin) : lin :=
  if shift_op op then match is_const b with Some _ => b | None => match lowb fs b k with Some c => lconst c | None => b end end else b.
Definition ev_alu (fs : list fact) (op : aluop) (a b : lin) : option lin := ev_alu0 fs op a (sh_amt fs op 6 b).
Definition ev_aluw (fs : list fact) (op : aluop) (a b : lin) : option lin := ev_aluw0 fs op a (sh_amt fs op 5 b).

(* [comment removed for export] *)
Definition set_res (s : sst) (rd : positive) (r : option lin) (fs : lin -> list fact) (npc : Z) : sst :=
  match r with
  | Some l => SST npc (rset (s_regs s) rd l) (s_rgs s) (s_facts s) (s_next s) (s_resv s)
  | None => let x := lvar (s_next s) in
            SST npc (rset (s_regs s) rd x) (s_rgs s) (fs x ++ s_facts s) (Pos.succ (s_next s)) (s_resv s)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ld_small (fs : list fact) (v : lin) (sz : msize) (sg : bool) : bool :=
  match sz with
  | SZ1 => Z.ltb (snd (irange fs v)) (if sg then 128 else 256)
  | SZ2 => Z.ltb (snd (irange fs v)) (if sg then 32768 else 65536)
  | SZ4 => Z.ltb (snd (irange fs v)) (if sg then 2147483648 else 4294967296)
  | SZ8 => true
  end.
(* [comment removed for export] *)
Definition ld_neg (fs : list fact) (v : lin) (sz : msize) : option lin :=
  let r := irange fs v in
  match sz with
  | SZ1 => if (Z.leb 128 (fst r) && Z.leb (snd r) 255)%bool then Some (ladd v (lconst (two64 - 256))) else None
  | SZ2 => if (Z.leb 32768 (fst r) && Z.leb (snd r) 65535)%bool then Some (ladd v (lconst (two64 - 65536))) else None
  | SZ4 => if (Z.leb 2147483648 (fst r) && Z.leb (snd r) 4294967295)%bool then Some (ladd v (lconst (two64 - 4294967296))) else None
  | SZ8 => None
  end.
(* [comment removed for export] *)
Definition mix_term (fs : list fact) (b : bval) : option lin :=
  match b with
  | BK c => if (Z.leb 0 c && Z.ltb c 256)%bool then Some (lconst c) else None
  | BV v 0 => let r := irange fs v in if (Z.leb 0 (fst r) && Z.ltb (snd r) 256)%bool then Some v else None
  | _ => None
  end.
Fixpoint mix_lin (fs : list fact) (bvs : list bval) (p : Z) : option lin :=
  match bvs with
  | [] => Some (lconst 0)
  | b :: r => match mix_term fs b, mix_lin fs r (256 * p) with
              | Some t, Some l => Some (ladd (lscale p t) l)
              | _, _ => None
              end
  end.
Definition ld_mix (fs : list fact) (bvs : list bval) (sz : msize) (sg : bool) : option lin :=
  match mix_lin fs bvs 1 with
  | Some l => if ld_small fs l sz sg then Some l else None
  | None => None
  end.
Definition ld_bvs (fs : list fact) (bvs : list bval) (sz : msize) (sg : bool) : option lin :=
  match all_bk bvs with
  | Some bks => Some (lconst (bv_unsigned (ld_word sz sg (map (Z_to_bv 8) bks))))
  | None => match (match bvs with
                   | BV v 0 :: _ => if is_bv_of v 0 bvs then (if ld_small fs v sz sg then Some v else if sg then ld_neg fs v sz else None) else None
                   | _ => None
                   end) with
            | Some l => Some l
            | None => ld_mix fs bvs sz sg
            end
  end.
(* [comment removed for export] *)
Definition ld_value (img : tree Z) (fs : list fact) (R : region) (o : Z) (sz : msize) (sg : bool) : option lin :=
  match rg_kind R with
  | RO => match is_const (rg_base R) with
          | Some A => match img_bytes img (A + o) (nbytes sz) with
                      | Some bks => Some (lconst (bv_unsigned (ld_word sz sg (map (Z_to_bv 8) bks))))
                      | None => None
                      end
          | None => None
          end
  | RW =>
      match get_bytes (rg_cont R) o (nbytes sz) with
      | Some bvs => ld_bvs fs bvs sz sg
      | None => None
      end
  | RZ => ld_bvs fs (get_bytes_z (rg_cont R) o (nbytes sz)) sz sg
  | RI => match is_const (rg_base R) with
          | Some A => match get_bytes_i img (rg_cont R) A o (nbytes sz) with Some bvs => ld_bvs fs bvs sz sg | None => None end
          | None => None
          end
  | RT =>
      match get_bytes (rg_cont R) o (nbytes sz) with
      | Some bvs => ld_bvs fs bvs sz sg
      | None => None
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint uni_ld (img : tree Z) (fs : list fact) (R : region) (o : Z) (n : nat) (sz : msize) (sg : bool) (c : Z) : bool :=
  match n with
  | O => true
  | S n' => match ld_value img fs R o sz sg with
            | Some (LIN c' []) => Z.eqb c' c &&& uni_ld img fs R (o + 1) n' sz sg c
            | _ => false
            end
  end.
(* [comment removed for export] *)
Definition is_rz (k : rkind) : bool := match k with RZ => true | _ => false end.
Definition sym_ld (img : tree Z) (fs : list fact) (R : region) (lo hi : Z) (sz : msize) (sg : bool) : option lin :=
  if is_rz (rg_kind R) &&& range_zero (rg_cont R) lo (hi + Z.of_nat (nbytes sz)) then ld_value img fs R lo sz sg
  else if Z.leb (hi - lo) 512 then
    match ld_value img fs R lo sz sg with
    | Some (LIN c []) => if uni_ld img fs R lo (Z.to_nat (hi - lo + 1)) sz sg c then Some (LIN c []) else None
    | _ => None
    end
  else None.
(* [comment removed for export] *)
Definition load_at (img : tree Z) (fs : list fact) (rgs : list region) (a : lin) (sz : msize) (sg : bool) : option (option lin) :=
  match find_rg fs rgs a (Z.of_nat (nbytes sz)) O with
  | Some (_, R0, o) => Some (ld_value img fs R0 o sz sg)
  | None => match find_rg_sym fs rgs a (Z.of_nat (nbytes sz)) O with
            | Some (_, R0, (lo, hi)) => Some (sym_ld img fs R0 lo hi sz sg)
            | None => None
            end
  end.
(* [comment removed for export] *)
Fixpoint win_minmax (img : tree Z) (fs : list fact) (R : region) (o : Z) (n : nat) (acc : Z * Z) : option (Z * Z) :=
  match n with
  | O => Some acc
  | S n' => match ld_value img fs R o SZ1 false with
            | Some (LIN c []) => if (Z.leb 0 c && Z.leb c 255)%bool then win_minmax img fs R (o + 1) n' (Z.min (fst acc) c, Z.max (snd acc) c) else None
            | _ => None
            end
  end.
Definition e3_range (img : tree Z) (fs : list fact) (rgs : list region) (a : lin) : option (Z * Z) :=
  match find_rg fs rgs a 1 O with
  | Some _ => None
  | None => match find_rg_sym fs rgs a 1 O with
            | Some (_, R, (lo, hi)) => if Z.leb (hi - lo) 511 then win_minmax img fs R lo (Z.to_nat (hi - lo + 1)) (255, 0) else None
            | None => None
            end
  end.
Definition e3_facts (img : tree Z) (fs : list fact) (rgs : list region) (a : lin) (sz : msize) (sg : bool) : lin -> list fact :=
  match sz, sg with
  | SZ1, false => match e3_range img fs rgs a with Some (mn, mx) => fun x => [FRange x mn mx] | None => fun _ => [] end
  | _, _ => fun _ => []
  end.
(* [comment removed for export] *)
Definition byte_src (fs : list fact) (rgs : list region) (a : lin) : option (lin * Z) :=
  match find_rg fs rgs a 1 O with
  | Some (_, R, o) => match rg_kind R, tget (okey o) (rg_cont R) with
                      | RO, _ => None
                      | _, Some (BV v j) => Some (v, j)
                      | _, _ => None
                      end
  | None => None
  end.
(* [comment removed for export] *)
Definition ld_facts0 (fs : list fact) (rgs : list region) (a : lin) (sz : msize) (sg : bool) : lin -> list fact :=
  match sz, sg with
  | SZ1, false => match byte_src fs rgs a with Some (v, j) => fun x => [FByte x v j; FRange x 0 255] | None => fun x => [FRange x 0 255] end
  | SZ2, false => fun x => [FRange x 0 65535]
  | SZ4, false => fun x => [FRange x 0 4294967295]
  | _, _ => fun _ => []
  end.
(* [comment removed for export] *)
Fixpoint bvs_src (c : tree bval) (o : Z) (w : nat) : option (list (lin * Z)) :=
  match w with
  | O => Some []
  | S w' => match tget (okey o) c, bvs_src c (o + 1) w' with Some (BV v j), Some r => Some ((v, j) :: r) | _, _ => None end
  end.
Definition bytes_src (fs : list fact) (rgs : list region) (a : lin) (w : nat) : option (list (lin * Z)) :=
  match find_rg fs rgs a (Z.of_nat w) O with
  | Some (_, R, o) => match rg_kind R with RO => None | _ => bvs_src (rg_cont R) o w end
  | None => None
  end.
(* [comment removed for export] *)
Definition ld_facts (fs : list fact) (rgs : list region) (a : lin) (sz : msize) (sg : bool) : lin -> list fact :=
  match sz with
  | SZ1 => ld_facts0 fs rgs a sz sg
  | _ => match bytes_src fs rgs a (nbytes sz) with
         | Some bs => fun x => FBytes x bs :: ld_facts0 fs rgs a sz sg x
         | None => ld_facts0 fs rgs a sz sg
         end
  end.
Fixpoint find_fbyte (fs : list fact) (x : lin) : option (lin * Z) :=
  match fs with
  | [] => None
  | FByte x' v j :: fs' => if lin_eqb x' x then Some (v, j) else find_fbyte fs' x
  | _ :: fs' => find_fbyte fs' x
  end.
Fixpoint find_fbytes (fs : list fact) (x : lin) : option (list (lin * Z)) :=
  match fs with
  | [] => None
  | FBytes x' bs :: fs' => if lin_eqb x' x then Some bs else find_fbytes fs' x
  | _ :: fs' => find_fbytes fs' x
  end.
(* [comment removed for export] *)
Fixpoint unmix_term (ts : list (positive * Z)) (p : Z) : option positive :=
  match ts with [] => None | (x, a) :: r => if Z.eqb a p then Some x else unmix_term r p end.
Fixpoint unmix (l : lin) (j : Z) (p : Z) (n : nat) : list bval :=
  match n with
  | O => []
  | S n' => (match unmix_term (l_t l) p with Some x => BV (lvar x) 0 | None => BK (Z.land (Z.shiftr (l_c l) (8 * j)) 255) end)
            :: unmix l (j + 1) (256 * p) n'
  end.
Definition st_mix (fs : list fact) (v : lin) (w : nat) : option (list bval) :=
  if existsb (fun t => Z.leb 256 (snd t)) (l_t v) then
    let bvs := unmix v 0 1 w in
    match mix_lin fs bvs 1 with Some l => if lin_eqb l v then Some bvs else None | None => None end
  else None.
Definition st_vals (fs : list fact) (v : lin) (w : nat) : list bval :=
  match w, is_const v with
  | S O, None => match find_fbyte fs v with Some (v', j) => [BV v' j] | None => st_bytes v None 0 1 end
  | _, None => match find_fbytes fs v with
               | Some bs => if Nat.leb w (length bs) then List.map (fun p => BV (fst p) (snd p)) (firstn w bs) else st_bytes v None 0 w
               | None => match st_mix fs v w with Some bvs => bvs | None => st_bytes v None 0 w end
               end
  | _, _ => st_bytes v (is_const v) 0 w
  end.
(* [comment removed for export] *)
Definition store_at (fs : list fact) (rgs : list region) (a : lin) (w : nat) (bvs : list bval) : option (list region) :=
  match find_rg fs rgs a (Z.of_nat w) O with
  | Some (i, R0, o) =>
      match rg_kind R0 with
      | RW => Some (upd_nth rgs i (RG (rg_base R0) (rg_size R0) RW (put_bytes (rg_cont R0) o bvs)))
      | RZ => Some (upd_nth rgs i (RG (rg_base R0) (rg_size R0) RZ (put_bytes (rg_cont R0) o bvs)))   (* [comment removed for export] *)
      | RI => Some (upd_nth rgs i (RG (rg_base R0) (rg_size R0) RI (put_bytes (rg_cont R0) o bvs)))
      | RO | RT => None
      end
  | None =>
      match find_rg_sym fs rgs a (Z.of_nat w) O with
      | Some (i, R0, (lo, hi)) =>
          match rg_kind R0 with
          | RZ => if (forallb is_bk0 bvs && range_zero (rg_cont R0) lo (hi + Z.of_nat w))%bool
                  then Some (upd_nth rgs i (RG (rg_base R0) (rg_size R0) RZ (havoc_range (rg_cont R0) lo (hi + Z.of_nat w))))
                  else Some (upd_nth rgs i (RG (rg_base R0) (rg_size R0) RW (havoc_range (rg_cont R0) lo (hi + Z.of_nat w))))
          | RW | RI => Some (upd_nth rgs i (RG (rg_base R0) (rg_size R0) RW (havoc_range (rg_cont R0) lo (hi + Z.of_nat w))))
          | RO | RT => None
          end
      | None => None
      end
  end.
(* [comment removed for export] *)
Definition inval (r : rsv) (a : lin) : rsv :=
  match r with
  | RAt l => match lin_off l a with Some d => if Z.eqb d 0 then RNone else RAt l | None => RUnk end
  | RNone => RNone
  | RUnk => RUnk
  end.
(* [comment removed for export] *)
Definition sc_ok (r : rsv) (a : lin) : option bool :=
  match r with
  | RNone => Some false
  | RAt l => match lin_off l a with Some d => Some (Z.eqb d 0) | None => None end
  | RUnk => None
  end.
Definition amo_sz (wd : awidth) : msize := match wd with AW => SZ4 | AD => SZ8 end.
Definition amo_sg (wd : awidth) : bool := match wd with AW => true | AD => false end.
Definition amo_lg (wd : awidth) : Z := match wd with AW => 2 | AD => 3 end.
Definition fsz (fmt : ffmt) : msize := match fmt with FMT_S => SZ4 | FMT_D => SZ8 end.
(* [comment removed for export] *)
Definition amo_al (fs : list fact) (wd : awidth) (a : lin) : bool := Z.leb (amo_lg wd) (lalign fs a).
(* [comment removed for export] *)
Definition amo_new (op : amoop) (old src : lin) : lin := match op with AMO_ADD => ladd old src | _ => src end.

(* [comment removed for export] *)
Definition lclosed (n : positive) (l : lin) : bool := forallb (fun '(x, _) => Pos.ltb x n) (l_t l).
(* [comment removed for export] *)
Definition win_split (fs : list fact) (k : Z) (l : lin) : option (lin * Z) :=
  let '(dt, rt) := tsplit k (l_t l) in
  match rt with
  | [] => None
  | _ =>
      let R := LIN (l_c l) rt in
      if nowrap (l_iv fs R) then
        let '(lo, hi) := irange fs R in
        let t := Z.shiftr lo k in if Z.eqb (Z.shiftr hi k) (t + 1) then Some (R, 2 ^ k * (t + 1)) else None
      else None
  end.
Definition split_req (fs : list fact) (op : aluop) (a b : lin) : option (lin * Z) :=
  match op, is_const b with
  | ALU_SRL, Some k => win_split fs (Z.land k 63) a
  | ALU_AND, Some m =>
      let k' := ctz64 m in
      if Z.eqb m (w64 (- 2 ^ k')) then win_split fs k' a
      else let k := ctz64 (m + 1) in if Z.eqb m (Z.ones k) then win_split fs k a else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Inductive sres : Type :=
| SOk (s : sst)                                     (* [comment removed for export] *)
| SBr (c : branch_cond) (a b : lin) (tgt : Z)       (* [comment removed for export] *)
| SSplit (l : lin) (c : Z)                          (* [comment removed for export] *)
| SStop.                                            (* [comment removed for export] *)

Definition fx_step (t : tree xi) (img : tree Z) (s : sst) : sres :=
  let pc := s_pc s in
  let R := s_regs s in
  let fs := s_facts s in
  let g k := rget R k in
  match tlookup t pc with
  | XAluI op rd rs imm =>
      let b := lconst imm in
      match ev_alu fs op (g rs) b with
      | None => match split_req fs op (g rs) b with
                | Some (l, c) => if lclosed (s_next s) l then SSplit l c else SOk (set_res s rd None (res_facts fs op (g rs) b) (pc + 4))
                | None => SOk (set_res s rd None (res_facts fs op (g rs) b) (pc + 4))
                end
      | r => SOk (set_res s rd r (res_facts fs op (g rs) b) (pc + 4))
      end
  | XAlu op rd rs1 rs2 =>
      match ev_alu fs op (g rs1) (g rs2) with
      | None => match split_req fs op (g rs1) (g rs2) with
                | Some (l, c) => if lclosed (s_next s) l then SSplit l c else SOk (set_res s rd None (res_facts fs op (g rs1) (g rs2)) (pc + 4))
                | None => SOk (set_res s rd None (res_facts fs op (g rs1) (g rs2)) (pc + 4))
                end
      | r => SOk (set_res s rd r (res_facts fs op (g rs1) (g rs2)) (pc + 4))
      end
  | XAluIW op rd rs imm => SOk (set_res s rd (ev_aluw fs op (g rs) (lconst imm)) (w_facts fs op (g rs) (lconst imm)) (pc + 4))
  | XAluW op rd rs1 rs2 => SOk (set_res s rd (ev_aluw fs op (g rs1) (g rs2)) (w_facts fs op (g rs1) (g rs2)) (pc + 4))
  | XMul op rd rs1 rs2 => SOk (set_res s rd (ev_mulf fs op (g rs1) (g rs2)) (mul_facts fs op (g rs1) (g rs2)) (pc + 4))
  | XMulW op rd rs1 rs2 => SOk (set_res s rd (ev_mulw fs op (g rs1) (g rs2)) nofacts (pc + 4))
  | XLi rd v => SOk (set_res s rd (Some (lconst v)) nofacts (pc + 4))
  | XJal rd tgt link => SOk (set_res s rd (Some (lconst link)) nofacts tgt)
  | XJalr rd rs imm link =>
      match is_const (g rs) with
      | Some x => SOk (set_res s rd (Some (lconst link)) nofacts (bv_unsigned (bv_and (Z_to_bv 64 x + Z_to_bv 64 imm)%bv (bv_not w1))))
      | None => SStop
      end
  | XBr c rs1 rs2 tgt =>
      match ev_br fs c (g rs1) (g rs2) with
      | Some true => SOk (with_pc s tgt)
      | Some false => SOk (with_pc s (pc + 4))
      | None => SBr c (g rs1) (g rs2) tgt
      end
  | XLd sz sg rd rs imm =>
      match load_at img fs (s_rgs s) (laddc (g rs) imm) sz sg with
      | Some r => SOk (set_res s rd r (fun x => e3_facts img fs (s_rgs s) (laddc (g rs) imm) sz sg x ++ ld_facts fs (s_rgs s) (laddc (g rs) imm) sz sg x) (pc + 4))
      | None => SStop
      end
  | XSt sz rs1 rs2 imm =>
      let a := laddc (g rs1) imm in
      let w := nbytes sz in
      let v := g rs2 in
      match store_at fs (s_rgs s) a w (st_vals fs v w) with
      | Some rgs' => SOk (SST (pc + 4) R rgs' fs (s_next s) (inval (s_resv s) a))
      | None => SStop
      end
  | XFence => SOk (with_pc s (pc + 4))
  | XLr wd rd rs =>
      let a := g rs in
      if amo_al fs wd a then
        match load_at img fs (s_rgs s) a (amo_sz wd) (amo_sg wd) with
        | Some r => SOk (with_resv (set_res s rd r nofacts (pc + 4)) (RAt a))
        | None => SStop
        end
      else SStop
  | XSc wd rd rs1 rs2 =>
      let a := g rs1 in
      if amo_al fs wd a then
        match sc_ok (s_resv s) a with
        | Some true =>
            let w := nbytes (amo_sz wd) in
            let v := g rs2 in
            match store_at fs (s_rgs s) a w (st_bytes v (is_const v) 0 w) with
            | Some rgs' => SOk (SST (pc + 4) (rset R rd lc0) rgs' fs (s_next s) RNone)
            | None => SStop
            end
        | Some false => SOk (SST (pc + 4) (rset R rd (lconst 1)) (s_rgs s) fs (s_next s) RNone)
        | None => SStop
        end
      else SStop
  | XAmo op wd rd rs1 rs2 =>
      let a := g rs1 in
      let src := g rs2 in
      if amo_al fs wd a then
        match load_at img fs (s_rgs s) a (amo_sz wd) (amo_sg wd) with
        | Some r =>
            let ov := match r with Some l => l | None => lvar (s_next s) end in
            let nx := match r with Some _ => s_next s | None => Pos.succ (s_next s) end in
            let nv := amo_new op ov src in
            let w := nbytes (amo_sz wd) in
            match store_at fs (s_rgs s) a w (st_bytes nv (is_const nv) 0 w) with
            | Some rgs' => SOk (SST (pc + 4) (rset R rd ov) rgs' fs nx (inval (s_resv s) a))
            | None => SStop
            end
        | None => SStop
        end
      else SStop
  | XFLd fmt rs imm =>
      match load_at img fs (s_rgs s) (laddc (g rs) imm) (fsz fmt) false with
      | Some _ => SOk (with_pc s (pc + 4))
      | None => SStop
      end
  | XFSt fmt rs1 imm =>
      let a := laddc (g rs1) imm in
      let w := nbytes (fsz fmt) in
      match store_at fs (s_rgs s) a w (st_bytes (lvar (s_next s)) None 0 w) with
      | Some rgs' => SOk (SST (pc + 4) R rgs' fs (Pos.succ (s_next s)) (inval (s_resv s) a))
      | None => SStop
      end
  | XFInt rd cmp => SOk (set_res s rd None (if cmp then bit_facts else nofacts) (pc + 4))
  | XFOp => SOk (with_pc s (pc + 4))
  | XEcall | XOther => SStop
  end.

(* [comment removed for export] *)
Definition with_pc_fact (s : sst) (npc : Z) (f : fact) : sst :=
  SST npc (s_regs s) (s_rgs s) (f :: s_facts s) (s_next s) (s_resv s).

Fixpoint fx_explore (t : tree xi) (img : tree Z) (fuel : nat) (stops : list Z) (s : sst) (acc : list sst) : list sst :=
  match fuel with
  | O => s :: acc
  | S f =>
      match fx_step t img s with
      | SOk s' => if existsb (Z.eqb (s_pc s')) stops then s' :: acc else fx_explore t img f stops s' acc
      | SBr c a b tgt =>
          let s1 := with_pc_fact s tgt (FCond c a b true) in
          let s2 := with_pc_fact s (s_pc s + 4) (FCond c a b false) in
          let acc1 := if existsb (Z.eqb (s_pc s1)) stops then s1 :: acc else fx_explore t img f stops s1 acc in
          if existsb (Z.eqb (s_pc s2)) stops then s2 :: acc1 else fx_explore t img f stops s2 acc1
      | SSplit l c =>
          let s1 := with_pc_fact s (s_pc s) (FCond BC_LTU l (lconst c) true) in
          let s2 := with_pc_fact s (s_pc s) (FCond BC_LTU l (lconst c) false) in
          fx_explore t img f stops s2 (fx_explore t img f stops s1 acc)
      | SStop => s :: acc
      end
  end.

(* [comment removed for export] *)
Fixpoint fx_run (t : tree xi) (img : tree Z) (fuel : nat) (stops : list Z) (s : sst) : sst :=
  match fuel with
  | O => s
  | S f => match fx_step t img s with
           | SOk s' => if existsb (Z.eqb (s_pc s')) stops then s' else fx_run t img f stops s'
           | _ => s
           end
  end.

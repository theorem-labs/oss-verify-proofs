(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64.
Open Scope Z_scope.
Unset Lia Cache.

Module Val.

Inductive fop1 : Type :=
| F1_NANBOX
| F1_LOW32SX
| F1_FCVT (sf df : ffmt) (md : rmode).

Inductive sv : Type :=
| VL   (w : w64)
| VP   (k : int) (off : w64)
| VAlu (op : aluop) (a b : sv)
| VAluw (op : aluop) (a b : sv)
| VMd  (op : mulop) (a b : sv)
| VMdw (op : mulop) (a b : sv)
| VExt (sx : bool) (lo n : int) (a : sv)
| VIns (lo n : int) (a v : sv)
| VBlob (sx : bool) (j : int) (off : sv) (n : int)
| VBg  (sx : bool) (k : int) (off : w64) (n : int)
| VF1  (op : fop1) (a : sv).

Record env : Type := Env {
  ev : int -> word;
  eb : int -> list byte;
  eg : int -> Z -> byte
}.

Definition ext_word (sx : bool) (lo n : Z) (w : word) : word :=
  Z_to_bv 64 (ext_Z sx lo n (bv_unsigned w)).

Definition bytes_val (sx : bool) (n : Z) (bs : list byte) : word :=
  Z_to_bv 64 (ext_Z sx 0 n (bytes_le_to_Z bs)).

Definition blob_bytes (bs : list byte) (off : Z) (n : Z) : list byte :=
  firstn (Z.to_nat n) (skipn (Z.to_nat off) bs).

Fixpoint bg_bytes (g : Z -> byte) (off : Z) (n : nat) : list byte :=
  match n with O => [] | S n' => g off :: bg_bytes g (off + 1) n' end.

Definition fop1_sem (op : fop1) (a : word) : word :=
  match op with
  | F1_NANBOX => nan_box (low32 a)
  | F1_LOW32SX => sext 64 (low32 a)
  | F1_FCVT sf df md =>
      match df with
      | FMT_S => nan_box (Z_to_bv 32 (fst (fp_convert (fp_format sf) (fp_format df) md
                                            (match sf with FMT_S => bv_unsigned (unbox_s a) | FMT_D => bv_unsigned a end))))
      | FMT_D => Z_to_bv 64 (fst (fp_convert (fp_format sf) (fp_format df) md
                                            (match sf with FMT_S => bv_unsigned (unbox_s a) | FMT_D => bv_unsigned a end)))
      end
  end.

Fixpoint den (E : env) (v : sv) : word :=
  match v with
  | VL w => wbv w
  | VP k off => bv_add (ev E k) (wbv off)
  | VAlu op a b => alu64 op (den E a) (den E b)
  | VAluw op a b => sext 64 (alu32 op (low32 (den E a)) (low32 (den E b)))
  | VMd op a b => mul_div op (den E a) (den E b)
  | VMdw op a b => sext 64 (mul_div op (low32 (den E a)) (low32 (den E b)))
  | VExt sx lo n a => ext_word sx (to_Z lo) (to_Z n) (den E a)
  | VIns lo n a v => Z_to_bv 64 (ins_Z (to_Z lo) (to_Z n) (bv_unsigned (den E a)) (bv_unsigned (den E v)))
  | VBlob sx j off n => bytes_val sx (to_Z n) (blob_bytes (eb E j) (bv_unsigned (den E off)) (to_Z n))
  | VBg sx k off n => bytes_val sx (to_Z n) (bg_bytes (eg E k) (w2Zs off) (Z.to_nat (to_Z n)))
  | VF1 op a => fop1_sem op (den E a)
  end.

Definition aluop_eqb (a b : aluop) : bool :=
  match a, b with
  | ALU_ADD, ALU_ADD | ALU_SUB, ALU_SUB | ALU_SLL, ALU_SLL | ALU_SLT, ALU_SLT | ALU_SLTU, ALU_SLTU
  | ALU_XOR, ALU_XOR | ALU_SRL, ALU_SRL | ALU_SRA, ALU_SRA | ALU_OR, ALU_OR | ALU_AND, ALU_AND => true
  | _, _ => false
  end.
Definition mulop_eqb (a b : mulop) : bool :=
  match a, b with
  | M_MUL, M_MUL | M_MULH, M_MULH | M_MULHSU, M_MULHSU | M_MULHU, M_MULHU
  | M_DIV, M_DIV | M_DIVU, M_DIVU | M_REM, M_REM | M_REMU, M_REMU => true
  | _, _ => false
  end.
Definition ffmt_eqb (a b : ffmt) : bool :=
  match a, b with FMT_S, FMT_S | FMT_D, FMT_D => true | _, _ => false end.
Definition rmode_eqb (a b : rmode) : bool :=
  match a, b with
  | RNE, RNE | RTZ, RTZ | RDN, RDN | RUP, RUP | RMM, RMM => true
  | _, _ => false
  end.
Definition fop1_eqb (a b : fop1) : bool :=
  match a, b with
  | F1_NANBOX, F1_NANBOX | F1_LOW32SX, F1_LOW32SX => true
  | F1_FCVT s d m, F1_FCVT s' d' m' => ffmt_eqb s s' && ffmt_eqb d d' && rmode_eqb m m'
  | _, _ => false
  end.

Fixpoint sv_eqb (x y : sv) : bool :=
  match x, y with
  | VL a, VL b => weqb a b
  | VP k a, VP k' b => PrimInt63.eqb k k' && weqb a b
  | VAlu o a b, VAlu o' a' b' => aluop_eqb o o' && sv_eqb a a' && sv_eqb b b'
  | VAluw o a b, VAluw o' a' b' => aluop_eqb o o' && sv_eqb a a' && sv_eqb b b'
  | VMd o a b, VMd o' a' b' => mulop_eqb o o' && sv_eqb a a' && sv_eqb b b'
  | VMdw o a b, VMdw o' a' b' => mulop_eqb o o' && sv_eqb a a' && sv_eqb b b'
  | VExt s l n a, VExt s' l' n' a' => Bool.eqb s s' && PrimInt63.eqb l l' && PrimInt63.eqb n n' && sv_eqb a a'
  | VIns l n a v, VIns l' n' a' v' => PrimInt63.eqb l l' && PrimInt63.eqb n n' && sv_eqb a a' && sv_eqb v v'
  | VBlob s j o n, VBlob s' j' o' n' => Bool.eqb s s' && PrimInt63.eqb j j' && sv_eqb o o' && PrimInt63.eqb n n'
  | VBg s k o n, VBg s' k' o' n' => Bool.eqb s s' && PrimInt63.eqb k k' && weqb o o' && PrimInt63.eqb n n'
  | VF1 o a, VF1 o' a' => fop1_eqb o o' && sv_eqb a a'
  | _, _ => false
  end.

Module BD.
Inductive bsrc := BZ | BU | BY (j : nat).

Definition bsrc_eqb (a b : bsrc) : bool :=
  match a, b with BZ, BZ => true | BU, BU => true | BY i, BY j => Nat.eqb i j | _, _ => false end.
Fixpoint bsrcs_eqb (xs ys : list bsrc) : bool :=
  match xs, ys with
  | nil, nil => true
  | x :: xs, y :: ys => bsrc_eqb x y && bsrcs_eqb xs ys
  | _, _ => false
  end.
Definition bmerge_y (a b : option sv) : option (option sv) :=
  match a, b with
  | None, _ => Some b
  | _, None => Some a
  | Some x, Some y => if sv_eqb x y then Some a else None
  end.
Definition bor (x y : bsrc) : option bsrc :=
  match x, y with BZ, _ => Some y | _, BZ => Some x | _, _ => None end.
Fixpoint bzip (xs ys : list bsrc) : option (list bsrc) :=
  match xs, ys with
  | nil, nil => Some nil
  | x :: xs, y :: ys =>
      match bor x y, bzip xs ys with Some z, Some zs => Some (z :: zs) | _, _ => None end
  | _, _ => None
  end.
Definition brange (lo n : nat) : list bsrc := map BY (seq lo n).

Definition byte_shift (c : w64) : option nat :=
  let s := shamt6 c in
  if PrimInt63.eqb (PrimInt63.land s 7%uint63) 0%uint63
  then Some (Z.to_nat (to_Z (PrimInt63.lsr s 3%uint63))) else None.
Definition bdesc_t : Type := option sv * list bsrc.
Definition bunk : bdesc_t := (None, repeat BU 8).
Definition nat2int (k : nat) : int :=
  match k with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | _ => 0
  end%uint63%nat.

Fixpoint bdesc (v : sv) : option bdesc_t :=
  match v with
  | VL w => if weqb w wzero then Some (None, repeat BZ 8) else None
  | VExt sx lo n y =>
      let lo' := Z.to_nat (to_Z lo) in
      let n' := Z.to_nat (to_Z n) in
      if (1 <=? n')%nat && (lo' + n' <=? 8)%nat then
        let dy := match bdesc y with Some d => d | None => (Some y, brange 0 8) end in
        Some (fst dy, firstn n' (skipn lo' (snd dy)) ++ repeat (if sx then BU else BZ) (8 - n'))
      else None
  | VAlu ALU_SLL a (VL c) =>
      match byte_shift c, bdesc a with
      | Some k, Some (oy, ds) => Some (oy, repeat BZ k ++ firstn (8 - k) ds)
      | _, _ => None
      end
  | VAlu ALU_SRL a (VL c) =>
      match byte_shift c, bdesc a with
      | Some k, Some (oy, ds) => Some (oy, skipn k ds ++ repeat BZ k)
      | _, _ => None
      end
  | VAlu ALU_OR a b =>
      match bdesc a, bdesc b with
      | Some (ya, da), Some (yb, db) =>
          match bmerge_y ya yb, bzip da db with
          | Some oy, Some ds => Some (oy, ds)
          | _, _ => None
          end
      | _, _ => None
      end
  | VIns lo n a v =>
      let lo' := Z.to_nat (to_Z lo) in
      let n' := Z.to_nat (to_Z n) in
      if (1 <=? n')%nat && (lo' + n' <=? 8)%nat then
        let da := match bdesc a with Some d => d | None => bunk end in
        match bdesc v with
        | Some (yv, dv) =>
            match bmerge_y (fst da) yv with
            | Some oy => Some (oy, firstn lo' (snd da) ++ firstn n' dv ++ skipn (lo' + n') (snd da))
            | None => None
            end
        | None => None
        end
      else None
  | _ => None
  end.

Definition bfold (d : bdesc_t) : option sv :=
  match d with
  | (Some y, ds) =>
      if bsrcs_eqb ds (brange 0 8) then Some y
      else match ds with
           | BY lo :: _ =>
               let fit (m : nat) := (lo + m <=? 8)%nat && bsrcs_eqb ds (brange lo m ++ repeat BZ (8 - m)) in
               let mk (m : nat) := VExt false (nat2int lo) (nat2int m) y in
               if fit 4%nat then Some (mk 4%nat)
               else if fit 2%nat then Some (mk 2%nat)
               else if fit 1%nat then Some (mk 1%nat) else None
           | _ => None
           end
  | _ => None
  end.

Definition refold (r : sv) : sv :=
  match bdesc r with
  | Some d => match bfold d with Some y => y | None => r end
  | None => r
  end.
End BD.

Definition wones : w64 := W64 true ones63.
Definition vlit (i : int) : sv := VL (wlit i).
Definition vvar (k : int) : sv := VP k wzero.

Definition add_lit_fold (a : sv) (c : w64) : sv :=
  match a with
  | VAlu ALU_ADD x (VP k o) => VAlu ALU_ADD x (VP k (wadd o c))
  | VAlu ALU_ADD (VP k o) x => VAlu ALU_ADD (VP k (wadd o c)) x
  | VAlu ALU_SUB y (VL c') => if weqb c c' then y else VAlu ALU_ADD a (VL c)
  | _ => VAlu ALU_ADD a (VL c)
  end.

Definition sv_alu0 (op : aluop) (a b : sv) : sv :=
  match a, b with
  | VL x, VL y => VL (walu op x y)
  | _, _ =>
    match op with
    | ALU_ADD =>
        match a, b with
        | VP k o, VL c => VP k (wadd o c)
        | VL c, VP k o => VP k (wadd o c)
        | _, VL c => if weqb c wzero then a else add_lit_fold a c
        | VL c, _ => if weqb c wzero then b else add_lit_fold b c
        | VAlu ALU_SUB x y, _ => if sv_eqb y b then x else VAlu op a b
        | _, VAlu ALU_SUB x y => if sv_eqb y a then x else VAlu op a b
        | VAlu ALU_ADD (VP k o) y, _ => VAlu op (VP k o) (VAlu ALU_ADD y b)
        | VP _ _, VAlu ALU_ADD (VP _ _) _ => VAlu op a b
        | _, VAlu ALU_ADD (VP k o) y => VAlu op (VP k o) (VAlu ALU_ADD y a)
        | _, _ => VAlu op a b
        end
    | ALU_SUB =>
        match a, b with
        | VP k o, VL c => VP k (wsub o c)
        | VP k o1, VP k' o2 => if PrimInt63.eqb k k' then VL (wsub o1 o2) else VAlu op a b
        | _, VL c => if weqb c wzero then a else VAlu op a b
        | _, _ => if sv_eqb a b then VL wzero else VAlu op a b
        end
    | ALU_OR =>
        match a, b with
        | _, VL c => if weqb c wzero then a else VAlu op a b
        | VL c, _ => if weqb c wzero then b else VAlu op a b
        | _, _ => VAlu op a b
        end
    | ALU_XOR =>
        match a, b with
        | _, VL c => if weqb c wzero then a else VAlu op a b
        | VL c, _ => if weqb c wzero then b else VAlu op a b
        | _, _ => if sv_eqb a b then VL wzero else VAlu op a b
        end
    | ALU_SLL | ALU_SRL | ALU_SRA =>
        match b with
        | VL c => if PrimInt63.eqb (shamt6 c) 0%uint63 then a else VAlu op a b
        | _ => VAlu op a b
        end
    | ALU_AND =>
        match a, b with
        | _, VL c => if weqb c wones then a else if weqb c wzero then VL wzero else VAlu op a b
        | VL c, _ => if weqb c wones then b else if weqb c wzero then VL wzero else VAlu op a b
        | _, _ => VAlu op a b
        end
    | _ => VAlu op a b
    end
  end.

Definition sv_aluw (op : aluop) (a b : sv) : sv :=
  match a, b with
  | VL x, VL y => VL (walu32 op x y)
  | _, _ => VAluw op a b
  end.

Definition sv_md (op : mulop) (a b : sv) : sv :=
  match a, b with
  | VL x, VL y => VL (wmd op x y)
  | _, _ => VMd op a b
  end.

Definition sv_mdw (op : mulop) (a b : sv) : sv :=
  match a, b with
  | VL x, VL y => VL (wmd32 op x y)
  | _, _ => VMdw op a b
  end.

Fixpoint sv_ext (sx : bool) (lo n : int) (a : sv) {struct a} : sv :=
  match a with
  | VL x => VL (wext sx lo n x)
  | VExt sx' lo2 n2 y =>

      if PrimInt63.leb lo2 8%uint63 && PrimInt63.leb (PrimInt63.add lo n) n2
         && PrimInt63.leb (PrimInt63.add lo2 (PrimInt63.add lo n)) 8%uint63
      then sv_ext sx (PrimInt63.add lo2 lo) n y
      else if PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb n 8%uint63 then a else VExt sx lo n a
  | VBlob sx' j (VL x) n' =>

      if PrimInt63.leb (PrimInt63.add lo n) n' && negb (wt x)
      then VBlob sx j (VL (wadd x (wlit lo))) n
      else VExt sx lo n a
  | VBg sx' k off n' =>

      if PrimInt63.leb (PrimInt63.add lo n) n' && (wt off || negb (wt (wadd off (wlit lo))))
      then VBg sx k (wadd off (wlit lo)) n
      else VExt sx lo n a
  | VIns lo2 n2 a1 a2 =>

      if PrimInt63.leb lo2 8%uint63 && PrimInt63.ltb 0%uint63 n2 && PrimInt63.leb n2 8%uint63
         && PrimInt63.leb (PrimInt63.add lo2 n2) 8%uint63 then
        if PrimInt63.leb lo2 lo && PrimInt63.leb (PrimInt63.add lo n) (PrimInt63.add lo2 n2)
        then sv_ext sx (PrimInt63.sub lo lo2) n a2
        else if PrimInt63.leb (PrimInt63.add lo n) lo2 || PrimInt63.leb (PrimInt63.add lo2 n2) lo
        then sv_ext sx lo n a1
        else (if PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb n 8%uint63 then a else VExt sx lo n a)
      else (if PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb n 8%uint63 then a else VExt sx lo n a)
  | _ =>
      if PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb n 8%uint63 then a else VExt sx lo n a
  end.

Definition sv_ins (lo n : int) (a v : sv) : sv :=
  if PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb n 8%uint63 then v else
  match a, v with
  | VL x, VL y => VL (wins lo n x y)
  | _, _ => BD.refold (VIns lo n a v)
  end.

Definition sv_f1 (op : fop1) (a : sv) : sv := VF1 op a.

Definition umax_of_width (n : int) : option w64 :=
  if PrimInt63.ltb n 8%uint63 && PrimInt63.ltb 0%uint63 n
  then Some (W64 false (PrimInt63.sub (PrimInt63.lsl 1%uint63 (PrimInt63.lsl n 3%uint63)) 1%uint63))
  else None.

Definition wminu (a b : w64) : w64 := if wltu a b then a else b.

Definition wmaxu (a b : w64) : w64 := if wltu a b then b else a.

Fixpoint sv_umax (v : sv) : option w64 :=
  match v with
  | VL x => Some x
  | VExt false _ n _ => umax_of_width n
  | VBlob false _ _ n => umax_of_width n
  | VBg false _ _ n => umax_of_width n
  | VAlu ALU_AND x (VL m) => Some (match sv_umax x with Some u => wminu u m | None => m end)
  | VAlu ALU_AND (VL m) x => Some (match sv_umax x with Some u => wminu u m | None => m end)
  | VAlu ALU_SRL x (VL s) => Some (wsrl (match sv_umax x with Some u => u | None => wones end) s)
  | VAlu ALU_OR x y | VAlu ALU_ADD x y =>

      match sv_umax x, sv_umax y with
      | Some u, Some v => if wt u || wt v then None else Some (wadd u v)
      | _, _ => None
      end
  | _ => None
  end.

Definition zext_twin (a : sv) : option (int * sv) :=
  match a with
  | VExt true lo n y => Some (n, VExt false lo n y)
  | VBlob true j o n => Some (n, VBlob false j o n)
  | VBg true k o n => Some (n, VBg false k o n)
  | _ => None
  end.

Definition is_low_mask (c : w64) : bool := Z.eqb (w2Z c + 1) (2 ^ Z.log2 (w2Z c + 1)) && negb (weqb c wzero).

Definition and_refold (r : sv) : sv :=
  match r with
  | VAlu ALU_AND x (VL c) =>
      match zext_twin x with
      | Some (n, x') =>
          match umax_of_width n with
          | Some m => if weqb m c then x' else if wleu c m then VAlu ALU_AND x' (VL c) else r
          | None => r
          end
      | None =>
          if is_low_mask c then match sv_umax x with Some u => if wleu u c then x else r | None => r end else r
      end
  | _ => r
  end.

Definition subsub_fold (r : sv) : sv :=
  match r with
  | VAlu ALU_SUB a (VAlu ALU_SUB x y) => if sv_eqb x a then y else r
  | _ => r
  end.

Definition zext_bytes (s : int) : option int :=
  if PrimInt63.eqb s 8%uint63 then Some 7%uint63 else if PrimInt63.eqb s 16%uint63 then Some 6%uint63
  else if PrimInt63.eqb s 24%uint63 then Some 5%uint63 else if PrimInt63.eqb s 32%uint63 then Some 4%uint63
  else if PrimInt63.eqb s 40%uint63 then Some 3%uint63 else if PrimInt63.eqb s 48%uint63 then Some 2%uint63
  else if PrimInt63.eqb s 56%uint63 then Some 1%uint63 else None.
Definition zext_canon (x : sv) (k : w64) (r : sv) : sv :=
  match zext_bytes (shamt6 k) with Some n => sv_ext false 0%uint63 n x | None => r end.

Definition srlsll_fold (r : sv) : sv :=
  match r with
  | VAlu ALU_SRL (VAlu ALU_SLL x (VL k)) (VL k') =>
      if PrimInt63.eqb (shamt6 k) (shamt6 k') then
        match sv_umax x with
        | Some u => if weqb (wsrl (wsll u k) k) u then x else zext_canon x k r
        | None => zext_canon x k r
        end
      else r
  | _ => r
  end.

Definition sllw_fold (r : sv) : sv :=
  match r with
  | VAlu ALU_SLL (VAluw ALU_ADD x (VL z)) (VL c) =>
      if weqb z wzero && PrimInt63.leb 32%uint63 (shamt6 c) then VAlu ALU_SLL x (VL c) else r
  | VAlu ALU_SLL (VAluw ALU_ADD (VL z) x) (VL c) =>
      if weqb z wzero && PrimInt63.leb 32%uint63 (shamt6 c) then VAlu ALU_SLL x (VL c) else r
  | _ => r
  end.

Definition xor_not_fold (r : sv) : sv :=
  match r with
  | VAlu ALU_XOR x (VL c) => if weqb c wones then VAlu ALU_SUB (VL wones) x else r
  | VAlu ALU_XOR (VL c) x => if weqb c wones then VAlu ALU_SUB (VL wones) x else r
  | _ => r
  end.

Definition sv_alu (op : aluop) (a b : sv) : sv :=
  let r := sv_alu0 op a b in
  match op with ALU_OR => BD.refold r | ALU_AND => and_refold r | ALU_SUB => subsub_fold r | ALU_SRL => srlsll_fold r
             | ALU_SLL => sllw_fold r | ALU_XOR => xor_not_fold r | _ => r end.
Arguments sv_alu _ _ _ : simpl never.

Definition as_lit (a : sv) : option w64 := match a with VL x => Some x | _ => None end.
Definition as_ptr (a : sv) : option (int * w64) := match a with VP k o => Some (k, o) | _ => None end.

End Val.

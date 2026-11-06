(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExLin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Inductive aval : Type :=
| VL (w : w64)
| VS (f : lin)
| VR (lo hi : Z)
| VT
| VK (m v : Z).

Definition aval_val (ρ : valuation) (v : aval) (w : bv 64) : Prop :=
  match v with
  | VL x => bv_unsigned w = wZ x
  | VS f => bv_unsigned w = leval ρ f
  | VR lo hi => lo <= bv_unsigned w <= hi
  | VT => True
  | VK m v => Z.land (bv_unsigned w) m = v
  end.

Definition vzero : aval := VL w_zero.

Lemma bvu_range (w : bv 64) : 0 <= bv_unsigned w < two64.
Proof. pose proof (bv_unsigned_in_range 64 w) as H. rewrite bv_modulus_64 in H. exact H. Qed.

Definition vrange (s : store) (v : aval) : option ivl :=
  match v with
  | VL x => let z := wZ x in Some (z, z)
  | VS f => lrange s f
  | VR lo hi => Some (lo, hi)
  | VT => None
  | VK _ _ => None
  end.

Definition vform (v : aval) : option lin :=
  match v with
  | VL x => Some (lconst (wZ x))
  | VS f => Some f
  | _ => None
  end.

Definition mk_vs0 (s : store) (f : lin) : aval :=
  match snd f with
  | [] => VL (wofZ (fst f))
  | _ =>
    match lrange s f with
    | Some (lo, hi) =>
        let j := lo / two64 in
        if j =? hi / two64 then
          (if lo =? hi then VL (wofZ lo) else VS (laddc f (- (j * two64))))
        else VT
    | None => VT
    end
  end.

Definition mk_vs (s : store) (f : lin) : aval := mk_vs0 s (lnorm s f).

Definition mk_rng (lo hi : Z) : aval :=
  if (0 <=? lo) && (lo <=? hi) && (hi <? two64) then (if lo =? hi then VL (wofZ lo) else VR lo hi) else VT.

Definition a_add (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_add a b)
  | VS f, VL b => mk_vs s (laddc f (wS b))
  | VL b, VS f => mk_vs s (laddc f (wS b))
  | VS f, VS g => mk_vs s (ladd f g)
  | VR lo hi, VL b => let k := wS b in mk_rng (lo + k) (hi + k)
  | VL b, VR lo hi => let k := wS b in mk_rng (lo + k) (hi + k)
  | _, _ => VT
  end.

Definition a_sub (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_sub a b)
  | VS f, VL b => mk_vs s (laddc f (- wS b))
  | VL a, VS g => mk_vs s (lsub (lconst (wZ a)) g)
  | VS f, VS g => mk_vs s (lsub f g)
  | VR lo hi, VL b => let k := wS b in mk_rng (lo - k) (hi - k)
  | _, _ => VT
  end.

Definition low_mask_bits (m : Z) : option Z :=
  let k := Z.log2 (m + 1) in if (0 <=? m) && (2 ^ k =? m + 1) then Some k else None.

Fixpoint tsplit (k2 : Z) (ts : terms) : terms * terms :=
  match ts with
  | [] => ([], [])
  | (x, a) :: r =>
      let p := tsplit k2 r in
      if a mod k2 =? 0 then ((x, a / k2) :: fst p, snd p) else (fst p, (x, a) :: snd p)
  end.

Definition lshr0 (s : store) (f : lin) (k : Z) : option lin :=
  let k2 := 2 ^ k in
  let p := tsplit k2 (snd f) in
  match lrange s (fst f, snd p) with
  | Some (lo, hi) => if lo / k2 =? hi / k2 then Some (lo / k2, fst p) else None
  | None => None
  end.

Definition lshr (s : store) (f : lin) (k : Z) : option lin :=
  match lrange s f with
  | Some (lo, hi) => if lo / 2 ^ k =? hi / 2 ^ k then Some (lconst (lo / 2 ^ k)) else lshr0 s f k
  | None => lshr0 s f k
  end.

Definition bitrun (m : Z) : option (Z * Z) :=
  if 0 <? m then
    let j := Z.log2 (Z.land m (- m)) in
    if m mod 2 ^ j =? 0 then match low_mask_bits (m / 2 ^ j) with Some i => Some (j, i) | None => None end else None
  else None.

Definition a_and_run (s : store) (f : lin) (m : Z) : option aval :=
  match bitrun m with
  | Some (j, i) =>
      match lshr s f j with
      | Some g1 => match lshr s g1 i with
                   | Some g2 => Some (mk_vs s (lscale (2 ^ j) (lsub g1 (lscale (2 ^ i) g2))))
                   | None => None
                   end
      | None => None
      end
  | None => None
  end.

Definition a_and_mask0 (s : store) (v : aval) (m : w64) : aval :=
  match low_mask_bits (wZ m) with
  | Some k =>
      match v with
      | VS f =>
          match lrange s f with
          | Some (lo, hi) => if (0 <=? lo) && (hi <=? wZ m) then VS f else mk_rng 0 (wZ m)
          | None => mk_rng 0 (wZ m)
          end
      | VR lo hi => if (0 <=? lo) && (hi <=? wZ m) then v else mk_rng 0 (wZ m)
      | _ => mk_rng 0 (wZ m)
      end
  | None => VT
  end.

Definition a_and_mask (s : store) (v : aval) (m : w64) : aval :=
  match v with
  | VS f => match a_and_run s f (wZ m) with Some r => r | None => a_and_mask0 s v m end
  | _ => a_and_mask0 s v m
  end.

Definition a_and (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_and a b)
  | v, VL m => a_and_mask s v m
  | VL m, v => a_and_mask s v m
  | _, _ => VT
  end.

Definition a_or0 (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_or a b)
  | v, VL b => if w_eqb b w_zero then v else VT
  | VL b, v => if w_eqb b w_zero then v else VT
  | _, _ => VT
  end.

Definition a_xor (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_xor a b)
  | _, _ => VT
  end.

Definition a_sll (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_sll a (w_shamt6 b))
  | VS f, VL b => mk_vs s (lscale (2 ^ to_Z (w_shamt6 b)) f)
  | _, _ => VT
  end.

Definition a_srl (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_srl a (w_shamt6 b))
  | VS f, VL b =>
      let k := to_Z (w_shamt6 b) in
      match lshr s f k with
      | Some g => mk_vs s g
      | None => match lrange s f with Some (lo, hi) => mk_rng (Z.max 0 lo / 2 ^ k) (Z.min (two64 - 1) hi / 2 ^ k) | None => VT end
      end
  | VR lo hi, VL b => let k := to_Z (w_shamt6 b) in mk_rng (lo / 2 ^ k) (hi / 2 ^ k)
  | _, _ => VT
  end.

Definition a_sra (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_sra a (w_shamt6 b))
  | _, _ => VT
  end.

Definition a_mul (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_mul a b)
  | VS f, VL b => mk_vs s (lscale (wZ b) f)
  | VL b, VS f => mk_vs s (lscale (wZ b) f)
  | _, _ => VT
  end.

Lemma ones64 : two64 - 1 = Z.ones 64.
Proof. reflexivity. Qed.

Fixpoint ptz (lo hi t : Z) (fuel : nat) : Z :=
  match fuel with O => 64 | S f => if lo / 2 ^ t =? hi / 2 ^ t then t else ptz lo hi (t + 1) f end.

Definition tok (s : store) (x : aval) : option (Z * Z) :=
  match x with
  | VL a => Some (two64 - 1, wZ a)
  | VK m v => Some (m, v)
  | VT => None
  | _ =>
      match vrange s x with
      | Some (lo, hi) =>
          let t := ptz lo hi 0 65 in
          if (0 <=? lo) && (lo <=? hi) && (hi <? two64) && (0 <=? t) && (t <=? 64) && (lo / 2 ^ t =? hi / 2 ^ t)
          then Some (two64 - 2 ^ t, lo / 2 ^ t * 2 ^ t) else None
      | None => None
      end
  end.

Definition mkvk (m v : Z) : aval := if m =? two64 - 1 then VL (wofZ v) else VK m v.

Definition a_or_kb (s : store) (x y : aval) : aval :=
  match tok s x, tok s y with
  | Some (m1, v1), Some (m2, v2) => mkvk (Z.lor (Z.land m1 m2) (Z.lor v1 v2)) (Z.lor v1 v2)
  | _, _ => VT
  end.

Definition a_or_disj (s : store) (x y : aval) : option aval :=
  match vform x, vform y with
  | Some f, Some g =>
      match lrange s g, lrange s f with
      | Some (lo2, hi2), Some (lo1, hi1) =>
          if (0 <=? lo2) && (0 <? hi2) && (0 <=? lo1) && (hi1 + hi2 <? two64) then
            let k2 := 2 ^ (Z.log2 hi2 + 1) in
            match tsplit k2 (snd f) with
            | (_, []) => if fst f mod k2 =? 0 then Some (mk_vs s (ladd f g)) else None
            | _ => None
            end
          else None
      | _, _ => None
      end
  | _, _ => None
  end.

Definition a_or_low (s : store) (x y : aval) : option aval :=
  match x, y with
  | VS f, VL c =>
      let cz := wZ c in
      if 0 <? cz then
        let K := Z.log2 cz + 1 in
        match lshr s f K with
        | Some g =>
            match lrange s (lsub f (lscale (2 ^ K) g)) with
            | Some (r0, r1) => if (r0 =? r1) && (0 <=? r0) then Some (mk_vs s (laddc (lscale (2 ^ K) g) (Z.lor r0 cz))) else None
            | None => None
            end
        | None => None
        end
      else None
  | _, _ => None
  end.

Definition a_or (s : store) (x y : aval) : aval :=
  match a_or0 s x y with
  | VT => match a_or_disj s x y with
          | Some v => v
          | None => match a_or_disj s y x with
                    | Some v => v
                    | None => match a_or_low s x y with
                              | Some v => v
                              | None => match a_or_low s y x with Some v => v | None => a_or_kb s x y end
                              end
                    end
          end
  | v => v
  end.

Definition a_srl' (s : store) (x y : aval) : aval :=
  match a_srl s x y, x, y with
  | VT, VK m v, VL b => let k := to_Z (w_shamt6 b) in mkvk (Z.lor (Z.shiftr m k) (two64 - 2 ^ (64 - k))) (Z.shiftr v k)
  | r, _, _ => r
  end.

Definition a_sll' (s : store) (x y : aval) : aval :=
  match a_sll s x y, x, y with
  | VT, VK m v, VL b => let k := to_Z (w_shamt6 b) in mkvk (Z.lor ((Z.shiftl m k) mod two64) (Z.ones k)) ((Z.shiftl v k) mod two64)
  | r, _, _ => r
  end.

Definition a_ltu (s : store) (x y : aval) : option bool :=
  match x, y with
  | VL a, VL b => Some (w_ltu a b)
  | _, _ =>
      match vform x, vform y with
      | Some f, Some g =>
          match lrange s (lsub f g) with
          | Some (lo, hi) => if hi <? 0 then Some true else if 0 <=? lo then Some false else None
          | None => None
          end
      | _, _ =>
          match vrange s x, vrange s y with
          | Some (xl, xh), Some (yl, yh) => if xh <? yl then Some true else if yh <=? xl then Some false else None
          | _, _ => None
          end
      end
  end.

Definition a_eq (s : store) (x y : aval) : option bool :=
  match x, y with
  | VL a, VL b => Some (w_eqb a b)
  | _, _ =>
      match vform x, vform y with
      | Some f, Some g =>
          match lrange s (lsub f g) with
          | Some (lo, hi) => if (hi <? 0) || (0 <? lo) then Some false else if (lo =? 0) && (hi =? 0) then Some true else None
          | None => None
          end
      | _, _ =>
          match vrange s x, vrange s y with
          | Some (xl, xh), Some (yl, yh) => if (xh <? yl) || (yh <? xl) then Some false else None
          | _, _ => None
          end
      end
  end.

Definition a_lts (s : store) (x y : aval) : option bool :=
  match x, y with
  | VL a, VL b => Some (w_lts a b)
  | _, _ =>
      match vrange s x, vrange s y with
      | Some (xl, xh), Some (yl, yh) =>
          if (0 <=? xl) && (xh <? two63) && (0 <=? yl) && (yh <? two63) then a_ltu s x y else None
      | _, _ => None
      end
  end.

Definition a_bool (b : option bool) : aval :=
  match b with Some true => VL w_one | Some false => VL w_zero | None => VR 0 1 end.

Definition a_alu64 (s : store) (op : aluop) (x y : aval) : aval :=
  match op with
  | ALU_ADD => a_add s x y
  | ALU_SUB => a_sub s x y
  | ALU_SLL => a_sll' s x y
  | ALU_SLT => a_bool (a_lts s x y)
  | ALU_SLTU => a_bool (a_ltu s x y)
  | ALU_XOR => a_xor s x y
  | ALU_SRL => a_srl' s x y
  | ALU_SRA => a_sra s x y
  | ALU_OR => a_or s x y
  | ALU_AND => a_and s x y
  end.

Definition a_muldiv (s : store) (op : mulop) (x y : aval) : aval :=
  match op, x, y with
  | M_MUL, _, _ => a_mul s x y
  | _, VL a, VL b => VL (w_muldiv op a b)
  | _, _, _ => VT
  end.

Definition aval_val32 (ρ : valuation) (v : aval) (X : bv 32) : Prop :=
  exists a : bv 64, aval_val ρ v a /\ bv_unsigned X = bv_unsigned a mod two32.

Definition a_alu32 (s : store) (op : aluop) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_sext32 (w_alu32 op (w_low32 a) (w_low32 b)))
  | _, _ => VT
  end.

Definition a_muldiv32 (s : store) (op : mulop) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_sext32 (w_muldiv32 op (w_low32 a) (w_low32 b)))
  | _, _ => VT
  end.

Definition a_branch (s : store) (bc : branch_cond) (x y : aval) : option bool :=
  match bc with
  | BC_EQ => a_eq s x y
  | BC_NE => option_map negb (a_eq s x y)
  | BC_LT => a_lts s x y
  | BC_GE => option_map negb (a_lts s x y)
  | BC_LTU => a_ltu s x y
  | BC_GEU => option_map negb (a_ltu s x y)
  end.

Definition fk (s : store) (d : lin) (lo hi : Z) (b : bool) : list (store * bool) :=
  match lrange s d with
  | Some (l, h) => let l' := Z.max l lo in let h' := Z.min h hi in
                   if l' <=? h' then [(sadd s d l' h', b)] else []
  | None => [(sadd s d lo hi, b)]
  end.

Definition a_fork (s : store) (bc : branch_cond) (x y : aval) : option (list (store * bool)) :=
  match vform x, vform y with
  | Some f, Some g =>
      let d := lsub f g in
      let lt := fk s d (- two64) (-1) true ++ fk s d 0 two64 false in
      let eq := fk s d 0 0 true ++ fk s d (- two64) (-1) false ++ fk s d 1 two64 false in
      let small := match vrange s x, vrange s y with
                   | Some (xl, xh), Some (yl, yh) => (0 <=? xl) && (xh <? two63) && (0 <=? yl) && (yh <? two63)
                   | _, _ => false
                   end in
      match bc with
      | BC_LTU => Some lt
      | BC_GEU => Some (map (fun p => (fst p, negb (snd p))) lt)
      | BC_LT => if small then Some lt else None
      | BC_GE => if small then Some (map (fun p => (fst p, negb (snd p))) lt) else None
      | BC_EQ => Some eq
      | BC_NE => Some (map (fun p => (fst p, negb (snd p))) eq)
      end
  | _, _ => None
  end.

Definition two31 : Z := 2147483648.

Definition a_alu32' (s : store) (op : aluop) (x y : aval) : aval :=
  match a_alu32 s op x y with
  | VT =>
      match op with
      | ALU_ADD | ALU_SUB =>
          match vform x, vform y with
          | Some f, Some g =>
              let d := match op with ALU_ADD => ladd f g | _ => lsub f g end in
              match lrange s d with
              | Some (lo, hi) => if (0 <=? lo) && (hi <? two31) then mk_vs s d
                                 else if (- two31 <=? lo) && (hi <? 0) then mk_vs s (laddc d two64) else VT
              | None => VT
              end
          | _, _ => VT
          end
      | ALU_SRL =>
          match y with
          | VL b => let k := to_Z (w_low32 b) mod 32 in
                    if 1 <=? k then
                      match tok s x with
                      | Some (m, v) => mkvk (Z.lor (Z.shiftr (m mod two32) k) (two64 - 2 ^ (32 - k))) (Z.shiftr (v mod two32) k)
                      | None => VT
                      end
                    else VT
          | _ => VT
          end
      | _ => VT
      end
  | r => r
  end.


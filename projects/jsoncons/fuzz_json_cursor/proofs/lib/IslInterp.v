(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool FMapPositive.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec SymStepR.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ISL.

Inductive aval : Type := AL (z : Z) | AS (k : nat) (off : Z).
Inductive abyte : Type := BL (b : Z) | BS (k : nat) (off : Z) (i : nat).
Inductive aaddr : Type := AAbs (a : Z) | ARg (j : nat) (off : Z).
Record region : Type := RG { rg_k : nat; rg_lo : Z; rg_hi : Z }.
Record cfg : Type := CFG {
  c_rgs : list region;
  c_abs_hi : Z;
  c_wabs : list (Z * Z);
  c_clear : list (Z * Z);
  c_kn0 : list (Z * abyte);
  c_zero : list (Z * Z)
}.
Record ast : Type := ST {
  s_pc : Z; s_regs : list aval; s_abs : PositiveMap.t abyte; s_rgs : list (PositiveMap.t abyte); s_resv : option aaddr }.
Inductive result : Type := RFin (s : ast) (v : aval) (imm : Z) | ROut (s : ast) | RStuck (code : Z) (pc : Z).

Definition zkey (z : Z) : positive := match z with Z0 => 1%positive | Zpos p => p~0%positive | Zneg p => p~1%positive end.

Definition aval_eqb (a b : aval) : bool :=
  match a, b with AL x, AL y => Z.eqb x y | AS k o, AS k' o' => Nat.eqb k k' && Z.eqb o o' | _, _ => false end.
Definition aaddr_eqb (a b : aaddr) : bool :=
  match a, b with AAbs x, AAbs y => Z.eqb x y | ARg j o, ARg j' o' => Nat.eqb j j' && Z.eqb o o' | _, _ => false end.
Fixpoint in_ivs (l : list (Z * Z)) (a : Z) : bool :=
  match l with [] => false | (lo, hi) :: t => ((lo <=? a) && (a <? hi)) || in_ivs t a end.

Fixpoint kn_find (l : list (Z * abyte)) (a : Z) : option abyte :=
  match l with [] => None | (x, b) :: t => if Z.eqb x a then Some b else kn_find t a end.

Definition ashift (ad : aaddr) (d : Z) : aaddr := match ad with AAbs a => AAbs (a + d) | ARg j off => ARg j (off + d) end.
Definition aaddi (v : aval) (imm : Z) : aval := match v with AL z => AL (bv_wrap 64 (z + imm)) | AS k off => AS k (off + imm) end.

Fixpoint find_rg (rgs : list region) (k : nat) (off : Z) (j : nat) : option nat :=
  match rgs with
  | [] => None
  | rg :: t => if Nat.eqb (rg_k rg) k && (rg_lo rg <=? off) && (off <? rg_hi rg) then Some j else find_rg t k off (S j)
  end.
Definition classify (C : cfg) (v : aval) : option aaddr :=
  match v with
  | AL z => Some (AAbs z)
  | AS k off => match find_rg (c_rgs C) k off 0 with Some j => Some (ARg j off) | None => None end
  end.

Fixpoint upd {A} (n : nat) (v : A) (l : list A) : list A :=
  match l, n with [] , _ => [] | _ :: t, O => v :: t | x :: t, S n' => x :: upd n' v t end.

Definition rnat (r : reg) : nat := Z.to_nat (bv_unsigned r).
Definition getreg (s : ast) (r : reg) : aval := nth (rnat r) (s_regs s) (AL 0).
Definition setreg (s : ast) (r : reg) (v : aval) : ast :=
  if bv_eqb r 0 then s else ST (s_pc s) (upd (rnat r) v (s_regs s)) (s_abs s) (s_rgs s) (s_resv s).
Definition setpc (s : ast) (pc : Z) : ast := ST pc (s_regs s) (s_abs s) (s_rgs s) (s_resv s).
Definition setresv (s : ast) (r : option aaddr) : ast := ST (s_pc s) (s_regs s) (s_abs s) (s_rgs s) r.

Section WithSegs.
Variable segs : list Segment.
Variable C : cfg.

Definition fetch_entry (pc : Z) : option instr :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | None => None
  | Some w => if is_ecall w then None else
              match decode_any w with Some (i, sz) => if Z.eqb sz 4 then Some i else None | None => None end
  end.

Definition rdb (s : ast) (ad : aaddr) : option abyte :=
  match ad with
  | AAbs a =>
      if (0 <? a) && (a <? c_abs_hi C) then
        match PositiveMap.find (zkey a) (s_abs s) with
        | Some b => Some b
        | None =>
            match kn_find (c_kn0 C) a with
            | Some b => Some b
            | None => if in_ivs (c_clear C) a then
                        match seg_rom segs (Z_to_bv 64 a) with Some b => Some (BL (bv_unsigned b)) | None => None end
                      else if in_ivs (c_zero C) a then Some (BL 0) else None
            end
        end
      else None
  | ARg j off =>
      match nth_error (c_rgs C) j, nth_error (s_rgs s) j with
      | Some rg, Some t => if (rg_lo rg <=? off) && (off <? rg_hi rg) then PositiveMap.find (zkey off) t else None
      | _, _ => None
      end
  end.
Fixpoint rdbs (s : ast) (ad : aaddr) (n : nat) : option (list abyte) :=
  match n with
  | O => Some []
  | S n' => match rdb s ad with
            | Some b => match rdbs s (ashift ad 1) n' with Some r => Some (b :: r) | None => None end
            | None => None
            end
  end.

Definition abs_wr (a : Z) : bool :=
  match wview segs (fun _ => None) (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition wr_chk (ad : aaddr) : bool :=
  match ad with
  | AAbs a => (0 <? a) && (a <? c_abs_hi C) && in_ivs (c_wabs C) a && abs_wr a
  | ARg j off => match nth_error (c_rgs C) j with Some rg => (rg_lo rg <=? off) && (off <? rg_hi rg) | None => false end
  end.
Definition wrb (s : ast) (ad : aaddr) (b : abyte) : ast :=
  match ad with
  | AAbs a => ST (s_pc s) (s_regs s) (PositiveMap.add (zkey a) b (s_abs s)) (s_rgs s) (s_resv s)
  | ARg j off => ST (s_pc s) (s_regs s) (s_abs s)
                    (match nth_error (s_rgs s) j with Some t => upd j (PositiveMap.add (zkey off) b t) (s_rgs s) | None => s_rgs s end) (s_resv s)
  end.
Fixpoint wrbs (s : ast) (ad : aaddr) (bs : list abyte) : option ast :=
  match bs with
  | [] => Some s
  | b :: t => if wr_chk ad && (match ad with ARg j _ => match nth_error (s_rgs s) j with Some _ => true | None => false end | _ => true end)
              then wrbs (wrb s ad b) (ashift ad 1) t else None
  end.

Definition avalid (ad : aaddr) : bool :=
  match ad with
  | AAbs a => (0 <? a) && (a <? c_abs_hi C)
  | ARg j off => match nth_error (c_rgs C) j with Some rg => (rg_lo rg <=? off) && (off <? rg_hi rg) | None => false end
  end.
Definition aalign (ad : aaddr) (n : Z) : bool :=
  avalid ad && match ad with AAbs a => Z.eqb (a mod n) 0 | ARg _ off => Z.eqb (off mod n) 0 end.
Definition resv_upd (o : option aaddr) (ad : aaddr) : option (option aaddr) :=
  match o with
  | None => Some None
  | Some r => if aaddr_eqb r ad then Some None else if avalid r && avalid ad then Some (Some r) else None
  end.

Fixpoint lits (l : list abyte) : option (list Z) :=
  match l with
  | [] => Some []
  | BL b :: t => match lits t with Some r => Some (b :: r) | None => None end
  | _ => None
  end.
Definition is_sym8 (l : list abyte) : option aval :=
  match l with
  | [BS k o 0; BS k1 o1 1; BS k2 o2 2; BS k3 o3 3; BS k4 o4 4; BS k5 o5 5; BS k6 o6 6; BS k7 o7 7] =>
      if aval_eqb (AS k o) (AS k1 o1) && aval_eqb (AS k o) (AS k2 o2) && aval_eqb (AS k o) (AS k3 o3) && aval_eqb (AS k o) (AS k4 o4)
         && aval_eqb (AS k o) (AS k5 o5) && aval_eqb (AS k o) (AS k6 o6) && aval_eqb (AS k o) (AS k7 o7) then Some (AS k o) else None
  | _ => None
  end.
Definition zbytes (zs : list Z) : list byte := map (Z_to_bv 8) zs.
Definition blits (bs : list byte) : list abyte := map (fun b : byte => BL (bv_unsigned b)) bs.
Definition wlit (w : word) : aval := AL (bv_unsigned w).

Definition load_val (sz : msize) (sx : bool) (l : list abyte) : option aval :=
  match lits l with
  | Some zs => Some (wlit (load_result sz sx (zbytes zs)))
  | None => match sz with SZ8 => is_sym8 l | _ => None end
  end.
Definition store_bytes (n : nat) (v : aval) : option (list abyte) :=
  match v with
  | AL z => Some (blits (word_to_le_bytes n (Z_to_bv 64 z)))
  | AS k o => if Nat.eqb n 8 then Some [BS k o 0; BS k o 1; BS k o 2; BS k o 3; BS k o 4; BS k o 5; BS k o 6; BS k o 7] else None
  end.

Definition abranch (c : branch_cond) (a b : aval) : option bool :=
  match a, b with
  | AL x, AL y => Some (branch_taken c (Z_to_bv 64 x) (Z_to_bv 64 y))
  | _, _ => if aval_eqb a b then match c with BC_EQ => Some true | BC_NE => Some false | _ => None end else None
  end.
Definition pcw (s : ast) : word := Z_to_bv 64 (s_pc s).
Definition next (s : ast) : ast := setpc s (bv_unsigned (v_addi (pcw s) 4)).

Inductive sres : Type := SNext (s : ast) | SFin (s : ast) (v : aval) (imm : Z) | SStuck (code : Z).

Definition astep (s : ast) : sres :=
  match fetch_entry (s_pc s) with
  | None => SStuck 1
  | Some i =>
    match i with
    | OpImm op rd rs imm =>
        match getreg s rs, op with
        | AL x, _ => SNext (next (setreg s rd (wlit (alu64 op (Z_to_bv 64 x) (sext 64 imm)))))
        | AS k o, ALU_ADD => SNext (next (setreg s rd (AS k (o + bv_signed imm))))
        | _, _ => SStuck 10
        end
    | ShiftImm op rd rs sh =>
        match getreg s rs with
        | AL x => SNext (next (setreg s rd (wlit (alu64 op (Z_to_bv 64 x) (zext 64 sh)))))
        | _ => SStuck 11
        end
    | Op op rd rs1 rs2 =>
        match getreg s rs1, getreg s rs2 with
        | AL x, AL y => SNext (next (setreg s rd (wlit (alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y)))))
        | _, _ => SStuck 12
        end
    | OpImm32 rd rs imm =>
        match getreg s rs with
        | AL x => SNext (next (setreg s rd (wlit (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 x)) (sext 32 imm))))))
        | _ => SStuck 13
        end
    | ShiftImm32 op rd rs sh =>
        match getreg s rs with
        | AL x => SNext (next (setreg s rd (wlit (sext 64 (alu32 op (low32 (Z_to_bv 64 x)) (zext 32 sh))))))
        | _ => SStuck 14
        end
    | Op32 op rd rs1 rs2 =>
        match getreg s rs1, getreg s rs2 with
        | AL x, AL y => SNext (next (setreg s rd (wlit (sext 64 (alu32 op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y)))))))
        | _, _ => SStuck 15
        end
    | Mul op rd rs1 rs2 =>
        match getreg s rs1, getreg s rs2 with
        | AL x, AL y => SNext (next (setreg s rd (wlit (mul_div op (Z_to_bv 64 x) (Z_to_bv 64 y)))))
        | _, _ => SStuck 16
        end
    | Mul32 op rd rs1 rs2 =>
        match getreg s rs1, getreg s rs2 with
        | AL x, AL y => SNext (next (setreg s rd (wlit (sext 64 (mul_div op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y)))))))
        | _, _ => SStuck 17
        end
    | Lui rd imm => SNext (next (setreg s rd (wlit (v_lui (Z.shiftl (bv_signed imm) 12)))))
    | Auipc rd imm => SNext (next (setreg s rd (wlit (v_auipc (pcw s) (Z.shiftl (bv_signed imm) 12)))))
    | Jal rd imm => SNext (setpc (setreg s rd (wlit (v_addi (pcw s) 4))) (bv_unsigned (btgt (pcw s) (bv_signed imm))))
    | Jalr rd rs1 imm =>
        match getreg s rs1 with
        | AL x => SNext (setpc (setreg s rd (wlit (v_addi (pcw s) 4))) (bv_unsigned (v_jalr (Z_to_bv 64 x) (bv_signed imm))))
        | v => SFin (setreg s rd (wlit (v_addi (pcw s) 4))) v (bv_signed imm)
        end
    | Branch c rs1 rs2 imm =>
        match abranch c (getreg s rs1) (getreg s rs2) with
        | Some true => SNext (setpc s (bv_unsigned (btgt (pcw s) (bv_signed imm))))
        | Some false => SNext (next s)
        | None => SStuck 20
        end
    | Fence _ _ _ _ _ => SNext (next s)
    | Load sz sx rd rs imm =>
        match classify C (aaddi (getreg s rs) (bv_signed imm)) with
        | Some ad =>
            match rdbs s ad (SymStepR.msize_bytes sz) with
            | Some l => match load_val sz sx l with Some v => SNext (next (setreg s rd v)) | None => SStuck 31 end
            | None => SStuck 32
            end
        | None => SStuck 33
        end
    | Store sz rs1 rs2 imm =>
        match classify C (aaddi (getreg s rs1) (bv_signed imm)) with
        | Some ad =>
            match store_bytes (SymStepR.msize_bytes sz) (getreg s rs2), resv_upd (s_resv s) ad with
            | Some l, Some rv' => match wrbs s ad l with Some s' => SNext (next (setresv s' rv')) | None => SStuck 41 end
            | _, _ => SStuck 42
            end
        | None => SStuck 43
        end
    | Lr wd aq rl rd rs =>
        match classify C (getreg s rs) with
        | Some ad =>
            if aalign ad (amo_bytes wd) then
              match rdbs s ad (amo_nbytes wd) with
              | Some l => match lits l with
                          | Some zs => SNext (next (setresv (setreg s rd (wlit (load_result (amo_msize wd) true (zbytes zs)))) (Some ad)))
                          | None => SStuck 51 end
              | None => SStuck 52
              end
            else SStuck 53
        | None => SStuck 54
        end
    | Sc wd aq rl rd rs1 rs2 =>
        match classify C (getreg s rs1), s_resv s with
        | Some ad, Some r =>
            if aalign ad (amo_bytes wd) && aaddr_eqb r ad then
              match store_bytes (amo_nbytes wd) (getreg s rs2) with
              | Some l => match wrbs s ad l with
                          | Some s' => SNext (next (setresv (setreg s' rd (AL 0)) None))
                          | None => SStuck 61 end
              | None => SStuck 62
              end
            else SStuck 63
        | _, _ => SStuck 64
        end
    | Amo op wd aq rl rd rs1 rs2 =>
        match classify C (getreg s rs1), getreg s rs2 with
        | Some ad, AL y =>
            if aalign ad (amo_bytes wd) then
              match rdbs s ad (amo_nbytes wd), resv_upd (s_resv s) ad with
              | Some l, Some rv' =>
                  match lits l with
                  | Some zs =>
                      match wrbs s ad (blits (amo_store_bytes op wd (zbytes zs) (Z_to_bv 64 y))) with
                      | Some s' => SNext (next (setresv (setreg s' rd (wlit (load_result (amo_msize wd) true (zbytes zs)))) rv'))
                      | None => SStuck 71 end
                  | None => SStuck 72
                  end
              | _, _ => SStuck 73
              end
            else SStuck 74
        | _, _ => SStuck 75
        end
    | _ => SStuck 2
    end
  end.

Fixpoint arun (fuel : nat) (s : ast) : result :=
  match fuel with
  | O => ROut s
  | S f => match astep s with
           | SNext s' => arun f s'
           | SFin s' v imm => RFin s' v imm
           | SStuck c => RStuck c (s_pc s)
           end
  end.

Fixpoint arunS (stops : list Z) (fuel : nat) (s : ast) : result :=
  match fuel with
  | O => ROut s
  | S f => if existsb (Z.eqb (s_pc s)) stops then ROut s else
           match astep s with
           | SNext s' => arunS stops f s'
           | SFin s' v imm => RFin s' v imm
           | SStuck c => RStuck c (s_pc s)
           end
  end.

Definition cell_lit (s : ast) (ad : aaddr) (n : nat) : option (list Z) :=
  match rdbs s ad n with Some l => lits l | None => None end.

Definition std_regs (f : nat -> aval) : list aval := AL 0 :: map f (seq 1 31).
Fixpoint regs_same (rs : list nat) (l0 l1 : list aval) : bool :=
  match rs with [] => true | r :: t => aval_eqb (nth r l0 (AL 0)) (nth r l1 (AL 0)) && regs_same t l0 l1 end.

End WithSegs.
End ISL.

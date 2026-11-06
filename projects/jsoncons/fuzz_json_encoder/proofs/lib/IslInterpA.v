(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FMapPositive.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec SymStepR.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ISLA.

Inductive aval : Type := AL (z : Z) | AS (k : nat) (off : Z) | AU.      (* [comment removed for export] *)
Inductive abyte : Type := BL (b : Z) | BS (k : nat) (off : Z) (i : nat).
Inductive aaddr : Type := AAbs (a : Z) | ARg (j : nat) (off : Z).
Record region : Type := RG { rg_k : nat; rg_lo : Z; rg_hi : Z }.
Inductive ckind : Type := KMemset | KMemcmp.
Record cfg : Type := CFG {
  c_rgs : list region;                 (* [comment removed for export] *)
  c_abs_hi : Z;                        (* [comment removed for export] *)
  c_wabs : list (Z * Z);               (* [comment removed for export] *)
  c_clear : list (Z * Z);              (* [comment removed for export] *)
  c_kn0 : list (Z * abyte);            (* [comment removed for export] *)
  c_zero : list (Z * Z);               (* [comment removed for export] *)
  c_calls : list (Z * ckind);          (* [comment removed for export] *)
  c_msok : list (Z * Z);               (* [comment removed for export] *)
  c_rook : list (Z * Z);               (* [comment removed for export] *)
  c_spk : nat                          (* [comment removed for export] *)
}.
Record ast : Type := ST {
  s_pc : Z; s_regs : list aval; s_abs : PositiveMap.t abyte; s_rgs : list (PositiveMap.t abyte); s_resv : option aaddr }.
Inductive result : Type := RFin (s : ast) (v : aval) (imm : Z) | ROut (s : ast) | RStuck (code : Z) (pc : Z).

(* [comment removed for export] *)
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
Definition aaddi (v : aval) (imm : Z) : aval := match v with AL z => AL (bv_wrap 64 (z + imm)) | AS k off => AS k (off + imm) | AU => AU end.

Fixpoint find_rg (rgs : list region) (k : nat) (off : Z) (j : nat) : option nat :=
  match rgs with
  | [] => None
  | rg :: t => if Nat.eqb (rg_k rg) k && (rg_lo rg <=? off) && (off <? rg_hi rg) then Some j else find_rg t k off (S j)
  end.
Definition classify (C : cfg) (v : aval) : option aaddr :=
  match v with
  | AL z => Some (AAbs z)
  | AS k off => match find_rg (c_rgs C) k off 0 with Some j => Some (ARg j off) | None => None end
  | AU => None
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

(* [comment removed for export] *)
Definition rdb0 (a : Z) : option abyte :=
  match kn_find (c_kn0 C) a with
  | Some b => Some b
  | None => if in_ivs (c_clear C) a then
              match seg_rom segs (Z_to_bv 64 a) with Some b => Some (BL (bv_unsigned b)) | None => None end
            else if in_ivs (c_zero C) a then Some (BL 0) else None
  end.
(* [comment removed for export] *)
Definition rdb (s : ast) (ad : aaddr) : option abyte :=
  match ad with
  | AAbs a =>
      if (0 <? a) && (a <? c_abs_hi C) then
        match PositiveMap.find (zkey a) (s_abs s) with
        | Some b => Some b
        | None => rdb0 a
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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
  | AU => None
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
        | AS k o => SFin (setreg s rd (wlit (v_addi (pcw s) 4))) (AS k o) (bv_signed imm)
        | AU => SStuck 18
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition CSAVEDN : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition gr (s : ast) (k : nat) : aval := nth k (s_regs s) (AL 0).
Fixpoint clobber_regs (k : nat) (l : list aval) : list aval :=
  match l with [] => [] | v :: t => (if (Nat.eqb k 0 || existsb (Nat.eqb k) CSAVEDN)%bool then v else AU) :: clobber_regs (S k) t end.
Definition unzkey (q : positive) : Z := match q with xH => Z0 | xO p => Zpos p | xI p => Zneg p end.
Definition prune_below (lo : Z) (t : PositiveMap.t abyte) : PositiveMap.t abyte :=
  fold_left (fun acc kb => if unzkey (fst kb) <? lo then PositiveMap.remove (fst kb) acc else acc) (PositiveMap.elements t) t.
Fixpoint prune_rgs (rgs : list region) (ts : list (PositiveMap.t abyte)) (lo : Z) : list (PositiveMap.t abyte) :=
  match rgs, ts with
  | rg :: rgs', t :: ts' => (if Nat.eqb (rg_k rg) (c_spk C) then prune_below lo t else t) :: prune_rgs rgs' ts' lo
  | _, _ => ts
  end.
Definition after_call (s : ast) (a0v : aval) (ret spoff : Z) : ast :=
  ST ret (upd 10 a0v (clobber_regs 0 (s_regs s))) (s_abs s) (prune_rgs (c_rgs C) (s_rgs s) spoff) None.
Fixpoint span_in (ivs : list (Z * Z)) (a : Z) (n : nat) : bool :=
  match n with O => true | S n' => in_ivs ivs a && span_in ivs (a + 1) n' end.
(* [comment removed for export] *)
Fixpoint zmemcmp (b1 b2 : list byte) : Z :=
  match b1, b2 with
  | x :: r1, y :: r2 => if Z.eqb (bv_unsigned x) (bv_unsigned y) then zmemcmp r1 r2 else bv_unsigned x - bv_unsigned y
  | _, _ => 0
  end.
Inductive event : Type :=
  | EvMemset (dst c n : Z) (spoff : Z) (ret : Z) (tp : Z)                            (* [comment removed for export] *)
  | EvMemcmp (poff : Z) (q n : Z) (zs1 zs2 : list Z) (spoff : Z) (ret : Z) (tp : Z). (* [comment removed for export] *)

Definition sum_memset (s : ast) : option (event * ast) :=
  match gr s 10, gr s 11, gr s 12, gr s 1, gr s 2, gr s 4, s_resv s with
  | AL dst, AL c, AL n, AL ret, AS k2 spoff, AL tp, None =>
      if (Nat.eqb k2 (c_spk C) && (0 <=? n) && span_in (c_msok C) dst (Z.to_nat n))%bool then
        match wrbs s (AAbs dst) (repeat (BL (c mod 256)) (Z.to_nat n)) with
        | Some s1 => Some (EvMemset dst c n spoff ret tp, after_call s1 (AL dst) ret spoff)
        | None => None
        end
      else None
  | _, _, _, _, _, _, _ => None
  end.
Definition sum_memcmp (s : ast) : option (event * ast) :=
  match gr s 10, gr s 11, gr s 12, gr s 1, gr s 2, gr s 4, s_resv s with
  | AS kp poff, AL q, AL n, AL ret, AS k2 spoff, AL tp, None =>
      if (Nat.eqb k2 (c_spk C) && Nat.eqb kp (c_spk C) && (0 <=? n) && span_in (c_rook C) q (Z.to_nat n) && (spoff <=? poff))%bool then
        match classify C (AS kp poff) with
        | Some adp =>
            match rdbs s adp (Z.to_nat n), rdbs s (AAbs q) (Z.to_nat n) with
            | Some l1, Some l2 =>
                match lits l1, lits l2 with
                | Some zs1, Some zs2 => Some (EvMemcmp poff q n zs1 zs2 spoff ret tp, after_call s (AL (zmemcmp (zbytes zs1) (zbytes zs2))) ret spoff)
                | _, _ => None
                end
            | _, _ => None
            end
        | None => None
        end
      else None
  | _, _, _, _, _, _, _ => None
  end.
Fixpoint find_call (l : list (Z * ckind)) (pc : Z) : option ckind :=
  match l with [] => None | (p, k) :: t => if Z.eqb p pc then Some k else find_call t pc end.
Definition summary (s : ast) : option (event * ast) :=
  match find_call (c_calls C) (s_pc s) with
  | Some KMemset => sum_memset s
  | Some KMemcmp => sum_memcmp s
  | None => None
  end.
Definition call_pcs : list Z := map fst (c_calls C).
Inductive cres : Type := CFin (s : ast) (v : aval) (imm : Z) (log : list event) | COut (s : ast) (log : list event) | CStuck (code : Z) (pc : Z) (log : list event).
(* [comment removed for export] *)
Fixpoint arunC (n : nat) (fuel : nat) (s : ast) : cres :=
  match n with
  | O => COut s []
  | S n' =>
      match arunS call_pcs fuel s with
      | ROut s1 =>
          if existsb (Z.eqb (s_pc s1)) call_pcs then
            match summary s1 with
            | Some (ev, s2) =>
                match arunC n' fuel s2 with
                | CFin s' v imm log => CFin s' v imm (ev :: log)
                | COut s' log => COut s' (ev :: log)
                | CStuck c pc log => CStuck c pc (ev :: log)
                end
            | None => CStuck 100 (s_pc s1) []
            end
          else COut s1 []
      | RFin s' v imm => CFin s' v imm []
      | RStuck c pc => CStuck c pc []
      end
  end.

(* [comment removed for export] *)
Definition cell_lit (s : ast) (ad : aaddr) (n : nat) : option (list Z) :=
  match rdbs s ad n with Some l => lits l | None => None end.
(* [comment removed for export] *)
Definition std_regs (f : nat -> aval) : list aval := AL 0 :: map f (seq 1 31).
Fixpoint regs_same (rs : list nat) (l0 l1 : list aval) : bool :=
  match rs with [] => true | r :: t => aval_eqb (nth r l0 (AL 0)) (nth r l1 (AL 0)) && regs_same t l0 l1 end.

End WithSegs.
End ISLA.

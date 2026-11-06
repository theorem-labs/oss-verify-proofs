(* Modified by Theorem Labs, 2026-10: proofs/plugin-hostd/fuzz_command/lib/A/Prog/__intscan_c.v at 2d2ff01bb6f; module paths changed to reac-pw/fuzz_headamp; 1 numeral(s) moved from fuzz_command.asan to fuzz_headamp.asan by alreloc a5c53bb2bed4. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/Prog/__intscan_c.v of this library by derive_y.py b7b132fb12a7: module paths lib.A -> lib.AU, the image module Asan -> AsanUbsan and Img0 -> Img0U, addresses moved from fuzz_headamp's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/Prog/__intscan_c.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Spec Require Import CType.
Import ListNotations.
Open Scope Z_scope.

Definition INTSCAN : Z := 0x94c9c.
Definition LMIN : Z := 9223372036854775808.
Definition M64 : Z := 18446744073709551615.

Fixpoint ndig (s : list byte) : nat :=
  match s with
  | b :: s' => if c_digit b then S (ndig s') else O
  | [] => O
  end.

Fixpoint dval (acc : Z) (s : list byte) : Z :=
  match s with
  | b :: s' => if c_digit b then dval (10 * acc + (bv_unsigned b - 48)) s' else acc
  | [] => acc
  end.

Definition sign_split (t : list byte) : bool * list byte :=
  match t with
  | b :: r => if bv_unsigned b =? 45 then (true, r) else if bv_unsigned b =? 43 then (false, r) else (false, t)
  | [] => (false, [])
  end.

Definition s10_neg (s : list byte) : bool := fst (sign_split (skip_space s)).
Definition s10_rest (s : list byte) : list byte := snd (sign_split (skip_space s)).
Definition s10_nd (s : list byte) : nat := ndig (s10_rest s).
Definition s10_mag (s : list byte) : Z := dval 0 (s10_rest s).
Definition s10_signed (s : list byte) : Z := if s10_neg s then - s10_mag s else s10_mag s.
Definition s10_val (s : list byte) : Z := Z.max (- LMIN) (Z.min (LMIN - 1) (s10_signed s)).
Definition atoi_a (s : list byte) : Z := bv_swrap 32 (s10_val s).
Definition s10_inrange (s : list byte) : bool := (- LMIN <=? s10_signed s) && (s10_signed s <=? LMIN - 1).
Definition s10_end (s : list byte) : Z :=
  if (s10_nd s =? 0)%nat then 0 else Z.of_nat (length s - length (s10_rest s) + s10_nd s).
Definition s10_errno (s : list byte) (ev : word) : word :=
  if (s10_nd s =? 0)%nat then Z_to_bv 64 22 else if s10_inrange s then ev else Z_to_bv 64 34.

Definition __intscan_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp P : Z) (str : list byte) (ev : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (s10_val str)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (Fp + 8, Fp + 16); (Fp + 184, Fp + 208);
              (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (Fp + 8) [C8 (Z_to_bv 64 (P + r)); C8 (Z_to_bv 64 M64)]
    /\ rw_cells rsegs m' (Fp + 184) [C8 (Z_to_bv 64 M64); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (s10_end str - r))]
    /\ rw_cells rsegs m' (bv_unsigned tp + -164) [C4 (s10_errno str ev)].

Definition __intscan_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp P : Z) (str : list byte) (ev : word) (lo : Z),
    rw_cells rsegs m (Fp + 8) [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 M64)] ->
    rw_cells rsegs m (Fp + 88) [C8 (Z_to_bv 64 P)] ->
    rw_cells rsegs m (Fp + 184) [C8 (Z_to_bv 64 M64); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    bytes_at rsegs m P (str ++ [Z_to_bv 8 0]) ->
    P + Z.of_nat (length str) + 1 < 2^64 ->
    rw_cells rsegs m (bv_unsigned tp + -164) [C4 ev] ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp ->
    (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
    (P + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= P) ->
    (bv_unsigned tp + -164 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -164) ->
    (P + Z.of_nat (length str) + 1 <= Fp \/ Fp + 232 <= P) ->
    (bv_unsigned tp + -164 + 4 <= Fp \/ Fp + 232 <= bv_unsigned tp + -164) ->
    mem_inv rsegs m ->
    evt rsegs (__intscan_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp P str ev lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 10) a2 (Z_to_bv 64 LMIN) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 INTSCAN) fc None m (seg_rom rsegs)).

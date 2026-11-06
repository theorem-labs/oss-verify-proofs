From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition REC_CALLS_EQUAL : Z := 0x157cc.
Definition REC_CALLS_EQUAL_FRAME : Z := 96.

Definition rc_entry : Type := (Z * list (word * list byte))%type.

Definition apart (lo hi a n : Z) : Prop := a + n <= lo \/ hi <= a.

Definition arg_at (m : word -> option byte) (lo hi a : Z) (k : nat) (p : word * list byte) : Prop :=
  bytes_at rsegs m (a + 8 + 8 * Z.of_nat k) (le8 (fst p)) /\
  bytes_at rsegs m (bv_unsigned (fst p)) (snd p ++ [Z_to_bv 8 0]) /\
  ~ In (Z_to_bv 8 0) (snd p) /\
  apart lo hi (bv_unsigned (fst p)) (Z.of_nat (length (snd p)) + 1).

Definition entry_at (m : word -> option byte) (lo hi a : Z) (e : rc_entry) : Prop :=
  -2^31 <= fst e < 2^31 /\
  (length (snd e) <= 6)%nat /\
  bytes_at rsegs m a (le4 (Z_to_bv 64 (fst e)) ++ le4 (Z_to_bv 64 (Z.of_nat (length (snd e))))) /\
  apart lo hi a 56 /\
  (forall k p, nth_error (snd e) k = Some p -> arg_at m lo hi a k p).

Definition calls_at (m : word -> option byte) (lo hi a : Z) (es : list rc_entry) : Prop :=
  (length es <= 16)%nat /\
  (forall i e, nth_error es i = Some e -> entry_at m lo hi (a + 56 * Z.of_nat i) e).

Definition cstr_eqb (x y : list byte) : bool :=
  if list_eq_dec Z.eq_dec (map bv_unsigned x) (map bv_unsigned y) then true else false.

Fixpoint args_eqb (x y : list (word * list byte)) : bool :=
  match x, y with
  | [], [] => true
  | p :: x', q :: y' => cstr_eqb (snd p) (snd q) && args_eqb x' y'
  | _, _ => false
  end.

Fixpoint calls_eqb (x y : list rc_entry) : bool :=
  match x, y with
  | [], [] => true
  | e :: x', f :: y' => (fst e =? fst f) && args_eqb (snd e) (snd f) && calls_eqb x' y'
  | _, _ => false
  end.

Definition rec_calls_equal_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (ca cb : list rc_entry),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REC_CALLS_EQUAL_FRAME <= bv_unsigned sp ->
    a1 = Z_to_bv 64 (Z.of_nat (length ca)) ->
    a3 = Z_to_bv 64 (Z.of_nat (length cb)) ->
    calls_at m (bv_unsigned sp - REC_CALLS_EQUAL_FRAME) (bv_unsigned sp) (bv_unsigned a0) ca ->
    calls_at m (bv_unsigned sp - REC_CALLS_EQUAL_FRAME) (bv_unsigned sp) (bv_unsigned a2) cb ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if calls_eqb ca cb then 1 else 0)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REC_CALLS_EQUAL_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REC_CALLS_EQUAL) fc None m (seg_rom rsegs)).

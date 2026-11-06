From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition WRITE_UINT : Z := 0x14944.

Definition write_uint_dg (x : Z) : byte := Z_to_bv 8 (48 + x).

Fixpoint write_uint_lsd (k : nat) (v : Z) : list byte :=
  match k with
  | O => []
  | S k' => write_uint_dg (v mod 10) :: (if v <? 10 then [] else write_uint_lsd k' (v / 10))
  end.

Definition write_uint_D (v : Z) : list byte := rev (write_uint_lsd 5 v).

Definition write_uint_n (v : Z) : Z := Z.of_nat (length (write_uint_D v)).

Definition write_uint_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o v lo : Z),
    a0 = Z_to_bv 64 o -> a1 = Z_to_bv 64 v -> 0 <= v < 65536 ->
    wr_at rsegs m o (write_uint_n v) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
    (o + write_uint_n v <= bv_unsigned sp - 16 \/ bv_unsigned sp <= o) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (write_uint_n v)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 16, bv_unsigned sp); (o, o + write_uint_n v)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' o (write_uint_D v))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 WRITE_UINT) fc None m (seg_rom rsegs)).

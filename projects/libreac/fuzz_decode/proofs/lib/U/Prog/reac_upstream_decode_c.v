From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import reac_frame_inspect_c reac_decode_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_UPSTREAM_DECODE : Z := 0x13f20.
Definition DIV36_MAGIC_AT : Z := 0x103a0.
Definition DIV36_MAGIC : Z := 0xe38e38e38e38e38f.

Definition up_nch (len : Z) : Z :=
  if (124 <=? len) && ((len - 52) mod 36 =? 0) && (((len - 52) / 36) mod 2 =? 0) && ((len - 52) / 36 <=? 40)
  then (len - 52) / 36 else -1.

Definition up_ok (raw out len : Z) (bs : list byte) : bool :=
  negb (raw =? 0) && negb (out =? 0) && (0 <=? up_nch len) &&
  (inspect_byte bs 12 =? 0x88) && (inspect_byte bs 13 =? 0x19) &&
  (inspect_byte bs (Z.to_nat (len - 2)) =? 0xC2) && (inspect_byte bs (Z.to_nat (len - 1)) =? 0xEA).

Definition reac_upstream_decode_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw out lo : Z),
    a0 = Z_to_bv 64 raw -> a2 = Z_to_bv 64 out ->
    0 <= raw < 2^64 -> 0 <= out < 2^64 -> bv_unsigned a1 < 2^32 ->
    bytes_at rsegs m DIV36_MAGIC_AT (le8 (Z_to_bv 64 DIV36_MAGIC)) ->
    (raw <> 0 -> out <> 0 -> 0 <= up_nch (bv_unsigned a1) ->
       length bs = Z.to_nat (bv_unsigned a1) /\ bytes_at rsegs m raw bs) ->
    (up_ok raw out (bv_unsigned a1) bs = true ->
       wr_at rsegs m out (36 * up_nch (bv_unsigned a1)) /\ out + 36 * up_nch (bv_unsigned a1) < 2^64 /\
       (out + 36 * up_nch (bv_unsigned a1) <= raw \/ raw + bv_unsigned a1 <= out)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    (raw <> 0 -> out <> 0 -> 0 <= up_nch (bv_unsigned a1) ->
       raw + bv_unsigned a1 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= raw) ->
    (up_ok raw out (bv_unsigned a1) bs = true ->
       out + 36 * up_nch (bv_unsigned a1) <= bv_unsigned sp - 48 \/ bv_unsigned sp <= out) ->
    (DIV36_MAGIC_AT + 8 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= DIV36_MAGIC_AT) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (if up_ok raw out (bv_unsigned a1) bs then 12 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         (if up_ok raw out (bv_unsigned a1) bs
          then munch [(bv_unsigned sp - 48, bv_unsigned sp); (out, out + 36 * up_nch (bv_unsigned a1))] m m' /\
               bytes_at rsegs m' out (braid_out bs (up_nch (bv_unsigned a1)) 12)
          else munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_UPSTREAM_DECODE) fc None m (seg_rom rsegs)).

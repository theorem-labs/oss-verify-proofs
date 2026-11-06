From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_WORDS_PIN_SET : Z := 0x157f8.
Definition CHECK_WORDS_PIN_SET_K : Z := 32.

Definition pin_verdict (r : Z) (w4 : list byte) : list byte :=
  if r <=? 4 then S_DASH
  else if prefixb w4 S_VERDICT then skipn 8 w4 else w4.

Definition check_words_pin_set_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (r nargs : Z) (p4 p3 : word) (w4 x3 : list byte),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_WORDS_PIN_SET_K <= bv_unsigned sp -> IMG_END <= lo ->
    0 <= r <= 64 -> a2 = Z_to_bv 64 r ->
    (4 < r -> word_slot m lo (bv_unsigned sp) (bv_unsigned a1 + 32) p4 w4) ->
    (4 < r -> bv_unsigned a1 <> 0 /\ bv_unsigned a1 mod 8 = 0 /\ bv_unsigned p4 <> 0) ->
    0 <= nargs <= 6 ->
    bytes_at rsegs m (bv_unsigned a0 + CALL_NARGS) (le4 (Z_to_bv 64 nargs)) ->
    outside_stack lo (bv_unsigned sp) (bv_unsigned a0 + CALL_NARGS) 4 ->
    bv_unsigned a0 <> 0 -> bv_unsigned a0 mod 8 = 0 ->
    (nargs = 4 -> word_slot m lo (bv_unsigned sp) (bv_unsigned a0 + CALL_ARGS + 24) p3 x3) ->
    nargs = 4 -> x3 = pin_verdict r w4 ->
    evt rsegs (void_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_WORDS_PIN_SET) fc None m (seg_rom rsegs)).

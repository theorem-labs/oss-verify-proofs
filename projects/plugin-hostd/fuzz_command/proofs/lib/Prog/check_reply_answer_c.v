From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandModel sup_reply_code_c.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_REPLY_ANSWER : Z := 0x14dc0.
Definition CHECK_REPLY_ANSWER_K : Z := 112.

Definition answer_ok (ans : word) (xr xa : list byte) (n : Z) (w0 : list byte) : Prop :=
  (bv_unsigned ans <> 0 -> xr = xa) /\
  (bv_unsigned ans = 0 -> reply_code xr < 0 \/ (n = 1 /\ w0 = S_QUIT)).

Definition check_reply_answer_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ans rep ww p0 : word) (xr xa w0 : list byte) (n : Z) (can : word),
    let S := bv_unsigned sp in
    mem_inv rsegs m ->
    stk rsegs m lo S -> lo + CHECK_REPLY_ANSWER_K <= S -> IMG_END <= lo ->
    bytes_at rsegs m GOT_GREC (le8 (Z_to_bv 64 G_REC)) ->
    bytes_at rsegs m (G_REC + REC_ANSWER) (le8 ans) ->
    bytes_at rsegs m (G_REC + REC_REPLY) (le8 rep) ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 can) ->
    bv_unsigned rep <> 0 ->
    cstr_at m (bv_unsigned rep) xr -> outside_stack lo S (bv_unsigned rep) (Z.of_nat (length xr) + 1) ->
    (bv_unsigned ans <> 0 ->
       cstr_at m (bv_unsigned ans) xa /\ outside_stack lo S (bv_unsigned ans) (Z.of_nat (length xa) + 1)) ->
    0 <= n < 2^31 ->
    bytes_at rsegs m (bv_unsigned a0 + WORDS_N) (le4 (Z_to_bv 64 n)) ->
    outside_stack lo S (bv_unsigned a0 + WORDS_N) 4 ->
    bytes_at rsegs m (bv_unsigned a0 + WORDS_W) (le8 ww) ->
    outside_stack lo S (bv_unsigned a0 + WORDS_W) 8 ->
    (n = 1 -> word_slot m lo S (bv_unsigned ww) p0 w0) ->
    answer_ok ans xr xa n w0 ->
    evt rsegs (void_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_REPLY_ANSWER) fc None m (seg_rom rsegs)).

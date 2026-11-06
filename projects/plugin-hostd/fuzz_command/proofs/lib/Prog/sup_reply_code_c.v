From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition SUP_REPLY_CODE : Z := 0x158fc.
Definition SUP_REPLY_CODE_FRAME : Z := 16.
Definition RESP_LIT : Z := 0x107d4.

Definition resp_lit_bytes : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 0].

Fixpoint atoi_digits (n : Z) (s : list byte) : Z :=
  match s with
  | [] => n
  | c :: s' =>
      if (48 <=? bv_unsigned c) && (bv_unsigned c <=? 57)
      then atoi_digits (bv_swrap 32 (10 * n - (bv_unsigned c - 48))) s'
      else n
  end.

Fixpoint atoi_musl (s : list byte) : Z :=
  match s with
  | [] => 0
  | c :: s' =>
      if ((9 <=? bv_unsigned c) && (bv_unsigned c <=? 13)) || (bv_unsigned c =? 32) then atoi_musl s'
      else if bv_unsigned c =? 45 then atoi_digits 0 s'
      else if bv_unsigned c =? 43 then bv_swrap 32 (- atoi_digits 0 s')
      else bv_swrap 32 (- atoi_digits 0 s)
  end.

Definition reply_code (x : list byte) : Z :=
  if list_eq_dec Z.eq_dec (map bv_unsigned (firstn 5 x)) [114; 101; 115; 112; 32]
  then atoi_musl (skipn 5 x)
  else -999.

Definition sup_reply_code_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (x : list byte),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + SUP_REPLY_CODE_FRAME <= bv_unsigned sp ->
    bv_unsigned a0 <> 0 ->
    bytes_at rsegs m (bv_unsigned a0) (x ++ [Z_to_bv 8 0]) ->
    ~ In (Z_to_bv 8 0) x ->
    bv_unsigned a0 + Z.of_nat (length x) + 1 <= bv_unsigned sp - SUP_REPLY_CODE_FRAME \/ bv_unsigned sp <= bv_unsigned a0 ->
    bytes_at rsegs m RESP_LIT resp_lit_bytes ->
    RESP_LIT + 6 <= bv_unsigned sp - SUP_REPLY_CODE_FRAME \/ bv_unsigned sp <= RESP_LIT ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (reply_code x)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - SUP_REPLY_CODE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SUP_REPLY_CODE) fc None m (seg_rom rsegs)).

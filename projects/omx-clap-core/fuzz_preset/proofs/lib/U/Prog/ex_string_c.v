From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
Import ListNotations.
Open Scope Z_scope.

Definition EX_STRING : Z := 0x14d1c.
Definition EX_STRING_K : Z := 128.

Definition ex_string_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q x0 i0 scr lo : Z) (x : list byte),
    a0 = Z_to_bv 64 q -> q mod 8 = 0 ->
    bytes_at rsegs m q (le8 (Z_to_bv 64 (x0 + i0))) ->
    bytes_at rsegs m (q + 8) (le8 (Z_to_bv 64 (x0 + Z.of_nat (length x)))) ->
    bytes_at rsegs m (q + 24) (le8 (Z_to_bv 64 scr)) ->
    wr_at rsegs m q 8 ->
    bytes_at rsegs m x0 x -> 0 < x0 -> x0 + Z.of_nat (length x) < 2 ^ 64 -> Z.of_nat (length x) < 2 ^ 63 ->
    0 <= i0 < Z.of_nat (length x) ->
    0 < scr -> wr_at rsegs m scr (Z.of_nat (length x) + 1) ->
    (scr + Z.of_nat (length x) + 1 <= q \/ q + 40 <= scr) ->
    (scr + Z.of_nat (length x) + 1 <= x0 \/ x0 + Z.of_nat (length x) <= scr) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + EX_STRING_K <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (bv_unsigned sp <= q \/ q + 40 <= bv_unsigned sp - EX_STRING_K) ->
    (bv_unsigned sp <= x0 \/ x0 + Z.of_nat (length x) <= bv_unsigned sp - EX_STRING_K) ->
    (bv_unsigned sp <= scr \/ scr + Z.of_nat (length x) + 1 <= bv_unsigned sp - EX_STRING_K) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         match fst (fst (jr_string (map bv_unsigned (skipn (S (Z.to_nat i0)) x)) [])) with
         | None => r = Z_to_bv 64 (-1) /\
             munch [(bv_unsigned sp - EX_STRING_K, bv_unsigned sp); (scr, scr + Z.of_nat (length x) - i0 - 1)] m m'
         | Some (s, rest) => r = Z_to_bv 64 0 /\
             munch [(q, q + 8); (bv_unsigned sp - EX_STRING_K, bv_unsigned sp); (scr, scr + Z.of_nat (length s) + 1)] m m' /\
             (exists c, scan (map bv_unsigned (skipn (S (Z.to_nat i0)) x)) = Some c /\
                rest = skipn (S c) (map bv_unsigned (skipn (S (Z.to_nat i0)) x)) /\
                bytes_at rsegs m' q (le8 (Z_to_bv 64 (x0 + i0 + Z.of_nat c + 2)))) /\
             bytes_at rsegs m' scr (map (Z_to_bv 8) s ++ [Z_to_bv 8 0])
         end)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EX_STRING) fc None m (seg_rom rsegs)).

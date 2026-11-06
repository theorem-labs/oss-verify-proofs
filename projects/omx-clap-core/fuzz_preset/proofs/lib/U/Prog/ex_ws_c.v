From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
Import ListNotations.
Open Scope Z_scope.

Definition EX_WS : Z := 0x14cbc.

Definition ex_ws_p1 (x0 i0 : Z) (x : list byte) : Z :=
  x0 + Z.of_nat (length x) - Z.of_nat (length (skip (map bv_unsigned (skipn (Z.to_nat i0) x)))).

Definition ex_ws_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q x0 i0 : Z) (x : list byte),
    a0 = Z_to_bv 64 q -> q mod 8 = 0 ->
    bytes_at rsegs m q (le8 (Z_to_bv 64 (x0 + i0))) ->
    bytes_at rsegs m (q + 8) (le8 (Z_to_bv 64 (x0 + Z.of_nat (length x)))) ->
    wr_at rsegs m q 8 ->
    bytes_at rsegs m x0 x -> 0 < x0 -> x0 + Z.of_nat (length x) < 2 ^ 62 -> 0 <= i0 <= Z.of_nat (length x) ->
    ((length x = 0)%nat \/ q + 16 <= x0 \/ x0 + Z.of_nat (length x) <= q) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(q, q + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         bytes_at rsegs m' q (le8 (Z_to_bv 64 (ex_ws_p1 x0 i0 x))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EX_WS) fc None m (seg_rom rsegs)).

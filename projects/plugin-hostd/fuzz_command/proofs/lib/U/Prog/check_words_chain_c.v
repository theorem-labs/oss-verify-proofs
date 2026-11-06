From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel CommandFP printf_facts_c atoi_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_WORDS_CHAIN : Z := 0x15658.
Definition CHECK_WORDS_CHAIN_K : Z := 6848.

Fixpoint chain_items (k : nat) (n : nat) (ws : list (list byte)) : list Z :=
  match n with
  | O => []
  | S n' => (if Nat.eqb k 2 then [] else [32]) ++ pf_dec (atoi_val (nth k ws [])) ++ chain_items (S k) n' ws
  end.

Definition chain_list (r : Z) (ws : list (list byte)) : list Z := chain_items 2 (Z.to_nat (r - 2)) ws.

Definition check_words_chain_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (r nargs : Z) (wp : list word) (ws : list (list byte)) (p1 p2 : word) (x1 x2 : list byte) (can : word),
    mem_inv rsegs m -> MemNorm.task_mem rsegs m -> frm0 fc ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_WORDS_CHAIN_K <= bv_unsigned sp -> IMG_END <= lo ->
    bv_unsigned sp < 2^63 ->
    rw_cells rsegs m GOT_GUARD [C8 (Z_to_bv 64 GUARD)] -> rw_cells rsegs m GUARD [C8 can] ->
    0 <= r <= 64 -> a2 = Z_to_bv 64 r ->
    (forall k, 2 <= k < r ->
       word_slot m lo (bv_unsigned sp) (bv_unsigned a1 + 8 * k) (nth (Z.to_nat k) wp (Z_to_bv 64 0)) (nth (Z.to_nat k) ws [])) ->
    (2 < r -> bv_unsigned a1 <> 0 /\ bv_unsigned a1 mod 8 = 0) ->
    0 <= nargs <= 6 ->
    bytes_at rsegs m (bv_unsigned a0 + CALL_NARGS) (le4 (Z_to_bv 64 nargs)) ->
    outside_stack lo (bv_unsigned sp) (bv_unsigned a0 + CALL_NARGS) 4 ->
    bv_unsigned a0 <> 0 -> bv_unsigned a0 mod 8 = 0 ->
    (nargs = 3 -> word_slot m lo (bv_unsigned sp) (bv_unsigned a0 + CALL_ARGS + 8) p1 x1) ->
    (nargs = 3 -> word_slot m lo (bv_unsigned sp) (bv_unsigned a0 + CALL_ARGS + 16) p2 x2) ->
    nargs = 3 -> x1 = pf_bytes (pf_dec (r - 2)) -> x2 = pf_bytes (chain_list r ws) ->
    evt rsegs (fp_void_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_WORDS_CHAIN) fc None m (seg_rom rsegs)).

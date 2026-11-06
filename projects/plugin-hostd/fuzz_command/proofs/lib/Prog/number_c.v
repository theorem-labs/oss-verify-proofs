From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import VerbsMem.
Import ListNotations.
Open Scope Z_scope.

Definition NUMBER : Z := 0x17c70.
Definition NUMBER_K : Z := 400.

Definition number_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo out : Z) (wd ob : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (match number_m wd with Some _ => 1 | None => 0 end))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - NUMBER_K, bv_unsigned sp); (out, out + 4);
           (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    bytes_at rsegs m' out (match number_m wd with Some v => le4 (Z_to_bv 64 v) | None => ob end).

Definition number_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (can ev : word) (wd ob : list byte),
    cstr0_at m (bv_unsigned a0) wd ->
    4096 <= bv_unsigned a0 -> Z.of_nat (length wd) <= 8192 ->
    bv_unsigned a0 + Z.of_nat (length wd) + 1 <= 2^63 ->
    bv_unsigned a1 mod 4 = 0 ->
    bytes_at rsegs m (bv_unsigned a1) ob -> length ob = 4%nat -> wr_at rsegs m (bv_unsigned a1) 4 ->
    rw_cells rsegs m (bv_unsigned tp + -164) [C4 ev] ->
    ssp_at m can ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + NUMBER_K <= bv_unsigned sp ->
    off_lo lo sp (bv_unsigned a0) (Z.of_nat (length wd) + 1) ->
    off_lo lo sp (bv_unsigned a1) 4 ->
    off_lo lo sp (bv_unsigned tp + -164) 4 ->
    off_lo lo sp SSP_GOT 8 -> off_lo lo sp SSP_GUARD 8 ->
    (bv_unsigned a1 + 4 <= bv_unsigned a0 \/ bv_unsigned a0 + Z.of_nat (length wd) + 1 <= bv_unsigned a1) ->
    (bv_unsigned tp + -164 + 4 <= bv_unsigned a0 \/ bv_unsigned a0 + Z.of_nat (length wd) + 1 <= bv_unsigned tp + -164) ->
    (bv_unsigned tp + -164 + 4 <= bv_unsigned a1 \/ bv_unsigned a1 + 4 <= bv_unsigned tp + -164) ->
    (bv_unsigned tp + -164 + 4 <= SSP_GUARD \/ SSP_GUARD + 8 <= bv_unsigned tp + -164) ->
    evt rsegs (number_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (bv_unsigned a1) wd ob m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 NUMBER) fc None m (seg_rom rsegs)).

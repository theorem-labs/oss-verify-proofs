From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition SSP_GOT : Z := 0x22d40.
Definition SSP_GUARD : Z := 0x54730.

Definition ssp_at (m : word -> option byte) (can : word) : Prop :=
  bytes_at rsegs m SSP_GOT (le8 (Z_to_bv 64 SSP_GUARD)) /\ bytes_at rsegs m SSP_GUARD (le8 can).

Definition cstr0_at (m : word -> option byte) (s : Z) (bs : list byte) : Prop :=
  bytes_at rsegs m s (bs ++ [Z_to_bv 8 0]) /\ Forall (fun b => bv_unsigned b <> 0) bs.

Definition cstr_at (m : word -> option byte) (s : Z) (bs slack : list byte) : Prop :=
  bytes_at rsegs m s (bs ++ Z_to_bv 8 0 :: slack) /\
  Forall (fun b => bv_unsigned b <> 0) bs /\
  (- (s + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length slack).

Definition off_stack (sp : word) (K a n : Z) : Prop := a + n <= bv_unsigned sp - K \/ bv_unsigned sp <= a.

Definition off_lo (lo : Z) (sp : word) (a n : Z) : Prop := a + n <= lo \/ bv_unsigned sp <= a.

Definition kret (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo K : Z) (m : word -> option byte) (W : list ivl) (R : word -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch ((bv_unsigned sp - K, bv_unsigned sp) :: W) m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    R a0'.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c.
Import ListNotations.
Open Scope Z_scope.

Definition ASAN_STACK_FREE_6 : Z := 0x3dd30.
Definition ASAN_STACK_FREE_K : Z := 32.

Definition asan_stack_free_post (c : nat) (K : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (L FS j lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    let fr := fs_frame FS c j in let n := fs_shadow_n c L in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(fs_flag FS c j, fs_flag FS c j + 1); (shadow_addr fr, shadow_addr fr + n);
              (bv_unsigned sp - K, bv_unsigned sp)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ fs_place m' FS
    /\ bytes_at rsegs m' (fs_flag FS c j) [Z_to_bv 8 0]
    /\ bytes_at rsegs m' (shadow_addr fr) (repeat (Z_to_bv 8 0xf5) (Z.to_nat n))
    /\ asan_cells m' /\ shadow_rw m'.

Definition asan_stack_free_contract (c : nat) (entry K : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FS j : Z),
  let fr := bv_unsigned a0 in let L := bv_unsigned a1 in let S0 := bv_unsigned sp in
  0 <= j < fs_M c -> fr = fs_frame FS c j ->
  1 <= L <= fs_B c -> L mod 8 = 0 ->
  fs_place m FS ->
  bytes_at rsegs m (fs_flag FS c j) [Z_to_bv 8 1] ->
  bytes_at rsegs m (fr + fs_B c - 8) (le8 (Z_to_bv 64 (fs_flag FS c j))) ->
  asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
  stk rsegs m lo S0 -> lo + K <= S0 -> FS + FS_SIZE <= S0 - K ->
  HIGHMEM_BEG <= lo -> S0 <= APPMEM_END ->
  evt rsegs (asan_stack_free_post c K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS j lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).

Definition asan_stack_free_6_contract : Prop :=
  asan_stack_free_contract 6 ASAN_STACK_FREE_6 ASAN_STACK_FREE_K.

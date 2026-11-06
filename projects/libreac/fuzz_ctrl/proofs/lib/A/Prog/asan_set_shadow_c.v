From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
Import ListNotations.
Open Scope bv_scope.

Definition ASAN_SET_SHADOW_00 : Z := 0x54ee8.
Definition ASAN_SET_SHADOW_F5 : Z := 0x54ff0.
Definition ASAN_SET_SHADOW_F8 : Z := 0x55008.

Definition asan_set_shadow_post (v : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (a0 a1 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a1)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a1)) (repeat (Z_to_bv 8 v) (Z.to_nat (bv_unsigned a1)))].

Definition asan_set_shadow_contract (entry v : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  let A := bv_unsigned a0 in let N := bv_unsigned a1 in
  (forall i, (0 <= i < N)%Z -> in_shadow (A + i)) ->
  rw_cells rsegs m A [CB (Z.to_nat N) junk] ->
  asan_cells m -> mem_inv rsegs m ->
  evt rsegs (asan_set_shadow_post v ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).

Definition asan_set_shadow_00_contract : Prop := asan_set_shadow_contract ASAN_SET_SHADOW_00 0x00.
Definition asan_set_shadow_f5_contract : Prop := asan_set_shadow_contract ASAN_SET_SHADOW_F5 0xf5.
Definition asan_set_shadow_f8_contract : Prop := asan_set_shadow_contract ASAN_SET_SHADOW_F8 0xf8.

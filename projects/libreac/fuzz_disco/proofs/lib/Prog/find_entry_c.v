From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c.
Import ListNotations.
Open Scope Z_scope.

Definition FIND_ENTRY : Z := 0x14b08.
Definition FIND_ENTRY_K : Z := 48.

Definition find_entry_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo t p : Z) (T P : list byte),
    a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 p ->
    t <> 0 -> t mod 8 = 0 ->
    bytes_at rsegs m t T -> length T = 400%nat ->
    bytes_at rsegs m p P -> length P = 6%nat ->
    tbl_T1 T ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + FIND_ENTRY_K <= bv_unsigned sp ->
    off_window sp FIND_ENTRY_K t 400 -> off_window sp FIND_ENTRY_K p 6 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte) (r : Z),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - FIND_ENTRY_K, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         find_res T P r)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FIND_ENTRY) fc None m (seg_rom rsegs)).

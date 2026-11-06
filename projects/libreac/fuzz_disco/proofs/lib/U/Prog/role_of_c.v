From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c find_entry_c.
Import ListNotations.
Open Scope Z_scope.

Definition ROLE_OF : Z := 0x146b0.
Definition ROLE_OF_K : Z := 16 + FIND_ENTRY_K.

Definition role_res (T P : list byte) (v : Z) : Prop :=
  exists r, find_res T P r /\ v = (if r <? 0 then -1 else role_of_e T r).

Definition role_of_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo t p : Z) (T P : list byte),
    a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 p ->
    t <> 0 -> t mod 8 = 0 ->
    bytes_at rsegs m t T -> length T = 400%nat ->
    bytes_at rsegs m p P -> length P = 6%nat ->
    tbl_T1 T -> tbl_T2 T ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + ROLE_OF_K <= bv_unsigned sp ->
    off_window sp ROLE_OF_K t 400 -> off_window sp ROLE_OF_K p 6 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte) (v : Z),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - ROLE_OF_K, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         role_res T P v /\ (v = -1 \/ v = 0 \/ v = 1 \/ v = 2))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ROLE_OF) fc None m (seg_rom rsegs)).

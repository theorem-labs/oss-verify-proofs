From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOXREG_INIT : Z := 0x139d8.
Definition REAC_BOXREG_INIT_FRAME : Z := 32.

Definition clamp40 (x : Z) : Z := if (1 <=? x) && (x <=? 40) then x else 40.

Definition init_bytes (f : Z) : list byte := repeat (Z_to_bv 8 0) 284 ++ le4 (Z_to_bv 64 f).

Definition reac_boxreg_init_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo r : Z) (junk : list byte),
    a0 = Z_to_bv 64 r ->
    rw_cells rsegs m r [CB 288 junk] -> r <> 0 -> r mod 4 = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_BOXREG_INIT_FRAME <= bv_unsigned sp ->
    (r + 288 <= bv_unsigned sp - REAC_BOXREG_INIT_FRAME \/ bv_unsigned sp <= r) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(r, r + 288); (bv_unsigned sp - REAC_BOXREG_INIT_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' r (init_bytes (clamp40 (bv_swrap 32 (bv_unsigned a1)))) /\
         boxreg_inv (init_bytes (clamp40 (bv_swrap 32 (bv_unsigned a1)))) /\
         bx_n (init_bytes (clamp40 (bv_swrap 32 (bv_unsigned a1)))) = 0 /\
         bx_fabric (init_bytes (clamp40 (bv_swrap 32 (bv_unsigned a1)))) = clamp40 (bv_swrap 32 (bv_unsigned a1)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOXREG_INIT) fc None m (seg_rom rsegs)).

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Prog Require Import reac_knock_struct.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_KNOCK_STEP : Z := 0x12e1c.

Definition knock_step_f (st g : Z) (due heard t : word) : Z * Z * word * Z :=
  if Z.eqb st 2 then
    if (bv_unsigned t <=? bv_unsigned heard) || (bv_unsigned t - bv_unsigned heard <? L_NS)
    then (0, st, due, g)
    else (1, 1, Z_to_bv 64 (bv_unsigned heard + L_NS), 1)
  else if Z.eqb st 0 then
    if bv_unsigned t <? bv_unsigned due then (0, st, due, g) else (1, 1, due, 1)
  else (0, st, due, g).

Definition reac_knock_step_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (st : Z) (p1 opened due heard : word) (g : Z) (p2 : word),
    0 <= st < 2^32 -> 0 <= g < 2^32 ->
    bv_unsigned a0 <> 0 -> bv_unsigned a0 mod 8 = 0 ->
    rw_cells rsegs m (bv_unsigned a0) (knock_cells st p1 opened due heard g p2) ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned a0, bv_unsigned a0 + 40)] m m' /\
         wmono rsegs m m' /\
         let '(r, st', due', g') := knock_step_f st g due heard a1 in
         a0' = Z_to_bv 64 r /\
         rw_cells rsegs m' (bv_unsigned a0) (knock_cells st' p1 opened due' heard g' p2))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_KNOCK_STEP) fc None m (seg_rom rsegs)).

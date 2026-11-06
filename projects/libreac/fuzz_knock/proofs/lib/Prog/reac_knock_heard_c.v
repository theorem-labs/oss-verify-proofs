From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Prog Require Import reac_knock_struct.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_KNOCK_HEARD : Z := 0x12d9c.

Definition reac_knock_heard_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (st : Z) (p1 opened due heard : word) (g : Z) (p2 : word),
    0 <= st < 2^32 -> 0 <= g < 2^32 ->
    rw_cells rsegs m (bv_unsigned a0) (knock_cells st p1 opened due heard g p2) ->
    evt rsegs
      (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned a0, bv_unsigned a0 + 40)] m m' /\
         wmono rsegs m m' /\
         rw_cells rsegs m' (bv_unsigned a0)
           (knock_cells (if Z.eqb st 0 then 2 else st) p1 opened due a1 g p2))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_KNOCK_HEARD) fc None m (seg_rom rsegs)).

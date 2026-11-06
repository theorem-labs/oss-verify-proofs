From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c disco_table_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_HUNT_INIT : Z := 0x15eb4.

Definition hunt_init_bytes (ob : list byte) (now : Z) : list byte :=
  repeat (Z_to_bv 8 0) 412 ++ ob ++ repeat (Z_to_bv 8 0) 6 ++ le8 (Z_to_bv 64 now) ++ repeat (Z_to_bv 8 0) 48.

Definition reac_hunt_init_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (h our now lo : Z) (junk ob : list byte),
    a0 = Z_to_bv 64 h -> 0 < h -> h mod 8 = 0 ->
    rw_cells rsegs m h [CB 480 junk] ->
    a1 = Z_to_bv 64 our -> 0 <= our < 2^64 ->
    (our <> 0 -> bytes_at rsegs m our ob /\ length ob = 6%nat /\
                 (our + 6 <= h \/ h + 480 <= our) /\ (our + 6 <= lo \/ bv_unsigned sp <= our)) ->
    a2 = Z_to_bv 64 now -> 0 <= now < 2^64 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
    (h + 480 <= lo \/ bv_unsigned sp <= h) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 32, bv_unsigned sp); (h, h + 480)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' h (hunt_init_bytes (if our =? 0 then repeat (Z_to_bv 8 0) 6 else ob) now) /\
         table_ok (firstn 400 (hunt_init_bytes (if our =? 0 then repeat (Z_to_bv 8 0) 6 else ob) now)) /\
         lock_ok (firstn 12 (skipn 400 (hunt_init_bytes (if our =? 0 then repeat (Z_to_bv 8 0) 6 else ob) now))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_HUNT_INIT) fc None m (seg_rom rsegs)).

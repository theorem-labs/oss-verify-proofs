From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_IDENTITY_INIT : Z := 0x14954.

Definition reac_identity_init_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (id : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(id, id + 38)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ (id = 0 -> m' = m)
    /\ (id <> 0 -> rw_cells rsegs m' id [CB 38 (repeat (Z_to_bv 8 0) 38)]).

Definition reac_identity_init_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (id : Z) (idb : list byte),
    a0 = Z_to_bv 64 id -> 0 <= id < 2^64 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    mem_inv rsegs m ->
    evt rsegs (reac_identity_init_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m id)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_IDENTITY_INIT) fc None m (seg_rom rsegs)).

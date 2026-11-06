From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_HUNT_VERDICT_NAME : Z := 0x15e80.
Definition TB : Z := 0x1058c.
Definition A_MASTER : Z := 0x103e6.
Definition A_SLAVE : Z := 0x10453.
Definition A_REFUSED : Z := 0x103af.
Definition A_HUNTING : Z := 0x102b1.

Definition cstr (l : list Z) : list byte := map (Z_to_bv 8) (l ++ [0]).
Definition S_MASTER : list byte := cstr [109; 97; 115; 116; 101; 114].
Definition S_SLAVE : list byte := cstr [115; 108; 97; 118; 101].
Definition S_REFUSED : list byte := cstr [114; 101; 102; 117; 115; 101; 100].
Definition S_HUNTING : list byte := cstr [104; 117; 110; 116; 105; 110; 103].

Definition reac_hunt_verdict_name_model (v : Z) : Z :=
  if v =? 1 then A_MASTER else if v =? 2 then A_SLAVE else if v =? 3 then A_REFUSED else A_HUNTING.
Definition reac_hunt_verdict_name_str (v : Z) : list byte :=
  if v =? 1 then S_MASTER else if v =? 2 then S_SLAVE else if v =? 3 then S_REFUSED else S_HUNTING.

Definition reac_hunt_verdict_name_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v : Z),
    a0 = Z_to_bv 64 v -> -2^31 <= v < 2^31 ->
    bytes_at rsegs m TB (le4 (Z_to_bv 64 (-422))) ->
    bytes_at rsegs m (TB + 4) (le4 (Z_to_bv 64 (-313))) ->
    bytes_at rsegs m (TB + 8) (le4 (Z_to_bv 64 (-477))) ->
    bytes_at rsegs m A_MASTER S_MASTER -> bytes_at rsegs m A_SLAVE S_SLAVE ->
    bytes_at rsegs m A_REFUSED S_REFUSED -> bytes_at rsegs m A_HUNTING S_HUNTING ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (reac_hunt_verdict_name_model v)) a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs) /\
         bytes_at rsegs m (reac_hunt_verdict_name_model v) (reac_hunt_verdict_name_str v))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_HUNT_VERDICT_NAME) fc None m (seg_rom rsegs)).

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_RIVAL_KIND_OF : Z := 0x16498.

Definition reac_rival_kind_model (d r s c : Z) : Z :=
  if negb (d =? 0) then 2
  else if r =? 1 then 2
  else if (1 <=? s) && (s <? 40) then 2
  else if c =? 0 then 3
  else if c <? 40 then 2
  else if negb (r =? 2) then 3
  else if s =? 40 then 1
  else 4.

Definition reac_rival_kind_of_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (e r d s c : Z),
    a0 = Z_to_bv 64 e -> 0 <= e < 2^64 -> e mod 8 = 0 ->
    (e <> 0 ->
       -2^31 <= r < 2^31 /\ 0 <= d < 2^8 /\ 0 <= s < 2^8 /\ 0 <= c < 2^32 /\
       bytes_at rsegs m (e + 8) (le4 (Z_to_bv 64 r)) /\ bytes_at rsegs m (e + 12) [Z_to_bv 8 d] /\
       bytes_at rsegs m (e + 16) [Z_to_bv 8 s] /\ bytes_at rsegs m (e + 20) (le4 (Z_to_bv 64 c))) ->
    evt rsegs
      (fun ms' => exists a1' a2' a3' a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if e =? 0 then 0 else reac_rival_kind_model d r s c))
                       a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_RIVAL_KIND_OF) fc None m (seg_rom rsegs)).

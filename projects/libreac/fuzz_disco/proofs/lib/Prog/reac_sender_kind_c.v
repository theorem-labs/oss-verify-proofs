From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_rate_snap_c reac_rival_kind_of_c reac_master_only_cadence_ns_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_SENDER_KIND : Z := 0x1666c.

Definition reac_sender_kind_model (e r d s c fs now : Z) : Z :=
  if e =? 0 then 0
  else if negb (d =? 0) || (r =? 1) || (r =? 2) then reac_rival_kind_model d r s c
  else if c =? 0 then 3
  else if now <=? fs then 3
  else if now - fs <? 10^9 then 3
  else 2.

Definition reac_sender_kind_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (e now fps r d s c fs lo : Z),
    a0 = Z_to_bv 64 e -> 0 <= e < 2^64 -> e mod 8 = 0 ->
    a1 = Z_to_bv 64 now -> 0 <= now < 2^64 ->
    a2 = Z_to_bv 64 fps -> -2^31 <= fps < 2^31 ->
    (e <> 0 ->
       -2^31 <= r < 2^31 /\ 0 <= d < 2^8 /\ 0 <= s < 2^8 /\ 0 <= c < 2^32 /\ 0 <= fs < 2^64 /\
       bytes_at rsegs m (e + 8) (le4 (Z_to_bv 64 r)) /\ bytes_at rsegs m (e + 12) [Z_to_bv 8 d] /\
       bytes_at rsegs m (e + 16) [Z_to_bv 8 s] /\ bytes_at rsegs m (e + 20) (le4 (Z_to_bv 64 c)) /\
       bytes_at rsegs m (e + 32) (le8 (Z_to_bv 64 fs))) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> RT + 12 <= lo ->
    bytes_at rsegs m RT RATES ->
    bytes_at rsegs m A_P6000 (le8 (Z_to_bv 64 D6000)) ->
    bytes_at rsegs m A_P3837 (le8 (Z_to_bv 64 D3837)) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' a5' : word) (F' : bvmap 5 word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (reac_sender_kind_model e r d s c fs now))
                       a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\ freg_kept F F')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_SENDER_KIND) fc None m (seg_rom rsegs)).

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c SightModel.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_SIGHTING : Z := 0x1471c.
Definition CHECK_SIGHTING_K : Z := 48.

Definition check_sighting_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo s f len u st : Z) (S FB U : list byte),
    a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 f -> a2 = Z_to_bv 64 len -> a3 = Z_to_bv 64 u -> a4 = Z_to_bv 64 st ->
    0 < s -> s mod 4 = 0 -> bytes_at rsegs m s S ->
    0 < f -> f + len <= 2 ^ 64 -> length FB = 50%nat -> bytes_at rsegs m f FB ->
    length U = 6%nat -> bytes_at rsegs m u U ->
    0 <= st < 2 ^ 64 ->
    len <= 65535 ->
    sighting_facts S FB U len st ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_SIGHTING_K <= bv_unsigned sp ->
    (s + 24 <= bv_unsigned sp - CHECK_SIGHTING_K \/ bv_unsigned sp <= s) ->
    (f + 50 <= bv_unsigned sp - CHECK_SIGHTING_K \/ bv_unsigned sp <= f) ->
    (u + 6 <= bv_unsigned sp - CHECK_SIGHTING_K \/ bv_unsigned sp <= u) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_SIGHTING_K, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_SIGHTING) fc None m (seg_rom rsegs)).

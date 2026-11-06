(* Ported by RtStr from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Prog/twoway_loops_c.v, unchanged. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Spec Require Import TwoWay.
Import ListNotations.
Open Scope Z_scope.

Definition MSUF1_OK : Prop :=
  forall (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x : list byte) (c jp k p : nat),
    bytes_at rsegs m (bv_unsigned s0) (x ++ [Z_to_bv 8 0]) ->
    bv_unsigned s7 = Z.of_nat (length x) ->
    (c <= jp)%nat -> (1 <= k <= p)%nat -> (p <= length x)%nat -> (jp + k < length x)%nat ->
    (forall (c' p' : nat) (y2 y3 y4 y5 y6 : word),
        msuf_run Z.gtb (map bv_unsigned x) c jp k p c' p' ->
        evt rsegs Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat c' - 1)) (Z_to_bv 64 (Z.of_nat p'))
                   y2 y3 y4 y5 y6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x9b56c) fc None m (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat c - 1)) (Z_to_bv 64 (Z.of_nat p))
               (Z_to_bv 64 (Z.of_nat jp)) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (Z.of_nat (jp + k))) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9b308) fc None m (seg_rom rsegs)).

Definition MSUF2_OK : Prop :=
  forall (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x : list byte) (c jp k p : nat),
    bytes_at rsegs m (bv_unsigned s0) (x ++ [Z_to_bv 8 0]) ->
    bv_unsigned s7 = Z.of_nat (length x) ->
    (c <= jp)%nat -> (1 <= k <= p)%nat -> (p <= length x)%nat -> (jp + k < length x)%nat ->
    (forall (c' p' : nat) (y2 y3 y4 y5 y6 : word),
        msuf_run Z.ltb (map bv_unsigned x) c jp k p c' p' ->
        evt rsegs Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 y2 y3 y4 y5 y6 a7
                   s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (Z.of_nat c' - 1)) (Z_to_bv 64 (Z.of_nat p')) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x9b35c) fc None m (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1
               (Z_to_bv 64 (Z.of_nat jp)) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (Z.of_nat (jp + k))) a5 a6 a7
               s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (Z.of_nat c - 1)) (Z_to_bv 64 (Z.of_nat p)) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9b59c) fc None m (seg_rom rsegs)).

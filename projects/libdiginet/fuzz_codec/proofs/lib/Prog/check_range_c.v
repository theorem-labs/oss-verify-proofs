From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** check_range (fuzz_codec.c:293-314; 80 bytes at 0x15194, frame 0x20, calls bcmp at 0x151bc). Called by
    LLVMFuzzerTestOneInput at 0x14814 with a0 = &k. It returns without calling abort when (rc <> 0 ->
    the 32 bytes of out, padding included, equal those of before) and rc = want_rc. *)
Definition CHECK_RANGE : Z := 0x15194.
Definition CHECK_RANGE_DEPTH : Z := 0x20.

Definition check_range_pre (sp a0 : word) (m : word -> option byte) (lo : Z) (k : kcall) : Prop :=
  cells_at rsegs m (bv_unsigned a0) (kcall_cells k) /\
  kcall_wf k /\
  bv_unsigned sp <= bv_unsigned a0 /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + CHECK_RANGE_DEPTH <= bv_unsigned sp /\
  (k_rc k <> 0 -> k_out k = k_before k) /\
  k_rc k = k_want_rc k.

Definition check_range_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (k : kcall),
    check_range_pre sp a0 m lo k ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_RANGE_DEPTH, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_RANGE) fc None m (seg_rom rsegs)).

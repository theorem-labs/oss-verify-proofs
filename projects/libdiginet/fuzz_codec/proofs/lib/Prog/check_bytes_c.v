From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** check_bytes (fuzz_codec.c:316-344; 88 bytes at 0x151e4, frame 0x10, calls bcmp at 0x15208). Called by
    LLVMFuzzerTestOneInput at 0x14824 (only when k.rc = 0) with a0 = &k. It compares out.len (lbu) with
    want_len (ld), out.bytes with want over out.len bytes, out.key with want_key (lw, lw) and out.display
    (lbu) with want_display (lw), and returns without calling abort when all four are equal. *)
Definition CHECK_BYTES : Z := 0x151e4.
Definition CHECK_BYTES_DEPTH : Z := 0x10.

Definition check_bytes_pre (sp a0 : word) (m : word -> option byte) (lo : Z) (k : kcall) : Prop :=
  cells_at rsegs m (bv_unsigned a0) (kcall_cells k) /\
  kcall_wf k /\
  bv_unsigned sp <= bv_unsigned a0 /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + CHECK_BYTES_DEPTH <= bv_unsigned sp /\
  k_want_len k = cmd_len (k_out k) /\
  k_want_len k <= 24 /\
  firstn (Z.to_nat (k_want_len k)) (k_out k) = firstn (Z.to_nat (k_want_len k)) (k_want k) /\
  cmd_key (k_out k) = k_want_key k /\
  cmd_display (k_out k) = k_want_display k.

Definition check_bytes_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (k : kcall),
    check_bytes_pre sp a0 m lo k ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_BYTES_DEPTH, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_BYTES) fc None m (seg_rom rsegs)).

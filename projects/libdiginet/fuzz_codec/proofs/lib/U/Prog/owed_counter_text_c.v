From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** owed_counter_text (fuzz_codec.c:402-429; 508 bytes at 0x150cc, frame 0x90, calls owed_seg7 at 0x15184).
    Called by check_text_counter at 0x15018 and LLVMFuzzerTestOneInput at 0x139e0. As in the plain image;
    writes t0, a0-a7 and its frame; its bounds, overflow and pointer traps do not fire. *)
Definition OWED_COUNTER_TEXT : Z := 0x150cc.
Definition OWED_COUNTER_TEXT_DEPTH : Z := 0x90.

Definition owed_counter_text_pre (sp a0 a1 a2 : word) (m : word -> option byte) (lo : Z) (tb sj : list byte) (dj : byte) : Prop :=
  bv_unsigned a0 <> 0 /\
  cstr m (bv_unsigned a0) tb /\
  bv_unsigned a1 <> 0 /\
  rw_cells rsegs m (bv_unsigned a1) [CB 8 sj] /\
  bv_unsigned a2 <> 0 /\
  rw_cells rsegs m (bv_unsigned a2) [C1 dj] /\
  disj (bv_unsigned a1) 8 (bv_unsigned a2) 1 /\
  relro_img m /\
  disj lo (bv_unsigned sp - lo) RELRO_BASE RELRO_LEN /\
  bv_unsigned sp <= bv_unsigned a0 /\
  bv_unsigned sp <= bv_unsigned a1 /\
  bv_unsigned sp <= bv_unsigned a2 /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + OWED_COUNTER_TEXT_DEPTH <= bv_unsigned sp.

Definition owed_counter_text_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (tb sj : list byte) (dj : byte),
    owed_counter_text_pre sp a0 a1 a2 m lo tb sj dj ->
    evt rsegs
      (fun ms' => exists (t0' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - OWED_COUNTER_TEXT_DEPTH, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 8); (bv_unsigned a2, bv_unsigned a2 + 1)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         let '(rc, sg, d) := owed_counter_text_spec (zb tb) in
         a0' = Z_to_bv 64 rc /\
         (rc = 0 -> rw_cells rsegs m' (bv_unsigned a1) [CB 8 (bz sg)] /\ rw_cells rsegs m' (bv_unsigned a2) [C1 (b8 d)]) /\
         (rc <> 0 -> exists sg' dv, rw_cells rsegs m' (bv_unsigned a1) [CB 8 sg'] /\ rw_cells rsegs m' (bv_unsigned a2) [C1 dv]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 OWED_COUNTER_TEXT) fc None m (seg_rom rsegs)).

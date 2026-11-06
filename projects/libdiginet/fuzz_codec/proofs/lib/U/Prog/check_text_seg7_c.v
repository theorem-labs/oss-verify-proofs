From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** check_text_seg7 (fuzz_codec.c:454-466; 120 bytes at 0x14f6c, frame 0x30). Called by
    LLVMFuzzerTestOneInput at 0x139bc. As in the plain image; writes t0, a0-a7 and its frame. *)
Definition CHECK_TEXT_SEG7 : Z := 0x14f6c.
Definition CHECK_TEXT_SEG7_DEPTH : Z := 0x30.

Definition check_text_seg7_pre (sp : word) (m : word -> option byte) (lo : Z) : Prop :=
  relro_img m /\
  disj lo (bv_unsigned sp - lo) RELRO_BASE RELRO_LEN /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + CHECK_TEXT_SEG7_DEPTH <= bv_unsigned sp /\
  (forall c, 0 <= c < 256 -> seg7_spec c = owed_seg7_spec c).

Definition check_text_seg7_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    check_text_seg7_pre sp m lo ->
    evt rsegs
      (fun ms' => exists (t0' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_TEXT_SEG7_DEPTH, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_TEXT_SEG7) fc None m (seg_rom rsegs)).

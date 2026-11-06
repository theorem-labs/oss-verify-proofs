From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** check_personality (fuzz_codec.c:256-281; 292 bytes at 0x149ec, frame 0x20; calls diginet_personality_of
    x3, strcmp x2, diginet_personality_from_name x5 (frame 0x30): depth 0x50). Called by
    LLVMFuzzerTestOneInput at 0x13274, no arguments. It returns without calling abort: everything it
    compares is image data, personalities[] in RELRO (relro_img) and five .rodata strings (mem_inv).
    Writes a0-a3 and the stack below sp. *)
Definition CHECK_PERSONALITY : Z := 0x149ec.
Definition CHECK_PERSONALITY_DEPTH : Z := 0x50.

Definition check_personality_pre (sp : word) (m : word -> option byte) (lo : Z) : Prop :=
  relro_img m /\
  disj lo (bv_unsigned sp - lo) RELRO_BASE RELRO_LEN /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + CHECK_PERSONALITY_DEPTH <= bv_unsigned sp.

Definition check_personality_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    check_personality_pre sp m lo ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_PERSONALITY_DEPTH, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_PERSONALITY) fc None m (seg_rom rsegs)).

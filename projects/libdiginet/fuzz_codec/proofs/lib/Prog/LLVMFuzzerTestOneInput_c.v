From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** LLVMFuzzerTestOneInput of fuzz_codec.c:556-658 (6084 bytes at 0x13228 in the plain image; frame 0x190,
    the deepest callee chain check_text_counter -> diginet_counter_text adds 0xc0: stack 0x250). The form of
    libreac/fuzz_knock's released knock_main_contract (its Prog/LLVMFuzzerTestOneInput_c.v), so the slot
    proof ports, with one more premise: relro_img, the image's bytes in the RELRO tables the function and
    its callees read (SPEC_DESK, SPEC_C24, SPEC_PC, GLYPH, personalities[]), which lie in a writable
    PT_LOAD and so are not given by mem_inv; the frame's G_img_c frame_RELRO supplies it. *)
Definition LLVM_CODEC : Z := 0x13228.
Definition LLVM_CODEC_STACK : Z := 0x250.

Definition codec_main_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (data : list byte),
    bytes_at rsegs m (bv_unsigned a0) data ->
    bv_unsigned a1 = Z.of_nat (length data) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + LLVM_CODEC_STACK <= bv_unsigned sp ->
    bv_unsigned sp mod 16 = 0 ->
    (bv_unsigned a0 + Z.of_nat (length data) <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    bv_unsigned a0 + Z.of_nat (length data) < 2 ^ 63 ->
    relro_img m ->
    disj lo (bv_unsigned sp - lo) RELRO_BASE RELRO_LEN ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - LLVM_CODEC_STACK, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 LLVM_CODEC) fc None m (seg_rom rsegs)).

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** diginet_personality_from_name (diginet_codec.c:17-25; 136 bytes at 0x1523c, frame 0x30, calls strcmp at
    0x15284). Called by check_personality (0x14ab0, 0x14ac0, 0x14ad0, 0x14ae0, 0x14af0) with a0 one of the
    .rodata strings "CNTRL|24", "MAINUNIT", "CNTRL|2", "MAINUNITS", "". It compares the C string at a0 with
    the announce names that personalities[0..1] point at (RELRO) and returns from_name_res; it writes a0-a3
    and its frame. *)
Definition DIGINET_PERSONALITY_FROM_NAME : Z := 0x1523c.
Definition DIGINET_PERSONALITY_FROM_NAME_DEPTH : Z := 0x30.

Definition diginet_personality_from_name_pre (sp a0 : word) (m : word -> option byte) (lo : Z) (tb : list byte) : Prop :=
  bv_unsigned a0 <> 0 /\
  cstr m (bv_unsigned a0) tb /\
  (bv_unsigned a0 + Z.of_nat (length tb) <= lo \/ bv_unsigned sp <= bv_unsigned a0) /\
  relro_img m /\
  disj lo (bv_unsigned sp - lo) RELRO_BASE RELRO_LEN /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + DIGINET_PERSONALITY_FROM_NAME_DEPTH <= bv_unsigned sp.

Definition diginet_personality_from_name_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (tb : list byte),
    diginet_personality_from_name_pre sp a0 m lo tb ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (from_name_res tb)) a1' a2' a3' a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - DIGINET_PERSONALITY_FROM_NAME_DEPTH, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_PERSONALITY_FROM_NAME) fc None m (seg_rom rsegs)).

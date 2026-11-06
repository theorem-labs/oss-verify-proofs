From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** diginet_counter_text (diginet_codec.c:337-369; 416 bytes at 0x15b24, frame 0x80, calls diginet_seg7 at
    0x15bcc). Called by check_text_counter at 0x14e00 with a0 = the text (a C string), a1 = seg (k.bytes),
    a2 = dots (one byte). Returns counter_text_spec's rc; on success seg[0..8) and *dots are its digits and
    dots; on failure it has written at most seg[0..8). Writes a0-a7 and its frame. *)
Definition DIGINET_COUNTER_TEXT : Z := 0x15b24.
Definition DIGINET_COUNTER_TEXT_DEPTH : Z := 0x80.

Definition diginet_counter_text_pre (sp a0 a1 a2 : word) (m : word -> option byte) (lo : Z) (tb sj : list byte) (dj : byte) : Prop :=
  bv_unsigned a0 <> 0 /\
  cstr m (bv_unsigned a0) tb /\
  bv_unsigned a1 <> 0 /\
  rw_cells rsegs m (bv_unsigned a1) [CB 8 sj] /\
  bv_unsigned a2 <> 0 /\
  rw_cells rsegs m (bv_unsigned a2) [C1 dj] /\
  disj (bv_unsigned a1) 8 (bv_unsigned a2) 1 /\
  bv_unsigned sp <= bv_unsigned a0 /\
  bv_unsigned sp <= bv_unsigned a1 /\
  bv_unsigned sp <= bv_unsigned a2 /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + DIGINET_COUNTER_TEXT_DEPTH <= bv_unsigned sp.

Definition diginet_counter_text_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (tb sj : list byte) (dj : byte),
    diginet_counter_text_pre sp a0 a1 a2 m lo tb sj dj ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - DIGINET_COUNTER_TEXT_DEPTH, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 8); (bv_unsigned a2, bv_unsigned a2 + 1)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         let '(rc, sg, d) := counter_text_spec (zb tb) in
         a0' = Z_to_bv 64 rc /\
         (rc = 0 -> rw_cells rsegs m' (bv_unsigned a1) [CB 8 (bz sg)] /\ rw_cells rsegs m' (bv_unsigned a2) [C1 (b8 d)]) /\
         (rc <> 0 -> exists sg' dv, rw_cells rsegs m' (bv_unsigned a1) [CB 8 sg'] /\ rw_cells rsegs m' (bv_unsigned a2) [C1 dv]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_COUNTER_TEXT) fc None m (seg_rom rsegs)).

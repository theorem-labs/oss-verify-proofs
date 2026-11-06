From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** check_text_counter (fuzz_codec.c:468-490; 208 bytes at 0x14da0, frame 0x40, fuzz_all inlined, cap = 24
    constant-propagated; calls owed_counter_text and diginet_counter_text (frames 0x80), memset, bcmp:
    depth 0xc0). Called by LLVMFuzzerTestOneInput at 0x1386c with three arguments: a0 = text, a1 = seg
    (&k.bytes, 24 bytes), a2 = &dots. It returns without calling abort when diginet_counter_text agrees
    with owed_counter_text on the text (rc, and on success the digits and the dots), and leaves
    seg[8..24) = 0xa5. *)
Definition CHECK_TEXT_COUNTER : Z := 0x14da0.
Definition CHECK_TEXT_COUNTER_DEPTH : Z := 0xc0.

Definition check_text_counter_pre (sp a0 a1 a2 : word) (m : word -> option byte) (lo : Z) (tb sj : list byte) (dj : byte) : Prop :=
  bv_unsigned a0 <> 0 /\
  cstr m (bv_unsigned a0) tb /\
  bv_unsigned a1 <> 0 /\
  rw_cells rsegs m (bv_unsigned a1) [CB 24 sj] /\
  bv_unsigned a2 <> 0 /\
  rw_cells rsegs m (bv_unsigned a2) [C1 dj] /\
  disj (bv_unsigned a1) 24 (bv_unsigned a2) 1 /\
  disj (bv_unsigned a0) (Z.of_nat (length tb)) (bv_unsigned a1) 24 /\
  disj (bv_unsigned a0) (Z.of_nat (length tb)) (bv_unsigned a2) 1 /\
  relro_img m /\
  disj lo (bv_unsigned sp - lo) RELRO_BASE RELRO_LEN /\
  bv_unsigned sp <= bv_unsigned a0 /\
  bv_unsigned sp <= bv_unsigned a1 /\
  bv_unsigned sp <= bv_unsigned a2 /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + CHECK_TEXT_COUNTER_DEPTH <= bv_unsigned sp /\
  (let '(r1, s1, d1) := counter_text_spec (zb tb) in
     let '(r2, s2, d2) := owed_counter_text_spec (zb tb) in
     r1 = r2 /\ (r1 = 0 -> s1 = s2 /\ d1 = d2)).

Definition check_text_counter_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (tb sj : list byte) (dj : byte),
    check_text_counter_pre sp a0 a1 a2 m lo tb sj dj ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_TEXT_COUNTER_DEPTH, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 24); (bv_unsigned a2, bv_unsigned a2 + 1)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         exists sg dv, rw_cells rsegs m' (bv_unsigned a1) [CB 8 sg; CB 16 (repeat (b8 0xa5) 16)] /\
           rw_cells rsegs m' (bv_unsigned a2) [C1 dv])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_TEXT_COUNTER) fc None m (seg_rom rsegs)).

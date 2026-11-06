From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** diginet_scribble_text (diginet_codec.c:267-285; 224 bytes at 0x15d70, leaf, no frame, inline pad loop).
    Called by check_text_scribble at 0x14ef0 (text, chars, n). Writes exactly out[0..n) and returns the
    text bytes used; writes t0-t5, a0-a1, a3-a7; its pointer-overflow traps do not fire. *)
Definition DIGINET_SCRIBBLE_TEXT : Z := 0x15d70.

Definition diginet_scribble_text_pre (a0 a1 a2 : word) (m : word -> option byte) (n : Z) (tb oj : list byte) : Prop :=
  bv_unsigned a0 <> 0 /\
  cstr m (bv_unsigned a0) tb /\
  bv_unsigned a1 <> 0 /\
  bv_unsigned a2 = n /\
  rw_cells rsegs m (bv_unsigned a1) [CB (Z.to_nat n) oj] /\
  disj (bv_unsigned a0) (Z.of_nat (length tb)) (bv_unsigned a1) n /\
  mem_inv rsegs m.

Definition diginet_scribble_text_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z) (tb oj : list byte),
    diginet_scribble_text_pre a0 a1 a2 m n tb oj ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' t3' t4' t5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2 a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned a1, bv_unsigned a1 + n)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         a0' = Z_to_bv 64 (snd (scribble_text_spec (zb tb) n)) /\
         rw_cells rsegs m' (bv_unsigned a1) [CB (Z.to_nat n) (bz (fst (scribble_text_spec (zb tb) n)))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_SCRIBBLE_TEXT) fc None m (seg_rom rsegs)).

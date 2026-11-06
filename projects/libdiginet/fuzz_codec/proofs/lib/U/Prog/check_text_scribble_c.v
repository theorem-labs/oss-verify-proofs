From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** check_text_scribble (fuzz_codec.c:431-452; 364 bytes at 0x14e00, frame 0x30, cap folded; calls memset,
    diginet_scribble_text (no frame), bcmp: depth 0x30). Called by LLVMFuzzerTestOneInput at 0x13d70
    (text, &k.bytes, k.desk->chars). Returns without calling abort under the agreement; its
    pointer-overflow traps do not fire. *)
Definition CHECK_TEXT_SCRIBBLE : Z := 0x14e00.
Definition CHECK_TEXT_SCRIBBLE_DEPTH : Z := 0x30.

Definition check_text_scribble_pre (sp a0 a1 a2 : word) (m : word -> option byte) (lo n : Z) (tb cj : list byte) : Prop :=
  bv_unsigned a0 <> 0 /\
  cstr m (bv_unsigned a0) tb /\
  rw_cells rsegs m (bv_unsigned a1) [CB 24 cj] /\
  disj (bv_unsigned a0) (Z.of_nat (length tb)) (bv_unsigned a1) 24 /\
  bv_unsigned a2 = n /\
  0 <= n <= 8 /\
  bv_unsigned sp <= bv_unsigned a0 /\
  bv_unsigned sp <= bv_unsigned a1 /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + CHECK_TEXT_SCRIBBLE_DEPTH <= bv_unsigned sp /\
  owed_scribble_text_spec (zb tb) n = scribble_text_spec (zb tb) n.

Definition check_text_scribble_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo n : Z) (tb cj : list byte),
    check_text_scribble_pre sp a0 a1 a2 m lo n tb cj ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_TEXT_SCRIBBLE_DEPTH, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 24)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (bv_unsigned a1) [CB 24 (bz (scribble_bytes (zb tb) n))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_TEXT_SCRIBBLE) fc None m (seg_rom rsegs)).

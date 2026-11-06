From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** text_arg (fuzz_codec.c:523-529; 212 bytes at 0x14b10, frame 0x20, fuzz_u16 and fuzz_take inlined, calls
    memcpy at 0x14bc4). Called by LLVMFuzzerTestOneInput at 0x13540 and 0x13854 with a0 = &in (struct
    fuzz_in {p@0; n@8}), a1 = text (char[65]). With data the n cursor bytes at p, it takes the u16
    length (text_hdr bytes), copies text_len bytes to text, puts the 0 after them, leaves text[len+1..65)
    as it was and advances the cursor by text_used. *)
Definition TEXT_ARG : Z := 0x14b10.
Definition TEXT_ARG_DEPTH : Z := 0x20.

Definition text_arg_pre (sp a0 a1 : word) (m : word -> option byte) (lo p : Z) (data tj : list byte) : Prop :=
  rw_cells rsegs m (bv_unsigned a0) [C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 (Z.of_nat (length data)))] /\
  bytes_at rsegs m p data /\
  rw_cells rsegs m (bv_unsigned a1) [CB 65 tj] /\
  disj (bv_unsigned a0) 16 (bv_unsigned a1) 65 /\
  disj p (Z.of_nat (length data)) (bv_unsigned a1) 65 /\
  disj p (Z.of_nat (length data)) (bv_unsigned a0) 16 /\
  bv_unsigned sp <= bv_unsigned a0 /\
  bv_unsigned sp <= bv_unsigned a1 /\
  (p + Z.of_nat (length data) <= lo \/ bv_unsigned sp <= p) /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + TEXT_ARG_DEPTH <= bv_unsigned sp.

Definition text_arg_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p : Z) (data tj : list byte),
    text_arg_pre sp a0 a1 m lo p data tj ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - TEXT_ARG_DEPTH, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 16); (bv_unsigned a1, bv_unsigned a1 + 65)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (bv_unsigned a0)
           [C8 (Z_to_bv 64 (p + Z.of_nat (text_used data))); C8 (Z_to_bv 64 (Z.of_nat (length data - text_used data)))] /\
         rw_cells rsegs m' (bv_unsigned a1) [CB 65 (text_taken data ++ [b8 0] ++ skipn (S (text_len data)) tj)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TEXT_ARG) fc None m (seg_rom rsegs)).

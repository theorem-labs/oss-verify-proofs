From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** diginet_ring_encode (diginet_codec.c:179-198; 284 bytes at 0x15624, sysex_encode inlined, no call;
    frame 0x10 from 0x15690). Called by LLVMFuzzerTestOneInput at 0x141ac with a0 = k.p, a1 = k.a,
    a2 = (uint16_t) k.b (lhu: zero-extended), a3 = &k.out. Writes t0-t4, a0-a2, a4-a7, its frame and, on
    success only, out. *)
Definition DIGINET_RING_ENCODE : Z := 0x15624.
Definition DIGINET_RING_ENCODE_DEPTH : Z := 0x10.

Definition diginet_ring_encode_pre (sp a0 a1 a2 a3 : word) (m : word -> option byte) (lo : Z) (pd : option desk) (strip mask : Z) (before : list byte) : Prop :=
  pers_arg m a0 pd /\
  arg_u32 a1 strip /\
  arg_zx 16 a2 mask /\
  bv_unsigned a3 <> 0 /\
  rw_cells rsegs m (bv_unsigned a3) [CB 32 before] /\
  bv_unsigned sp <= bv_unsigned a3 /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + DIGINET_RING_ENCODE_DEPTH <= bv_unsigned sp.

Definition diginet_ring_encode_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (pd : option desk) (strip mask : Z) (before : list byte),
    diginet_ring_encode_pre sp a0 a1 a2 a3 m lo pd strip mask before ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' t3' t4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3 a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - DIGINET_RING_ENCODE_DEPTH, bv_unsigned sp); (bv_unsigned a3, bv_unsigned a3 + 32)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         let '(rc, o) := ring_spec pd strip mask in
         a0' = Z_to_bv 64 rc /\ rw_cells rsegs m' (bv_unsigned a3) [CB 32 (cmd_out before o)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_RING_ENCODE) fc None m (seg_rom rsegs)).

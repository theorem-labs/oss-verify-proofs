From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** diginet_sysex_encode (diginet_codec.c:66-91; 336 bytes at 0x156b0, frame 0x30, calls memcpy at
    0x15798). Called by LLVMFuzzerTestOneInput (0x144c8), diginet_ring_encode (0x15b44), diginet_meter_encode
    (0x15c58), leds_encode (0x15d10), diginet_scribble_encode (0x15ee0) and diginet_counter_encode (0x161fc);
    device and fn zero-extended, the payload on the caller's stack. Its UBSan checks (payload and out pointer
    arithmetic, out alignment, bounds of out->bytes[4 + len]) hold under these premises. *)
Definition DIGINET_SYSEX_ENCODE : Z := 0x156b0.
Definition DIGINET_SYSEX_ENCODE_DEPTH : Z := 0x30.

Definition diginet_sysex_encode_pre (sp a0 a1 a2 a3 a4 : word) (m : word -> option byte) (lo : Z) (dev fn : Z) (pl before : list byte) : Prop :=
  arg_zx 8 a0 dev /\
  arg_zx 8 a1 fn /\
  bv_unsigned a2 <> 0 /\
  bytes_at rsegs m (bv_unsigned a2) pl /\
  bv_unsigned a3 = Z.of_nat (length pl) /\
  bv_unsigned a4 <> 0 /\
  rw_cells rsegs m (bv_unsigned a4) [CB 32 before] /\
  bv_unsigned a4 mod 4 = 0 /\
  disj (bv_unsigned a2) (Z.of_nat (length pl)) (bv_unsigned a4) 32 /\
  bv_unsigned sp <= bv_unsigned a2 /\
  bv_unsigned sp <= bv_unsigned a4 /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + DIGINET_SYSEX_ENCODE_DEPTH <= bv_unsigned sp.

Definition diginet_sysex_encode_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (dev fn : Z) (pl before : list byte),
    diginet_sysex_encode_pre sp a0 a1 a2 a3 a4 m lo dev fn pl before ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - DIGINET_SYSEX_ENCODE_DEPTH, bv_unsigned sp); (bv_unsigned a4, bv_unsigned a4 + 32)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         let '(rc, o) := sysex_spec dev fn (zb pl) in
         a0' = Z_to_bv 64 rc /\ rw_cells rsegs m' (bv_unsigned a4) [CB 32 (cmd_out before o)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_SYSEX_ENCODE) fc None m (seg_rom rsegs)).

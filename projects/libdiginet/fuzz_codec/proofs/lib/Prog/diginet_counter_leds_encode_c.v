From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** diginet_counter_leds_encode (diginet_codec.c:257-263; 140 bytes at 0x158f4, leds_encode and
    sysex_encode inlined, leaf, no frame). Called by LLVMFuzzerTestOneInput at 0x14358 with a0 = k.p,
    a1 = k.b, a2 = &k.out. Writes t0, a0-a1, a3-a7 and, on success only, out. *)
Definition DIGINET_COUNTER_LEDS_ENCODE : Z := 0x158f4.

Definition diginet_counter_leds_encode_pre (a0 a1 a2 : word) (m : word -> option byte) (pd : option desk) (bits : Z) (before : list byte) : Prop :=
  pers_arg m a0 pd /\
  arg_u32 a1 bits /\
  bv_unsigned a2 <> 0 /\
  rw_cells rsegs m (bv_unsigned a2) [CB 32 before] /\
  mem_inv rsegs m.

Definition diginet_counter_leds_encode_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pd : option desk) (bits : Z) (before : list byte),
    diginet_counter_leds_encode_pre a0 a1 a2 m pd bits before ->
    evt rsegs
      (fun ms' => exists (t0' a0' a1' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2 a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned a2, bv_unsigned a2 + 32)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         let '(rc, o) := counter_leds_spec pd bits in
         a0' = Z_to_bv 64 rc /\ rw_cells rsegs m' (bv_unsigned a2) [CB 32 (cmd_out before o)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_COUNTER_LEDS_ENCODE) fc None m (seg_rom rsegs)).

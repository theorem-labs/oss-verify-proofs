From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** leds_encode (diginet_codec.c:235-245; static, out of line in the UBSan image only: 128 bytes at
    0x15cc4, frame 0x20, calls diginet_sysex_encode at 0x15d10: depth 0x50). Reached by tail calls from
    diginet_strip_leds_encode (0x15cb0: a1 = strip < strips) and diginet_counter_leds_encode (0x15d60:
    a1 = lbu p->counter_addr), a0 = p non-NULL, a2 = bits (sign-extended u32), a3 = out. It has no NULL
    test, and stores the key addr | 0x50000 without the & 0xffff, hence addr < 2^16. *)
Definition LEDS_ENCODE : Z := 0x15cc4.
Definition LEDS_ENCODE_DEPTH : Z := 0x50.

Definition leds_encode_pre (sp a0 a1 a2 a3 : word) (m : word -> option byte) (lo : Z) (d : desk) (addr bits : Z) (before : list byte) : Prop :=
  pers_arg m a0 (Some d) /\
  disj (bv_unsigned a0 + 16) 4 (bv_unsigned sp - LEDS_ENCODE_DEPTH) LEDS_ENCODE_DEPTH /\
  0 <= addr < 2 ^ 16 /\
  a1 = Z_to_bv 64 addr /\
  arg_u32 a2 bits /\
  bv_unsigned a3 <> 0 /\
  rw_cells rsegs m (bv_unsigned a3) [CB 32 before] /\
  bv_unsigned a3 mod 4 = 0 /\
  bv_unsigned sp <= bv_unsigned a3 /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + LEDS_ENCODE_DEPTH <= bv_unsigned sp.

Definition leds_encode_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (d : desk) (addr bits : Z) (before : list byte),
    leds_encode_pre sp a0 a1 a2 a3 m lo d addr bits before ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - LEDS_ENCODE_DEPTH, bv_unsigned sp); (bv_unsigned a3, bv_unsigned a3 + 32)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         let '(rc, o) := leds_spec d addr bits in
         a0' = Z_to_bv 64 rc /\ rw_cells rsegs m' (bv_unsigned a3) [CB 32 (cmd_out before o)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 LEDS_ENCODE) fc None m (seg_rom rsegs)).

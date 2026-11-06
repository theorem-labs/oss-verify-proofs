From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** diginet_sysex_encode (diginet_codec.c:66-91; 280 bytes at 0x152f0, frame 0x30, calls memcpy at
    0x153a8). Called by LLVMFuzzerTestOneInput (0x13a68: a0 = (u8) k.a, a1 = (u8) k.b, a2 = &k.bytes,
    a3 = k.n <= 24, a4 = &k.out) and diginet_scribble_encode (0x15ac4: a0 = p->device, a1 = 0x40, a2 = its
    pl, a3 = 2 + p->scribble_chars). device and fn arrive zero-extended (fn is compared with 0x70 on all
    64 bits). Every failing return precedes the first store to out, so out is unchanged on failure. *)
Definition DIGINET_SYSEX_ENCODE : Z := 0x152f0.
Definition DIGINET_SYSEX_ENCODE_DEPTH : Z := 0x30.

Definition diginet_sysex_encode_pre (sp a0 a1 a2 a3 a4 : word) (m : word -> option byte) (lo : Z) (dev fn : Z) (pl before : list byte) : Prop :=
  arg_zx 8 a0 dev /\
  arg_zx 8 a1 fn /\
  bv_unsigned a2 <> 0 /\
  bytes_at rsegs m (bv_unsigned a2) pl /\
  bv_unsigned a3 = Z.of_nat (length pl) /\
  bv_unsigned a4 <> 0 /\
  rw_cells rsegs m (bv_unsigned a4) [CB 32 before] /\
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

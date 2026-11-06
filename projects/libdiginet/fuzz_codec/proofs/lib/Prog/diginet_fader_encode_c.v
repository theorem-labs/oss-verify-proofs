From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** diginet_fader_encode (diginet_codec.c:95-111; 104 bytes at 0x15408, leaf, no frame). Called by
    LLVMFuzzerTestOneInput at 0x14050 with a0 = k.p, a1 = k.a, a2 = k.b (lw: sign-extended u32),
    a3 = &k.out. Writes a0-a2, a4-a6 and, on success only, out. *)
Definition DIGINET_FADER_ENCODE : Z := 0x15408.

Definition diginet_fader_encode_pre (a0 a1 a2 a3 : word) (m : word -> option byte) (pd : option desk) (strip value : Z) (before : list byte) : Prop :=
  pers_arg m a0 pd /\
  arg_u32 a1 strip /\
  arg_u32 a2 value /\
  bv_unsigned a3 <> 0 /\
  rw_cells rsegs m (bv_unsigned a3) [CB 32 before] /\
  mem_inv rsegs m.

Definition diginet_fader_encode_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pd : option desk) (strip value : Z) (before : list byte),
    diginet_fader_encode_pre a0 a1 a2 a3 m pd strip value before ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4' a5' a6' a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned a3, bv_unsigned a3 + 32)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         let '(rc, o) := fader_spec pd strip value in
         a0' = Z_to_bv 64 rc /\ rw_cells rsegs m' (bv_unsigned a3) [CB 32 (cmd_out before o)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_FADER_ENCODE) fc None m (seg_rom rsegs)).

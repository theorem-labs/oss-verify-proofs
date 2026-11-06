From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** diginet_button_encode (diginet_codec.c:113-122; 108 bytes at 0x15884, leaf, no frame). Called by
    LLVMFuzzerTestOneInput at 0x14464 (k.a, k.b, (int) k.c, &k.out). Writes a0-a2, a4-a6 and, on success
    only, out. *)
Definition DIGINET_BUTTON_ENCODE : Z := 0x15884.

Definition diginet_button_encode_pre (a0 a1 a2 a3 : word) (m : word -> option byte) (button id on : Z) (before : list byte) : Prop :=
  arg_u32 a0 button /\
  arg_u32 a1 id /\
  arg_s32 a2 on /\
  bv_unsigned a3 <> 0 /\
  rw_cells rsegs m (bv_unsigned a3) [CB 32 before] /\
  bv_unsigned a3 mod 4 = 0 /\
  mem_inv rsegs m.

Definition diginet_button_encode_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (button id on : Z) (before : list byte),
    diginet_button_encode_pre a0 a1 a2 a3 m button id on before ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4' a5' a6' a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned a3, bv_unsigned a3 + 32)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         let '(rc, o) := button_spec button id on in
         a0' = Z_to_bv 64 rc /\ rw_cells rsegs m' (bv_unsigned a3) [CB 32 (cmd_out before o)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_BUTTON_ENCODE) fc None m (seg_rom rsegs)).

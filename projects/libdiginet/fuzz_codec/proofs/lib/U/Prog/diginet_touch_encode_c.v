From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** diginet_touch_encode (diginet_codec.c:124-134; 148 bytes at 0x158f0, leaf, no frame). Called by
    LLVMFuzzerTestOneInput at 0x1441c (k.p, k.a, (int) k.c, &k.out). Writes a0-a2, a4-a5 and out; the
    failing store path (0x15910 -> 0x15978) is excluded by d_strips <= 64. *)
Definition DIGINET_TOUCH_ENCODE : Z := 0x158f0.

Definition diginet_touch_encode_pre (a0 a1 a2 a3 : word) (m : word -> option byte) (pd : option desk) (strip on : Z) (before : list byte) : Prop :=
  pers_arg m a0 pd /\
  (forall d, pd = Some d -> d_strips d <= 64) /\
  arg_u32 a1 strip /\
  arg_s32 a2 on /\
  bv_unsigned a3 <> 0 /\
  rw_cells rsegs m (bv_unsigned a3) [CB 32 before] /\
  bv_unsigned a3 mod 4 = 0 /\
  mem_inv rsegs m.

Definition diginet_touch_encode_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pd : option desk) (strip on : Z) (before : list byte),
    diginet_touch_encode_pre a0 a1 a2 a3 m pd strip on before ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a4' a5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4' a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned a3, bv_unsigned a3 + 32)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         let '(rc, o) := touch_spec pd strip on in
         a0' = Z_to_bv 64 rc /\ rw_cells rsegs m' (bv_unsigned a3) [CB 32 (cmd_out before o)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_TOUCH_ENCODE) fc None m (seg_rom rsegs)).

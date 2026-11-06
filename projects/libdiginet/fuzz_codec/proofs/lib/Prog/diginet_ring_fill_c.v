From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** diginet_ring_fill (diginet_codec.c:174-177; 36 bytes at 0x15600, leaf, no memory access). Called by
    check_text_masks at 0x15098 with a0 = n sign-extended from 32 bits. Returns ring_fill_spec n;
    writes a0-a2. *)
Definition DIGINET_RING_FILL : Z := 0x15600.

Definition diginet_ring_fill_pre (a0 : word) (m : word -> option byte) (n : Z) : Prop :=
  arg_u32 a0 n.

Definition diginet_ring_fill_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
    diginet_ring_fill_pre a0 m n ->
    evt rsegs
      (fun ms' => exists (a1' a2' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ring_fill_spec n)) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_RING_FILL) fc None m (seg_rom rsegs)).

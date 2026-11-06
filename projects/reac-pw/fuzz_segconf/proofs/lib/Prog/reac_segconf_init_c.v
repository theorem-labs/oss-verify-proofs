From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** reac_segconf_init(c) (reac_segconf.c:19-22; 16 bytes, 4 instructions at 0x14cac in the image 3776ca44d75c):
    `lui a1,4; addiw a2,a1,0xe8; mv a1,zero; j memset`: memset(c, 0, 16616) as a tail call, so it
    returns from memset to the caller's ra with a0 = c (memset_c.v's post keeps a0). It uses no stack.

    Post in the spine's terms: the 16616 bytes at c are zero, which encode SegModel.rconf0 (seg_spec.rconf_enc_zero).
    It writes exactly [c, c + 16616).

    Callee contract its walk takes as a premise: memset_contract (Prog/memset_c.v, MEMSET = 0x1e930).

    Call site (LLVMFuzzerTestOneInput): 0x138c4 `jal reac_segconf_init` with a0 = c = malloc(16616)'s result:
    nonzero and 16-aligned (malloc_ret), its 16616 bytes present and writable
    (the frame's blocks_writable), the block below alloc_ceiling <= lo = S - 65536, so apart from the stack region. *)
Definition REAC_SEGCONF_INIT : Z := 0x14cac.

Definition reac_segconf_init_pre (m : word -> option byte) (sp lo c : Z) : Prop :=
  c <> 0 /\ c mod 16 = 0 /\ (exists junk, rw_cells rsegs m c [CB (Z.to_nat SEG_C_SIZE) junk]) /\
  stack_ok rsegs m lo sp 0 /\ apart c SEG_C_SIZE lo sp /\ mem_inv rsegs m.

Definition reac_segconf_init_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    reac_segconf_init_pre m (bv_unsigned sp) lo (bv_unsigned a0) ->
    evt rsegs
      (ret_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         (bv_unsigned a0)
         m
         ([(bv_unsigned a0, bv_unsigned a0 + SEG_C_SIZE)])
         lo
         (fun m' => bytes_at rsegs m' (bv_unsigned a0) (repeat ZERO (Z.to_nat SEG_C_SIZE)) /\
                   rconf_at rsegs m' (bv_unsigned a0) rconf0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_SEGCONF_INIT) fc None m (seg_rom rsegs)).

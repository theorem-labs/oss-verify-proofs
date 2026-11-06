From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** check_segments (fuzz_segconf.c:392-400, 407-429; at 0x14788 in the image 3776ca44d75c; frame 48 bytes).
    segments_are(c, m) || !returned aborts: c->n (`lw` c + 0x2c80) = m->n (m + 0x2000), c->overflow (c + 0x34d0) =
    m->overflow (m + 0x2004), strcmp(c->seg[i].name, m->seg[i].name) = 0 for i < n, then returned <> 0 (`beqz a2`,
    the full register).

    The premise is exactly the spine's condition under which the check does not abort, on the encodings of its
    arguments; the abort branch (`jal abort`) is then dead. Post: it returns with no byte changed outside its frame
    and its callees' frames below sp. That is SegModel.check_segments rc mc ret = true.

    Callee contracts its walk takes as premises: strcmp_contract (Prog/strcmp_c.v, 0x1ebf8).

    Call site (LLVMFuzzerTestOneInput): 0x13aec `jal check_segments` with a0 = c, a1 = m (the two blocks, holding the states after the files and
    m_cross), a2 = returned (the AND of `parse_file(..) == m->n` over the files: 0 or 1). *)
Definition CHECK_SEGMENTS : Z := 0x14788.
Definition CHECK_SEGMENTS_STACK : Z := 48.

Definition check_segments_pre (m : word -> option byte) (sp lo c mm retv : Z) (rc : rconf) (mc : mconf) (ret : bool)
    : Prop :=
  c <> 0 /\ c mod 16 = 0 /\ rconf_at rsegs m c rc /\ apart c SEG_C_SIZE lo sp /\
  mm <> 0 /\ mm mod 16 = 0 /\ mconf_at rsegs m mm mc /\ apart mm SEG_M_SIZE lo sp /\
  retv = b2z ret /\ check_segments rc mc ret = true /\
  stack_ok rsegs m lo sp CHECK_SEGMENTS_STACK /\ mem_inv rsegs m.

Definition check_segments_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (rc : rconf) (mc : mconf) (ret : bool),
    check_segments_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) rc mc ret ->
    evt rsegs
      (ret_void rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         m
         ([(bv_unsigned sp - CHECK_SEGMENTS_STACK, bv_unsigned sp)])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_SEGMENTS) fc None m (seg_rom rsegs)).

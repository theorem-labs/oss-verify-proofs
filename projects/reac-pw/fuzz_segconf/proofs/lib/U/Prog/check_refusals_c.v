From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** check_refusals (fuzz_segconf.c:516-529; at 0x14bf8 in the UBSan image 1696d6c34ffd; no frame on the path that returns (the 16-byte frame is set up only on the abort path, which the
    premise makes dead)).
    c->refused (c + 0x34cc) <> m->refused (m + 0x2008) or c->n_refusals (c + 0x34c8) <> m->n_kept (m + 0x23ac)
    aborts (`lw` both, compared as sign-extended 32-bit values).
    UBSan: every check traps to the function's own `unimp`; the alignment, bounds and no-wrap facts of the premise
    (pointers 16- or 4-aligned, n <= 32, the objects inside the address space) make each trap branch fall through.

    The premise is exactly the spine's condition under which the check does not abort, on the encodings of its
    arguments; the abort branch (`jal abort`) is then dead. Post: it returns with no byte changed outside its frame
    and its callees' frames below sp. That is SegModel.check_refusals rc mc = true.

    Callee contracts its walk takes as premises: none.

    Call site (LLVMFuzzerTestOneInput): 0x13d0c `jal check_refusals` with a0 = c, a1 = m. *)
Definition CHECK_REFUSALS : Z := 0x14bf8.
Definition CHECK_REFUSALS_STACK : Z := 0.

Definition check_refusals_pre (m : word -> option byte) (sp lo c mm : Z) (rc : rconf) (mc : mconf) : Prop :=
  c <> 0 /\ c mod 16 = 0 /\ rconf_at rsegs m c rc /\ apart c SEG_C_SIZE lo sp /\
  mm <> 0 /\ mm mod 16 = 0 /\ mconf_at rsegs m mm mc /\ apart mm SEG_M_SIZE lo sp /\
  check_refusals rc mc = true /\
  stack_ok rsegs m lo sp CHECK_REFUSALS_STACK /\ mem_inv rsegs m.

Definition check_refusals_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (rc : rconf) (mc : mconf),
    check_refusals_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) rc mc ->
    evt rsegs
      (ret_void rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         m
         ([])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_REFUSALS) fc None m (seg_rom rsegs)).

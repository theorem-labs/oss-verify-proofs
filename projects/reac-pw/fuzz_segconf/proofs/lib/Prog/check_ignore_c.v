From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** check_ignore (fuzz_segconf.c:470-483; at 0x14888 in the image 3776ca44d75c; no frame on the path that returns (the 16-byte frame is set up only on the abort path, which the
    premise makes dead)).
    got (a0) <> want->ignore (`lw 0x18`, compared as full registers) aborts.

    The premise is exactly the spine's condition under which the check does not abort, on the encodings of its
    arguments; the abort branch (`jal abort`) is then dead. Post: it returns with no byte changed outside its frame
    and its callees' frames below sp. With b the reader's answer (SegModel.r_ignored), the premise is check_seg's third conjunct:
    Bool.eqb b (ms_ignore g) = true.

    Callee contracts its walk takes as premises: none.

    Call site (LLVMFuzzerTestOneInput): 0x13b48 `jal check_ignore` with a0 = reac_segconf_ignored's result (0 or 1), a1 = g = &m->seg[i]. *)
Definition CHECK_IGNORE : Z := 0x14888.
Definition CHECK_IGNORE_STACK : Z := 0.

Definition check_ignore_pre (m : word -> option byte) (sp lo got want : Z) (b : bool) (g : mseg) : Prop :=
  want mod 4 = 0 /\ mseg_at rsegs m want g /\ apart want MSEG_SIZE lo sp /\
  got = b2z b /\ Bool.eqb b (ms_ignore g) = true /\
  stack_ok rsegs m lo sp CHECK_IGNORE_STACK /\ mem_inv rsegs m.

Definition check_ignore_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (b : bool) (g : mseg),
    check_ignore_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) b g ->
    evt rsegs
      (ret_void rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         m
         ([])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_IGNORE) fc None m (seg_rom rsegs)).

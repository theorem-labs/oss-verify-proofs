From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_find_c reac_segconf_role_c.
Import ListNotations.
Open Scope Z_scope.

(** check_absent (fuzz_segconf.c:544-554; at 0x14d9c in the UBSan image 1696d6c34ffd; frame 32 bytes).
    reac_segconf_find(c, name), reac_segconf_role(c, name, NULL), reac_segconf_ignored(c, name) or
    reac_segconf_model(c, name) nonzero aborts (each tested in that order, `bnez a0`).
    UBSan: every check traps to the function's own `unimp`; the alignment, bounds and no-wrap facts of the premise
    (pointers 16- or 4-aligned, n <= 32, the objects inside the address space) make each trap branch fall through.

    The premise is exactly the spine's condition under which the check does not abort, on the encodings of its
    arguments; the abort branch (`jal abort`) is then dead. Post: it returns with no byte changed outside its frame
    and its callees' frames below sp. That is SegModel.absent rc nm = true.

    Callee contracts its walk takes as premises: reac_segconf_find_contract, reac_segconf_role_contract, reac_segconf_ignored_contract,
    reac_segconf_model_contract (this directory).

    Call site (LLVMFuzzerTestOneInput): 0x13e30 and 0x13e68 `jal check_absent` with a0 = c, a1 = the probe (snprintf "%sx" of m->seg[i].name into main's
    probe[18]) when m_find(m, probe) = NULL, and then "nosuch0" (seg_spec.STR_NOSUCH) when m_find of it is NULL. *)
Definition CHECK_ABSENT : Z := 0x14d9c.
Definition CHECK_ABSENT_STACK : Z := 32 + ROLE_STACK.

Definition check_absent_pre (m : word -> option byte) (sp lo c name : Z) (rc : rconf) (nm : list Z) : Prop :=
  query_pre CHECK_ABSENT_STACK m sp lo c name rc nm /\ absent rc nm = true.

Definition check_absent_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (rc : rconf) (nm : list Z),
    check_absent_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) rc nm ->
    evt rsegs
      (ret_void rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         m
         ([(bv_unsigned sp - CHECK_ABSENT_STACK, bv_unsigned sp)])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ABSENT) fc None m (seg_rom rsegs)).

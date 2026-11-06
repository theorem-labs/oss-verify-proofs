From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import reac_segconf_find_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_segconf_role_file(c, name) (reac_segconf.c:543-547; at 0x15904 in the image 3776ca44d75c; frame 16 bytes, saves ra):
    s = find(c, name); NULL when s is NULL, when s->role_set = 0 (`lw 0x14`) or when s->role_file[0] = 0
    (`lbu 0xa0`); else s + 0xa0.
    It writes its frame [sp - 16, sp) and find's below it: [sp - 16 - FIND_STACK, sp).

    Post in the spine's terms: a0 = seg_spec.role_file_ptr c rc nm: &c->seg[i].role_file when SegModel.r_role_file rc nm = Some _, else 0.

    Callee contract its walk takes as a premise: reac_segconf_find_contract (reac_segconf_find_c.v, REAC_SEGCONF_FIND).

    Call sites: LLVMFuzzerTestOneInput 0x13b54 (c, g->name with g = &m->seg[i], i < m->n). The premise is
    reac_segconf_find_c.query_pre with the depth of this frame plus find's. *)
Definition REAC_SEGCONF_ROLE_FILE : Z := 0x15904.
Definition ROLE_FILE_STACK : Z := 16 + FIND_STACK.

Definition reac_segconf_role_file_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (rc : rconf) (nm : list Z),
    query_pre ROLE_FILE_STACK m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) rc nm ->
    evt rsegs
      (ret_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         (role_file_ptr (bv_unsigned a0) rc nm)
         m
         ([(bv_unsigned sp - ROLE_FILE_STACK, bv_unsigned sp)])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_SEGCONF_ROLE_FILE) fc None m (seg_rom rsegs)).

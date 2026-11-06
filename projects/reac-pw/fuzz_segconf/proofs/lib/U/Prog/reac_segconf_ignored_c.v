From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_find_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_segconf_ignored(c, name) (reac_segconf.c:527-531; at 0x160b4 in the UBSan image 1696d6c34ffd; frame 16 bytes, saves ra):
    s = find(c, name); `beqz a0`; `lw a0,0x18(a0); snez a0`: 1 when s is found and s->ignore <> 0, else 0.
    The UBSan check traps on s & 3 <> 0: s = c + 356 i with c 16-aligned rules it out.
    It writes its frame [sp - 16, sp) and find's below it: [sp - 16 - FIND_STACK, sp).

    Post in the spine's terms: a0 = b2z (SegModel.r_ignored rc nm) (the ignore field holds 0 or 1: flag_enc).

    Callee contract its walk takes as a premise: reac_segconf_find_contract (reac_segconf_find_c.v, REAC_SEGCONF_FIND).

    Call sites: LLVMFuzzerTestOneInput 0x13cb8 (c, g->name with g = &m->seg[i], i < m->n); check_absent 0x14dd8 (c, the probe). The premise is
    reac_segconf_find_c.query_pre with the depth of this frame plus find's. *)
Definition REAC_SEGCONF_IGNORED : Z := 0x160b4.
Definition IGNORED_STACK : Z := 16 + FIND_STACK.

Definition reac_segconf_ignored_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (rc : rconf) (nm : list Z),
    query_pre IGNORED_STACK m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) rc nm ->
    evt rsegs
      (ret_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         (b2z (r_ignored rc nm))
         m
         ([(bv_unsigned sp - IGNORED_STACK, bv_unsigned sp)])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_SEGCONF_IGNORED) fc None m (seg_rom rsegs)).

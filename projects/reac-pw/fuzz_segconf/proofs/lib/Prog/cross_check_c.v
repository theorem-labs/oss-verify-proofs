From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import refuse_c.
Import ListNotations.
Open Scope Z_scope.

(** cross_check(c) (reac_segconf.c:303-325, static; at 0x15738 in the image 3776ca44d75c; frame 0x40): for i < c->n (`lw` c + 0x2c80,
    reloaded each pass), s = &c->seg[i]: model_set and not (role_set and role = BOX) -> refuse(c, 0, F_xmodel, s->name,
    s->model), `sb zero` s->model[0], model_set = 0; else BOX without model_set -> refuse(c, 0, F_xbox, s->name),
    role = AUTO, role_set = 0.

    Post in the spine's terms: c holds SegModel.cross_check rc. It writes its frame and refuse's below it, the seg
    entries (model[0], model_set, role, role_set) and, through refuse, refusal[], n_refusals, refused.

    Callee contract its walk takes as a premise: refuse_contract (refuse_c.v, REFUSE; line 0, the formats at 0x10474
    and 0x106b5, the string arguments s->name and s->model in the c block, apart from the refusal slots).

    Call site: reac_segconf_parse 0x1571c (c, after reac_segconf_parse_file of the last file). *)
Definition CROSS_CHECK : Z := 0x15738.
Definition CROSS_CHECK_STACK : Z := 0x40 + REFUSE_STACK.

Definition cross_check_pre (m : word -> option byte) (fc : bv 32) (sp lo c : Z) (rc : rconf) : Prop :=
  c <> 0 /\ c mod 16 = 0 /\ rconf_at rsegs m c rc /\ apart c SEG_C_SIZE lo sp /\ blk_noimg rsegs c SEG_C_SIZE /\
  rc_refused rc + 64 < 2 ^ 32 /\
  printf_env m fc lo sp /\ stack_ok rsegs m lo sp CROSS_CHECK_STACK /\ mem_inv rsegs m.

Definition cross_check_W (sp c : Z) : list ivl :=
  [(sp - CROSS_CHECK_STACK, sp); (c, c + RSEG_SIZE * 32); (c + RC_REFUSAL, c + RC_OVERFLOW)].

Definition cross_check_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (rc : rconf),
    cross_check_pre m fc (bv_unsigned sp) lo (bv_unsigned a0) rc ->
    evt rsegs
      (ret_void_fp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
         m
         (cross_check_W (bv_unsigned sp) (bv_unsigned a0))
         lo
         (fun m' => rconf_at rsegs m' (bv_unsigned a0) (cross_check rc)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CROSS_CHECK) fc None m (seg_rom rsegs)).

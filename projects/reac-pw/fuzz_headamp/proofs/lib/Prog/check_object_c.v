From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(** check_object(rc, res, x) (fuzz_headamp.c:221-237; 68 bytes, 17 instructions at 0x1473c in the plain image):
      0x1473c lw a2,0(a2); addi a3,a0,1; seqz a3,a3; sltiu a2,a2,-1; beq a3,a2,0x14774;
              addi a2,zero,-1; bne a0,a2,0x14770; lw a0,0(a1); bnez a0,0x14774; lw a0,4(a1); bnez a0,0x14774;
              lw a0,8(a1); bnez a0,0x14774;
      0x14770 ret;
      0x14774 addi sp,sp,-16; sd ra,8(sp); jal abort (0x15e64).
    a3 = (rc = -1) on the 64-bit rc, a2 = (x->rc <> -1) on the sign-extended 32-bit x->rc; `beq` aborts when they are
    equal, i.e. when (rc = -1) <> (x->rc = -1); for rc = -1 the three words of res (n, keys, refusal) must be 0
    (REFUSE_NONE = 0). It returns exactly when the C condition of :234-235 is false, which the premises state on the
    four bytes of x->rc and, for rc = -1, the twelve bytes of res. On that path it writes a0 (rc = -1 only), a2, a3,
    stores nothing and uses no stack (only the abort path has a frame).

    Call site (LLVMFuzzerTestOneInput, plain): 0x14118 `jal check_object` (the only one), reached when pp->corrupt = 0
    (0x140e8 `lw a0,4(s8)`, 0x140ec `bnez a0` not taken), after expect_of (0x140f0-0x14108: memset(x, 0, 0x88) at
    0x140fc, then the pair loop) stored x->rc at 0x14108 `sw s0,0x90(sp)`, with sp = S - 560 and
      a0 = s6 = rc (0x14114; 0x140c0 `mv s6,a0` after reac_headamp_prop_parse_result at 0x140bc);
      a1 = sp + 0x150 = &res (0x1410c); a2 = sp + 0x90 = &x (0x14110).
    Why the premises hold there: M03's walk shows x = x_bytes (expect_model null cap r) (Spec/HeadBytes.v) for the
    record r in the pp block; the pod block is buf r and corrupt r = false, so parse_props (if null then None else
    Some (buf r)) cap = expect_model null cap r (Pod/Headamp.v's parse_props_build), whence rc = x->rc; and for
    rc = -1 answer_ok (parse_props_total) gives n = keys = refusal = 0, the res the parse contract stored:
    Prog/HeadSites.v [site_object]. *)
Definition CHECK_OBJECT : Z := 0x1473c.

Definition check_object_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rc xrc : Z),
    a0 = Z_to_bv 64 rc -> - 2 ^ 31 <= rc < 2 ^ 31 ->
    bytes_at rsegs m (bv_unsigned a2) (le4 (Z_to_bv 64 xrc)) -> - 2 ^ 31 <= xrc < 2 ^ 31 ->
    (rc = -1 <-> xrc = -1) ->
    (rc = -1 -> bytes_at rsegs m (bv_unsigned a1) (ha_res_bytes 0 0 0)) ->
    evt rsegs
      (fun ms' => exists a0' a2' a3' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2' a3' a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_OBJECT) fc None m (seg_rom rsegs)).

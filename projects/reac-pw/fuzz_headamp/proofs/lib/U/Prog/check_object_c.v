From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(** check_object(rc, res, x) (fuzz_headamp.c:221-237; 88 bytes, 22 instructions at 0x1498c in the UBSan image):
      0x1498c andi a3,a2,3; bnez a3,0x149e0; lw a2,0(a2); addi a3,a0,1; seqz a3,a3; sltiu a2,a2,-1;
              beq a3,a2,0x149d4; addi a2,zero,-1; bne a0,a2,0x149d0; andi a0,a1,3; bnez a0,0x149e0;
              lw a0,0(a1); bnez a0,0x149d4; lw a0,4(a1); bnez a0,0x149d4; lw a0,8(a1); bnez a0,0x149d4;
      0x149d0 ret;
      0x149d4 addi sp,sp,-16; sd ra,8(sp); jal abort (0x16364); 0x149e0 unimp.
    The plain text (lib/Prog/check_object_c.v) with two UBSan alignment checks, x & 3 before the x->rc load and
    res & 3 before the res loads (rc = -1 only), both to the trap 0x149e0: discharged by the premises x mod 4 = 0
    and (rc = -1 ->) res mod 4 = 0. On the path that returns it writes a0 (rc = -1 only), a2, a3, stores nothing and
    uses no stack.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x14790 `jal check_object` (the only one), reached when
    pp->corrupt = 0 (0x1418c `ld a0,0x68(sp)`, 0x14190 `lw a0,4(a0)`, 0x14194 `bnez a0` not taken), after
    expect_of (memset(x, 0, 0x88) at 0x141a4, the pair loop) stored x->rc at 0x14780 `sw s9,0xb8(sp)`, with
    sp = S - 608 and
      a0 = s6 = rc (0x1478c), a1 = sp + 0x178 = &res (0x14784), a2 = sp + 0xb8 = &x (0x14788).
    Why the premises hold there: as in the plain file (x = x_bytes (expect_model null cap r), parse_props_build,
    answer_ok); both addresses are sp + a multiple of 4 and S mod 16 = 0: U/Prog/HeadSites.v [site_object]. *)
Definition CHECK_OBJECT : Z := 0x1498c.

Definition check_object_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rc xrc : Z),
    a0 = Z_to_bv 64 rc -> - 2 ^ 31 <= rc < 2 ^ 31 ->
    bv_unsigned a2 mod 4 = 0 ->
    bytes_at rsegs m (bv_unsigned a2) (le4 (Z_to_bv 64 xrc)) -> - 2 ^ 31 <= xrc < 2 ^ 31 ->
    (rc = -1 <-> xrc = -1) ->
    (rc = -1 -> bv_unsigned a1 mod 4 = 0 /\ bytes_at rsegs m (bv_unsigned a1) (ha_res_bytes 0 0 0)) ->
    evt rsegs
      (fun ms' => exists a0' a2' a3' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2' a3' a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_OBJECT) fc None m (seg_rom rsegs)).

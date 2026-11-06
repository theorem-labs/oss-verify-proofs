From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** reac_role_refuse_code(r) (reac_role_cfg.c:14-20; 60 bytes, 15 instructions at 0x145e4 in the UBSan image):
      0x145e4 addi a1,zero,1; bgeu a1,a0,0x145f8;
              auipc a0,0xffffc; addi a0,a0,-0x20c (a0 = 0x145ec - 0x4000 - 0x20c = 0x103e0 = codes[0]); ret;
      0x145f8 slli a2,a0,3; auipc a1,0xa; addi a1,a1,-0x404 (a1 = 0x145fc + 0xa000 - 0x404 = 0x1e1f8); not a3,a1;
              bltu a3,a2,0x1461c; slli a0,a0,3; add a0,a1,a0; ld a0,0(a0); ret;
      0x1461c unimp (the pointer-overflow trap of codes + r).
    Unlike the plain image, codes[] stays an absolute pointer table: REFUSE_TBL = 0x1e1f8 in .data.rel.ro (the rw-
    segment at 0x1e0f0, under PT_GNU_RELRO [0x1e0f0, 0x1f000)) holds the two 8-byte pointers 0x103e0 ("none",
    CODE_NONE) and 0x103d6 ("malformed", CODE_MALFORMED), both strings in .rodata at the plain image's addresses.
    Total: for a0 <= 1 as a 64-bit unsigned word (the bgeu; the source's `(unsigned)r >= 2` on the sign-extended
    int) it returns the 8 bytes at REFUSE_TBL + 8 a0 (ld), else codes[0] directly. On the table path the trap branch
    tests ~REFUSE_TBL <u 8 a0; with 8 a0 <= 8 and ~REFUSE_TBL = 2^64 - 1 - 0x1e1f8 it is never taken, so the
    contract needs no premise for it. It writes a0 and a1 (1, or REFUSE_TBL on the table path) and, on the table
    path, a2 (8 a0) and a3 (~REFUSE_TBL); it stores nothing and uses no stack. It reads only the 8-byte entry at
    REFUSE_TBL + 8 a0. That segment is writable, so mem_inv does not fix those bytes: hence the table premise (the
    16 table bytes read as the image's).

    Call sites (LLVMFuzzerTestOneInput, UBSan), reached on every run past the size check and both mallocs, right
    after check_answer (0x14190):
      0x14198 `jal reac_role_refuse_code` with a0 = 0 (0x14194 `mv a0,zero`); the result goes to s2 (0x1419c
              `mv s2,a0`) and on to check_code's a0 (0x141ac `mv a0,s2`);
      0x141a4 `jal reac_role_refuse_code` with a0 = 1 (0x141a0 `addi a0,zero,1`); the result goes to check_code's a1
              (0x141a8 `mv a1,a0`).
    Why the premise holds there: U/Prog/LLVMFuzzerTestOneInput_c.v's role_check_contract takes the same fact for
    [CODES_TBL, CODES_TBL_END) = [0x1e1f8, 0x1e208) of the memory its evt starts on; the table lies in frame_RELRO's
    first range [0x1e0f0, 0x1e0f0 + 424) (U/FrameAPI.v), so the slot's relro conjunct (G_img_c frame_RELRO:
    mbyte = seg_rom there) gives it at the cut. Between the evt's start and these calls the harness writes only its
    heap blocks and stack (the pod copy, the parse's frame and role cell, the check frames), none of these 16 bytes.
    refuse_code_res 0 = CODE_NONE and refuse_code_res 1 = CODE_MALFORMED by computation: check_code's premises. *)
Definition REAC_ROLE_REFUSE_CODE : Z := 0x145e4.
Definition REFUSE_TBL : Z := 0x1e1f8.
Definition REFUSE_TBL_SIZE : Z := 16.
Definition CODE_NONE : Z := 0x103e0.
Definition CODE_MALFORMED : Z := 0x103d6.

(** codes[] = REAC_ROLE_REFUSE_CODES_INIT, the two pointers in the table. *)
Definition REFUSE_CODES : list Z := [CODE_NONE; CODE_MALFORMED].

(** The result for r = bv_unsigned a0: codes[r] for r < 2, else codes[0]. *)
Definition refuse_code_res (r : Z) : Z :=
  if r <? 2 then nth (Z.to_nat r) REFUSE_CODES CODE_NONE else CODE_NONE.

Definition reac_role_refuse_code_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    (forall a, REFUSE_TBL <= a < REFUSE_TBL + REFUSE_TBL_SIZE -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (refuse_code_res (bv_unsigned a0))) a1' a2' a3'
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_ROLE_REFUSE_CODE) fc None m (seg_rom rsegs)).

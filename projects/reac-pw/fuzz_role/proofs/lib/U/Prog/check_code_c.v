From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import reac_role_refuse_code_c.
Import ListNotations.
Open Scope Z_scope.

(** check_code(none, malformed) (fuzz_role.c:121-131; 76 bytes, 19 instructions at 0x142d8 in the UBSan image;
    frame 16 bytes, saves ra at sp - 8 and s0 at sp - 16):
      0x142d8 addi sp,sp,-16; sd ra,8(sp); sd s0,0(sp); mv s0,a1;
              auipc a1,0xffffc; addi a1,a1,0xf8 (a1 = 0x142e8 - 0x4000 + 0xf8 = 0x103e0, "none");
              jal strcmp (0x1cb44); bnez a0,0x1431c;
      0x142f8 auipc a0,0xffffc; addi a1,a0,0xde (a1 = 0x142f8 - 0x4000 + 0xde = 0x103d6, "malformed"); mv a0,s0;
              jal strcmp (0x1cb44); bnez a0,0x1431c; ld ra,8(sp); ld s0,0(sp); addi sp,sp,16; ret;
      0x1431c jal abort (0x15b14); unimp.
    The plain text with a trap after the abort call (no UBSan check in it). Its two literals are the very addresses
    CODE_NONE and CODE_MALFORMED that U's reac_role_refuse_code returns for 0 and 1 (the two pointers of its
    .data.rel.ro table; the strings are merged in .rodata), so with a0 = CODE_NONE and a1 = CODE_MALFORMED each
    strcmp compares one string with itself and strcmp_contract's r = 0 <-> sx = sy gives r = 0: neither bnez is
    taken. The premises are pointer equalities for that reason (equal bytes at other addresses would also pass, but
    the caller holds the pointers). On that path it writes a0-a3 (the auipc, the moves and strcmp) and s0, which it
    restores, stores ra and s0 in its frame [sp - 16, sp) and loads them back (strcmp stores nothing), and reads the
    two strings (.rodata, in the read-only segment at 0x10000: mem_inv makes those reads come from the image; the
    stack premise keeps the frame stores off them).

    Callee contract its walk takes as a premise, twice: strcmp_contract (U/Prog/strcmp_c.v, STRCMP = 0x1cb44; the
    released form of libreac/fuzz_ctrl, relocated: both strings NUL-terminated, r = 0 <-> sx = sy, writes a0-a3, no
    stack, no store), with sx = sy = "none" and then sx = sy = "malformed" (read from the image).

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x141b0 `jal check_code` (the only one), reached on every run past the
    size check and both mallocs, with sp = S - 544 (the harness frame) and
      a0 = s2 = reac_role_refuse_code(0) (0x141ac `mv a0,s2`; 0x1419c `mv s2,a0` after the call at 0x14198 with
           a0 = 0 from 0x14194 `mv a0,zero`);
      a1 = reac_role_refuse_code(1) (0x141a8 `mv a1,a0` after the call at 0x141a4 with a0 = 1 from 0x141a0
           `addi a0,zero,1`).
    Why each premise holds there: U's reac_role_refuse_code_contract returns Z_to_bv 64 (refuse_code_res 0) =
    Z_to_bv 64 CODE_NONE at 0x14198 and Z_to_bv 64 (refuse_code_res 1) = Z_to_bv 64 CODE_MALFORMED at 0x141a4, and
    keeps s2 across the second call. The stack region [lo, sp) with lo = S - SLOT_K (SLOT_K = 65536) is the frame's
    stack (FR's stk), writable and outside the image (seg_rom None), and lo + 16 <= S - 544; mem_inv holds of the
    memory the cut runs on and every callee since keeps it. *)
Definition CHECK_CODE : Z := 0x142d8.
Definition CHECK_CODE_FRAME : Z := 16.

Definition check_code_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    a0 = Z_to_bv 64 CODE_NONE ->
    a1 = Z_to_bv 64 CODE_MALFORMED ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_CODE_FRAME <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_CODE_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_CODE) fc None m (seg_rom rsegs)).

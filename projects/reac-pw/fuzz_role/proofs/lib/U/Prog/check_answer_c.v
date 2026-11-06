From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import
  reac_role_cfg_changes_c reac_role_cfg_apply_state_c.
Import ListNotations.
Open Scope Z_scope.

(** check_answer(changes, state, cur, req) (fuzz_role.c:107-119; 80 bytes, 20 instructions at 0x14288 in the UBSan
    image; frame 16 bytes, saves ra at sp - 8):
      0x14288 addi sp,sp,-16; sd ra,8(sp); xor a4,a2,a3; snez a4,a4; bne a0,a4,0x142d0;
      0x1429c bne a2,a3,0x142ac; auipc a0,0xffffc; addi a2,a0,0x1eb (a2 = 0x142a0 - 0x4000 + 0x1eb = 0x1048b);
              j 0x142b4;
      0x142ac auipc a0,0xffffc; addi a2,a0,0x51 (a2 = 0x142ac - 0x4000 + 0x51 = 0x102fd);
      0x142b4 mv a0,a1; mv a1,a2; jal strcmp (0x1cb44); bnez a0,0x142d0; ld ra,8(sp); addi sp,sp,16; ret;
      0x142d0 jal abort (0x15b14); unimp.
    The plain text with a trap after the abort call (no UBSan check in it). The first test compares a0 with
    snez (a2 xor a3), both 64-bit words: a0 = changes_res a2 a3 passes it. The literal is 0x1048b ("applied") when
    a2 = a3, else 0x102fd ("role_reestablish_pending"): the very addresses STATE_APPLIED and STATE_PENDING that U's
    reac_role_cfg_apply_state returns (the strings are merged in .rodata), so a1 = apply_state_res a2 a3 makes strcmp
    compare one string with itself, and strcmp_contract's r = 0 <-> sx = sy gives r = 0: the bnez is not taken. On
    that path it writes a0-a4 (a4 by snez, a2 by the addi, a0 and a1 by the moves, a0-a3 by strcmp), stores ra at
    sp - 8 (in its frame [sp - 16, sp)) and loads it back (strcmp stores nothing), and reads the two strings at a1 and
    the literal (.rodata, in the read-only segment at 0x10000: mem_inv makes those reads come from the image; the
    stack premise keeps the frame store off them).

    Callee contract its walk takes as a premise: strcmp_contract (U/Prog/strcmp_c.v, STRCMP = 0x1cb44; the released
    form of libreac/fuzz_ctrl, relocated: both strings NUL-terminated, r = 0 <-> sx = sy, writes a0-a3, no stack, no
    store), with sx = sy = the text of the chosen string ("applied" or "role_reestablish_pending", read from the
    image).

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x14190 `jal check_answer` (the only one), reached on every run past
    the size check and both mallocs, with sp = S - 544 (the harness frame) and
      a0 = s4 = changes (0x14184 `mv a0,s4`; 0x14170 `mv s4,a0` after reac_role_cfg_changes at 0x1416c);
      a1 = state (0x14180 `mv a1,a0` after reac_role_cfg_apply_state at 0x1417c);
      a2 = s3 = cur (0x14188 `mv a2,s3`; 0x14150 `srli s3,a0,0x3f`, a0 = flags << 62 from 0x14148): flags bit 1;
      a3 = s2 = req (0x1418c `mv a3,s2`; 0x14160 `lw s2,0x158(sp)` when rc = 1, else 0x14158 `xori s2,s3,1`).
    Why each premise holds there: U's reac_role_cfg_changes_contract at 0x1416c (a0 = s3, a1 = s2 by 0x14164,
    0x14168) returns Z_to_bv 64 (changes_res s3 s2), and U's reac_role_cfg_apply_state_contract at 0x1417c (a0 = s3,
    a1 = s2 by 0x14174, 0x14178) returns Z_to_bv 64 (apply_state_res s3 s2); both keep s2, s3 and s4, so the two
    value premises hold for every cur and req, corrupted pods included. The stack region [lo, sp) with
    lo = S - SLOT_K (SLOT_K = 65536) is the frame's stack (FR's stk), writable and outside the image (seg_rom None),
    and lo + 16 <= S - 544; mem_inv holds of the memory the cut runs on and every callee since keeps it. *)
Definition CHECK_ANSWER : Z := 0x14288.
Definition CHECK_ANSWER_FRAME : Z := 16.

Definition check_answer_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    a0 = Z_to_bv 64 (changes_res a2 a3) ->
    a1 = Z_to_bv 64 (apply_state_res a2 a3) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_ANSWER_FRAME <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_ANSWER_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ANSWER) fc None m (seg_rom rsegs)).

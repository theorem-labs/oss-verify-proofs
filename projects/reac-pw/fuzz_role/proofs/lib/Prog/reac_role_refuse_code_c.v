From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** reac_role_refuse_code(r) (reac_role_cfg.c:14-20; 48 bytes, 12 instructions at 0x143b8 in the plain image):
      0x143b8 addi a1,zero,1; bgeu a1,a0,0x143cc;
              auipc a0,0xffffc; addi a0,a0,0x20 (a0 = 0x143c0 - 0x4000 + 0x20 = 0x103e0 = codes[0]); ret;
      0x143cc slli a0,a0,2; auipc a1,0xffffc; addi a1,a1,0x268 (a1 = 0x143d0 - 0x4000 + 0x268 = 0x10638);
              add a0,a1,a0; lw a0,0(a0); add a0,a1,a0; ret.
    The compiler turned `static const char *const codes[]` into a relative table in .rodata: REFUSE_TBL = 0x10638
    holds two signed 32-bit offsets from the table, -600 and -610, so codes[0] = 0x10638 - 600 = 0x103e0 ("none",
    CODE_NONE) and codes[1] = 0x10638 - 610 = 0x103d6 ("malformed", CODE_MALFORMED); both strings are in .rodata.
    Total: for a0 <= 1 as a 64-bit unsigned word (the bgeu; it is the source's `(unsigned)r >= 2` on the
    sign-extended int) it returns REFUSE_TBL + the sign-extended entry a0 (lw), else codes[0] directly. It writes a0
    and a1 (1, or REFUSE_TBL on the table path), stores nothing and uses no stack. It reads only the 4-byte entry at
    REFUSE_TBL + 4 a0, in the read-only segment at 0x10000: mem_inv makes that read come from the image.

    Call sites (LLVMFuzzerTestOneInput, plain), reached on every run past the size check and both mallocs, right
    after check_answer (0x14134):
      0x1413c `jal reac_role_refuse_code` with a0 = 0 (0x14138 `mv a0,zero`); the result goes to s2 (0x14140
              `mv s2,a0`) and on to check_code's a0 (0x14150 `mv a0,s2`);
      0x14148 `jal reac_role_refuse_code` with a0 = 1 (0x14144 `addi a0,zero,1`); the result goes to check_code's a1
              (0x1414c `mv a1,a0`).
    Why the premise holds there: mem_inv holds of the memory the cut runs on and is kept by every callee before
    (check_answer_contract's post has mem_inv of its m'; this function stores nothing). refuse_code_res 0 = CODE_NONE
    and refuse_code_res 1 = CODE_MALFORMED by computation: check_code's premises. *)
Definition REAC_ROLE_REFUSE_CODE : Z := 0x143b8.
Definition REFUSE_TBL : Z := 0x10638.
Definition CODE_NONE : Z := 0x103e0.
Definition CODE_MALFORMED : Z := 0x103d6.

(** codes[] = REAC_ROLE_REFUSE_CODES_INIT, as the table's two targets. *)
Definition REFUSE_CODES : list Z := [CODE_NONE; CODE_MALFORMED].

(** The result for r = bv_unsigned a0: codes[r] for r < 2, else codes[0]. *)
Definition refuse_code_res (r : Z) : Z :=
  if r <? 2 then nth (Z.to_nat r) REFUSE_CODES CODE_NONE else CODE_NONE.

Definition reac_role_refuse_code_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a1' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (refuse_code_res (bv_unsigned a0))) a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_ROLE_REFUSE_CODE) fc None m (seg_rom rsegs)).

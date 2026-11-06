From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** reac_role_cfg_changes(current_role, requested_role) (reac_role_cfg.c:22-25; 12 bytes, 3 instructions at 0x14620
    in the UBSan image): 0x14620 xor a0,a0,a1; snez a0,a0; ret. No UBSan check in it.
    Total: on every entry it returns 0 when a0 and a1 are the same 64-bit word, else 1 (snez of the xor), in a0. It
    writes only a0, stores nothing, reads no memory and uses no stack.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x1416c `jal reac_role_cfg_changes` (the only one), reached on every
    run past the size check and both mallocs, with
      a0 = s3 = cur (0x14164 `mv a0,s3`; 0x14150 `srli s3,a0,0x3f` with a0 = flags << 62 from 0x14148
           `slli a0,s3,0x3e`, s3 = flags): flags bit 1, 0 or 1;
      a1 = s2 = req (0x14168 `mv a1,s2`): 0x14160 `lw s2,0x158(sp)` (the role cell) when rc = 1 (0x14154 `beq s2,a1`
           with a1 = 1 from 0x1414c), else 0x14158 `xori s2,s3,1`.
    The result goes to s4 (0x14170 `mv s4,a0`) and on to check_answer's a0 (0x14184). No premise: the contract holds
    for any cur and req. *)
Definition REAC_ROLE_CFG_CHANGES : Z := 0x14620.

(** The result: 0 when the two roles are the same word, else 1. *)
Definition changes_res (cur req : word) : Z := if bv_eqb cur req then 0 else 1.

Definition reac_role_cfg_changes_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (changes_res a0 a1)) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_ROLE_CFG_CHANGES) fc None m (seg_rom rsegs)).

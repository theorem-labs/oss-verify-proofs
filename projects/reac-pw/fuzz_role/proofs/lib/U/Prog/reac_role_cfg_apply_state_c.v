From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** reac_role_cfg_apply_state(current_role, requested_role) (reac_role_cfg.c:27-37, with reac_role_cfg_changes
    inlined; 28 bytes, 7 instructions at 0x1462c in the UBSan image; no UBSan check in it):
      0x1462c beq a0,a1,0x1463c; auipc a0,0xffffc; addi a0,a0,-0x333 (a0 = 0x14630 - 0x4000 - 0x333 = 0x102fd); ret;
      0x1463c auipc a0,0xffffc; addi a0,a0,-0x1b1 (a0 = 0x1463c - 0x4000 - 0x1b1 = 0x1048b); ret.
    Total: on every entry it returns in a0 the address of "applied" (STATE_APPLIED, REAC_ROLE_STATE_APPLIED) when a0
    and a1 are the same 64-bit word, else the address of "role_reestablish_pending" (STATE_PENDING,
    REAC_ROLE_STATE_REESTABLISH_PENDING). Both strings lie in .rodata, in the read-only segment at 0x10000, and each
    ends at its first NUL (7 and 24 bytes of text); the UBSan image has them at the same addresses as the plain one.
    It writes only a0, stores nothing, reads no memory (the auipc/addi pairs only form addresses) and uses no stack.
    check_answer's two literals are these same two addresses (the strings are merged).

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x1417c `jal reac_role_cfg_apply_state` (the only one), right after
    reac_role_cfg_changes (0x1416c), with
      a0 = s3 = cur (0x14174 `mv a0,s3`), flags bit 1 (0x14150 `srli s3,a0,0x3f`);
      a1 = s2 = req (0x14178 `mv a1,s2`), set at 0x14160 (`lw s2,0x158(sp)` when rc = 1) or 0x14158 (`xori s2,s3,1`).
    s2 and s3 are as they were before reac_role_cfg_changes (its contract keeps them). The result goes to check_answer's
    a1 (0x14180 `mv a1,a0`). No premise: the contract holds for any cur and req. *)
Definition REAC_ROLE_CFG_APPLY_STATE : Z := 0x1462c.
Definition STATE_APPLIED : Z := 0x1048b.
Definition STATE_PENDING : Z := 0x102fd.

(** The result: the address of "applied" when the two roles are the same word, else of "role_reestablish_pending". *)
Definition apply_state_res (cur req : word) : Z := if bv_eqb cur req then STATE_APPLIED else STATE_PENDING.

Definition reac_role_cfg_apply_state_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (apply_state_res a0 a1)) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_ROLE_CFG_APPLY_STATE) fc None m (seg_rom rsegs)).

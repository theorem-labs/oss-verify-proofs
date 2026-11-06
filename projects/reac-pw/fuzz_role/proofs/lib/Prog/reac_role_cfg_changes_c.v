From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** reac_role_cfg_changes(current_role, requested_role) (reac_role_cfg.c:22-25; 12 bytes, 3 instructions at 0x143e8
    in the plain image): 0x143e8 xor a0,a0,a1; snez a0,a0; ret.
    Total: on every entry it returns 0 when a0 and a1 are the same 64-bit word, else 1 (snez of the xor), in a0. It
    writes only a0, stores nothing, reads no memory and uses no stack.

    Call site (LLVMFuzzerTestOneInput, plain): 0x14110 `jal reac_role_cfg_changes` (the only one), reached on every
    run past the size check and both mallocs, with
      a0 = s3 = cur (0x14108 `mv a0,s3`; 0x140f4 `srli s3,s0,0x3f` with s0 = flags << 62 from 0x13f68
           `slli s0,s5,0x3e`): flags bit 1, 0 or 1;
      a1 = s2 = req (0x1410c `mv a1,s2`): 0x14104 `lw s2,0x128(sp)` (the role cell) when rc = 1 (0x140f8 `beq s2,a0`
           with a0 = 1 from 0x140f0), else 0x140fc `xori s2,s3,1`.
    The result goes to s4 (0x14114 `mv s4,a0`) and on to check_answer's a0 (0x14128). No premise: the contract holds
    for any cur and req. *)
Definition REAC_ROLE_CFG_CHANGES : Z := 0x143e8.

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

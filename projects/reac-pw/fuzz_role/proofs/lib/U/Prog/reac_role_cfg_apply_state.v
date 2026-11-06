From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import reac_role_cfg_apply_state_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_role_cfg_apply_state of the UBSan image (0x1462c, 7 instructions), walked with Lib/Tac.v and Lib/Step.v:
    `beq a0, a1` to 0x1463c, which forms STATE_APPLIED with auipc/addi and returns; else it forms STATE_PENDING and
    returns. The walk splits on bv_eqb a0 a1 first; the branch that disagrees with it is refuted. *)

Theorem reac_role_cfg_apply_state_holds : reac_role_cfg_apply_state_contract.
Proof.
  unfold reac_role_cfg_apply_state_contract, REAC_ROLE_CFG_APPLY_STATE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m.
  unfold apply_state_res, STATE_APPLIED, STATE_PENDING.
  destruct (bv_eqb a0 a1) eqn:EQ; pose proof EQ as EQz; unfold bv_eqb in EQz;
    [apply Z.eqb_eq in EQz | apply Z.eqb_neq in EQz].
  all: zstep;
    let K := fresh "K" in
    if_cases K;
      first [ exfalso; zify_cond K; lia
            | zstep; zstep; zstep; finish ].
Qed.

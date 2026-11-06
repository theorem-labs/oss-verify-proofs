From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import reac_role_refuse_code_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_role_refuse_code of the plain image (0x143b8, 12 instructions), walked with Lib/Tac.v and Lib/Step.v.
    `addi a1, zero, 1; bgeu a1, a0` splits on a0 <= 1 (unsigned). For a0 > 1 it forms codes[0] with auipc/addi and
    returns. For a0 = 0 or 1 (the walk substitutes the literal) it loads the 4-byte entry a0 of the relative table at
    REFUSE_TBL (.rodata: mem_inv makes the load read the image) and adds it to REFUSE_TBL. *)

Ltac kill K :=
  exfalso;
  first [ zify_cond K; lia
        | revert K; vm_compute; let H := fresh in intro H; discriminate H ].

Theorem reac_role_refuse_code_holds : reac_role_refuse_code_contract.
Proof.
  unfold reac_role_refuse_code_contract, REAC_ROLE_REFUSE_CODE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m MI.
  pose proof (zr_word a0) as R0. unfold inr64 in R0.
  destruct (Z_le_gt_dec (bv_unsigned a0) 1) as [LE|GT].
  - (* the table path: a0 is 0 or 1 *)
    assert (E : a0 = Z_to_bv 64 0 \/ a0 = Z_to_bv 64 1).
    { destruct (Z.eq_dec (bv_unsigned a0) 0) as [E0|E0]; [left|right];
        apply bv_eq; rewrite unsigned_lit by lia; lia. }
    clear LE R0.
    destruct E as [-> | ->].
    all: (* addi a1, zero, 1; bgeu a1, a0: taken *)
      zstep; zstep;
      let K := fresh "K" in
      if_cases K; [ first [ kill K | idtac ] .. ];
      (* slli a0, a0, 2; auipc a1; addi a1; add a0, a1, a0; lw a0, 0(a0); add a0, a1, a0; ret *)
      do 7 zstep; finish.
  - (* a0 > 1: codes[0] *)
    assert (RC : refuse_code_res (bv_unsigned a0) = CODE_NONE).
    { unfold refuse_code_res. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    rewrite RC. unfold CODE_NONE.
    (* addi a1, zero, 1; bgeu a1, a0: not taken *)
    zstep. zstep.
    let K := fresh "K" in
    if_cases K; [ first [ kill K | idtac ] .. ].
    (* auipc a0; addi a0; ret *)
    zstep. zstep. zstep. finish.
Qed.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import reac_rate_refuse_code_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_refuse_code of the plain image (0x14990, 12 instructions), walked with Lib/Tac.v and Lib/Step.v
    (reac-pw/fuzz_role's walk of reac_role_refuse_code, with the bound 4 for role's 1). `addi a1, zero, 4;
    bgeu a1, a0` splits on a0 <= 4 (unsigned). For a0 > 4 it forms codes[0] with auipc/addi and returns. For
    a0 in 0..4 (the walk substitutes the literal) it loads the 4-byte entry a0 of the relative table at REFUSE_TBL
    (.rodata: mem_inv makes the load read the image) and adds it to REFUSE_TBL. *)

Ltac kill K :=
  exfalso;
  first [ zify_cond K; lia
        | revert K; vm_compute; let H := fresh in intro H; discriminate H ].

Theorem reac_rate_refuse_code_holds : reac_rate_refuse_code_contract.
Proof.
  unfold reac_rate_refuse_code_contract, REAC_RATE_REFUSE_CODE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m MI.
  pose proof (zr_word a0) as R0. unfold inr64 in R0.
  destruct (Z_le_gt_dec (bv_unsigned a0) 4) as [LE|GT].
  - (* the table path: a0 is 0, 1, 2, 3 or 4 *)
    assert (E : exists k, 0 <= k <= 4 /\ a0 = Z_to_bv 64 k).
    { exists (bv_unsigned a0). split; [lia|]. symmetry. apply Z_to_bv_lit_self. }
    destruct E as (k & Hk & ->). clear LE R0.
    assert (Ek : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia. clear Hk.
    destruct Ek as [-> | [-> | [-> | [-> | ->]]]].
    all: (* addi a1, zero, 4; bgeu a1, a0: taken *)
      zstep; zstep;
      let K := fresh "K" in
      if_cases K; [ first [ kill K | idtac ] .. ];
      (* slli a0, a0, 2; auipc a1; addi a1; add a0, a1, a0; lw a0, 0(a0); add a0, a1, a0; ret *)
      do 7 zstep; finish.
  - (* a0 > 4: codes[0] *)
    assert (RC : refuse_code_addr (bv_unsigned a0) = CODE_NONE).
    { unfold refuse_code_addr, refuse_idx. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
    rewrite RC. unfold CODE_NONE.
    (* addi a1, zero, 4; bgeu a1, a0: not taken *)
    zstep. zstep.
    let K := fresh "K" in
    if_cases K; [ first [ kill K | idtac ] .. ].
    (* auipc a0; addi a0; ret *)
    zstep. zstep. zstep. finish.
Qed.

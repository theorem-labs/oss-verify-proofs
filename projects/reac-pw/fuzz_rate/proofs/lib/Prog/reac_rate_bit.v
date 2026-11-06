From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import reac_rate_bit_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_bit of the plain image (0x149f4, 17 instructions), walked with Lib/Tac.v and Lib/Step.v. The walk splits
    on the value of a0 ([rate_bit_cases]: 44100, 48000, 96000 or none of them) and rewrites the answer to its
    literal; then each of the three 64-bit compares (`beq a0, a1` with a1 = 44100, `beq` with 96000, `bne` with 48000,
    each built by `lui; addiw`) is decided by that case, and the path returns 1, 4, 2 or 0. *)

(** A branch the context contradicts: every compare here is of a0 with a literal, so lia decides it. *)
Ltac kill K := exfalso; zify_cond K; lia.

(** Step to the `ret`, deciding each branch from the context. *)
Ltac walk :=
  repeat first [ let K := fresh "K" in if_cases K; [ first [ kill K | idtac ] .. ]
               | zstep ].

Theorem reac_rate_bit_holds : reac_rate_bit_contract.
Proof.
  unfold reac_rate_bit_contract, REAC_RATE_BIT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m.
  destruct (rate_bit_cases (bv_unsigned a0)) as [[E R] | [[E R] | [[E R] | (E1 & E2 & E3 & R)]]];
    rewrite R; unfold RATE_44K1, RATE_48K, RATE_96K in *.
  all: walk; finish.
Qed.

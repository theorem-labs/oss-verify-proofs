From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import reac_rate_is_closed_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_is_closed of the UBSan image (0x14d14, 13 instructions; the plain code, Prog/reac_rate_is_closed.v, at
    another address), walked with Lib/Tac.v and Lib/Step.v. The walk splits on the value of a0 ([rate_bit_cases])
    and rewrites the answer to its literal. On 44100 and 48000 a `beq` is taken and it returns a1 = 1. Otherwise it
    returns `seqz (a0 xor 96000)`: for 96000 the walk substitutes the literal, and for any other value the xor is a
    nonzero integer ([lxor_ne]), so the seqz is 0. *)

(** A branch the context contradicts: every compare here is of a0 with a literal, so lia decides it. *)
Ltac kill K := exfalso; zify_cond K; lia.

(** Step to the `ret`, deciding each branch from the context. *)
Ltac walk :=
  repeat first [ let K := fresh "K" in if_cases K; [ first [ kill K | idtac ] .. ]
               | zstep ].

(** The xor of two different values in range is a positive integer. *)
Lemma lxor_ne : forall x c, 0 <= x -> 0 <= c -> x <> c -> 1 <= Z.lxor x c.
Proof.
  intros x c Hx Hc N.
  assert (L : 0 <= Z.lxor x c) by (apply Z.lxor_nonneg; split; intros; lia).
  assert (Z.lxor x c <> 0) by (intros Z0; apply N; apply Z.lxor_eq_0_iff; exact Z0).
  lia.
Qed.

Theorem reac_rate_is_closed_holds : reac_rate_is_closed_contract.
Proof.
  unfold reac_rate_is_closed_contract, REAC_RATE_IS_CLOSED.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m.
  pose proof (zr_word a0) as R0. unfold inr64 in R0.
  unfold rate_closed.
  destruct (rate_bit_cases (bv_unsigned a0)) as [[E R] | [[E R] | [[E R] | (E1 & E2 & E3 & R)]]];
    rewrite R; unfold RATE_44K1, RATE_48K, RATE_96K in *.
  - walk. finish.
  - walk. finish.
  - (* 96000: substitute the literal *)
    assert (A : a0 = Z_to_bv 64 96000) by (rewrite <- E; symmetry; apply Z_to_bv_lit_self).
    subst a0. walk. finish.
  - (* no closed rate: the xor with 96000 is nonzero *)
    pose proof (lxor_ne (bv_unsigned a0) 96000 ltac:(lia) ltac:(lia) E3) as X.
    walk. decide_tests. cbn [Z.b2z]. finish.
Qed.

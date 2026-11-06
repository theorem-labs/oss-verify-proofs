From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import reac_rate_cfg_decide_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_cfg_decide of the UBSan image (0x14f94, 21 instructions; the plain code, Prog/reac_rate_cfg_decide.v,
    at another address), walked with Lib/Tac.v and Lib/Step.v. The walk splits as decide_res does: role a0 = 1
    (`bne a0, a3` with a3 = 1 not taken: 3); else the value of the rate a1 ([rate_bit_cases]): none of the three (the
    three compares fall through to the `mv a0, a3` with a3 = 1: 1), or a rate with bit b in a3, where
    `and a2, a3, a2; seqz a3, a2; slli a3, a3, 1` gives 2 when b and the mask a2 share no bit and 0 else (the walk
    splits on that test too). *)

(** A branch the context contradicts: every compare here is of an argument or a literal, so lia decides it. *)
Ltac kill K := exfalso; zify_cond K; lia.

(** Step to the `ret`, deciding each branch from the context. *)
Ltac walk :=
  repeat first [ let K := fresh "K" in if_cases K; [ first [ kill K | idtac ] .. ]
               | zstep ].

(** The rate has bit b: split on the test of b against the mask, then walk; the seqz is decided by that test. *)
Ltac mask_case b a2 :=
  pose proof (Z.land_nonneg b (bv_unsigned a2)) as LN;
  assert (L0 : 0 <= Z.land b (bv_unsigned a2)) by (apply LN; left; lia); clear LN;
  let L := fresh "L" in
  destruct (Z.land b (bv_unsigned a2) =? 0) eqn:L;
  [ apply Z.eqb_eq in L | apply Z.eqb_neq in L ];
  walk; decide_tests; cbn [Z.b2z]; zb_fold_lits; finish.

Theorem reac_rate_cfg_decide_holds : reac_rate_cfg_decide_contract.
Proof.
  unfold reac_rate_cfg_decide_contract, REAC_RATE_CFG_DECIDE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m.
  pose proof (zr_word a2) as R2. unfold inr64 in R2.
  unfold decide_res, REFUSE_ROLE_SLAVE, REFUSE_NOT_CLOSED, REFUSE_NOT_DRIVABLE, REFUSE_NONE.
  (* destructing Z.eqb_spec replaces the test `bv_unsigned a0 =? 1` of decide_res by its value *)
  destruct (Z.eqb_spec (bv_unsigned a0) 1) as [A | A].
  - (* role = 1: 3 *)
    walk. finish.
  - destruct (rate_bit_cases (bv_unsigned a1)) as [[E R] | [[E R] | [[E R] | (E1 & E2 & E3 & R)]]];
      rewrite R; unfold RATE_44K1, RATE_48K, RATE_96K in *.
    + mask_case 1 a2.
    + mask_case 2 a2.
    + mask_case 4 a2.
    + (* no closed rate: 1 *)
      walk. finish.
Qed.

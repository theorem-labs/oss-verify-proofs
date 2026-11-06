From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Prog Require Import reac_knock_struct.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Prog Require Import reac_knock_heard_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Theorem reac_knock_heard_holds : reac_knock_heard_contract.
Proof.
  unfold reac_knock_heard_contract, REAC_KNOCK_HEARD, knock_cells.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m st p1 opened due heard g p2 HS HG NZ AL H.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  if_cases K0.
  - exfalso. zify_cond K0. lia.
  - step. step.
    if_cases K1.
    + exfalso. zify_cond K1. rewrite land7_mod8 in K1. lia.
    + step. step. step.
      if_cases HC.
      * rewrite knock_sx32_eqb in HC by lia. apply Z.eqb_eq in HC. subst st.
        step. step. step.
        finish.
      * rewrite knock_sx32_eqb in HC by lia.
        step.
        finish; try (rewrite HC; exact H).
Qed.

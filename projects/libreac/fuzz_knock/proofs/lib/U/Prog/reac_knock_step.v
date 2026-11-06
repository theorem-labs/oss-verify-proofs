From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Prog Require Import reac_knock_struct.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Prog Require Import reac_knock_step_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma u64_range : forall x : word, 0 <= bv_unsigned x < 18446744073709551616.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as R. exact R. Qed.

Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac close_step :=
  unfold knock_step_f, knock_cells, L_NS;
  repeat match goal with
  | E : (?a <=? ?b) = _ |- context [?a <=? ?b] => rewrite E
  | E : (?a <? ?b) = _ |- context [?a <? ?b] => rewrite E
  | E : (?a =? ?b) = _ |- context [?a =? ?b] => rewrite E
  end;
  cbn [Z.eqb Pos.eqb orb negb];
  split; [reflexivity | assumption].

Theorem reac_knock_step_holds : reac_knock_step_contract.
Proof.
  unfold reac_knock_step_contract, REAC_KNOCK_STEP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m st p1 opened due heard g p2 HS HG NZ AL H.
  unfold knock_cells in H.
  pose proof (u64_range a1) as Ba. pose proof (u64_range heard) as Bh. pose proof (u64_range due) as Bd.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  if_cases T0; [exfalso; zify_cond T0; lia |].
  step. step.
  if_cases T1; [exfalso; zify_cond T1; rewrite land7_mod8 in T1; lia |].
  step. step.
  if_cases K1.
  - rewrite knock_sx32_eqb in K1 by lia. apply Z.eqb_eq in K1. subst st.
    step. step.
    if_cases K6.
    + zify_cond K6.
      assert (E3 : (bv_unsigned a1 <? bv_unsigned due) = false) by (apply Z.ltb_ge; lia).
      step. step. step. step. step. finish. close_step.
    + zify_cond K6.
      assert (E3 : (bv_unsigned a1 <? bv_unsigned due) = true) by (apply Z.ltb_lt; lia).
      step. step. step. step. finish. close_step.
  - rewrite knock_sx32_eqb in K1 by lia.
    step. step.
    if_cases K2.
    + rewrite knock_sx32_eqb in K2 by lia. apply negb_true_iff in K2.
      step. step. step. step. finish. close_step.
    + rewrite knock_sx32_eqb in K2 by lia. apply negb_false_iff in K2.
      apply Z.eqb_eq in K2. subst st.
      step. step. step.
      if_cases K3.
      * zify_cond K3.
        assert (E1 : (bv_unsigned a1 <=? bv_unsigned heard) = true) by (apply Z.leb_le; lia).
        step. step. finish. close_step.
      * zify_cond K3.
        assert (E1 : (bv_unsigned a1 <=? bv_unsigned heard) = false) by (apply Z.leb_gt; lia).
        step. step. step. step.
        if_cases K4.
        -- zify_cond K4. try rewrite Z.mod_small in K4 by lia.
           assert (E2 : (bv_unsigned a1 - bv_unsigned heard <? 500000000) = true) by (apply Z.ltb_lt; lia).
           step. step. finish. close_step.
        -- zify_cond K4. try rewrite Z.mod_small in K4 by lia.
           assert (E2 : (bv_unsigned a1 - bv_unsigned heard <? 500000000) = false) by (apply Z.ltb_ge; lia).
           step. step. step. step. step.
           if_cases K5.
           ++ step. step. step. step. step. finish. close_step.
           ++ exfalso. zify_cond K5. try rewrite Z.mod_small in K5 by lia. lia.
Qed.

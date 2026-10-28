From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require Import S_u18350.
Import ListNotations.
Open Scope Z_scope.
Import SliceEqAddr.

Definition FUEL_se : nat := 200%nat.
Definition M64m1 : Z := 2 ^ 64 - 1.

Definition C_se (lit k : Z) : sstate :=
  mkSS se_loop
       (setregs (cut_regs NF)
          [(10%nat, SAlu ALU_ADD vB vI); (11%nat, vN); (12%nat, SLit lit); (13%nat, SLit k);
           (14%nat, SLit (M64m1 - lit)); (15%nat, SAlu ALU_XOR (SAlu ALU_ADD vB vI) (SLit M64m1))])
       pre_fregs FcsrFrm0 None [O_txt] (se_facts ++ [SPUle (SLit (k + 1)) vN]) 135 false.

Definition cuts_se (lit : Z) (n : nat) : list sstate :=
  Pre_se lit :: map (fun k => C_se lit (Z.of_nat k)) (seq 0 (S n)).
Definition exits_se : list sstate := [P_A; P_B; P_C].
Definition cutpcs_se : list Z := [se_loop].

Definition vcuts_se (lit : Z) (n : nat) : list vnode :=
  mkVN (Pre_se lit) 30 (SLit 0)
    :: map (fun k => mkVN (C_se lit (Z.of_nat k)) (20 - Z.of_nat k) (SLit 0)) (seq 0 (S n)).
Definition vexits_se : list vnode := [mkVN P_A 1 vTop; mkVN P_B 1 vTop; mkVN P_C 1 vTop].

Section Gen.
Variable lit : Z.
Variable n : nat.
Hypothesis check_se : check_cfg segsU FUEL_se cutpcs_se NF (cuts_se lit n) exits_se = true.
Hypothesis echeck_se : check_ecfgI segsU FUEL_se cutpcs_se NF (vcuts_se lit n) vexits_se = true.
Hypothesis strict_se : existsb ss_lenient (cuts_se lit n) = false.

Theorem slice_eq_sum_gen : slice_eq_sum_stmt lit.
Proof using check_se strict_se.
  intros ok K rho Hok.
  apply (cfg_sound segsU FUEL_se cutpcs_se NF (cuts_se lit n) exits_se
           (fun rho' => agree_below NF rho rho') ok K (LQ segsU K NF rho Posts_se) Hok).
  - rewrite strict_se. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_se.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[<-|[<-|[]]]]; revert HagE.
    + apply exit_post. in_nth 0.
    + apply exit_post. in_nth 1.
    + apply exit_post. in_nth 2.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Theorem slice_eq_sum_ex_gen : slice_eq_sum_ex_stmt lit.
Proof using echeck_se.
  intros K rho.
  change (Pre_se lit) with (vn_state (mkVN (Pre_se lit) 30 (SLit 0))).
  apply (cfg_complete_autoI segsU FUEL_se cutpcs_se NF (vcuts_se lit n) vexits_se
           (fun rho' => agree_below NF rho rho') K (LQ segsU K NF rho Posts_se)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_se.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[<-|[<-|[]]]]; revert HgE.
    + apply (eexit_post_I0 segsU K NF rho (vcuts_se lit n) Posts_se (mkVN P_A 1 vTop)). in_nth 0.
    + apply (eexit_post_I0 segsU K NF rho (vcuts_se lit n) Posts_se (mkVN P_B 1 vTop)). in_nth 1.
    + apply (eexit_post_I0 segsU K NF rho (vcuts_se lit n) Posts_se (mkVN P_C 1 vTop)). in_nth 2.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
End Gen.

Theorem slice_eq_sum : forall lit n, In (lit, n) se_lits -> slice_eq_sum_stmt lit.
Proof.
  intros lit n Hin. apply (slice_eq_sum_gen lit n);
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; vm_compute; reflexivity|]); destruct Hin.
Qed.

Theorem slice_eq_sum_ex : forall lit n, In (lit, n) se_lits -> slice_eq_sum_ex_stmt lit.
Proof.
  intros lit n Hin. apply (slice_eq_sum_ex_gen lit n);
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; vm_compute; reflexivity|]); destruct Hin.
Qed.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10 Require Import S_si.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanIntAddrU.

Definition siU_L1 : Z := 0x1a570.
Definition siU_L2 : Z := 0x1a608.
Definition siU_trap : Z := 0x1a68c.
Definition FUEL_siU : nat := 300%nat.

Definition C1_U : sstate :=
  SI.si_state siU_L1 [(13%nat, SI.pB SI.v120); (14%nat, SLit 32); (15%nat, SLit 9)] (SI.pB SI.vI) [] [] SI.inv1 135.

Definition v121 : sv := SVar 121.
Definition v123 : sv := SVar 123.
Definition v124 : sv := SVar 124.
Definition v125 : sv := SVar 125.
Definition inv2U : list sprop :=
  [SPUle SI.vI SI.v120; SPUle SI.v120 v121; SPUlt v121 SI.vE; SPUlt v121 SI.vL; SPUle v121 (SLit SI.two40);
   SPBranch BC_LTU (SI.pB v121) (SI.pB SI.vE); SPUle v125 (SLit SI.imax)].
Definition C2_U : sstate :=
  SI.si_state siU_L2
    [(5%nat, SLit SI.imax); (6%nat, v123); (13%nat, SI.pB v121); (14%nat, v124); (15%nat, v125);
     (16%nat, SLit 9); (17%nat, SLit 10)] (SI.pB SI.v120) [] [] inv2U 135.

Definition cutpcs_siU : list Z := [siU_L1; siU_L2].

Definition trap_leaves (C : sstate) : list sstate :=
  match sym_run segsU FUEL_siU cutpcs_siU C true with
  | Some l => filter (fun S => Z.eqb (ss_pc S) siU_trap) (map lf_state l)
  | None => []
  end.

Definition X_t1 : sstate := Eval vm_compute in nth 0 (trap_leaves C2_U) Pre_si_U.
Definition X_t2 : sstate := Eval vm_compute in nth 1 (trap_leaves C2_U) Pre_si_U.
Definition X_t3 : sstate := Eval vm_compute in nth 2 (trap_leaves C2_U) Pre_si_U.

Lemma trap_leaves_count : length (trap_leaves C2_U) = 3%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma contra_t1 : forall rho, Forall (holds rho) (ss_facts X_t1) -> False.
Proof. intros rho HF. concrete_facts HF. zfacts; lia. Qed.
Lemma contra_t2 : forall rho, Forall (holds rho) (ss_facts X_t2) -> False.
Proof. intros rho HF. concrete_facts HF. zfacts; lia. Qed.
Lemma contra_t3 : forall rho, Forall (holds rho) (ss_facts X_t3) -> False.
Proof. intros rho HF. concrete_facts HF. zfacts; lia. Qed.

Definition cuts_siU : list sstate := [Pre_si_U; C1_U; C2_U].
Definition exits_siU : list sstate := [P_none_U; P_num_U; X_t1; X_t2; X_t3].

Lemma check_siU : check_cfg segsU FUEL_siU cutpcs_siU NF cuts_siU exits_siU = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cuts_siU_strict : existsb ss_lenient cuts_siU = false.
Proof. vm_compute. reflexivity. Qed.

Theorem scan_int_sum_U : scan_int_sum_stmt_U.
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segsU FUEL_siU cutpcs_siU NF cuts_siU exits_siU
           (fun rho' => agree_below NF rho rho') ok K (LQ segsU K NF rho Posts_si_U) Hok).
  - rewrite cuts_siU_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_siU.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]]; revert HagE.
    + apply exit_post. in_nth 0.
    + apply exit_post. in_nth 1.
    + apply (exit_contra segsU ok K (fun r => agree_below NF rho r)). intros r _ HF. exact (contra_t1 r HF).
    + apply (exit_contra segsU ok K (fun r => agree_below NF rho r)). intros r _ HF. exact (contra_t2 r HF).
    + apply (exit_contra segsU ok K (fun r => agree_below NF rho r)). intros r _ HF. exact (contra_t3 r HF).
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition vcuts_siU : list vnode :=
  [mkVN Pre_si_U 30 (SLit 0); mkVN C1_U 20 SI.v120; mkVN C2_U 10 v121].
Definition vexits_siU : list vnode :=
  [mkVN P_none_U 1 vTop; mkVN P_num_U 1 vTop; mkVN X_t1 1 vTop; mkVN X_t2 1 vTop; mkVN X_t3 1 vTop].

Lemma echeck_siU : check_ecfgI segsU FUEL_siU cutpcs_siU NF vcuts_siU vexits_siU = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem scan_int_sum_ex_U : scan_int_sum_ex_stmt_U.
Proof.
  intros K rho.
  change Pre_si_U with (vn_state (mkVN Pre_si_U 30 (SLit 0))).
  apply (cfg_complete_autoI segsU FUEL_siU cutpcs_siU NF vcuts_siU vexits_siU
           (fun rho' => agree_below NF rho rho') K (LQ segsU K NF rho Posts_si_U)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_siU.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]]; revert HgE.
    + apply (eexit_post_I0 segsU K NF rho vcuts_siU Posts_si_U (mkVN P_none_U 1 vTop)). in_nth 0.
    + apply (eexit_post_I0 segsU K NF rho vcuts_siU Posts_si_U (mkVN P_num_U 1 vTop)). in_nth 1.
    + apply (eexit_contra segsU K (fun r => agree_below NF rho r)). intros r _ HF. exact (contra_t1 r HF).
    + apply (eexit_contra segsU K (fun r => agree_below NF rho r)). intros r _ HF. exact (contra_t2 r HF).
    + apply (eexit_contra segsU K (fun r => agree_below NF rho r)). intros r _ HF. exact (contra_t3 r HF).
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

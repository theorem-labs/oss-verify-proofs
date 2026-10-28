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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10 Require Import S_nt.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import NextTokenAddrU.

Definition FUEL_ntU : nat := 200%nat.

Definition regs1U (c : sv) : list (nat * sv) :=
  [(13%nat, NT.pB NT.vE); (14%nat, c); (15%nat, SLit 32); (16%nat, SLit 9)].
Definition C1_U : sstate :=
  add_facts NT.inv1 (NT.nt_state ntU_L1 (regs1U (NT.pB NT.v120)) (NT.pB NT.vI) [] [] [] [] 135).

Definition regs2U (c : sv) : list (nat * sv) :=
  [(5%nat, c); (6%nat, c); (13%nat, NT.pB NT.vE); (14%nat, NT.pB NT.v120);
   (15%nat, SLit 9); (16%nat, SLit 32); (17%nat, SLit 1)].
Definition C2f_U : sstate :=
  NT.nt_state ntU_L2 (regs2U (NT.pB NT.v120)) (NT.pB NT.v120) [mkCell NT.v120 1 (SVar 122)] [] []
    (NT.nonblank 122 ++ NT.inv1) 135.

Definition v123 : sv := SVar 123.
Definition inv2U : list sprop :=
  NT.inv1 ++ [SPUlt NT.v120 v123; SPUlt v123 NT.vE; SPUlt v123 NT.vL; SPUle v123 (SLit NT.two40);
              SPBranch BC_LTU (NT.pB v123) (NT.pB NT.vE)].
Definition C2_U : sstate :=
  add_facts inv2U (NT.nt_state ntU_L2 (regs2U (NT.pB v123)) (NT.pB v123) [] [] [] [] 135).

Definition cuts_ntU : list sstate := [Pre_nt_U; C1_U; C2f_U; C2_U].
Definition exits_ntU : list sstate := [P_nf_U; P_found_U].
Definition cutpcs_ntU : list Z := [ntU_L1; ntU_L2].

Lemma check_ntU : check_cfg segsU FUEL_ntU cutpcs_ntU NF cuts_ntU exits_ntU = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cuts_ntU_strict : existsb ss_lenient cuts_ntU = false.
Proof. vm_compute. reflexivity. Qed.

Theorem next_token_sum_U : next_token_sum_stmt_U.
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segsU FUEL_ntU cutpcs_ntU NF cuts_ntU exits_ntU
           (fun rho' => agree_below NF rho rho') ok K (LQ segsU K NF rho Posts_nt_U) Hok).
  - rewrite cuts_ntU_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_ntU.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[<-|[]]]; revert HagE.
    + apply exit_post. in_nth 0.
    + apply exit_post. in_nth 1.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition vcuts_ntU : list vnode :=
  [mkVN Pre_nt_U 30 (SLit 0); mkVN C1_U 20 NT.v120; mkVN C2f_U 15 NT.v120; mkVN C2_U 10 v123].
Definition vexits_ntU : list vnode := [mkVN P_nf_U 1 vTop; mkVN P_found_U 1 vTop].

Lemma echeck_ntU : check_ecfgI segsU FUEL_ntU cutpcs_ntU NF vcuts_ntU vexits_ntU = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem next_token_sum_ex_U : next_token_sum_ex_stmt_U.
Proof.
  intros K rho.
  change Pre_nt_U with (vn_state (mkVN Pre_nt_U 30 (SLit 0))).
  apply (cfg_complete_autoI segsU FUEL_ntU cutpcs_ntU NF vcuts_ntU vexits_ntU
           (fun rho' => agree_below NF rho rho') K (LQ segsU K NF rho Posts_nt_U)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_ntU.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[<-|[]]]; revert HgE.
    + apply (eexit_post_I0 segsU K NF rho vcuts_ntU Posts_nt_U (mkVN P_nf_U 1 vTop)). in_nth 0.
    + apply (eexit_post_I0 segsU K NF rho vcuts_ntU Posts_nt_U (mkVN P_found_U 1 vTop)). in_nth 1.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

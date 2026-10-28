From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
Import ListNotations.
Open Scope Z_scope.

Module SliceEqAddr.
  Definition se_entry : Z := 0x18350.
  Definition se_loop : Z := 0x18368.
  Definition se_retA : Z := 0x183b4.
  Definition se_retB : Z := 0x183bc.
  Definition se_retC : Z := 0x183c8.
End SliceEqAddr.
Import SliceEqAddr.

Definition vB : sv := SVar 15.
Definition vI : sv := SVar 16.
Definition vL : sv := SVar 17.
Definition vN : sv := SVar 13.
Definition two40 : Z := 2 ^ 40.
Definition two47 : Z := 2 ^ 47.

Definition se_facts : list sprop :=
  [SPUle vI vL; SPUle vN vL; SPUle (SAlu ALU_ADD vI vN) vL; SPUle vL (SLit two40);
   SPUle vB (SLit two47); SPUle (SLit 1) vB].

Definition O_txt : sobj := mkObj vB (SLit 0) vL [] DUnknown.

Definition Pre_se (lit : Z) : sstate :=
  mkSS se_entry (setregs pre_regs [(10%nat, SAlu ALU_ADD vB vI); (12%nat, SLit lit)]) pre_fregs FcsrFrm0 None
       [O_txt] se_facts NF false.

Definition se_post (pc : Z) (a0 : sv) : sstate :=
  mkSS pc (setregs (post_regs NF) [(10%nat, a0)]) pre_fregs FcsrFrm0 None [O_txt] se_facts 144 false.
Definition P_A : sstate := se_post se_retA (SVar 140).
Definition P_B : sstate := se_post se_retB (SLit 0).
Definition P_C : sstate := se_post se_retC (SVar 140).
Definition Posts_se : list leaf := [mkLeaf P_A RsSymJump; mkLeaf P_B RsSymJump; mkLeaf P_C RsSymJump].

Definition slice_eq_sum_stmt (lit : Z) : Prop :=
  forall (ok : world -> Prop) (K : list event -> Model -> Prop) (rho : valuation),
    ok_frame segsU ok K -> triple segsU ok (SP segsU K (Pre_se lit) rho) (LQ segsU K NF rho Posts_se).

Definition slice_eq_sum_ex_stmt (lit : Z) : Prop :=
  forall (K : list event -> Model -> Prop) (rho : valuation),
    etriple segsU (SP segsU K (Pre_se lit) rho) (LQ segsU K NF rho Posts_se).

Definition se_lits : list (Z * nat) :=
  [(0x102f7, 2%nat); (0x1048f, 1%nat); (0x102e6, 1%nat); (0x106a5, 1%nat); (0x104e0, 1%nat);
   (0x10449, 1%nat); (0x104c5, 3%nat); (0x105cc, 6%nat); (0x105d3, 6%nat)].

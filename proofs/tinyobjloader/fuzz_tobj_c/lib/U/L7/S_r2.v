From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
Import ListNotations.
Open Scope Z_scope.

Definition r2_entry : Z := 0x1eb60.
Definition r2_ret : Z := 0x1f724.
Definition r2_frame : Z := 128.

Definition r2_W : sv := SVar 12.
Definition r2_N : sv := SVar 13.
Definition r2_OUT : sv := SVar 14.
Definition r2_P2D : sv := SVar 15.
Definition r2_NXT : sv := SVar 16.
Definition r2_PRV : sv := SVar 17.
Definition r2_RFX : sv := SVar 18.
Definition r2_DEPTH : positive := 19%positive.

Definition r2_two20 : Z := 2 ^ 20.
Definition r2_two47 : Z := 2 ^ 47.

Definition r2_arrK (k : sv) : odefault := DArr 4 k [(0, 4)] [TFle true 0 None r2_N].
Definition r2_outK (k : sv) : odefault :=
  DArr 12 k [(0, 4); (4, 4); (8, 4)] [TFle true 0 None r2_N; TFle true 1 None r2_N; TFle true 2 None r2_N].

Definition r2_O_stk (cells : list cell) : sobj := mkObj (SVar 10) (SVar r2_DEPTH) (SLit 0) cells DUnknown.
Definition r2_O_w : sobj := mkObj r2_W (SLit 0) (SLit 32)
  [mkCell (SLit 0) 8 r2_P2D; mkCell (SLit 8) 8 r2_NXT; mkCell (SLit 16) 8 r2_PRV; mkCell (SLit 24) 8 r2_RFX]
  DUnknown.
Definition r2_O_p2d : sobj := mkObj r2_P2D (SLit 0) (SAlu ALU_SLL r2_N (SLit 4)) [] DUnknown.
Definition r2_O_nxt (d : odefault) : sobj := mkObj r2_NXT (SLit 0) (SAlu ALU_SLL r2_N (SLit 2)) [] d.
Definition r2_O_prv (d : odefault) : sobj := mkObj r2_PRV (SLit 0) (SAlu ALU_SLL r2_N (SLit 2)) [] d.
Definition r2_O_rfx : sobj :=
  mkObj r2_RFX (SLit 0) (SAlu ALU_SRL (SAlu ALU_ADD r2_N (SLit 7)) (SLit 3)) [] DUnknown.
Definition r2_szO : sv := SMd M_MUL (SAlu ALU_ADD r2_N (SLit (-2))) (SLit 12).
Definition r2_O_out (cells : list cell) (d : odefault) : sobj := mkObj r2_OUT (SLit 0) r2_szO cells d.

Definition r2_objs (stkc : list cell) (dn dp : odefault) (outc : list cell) (dout : odefault) : list sobj :=
  [r2_O_stk stkc; r2_O_w; r2_O_p2d; r2_O_nxt dn; r2_O_prv dp; r2_O_rfx; r2_O_out outc dout].

Definition r2_ptr (i : positive) (al : Z) : list sprop :=
  [SPUle (SLit 4096) (SVar i); SPUle (SVar i) (SLit r2_two47); SPAlign i al].
Definition r2_rng (i : positive) : list sprop :=
  [SPUle (SLit 4096) (SVar i); SPUle (SVar i) (SLit r2_two47)].

Definition r2_base_facts : list sprop :=
  [SPUle (SLit 5) r2_N; SPUle r2_N (SLit r2_two20);
   SPBranch BC_GE (SLit (- r2_frame)) (SVar r2_DEPTH);
   SPBranch BC_GE (SVar r2_DEPTH) (SLit (- 2 ^ 40));
   SPAlign 10 4; SPUle (SLit 65536) (SVar 10); SPUle (SVar 10) (SLit r2_two47)] ++
  r2_ptr 12 3 ++ r2_ptr 14 4 ++ r2_ptr 15 4 ++ r2_ptr 16 2 ++ r2_ptr 17 2 ++ r2_rng 18.

Definition r2_fcallee_saved (r : nat) : bool :=
  match r with 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition r2_post_fregs : list sv :=
  map (fun r => if r2_fcallee_saved r then SVar (Pos.of_nat (60 + r)) else SVar (Pos.of_nat (140 + r)))
    (seq 0 32).
Definition r2_NXC : positive := 200%positive.

Definition Pre_r2U : sstate :=
  mkSS r2_entry (setregs pre_regs [(13%nat, SLit 0)]) pre_fregs FcsrFrm0 None
    (r2_objs [] DUnknown DUnknown [] DUnknown) r2_base_facts NF false.

Definition P_r2U : sstate :=
  mkSS r2_ret (post_regs NF) r2_post_fregs FcsrFrm0 None
    (r2_objs [] (r2_arrK r2_N) (r2_arrK r2_N) [] (r2_outK (SAlu ALU_ADD r2_N (SLit (-2)))))
    r2_base_facts r2_NXC false.

Definition Posts_r2U : list leaf := [mkLeaf P_r2U RsSymJump].

Definition r2_sum_stmt_U : Prop :=
  forall (ok : world -> Prop) (K : list event -> Model -> Prop) (rho : valuation),
    ok_frame segsU ok K -> triple segsU ok (SP segsU K Pre_r2U rho) (LQ segsU K NF rho Posts_r2U).

Definition r2_sum_ex_stmt_U : Prop :=
  forall (K : list event -> Model -> Prop) (rho : valuation),
    etriple segsU (SP segsU K Pre_r2U rho) (LQ segsU K NF rho Posts_r2U).

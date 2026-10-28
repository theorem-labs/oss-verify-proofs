From Stdlib Require Import ZArith NArith List Bool PArith Lia Sorting.Permutation.
From stdpp Require Import bitvector base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require Import S_op.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import OptPushAddrU.

Module VRU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9.S_vr.

Definition op_L_U : Z := 0x1be08.
Definition op_J2_U : Z := 0x1be88.
Definition raL_U : Z := 0x1be1c.
Definition ra2_U : Z := 0x1beac.
Definition FUEL_op : nat := 400%nat.
Definition cutpcs_op_U : list Z := [VRU.vr_entry; op_L_U; op_J2_U].

Definition run_of (S : sstate) : list sstate :=
  match sym_run segsU FUEL_op cutpcs_op_U S true with Some ls => map lf_state ls | None => [] end.
Definition leaves_at (S : sstate) (pc : Z) : list sstate := List.filter (fun l => Z.eqb (ss_pc l) pc) (run_of S).
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_op_U 1 end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition F_saved_U : list cell :=
  [OP1.c8 (-80) (SVar 44); OP1.c8 (-72) (SVar 43); OP1.c8 (-64) (SVar 42); OP1.c8 (-56) (SVar 41);
   OP1.c8 (-48) (SVar 40); OP1.c8 (-40) (SVar 39); OP1.c8 (-32) (SVar 38); OP1.c8 (-24) (SVar 29);
   OP1.c8 (-16) (SVar 28); OP1.c8 (-8) (SVar 11)].
Definition body_regs_U (cm : Z) (l : list (nat * sv)) : list sv :=
  setregs OP1.op_xregs
    ([(1%nat, OP1.hx 1); (2%nat, VRU.spo (-80)); (8%nat, OP1.vV); (9%nat, SLit cm); (18%nat, OP1.vVALS);
      (19%nat, OP1.vAL); (20%nat, OP1.vDEF); (21%nat, OP1.vPRES); (22%nat, OP1.vVIDX);
      (23%nat, SLit (2 ^ 64 - 1 - cm)); (24%nat, SAlu ALU_XOR OP1.vDEF (SLit (2 ^ 64 - 1)))] ++ l).
Definition HS_U (cm pc : Z) (regs : list (nat * sv)) (d c k : sv) (dv : positive) (facts : list sprop) : sstate :=
  mkSS pc (body_regs_U cm regs) pre_fregs FcsrFrm0 None
    [OP1.O_F F_saved_U; OP1.O_D; OP1.O_vec4 d c k; O_al_U; O_vals_U cm; O_deflt_U cm; OP1.O_dat d k]
    (facts ++ OP1.vec_facts d c k dv ++ OP1.op_facts) OP1.HNEXT false.

Definition nzB : list (positive * Z * positive) := [(280%positive, 4, 282%positive)].

Definition C_L_U (cm : Z) : sstate := HS_U cm op_L_U [(11%nat, OP1.pC)] OP1.pD OP1.pC OP1.pK 280 [].
Definition C_J2_U (cm : Z) : sstate := HS_U cm op_J2_U [(11%nat, OP1.pC); (24%nat, OP1.hx 24)] OP1.pD OP1.pC OP1.pK 280 [].

Definition tvfB : list sprop := tv_facts (OP1.pD, OP1.kb4 OP1.pK).
Definition TA_L_U (cm : Z) : sstate :=
  HS_U cm VRU.vr_ret [(1%nat, SLit raL_U); (10%nat, SLit 1)] OP1.pD OP1.pC OP1.pK 280
    (SPUle (SAlu ALU_ADD OP1.pC (SLit cm)) OP1.pK :: tvfB).
Definition TF_L_U (cm : Z) : sstate :=
  HS_U cm VRU.vr_ret [(1%nat, SLit raL_U); (10%nat, SLit 0)] OP1.pD OP1.pC OP1.pK 280 [].
Definition TA_2_U (cm : Z) (src : sv) : sstate :=
  HS_U cm VRU.vr_ret [(1%nat, SLit ra2_U); (10%nat, SLit 1); (18%nat, src); (24%nat, OP1.hx 24)] OP1.pD OP1.pC OP1.pK 280
    (SPUle (SAlu ALU_ADD OP1.pC (SLit cm)) OP1.pK :: tvfB).
Definition TF_2_U (cm : Z) : sstate :=
  HS_U cm VRU.vr_ret [(1%nat, SLit ra2_U); (10%nat, SLit 0); (18%nat, OP1.hx 18); (24%nat, OP1.hx 24)]
    OP1.pD OP1.pC OP1.pK 280 [].

Definition E_vrL_U (cm : Z) : sstate := nth 0 (leaves_at (C_L_U cm) VRU.vr_entry) (Pre_op_U cm).
Definition E_vr2v_U (cm : Z) : sstate := nth 0 (leaves_at (C_J2_U cm) VRU.vr_entry) (Pre_op_U cm).
Definition E_vr2d_U (cm : Z) : sstate := nth 1 (leaves_at (C_J2_U cm) VRU.vr_entry) (Pre_op_U cm).

Definition xs_vr : list xform := [XSplit 1 (SLit (-32))].
Definition vr_view_U (E : sstate) : sstate := optS (unbase_obj_at (optS (apply_xforms E xs_vr)) 1 (-32)).
Definition vr_sub_U (E : sstate) : wsub :=
  [(19%positive, SAlu ALU_ADD VRU.vDp (SLit 32)); (15%positive, OP1.pD); (16%positive, OP1.pC);
   (17%positive, OP1.pK); (18%positive, SLit 4)] ++ infer_sub 10 E VRU.Pre_vr.
Definition R_of (E : sstate) : list sobj := optR (entails_fr (vr_view_U E) VRU.Pre_vr (vr_sub_U (vr_view_U E))).

Definition z0 : sv := SLit 0.
Definition cutsE_U (cm : Z) : list edesc :=
  [(Pre_op_U cm, OP1.tv0, (100, z0)); (C_L_U cm, OP1.tvB, (50, OP1.VB OP1.pC (SLit 20)));
   (TA_L_U cm, OP1.tvB, (50, OP1.VB OP1.pC (SLit 18))); (TF_L_U cm, OP1.tvB, (45, z0));
   (C_J2_U cm, OP1.tvB, (40, z0)); (TA_2_U cm OP1.vVALS, OP1.tvB, (30, z0));
   (TA_2_U cm OP1.vDEF, OP1.tvB, (30, z0)); (TF_2_U cm, OP1.tvB, (30, z0))].
Definition exitsE_U (cm : Z) : list edesc :=
  [(E_vrL_U cm, OP1.tvB, (50, OP1.VB OP1.pC (SLit 19))); (E_vr2v_U cm, OP1.tvB, (35, z0));
   (E_vr2d_U cm, OP1.tvB, (35, z0)); (P_ret_U cm, OP1.tvP, (0, z0))].

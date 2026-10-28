From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract Glue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform ZeroObj
  CellTile TobjJV TobjJVx TobjArena TobjJVA TobjJVAx TobjJVAs ArenaDestroy FuzzOneIface.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_load__G1.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4 Require Import ZeroKeep.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation segs := U.Init.segsU.
Local Abbreviation P0_lo := P.Lib_load__G1.Lib_load_obj_defs.P0_lo.

Definition NP_lo : positive := ss_next Pre_lo_U.
Definition P_ok_lo : sstate := fst (nth 0 PDA_lo_U (Pre_lo_U, ([], ANone))).
Definition P_err_lo : sstate := fst (nth 1 PDA_lo_U (Pre_lo_U, ([], ANone))).

Definition fz_loop : Z := 0x13a08.
Definition fz_reto : Z := 0x19148.
Definition fz_rete : Z := 0x19130.
Definition FUEL_fz : nat := 2000%nat.
Definition cutpcs_fz : list Z := [ss_pc Pre_lo_U; fz_loop; ec_free EC_U].

Definition Pre_fz : sstate := Pre_fuzz FZ_U.
Definition run_of (S : sstate) : list sstate :=
  match sym_run segs FUEL_fz cutpcs_fz S true with Some ls => map lf_state ls | None => [] end.
Definition leaves_at (S : sstate) (pc : Z) : list sstate := List.filter (fun x => Z.eqb (ss_pc x) pc) (run_of S).
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_fz end.

Definition E_lo : sstate := Eval vm_compute in nth 0 (leaves_at Pre_fz (ss_pc Pre_lo_U)) Pre_fz.
Definition spm : sv := SAlu ALU_ADD (SVar 10) (SLit (-368)).
Definition lo_facts : list sprop :=
  [SPUle (SAlu ALU_ADD (SVar 30) (SLit 16384)) spm; SPUle (SVar 30) (SAlu ALU_ADD (SVar 10) (SLit (-360)))].
Definition E_lof : sstate := add_facts lo_facts E_lo.
Definition E_lo1 : sstate := Eval vm_compute in
  optS (apply_xforms E_lof [XSplit 0 (SLit (-360)); XSplit 1 (SLit (-216)); XSplit 2 (SLit (-8)); XSplit 4 (SLit (-1856))]).
Definition E_lo1z : sstate := Eval vm_compute in optS (zero_keep_at E_lo1 1).
Definition E_loA : sstate := Eval vm_compute in optS (unbase_obj_at E_lo1z 1 (-360)).
Definition E_loB : sstate := Eval vm_compute in optS (unbase_obj_at E_loA 2 (-216)).
Definition E_lo2 : sstate := Eval vm_compute in optS (unbase_obj_at E_loB 4 (-1856)).
Definition E_lo3 : sstate := Eval vm_compute in optS (recell_at E_lo2 1 0 4294967295).
Definition s_lo : wsub := (19%positive, SAlu ALU_ADD (SVar 15) (SLit 1856)) :: infer_sub 10 E_lo3 Pre_lo_U.
Definition R_lo : list sobj := Eval vm_compute in optR (entails_fr E_lo3 Pre_lo_U s_lo).

Definition T_ok : sstate := Eval vm_compute in T_afterN NP_lo E_lo3 s_lo R_lo P_ok_lo.
Definition T_err : sstate := Eval vm_compute in T_afterN NP_lo E_lo3 s_lo R_lo P_err_lo.
Definition T_ok0 : sstate := Eval vm_compute in optS (apply_xforms T_ok [XSplit 0 (SLit (-64))]).
Definition T_ok1 : sstate := Eval vm_compute in optS (unbase_obj_at T_ok0 0 (-64)).
Definition isub_ok : wsub := import_sub s_lo NP_lo P_ok_lo (ss_next E_lo3).
Definition xARi : sv := Eval vm_compute in wsub_get isub_ok 100%positive.
Definition pHi : sv := Eval vm_compute in wsub_get isub_ok 101%positive.
Definition tv_ok : list (sv * sv) := [(xARi, SLit 64)].
Definition am_ok : amode := AHead pHi.

Definition pB : sv := SVar 400.  Definition pNn : positive := 401.  Definition pNX : sv := SVar 401.  Definition vG : sv := SVar 404.
Definition X_P0 : sstate := Eval vm_compute in nth 0 (leaves_at T_ok1 fz_loop) Pre_fz.
Definition X_far0 : sstate := Eval vm_compute in nth 0 (leaves_at T_ok1 (ec_free EC_U)) Pre_fz.
Definition X_rete : sstate := Eval vm_compute in nth 0 (leaves_at T_err fz_rete) Pre_fz.
Definition C_L : sstate :=
  mkSS fz_loop (list_set (list_set (list_set (ss_regs X_P0) 21 pB) 10 (SVar 405)) 1 (SVar 406)) (ss_fregs X_P0)
    FcsrFrm0 None (ss_objs X_P0 ++ [popped pB pNn]) (open_facts pB pNn ++ ghost_facts 404 ++ ss_facts X_P0) 407 false.

Definition is_pay (o : sobj) : bool :=
  sv_eqb (ob_base o) (SVar 12) && sv_eqb (ob_lo o) (SLit 0) && sv_eqb (ob_hi o) (SVar 13).
Definition tv_L : list (sv * sv) := pop_tv pB pNn tv_ok.
Definition am_L : amode := AHeadN pNX vG.
Definition E_fd : sstate := Eval vm_compute in nth 0 (leaves_at C_L (ec_free EC_U)) Pre_fz.
Definition s_fd : wsub := infer_sub 10 E_fd (Pre_free EC_U).
Definition R_fd : list sobj := Eval vm_compute in optR (entails_fr E_fd (Pre_free EC_U) s_fd).
Definition T_fd : sstate := Eval vm_compute in T_after E_fd s_fd R_fd (L_free EC_U).
Definition X_P : sstate := Eval vm_compute in nth 0 (leaves_at T_fd fz_loop) Pre_fz.
Definition X_far1 : sstate := Eval vm_compute in nth 0 (leaves_at T_fd (ec_free EC_U)) Pre_fz.

Definition E_FAR : sstate :=
  mkSS (ss_pc X_far0) (ss_regs X_far0) (ss_fregs X_far0) FcsrFrm0 None (ss_objs X_far0) (ss_facts T_ok1)
    (Pos.add (ss_next X_far0) 1) false.
Definition am0 : amode := AHead (SLit 0).
Definition s_far1 : wsub := infer_sub NF X_far1 E_FAR.
Definition s_fa : wsub := infer_sub 10 E_FAR (Pre_free EC_U).
Definition R_fa : list sobj := Eval vm_compute in optR (entails_fr E_FAR (Pre_free EC_U) s_fa).
Definition T_far : sstate := Eval vm_compute in T_after E_FAR s_fa R_fa (L_free EC_U).
Definition X_ret : sstate := Eval vm_compute in nth 0 (leaves_at T_far fz_reto) Pre_fz.

Definition X_P0f : sstate := add_facts [SPNot (SPBranch BC_EQ pHi (SLit 0))] X_P0.
Definition X_P01 : sstate := lenN_state X_P0f.
Definition X_P02 : sstate := Eval vm_compute in pop_stateN X_P01 pHi (SVar (ss_next X_P0)).
Definition s_P0 : wsub :=
  [(404%positive, SVar (ss_next X_P01 + 3)); (405%positive, nth 10 (ss_regs X_P0) (SLit 0))].

Definition X_Pf : sstate := add_facts [SPNot (SPBranch BC_EQ pNX (SLit 0))] X_P.
Definition X_P2 : sstate := Eval vm_compute in pop_stateN X_Pf pNX vG.
Definition s_P : wsub :=
  [(404%positive, SVar (ss_next X_Pf + 3)); (405%positive, nth 10 (ss_regs X_P) (SLit 0))].

Definition ret_xforms : list xform :=
  [XRebase 0; XRebase 1; XRebase 2; XRebase 3; XRebase 5; XSelect [6; 5; 3; 7; 2; 0; 1; 4]%nat;
   XMerge 0; XMerge 0; XMerge 0; XMerge 1; XMerge 1].
Definition X_ret1 : sstate := Eval vm_compute in optS (apply_xforms X_ret ret_xforms).
Definition X_ret2 : sstate := Eval vm_compute in optS (unbase_obj_at X_ret1 1 (-368)).
Definition rete_xforms : list xform :=
  [XRebase 0; XRebase 1; XRebase 2; XRebase 4; XSelect [5; 4; 2; 6; 1; 0; 3]%nat;
   XMerge 0; XMerge 0; XMerge 0; XMerge 1].
Definition X_rete1 : sstate := Eval vm_compute in optS (apply_xforms X_rete rete_xforms).
Definition X_rete2 : sstate := Eval vm_compute in optS (unbase_obj_at X_rete1 1 (-368)).
Definition L_reto : sstate := L_fuzz FZ_U fz_reto.
Definition L_rete : sstate := L_fuzz FZ_U fz_rete.
Definition s_ret : wsub := infer_sub NF X_ret2 L_reto.
Definition s_rete : wsub := infer_sub NF X_rete2 L_rete.

Definition z0 : sv := SLit 0.
Definition VGp (k : Z) : sv := SAlu ALU_ADD vG (SLit k).
Definition VGm (k : Z) : sv := SAlu ALU_SUB vG (SLit k).
Definition tv00 : list (sv * sv) := [].
Definition cutsE : list aedesc :=
  [(Pre_fz, (tv00, ANone), (100, z0)); (T_ok1, (tv_ok, am_ok), (60, z0)); (T_err, (tv00, ANone), (60, z0));
   (C_L, (tv_L, am_L), (40, VGp 2)); (T_fd, (tv_ok, am_L), (40, VGp 0)); (T_far, (tv00, am0), (20, z0))].
Definition exitsE : list aedesc :=
  [(E_lo, (tv00, ANone), (80, z0)); (X_rete, (tv00, ANone), (10, z0)); (X_P0, (tv_ok, am_ok), (50, z0));
   (X_far1, (tv_ok, am_L), (30, z0)); (X_far0, (tv_ok, am_ok), (55, z0)); (E_fd, (tv_L, am_L), (40, VGp 1));
   (X_P, (tv_ok, am_L), (40, VGm 1)); (X_ret, (tv00, am0), (10, z0))].


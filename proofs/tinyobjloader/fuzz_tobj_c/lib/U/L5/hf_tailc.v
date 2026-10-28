From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjUnbase ObjXform TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs hf_tail.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes.
Import HfAddrU.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module VRU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9.S_vr.

Definition tail_cps : list Z := [vrU_entry; pcU_entry; pgU_entry; pc_L14_U].

Definition tail_leaf (S : sstate) (pc : Z) : sstate :=
  match sym_run segsU FUEL_U tail_cps S true with
  | Some ls => nth 0 (filter (fun st => Z.eqb (ss_pc st) pc) (map lf_state ls)) S
  | None => S
  end.

Definition svar_idx (v : sv) : positive := match v with SVar n => n | _ => 1%positive end.

Definition xs_t1 : list xform := [XSplit 1 (SLit (-32))].
Definition xs_t0 : list xform := [XSplit 0 (SLit (-32))].

Definition E2_of (xs : list xform) (i : nat) (E : sstate) : sstate :=
  match TobjJVx.norm_xu xs i (-32) E with Some x => x | None => E end.

Definition s_site (E2 : sstate) (v : sv * sv * sv) (esz : Z) : wsub :=
  [(19%positive, SAlu ALU_ADD xD (SLit 32)); (15%positive, t_d v); (16%positive, t_c v);
   (17%positive, t_k v); (18%positive, SLit esz)] ++ infer_sub 10 E2 VRU.Pre_vr.

Definition nz_site (v : sv * sv * sv) (esz : Z) : list (positive * Z * positive) :=
  [(svar_idx (t_d v), esz, svar_idx (t_k v))].

Definition post_of (E2 : sstate) (s : wsub) (nzk : list (positive * Z * positive)) (keep : bool) : sstate :=
  match entails_fr E2 VRU.Pre_vr s with
  | Some R =>
      let T := if keep then add_facts (TobjJVx.nz_facts nzk) (T_afterN NF E2 s R VRU.P_keep)
               else T_afterN NF E2 s R VRU.P_fail in
      match TobjJVx.norm_xu (xs_keep (nobj T)) 0 (-272) T with Some x => x | None => E2 end
  | None => E2
  end.

Definition nzU_mi := Eval vm_compute in nz_site mi1 12.
Definition nzU_fv := Eval vm_compute in nz_site fv1 4.
Definition nzU_mm := Eval vm_compute in nz_site mm1 4.
Definition nzU_sg := Eval vm_compute in nz_site sg1 4.

Definition EU_mi : sstate := Eval vm_compute in tail_leaf L14_U vrU_entry.
Definition E2U_mi : sstate := Eval vm_compute in E2_of xs_t1 1 EU_mi.
Definition sU_mi : wsub := Eval vm_compute in s_site E2U_mi mi1 12.
Definition AU_mi : sstate := Eval vm_compute in post_of E2U_mi sU_mi nzU_mi true.
Definition FU_mi : sstate := Eval vm_compute in post_of E2U_mi sU_mi nzU_mi false.

Definition EU_fv : sstate := Eval vm_compute in tail_leaf AU_mi vrU_entry.
Definition E2U_fv : sstate := Eval vm_compute in E2_of xs_t0 0 EU_fv.
Definition sU_fv : wsub := Eval vm_compute in s_site E2U_fv fv1 4.
Definition AU_fv : sstate := Eval vm_compute in post_of E2U_fv sU_fv nzU_fv true.
Definition FU_fv : sstate := Eval vm_compute in post_of E2U_fv sU_fv nzU_fv false.

Definition EU_mm : sstate := Eval vm_compute in tail_leaf AU_fv vrU_entry.
Definition E2U_mm : sstate := Eval vm_compute in E2_of xs_t0 0 EU_mm.
Definition sU_mm : wsub := Eval vm_compute in s_site E2U_mm mm1 4.
Definition AU_mm : sstate := Eval vm_compute in post_of E2U_mm sU_mm nzU_mm true.
Definition FU_mm : sstate := Eval vm_compute in post_of E2U_mm sU_mm nzU_mm false.

Definition EU_sg : sstate := Eval vm_compute in tail_leaf AU_mm vrU_entry.
Definition E2U_sg : sstate := Eval vm_compute in E2_of xs_t0 0 EU_sg.
Definition sU_sg : wsub := Eval vm_compute in s_site E2U_sg sg1 4.
Definition AU_sg : sstate := Eval vm_compute in post_of E2U_sg sU_sg nzU_sg true.
Definition FU_sg : sstate := Eval vm_compute in post_of E2U_sg sU_sg nzU_sg false.

Definition EU_bk : sstate := Eval vm_compute in tail_leaf AU_sg pc_L14_U.
Definition cU_bk : sprop := Eval vm_compute in
  match sprop_subst (infer_sub NP EU_bk L14_U) (tr_bound pI) with Some p => p | None => tr_bound pI end.

Definition tail_cuts : list edesc :=
  [(L14_U, tvH, L14_rv); (AU_mi, tvH, (40, VL 7)); (AU_fv, tvH, (40, VL 5)); (AU_mm, tvH, (40, VL 3));
   (AU_sg, tvH, (40, VL 1)); (FU_mi, tvH, (38, z0)); (FU_fv, tvH, (38, z0)); (FU_mm, tvH, (38, z0));
   (FU_sg, tvH, (38, z0))].

Definition tail_exits : list edesc :=
  [(EU_mi, tvH, (40, VL 8)); (EU_fv, tvH, (40, VL 6)); (EU_mm, tvH, (40, VL 4)); (EU_sg, tvH, (40, VL 2));
   (EU_bk, tvH, (40, VL 0))].

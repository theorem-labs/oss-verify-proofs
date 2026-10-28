From Stdlib Require Import ZArith List Bool PArith.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Code Str_memcpy__G1.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr S_aa S_vp.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require S_vf S_ad.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require Import S_fs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require fs_st.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L12 Require Import fsB_st.
Import ListNotations.
Open Scope Z_scope.

(* fs tail from t-mal1's joins J1236 (vp call, memcpy of the shape into the slot, return 1) and J1344 (the shared
   failure block); the cut states after the vp call are in Pre_fs's object layout so the returns match Posts_fs *)
Definition cutpcs_T : list Z := [S_vp.vp_entry; mc_entry].
Definition FUEL_T : nat := 3000%nat.
Definition runT (S : sstate) : list sstate :=
  match sym_run segsU FUEL_T cutpcs_T S true with Some ls => map lf_state ls | None => [] end.
Definition atT (S : sstate) (pc : Z) : list sstate := List.filter (fun l => Z.eqb (ss_pc l) pc) (runT S).
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

(* vp call: vp's frame [sp-16, sp) and stack below carved from the three stack pieces of the vf-call layout *)
Definition hVP : positive := 99.
Definition xs_vp : list xform := [XRebase 1; XRebase 2; XRebase 3; XMerge 1; XMerge 1; XSplit 1 (SLit (-208))].
Definition E_vp0 : sstate := Eval vm_compute in nth 0 (atT J1236 S_vp.vp_entry) Pre_fs.
Definition E_vp1 : sstate := Eval vm_compute in optS (apply_xforms E_vp0 xs_vp).
Definition E_vp2 : sstate := Eval vm_compute in optS (unbase_obj_at E_vp1 2 (-192)).
Definition E_vp : sstate := Eval vm_compute in optS (unbase_obj_at E_vp2 1 (-208)).
Definition s_vp : wsub := Eval vm_compute in
  [(hVP, headv E_vp); (19%positive, SAlu ALU_ADD (SVar 19) (SLit 16)); (15%positive, cellv E_vp 448);
   (16%positive, cellv E_vp 456); (17%positive, cellv E_vp 464); (18%positive, cellv E_vp 472)] ++ infer_sub 10 E_vp S_vp.Pre_vp.
Definition R_vp : list sobj := Eval vm_compute in optR (entails_fr E_vp S_vp.Pre_vp s_vp).
Definition T_vpf : sstate := Eval vm_compute in T_afterN NF E_vp s_vp R_vp S_vp.P_push_fail.
Definition T_vpk : sstate := Eval vm_compute in T_afterN NF E_vp s_vp R_vp S_vp.P_push_keep.
Definition T_vpg : sstate := Eval vm_compute in T_afterN NF E_vp s_vp R_vp S_vp.P_push_grown.

(* back to Pre_fs's layout: vp's stack pieces [O_Dp; ...; O_Fp] merged and split at sp-48 into O_DD and O_AF *)
Definition sel_fp : list nat := ([0; 4; 1; 2; 3] ++ seq 5 25)%nat.
Definition fs_lay0 (X : sstate) : sstate :=
  optS (ub (apply_xforms (optS (unbase_obj_at X 0 16)) [XSelect sel_fp; XMerge 0; XSplit 0 (SLit (-48))]) 0 (-48)).
(* vp's fail post and its keep/grown posts list their objects in different orders *)
Definition p_f : list nat := Eval vm_compute in cperm Pre_fs (fs_lay0 T_vpf).
Definition p_k : list nat := Eval vm_compute in cperm Pre_fs (fs_lay0 T_vpk).
(* callees hand back the builder's vector objects based at their own address (base vb+o, lo 0); Pre_fs has them
   based at the builder (base vb, lo o): rebase them *)
Definition rebased (X : sstate) : list nat :=
  map fst (filter (fun p => match ob_base (snd p) with SAlu ALU_ADD (SVar 12) (SLit _) => true | _ => false end)
    (combine (seq 0 (length (ss_objs X))) (ss_objs X))).
Definition xs_reb (X : sstate) : list xform := map XRebase (rebased X).
Definition sel_X (X : sstate) (p : list nat) : sstate := optS (apply_xforms (fs_lay0 X) [XSelect p]).
Definition to_fs (X : sstate) (p : list nat) : sstate := let Y := sel_X X p in optS (apply_xforms Y (xs_reb Y)).

Definition d_sh : sv := SVar 110.
Definition k_sh : sv := SVar 112.
Definition tv_sh : sv * sv := (d_sh, SMd M_MUL (SLit 128) k_sh).
Definition C_vpf : sstate := Eval vm_compute in to_fs T_vpf p_f.
Definition C_vpk : sstate := Eval vm_compute in to_fs (add_facts (tv_facts tv_sh) T_vpk) p_k.
Definition C_vpg : sstate := Eval vm_compute in to_fs T_vpg p_k.

(* memcpy (slot, sp-184, 128): the slot [d+128c, +128) carved out of the sh data, the source [sp-184, sp-56) out of
   fs's frame *)
Definition reg (S : sstate) (r : nat) : sv := nth r (ss_regs S) (SLit 0).
Definition slot_d (E : sstate) : sv := match reg E 10 with SAlu ALU_ADD d _ => d | _ => SLit 0 end.
Definition slot_o (E : sstate) : sv := match reg E 10 with SAlu ALU_ADD _ o => o | _ => SLit 0 end.
Fixpoint idx_base (b : sv) (os : list sobj) (i : nat) : nat :=
  match os with [] => 1000%nat | o :: t => if sv_eqb (ob_base o) b then i else idx_base b t (Datatypes.S i) end.
Definition i_dat (E : sstate) : nat := idx_base (slot_d E) (ss_objs E) 0.
Definition dat_hi (E : sstate) : sv := ob_hi (nth (i_dat E) (ss_objs E) O_AF).
Definition slot_end (E : sstate) : sv := SAlu ALU_ADD (slot_o E) (SLit 128).
Definition sfacts (E : sstate) : list sprop := [SPUle (slot_o E) (dat_hi E); SPUle (slot_end E) (dat_hi E)].
Definition xs_mc (E : sstate) : list xform :=
  [XSplit 0 (SLit (-184)); XSplit 1 (SLit (-56)); XSplit (i_dat E + 2) (slot_o E); XSplit (i_dat E + 3) (slot_end E)].
Definition slot_obj (E : sstate) : sobj := mkObj (reg E 10) (SLit 0) (SLit 128) [] DUnknown.
Definition carve1 (E : sstate) : sstate := optS (apply_xforms (add_facts (sfacts E) E) (xs_mc E)).
Definition carve2 (E : sstate) : sstate := optS (unbase_obj_at (carve1 E) 1 (-184)).
Definition carve (E : sstate) : sstate := reshape_obj_at (carve2 E) (i_dat E + 3) (slot_obj E).

Module MC := U.Str_memcpy__G1.Str_memcpy.
Definition E_mk0 : sstate := Eval vm_compute in nth 0 (atT C_vpk mc_entry) Pre_fs.
Definition E_mg0 : sstate := Eval vm_compute in nth 0 (atT C_vpg mc_entry) Pre_fs.
Definition E_mk : sstate := Eval vm_compute in carve E_mk0.
Definition E_mg : sstate := Eval vm_compute in carve E_mg0.
Definition s_mk : wsub := Eval vm_compute in infer_sub 10 E_mk MC.Pre_memcpy.
Definition s_mg : wsub := Eval vm_compute in infer_sub 10 E_mg MC.Pre_memcpy.
Definition R_mk : list sobj := Eval vm_compute in optR (entails_fr E_mk MC.Pre_memcpy s_mk).
Definition R_mg : list sobj := Eval vm_compute in optR (entails_fr E_mg MC.Pre_memcpy s_mg).

(* memcpy's returns: back to the carve layout, slot merged into the sh data, source merged into fs's frame *)
Definition T_mc (E : sstate) (s : wsub) (R : list sobj) (L : leaf) : sstate :=
  add_facts (ss_facts E) (import_post s (ss_next MC.Pre_memcpy) (lf_state L) (ss_next E) R).
Definition mid_obj (E : sstate) : sobj := mkObj (slot_d E) (slot_o E) (slot_end E) [] DUnknown.
Definition unc1 (E0 E X : sstate) : sstate := optS (apply_xforms X [XSelect (cperm E X)]).
Definition unc2 (E0 E X : sstate) : sstate := reshape_obj_at (unc1 E0 E X) (i_dat E0 + 3) (mid_obj E0).
Definition unc (E0 E X : sstate) : sstate :=
  optS (apply_xforms (unc2 E0 E X) [XMerge (i_dat E0 + 2); XMerge (i_dat E0 + 2); XRebase 1; XMerge 0; XMerge 0]).
Definition L_mcA : leaf := nth 0 MC.Posts_memcpy (mkLeaf Pre_fs RsSymJump).
Definition L_mcB : leaf := nth 1 MC.Posts_memcpy (mkLeaf Pre_fs RsSymJump).
Definition T_mkA : sstate := Eval vm_compute in T_mc E_mk s_mk R_mk L_mcA.
Definition T_mkB : sstate := Eval vm_compute in T_mc E_mk s_mk R_mk L_mcB.
Definition T_mgA : sstate := Eval vm_compute in T_mc E_mg s_mg R_mg L_mcA.
Definition T_mgB : sstate := Eval vm_compute in T_mc E_mg s_mg R_mg L_mcB.
Definition C_mkA : sstate := Eval vm_compute in unc E_mk0 E_mk T_mkA.
Definition C_mkB : sstate := Eval vm_compute in unc E_mk0 E_mk T_mkB.
Definition C_mgA : sstate := Eval vm_compute in unc E_mg0 E_mg T_mgA.
Definition C_mgB : sstate := Eval vm_compute in unc E_mg0 E_mg T_mgB.

Definition E_mk2 : sstate := Eval vm_compute in carve1 E_mk0.
Definition E_mk3 : sstate := Eval vm_compute in carve2 E_mk0.
Definition E_mg2 : sstate := Eval vm_compute in carve1 E_mg0.
Definition E_mg3 : sstate := Eval vm_compute in carve2 E_mg0.
Definition U_mkA1 : sstate := Eval vm_compute in unc1 E_mk0 E_mk T_mkA.
Definition U_mkB1 : sstate := Eval vm_compute in unc1 E_mk0 E_mk T_mkB.
Definition U_mgA1 : sstate := Eval vm_compute in unc1 E_mg0 E_mg T_mgA.
Definition U_mgB1 : sstate := Eval vm_compute in unc1 E_mg0 E_mg T_mgB.
Definition xs_unc (E0 : sstate) : list xform := [XMerge (i_dat E0 + 2); XMerge (i_dat E0 + 2); XRebase 1; XMerge 0; XMerge 0].

Definition amT : amode := AHead (SVar h1236).
Definition tv_k : list (sv * sv) := Eval vm_compute in firstn 7 tv0 ++ skipn 8 tv0.
Definition tv_p : list (sv * sv) := Eval vm_compute in firstn 1 (skipn 7 tv0).
Definition tv_gp : list (sv * sv) := Eval vm_compute in
  import_tv (import_sub s_vp NF S_vp.P_push_grown (ss_next E_vp)) S_vr.tv_post.
Definition tvG : list (sv * sv) := Eval vm_compute in firstn 7 tv0 ++ tv_gp ++ skipn 8 tv0.

Definition z0 : sv := SLit 0.
Definition cutsE : list aedesc :=
  [ (J1236, (tv0, amT), (100, z0));
    (C_vpf, (tv0, amT), (90, z0));
    (C_vpk, (tv0, amT), (90, z0));
    (C_vpg, (tvG, amT), (90, z0));
    (C_mkA, (tv0, amT), (80, z0));
    (C_mkB, (tv0, amT), (80, z0));
    (C_mgA, (tvG, amT), (80, z0));
    (C_mgB, (tvG, amT), (80, z0)) ].
Definition exitsE : list aedesc :=
  [ (E_vp0, (tv0, amT), (95, z0));
    (E_mk0, (tv0, amT), (85, z0));
    (E_mg0, (tvG, amT), (85, z0));
    (P_fail, (tv0, amq), (0, z0));
    (P_failz, (tv0, amq), (0, z0));
    (P_ok, (tvOK, amq), (0, z0)) ].

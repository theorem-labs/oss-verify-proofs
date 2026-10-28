From Stdlib Require Import ZArith List Bool PArith.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Code.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr S_aa S_vp.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require S_vf S_ad.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require Import S_fs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require fs_st.
Import ListNotations.
Open Scope Z_scope.

Definition off (k : Z) : Z := fs_entry + k.
Definition mc_entry : Z := U.Code.StrAddr.memcpy_entry.
Definition cps : list Z := [S_aa.aa_entry; S_vf.vf_entry; S_vp.vp_entry; S_ad.ad_entry; mc_entry; off 892; off 932; off 1236; off 1344; off 1036].
Definition run (S : sstate) := match sym_run segsU 3000 cps S true with Some l => l | None => [] end.
Definition leaves_at (S : sstate) (pc : Z) : list sstate := List.filter (fun l => Z.eqb (ss_pc l) pc) (map lf_state (run S)).
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_fs end.
Definition reg (S : sstate) (r : nat) : sv := nth r (ss_regs S) (SLit 0).
Definition sel_swap (n i : nat) : list nat := firstn i (seq 0 n) ++ [Datatypes.S i; i] ++ skipn (i + 2) (seq 0 n).
Definition xs_vf : list xform :=
  [XRebase 1; XRebase 2; XRebase 2; XSelect (sel_swap 30 1); XMerge 1; XSplit 1 (SLit (-272)); XSplit 2 (SLit (-224))].
Definition ub (o : option sstate) (i : nat) (c : Z) : option sstate := match o with Some X => unbase_obj_at X i c | None => None end.

Definition objkey (o : sobj) : sv * sv :=
  (fs_st.nsv (SAlu ALU_ADD (ob_base o) (ob_lo o)), fs_st.nsv (SAlu ALU_ADD (ob_base o) (ob_hi o))).
Definition key_eqb (a b : sv * sv) : bool := let '(a1, a2) := a in let '(b1, b2) := b in sv_eqb a1 b1 && sv_eqb a2 b2.
Fixpoint index_of (k : sv * sv) (os : list sobj) (i : nat) : nat :=
  match os with [] => 1000%nat | o :: t => if key_eqb k (objkey o) then i else index_of k t (Datatypes.S i) end.
Definition cperm (Ref X : sstate) : list nat := map (fun o => index_of (objkey o) (ss_objs X) 0) (ss_objs Ref).
Definition cellv (X : sstate) (o : Z) : sv :=
  match find (fun ob => sv_eqb (ob_base ob) (SVar 12) && match ob_lo ob, ob_hi ob with SLit l, SLit h => Z.leb l o && Z.ltb o h | _, _ => false end) (ss_objs X) with
  | Some ob => match find (fun c => sv_eqb (c_off c) (SLit o)) (ob_cells ob) with Some c => c_val c | None => SLit (-1) end
  | None => SLit (-2) end.
Definition headv (X : sstate) : sv :=
  match find (fun ob => sv_eqb (ob_base ob) (SVar 101)) (ss_objs X) with
  | Some ob => match find (fun c => sv_eqb (c_off c) (SLit 48)) (ob_cells ob) with Some c => c_val c | None => SLit (-1) end
  | None => SLit (-2) end.
Definition s_vec (X : sstate) (b : Z) : wsub :=
  [(19%positive, SAlu ALU_ADD (SVar 19) (SLit 32)); (15%positive, cellv X b); (16%positive, cellv X (b + 8));
   (17%positive, cellv X (b + 16)); (18%positive, cellv X (b + 24))].
Definition joinA (pc : Z) (Ls : list sstate) : sstate := fs_st.au_states pc (nth 0 Ls Pre_fs) (tl Ls).

(* vf call 1 from the join at +852: frame [vf frame 32 | aa frame 48 | below] carved from fs's O_AF/O_DD *)
Definition J := fs_st.J852.
Definition E1 : sstate := Eval vm_compute in nth 0 (leaves_at J S_vf.vf_entry) Pre_fs.
Definition E1v : sstate := Eval vm_compute in optS (ub (ub (ub (apply_xforms E1 xs_vf) 3 (-192)) 2 (-224)) 1 (-272)).
Definition f272 : sprop := SPUle (SVar 30) (SAlu ALU_ADD (SVar 10) (SLit (-272))).
Definition E1f : sstate := Eval vm_compute in add_facts [f272] E1v.
Definition s_v1 : wsub := Eval vm_compute in s_vec E1f 624 ++ infer_sub 10 E1f S_vf.Pre_vf.
Definition R_v1 : list sobj := Eval vm_compute in match entails_fr E1f S_vf.Pre_vf s_v1 with Some R => R | None => [] end.
Definition T1z : sstate := Eval vm_compute in T_afterN NF E1f s_v1 R_v1 S_vf.P_zero.
Definition T1f : sstate := Eval vm_compute in T_afterN NF E1f s_v1 R_v1 S_vf.P_fail.
Definition T1o : sstate := Eval vm_compute in T_afterN NF E1f s_v1 R_v1 S_vf.P_ok.
(* canonical layout = E1f's object order *)
Definition p1 : list nat := Eval vm_compute in cperm E1f T1o.
Definition canon (X : sstate) (p : list nat) : sstate := optS (apply_xforms X [XSelect p]).
Definition C1z : sstate := Eval vm_compute in canon T1z p1.
Definition C1f : sstate := Eval vm_compute in canon T1f p1.
Definition C1o : sstate := Eval vm_compute in canon T1o p1.
Definition J892 : sstate := Eval vm_compute in joinA (off 892) (leaves_at C1z (off 892) ++ leaves_at C1f (off 892) ++ leaves_at C1o (off 892)).
Definition E2 : sstate := Eval vm_compute in nth 0 (leaves_at J892 S_vf.vf_entry) Pre_fs.
Definition s_v2 : wsub := Eval vm_compute in s_vec E2 656 ++ infer_sub 10 E2 S_vf.Pre_vf.
Definition R_v2 : list sobj := Eval vm_compute in match entails_fr E2 S_vf.Pre_vf s_v2 with Some R => R | None => [] end.
Definition T2z : sstate := Eval vm_compute in T_afterN NF E2 s_v2 R_v2 S_vf.P_zero.
Definition T2f : sstate := Eval vm_compute in T_afterN NF E2 s_v2 R_v2 S_vf.P_fail.
Definition T2o : sstate := Eval vm_compute in T_afterN NF E2 s_v2 R_v2 S_vf.P_ok.
Definition p2 : list nat := Eval vm_compute in cperm E1f T2o.
Definition C2z : sstate := Eval vm_compute in canon T2z p2.
Definition C2f : sstate := Eval vm_compute in canon T2f p2.
Definition C2o : sstate := Eval vm_compute in canon T2o p2.
Definition J932 : sstate := Eval vm_compute in joinA (off 932) (leaves_at C2z (off 932) ++ leaves_at C2f (off 932) ++ leaves_at C2o (off 932)).
Definition E3 : sstate := Eval vm_compute in nth 0 (leaves_at J932 S_vf.vf_entry) Pre_fs.
Definition s_v3 : wsub := Eval vm_compute in s_vec E3 688 ++ infer_sub 10 E3 S_vf.Pre_vf.
Definition R_v3 : list sobj := Eval vm_compute in match entails_fr E3 S_vf.Pre_vf s_v3 with Some R => R | None => [] end.
Definition T3z : sstate := Eval vm_compute in T_afterN NF E3 s_v3 R_v3 S_vf.P_zero.
Definition T3f : sstate := Eval vm_compute in T_afterN NF E3 s_v3 R_v3 S_vf.P_fail.
Definition T3o : sstate := Eval vm_compute in T_afterN NF E3 s_v3 R_v3 S_vf.P_ok.
Definition p3 : list nat := Eval vm_compute in cperm E1f T3o.
Definition C3z : sstate := Eval vm_compute in canon T3z p3.
Definition C3f : sstate := Eval vm_compute in canon T3f p3.
Definition C3o : sstate := Eval vm_compute in canon T3o p3.
Definition J1236 : sstate := Eval vm_compute in joinA (off 1236) (leaves_at C3z (off 1236) ++ leaves_at C3f (off 1236) ++ leaves_at C3o (off 1236)).
(* fail block +1344, one join per vf layer (the vector objects a vf call rebases differ between layers) *)
Definition J1344a : sstate := Eval vm_compute in joinA (off 1344) (leaves_at C1z (off 1344) ++ leaves_at C1f (off 1344)).
Definition J1344b : sstate := Eval vm_compute in joinA (off 1344) (leaves_at C2z (off 1344) ++ leaves_at C2f (off 1344)).
Definition J1344c : sstate := Eval vm_compute in joinA (off 1344) (leaves_at C3z (off 1344) ++ leaves_at C3f (off 1344)).
Definition head_var (X : sstate) : positive := match headv X with SVar h => h | _ => 1%positive end.
Definition h892 : positive := Eval vm_compute in head_var J892.
Definition h932 : positive := Eval vm_compute in head_var J932.
Definition h1236 : positive := Eval vm_compute in head_var J1236.
Definition h1344a : positive := Eval vm_compute in head_var J1344a.
Definition h1344b : positive := Eval vm_compute in head_var J1344b.
Definition h1344c : positive := Eval vm_compute in head_var J1344c.
Definition XFa1 : sstate := Eval vm_compute in nth 0 (map lf_state (run J1344a)) Pre_fs.
Definition XFa2 : sstate := Eval vm_compute in nth 1 (map lf_state (run J1344a)) Pre_fs.
Definition XFb1 : sstate := Eval vm_compute in nth 0 (map lf_state (run J1344b)) Pre_fs.
Definition XFb2 : sstate := Eval vm_compute in nth 1 (map lf_state (run J1344b)) Pre_fs.
Definition XFc1 : sstate := Eval vm_compute in nth 0 (map lf_state (run J1344c)) Pre_fs.
Definition XFc2 : sstate := Eval vm_compute in nth 1 (map lf_state (run J1344c)) Pre_fs.
(* back to Pre_fs's object order at the rets: fs's O_AF/O_DD again, vector objects based at the builder *)
Definition xs_back (rb : list nat) : list xform :=
  [XRebase 1; XRebase 2; XRebase 3; XMerge 1; XMerge 1; XSplit 1 (SLit (-240)); XSelect ([0; 2; 1] ++ seq 3 27)%nat] ++ map XRebase rb.
Definition back_o (X : sstate) (rb : list nat) : option sstate :=
  match apply_xforms X (xs_back rb) with
  | Some X1 => match unbase_obj_at X1 1 (-192) with
               | Some X2 => match unbase_obj_at X2 2 (-192) with Some X3 => unbase_obj_at X3 2 (-48) | None => None end
               | None => None end
  | None => None end.
Definition Ya1 : sstate := Eval vm_compute in optS (back_o XFa1 [13%nat]).
Definition Ya2 : sstate := Eval vm_compute in optS (back_o XFa2 [13%nat]).
Definition Yb1 : sstate := Eval vm_compute in optS (back_o XFb1 [13%nat; 14%nat]).
Definition Yb2 : sstate := Eval vm_compute in optS (back_o XFb2 [13%nat; 14%nat]).
Definition Yc1 : sstate := Eval vm_compute in optS (back_o XFc1 [13%nat; 14%nat; 15%nat]).
Definition Yc2 : sstate := Eval vm_compute in optS (back_o XFc2 [13%nat; 14%nat; 15%nat]).

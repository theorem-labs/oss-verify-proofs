From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymSummary SymCFG Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6 Require Import S_pg S_pgB.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require Import S_sc.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import S_r2.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4 Require Import PcJoin.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import TessPolygonAddrU.

Definition sc_entryU : Z := 0x1ea8c.
Definition u1e964_entry : Z := 0x1e964.
Definition FUEL_pgB : nat := 3000%nat.
Definition cutpcs_pgB : list Z := [sc_entryU; r2_entry; pgU_ret; u1e964_entry].

Definition run_of (S : sstate) : list sstate :=
  match sym_run segsU FUEL_pgB cutpcs_pgB S true with Some l => map lf_state l | None => [] end.
Definition at_pc (pc : Z) (S : sstate) : list sstate := List.filter (fun T => Z.eqb (ss_pc T) pc) (run_of S).
Definition optS (d : sstate) (o : option sstate) : sstate := match o with Some X => X | None => d end.
Definition optR (o : option (list sobj)) : list sobj := match o with Some r => r | None => [] end.

(* State after a summarised call: the callee's post imported at the call site, caller facts kept. *)
Definition post_cut (C : sstate) (s : wsub) (R : list sobj) (P : sstate) : sstate :=
  let T := import_post s NF P (ss_next C) R in with_facts T (ss_facts T ++ ss_facts C).

(* From B_U: scale2d (n == 4), u1e964's triangle (n == 3), run2d (otherwise). *)
Definition E4 : sstate := Eval vm_compute in nth 0 (at_pc sc_entryU B_U) B_U.
Definition E5 : sstate := Eval vm_compute in nth 0 (at_pc r2_entry B_U) B_U.
Definition Ls3 : list sstate := Eval vm_compute in at_pc u1e964_entry B_U.
Definition J3 := Eval vm_compute in join PGD.pSCR (SLit 0) true B_U (SLit 0) Ls3.
Definition G3 : sstate := Eval vm_compute in fst J3.
(* n == 3: after the triangle and the orientation test, scale2d on three points. *)
Definition sc3 : list sstate := Eval vm_compute in at_pc sc_entryU G3.
Definition E3a : sstate := Eval vm_compute in nth 0 sc3 B_U.
Definition E3b : sstate := Eval vm_compute in nth 1 sc3 B_U.

(* scale2d: the scratch object (index 6) is cut down to the a1 points the callee owns. *)
Definition sc_xf (E : sstate) : list xform := [XSplit 6 (SAlu ALU_SLL (reg E 11) (SLit 4))].
Definition X4 : sstate := Eval vm_compute in optS E4 (apply_xforms E4 (sc_xf E4)).
Definition X3a : sstate := Eval vm_compute in optS E3a (apply_xforms E3a (sc_xf E3a)).
Definition X3b : sstate := Eval vm_compute in optS E3b (apply_xforms E3b (sc_xf E3b)).
Definition s4 : wsub := Eval vm_compute in infer_sub 10 X4 Pre_sc_U.
Definition s3a : wsub := Eval vm_compute in infer_sub 10 X3a Pre_sc_U.
Definition s3b : wsub := Eval vm_compute in infer_sub 10 X3b Pre_sc_U.
Definition R4 : list sobj := Eval vm_compute in optR (entails_fr X4 Pre_sc_U s4).
Definition R3a : list sobj := Eval vm_compute in optR (entails_fr X3a Pre_sc_U s3a).
Definition R3b : list sobj := Eval vm_compute in optR (entails_fr X3b Pre_sc_U s3b).
Definition T4 : sstate := Eval vm_compute in post_cut X4 s4 R4 P_sc_U.
Definition T3a : sstate := Eval vm_compute in post_cut X3a s3a R3a P_sc_U.
Definition T3b : sstate := Eval vm_compute in post_cut X3b s3b R3b P_sc_U.

(* run2d: the work struct (sp+16, 32 bytes) becomes its own object; n >= 5 on this path. *)
Definition r2_xf : list xform := [XSplit 0 (SLit (-2288)); XSplit 1 (SLit (-2256))].
Definition E5s : sstate := Eval vm_compute in optS E5 (apply_xforms E5 r2_xf).
Definition E5u : sstate := Eval vm_compute in optS E5s (unbase_obj_at E5s 1 (-2288)).
Definition n5 : sprop := SPUle (SLit 5) PGD.pN.
Definition X5 : sstate := Eval vm_compute in with_facts E5u (n5 :: ss_facts E5u).
Definition s5 : wsub := Eval vm_compute in infer_sub 10 X5 Pre_r2U.
Definition R5 : list sobj := Eval vm_compute in optR (entails_fr X5 Pre_r2U s5).
Definition T5 : sstate := Eval vm_compute in post_cut X5 s5 R5 P_r2U.

(* n == 4: the paths after scale2d meet at the two first-triangle calls of u1e964. *)
Definition calls4 : list sstate := Eval vm_compute in at_pc u1e964_entry T4.
Definition grp (ra : Z) : list sstate := List.filter (fun S => sv_eqb (reg S 1) (SLit ra)) calls4.
Definition raA : Z := 0x1e75c.
Definition raB : Z := 0x1e8c0.
Definition LsA : list sstate := Eval vm_compute in grp raA.
Definition LsB : list sstate := Eval vm_compute in grp raB.
Definition JA := Eval vm_compute in join PGD.pSCR (SLit 0) true B_U (SLit 0) LsA.
Definition JB := Eval vm_compute in join PGD.pSCR (SLit 0) true B_U (SLit 0) LsB.
Definition GA : sstate := Eval vm_compute in fst JA.
Definition GB : sstate := Eval vm_compute in fst JB.

(* Second triangle: the first one is folded into the output array's count. *)
Definition absorb_obj (o : sobj) : sobj :=
  match ob_dflt o with
  | DArr esz (SLit c) flds tmpl =>
      mkObj (ob_base o) (ob_lo o) (ob_hi o)
        (List.filter (fun cl => negb (Z.leb (esz * c) (off_lit cl) && Z.ltb (off_lit cl) (esz * (c + 1)))) (ob_cells o))
        (DArr esz (SLit (c + 1)) flds tmpl)
  | _ => o
  end.
Definition absorb_out (S : sstate) : sstate :=
  set_objs S (map (fun o => if sv_eqb (ob_base o) PGD.pOUT then absorb_obj o else o) (ss_objs S)).
Definition CA : sstate := Eval vm_compute in absorb_out (nth 0 (at_pc u1e964_entry GA) B_U).
Definition CB : sstate := Eval vm_compute in absorb_out (nth 0 (at_pc u1e964_entry GB) B_U).

Definition cuts_pgB : list sstate := [B_U; T4; T3a; T3b; T5; G3; GA; GB; CA; CB].

(* Returns, folded back to P_ok_U's objects. *)
Definition RT3 : list sstate := Eval vm_compute in flat_map (at_pc pgU_ret) [T3a; T3b].
Definition RT4 : list sstate := Eval vm_compute in flat_map (at_pc pgU_ret) [CA; CB].
Definition RT5 : list sstate := Eval vm_compute in at_pc pgU_ret T5.
Definition is_scr (o : sobj) : bool := sv_eqb (ob_base o) PGD.pSCR.
Definition fin_xf (S : sstate) : list xform :=
  let S1 := optS S (apply_xforms S (rebase_plan S)) in
  let S2 := optS S1 (apply_xforms S1 (merge_plan S1)) in
  rebase_plan S ++ merge_plan S1 ++ merge_plan_by is_scr S2.
Definition fin (S : sstate) : sstate := optS S (apply_xforms S (fin_xf S)).

Definition exits_pgB : list sstate := [E4; E3a; E3b; E5] ++ RT3 ++ RT4 ++ RT5.

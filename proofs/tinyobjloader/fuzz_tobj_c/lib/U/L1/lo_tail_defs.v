From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV TobjJVA ObjXform ObjUnbase TobjJVAx TobjJVAy TobjJVAz DrvGlue2.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo lo_defs lo_view.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require S_fs S_vf.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require S_fu.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module LoT.
Definition z0 : sv := SLit 0.
Definition pc_col : Z := 0x14ae8.
Definition cps : list Z := [S_fs.fs_entry; S_vr.vr_entry; S_vf.vf_entry; S_fu.FuAddr.fu_entry; LoU.pc_bd; pc_col].

(* finalize_shape: a0 = builder; its 192-byte frame and the 48-byte frame below come from the deep stack. *)
Definition E_fs : sstate := LoU.LA S_fs.fs_entry [(1%nat, SLit 0x14a48); (10%nat, LoU.bx)] LD.vsP LD.pERR [].
Definition vops_fs : list LD.vop := [LD.VDeep2 192 48].
Definition ns_fs : list nstep := Eval vm_compute in LoV.view_ns E_fs vops_fs.
Definition Ev_fs : sstate := Eval vm_compute in LoV.view vops_fs E_fs.
Definition slots_fs : list nat := [7; 8; 9; 10; 11; 12; 13; 6; 19]%nat.
Definition x_fs : wsub := [(19%positive, SAlu ALU_ADD LD.vDp (SLit 192))].
Definition s_fs : wsub := Eval vm_compute in LoV.sOf Ev_fs S_fs.Pre_fs x_fs.
Definition R_fs : list sobj := Eval vm_compute in LoV.R_of Ev_fs S_fs.Pre_fs x_fs.

Definition A_fs1 : sstate := Eval vm_compute in T_afterN S_fs.FD.NP Ev_fs s_fs R_fs S_fs.P_nop.
Definition T_fs1 : sstate := Eval vm_compute in LoV.renorm A_fs1.
Definition is_fs1 : wsub := Eval vm_compute in import_sub s_fs S_fs.FD.NP S_fs.P_nop (ss_next Ev_fs).
Definition tvT_fs1 : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_fs (import_tv is_fs1 S_fs.tv0).
Definition amT_fs1 : amode := Eval vm_compute in am_subst is_fs1 S_fs.ahd.

Definition A_fs2 : sstate := Eval vm_compute in T_afterN S_fs.FD.NP Ev_fs s_fs R_fs S_fs.P_ok.
Definition T_fs2 : sstate := Eval vm_compute in LoV.renorm A_fs2.
Definition is_fs2 : wsub := Eval vm_compute in import_sub s_fs S_fs.FD.NP S_fs.P_ok (ss_next Ev_fs).
Definition tvT_fs2 : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_fs (import_tv is_fs2 S_fs.tvOK).
Definition amT_fs2 : amode := Eval vm_compute in am_subst is_fs2 S_fs.amq.

Definition A_fs3 : sstate := Eval vm_compute in T_afterN S_fs.FD.NP Ev_fs s_fs R_fs S_fs.P_fail.
Definition T_fs3 : sstate := Eval vm_compute in LoV.renorm A_fs3.
Definition is_fs3 : wsub := Eval vm_compute in import_sub s_fs S_fs.FD.NP S_fs.P_fail (ss_next Ev_fs).
Definition tvT_fs3 : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_fs (import_tv is_fs3 S_fs.tv0).
Definition amT_fs3 : amode := Eval vm_compute in am_subst is_fs3 S_fs.amq.

Definition A_fs4 : sstate := Eval vm_compute in T_afterN S_fs.FD.NP Ev_fs s_fs R_fs S_fs.P_failz.
Definition T_fs4 : sstate := Eval vm_compute in LoV.renorm A_fs4.
Definition is_fs4 : wsub := Eval vm_compute in import_sub s_fs S_fs.FD.NP S_fs.P_failz (ss_next Ev_fs).
Definition tvT_fs4 : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_fs (import_tv is_fs4 S_fs.tv0).
Definition amT_fs4 : amode := Eval vm_compute in am_subst is_fs4 S_fs.amq.

Definition conts_fs : list cdesc :=
  [(LoV.renorm_prog A_fs1, (T_fs1, (tvT_fs1, amT_fs1), (390, z0)));
   (LoV.renorm_prog A_fs2, (T_fs2, (tvT_fs2, amT_fs2), (390, z0)));
   (LoV.renorm_prog A_fs3, (T_fs3, (tvT_fs3, amT_fs3), (390, z0)));
   (LoV.renorm_prog A_fs4, (T_fs4, (tvT_fs4, amT_fs4), (390, z0)))].

(* Vertex-colour fallback loop head: i in x18, numv in x22, white in x19 (its negation in x21), &acol in x9. *)
Definition white : sv := LoU.spo (-184).
Definition colregs (l : list (nat * sv)) : list (nat * sv) :=
  [(9%nat, LoU.spo (LoU.bofs + 280)); (18%nat, LD.pJ); (19%nat, white); (20%nat, SLit 6148914691236517205);
   (21%nat, SAlu ALU_SUB (SLit 0) white); (22%nat, SVar 111); (23%nat, SLit 18446744073709551612)] ++ l.
Definition K_col : sstate := LoU.LA pc_col (colregs []) LD.vsP LD.pERR LD.err0.

(* vec_reserve on acol (builder+280) for count+3; a2 = allocator copy. *)
Definition E_cv : sstate :=
  LoU.LA S_vr.vr_entry
    (colregs [(1%nat, SLit 0x14b00); (10%nat, LoU.spo (LoU.bofs + 280)); (11%nat, SAlu ALU_ADD (SVar 126) (SLit 3));
              (12%nat, LoU.alx)])
    LD.vsP LD.pERR LD.err0.
Definition vops_cv : list LD.vop := [LD.VVec 280; LD.VDeep 32].
Definition ns_cv : list nstep := Eval vm_compute in LoV.view_ns E_cv vops_cv.
Definition Ev_cv : sstate := Eval vm_compute in LoV.view vops_cv E_cv.
Definition slots_cv : list nat := [5]%nat.
Definition x_cv : wsub := [(99%positive, LD.pH); (19%positive, SAlu ALU_ADD LD.vDp (SLit 32))].
Definition s_cv : wsub := Eval vm_compute in LoV.sOf Ev_cv S_vr.Pre_vr x_cv.
Definition R_cv : list sobj := Eval vm_compute in LoV.R_of Ev_cv S_vr.Pre_vr x_cv.

Definition A_cv1 : sstate := Eval vm_compute in T_afterN 100 Ev_cv s_cv R_cv S_vr.P_keep.
Definition T_cv1 : sstate := Eval vm_compute in LoV.renorm A_cv1.
Definition is_cv1 : wsub := Eval vm_compute in import_sub s_cv 100 S_vr.P_keep (ss_next Ev_cv).
Definition tvT_cv1 : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_cv (import_tv is_cv1 S_vr.tv0).

Definition A_cv2 : sstate := Eval vm_compute in T_afterN 100 Ev_cv s_cv R_cv S_vr.P_fail.
Definition T_cv2 : sstate := Eval vm_compute in LoV.renorm A_cv2.
Definition is_cv2 : wsub := Eval vm_compute in import_sub s_cv 100 S_vr.P_fail (ss_next Ev_cv).
Definition tvT_cv2 : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_cv (import_tv is_cv2 S_vr.tv0).

Definition A_cv3 : sstate := Eval vm_compute in T_afterN 100 Ev_cv s_cv R_cv S_vr.P_grown.
Definition T_cv3 : sstate := Eval vm_compute in LoV.renorm A_cv3.
Definition is_cv3 : wsub := Eval vm_compute in import_sub s_cv 100 S_vr.P_grown (ss_next Ev_cv).
Definition tvT_cv3 : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_cv (import_tv is_cv3 S_vr.tv_post).

Definition conts_cv : list cdesc :=
  [(LoV.renorm_prog A_cv1, (T_cv1, (tvT_cv1, LoU.amL), (380, LD.VCp 2)));
   (LoV.renorm_prog A_cv2, (T_cv2, (tvT_cv2, LoU.amL), (380, LD.VCp 2)));
   (LoV.renorm_prog A_cv3, (T_cv3, (tvT_cv3, LoU.amL), (380, LD.VCp 2)))].
(* After a kept reservation the acol data block is nonempty, so its tracked-block facts hold. *)
Definition acol_blk : sv * sv := (SVar 125, SMd M_MUL (SLit 4) (SVar 127)).
Definition T_cv1x : sstate := add_facts (tv_facts acol_blk) T_cv1.

(* tobj_vec_finalize(vec, arena): a0 = vector header, a1 = arena; 32-byte frame and 48-byte frame below. *)
Definition E_vf (ra off : Z) (l : list (nat * sv)) : sstate :=
  LoU.LA S_vf.vf_entry ([(1%nat, SLit ra); (10%nat, LoU.spo (LoU.bofs + off)); (11%nat, LD.xAR); (21%nat, SVar 299)] ++ l)
    LD.vsP LD.pERR [].
Definition vops_vf (off : Z) : list LD.vop := [LD.VVec off; LD.VDeep2 32 48].
Definition slots_vf : list nat := [19]%nat.
Definition x_vf : wsub := [(19%positive, SAlu ALU_ADD LD.vDp (SLit 32))].
Definition empty0 : sobj := mkObj (SLit 0) (SLit 0) (SLit 0) [] DUnknown.

Definition E_vf0 : sstate := E_vf 0x14ba4 120 [].
Definition ns_vf0 : list nstep := Eval vm_compute in LoV.view_ns E_vf0 (vops_vf 120).
Definition Ev_vf0 : sstate := Eval vm_compute in LoV.view (vops_vf 120) E_vf0.
Definition s_vf0 : wsub := Eval vm_compute in LoV.sOf Ev_vf0 S_vf.Pre_vf x_vf.
Definition R_vf0 : list sobj := Eval vm_compute in LoV.R_of Ev_vf0 S_vf.Pre_vf x_vf.
Definition A_vf0z : sstate := Eval vm_compute in T_afterN NF Ev_vf0 s_vf0 R_vf0 S_vf.P_zero.
Definition T_vf0z : sstate := Eval vm_compute in LoV.renorm A_vf0z.
Definition is_vf0z : wsub := Eval vm_compute in import_sub s_vf0 NF S_vf.P_zero (ss_next Ev_vf0).
Definition tvT_vf0z : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf0z S_vf.tv0).
Definition amT_vf0z : amode := Eval vm_compute in am_subst is_vf0z S_vf.ahd.
Definition A_vf0f : sstate := Eval vm_compute in T_afterN NF Ev_vf0 s_vf0 R_vf0 S_vf.P_fail.
Definition T_vf0f : sstate := Eval vm_compute in LoV.renorm A_vf0f.
Definition is_vf0f : wsub := Eval vm_compute in import_sub s_vf0 NF S_vf.P_fail (ss_next Ev_vf0).
Definition tvT_vf0f : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf0f S_vf.tv0).
Definition amT_vf0f : amode := Eval vm_compute in am_subst is_vf0f S_vf.ahd.
Definition A_vf0o : sstate := Eval vm_compute in T_afterN NF Ev_vf0 s_vf0 R_vf0 S_vf.P_ok.
Definition T_vf0o : sstate := Eval vm_compute in LoV.renorm A_vf0o.
Definition is_vf0o : wsub := Eval vm_compute in import_sub s_vf0 NF S_vf.P_ok (ss_next Ev_vf0).
Definition tvT_vf0o : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf0o S_vf.tv0).
Definition amT_vf0o : amode := Eval vm_compute in am_subst is_vf0o S_vf.am_ok.
Definition conts_vf0 : list cdesc :=
  [(LoV.renorm_prog A_vf0z, (T_vf0z, (tvT_vf0z, amT_vf0z), (365, z0)));
   (LoV.renorm_prog A_vf0f, (T_vf0f, (tvT_vf0f, amT_vf0f), (365, z0)));
   (LoV.renorm_prog A_vf0o, (T_vf0o, (tvT_vf0o, amT_vf0o), (365, z0)))].

Definition E_vf1 : sstate := E_vf 0x14bd4 152 [].
Definition ns_vf1 : list nstep := Eval vm_compute in LoV.view_ns E_vf1 (vops_vf 152).
Definition Ev_vf1 : sstate := Eval vm_compute in LoV.view (vops_vf 152) E_vf1.
Definition s_vf1 : wsub := Eval vm_compute in LoV.sOf Ev_vf1 S_vf.Pre_vf x_vf.
Definition R_vf1 : list sobj := Eval vm_compute in LoV.R_of Ev_vf1 S_vf.Pre_vf x_vf.
Definition A_vf1z : sstate := Eval vm_compute in T_afterN NF Ev_vf1 s_vf1 R_vf1 S_vf.P_zero.
Definition T_vf1z : sstate := Eval vm_compute in LoV.renorm A_vf1z.
Definition is_vf1z : wsub := Eval vm_compute in import_sub s_vf1 NF S_vf.P_zero (ss_next Ev_vf1).
Definition tvT_vf1z : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf1z S_vf.tv0).
Definition amT_vf1z : amode := Eval vm_compute in am_subst is_vf1z S_vf.ahd.
Definition A_vf1f : sstate := Eval vm_compute in T_afterN NF Ev_vf1 s_vf1 R_vf1 S_vf.P_fail.
Definition T_vf1f : sstate := Eval vm_compute in LoV.renorm A_vf1f.
Definition is_vf1f : wsub := Eval vm_compute in import_sub s_vf1 NF S_vf.P_fail (ss_next Ev_vf1).
Definition tvT_vf1f : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf1f S_vf.tv0).
Definition amT_vf1f : amode := Eval vm_compute in am_subst is_vf1f S_vf.ahd.
Definition A_vf1o : sstate := Eval vm_compute in T_afterN NF Ev_vf1 s_vf1 R_vf1 S_vf.P_ok.
Definition T_vf1o : sstate := Eval vm_compute in LoV.renorm A_vf1o.
Definition is_vf1o : wsub := Eval vm_compute in import_sub s_vf1 NF S_vf.P_ok (ss_next Ev_vf1).
Definition tvT_vf1o : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf1o S_vf.tv0).
Definition amT_vf1o : amode := Eval vm_compute in am_subst is_vf1o S_vf.am_ok.
Definition conts_vf1 : list cdesc :=
  [(LoV.renorm_prog A_vf1z, (T_vf1z, (tvT_vf1z, amT_vf1z), (355, z0)));
   (LoV.renorm_prog A_vf1f, (T_vf1f, (tvT_vf1f, amT_vf1f), (355, z0)));
   (LoV.renorm_prog A_vf1o, (T_vf1o, (tvT_vf1o, amT_vf1o), (355, z0)))].

Definition E_vf2 : sstate := E_vf 0x14c04 184 [].
Definition ns_vf2 : list nstep := Eval vm_compute in LoV.view_ns E_vf2 (vops_vf 184).
Definition Ev_vf2 : sstate := Eval vm_compute in LoV.view (vops_vf 184) E_vf2.
Definition s_vf2 : wsub := Eval vm_compute in LoV.sOf Ev_vf2 S_vf.Pre_vf x_vf.
Definition R_vf2 : list sobj := Eval vm_compute in LoV.R_of Ev_vf2 S_vf.Pre_vf x_vf.
Definition A_vf2z : sstate := Eval vm_compute in T_afterN NF Ev_vf2 s_vf2 R_vf2 S_vf.P_zero.
Definition T_vf2z : sstate := Eval vm_compute in LoV.renorm A_vf2z.
Definition is_vf2z : wsub := Eval vm_compute in import_sub s_vf2 NF S_vf.P_zero (ss_next Ev_vf2).
Definition tvT_vf2z : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf2z S_vf.tv0).
Definition amT_vf2z : amode := Eval vm_compute in am_subst is_vf2z S_vf.ahd.
Definition A_vf2f : sstate := Eval vm_compute in T_afterN NF Ev_vf2 s_vf2 R_vf2 S_vf.P_fail.
Definition T_vf2f : sstate := Eval vm_compute in LoV.renorm A_vf2f.
Definition is_vf2f : wsub := Eval vm_compute in import_sub s_vf2 NF S_vf.P_fail (ss_next Ev_vf2).
Definition tvT_vf2f : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf2f S_vf.tv0).
Definition amT_vf2f : amode := Eval vm_compute in am_subst is_vf2f S_vf.ahd.
Definition A_vf2o : sstate := Eval vm_compute in T_afterN NF Ev_vf2 s_vf2 R_vf2 S_vf.P_ok.
Definition T_vf2o : sstate := Eval vm_compute in LoV.renorm A_vf2o.
Definition is_vf2o : wsub := Eval vm_compute in import_sub s_vf2 NF S_vf.P_ok (ss_next Ev_vf2).
Definition tvT_vf2o : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf2o S_vf.tv0).
Definition amT_vf2o : amode := Eval vm_compute in am_subst is_vf2o S_vf.am_ok.
Definition conts_vf2 : list cdesc :=
  [(LoV.renorm_prog A_vf2z, (T_vf2z, (tvT_vf2z, amT_vf2z), (345, z0)));
   (LoV.renorm_prog A_vf2f, (T_vf2f, (tvT_vf2f, amT_vf2f), (345, z0)));
   (LoV.renorm_prog A_vf2o, (T_vf2o, (tvT_vf2o, amT_vf2o), (345, z0)))].

Definition E_vf3 : sstate := E_vf 0x14c34 216 [].
Definition ns_vf3 : list nstep := Eval vm_compute in LoV.view_ns E_vf3 (vops_vf 216).
Definition Ev_vf3 : sstate := Eval vm_compute in LoV.view (vops_vf 216) E_vf3.
Definition s_vf3 : wsub := Eval vm_compute in LoV.sOf Ev_vf3 S_vf.Pre_vf x_vf.
Definition R_vf3 : list sobj := Eval vm_compute in LoV.R_of Ev_vf3 S_vf.Pre_vf x_vf.
Definition A_vf3z : sstate := Eval vm_compute in T_afterN NF Ev_vf3 s_vf3 R_vf3 S_vf.P_zero.
Definition T_vf3z : sstate := Eval vm_compute in LoV.renorm A_vf3z.
Definition is_vf3z : wsub := Eval vm_compute in import_sub s_vf3 NF S_vf.P_zero (ss_next Ev_vf3).
Definition tvT_vf3z : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf3z S_vf.tv0).
Definition amT_vf3z : amode := Eval vm_compute in am_subst is_vf3z S_vf.ahd.
Definition A_vf3f : sstate := Eval vm_compute in T_afterN NF Ev_vf3 s_vf3 R_vf3 S_vf.P_fail.
Definition T_vf3f : sstate := Eval vm_compute in LoV.renorm A_vf3f.
Definition is_vf3f : wsub := Eval vm_compute in import_sub s_vf3 NF S_vf.P_fail (ss_next Ev_vf3).
Definition tvT_vf3f : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf3f S_vf.tv0).
Definition amT_vf3f : amode := Eval vm_compute in am_subst is_vf3f S_vf.ahd.
Definition A_vf3o : sstate := Eval vm_compute in T_afterN NF Ev_vf3 s_vf3 R_vf3 S_vf.P_ok.
Definition T_vf3o : sstate := Eval vm_compute in LoV.renorm A_vf3o.
Definition is_vf3o : wsub := Eval vm_compute in import_sub s_vf3 NF S_vf.P_ok (ss_next Ev_vf3).
Definition tvT_vf3o : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf3o S_vf.tv0).
Definition amT_vf3o : amode := Eval vm_compute in am_subst is_vf3o S_vf.am_ok.
Definition conts_vf3 : list cdesc :=
  [(LoV.renorm_prog A_vf3z, (T_vf3z, (tvT_vf3z, amT_vf3z), (335, z0)));
   (LoV.renorm_prog A_vf3f, (T_vf3f, (tvT_vf3f, amT_vf3f), (335, z0)));
   (LoV.renorm_prog A_vf3o, (T_vf3o, (tvT_vf3o, amT_vf3o), (335, z0)))].

Definition E_vf4 : sstate := E_vf 0x14c64 248 [].
Definition ns_vf4 : list nstep := Eval vm_compute in LoV.view_ns E_vf4 (vops_vf 248).
Definition Ev_vf4 : sstate := Eval vm_compute in LoV.view (vops_vf 248) E_vf4.
Definition s_vf4 : wsub := Eval vm_compute in LoV.sOf Ev_vf4 S_vf.Pre_vf x_vf.
Definition R_vf4 : list sobj := Eval vm_compute in LoV.R_of Ev_vf4 S_vf.Pre_vf x_vf.
Definition A_vf4z : sstate := Eval vm_compute in T_afterN NF Ev_vf4 s_vf4 R_vf4 S_vf.P_zero.
Definition T_vf4z : sstate := Eval vm_compute in LoV.renorm A_vf4z.
Definition is_vf4z : wsub := Eval vm_compute in import_sub s_vf4 NF S_vf.P_zero (ss_next Ev_vf4).
Definition tvT_vf4z : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf4z S_vf.tv0).
Definition amT_vf4z : amode := Eval vm_compute in am_subst is_vf4z S_vf.ahd.
Definition A_vf4f : sstate := Eval vm_compute in T_afterN NF Ev_vf4 s_vf4 R_vf4 S_vf.P_fail.
Definition T_vf4f : sstate := Eval vm_compute in LoV.renorm A_vf4f.
Definition is_vf4f : wsub := Eval vm_compute in import_sub s_vf4 NF S_vf.P_fail (ss_next Ev_vf4).
Definition tvT_vf4f : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf4f S_vf.tv0).
Definition amT_vf4f : amode := Eval vm_compute in am_subst is_vf4f S_vf.ahd.
Definition A_vf4o : sstate := Eval vm_compute in T_afterN NF Ev_vf4 s_vf4 R_vf4 S_vf.P_ok.
Definition T_vf4o : sstate := Eval vm_compute in LoV.renorm A_vf4o.
Definition is_vf4o : wsub := Eval vm_compute in import_sub s_vf4 NF S_vf.P_ok (ss_next Ev_vf4).
Definition tvT_vf4o : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf4o S_vf.tv0).
Definition amT_vf4o : amode := Eval vm_compute in am_subst is_vf4o S_vf.am_ok.
Definition conts_vf4 : list cdesc :=
  [(LoV.renorm_prog A_vf4z, (T_vf4z, (tvT_vf4z, amT_vf4z), (325, z0)));
   (LoV.renorm_prog A_vf4f, (T_vf4f, (tvT_vf4f, amT_vf4f), (325, z0)));
   (LoV.renorm_prog A_vf4o, (T_vf4o, (tvT_vf4o, amT_vf4o), (325, z0)))].

Definition E_vf5 : sstate := E_vf 0x14c98 280 [(9%nat, LD.vOUT)].
Definition ns_vf5 : list nstep := Eval vm_compute in LoV.view_ns E_vf5 (vops_vf 280).
Definition Ev_vf5 : sstate := Eval vm_compute in LoV.view (vops_vf 280) E_vf5.
Definition s_vf5 : wsub := Eval vm_compute in LoV.sOf Ev_vf5 S_vf.Pre_vf x_vf.
Definition R_vf5 : list sobj := Eval vm_compute in LoV.R_of Ev_vf5 S_vf.Pre_vf x_vf.
Definition A_vf5z : sstate := Eval vm_compute in T_afterN NF Ev_vf5 s_vf5 R_vf5 S_vf.P_zero.
Definition T_vf5z : sstate := Eval vm_compute in LoV.renorm A_vf5z.
Definition is_vf5z : wsub := Eval vm_compute in import_sub s_vf5 NF S_vf.P_zero (ss_next Ev_vf5).
Definition tvT_vf5z : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf5z S_vf.tv0).
Definition amT_vf5z : amode := Eval vm_compute in am_subst is_vf5z S_vf.ahd.
Definition A_vf5f : sstate := Eval vm_compute in T_afterN NF Ev_vf5 s_vf5 R_vf5 S_vf.P_fail.
Definition T_vf5f : sstate := Eval vm_compute in LoV.renorm A_vf5f.
Definition is_vf5f : wsub := Eval vm_compute in import_sub s_vf5 NF S_vf.P_fail (ss_next Ev_vf5).
Definition tvT_vf5f : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf5f S_vf.tv0).
Definition amT_vf5f : amode := Eval vm_compute in am_subst is_vf5f S_vf.ahd.
Definition A_vf5o : sstate := Eval vm_compute in T_afterN NF Ev_vf5 s_vf5 R_vf5 S_vf.P_ok.
Definition T_vf5o : sstate := Eval vm_compute in LoV.renorm A_vf5o.
Definition is_vf5o : wsub := Eval vm_compute in import_sub s_vf5 NF S_vf.P_ok (ss_next Ev_vf5).
Definition tvT_vf5o : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf5o S_vf.tv0).
Definition amT_vf5o : amode := Eval vm_compute in am_subst is_vf5o S_vf.am_ok.
Definition conts_vf5 : list cdesc :=
  [(LoV.renorm_prog A_vf5z, (T_vf5z, (tvT_vf5z, amT_vf5z), (315, z0)));
   (LoV.renorm_prog A_vf5f, (T_vf5f, (tvT_vf5f, amT_vf5f), (315, z0)));
   (LoV.renorm_prog A_vf5o, (T_vf5o, (tvT_vf5o, amT_vf5o), (315, z0)))].

Definition E_vf6 : sstate := E_vf 0x14e18 448 [].
Definition ns_vf6 : list nstep := Eval vm_compute in LoV.view_ns E_vf6 (vops_vf 448).
Definition Ev_vf6 : sstate := Eval vm_compute in LoV.view (vops_vf 448) E_vf6.
Definition s_vf6 : wsub := Eval vm_compute in LoV.sOf Ev_vf6 S_vf.Pre_vf x_vf.
Definition R_vf6 : list sobj := Eval vm_compute in LoV.R_of Ev_vf6 S_vf.Pre_vf x_vf.
Definition A_vf6z : sstate := Eval vm_compute in T_afterN NF Ev_vf6 s_vf6 R_vf6 S_vf.P_zero.
Definition T_vf6z : sstate := Eval vm_compute in LoV.renorm A_vf6z.
Definition is_vf6z : wsub := Eval vm_compute in import_sub s_vf6 NF S_vf.P_zero (ss_next Ev_vf6).
Definition tvT_vf6z : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf6z S_vf.tv0).
Definition amT_vf6z : amode := Eval vm_compute in am_subst is_vf6z S_vf.ahd.
Definition A_vf6f : sstate := Eval vm_compute in T_afterN NF Ev_vf6 s_vf6 R_vf6 S_vf.P_fail.
Definition T_vf6f : sstate := Eval vm_compute in LoV.renorm A_vf6f.
Definition is_vf6f : wsub := Eval vm_compute in import_sub s_vf6 NF S_vf.P_fail (ss_next Ev_vf6).
Definition tvT_vf6f : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf6f S_vf.tv0).
Definition amT_vf6f : amode := Eval vm_compute in am_subst is_vf6f S_vf.ahd.
Definition A_vf6o : sstate := Eval vm_compute in T_afterN NF Ev_vf6 s_vf6 R_vf6 S_vf.P_ok.
Definition T_vf6o : sstate := Eval vm_compute in LoV.renorm A_vf6o.
Definition is_vf6o : wsub := Eval vm_compute in import_sub s_vf6 NF S_vf.P_ok (ss_next Ev_vf6).
Definition tvT_vf6o : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf6o S_vf.tv0).
Definition amT_vf6o : amode := Eval vm_compute in am_subst is_vf6o S_vf.am_ok.
Definition conts_vf6 : list cdesc :=
  [(LoV.renorm_prog A_vf6z, (T_vf6z, (tvT_vf6z, amT_vf6z), (295, z0)));
   (LoV.renorm_prog A_vf6f, (T_vf6f, (tvT_vf6f, amT_vf6f), (295, z0)));
   (LoV.renorm_prog A_vf6o, (T_vf6o, (tvT_vf6o, amT_vf6o), (295, z0)))].

Definition E_vf7 : sstate := E_vf 0x14e4c 320 [(9%nat, LD.vOUT)].
Definition E_vf7e : sstate := set_objs E_vf7 (ss_objs E_vf7 ++ [empty0]).
Definition ns_vf7 : list nstep := Eval vm_compute in LoV.view_ns E_vf7e (vops_vf 320).
Definition Ev_vf7 : sstate := Eval vm_compute in LoV.view (vops_vf 320) E_vf7e.
Definition s_vf7 : wsub := Eval vm_compute in LoV.sOf Ev_vf7 S_vf.Pre_vf x_vf.
Definition R_vf7 : list sobj := Eval vm_compute in LoV.R_of Ev_vf7 S_vf.Pre_vf x_vf.
Definition A_vf7z : sstate := Eval vm_compute in T_afterN NF Ev_vf7 s_vf7 R_vf7 S_vf.P_zero.
Definition T_vf7z : sstate := Eval vm_compute in LoV.renorm A_vf7z.
Definition is_vf7z : wsub := Eval vm_compute in import_sub s_vf7 NF S_vf.P_zero (ss_next Ev_vf7).
Definition tvT_vf7z : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf7z S_vf.tv0).
Definition amT_vf7z : amode := Eval vm_compute in am_subst is_vf7z S_vf.ahd.
Definition A_vf7f : sstate := Eval vm_compute in T_afterN NF Ev_vf7 s_vf7 R_vf7 S_vf.P_fail.
Definition T_vf7f : sstate := Eval vm_compute in LoV.renorm A_vf7f.
Definition is_vf7f : wsub := Eval vm_compute in import_sub s_vf7 NF S_vf.P_fail (ss_next Ev_vf7).
Definition tvT_vf7f : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf7f S_vf.tv0).
Definition amT_vf7f : amode := Eval vm_compute in am_subst is_vf7f S_vf.ahd.
Definition A_vf7o : sstate := Eval vm_compute in T_afterN NF Ev_vf7 s_vf7 R_vf7 S_vf.P_ok.
Definition T_vf7o : sstate := Eval vm_compute in LoV.renorm A_vf7o.
Definition is_vf7o : wsub := Eval vm_compute in import_sub s_vf7 NF S_vf.P_ok (ss_next Ev_vf7).
Definition tvT_vf7o : list (sv * sv) := Eval vm_compute in LoV.tvfill slots_vf (import_tv is_vf7o S_vf.tv0).
Definition amT_vf7o : amode := Eval vm_compute in am_subst is_vf7o S_vf.am_ok.
Definition conts_vf7 : list cdesc :=
  [(LoV.renorm_prog A_vf7z, (T_vf7z, (tvT_vf7z, amT_vf7z), (285, z0)));
   (LoV.renorm_prog A_vf7f, (T_vf7f, (tvT_vf7f, amT_vf7f), (285, z0)));
   (LoV.renorm_prog A_vf7o, (T_vf7o, (tvT_vf7o, amT_vf7o), (285, z0)))].

Fixpoint find_empty (i : nat) (l : list sobj) : nat :=
  match l with
  | [] => i
  | o :: r => if andb (sv_eqb (ob_base o) (SLit 0)) (sv_eqb (ob_hi o) (SLit 0)) then i else find_empty (S i) r
  end.
Definition drop_empty (S : sstate) : sstate := set_objs S (remove_nth (find_empty 0 (ss_objs S)) (ss_objs S)).
Definition T_vf7zx : sstate := Eval vm_compute in drop_empty T_vf7z.
Definition T_vf7fx : sstate := Eval vm_compute in drop_empty T_vf7f.
Definition T_vf7ox : sstate := Eval vm_compute in drop_empty T_vf7o.

(* finalize_unknowns(builder): pure call, 112-byte frame. *)
Definition E_fu : sstate :=
  LoU.LA S_fu.FuAddr.fu_entry [(1%nat, SLit 0x14dfc); (10%nat, LoU.bx); (21%nat, SVar 299)] LD.vsP LD.pERR [].
Definition vops_fu : list LD.vop := [LD.VDeep 112].
Definition ns_fu : list nstep := Eval vm_compute in LoV.view_ns E_fu vops_fu.
Definition Ev_fu : sstate := Eval vm_compute in LoV.view vops_fu E_fu.
Definition s_fu : wsub := Eval vm_compute in infer_sub 10 Ev_fu S_fu.Pre_fu_U.
Definition R_fu : list sobj := Eval vm_compute in match entails_fr Ev_fu S_fu.Pre_fu_U s_fu with Some r => r | None => [] end.
Definition T_fu0 : sstate := Eval vm_compute in
  add_facts (ss_facts Ev_fu) (import_post s_fu (ss_next S_fu.Pre_fu_U) S_fu.P_fu_U (ss_next Ev_fu) R_fu).
Definition T_fu : sstate := Eval vm_compute in LoV.renorm T_fu0.

Definition cutsE : list aedesc :=
  [((LoU.K_tail, (LoU.tvL, LoU.amL)), (400, z0));
   ((T_fs1, (tvT_fs1, amT_fs1)), (390, z0)); ((T_fs2, (tvT_fs2, amT_fs2)), (390, z0));
   ((T_fs3, (tvT_fs3, amT_fs3)), (390, z0)); ((T_fs4, (tvT_fs4, amT_fs4)), (390, z0));
   ((K_col, (LoU.tvL, LoU.amL)), (380, LD.VCp 6));
   ((T_cv1x, (tvT_cv1, LoU.amL)), (380, LD.VCp 2)); ((T_cv2, (tvT_cv2, LoU.amL)), (380, LD.VCp 2));
   ((T_cv3, (tvT_cv3, LoU.amL)), (380, LD.VCp 2));
   ((T_fu, (LoU.tvL, LoU.amL)), (305, z0))]
  ++ concat (map (fun t => let '(T, tv, am, r) := t in [((T, (tv, am)), (r, z0))])

       [(T_vf0z, tvT_vf0z, amT_vf0z, 365);
        (T_vf0f, tvT_vf0f, amT_vf0f, 365);
        (T_vf0o, tvT_vf0o, amT_vf0o, 365);
        (T_vf1z, tvT_vf1z, amT_vf1z, 355);
        (T_vf1f, tvT_vf1f, amT_vf1f, 355);
        (T_vf1o, tvT_vf1o, amT_vf1o, 355);
        (T_vf2z, tvT_vf2z, amT_vf2z, 345);
        (T_vf2f, tvT_vf2f, amT_vf2f, 345);
        (T_vf2o, tvT_vf2o, amT_vf2o, 345);
        (T_vf3z, tvT_vf3z, amT_vf3z, 335);
        (T_vf3f, tvT_vf3f, amT_vf3f, 335);
        (T_vf3o, tvT_vf3o, amT_vf3o, 335);
        (T_vf4z, tvT_vf4z, amT_vf4z, 325);
        (T_vf4f, tvT_vf4f, amT_vf4f, 325);
        (T_vf4o, tvT_vf4o, amT_vf4o, 325);
        (T_vf5z, tvT_vf5z, amT_vf5z, 315);
        (T_vf5f, tvT_vf5f, amT_vf5f, 315);
        (T_vf5o, tvT_vf5o, amT_vf5o, 315);
        (T_vf6z, tvT_vf6z, amT_vf6z, 295);
        (T_vf6f, tvT_vf6f, amT_vf6f, 295);
        (T_vf6o, tvT_vf6o, amT_vf6o, 295);
        (T_vf7zx, tvT_vf7z, amT_vf7z, 285);
        (T_vf7fx, tvT_vf7f, amT_vf7f, 285);
        (T_vf7ox, tvT_vf7o, amT_vf7o, 285)]).
Definition exitsE : list aedesc :=
  [((E_fs, (LoU.tvL, LoU.amL)), (395, z0));
   ((E_cv, (LoU.tvL, LoU.amL)), (380, LD.VCp 4));
   ((E_vf0, (LoU.tvL, LoU.amL)), (370, z0));
   ((E_vf1, (LoU.tvL, LoU.amL)), (360, z0));
   ((E_vf2, (LoU.tvL, LoU.amL)), (350, z0));
   ((E_vf3, (LoU.tvL, LoU.amL)), (340, z0));
   ((E_vf4, (LoU.tvL, LoU.amL)), (330, z0));
   ((E_vf5, (LoU.tvL, LoU.amL)), (320, z0));
   ((E_vf6, (LoU.tvL, LoU.amL)), (300, z0));
   ((E_vf7, (LoU.tvL, LoU.amL)), (290, z0));
   ((E_fu, (LoU.tvL, LoU.amL)), (310, z0));
   ((LoU.K_bd, (LoU.tvL, LoU.amL)), (0, z0))].
End LoT.

From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjUnbase ObjXform TobjJV TobjJVA TobjJVAx TobjJVAy.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require BuilderDispose ArenaDestroy.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo lo_defs lo_view lo_tail_addr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4 Require Import S_bd.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module LoBd.

Definition pc_L : Z := LoTailAddr.pc_desB + 4.
Definition FUEL : nat := 3000.
Definition cps : list Z := [ec_malloc EC_U; ec_free EC_U; LoTailAddr.c_bd; LoTailAddr.pc_bd; LoTailAddr.ra_fl; pc_L].
Definition runl (S : sstate) : list leaf :=
  match sym_run segsU FUEL cps S true with Some l => l | None => [] end.
Definition leaf_at (S : sstate) (pc : Z) (k : nat) : sstate :=
  nth k (filter (fun st => Z.eqb (ss_pc st) pc) (map lf_state (runl S))) S.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Fixpoint idx_of (p : sobj -> bool) (l : list sobj) : nat :=
  match l with [] => O | x :: t => if p x then O else S (idx_of p t) end.

Definition z0 : sv := SLit 0.
Definition am0 : amode := AHead (SLit 0).

(* builder_dispose call *)
Definition E_bd : sstate := Eval vm_compute in leaf_at LoU.K_bd LoTailAddr.c_bd 0.
Definition vops_bd : list LD.vop := [LD.VMergeB 320 4; LD.VMergeB 936 10; LD.VDeep 32].
Definition ns_bd : list nstep := Eval vm_compute in LoV.view_ns E_bd vops_bd.
Definition Ev_bd : sstate := Eval vm_compute in LoV.view vops_bd E_bd.
Definition slots_bd : list nat := Eval vm_compute in seq 0 18.
Definition x_bd : wsub := [(199%positive, LD.pH)].
Definition s_bd : wsub := Eval vm_compute in LoV.sOf Ev_bd Pre_bd x_bd.
Definition R_bd : list sobj := Eval vm_compute in LoV.R_of Ev_bd Pre_bd x_bd.
Definition PD_bd : list (sstate * list (sv * sv)) := [(BuilderDispose.P_bd bcU, [])].
Definition A_bd : sstate := Eval vm_compute in T_afterN 200 Ev_bd s_bd R_bd (BuilderDispose.P_bd bcU).
Definition T_bd : sstate := Eval vm_compute in LoV.renorm A_bd.
Definition conts_bd : list cdesc := [(LoV.renorm_prog A_bd, (T_bd, (LD.tv_fl, LoU.amL), (190, z0)))].

(* tobj_vec_free of the lines vector *)
Definition E_fl1 : sstate := Eval vm_compute in leaf_at T_bd (ec_free EC_U) 0.
Definition E_fl2 : sstate := Eval vm_compute in leaf_at T_bd (ec_free EC_U) 1.
Definition X_l0 : sstate := Eval vm_compute in leaf_at T_bd LoTailAddr.ra_fl 0.
Definition s_fl1 : wsub := Eval vm_compute in infer_sub 10 E_fl1 (Pre_free EC_U).
Definition R_fl1 : list sobj := Eval vm_compute in optR (entails_fr E_fl1 (Pre_free EC_U) s_fl1).
Definition T_fl1 : sstate := Eval vm_compute in T_after E_fl1 s_fl1 R_fl1 (L_free EC_U).
Definition s_fl2 : wsub := Eval vm_compute in infer_sub 10 E_fl2 (Pre_free EC_U).
Definition R_fl2 : list sobj := Eval vm_compute in optR (entails_fr E_fl2 (Pre_free EC_U) s_fl2).
Definition T_fl2 : sstate := Eval vm_compute in T_after E_fl2 s_fl2 R_fl2 (L_free EC_U).
Definition K_chk1 : sstate := Eval vm_compute in leaf_at T_fl1 LoTailAddr.ra_fl 0.
Definition K_chk : sstate := Eval vm_compute in
  mkSS (ss_pc K_chk1) (list_set (ss_regs K_chk1) 1 (SVar (ss_next K_chk1))) (ss_fregs K_chk1) (ss_fcsr K_chk1)
    (ss_resv K_chk1) (ss_objs K_chk1) (skipn 2 (ss_facts K_chk1)) (Pos.succ (ss_next K_chk1)) false.
Definition O_ldat : sobj := LD.O_lines LD.xLD LD.xLC LD.xLK.
Definition iL0 : nat := Eval vm_compute in idx_of (fun o => sv_eqb (ob_base o) LD.xLD) (ss_objs X_l0).
Definition X_l0d : sstate := Eval vm_compute in set_objs X_l0 (remove_nth iL0 (ss_objs X_l0)).

(* return paths: the frame pieces merged back into one frame object *)
Definition mk_post_ns (S : sstate) : list nstep :=
  let xs1 := map XRebase (LD.idxs_where (fun o => match LD.spoff_of o with Some c => Z.ltb (- LoU.FR) c | None => false end)
                                        (ss_objs S) 0) in
  match apply_xforms S xs1 with
  | Some S1 =>
      let os := ss_objs S1 in
      let sps := LD.idxs_where LD.is_sp os 0 in
      let others := filter (fun i => negb (existsb (Nat.eqb i) sps)) (seq 0 (length os)) in
      let perm := LD.sort_by (fun i => LD.lit_of (ob_lo (nth i os LD.O_D))) sps ++ others in
      [NX (xs1 ++ XSelect perm :: repeat (XMerge 0) (length sps - 1))]
  | None => [NX xs1]
  end.
Definition X_ok : sstate := Eval vm_compute in leaf_at K_chk LoTailAddr.pc_ret 0.
Definition ns_ok : list nstep := Eval vm_compute in mk_post_ns (with_facts X_ok LoU.base_facts).
Definition X_okN : sstate := Eval vm_compute in
  match run_nsteps (with_facts X_ok LoU.base_facts) ns_ok with Some X => with_facts X (ss_facts X_ok) | None => X_ok end.

(* error path: tobj_arena_destroy, free of the arena, memset of out *)
Definition X_P0 : sstate := Eval vm_compute in leaf_at K_chk pc_L 0.
Definition X_fa0 : sstate := Eval vm_compute in leaf_at K_chk (ec_free EC_U) 0.
Definition X_P0f : sstate := Eval vm_compute in add_facts [SPNot (SPBranch BC_EQ LD.pH (SLit 0))] X_P0.
Definition X_P01 : sstate := Eval vm_compute in ArenaDestroy.lenN_state X_P0f.
Definition X_P02 : sstate := Eval vm_compute in ArenaDestroy.pop_stateN X_P01 LD.pH (SVar (ss_next X_P0f)).

Definition pB : sv := SVar 500.
Definition pNn : positive := 501.
Definition pNX : sv := SVar 501.
Definition vG : sv := SVar 504.
Definition VGp (k : Z) : sv := SAlu ALU_ADD vG (SLit k).
Definition VGm (k : Z) : sv := SAlu ALU_SUB vG (SLit k).
Definition gl_regs : list nat := [0; 1; 5; 6; 7; 10; 11; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Fixpoint gen_regs (rs : list sv) (l : list nat) (v : positive) : list sv :=
  match l with [] => rs | i :: t => gen_regs (list_set rs i (SVar v)) t (Pos.succ v) end.
Definition C_L : sstate := Eval vm_compute in
  mkSS pc_L (gen_regs (list_set (ss_regs X_P0) 9 pB) gl_regs 505) (ss_fregs X_P0) (ss_fcsr X_P0) (ss_resv X_P0)
    (ss_objs X_P0 ++ [ArenaDestroy.popped pB pNn]) (open_facts pB pNn ++ ArenaDestroy.ghost_facts 504 ++ ss_facts X_P0)
    521 false.
Definition tv_L : list (sv * sv) := ArenaDestroy.pop_tv pB pNn LoU.tv_ar.
Definition am_L : amode := AHeadN pNX vG.
Definition s_P0 : wsub := Eval vm_compute in [(504%positive, SVar (ss_next X_P01 + 3))].

Definition E_fd : sstate := Eval vm_compute in leaf_at C_L (ec_free EC_U) 0.
Definition s_fd : wsub := Eval vm_compute in infer_sub 10 E_fd (Pre_free EC_U).
Definition R_fd : list sobj := Eval vm_compute in optR (entails_fr E_fd (Pre_free EC_U) s_fd).
Definition T_fd : sstate := Eval vm_compute in T_after E_fd s_fd R_fd (L_free EC_U).
Definition X_P : sstate := Eval vm_compute in leaf_at T_fd pc_L 0.
Definition X_fa1 : sstate := Eval vm_compute in leaf_at T_fd (ec_free EC_U) 0.
Definition X_Pf : sstate := Eval vm_compute in add_facts [SPNot (SPBranch BC_EQ pNX (SLit 0))] X_P.
Definition X_P2 : sstate := Eval vm_compute in ArenaDestroy.pop_stateN X_Pf pNX vG.
Definition s_P : wsub := Eval vm_compute in [(504%positive, SVar (ss_next X_Pf + 3))].

Definition E_FA : sstate := Eval vm_compute in
  mkSS (ss_pc X_fa0) (ss_regs X_fa0) (ss_fregs X_fa0) (ss_fcsr X_fa0) (ss_resv X_fa0) (ss_objs X_fa0)
    (filter (fun f => existsb (sprop_eqb f) (ss_facts X_fa1)) (ss_facts X_fa0)) (Pos.add (ss_next X_fa0) 1) false.
Definition s_fa0 : wsub := Eval vm_compute in infer_sub LD.NP X_fa0 E_FA.
Definition s_fa1 : wsub := Eval vm_compute in infer_sub LD.NP X_fa1 E_FA.
Definition s_fa : wsub := Eval vm_compute in infer_sub 10 E_FA (Pre_free EC_U).
Definition R_fa : list sobj := Eval vm_compute in optR (entails_fr E_FA (Pre_free EC_U) s_fa).
Definition T_fa : sstate := Eval vm_compute in T_after E_FA s_fa R_fa (L_free EC_U).
Definition X_err : sstate := Eval vm_compute in leaf_at T_fa LoTailAddr.pc_ret 0.
Definition ns_err : list nstep := Eval vm_compute in mk_post_ns (with_facts X_err LoU.base_facts).
Definition X_errN : sstate := Eval vm_compute in
  match run_nsteps (with_facts X_err LoU.base_facts) ns_err with Some X => with_facts X (ss_facts X_err) | None => X_err end.

Definition cutsE : list aedesc :=
  [(LoU.K_bd, (LoU.tvL, LoU.amL), (200, z0)); (T_bd, (LD.tv_fl, LoU.amL), (190, z0));
   (T_fl1, (LoU.tv_ar, LoU.amL), (180, z0)); (T_fl2, (LoU.tv_ar, LoU.amL), (180, z0));
   (K_chk, (LoU.tv_ar, LoU.amL), (170, z0)); (C_L, (tv_L, am_L), (60, VGp 2));
   (T_fd, (LoU.tv_ar, am_L), (60, VGp 0)); (T_fa, ([], am0), (20, z0))].
Definition exitsE : list aedesc :=
  [(E_bd, (LoU.tvL, LoU.amL), (195, z0)); (E_fl1, (LD.tv_fl, LoU.amL), (185, z0));
   (E_fl2, (LD.tv_fl, LoU.amL), (185, z0)); (X_l0, (LD.tv_fl, LoU.amL), (185, z0));
   (X_ok, (LoU.tv_ar, LoU.amL), (100, z0)); (X_P0, (LoU.tv_ar, LoU.amL), (160, z0));
   (X_fa1, (LoU.tv_ar, am_L), (30, z0)); (X_fa0, (LoU.tv_ar, LoU.amL), (155, z0));
   (E_fd, (tv_L, am_L), (60, VGp 1)); (X_P, (LoU.tv_ar, am_L), (60, VGm 1)); (X_err, ([], am0), (10, z0))].

End LoBd.

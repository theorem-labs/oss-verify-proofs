From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjXform TobjJV TobjJVs CellTile ArrMat.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require Import S_rad.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ra_L : Z := 0x1c224.
Definition FUEL_ra : nat := 400%nat.
Definition cutpcs_ra : list Z := [ra_L; ec_malloc EC_U; ec_free EC_U].

Definition run_of (S : sstate) : list sstate :=
  match sym_run segsU FUEL_ra cutpcs_ra S true with Some ls => map lf_state ls | None => [] end.
Definition leaf_k (S : sstate) (k : nat) : sstate := nth k (run_of S) Pre_rad.
Definition leaves_at (S : sstate) (pc : Z) : list sstate := filter (fun l => Z.eqb (ss_pc l) pc) (run_of S).
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_rad end.

(* malloc call *)
Definition E_m : sstate := Eval vm_compute in leaf_k Pre_rad 0.
Definition s_m : wsub := (15%positive, RA.vDp) :: infer_sub 10 E_m (Pre_malloc EC_U).
Definition R_m : list sobj := Eval vm_compute in optR (entails_fr E_m (Pre_malloc EC_U) s_m).
Definition vR : positive := 110.
Definition T_mnull : sstate := Eval vm_compute in T_after E_m s_m R_m (L_malloc_null EC_U).
Definition T_mok0 : sstate := Eval vm_compute in T_after E_m s_m R_m (L_malloc_ok EC_U).
Definition T_mok : sstate := add_facts (tv_facts (SVar vR, vNS)) T_mok0.

(* copy loop, one record (16 bytes) per pass: C_0 at a record boundary, D_k after k bytes *)
Definition X_cp0 : sstate := Eval vm_compute in nth 0 (leaves_at T_mok ra_L) Pre_rad.
Definition X_cp0s : sstate := Eval vm_compute in optS (apply_xforms X_cp0 [XSplit 1 (kb16 vK)]).

Definition vQ : sv := SVar 172.  Definition vF0 : sv := SVar 173.  Definition vF1 : sv := SVar 174.
Definition eoff (j : Z) : sv := SAlu ALU_ADD (SMd M_MUL (SLit 16) vQ) (SLit j).
Definition eoff0 : sv := SMd M_MUL (SLit 16) vQ.
Definition src_cells : list cell := [mkCell eoff0 8 vF0; mkCell (eoff 8) 8 vF1].
Definition q_facts : list sprop :=
  [SPBranch BC_LTU vQ vK; SPUle (eoff 16) (kb16 vK); SPUle (eoff 16) vOS; SPUle vQ (SLit two47)] ++ tmpl_inst [vF0; vF1] tmpl.
Definition loop_objs (os : list sobj) : list sobj :=
  match os with
  | o0 :: o1 :: o2 :: o3 :: o4 :: _ :: rest =>
      o0 :: mkObj (ob_base o1) (ob_lo o1) (ob_hi o1) [] (darr vQ) :: o2 :: o3 :: o4
         :: mkObj vP (SLit 0) vOS src_cells (darr vK) :: rest
  | _ => os
  end.
Definition loop_regs (i : sv) : list sv :=
  setregs (ss_regs X_cp0)
    [(14%nat, i); (5%nat, SVar 160); (6%nat, SVar 161); (7%nat, SVar 162);
     (17%nat, SVar 163); (28%nat, SVar 164); (29%nat, SVar 165); (30%nat, SVar 166); (31%nat, SVar 167)].
Definition C_0 : sstate :=
  mkSS ra_L (loop_regs eoff0) pre_fregs FcsrFrm0 None (loop_objs (ss_objs X_cp0s)) (q_facts ++ ss_facts X_cp0) 176 false.

Definition stepD (S : sstate) : sstate := nth 0 (leaves_at S ra_L) Pre_rad.
Definition D_1 : sstate := Eval vm_compute in stepD C_0.
Definition D_2 : sstate := Eval vm_compute in stepD D_1.
Definition D_3 : sstate := Eval vm_compute in stepD D_2.
Definition D_4 : sstate := Eval vm_compute in stepD D_3.
Definition D_5 : sstate := Eval vm_compute in stepD D_4.
Definition D_6 : sstate := Eval vm_compute in stepD D_5.
Definition D_7 : sstate := Eval vm_compute in stepD D_6.
Definition D_8 : sstate := Eval vm_compute in stepD D_7.
Definition D_9 : sstate := Eval vm_compute in stepD D_8.
Definition D_10 : sstate := Eval vm_compute in stepD D_9.
Definition D_11 : sstate := Eval vm_compute in stepD D_10.
Definition D_12 : sstate := Eval vm_compute in stepD D_11.
Definition D_13 : sstate := Eval vm_compute in stepD D_12.
Definition D_14 : sstate := Eval vm_compute in stepD D_13.
Definition D_15 : sstate := Eval vm_compute in stepD D_14.
Definition X_step : sstate := Eval vm_compute in stepD D_15.
Definition E_free : sstate := Eval vm_compute in nth 0 (leaves_at D_15 (ec_free EC_U)) Pre_rad.

Definition tiles2_l : list (nat * sv * Z * sv) := [(1%nat, eoff0, 8, vF0); (1%nat, eoff 8, 8, vF1)].
Definition tiles2 (S : sstate) : option sstate := tiles_at S tiles2_l.

Definition step_facts : list sprop :=
  [SPBranch BC_LTU (SAlu ALU_ADD vQ (SLit 1)) vK; SPUle (eoff 32) (kb16 vK); SPUle (eoff 32) vOS].
Definition X_t : sstate := Eval vm_compute in optS (tiles2 X_step).
Definition X_f : sstate := add_facts step_facts X_t.
Definition X_m : sstate := Eval vm_compute in optS (arr_mat_at X_f 5 (eoff 16) 8).
Definition s_step : wsub :=
  [(172%positive, SAlu ALU_ADD vQ (SLit 1)); (173%positive, SVar (ss_next X_f)); (174%positive, SVar (Pos.succ (ss_next X_f)))].

Definition cp0_facts : list sprop := [SPBranch BC_LTU (SLit 0) vK; SPUle (SLit 16) (kb16 vK); SPUle (SLit 16) vOS].
Definition X_cp0f : sstate := add_facts cp0_facts X_cp0s.
Definition X_cp0m : sstate := Eval vm_compute in optS (arr_mat_at X_cp0f 5 (SLit 0) 8).
Definition s_cp0 : wsub :=
  [(172%positive, SLit 0); (173%positive, SVar (ss_next X_cp0f)); (174%positive, SVar (Pos.succ (ss_next X_cp0f)))].

(* free of the old block once all records are copied *)
Definition free_facts : list sprop := [SPUle vK (SAlu ALU_ADD vQ (SLit 1))].
Definition E_ft : sstate := Eval vm_compute in optS (tiles2 E_free).
Definition E_ff : sstate := add_facts free_facts E_ft.
Definition trim_objs (os : list sobj) : list sobj :=
  match os with
  | o0 :: o1 :: o2 :: o3 :: o4 :: o5 :: rest =>
      o0 :: mkObj (ob_base o1) (ob_lo o1) (ob_hi o1) [] (darr vK) :: mkObj (ob_base o2) (ob_lo o2) (ob_hi o2) [] (ob_dflt o2)
         :: o3 :: o4 :: mkObj (ob_base o5) (ob_lo o5) (ob_hi o5) [] (ob_dflt o5) :: rest
  | _ => os
  end.
Definition E_fT1 : sstate := Eval vm_compute in set_objs E_ff (trim_objs (ss_objs E_ff)).
Definition E_freeT : sstate := Eval vm_compute in optS (TobjJVx.merge_arr_at E_fT1 1).
Definition s_f : wsub := (15%positive, RA.vDp) :: (13%positive, vOS) :: infer_sub 10 E_freeT (Pre_free EC_U).
Definition R_f : list sobj := Eval vm_compute in optR (entails_fr E_freeT (Pre_free EC_U) s_f).
Definition T_free : sstate := Eval vm_compute in T_after E_freeT s_f R_f (L_free EC_U).

(* bytes past the last whole record: byte loop *)
Definition vI : sv := SVar 175.
Definition B_objs (os : list sobj) : list sobj :=
  match os with
  | o0 :: o1 :: o2 :: o3 :: o4 :: _ :: rest =>
      o0 :: mkObj (ob_base o1) (ob_lo o1) (ob_hi o1) [] (darr vK) :: o2 :: o3 :: o4 :: mkObj vP (SLit 0) vOS [] (darr vK) :: rest
  | _ => os
  end.
Definition B_facts : list sprop := [SPUle (kb16 vK) vI; SPBranch BC_LTU vI vOS; SPBranch BC_LTU vI vNS].
Definition C_B : sstate :=
  mkSS ra_L (loop_regs vI) pre_fregs FcsrFrm0 None (B_objs (ss_objs X_cp0s)) (B_facts ++ ss_facts X_cp0) 176 false.
Definition cpB_facts : list sprop :=
  [SPUle vK (SLit 0); SPUle (kb16 vK) (SLit 0); SPBranch BC_LTU (SLit 0) vOS; SPBranch BC_LTU (SLit 0) vNS].
Definition X_cpB : sstate := add_facts cpB_facts X_cp0s.
Definition s_cpB : wsub := [(175%positive, SLit 0)].
Definition stepB_facts : list sprop :=
  [SPUle vK (SAlu ALU_ADD vQ (SLit 1)); SPUle (kb16 vK) (eoff 16); SPBranch BC_LTU (eoff 16) vOS; SPBranch BC_LTU (eoff 16) vNS].
Definition X_tB : sstate := add_facts stepB_facts X_t.
Definition s_stepB : wsub := [(175%positive, eoff 16)].
Definition E_freeB : sstate := Eval vm_compute in nth 0 (leaves_at C_B (ec_free EC_U)) Pre_rad.
Definition E_fBT1 : sstate := Eval vm_compute in set_objs E_freeB (trim_objs (ss_objs E_freeB)).
Definition E_freeBT : sstate := Eval vm_compute in optS (TobjJVx.merge_arr_at E_fBT1 1).
Definition s_fB : wsub := (15%positive, RA.vDp) :: (13%positive, vOS) :: infer_sub 10 E_freeBT (Pre_free EC_U).
Definition R_fB : list sobj := Eval vm_compute in optR (entails_fr E_freeBT (Pre_free EC_U) s_fB).
Definition T_freeB : sstate := Eval vm_compute in T_after E_freeBT s_fB R_fB (L_free EC_U).

Definition tv_m : list (sv * sv) := [(SVar vR, vNS); (vP, vOS)].
Definition tv_f : list (sv * sv) := [(SVar vR, vNS)].
Definition z0 : sv := SLit 0.
Definition VQ (c : Z) : sv :=
  SAlu ALU_SUB (SMd M_MUL (SLit 32) (SAlu ALU_SUB (SAlu ALU_ADD (SLit (two47 + 1)) vK) vQ)) (SLit c).
Definition VB : sv := SAlu ALU_SUB (SLit (2 ^ 48)) vI.

Definition cutsE : list edesc :=
  [(Pre_rad, tv0, (100, z0)); (T_mnull, tv0, (80, z0)); (T_mok, tv_m, (80, z0));
   (C_0, tv_m, (70, VQ 0)); (D_1, tv_m, (70, VQ 1)); (D_2, tv_m, (70, VQ 3)); (D_3, tv_m, (70, VQ 5));
   (D_4, tv_m, (70, VQ 7)); (D_5, tv_m, (70, VQ 9)); (D_6, tv_m, (70, VQ 11)); (D_7, tv_m, (70, VQ 13));
   (D_8, tv_m, (70, VQ 15)); (D_9, tv_m, (70, VQ 17)); (D_10, tv_m, (70, VQ 19)); (D_11, tv_m, (70, VQ 21));
   (D_12, tv_m, (70, VQ 23)); (D_13, tv_m, (70, VQ 25)); (D_14, tv_m, (70, VQ 27)); (D_15, tv_m, (70, VQ 29));
   (T_free, tv_f, (60, z0)); (C_B, tv_m, (68, VB)); (T_freeB, tv_f, (60, z0))].
Definition exitsE : list edesc :=
  [(E_m, tv0, (90, z0)); (X_cp0, tv_m, (75, z0)); (X_step, tv_m, (70, VQ 31)); (E_free, tv_m, (65, z0));
   (E_freeB, tv_m, (65, z0)); (P_fail_d, tv0, (0, z0)); (P_ok_d, tvP, (0, z0))].

Lemma ejcert_ok : ejcert segsU NF FUEL_ra cutpcs_ra 100 cutsE exitsE = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma call_m_ok : call_checkT C_U NF E_m (Pre_malloc EC_U) s_m R_m [L_malloc_null EC_U; L_malloc_ok EC_U] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma call_f_ok : call_checkT C_U NF E_freeT (Pre_free EC_U) s_f R_f [L_free EC_U] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma call_fB_ok : call_checkT C_U NF E_freeBT (Pre_free EC_U) s_fB R_fB [L_free EC_U] = true.
Proof. vm_compute. reflexivity. Qed.

Ltac find_idx F l := lazymatch l with | F :: _ => constr:(O) | _ :: ?t => let i := find_idx F t in constr:(S i) end.
Ltac have_fact HF F :=
  lazymatch type of HF with Forall _ ?l =>
    let l' := eval vm_compute in l in let F' := eval vm_compute in F in let i := find_idx F' l' in
    pose proof (Forall_pick _ _ i F HF eq_refl) end.

Lemma cp0_facts_ok : forall rho, bv_unsigned (rw rho 53%positive) <> 0 ->
  Forall (holds rho) (ss_facts X_cp0s) -> Forall (holds rho) cp0_facts.
Proof.
  intros rho Hk HF.
  have_fact HF (SPUle (kb16 vK) vOS). have_fact HF (SPUle vK (SLit two47)). clear HF.
  unfold cp0_facts, kb16, vOS, vK, RA.vOS, two47, RA.two47 in *. zfacts; lia.
Qed.

Lemma cpB_facts_ok : forall rho, bv_unsigned (rw rho 53%positive) = 0 ->
  Forall (holds rho) (ss_facts X_cp0s) -> Forall (holds rho) cpB_facts.
Proof.
  intros rho Hk HF.
  have_fact HF (SPUle (SLit 1) vOS). have_fact HF (SPBranch BC_LTU vOS vNS). clear HF.
  unfold cpB_facts, kb16, vOS, vNS, vK, RA.vOS, RA.vNS in *. zfacts; lia.
Qed.

Lemma step_facts_ok : forall rho, bv_unsigned (rw rho 172%positive) + 1 < bv_unsigned (rw rho 53%positive) ->
  Forall (holds rho) (ss_facts X_step) -> Forall (holds rho) step_facts.
Proof.
  intros rho Hlt HF.
  have_fact HF (SPUle vQ (SLit two47)). have_fact HF (SPUle vK (SLit two47)).
  have_fact HF (SPUle (kb16 vK) vOS). clear HF.
  unfold step_facts, eoff, kb16, vQ, vK, vOS, RA.vOS, two47, RA.two47 in *. zfacts; lia.
Qed.

Lemma stepB_facts_ok : forall rho, ~ (bv_unsigned (rw rho 172%positive) + 1 < bv_unsigned (rw rho 53%positive)) ->
  Forall (holds rho) (ss_facts X_step) -> Forall (holds rho) stepB_facts.
Proof.
  intros rho Hge HF.
  have_fact HF (SPBranch BC_NE vOS (eoff 16)). have_fact HF (SPUle (eoff 16) (kb16 vK)).
  have_fact HF (SPUle vQ (SLit two47)). have_fact HF (SPUle vK (SLit two47)).
  have_fact HF (SPUle (kb16 vK) vOS). have_fact HF (SPBranch BC_LTU vOS vNS). clear HF.
  unfold stepB_facts, eoff, kb16, vQ, vK, vOS, vNS, RA.vOS, RA.vNS, two47, RA.two47 in *. zfacts; lia.
Qed.

Lemma free_facts_ok : forall rho, Forall (holds rho) (ss_facts E_free) -> Forall (holds rho) free_facts.
Proof.
  intros rho HF.
  have_fact HF (SPNot (SPBranch BC_NE vOS (eoff 16))). have_fact HF (SPUle (eoff 16) (kb16 vK)).
  have_fact HF (SPUle vQ (SLit two47)). have_fact HF (SPUle vK (SLit two47)).
  have_fact HF (SPUle (kb16 vK) vOS). clear HF.
  unfold free_facts, eoff, kb16, vQ, vK, vOS, RA.vOS, two47, RA.two47 in *. zfacts; lia.
Qed.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis ML : malloc_laws segsU C_U.
Hypothesis MC : malloc_contracts segsU C_U EC_U.

Let nI : sstate * list (sv * sv) -> jnode := nodeI segsU C_U NF Kc rho0 P0_rad FB.
Let JGv (tv : list (sv * sv)) : jpred := JG segsU C_U NF Kc rho0 P0_rad FB tv.
Let Q : assn := LQP segsU NF rho0 (Posts_rad Kc FB).

Lemma robjs_nil : forall Ai x rho, robjs_ok segsU C_U Ai x rho [].
Proof. intros Ai x rho o a Ho. destruct Ho. Qed.
Lemma robjs_cons : forall Ai x rho o R,
  (forall a, fst (obj_range rho o) <= a < snd (obj_range rho o) -> caddr segsU C_U Ai x a) ->
  robjs_ok segsU C_U Ai x rho R -> robjs_ok segsU C_U Ai x rho (o :: R).
Proof. intros Ai x rho o R Ho HR o' a [<-|Hin] Hr; [exact (Ho a Hr) | exact (HR o' a Hin Hr)]. Qed.

Lemma stack_obj_caddr : forall Ai x rho b lo hi cells d,
  - 2 ^ 63 <= lo < 2 ^ 63 -> - 2 ^ 63 <= hi < 2 ^ 63 ->
  T_ok rho (topL (ma_L Ai)) ->
  bv_unsigned (rw rho 30%positive) <= bv_unsigned (eval rho b) + lo ->
  forall a, fst (obj_range rho (mkObj b (SLit lo) (SLit hi) cells d)) <= a <
            snd (obj_range rho (mkObj b (SLit lo) (SLit hi) cells d)) -> caddr segsU C_U Ai x a.
Proof.
  intros Ai x rho b lo hi cells d Hlo Hhi [HT _] Hb a Hr. left. unfold V_TOP in HT. rewrite <- HT.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite !soff_lit_small in Hr by lia. lia.
Qed.

Lemma block_obj_caddr : forall Ai x rho b hi cells d bb n,
  bv_unsigned (eval rho b) = bb ->
  (0 < Zsigned (bv_unsigned (eval rho hi)) ->
     In (bb, n) (ma_blocks Ai) /\ x <> Some bb /\ Zsigned (bv_unsigned (eval rho hi)) <= n) ->
  forall a, fst (obj_range rho (mkObj b (SLit 0) hi cells d)) <= a <
            snd (obj_range rho (mkObj b (SLit 0) hi cells d)) -> caddr segsU C_U Ai x a.
Proof.
  intros Ai x rho b hi cells d bb n Hb H a Hr. right; right.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite bv_signed_U, Hb in Hr.
  destruct (H ltac:(lia)) as (Hin & Hx & Hn). exists bb, n. split; [exact Hin|]. split; [exact Hx|]. lia.
Qed.

Lemma tnz_var : forall rho v sz, tnz rho (SVar v, sz) <-> bv_unsigned (rw rho v) <> 0.
Proof. intros. unfold tnz. cbn [fst eval]. tauto. Qed.

Lemma old_blk_ok : forall rho Ai tv x,
  holds rho (SPUle (SLit 4096) vP) -> holds rho (SPUle vOS (SLit RA.hiA)) ->
  tvin FB Ai rho tv -> In (vP, vOS) tv -> x <> Some (bv_unsigned (rw rho 13%positive)) ->
  forall a, fst (obj_range rho O_old) <= a < snd (obj_range rho O_old) -> caddr segsU C_U Ai x a.
Proof.
  intros rho Ai tv x H1 H2 HN Hin Hx.
  assert (Hnz : bv_unsigned (rw rho 13%positive) <> 0) by (unfold vP, RA.vP in H1; zfacts; lia).
  destruct (proj1 (Forall_forall _ _) HN _ Hin (proj2 (tnz_var rho _ _) Hnz)) as (_ & X & _).
  unfold tvv in X. cbn [fst snd] in X. unfold vP, vOS, RA.vP, RA.vOS in X. rewrite !eval_var in X.
  eapply (block_obj_caddr Ai x rho vP vOS [] (darr vK) _ (bv_unsigned (rw rho 14%positive)));
    [unfold vP, RA.vP; rewrite eval_var; reflexivity|].
  intros _. split; [exact X|]. split; [exact Hx|].
  unfold vOS, RA.vOS. rewrite eval_var. unfold vOS, RA.vOS, RA.hiA, S_vr.hiA in H2.
  destruct (Zsigned_spec (bv_unsigned (rw rho 14%positive))) as [[_ E]|[_ E]]; rewrite E;
    pose proof (bv_urange (rw rho 14%positive)); zfacts; lia.
Qed.

Lemma R_m_ok : forall rho Ai tv,
  Forall (holds rho) (ss_facts E_m) -> tvin FB Ai rho tv -> In (vP, vOS) tv ->
  T_ok rho (topL (ma_L Ai)) -> robjs_ok segsU C_U Ai None rho R_m.
Proof.
  intros rho Ai tv HF HN Hin HT.
  have_fact HF (SPUle (SVar 30) (SAlu ALU_ADD (SAlu ALU_ADD (SVar 10) (SLit (-48))) (SVar 19))).
  have_fact HF (SPBranch BC_GE (SLit (-784)) (SVar 19)). have_fact HF (SPBranch BC_GE (SVar 19) (SLit (- 2 ^ 40))).
  have_fact HF (SPUle (SVar 10) (SLit two47)). have_fact HF (SPUle (SVar 30) (SVar 10)).
  have_fact HF (SPUle (SVar 30) vA). have_fact HF (SPUle vA (SLit two47)).
  have_fact HF (SPUle (SLit 4096) vP). have_fact HF (SPUle vOS (SLit RA.hiA)). clear HF.
  apply robjs_cons; [|apply robjs_cons; [|apply robjs_cons; [|apply robjs_nil]]].
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30.
    rewrite eval_var. clear HN Hin. unfold vA, RA.vA, two47, RA.two47 in *. zfacts; lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30.
    rewrite eval_var. clear HN Hin. unfold vA, RA.vA, two47, RA.two47 in *. zfacts; lia.
  - eapply (old_blk_ok rho Ai tv); try eassumption. discriminate.
Qed.

Lemma R_f_ok : forall rho Ai,
  Forall (holds rho) (ss_facts E_freeT) -> tvin FB Ai rho tv_m -> tvd rho tv_m ->
  (exists rhoM md, MInvR segsU C_U Ai rhoM md) -> T_ok rho (topL (ma_L Ai)) ->
  robjs_ok segsU C_U Ai (Some (bv_unsigned (rw rho 13%positive))) rho R_f.
Proof.
  intros rho Ai HF HN HD (rhoM & md & HM) HT.
  have_fact HF (SPUle (SVar 30) (SAlu ALU_ADD (SAlu ALU_ADD (SVar 10) (SLit (-48))) (SVar 19))).
  have_fact HF (SPBranch BC_GE (SLit (-784)) (SVar 19)). have_fact HF (SPBranch BC_GE (SVar 19) (SLit (- 2 ^ 40))).
  have_fact HF (SPUle (SVar 10) (SLit two47)). have_fact HF (SPUle (SVar 30) (SVar 10)).
  have_fact HF (SPUle (SVar 30) vA). have_fact HF (SPUle vA (SLit two47)).
  have_fact HF (SPUle (SLit 4096) vP). have_fact HF (SPUle (SLit 4096) (SVar vR)).
  have_fact HF (SPUle vNS (SLit RA.hiA)). clear HF.
  assert (Hn : bv_unsigned (rw rho vR) <> 0) by (unfold vR in *; zfacts; lia).
  assert (Hd : bv_unsigned (rw rho 13%positive) <> 0) by (unfold vP, RA.vP in *; zfacts; lia).
  destruct (proj1 (Forall_forall _ _) HN (SVar vR, vNS) ltac:(left; reflexivity) (proj2 (tnz_var rho _ _) Hn)) as (Npos & NinA & _).
  destruct (proj1 (Forall_forall _ _) HN (vP, vOS) ltac:(right; left; reflexivity) (proj2 (tnz_var rho _ _) Hd)) as (Dpos & DinA & _).
  unfold tvv in NinA, DinA, Npos, Dpos. cbn [fst snd] in NinA, DinA, Npos, Dpos.
  unfold vP, vOS, vNS, RA.vP, RA.vOS, RA.vNS in *. rewrite !eval_var in NinA, DinA, Npos, Dpos.
  assert (Hne : bv_unsigned (rw rho vR) <> bv_unsigned (rw rho 13%positive)).
  { destruct HD as [HD1 _]. specialize (HD1 (vP, vOS) ltac:(left; reflexivity)
      (proj2 (tnz_var rho _ _) Hn) (proj2 (tnz_var rho _ _) Hd)).
    unfold tvv in HD1. cbn [fst snd] in HD1. unfold vP, vOS, vNS, RA.vP, RA.vOS, RA.vNS in HD1. rewrite !eval_var in HD1.
    eapply (blocks_bases_differ segsU C_U Ai rhoM md); eauto. }
  apply robjs_cons; [|apply robjs_cons; [|apply robjs_cons; [|apply robjs_nil]]].
  - eapply (block_obj_caddr Ai (Some _) rho (SVar vR) (SVar 33) _ (darr vK) (bv_unsigned (rw rho vR)) (bv_unsigned (rw rho 33%positive)));
      [rewrite eval_var; reflexivity|].
    intros _. split; [exact NinA|]. split; [congruence|]. rewrite eval_var.
    destruct (Zsigned_spec (bv_unsigned (rw rho 33%positive))) as [[_ X]|[_ X]]; rewrite X; pose proof (bv_urange (rw rho 33%positive)); lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30.
    rewrite eval_var. clear HN HD HM NinA DinA Hne Npos Dpos Hd Hn. unfold vA, RA.vA, two47, RA.two47 in *. zfacts; lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30.
    rewrite eval_var. clear HN HD HM NinA DinA Hne Npos Dpos Hd Hn. unfold vA, RA.vA, two47, RA.two47 in *. zfacts; lia.
Qed.

Lemma R_fB_ok : forall rho Ai,
  Forall (holds rho) (ss_facts E_freeBT) -> tvin FB Ai rho tv_m -> tvd rho tv_m ->
  (exists rhoM md, MInvR segsU C_U Ai rhoM md) -> T_ok rho (topL (ma_L Ai)) ->
  robjs_ok segsU C_U Ai (Some (bv_unsigned (rw rho 13%positive))) rho R_fB.
Proof.
  intros rho Ai HF HN HD (rhoM & md & HM) HT.
  have_fact HF (SPUle (SVar 30) (SAlu ALU_ADD (SAlu ALU_ADD (SVar 10) (SLit (-48))) (SVar 19))).
  have_fact HF (SPBranch BC_GE (SLit (-784)) (SVar 19)). have_fact HF (SPBranch BC_GE (SVar 19) (SLit (- 2 ^ 40))).
  have_fact HF (SPUle (SVar 10) (SLit two47)). have_fact HF (SPUle (SVar 30) (SVar 10)).
  have_fact HF (SPUle (SVar 30) vA). have_fact HF (SPUle vA (SLit two47)).
  have_fact HF (SPUle (SLit 4096) vP). have_fact HF (SPUle (SLit 4096) (SVar vR)).
  have_fact HF (SPUle vNS (SLit RA.hiA)). clear HF.
  assert (Hn : bv_unsigned (rw rho vR) <> 0) by (unfold vR in *; zfacts; lia).
  assert (Hd : bv_unsigned (rw rho 13%positive) <> 0) by (unfold vP, RA.vP in *; zfacts; lia).
  destruct (proj1 (Forall_forall _ _) HN (SVar vR, vNS) ltac:(left; reflexivity) (proj2 (tnz_var rho _ _) Hn)) as (Npos & NinA & _).
  destruct (proj1 (Forall_forall _ _) HN (vP, vOS) ltac:(right; left; reflexivity) (proj2 (tnz_var rho _ _) Hd)) as (Dpos & DinA & _).
  unfold tvv in NinA, DinA, Npos, Dpos. cbn [fst snd] in NinA, DinA, Npos, Dpos.
  unfold vP, vOS, vNS, RA.vP, RA.vOS, RA.vNS in *. rewrite !eval_var in NinA, DinA, Npos, Dpos.
  assert (Hne : bv_unsigned (rw rho vR) <> bv_unsigned (rw rho 13%positive)).
  { destruct HD as [HD1 _]. specialize (HD1 (vP, vOS) ltac:(left; reflexivity)
      (proj2 (tnz_var rho _ _) Hn) (proj2 (tnz_var rho _ _) Hd)).
    unfold tvv in HD1. cbn [fst snd] in HD1. unfold vP, vOS, vNS, RA.vP, RA.vOS, RA.vNS in HD1. rewrite !eval_var in HD1.
    eapply (blocks_bases_differ segsU C_U Ai rhoM md); eauto. }
  apply robjs_cons; [|apply robjs_cons; [|apply robjs_cons; [|apply robjs_nil]]].
  - eapply (block_obj_caddr Ai (Some _) rho (SVar vR) (SVar 33) _ (darr vK) (bv_unsigned (rw rho vR)) (bv_unsigned (rw rho 33%positive)));
      [rewrite eval_var; reflexivity|].
    intros _. split; [exact NinA|]. split; [congruence|]. rewrite eval_var.
    destruct (Zsigned_spec (bv_unsigned (rw rho 33%positive))) as [[_ X]|[_ X]]; rewrite X; pose proof (bv_urange (rw rho 33%positive)); lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30.
    rewrite eval_var. clear HN HD HM NinA DinA Hne Npos Dpos Hd Hn. unfold vA, RA.vA, two47, RA.two47 in *. zfacts; lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30.
    rewrite eval_var. clear HN HD HM NinA DinA Hne Npos Dpos Hd Hn. unfold vA, RA.vA, two47, RA.two47 in *. zfacts; lia.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall J S rho (Q' : assn),
  (Forall (holds rho) (ss_facts S) -> TR (SPJ segsU J S rho) Q') -> TR (SPJ segsU J S rho) Q'.
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segsU (J x) S rho) Q') -> TR (SPJ segsU (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : forall (P P' Q' : assn), (forall w, P' w -> P w) -> TR P Q' -> TR P' Q'.
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : forall (X : Prop) P Q', (X -> TR P Q') -> TR (fun w => X /\ P w) Q'.
Hypothesis TR_callP : forall (J Jp : jpred) (C Pre : sstate) (s : wsub) (R : list sobj)
    (Posts : list (sstate * jpost)) (Q' : assn) (rho : valuation),
  entails_fr C Pre s = Some R ->
  call_checkP C Pre s R (map fst Posts) = true ->
  (forall rho1, TR (SPJ segsU Jp Pre rho1) (LQP segsU (ss_next Pre) rho1 Posts)) ->
  (forall tr ms md, smatch segsU rho C (tr, mkCfg ms md) -> J rho tr md -> Jp (rho_sub (rho_absorb rho R ms) s) tr md) ->
  (forall L JL tr ms md rhoL tr' ms' md', In (L, JL) Posts ->
     smatch segsU rho C (tr, mkCfg ms md) -> J rho tr md ->
     agree_vals (ss_next Pre) (rho_sub (rho_absorb rho R ms) s) rhoL ->
     smatch segsU rhoL L (tr', mkCfg ms' md') ->
     JL (rho_sub (rho_absorb rho R ms) s) rhoL tr' md' ->
     import_okP rho ms R s Pre L rhoL /\
     (forall rho', call_linkP rho ms R s Pre C L rho' rhoL ->
        TR (SPJ segsU (J_ofP JL (rho_sub (rho_absorb rho R ms) s) rhoL) (import_post s (ss_next Pre) L (ss_next C) R) rho') Q')) ->
  TR (SPJ segsU J C rho) Q'.
Hypothesis CMALLOC : forall Ai rho1,
  TR (SPJ segsU (J_alloc_pre segsU C_U Ai Kc) (Pre_malloc EC_U) rho1) (LQP segsU NF rho1 (Posts_malloc segsU C_U EC_U Ai Kc)).
Hypothesis CFREE : forall Ai rho1,
  TR (SPJ segsU (J_free_pre segsU C_U Ai Kc) (Pre_free EC_U) rho1) (LQP segsU NF rho1 [(L_free EC_U, JL_free segsU C_U Ai Kc)]).
Hypothesis REENTER : forall T tv rv rho b, In ((T, tv), rv) cutsE ->
  0 <= emeas ((T, tv), rv) rho < b -> TR (SPJ segsU (JGv tv) T rho) (FAM b).
Hypothesis POST : forall P tv rho b,
  In (P, JLG segsU C_U Kc P0_rad FB tv) (Posts_rad Kc FB) -> TR (SPJ segsU (JGv tv) P rho) (FAM b).

Let MALLOC := malloc_callT segsU C_U EC_U NF Kc rho0 P0_rad FB ML TR TR_facts TR_ex TR_pre TR_callP.
Let FREE := free_callT segsU C_U EC_U NF Kc rho0 P0_rad FB ML TR TR_facts TR_ex TR_pre TR_callP.
Let ENTES := entEs_TR segsU C_U NF Kc rho0 P0_rad FB ML TR TR_pre TR_exw TR_pureh.

Lemma reenter_rank : forall T tv rT vT (X : edesc) rhoX rho,
  In (T, tv, (rT, vT)) cutsE -> 0 <= rT -> rT + 1 <= ed_rank X ->
  TR (SPJ segsU (JGv tv) T rho) (FAM (emeas X rhoX)).
Proof using REENTER.
  intros T tv rT vT X rhoX rho Hin H0 Hr. apply (REENTER T tv (rT, vT) rho); [exact Hin|].
  unfold emeas, ed_rank, ed_var in *. cbn [fst snd] in *.
  pose proof (urange (eval rho vT)). pose proof (urange (eval rhoX (snd (snd X)))). nia.
Qed.
Ltac reenter T tv rT vT := apply (reenter_rank T tv rT vT); [cbn; tauto | lia | cbn; lia].

Lemma X_P_fail : forall rho b, TR (SPJ segsU (JGv tv0) P_fail_d rho) (FAM b).
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_ok : forall rho b, TR (SPJ segsU (JGv tvP) P_ok_d rho) (FAM b).
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_E_m : forall rho, TR (SPJ segsU (JGv tv0) E_m rho) (FAM (emeas (E_m, tv0, (90, z0)) rho)).
Proof using CMALLOC MALLOC REENTER nI.
  intros rho.
  apply (MALLOC E_m s_m R_m rho tv0 _ CMALLOC).
  - vm_compute. reflexivity.
  - exact call_m_ok.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HM HT. split.
    + exact (R_m_ok rho Ai tv0 HF HN ltac:(left; reflexivity) HT).
    + change (wsub_get s_m 12) with vNS.
      have_fact HF (SPUle (SLit 1) vOS). have_fact HF (SPUle vOS vNS). have_fact HF (SPUle vOS (SLit RA.hiA)). clear HF.
      unfold vNS, vOS, RA.vNS, RA.vOS, RA.hiA, S_vr.hiA in *. zfacts; lia.
  - intros rho'.
    replace (T_after E_m s_m R_m (L_malloc_null EC_U)) with T_mnull by (vm_compute; reflexivity).
    reenter T_mnull tv0 80 z0.
  - intros rho'.
    replace (T_after E_m s_m R_m (L_malloc_ok EC_U)) with T_mok0 by (vm_compute; reflexivity).
    change (pos_add_nat (ss_next E_m) 10) with vR. change (wsub_get s_m 12) with vNS.
    eapply TR_pre; [ | reenter T_mok tv_m 80 z0 ].
    intros w Hw. unfold T_mok. apply SPJ_refacts_J; [exact Hw | reflexivity |].
    intros tr md HJ HF.
    eapply (JG_tv_facts segsU C_U NF Kc rho0 P0_rad FB); [exact HJ | left; reflexivity |].
    apply tnz_of_fact. have_fact HF (SPNot (SPBranch BC_EQ (SVar vR) (SLit 0))). assumption.
Qed.

Lemma X_cp0_ok : forall rho, TR (SPJ segsU (JGv tv_m) X_cp0 rho) (FAM (emeas (X_cp0, tv_m, (75, z0)) rho)).
Proof using ENTES REENTER.
  intros rho.
  apply (TR_pre (SPJ segsU (JGv tv_m) X_cp0s rho)).
  { intros w Hw. exact (SPJ_xforms segsU _ [XSplit 1 (kb16 vK)] rho X_cp0 X_cp0s w ltac:(vm_compute; reflexivity) Hw). }
  destruct (Z.eq_dec (bv_unsigned (rw rho 53%positive)) 0) as [Hk|Hk].
  { apply (TR_pre (SPJ segsU (JGv tv_m) X_cpB rho)).
    { intros w Hw. unfold X_cpB. apply SPJ_refacts_J; [exact Hw | reflexivity |].
      intros tr md _ HF. exact (cpB_facts_ok rho Hk HF). }
    apply (ENTES s_cpB (ss_next X_cpB) X_cpB C_B tv_m tv_m tv_m VB 68 75 z0 rho rho).
    - vm_cast_no_check (@eq_refl bool true).
    - apply Permutation_refl.
    - apply agree_vals_refl.
    - intros rho'' Hm. apply (REENTER C_B tv_m (68, VB) rho''); [apply (nth_error_In cutsE 20); reflexivity | rewrite TobjJVx.emeas_emeasZ; exact Hm]. }
  apply (TR_pre (fun w => exists rho', agree_below (ss_next X_cp0f) rho rho' /\ SPJ segsU (JGv tv_m) X_cp0m rho' w)).
  { intros w Hw. apply (SPJ_arr_mat segsU (JGv tv_m) rho X_cp0f 5 (SLit 0) 8 X_cp0m w); [vm_compute; reflexivity | |].
    - apply (stableJ_JG segsU C_U NF Kc rho0 P0_rad FB ML); [apply (proj1 (Pos.leb_le _ _)); reflexivity | reflexivity].
    - unfold X_cp0f. apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md _ HF. exact (cp0_facts_ok rho Hk HF). }
  apply TR_exw; intros rho'. apply TR_pureh; intros Hag.
  apply (ENTES s_cp0 (ss_next X_cp0f) X_cp0m C_0 tv_m tv_m tv_m (VQ 0) 70 75 z0 rho rho').
  - vm_cast_no_check (@eq_refl bool true).
  - apply Permutation_refl.
  - apply agree_below_vals. exact Hag.
  - intros rho'' Hm. apply (REENTER C_0 tv_m (70, VQ 0) rho''); [apply (nth_error_In cutsE 3); reflexivity | rewrite TobjJVx.emeas_emeasZ; exact Hm].
Qed.

Lemma X_step_ok : forall rho, TR (SPJ segsU (JGv tv_m) X_step rho) (FAM (emeas (X_step, tv_m, (70, VQ 31)) rho)).
Proof using ENTES REENTER.
  intros rho.
  destruct (Z_lt_dec (bv_unsigned (rw rho 172%positive) + 1) (bv_unsigned (rw rho 53%positive))) as [Hlt|Hge].
  2: { apply (TR_pre (SPJ segsU (JGv tv_m) X_tB rho)).
       { intros w Hw. unfold X_tB. apply SPJ_refacts_J; [ | reflexivity | intros tr md _ HF; exact (stepB_facts_ok rho Hge HF)].
         apply (SPJ_tiles segsU (JGv tv_m) rho tiles2_l X_step X_t w); [vm_compute; reflexivity | exact Hw]. }
       apply (ENTES s_stepB (ss_next X_tB) X_tB C_B tv_m tv_m tv_m VB 68 70 (VQ 31) rho rho).
       - vm_cast_no_check (@eq_refl bool true).
       - apply Permutation_refl.
       - apply agree_vals_refl.
       - intros rho'' Hm. apply (REENTER C_B tv_m (68, VB) rho''); [apply (nth_error_In cutsE 20); reflexivity | rewrite TobjJVx.emeas_emeasZ; exact Hm]. }
  apply (TR_pre (fun w => exists rho', agree_below (ss_next X_f) rho rho' /\ SPJ segsU (JGv tv_m) X_m rho' w)).
  { intros w Hw. apply (SPJ_arr_mat segsU (JGv tv_m) rho X_f 5 (eoff 16) 8 X_m w); [vm_compute; reflexivity | |].
    - apply (stableJ_JG segsU C_U NF Kc rho0 P0_rad FB ML); [apply (proj1 (Pos.leb_le _ _)); reflexivity | reflexivity].
    - unfold X_f. apply SPJ_refacts_J; [ | reflexivity | intros tr md _ HF; exact (step_facts_ok rho Hlt HF)].
      apply (SPJ_tiles segsU (JGv tv_m) rho tiles2_l X_step X_t w); [vm_compute; reflexivity | exact Hw]. }
  apply TR_exw; intros rho'. apply TR_pureh; intros Hag.
  apply (ENTES s_step (ss_next X_f) X_m C_0 tv_m tv_m tv_m (VQ 0) 70 70 (VQ 31) rho rho').
  - vm_cast_no_check (@eq_refl bool true).
  - apply Permutation_refl.
  - apply agree_below_vals. exact Hag.
  - intros rho'' Hm. apply (REENTER C_0 tv_m (70, VQ 0) rho''); [apply (nth_error_In cutsE 3); reflexivity | rewrite TobjJVx.emeas_emeasZ; exact Hm].
Qed.

Lemma X_E_free : forall rho, TR (SPJ segsU (JGv tv_m) E_free rho) (FAM (emeas (E_free, tv_m, (65, z0)) rho)).
Proof using CFREE FREE REENTER nI.
  intros rho.
  apply (TR_pre (SPJ segsU (JGv tv_m) E_freeT (rho_sub rho []))).
  { intros w Hw. apply (TobjJVx.SPJ_merge_arr segsU (JGv tv_m) (rho_sub rho []) E_fT1 1 E_freeT w); [vm_compute; reflexivity|].
    apply (SPJ_entails_JG segsU C_U NF Kc rho0 P0_rad FB ML E_ff E_fT1 [] tv_m tv_m rho w);
      [vm_cast_no_check (@eq_refl bool true) | reflexivity | reflexivity | reflexivity | reflexivity | ].
    unfold E_ff. apply SPJ_refacts_J; [ | reflexivity | intros tr md _ HF; exact (free_facts_ok rho HF)].
    apply (SPJ_tiles segsU (JGv tv_m) rho tiles2_l E_free E_ft w); [vm_compute; reflexivity | exact Hw]. }
  apply (FREE E_freeT s_f R_f (rho_sub rho []) tv_m 1%nat (vP, vOS) _ CFREE).
  - vm_compute. reflexivity.
  - exact call_f_ok.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HM HT.
    change (wsub_get s_f 12) with vP. change (wsub_get s_f 13) with vOS.
    split; [|split; [reflexivity|]].
    + unfold vP, RA.vP. apply (proj2 (tnz_var _ 13%positive vOS)).
      have_fact HF (SPUle (SLit 4096) vP). unfold vP, RA.vP in *. zfacts; lia.
    + unfold vP at 1, RA.vP. rewrite eval_var. exact (R_f_ok _ Ai HF HN HD HM HT).
  - intros rho'.
    replace (T_after E_freeT s_f R_f (L_free EC_U)) with T_free by (vm_compute; reflexivity).
    reenter T_free tv_f 60 z0.
Qed.

Lemma X_E_freeB : forall rho, TR (SPJ segsU (JGv tv_m) E_freeB rho) (FAM (emeas (E_freeB, tv_m, (65, z0)) rho)).
Proof using CFREE FREE REENTER nI.
  intros rho.
  apply (TR_pre (SPJ segsU (JGv tv_m) E_freeBT (rho_sub rho []))).
  { intros w Hw. apply (TobjJVx.SPJ_merge_arr segsU (JGv tv_m) (rho_sub rho []) E_fBT1 1 E_freeBT w); [vm_compute; reflexivity|].
    apply (SPJ_entails_JG segsU C_U NF Kc rho0 P0_rad FB ML E_freeB E_fBT1 [] tv_m tv_m rho w);
      [vm_cast_no_check (@eq_refl bool true) | reflexivity | reflexivity | reflexivity | reflexivity | ].
    exact Hw. }
  apply (FREE E_freeBT s_fB R_fB (rho_sub rho []) tv_m 1%nat (vP, vOS) _ CFREE).
  - vm_compute. reflexivity.
  - exact call_fB_ok.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HM HT.
    change (wsub_get s_fB 12) with vP. change (wsub_get s_fB 13) with vOS.
    split; [|split; [reflexivity|]].
    + unfold vP, RA.vP. apply (proj2 (tnz_var _ 13%positive vOS)).
      have_fact HF (SPUle (SLit 4096) vP). unfold vP, RA.vP in *. zfacts; lia.
    + unfold vP at 1, RA.vP. rewrite eval_var. exact (R_fB_ok _ Ai HF HN HD HM HT).
  - intros rho'.
    replace (T_after E_freeBT s_fB R_fB (L_free EC_U)) with T_freeB by (vm_compute; reflexivity).
    reenter T_freeB tv_f 60 z0.
Qed.

Lemma exits_okT : forall X tvX rvX rho, In (X, tvX, rvX) exitsE ->
  TR (SPJ segsU (JGv tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).
Proof using CFREE CMALLOC ENTES FREE MALLOC POST REENTER nI.
  intros X tvX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; injection H as <- <- <-.
  - apply X_E_m.
  - apply X_cp0_ok.
  - apply X_step_ok.
  - apply X_E_free.
  - apply X_E_freeB.
  - apply X_P_fail.
  - apply X_P_ok.
Qed.
End SumT.

Theorem ra_darr_sum_S : triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc P0_rad FB tv0) Pre_rad rho0) Q.
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segsU C_U NF Kc rho0 P0_rad FB ML FUEL_ra cutpcs_ra 100 cutsE exitsE ok Q (proj1 HS)
                (ejcert_jcert segsU NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nI (map (@edrop) cutsE)) w \/ Q w)
                (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
                (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segsU ok A P Q' H)
                (TobjJVx.triple_pureh segsU ok)
                (call_soundP segsU ok)).
       - intros Ai rho1. apply (mc_malloc _ _ _ MC). exact HS.
       - intros Ai rho1. apply (mc_free _ _ _ MC). exact HS.
       - intros T tv rv rho b Hin _. exact (reenter_cutGE segsU C_U NF Kc rho0 P0_rad FB ok cutsE T tv rv Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segsU C_U NF Kc P0_rad FB ok rho0 tv (Posts_rad Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.

Theorem ra_darr_sum_E : etriple segsU (SPJ segsU (JG_pre segsU C_U Kc P0_rad FB tv0) Pre_rad rho0) Q.
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segsU C_U NF Kc rho0 P0_rad FB ML FUEL_ra cutpcs_ra 100 cutsE exitsE Q ejcert_ok)
         with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeI segsU C_U NF Kc rho0 P0_rad FB) cutsE) b w \/ Q w)
                (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
                (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segsU A P Q' H)
                (TobjJVx.etriple_pureh segsU)
                (call_completeP segsU)).
       - intros Ai rho1. apply (mcx_malloc _ _ _ MCX). exact Hvi.
       - intros Ai rho1. apply (mcx_free _ _ _ MCX). exact Hvi.
       - intros T tv rv rho b Hin Hm. exact (ereenter_cutE segsU C_U NF Kc rho0 P0_rad FB cutsE T tv rv Q b rho Hin Hm).
       - intros P tv rho b Hin. apply (eexit_postG segsU C_U NF Kc P0_rad FB rho0 tv (Posts_rad Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem ra_darr_sum : ra_darr_stmt_U.
Proof. intros ok Kc FB rho0 HS ML MC. apply ra_darr_sum_S; assumption. Qed.

Theorem ra_darr_sum_ex : ra_darr_ex_stmt_U.
Proof. intros Kc FB rho0 Hvi ML MCX. apply ra_darr_sum_E; assumption. Qed.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue TobjJV ObjUnbase ObjXform.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr S_bli.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require Import S_vrd.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require S_rad rad bli.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module RAD := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11.S_rad.

Definition vr_nc : Z := 0x16878.
Definition FUEL_vr : nat := 400%nat.
Definition cutpcs_vr : list Z := [vr_nc; RAD.ra_entry; ec_calloc EC_U].

Definition run_of (S : sstate) : list sstate :=
  match sym_run segsU FUEL_vr cutpcs_vr S true with Some ls => map lf_state ls | None => [] end.
Definition leaf_k (S : sstate) (k : nat) : sstate := nth k (run_of S) Pre_vr.
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_vr end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition v120 : sv := SVar 120.
Definition L2 : sstate := Eval vm_compute in leaf_k Pre_vr 2.
Definition C_nc : sstate := Eval vm_compute in
  mkSS vr_nc (setregs (ss_regs L2) [(8%nat, v120); (11%nat, SMd M_MULHU v120 (SLit 16))])
    pre_fregs FcsrFrm0 None (ss_objs L2)
    ([SPUle vW v120; SPBranch BC_LTU vK vW; SPBranch BC_EQ (SMd M_MULHU v120 (SLit 16)) (SLit 0); SPUle v120 (SLit two48)] ++ base_facts)
    121 false.

Definition E_ra0 : sstate := Eval vm_compute in leaf_k C_nc 1.
Definition E_ra1 : sstate := Eval vm_compute in optS (split_obj_at E_ra0 1 (SLit (-48))).
Definition E_ra2 : sstate := Eval vm_compute in optS (unbase_obj_at E_ra1 1 (-48)).
Definition ra_add : list sprop :=
  [SPUle (SVar 30) (spo (-32)); SPBranch BC_LTU (kb16 vK) (kb16 v120); SPUle (kb16 vC) (kb16 vK); SPUle vC (SLit two47)]
  ++ tv_facts (vD, kb16 vK).
Definition E_ra : sstate := add_facts ra_add E_ra2.
Definition s_ra : wsub :=
  (19%positive, SAlu ALU_ADD vDp (SLit 48)) :: (53%positive, vC) :: (52%positive, vL) :: infer_sub 10 E_ra RAD.Pre_rad.
Definition R_ra : list sobj := Eval vm_compute in optR (entails_fr E_ra RAD.Pre_rad s_ra).
Definition T_rf : sstate := Eval vm_compute in T_afterN NF E_ra s_ra R_ra RAD.P_fail_d.
Definition T_rok0 : sstate := Eval vm_compute in T_afterN NF E_ra s_ra R_ra RAD.P_ok_d.
Definition T_rok : sstate := add_facts [SPUle v120 (SLit hiA)] T_rok0.
Definition vM : sv := SVar 161.
Definition tv_rok : list (sv * sv) := [(vM, kb16 v120)].
Definition X_rf : sstate := Eval vm_compute in leaf_k T_rf 0.
Definition X_rok : sstate := Eval vm_compute in leaf_k T_rok 0.

Definition xs_r : list xform := [XRebase 0; XRebase 1; XSelect [1; 0; 2; 3; 4; 5]%nat; XMerge 0].
Definition X_rf2 : sstate := Eval vm_compute in optS (apply_xforms X_rf xs_r).
Definition X_rf3 : sstate := Eval vm_compute in optS (unbase_obj_at X_rf2 0 (-32)).
Definition sel_rf : list xform := [XSelect [3; 0; 4; 1; 2]%nat].
Definition X_rf4 : sstate := Eval vm_compute in optS (apply_xforms X_rf3 sel_rf).
Definition s_rf : wsub := infer_sub 100 X_rf4 P_fail.
Definition X_rok2 : sstate := Eval vm_compute in optS (apply_xforms X_rok xs_r).
Definition X_rok3 : sstate := Eval vm_compute in optS (unbase_obj_at X_rok2 0 (-32)).
Definition sel_rok : list xform := [XSelect [0; 2; 3; 4; 1]%nat].
Definition X_rok4 : sstate := Eval vm_compute in optS (apply_xforms X_rok3 sel_rok).
Definition s_rok : wsub := infer_sub 100 X_rok4 P_grown.

Definition E_c : sstate := Eval vm_compute in leaf_k C_nc 0.
Definition s_c : wsub := (15%positive, vDp) :: infer_sub 10 E_c (Pre_calloc EC_U).
Definition R_c : list sobj := Eval vm_compute in optR (entails_fr E_c (Pre_calloc EC_U) s_c).
Definition vN : positive := 131.
Definition T_cn : sstate := Eval vm_compute in T_after E_c s_c R_c (L_calloc_null (ec_ret_calloc EC_U)).
Definition T_cn2 : sstate := Eval vm_compute in T_after E_c s_c R_c (L_calloc_null (ec_ret_calloc2 EC_U)).
Definition T_co0 : sstate := Eval vm_compute in T_after E_c s_c R_c (L_calloc_ok (ec_ret_calloc EC_U)).
Definition T_co20 : sstate := Eval vm_compute in T_after E_c s_c R_c (L_calloc_ok (ec_ret_memset EC_U)).
Definition co_add : list sprop := SPUle v120 (SLit hiA) :: tv_facts (SVar vN, kb16 v120).
Definition T_co : sstate := add_facts co_add T_co0.
Definition T_co2 : sstate := add_facts co_add T_co20.
Definition tv_m : list (sv * sv) := [(SVar vN, kb16 v120); (vD, kb16 vK)].
Definition tv_f : list (sv * sv) := [(SVar vN, kb16 v120)].
Definition X_co : sstate := Eval vm_compute in leaf_k T_co 0.
Definition X_co2 : sstate := Eval vm_compute in leaf_k T_co2 0.

Definition set_hi (o : sobj) (h : sv) : sobj := mkObj (ob_base o) (ob_lo o) h (ob_cells o) (ob_dflt o).
Definition gcA (X : sstate) : sstate := add_facts [SPUle (kb16 vK) (SLit 0); SPUle vC (SLit 0)] X.
Definition gcB (X : sstate) : sstate :=
  set_objs (gcA X) (match ss_objs (gcA X) with o0 :: o1 :: rest => o0 :: set_hi o1 (kb16 v120) :: rest | l => l end).
Definition gcC (X : sstate) : sstate := set_objs (gcB X) (firstn 5 (ss_objs (gcB X))).

Definition z0 : sv := SLit 0.
Definition cutsE : list edesc :=
  [(Pre_vr, tv0, (100, z0)); (C_nc, tv0, (95, z0)); (T_rf, tv0, (80, z0)); (T_rok, tv_rok, (80, z0));
   (T_cn, tv0, (80, z0)); (T_cn2, tv0, (80, z0)); (T_co, tv_m, (80, z0)); (T_co2, tv_m, (80, z0))].
Definition exitsE : list edesc :=
  [(E_ra0, tv0, (90, z0)); (E_c, tv0, (90, z0)); (P_keep, tv0, (0, z0)); (P_fail, tv0, (0, z0));
   (X_rf, tv0, (0, z0)); (X_rok, tv_rok, (0, z0)); (X_co, tv_m, (0, z0)); (X_co2, tv_m, (0, z0))].

Lemma ejcert_ok : ejcert segsU NF FUEL_vr cutpcs_vr 100 cutsE exitsE = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma call_c_ok : call_checkT C_U NF E_c (Pre_calloc EC_U) s_c R_c
  [L_calloc_null (ec_ret_calloc EC_U); L_calloc_null (ec_ret_calloc2 EC_U);
   L_calloc_ok (ec_ret_calloc EC_U); L_calloc_ok (ec_ret_memset EC_U)] = true.
Proof. vm_compute. reflexivity. Qed.

Ltac find_idx F l := lazymatch l with | F :: _ => constr:(O) | _ :: ?t => let i := find_idx F t in constr:(S i) end.
Ltac have_fact HF F :=
  lazymatch type of HF with Forall _ ?l =>
    let l' := eval vm_compute in l in let F' := eval vm_compute in F in let i := find_idx F' l' in
    pose proof (Forall_pick _ _ i F HF eq_refl) end.
Ltac unf := unfold vV, vW, vA, vD, vC, vK, vDp, vL, spo, kb16, two47, two48, hiA, loS, v120,
  S_vr.vV, S_vr.vW, S_vr.vA, S_vr.vD, S_vr.vC, S_vr.vK, S_vr.vDp, S_vr.spo, S_vr.two47, S_vr.two48,
  S_vr.hiA, S_vr.loS in *.

Lemma ek_exact : forall rho, holds rho (SPUle vK (SLit two47)) ->
  bv_unsigned (eval rho (kb16 vK)) = 16 * bv_unsigned (rw rho 17%positive) /\
  Zsigned (bv_unsigned (eval rho (kb16 vK))) = bv_unsigned (eval rho (kb16 vK)).
Proof.
  intros rho H3. unfold kb16, vK, S_vr.vK, two47, S_vr.two47 in *.
  pose proof (bv_urange (rw rho 17%positive)) as R2.
  cbn [holds] in H3. rewrite ?U_lit, ?eval_var in H3. unfold M64v in *.
  rewrite (Z.mod_small (2 ^ 47)) in H3 by lia.
  rewrite U_mul, U_lit, !eval_var. unfold M64v.
  rewrite (Z.mod_small 16) by lia. rewrite Z.mod_small by lia.
  split; [reflexivity|]. destruct (Zsigned_spec (16 * bv_unsigned (rw rho 17%positive))) as [[_ X]|[X _]]; [exact X|].
  exfalso. cbn in X. lia.
Qed.

Lemma data_empty : forall rho, holds rho (SPUle (kb16 vK) (SLit 0)) ->
  snd (obj_range rho (O_data vD (kb16 vK) vC)) <= fst (obj_range rho (O_data vD (kb16 vK) vC)).
Proof.
  intros rho H. cbn [holds] in H. rewrite U_lit in H. unfold M64v in H. rewrite Zmod_0_l in H.
  pose proof (bv_urange (eval rho (kb16 vK))) as R.
  assert (E : bv_unsigned (eval rho (kb16 vK)) = 0) by lia.
  unfold obj_range, obj_lo_of, obj_hi_of, O_data. cbn [ob_base ob_lo ob_hi fst snd].
  rewrite soff_lit_small by lia. unfold soff. rewrite bv_signed_U, E. cbn. lia.
Qed.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis ML : malloc_laws segsU C_U.
Hypothesis MC : malloc_contracts segsU C_U EC_U.

Let nI : sstate * list (sv * sv) -> jnode := nodeI segsU C_U NF Kc rho0 P0_vr FB.
Let JGv (tv : list (sv * sv)) : jpred := JG segsU C_U NF Kc rho0 P0_vr FB tv.
Let Q : assn := LQP segsU NF rho0 (Posts_vr Kc FB).

Lemma robjs_nil : forall Ai x rho, robjs_ok segsU C_U Ai x rho [].
Proof. intros Ai x rho o a Ho. destruct Ho. Qed.
Lemma robjs_cons : forall Ai x rho o R,
  (forall a, fst (obj_range rho o) <= a < snd (obj_range rho o) -> caddr segsU C_U Ai x a) ->
  robjs_ok segsU C_U Ai x rho R -> robjs_ok segsU C_U Ai x rho (o :: R).
Proof. intros Ai x rho o R Ho HR o' a [<-|Hin] Hr; [exact (Ho a Hr) | exact (HR o' a Hin Hr)]. Qed.

Lemma tnz_var : forall rho v sz, tnz rho (SVar v, sz) <-> bv_unsigned (rw rho v) <> 0.
Proof. intros. unfold tnz. cbn [fst eval]. tauto. Qed.

Lemma data_obj_ok : forall rho Ai tv,
  holds rho (SPUle vK (SLit two47)) ->
  tvin FB Ai rho tv -> tvz rho tv -> In (vD, kb16 vK) tv ->
  forall x, x <> Some (bv_unsigned (rw rho 15%positive)) ->
  forall a, fst (obj_range rho (O_data vD (kb16 vK) vC)) <= a < snd (obj_range rho (O_data vD (kb16 vK) vC)) ->
  caddr segsU C_U Ai x a.
Proof.
  intros rho Ai tv HK HN HZ Hin x Hx.
  destruct (ek_exact rho HK) as [E1 E2].
  eapply (rad.block_obj_caddr Ai x rho vD (kb16 vK) [] (darr vC) _ (bv_unsigned (eval rho (kb16 vK)))); [reflexivity|].
  intros Hpos. rewrite E2 in Hpos |- *.
  destruct (Z.eq_dec (bv_unsigned (rw rho 15%positive)) 0) as [Hd|Hd].
  - exfalso. pose proof (proj1 (Forall_forall _ _) HZ _ Hin (fun Hc => proj1 (tnz_var rho _ _) Hc Hd)) as X.
    unfold tvv in X. cbn [snd] in X. lia.
  - destruct (proj1 (Forall_forall _ _) HN _ Hin (proj2 (tnz_var rho _ _) Hd)) as (_ & X & _).
    unfold tvv in X. cbn [fst snd] in X. unfold vD, S_vr.vD in X |- *. rewrite eval_var in X |- *.
    split; [exact X|]. split; [exact Hx | lia].
Qed.

Lemma R_c_ok : forall rho Ai tv,
  Forall (holds rho) (ss_facts E_c) -> tvin FB Ai rho tv -> tvz rho tv -> In (vD, kb16 vK) tv ->
  T_ok rho (topL (ma_L Ai)) -> robjs_ok segsU C_U Ai None rho R_c.
Proof.
  intros rho Ai tv HF HN HZ Hin HT.
  have_fact HF (SPBranch BC_GE (SLit (-832)) vDp). have_fact HF (SPBranch BC_GE vDp (SLit (- 2 ^ 40))).
  have_fact HF (SPUle (SVar 30) (SAlu ALU_ADD (spo (-32)) vDp)). have_fact HF (SPUle (SVar 30) (SVar 10)).
  have_fact HF (SPUle (SVar 10) (SLit two47)). have_fact HF (SPUle (SVar 30) vV). have_fact HF (SPUle vV (SLit two47)).
  have_fact HF (SPUle (SVar 30) vA). have_fact HF (SPUle vA (SLit two47)). have_fact HF (SPUle vK (SLit two47)).
  have_fact HF (SPUle (SLit loS) (SVar 30)). clear HF.
  apply robjs_cons; [|apply robjs_cons; [|apply robjs_cons; [|apply robjs_cons; [|apply robjs_nil]]]].
  - apply rad.stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30.
    rewrite eval_var. clear HN HZ Hin. unf. zfacts; lia.
  - apply rad.stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30.
    rewrite eval_var. clear HN HZ Hin. unf. zfacts; lia.
  - apply rad.stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30.
    rewrite eval_var. clear HN HZ Hin. unf. zfacts; lia.
  - eapply (data_obj_ok rho Ai tv); try eassumption. discriminate.
Qed.

Lemma R_ra_ok : forall rho, agree_vals NF rho0 rho -> Forall (holds rho) (ss_facts E_ra) ->
  robjs_okF segsU C_U rho0 FB rho [] R_ra.
Proof.
  intros rho Hav HF.
  have_fact HF (SPUle (SVar 30) (spo (-32))). have_fact HF (SPUle (SVar 30) (SVar 10)).
  have_fact HF (SPUle (SVar 10) (SLit two47)). have_fact HF (SPUle (SVar 30) vV).
  have_fact HF (SPUle (SLit loS) (SVar 30)). clear HF.
  intros o a [<-|[<-|[]]] Hr; left;
    unfold obj_range, obj_lo_of, obj_hi_of in Hr; cbn [ob_base ob_lo ob_hi fst snd] in Hr;
    rewrite !soff_lit_small in Hr by lia; rewrite eval_var in Hr;
    unfold T0, V_TOP; rewrite (proj1 Hav 30%positive ltac:(reflexivity)); unf; zfacts; lia.
Qed.

Lemma ra_add_ok : forall rho tr md, JGv tv0 rho tr md -> Forall (holds rho) (ss_facts E_ra2) ->
  Forall (holds rho) ra_add.
Proof.
  intros rho tr md HJ HF.
  assert (HN : Forall (holds rho) (tv_facts (vD, kb16 vK))).
  { eapply (JG_tv_facts segsU C_U NF Kc rho0 P0_vr FB); [exact HJ | left; reflexivity |].
    apply tnz_of_fact. pick_facts HF [0%nat]. assumption. }
  have_fact HF (SPBranch BC_GE (SLit (-832)) vDp). have_fact HF (SPBranch BC_GE vDp (SLit (- 2 ^ 40))).
  have_fact HF (SPUle (SVar 30) (SAlu ALU_ADD (spo (-32)) vDp)). have_fact HF (SPUle (SVar 30) (SVar 10)).
  have_fact HF (SPUle (SVar 10) (SLit two47)). have_fact HF (SPUle (SLit loS) (SVar 30)).
  have_fact HF (SPUle vW v120). have_fact HF (SPBranch BC_LTU vK vW). have_fact HF (SPUle v120 (SLit two48)).
  have_fact HF (SPUle vC vK). have_fact HF (SPUle vK (SLit two47)). clear HF.
  constructor; [|constructor; [|constructor; [|constructor; [|exact HN]]]]; clear HN HJ; unf; zfacts; lia.
Qed.

Lemma kzero_ok : forall rho tr md, JGv tv_m rho tr md -> holds rho (SPBranch BC_EQ vD (SLit 0)) ->
  holds rho (SPUle vC vK) -> holds rho (SPUle vK (SLit two47)) ->
  Forall (holds rho) [SPUle (kb16 vK) (SLit 0); SPUle vC (SLit 0)].
Proof.
  intros rho tr md (Ai & Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0) H Hck HkT.
  apply holds_beq in H. rewrite U_lit in H. unfold vD, S_vr.vD in H. rewrite eval_var in H. unfold M64v in H. rewrite Zmod_0_l in H.
  pose proof (proj1 (Forall_forall _ _) HZ (vD, kb16 vK) ltac:(right; left; reflexivity)
                (fun Hc => proj1 (tnz_var rho _ _) Hc H)) as X.
  unfold tvv in X. cbn [snd] in X.
  assert (Hk0 : holds rho (SPUle (kb16 vK) (SLit 0))).
  { cbn [holds]. rewrite X, U_lit. unfold M64v. rewrite Zmod_0_l. lia. }
  constructor; [exact Hk0|constructor; [|constructor]].
  clear X HZ HN HD HK HP0 HM HP Hav Hk. unf. zfacts; lia.
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

Hypothesis CCALLOC : forall Ai rho1,
  TR (SPJ segsU (J_alloc_pre segsU C_U Ai Kc) (Pre_calloc EC_U) rho1) (LQP segsU NF rho1 (Posts_calloc segsU C_U EC_U Ai Kc)).
Hypothesis CRA : forall FBc rho1,
  TR (SPJ segsU (JG_pre segsU C_U Kc RAD.P0_rad FBc RAD.tv0) RAD.Pre_rad rho1)
     (LQP segsU NF rho1 (PostsC segsU C_U Kc (fun _ => RAD.P0_rad) RAD.PD_rad FBc)).
Hypothesis REENTER : forall T tv rT vT rho b,
  In (T, tv, (rT, vT)) cutsE -> 0 <= rT -> (rT + 1) * 2 ^ 64 <= b -> TR (SPJ segsU (JGv tv) T rho) (FAM b).
Hypothesis POST : forall P tv rho b,
  In (P, JLG segsU C_U Kc P0_vr FB tv) (Posts_vr Kc FB) -> TR (SPJ segsU (JGv tv) P rho) (FAM b).

Let CALLOC := calloc_callT segsU C_U EC_U NF Kc rho0 P0_vr FB ML TR TR_facts TR_ex TR_pre TR_callP.
Let CLIENT := client_callT segsU C_U NF Kc rho0 P0_vr FB ML (fun _ => RAD.P0_rad) RAD.Pre_rad RAD.tv0 RAD.PD_rad NF
  (@eq_refl positive (ss_next RAD.Pre_rad)) TR TR_facts TR_ex TR_pre TR_callP CRA.

Lemma bound_ge : forall r b rho v,
  (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v) <-> r + 1 <= b \/ (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v).
Proof. intros. pose proof (urange (eval rho v)). nia. Qed.
Ltac reenter T tv rT := apply (REENTER T tv rT z0); [cbn; tauto | lia | unfold emeas, ed_rank, ed_var; cbn [fst snd]; apply bound_ge; left; lia].

Lemma X_P_keep : forall rho b, TR (SPJ segsU (JGv tv0) P_keep rho) (FAM b).
Proof. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_fail : forall rho b, TR (SPJ segsU (JGv tv0) P_fail rho) (FAM b).
Proof. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_grown : forall rho b, TR (SPJ segsU (JGv tv_post) P_grown rho) (FAM b).
Proof. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_E_ra : forall rho, TR (SPJ segsU (JGv tv0) E_ra0 rho) (FAM (emeas (E_ra0, tv0, (90, z0)) rho)).
Proof.
  intros rho.
  eapply TR_pre.
  2: { change (JGv tv0) with (JGv ([] ++ tv0)).
       apply (CLIENT E_ra s_ra R_ra rho [] tv0 _).
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - intros Ai ms HF HP0 Hav _ _ _ _ _ _. split; [apply R_ra_ok; [exact Hav | exact HF] | exact I].
       - intros d rho' Hd _. destruct Hd as [<-|[<-|[]]]; cbn [fst snd app].
         + replace (T_afterN NF E_ra s_ra R_ra RAD.P_fail_d) with T_rf by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_ra NF RAD.P_fail_d (ss_next E_ra)) RAD.tv0) with tv0 by (vm_compute; reflexivity).
           reenter T_rf tv0 80.
         + replace (T_afterN NF E_ra s_ra R_ra RAD.P_ok_d) with T_rok0 by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_ra NF RAD.P_ok_d (ss_next E_ra)) RAD.tvP) with tv_rok by (vm_compute; reflexivity).
           eapply TR_pre; [ | reenter T_rok tv_rok 80 ].
           intros w Hw. unfold T_rok. apply SPJ_refacts_J; [exact Hw | reflexivity |].
           intros tr md _ HF. have_fact HF (SPUle (kb16 v120) (SLit hiA)). have_fact HF (SPUle v120 (SLit two48)).
           clear HF. constructor; [|constructor]. unf. zfacts; lia. }
  intros w Hw. unfold E_ra. apply SPJ_refacts_J; [ | reflexivity | exact (ra_add_ok rho) ].
  apply (SPJ_unbase segsU _ rho E_ra1 1 (-48) E_ra2 w ltac:(vm_compute; reflexivity)).
  apply (SPJ_xforms segsU _ [XSplit 1 (SLit (-48))] rho E_ra0 E_ra1 w ltac:(vm_compute; reflexivity)). exact Hw.
Qed.

Lemma co_add_okS : forall S rho' tr md, JGv tv_m rho' tr md ->
  holds rho' (SPNot (SPBranch BC_EQ (SVar vN) (SLit 0))) -> holds rho' (SPUle v120 (SLit two48)) ->
  Forall (holds rho') (ss_facts S) -> Forall (holds rho') co_add.
Proof.
  intros S rho' tr md HJ Hn Hb _. apply Forall_cons_iff.
  assert (HN : Forall (holds rho') (tv_facts (SVar vN, kb16 v120))).
  { eapply (JG_tv_facts segsU C_U NF Kc rho0 P0_vr FB); [exact HJ | left; reflexivity |].
    apply tnz_of_fact. exact Hn. }
  split; [|exact HN].
  unfold tv_facts in HN. cbn [fst snd] in HN. Forall_facts HN. clear HJ Hn. unf. zfacts; lia.
Qed.

Lemma co_add_ok : forall rho' tr md, JGv tv_m rho' tr md -> Forall (holds rho') (ss_facts T_co0) ->
  Forall (holds rho') co_add.
Proof.
  intros rho' tr md HJ HF. apply (co_add_okS T_co0 rho' tr md HJ); [ | | exact HF ].
  - have_fact HF (SPNot (SPBranch BC_EQ (SVar vN) (SLit 0))). assumption.
  - have_fact HF (SPUle v120 (SLit two48)). assumption.
Qed.

Lemma co_add_ok2 : forall rho' tr md, JGv tv_m rho' tr md -> Forall (holds rho') (ss_facts T_co20) ->
  Forall (holds rho') co_add.
Proof.
  intros rho' tr md HJ HF. apply (co_add_okS T_co20 rho' tr md HJ); [ | | exact HF ].
  - have_fact HF (SPNot (SPBranch BC_EQ (SVar vN) (SLit 0))). assumption.
  - have_fact HF (SPUle v120 (SLit two48)). assumption.
Qed.

Lemma tv_m_restate : forall rho' w,
  JG segsU C_U NF Kc rho0 P0_vr FB ((SVar vN, SMd M_MUL v120 (SLit 16)) :: tv0) rho' (w_tr w) (cfg_model (w_cfg w)) ->
  JGv tv_m rho' (w_tr w) (cfg_model (w_cfg w)).
Proof.
  intros rho' w HJ0. eapply JG_tv_requiv; [|exact HJ0].
  constructor; [|constructor; [|constructor]]; split; intros r; try reflexivity. apply mul_comm_eval.
Qed.

Lemma X_E_c : forall rho, TR (SPJ segsU (JGv tv0) E_c rho) (FAM (emeas (E_c, tv0, (90, z0)) rho)).
Proof.
  intros rho.
  apply (CALLOC E_c s_c R_c rho tv0 _ CCALLOC).
  - vm_compute. reflexivity.
  - exact call_c_ok.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HM HT. split.
    + exact (R_c_ok rho Ai tv0 HF HN HZ ltac:(left; reflexivity) HT).
    + change (wsub_get s_c 12) with v120. change (wsub_get s_c 13) with (SLit 16).
      have_fact HF (SPUle vW v120). have_fact HF (SPBranch BC_LTU vK vW). have_fact HF (SPUle v120 (SLit two48)).
      clear HF HN HZ HD HP HM HT HP0 Hav. unf. zfacts; lia.
  - intros rho'.
    replace (T_after E_c s_c R_c (L_calloc_null (ec_ret_calloc EC_U))) with T_cn by (vm_compute; reflexivity).
    reenter T_cn tv0 80.
  - intros rho'.
    replace (T_after E_c s_c R_c (L_calloc_null (ec_ret_calloc2 EC_U))) with T_cn2 by (vm_compute; reflexivity).
    reenter T_cn2 tv0 80.
  - intros rho'.
    replace (T_after E_c s_c R_c (L_calloc_ok (ec_ret_calloc EC_U))) with T_co0 by (vm_compute; reflexivity).
    change (pos_add_nat (ss_next E_c) 10) with vN.
    change (wsub_get s_c 12) with v120. change (wsub_get s_c 13) with (SLit 16).
    eapply TR_pre; [ | reenter T_co tv_m 80 ].
    intros w [Hsm HJ0]. pose proof (tv_m_restate rho' w HJ0) as HJ.
    unfold T_co. apply SPJ_refacts_J; [split; [exact Hsm | exact HJ] | reflexivity | exact (co_add_ok rho')].
  - intros rho'.
    replace (T_after E_c s_c R_c (L_calloc_ok (ec_ret_memset EC_U))) with T_co20 by (vm_compute; reflexivity).
    change (pos_add_nat (ss_next E_c) 10) with vN.
    change (wsub_get s_c 12) with v120. change (wsub_get s_c 13) with (SLit 16).
    eapply TR_pre; [ | reenter T_co2 tv_m 80 ].
    intros w [Hsm HJ0]. pose proof (tv_m_restate rho' w HJ0) as HJ.
    unfold T_co2. apply SPJ_refacts_J; [split; [exact Hsm | exact HJ] | reflexivity | exact (co_add_ok2 rho')].
Qed.

Lemma X_rf_ok : forall rho b, TR (SPJ segsU (JGv tv0) X_rf rho) (FAM b).
Proof.
  intros rho b.
  apply (TR_pre (fun w => exists r, SPJ segsU (JGv tv0) P_fail r w)); [ | apply TR_exw; intros r; apply X_P_fail ].
  intros w Hw. exists (rho_sub rho s_rf).
  apply (SPJ_entails_JG segsU C_U NF Kc rho0 P0_vr FB ML X_rf4 P_fail s_rf tv0 tv0 rho w);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
  apply (SPJ_xforms segsU _ sel_rf rho X_rf3 X_rf4 w ltac:(vm_compute; reflexivity)).
  apply (SPJ_unbase segsU _ rho X_rf2 0 (-32) X_rf3 w ltac:(vm_compute; reflexivity)).
  apply (SPJ_xforms segsU _ xs_r rho X_rf X_rf2 w ltac:(vm_compute; reflexivity)). exact Hw.
Qed.

Lemma X_rok_ok : forall rho b, TR (SPJ segsU (JGv tv_rok) X_rok rho) (FAM b).
Proof.
  intros rho b.
  apply (TR_pre (fun w => exists r, SPJ segsU (JGv tv_post) P_grown r w)); [ | apply TR_exw; intros r; apply X_P_grown ].
  intros w Hw. exists (rho_sub rho s_rok).
  apply (SPJ_entails_JG segsU C_U NF Kc rho0 P0_vr FB ML X_rok4 P_grown s_rok tv_rok tv_post rho w);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
  apply (SPJ_xforms segsU _ sel_rok rho X_rok3 X_rok4 w ltac:(vm_compute; reflexivity)).
  apply (SPJ_unbase segsU _ rho X_rok2 0 (-32) X_rok3 w ltac:(vm_compute; reflexivity)).
  apply (SPJ_xforms segsU _ xs_r rho X_rok X_rok2 w ltac:(vm_compute; reflexivity)). exact Hw.
Qed.

Ltac gc_tac X :=
  intros rho b;
  apply (TR_pre (fun w => exists r, SPJ segsU (JGv tv_post) P_grown r w)); [ | apply TR_exw; intros r; apply X_P_grown ];
  intros w Hw;
  assert (HwA : SPJ segsU (JGv tv_m) (gcA X) rho w)
    by (apply SPJ_refacts_J; [exact Hw | reflexivity |
        intros tr md HJ HF; have_fact HF (SPBranch BC_EQ vD (SLit 0)); have_fact HF (SPUle vC vK);
        have_fact HF (SPUle vK (SLit two47)); clear HF; apply (kzero_ok rho tr md HJ); assumption]);
  assert (HwB : SPJ segsU (JGv tv_m) (gcB X) rho w)
    by (eapply (SPJ_restate segsU _ rho (gcA X) (gcB X) w [(SMd M_MUL v120 (SLit 16), kb16 v120)] []);
        [vm_compute; reflexivity | vm_compute; reflexivity | | constructor | exact HwA];
        constructor; [|constructor]; cbn [fst snd]; apply mul_comm_eval);
  destruct (JG_drop_last_empty segsU C_U NF Kc rho0 P0_vr FB ML tv_m (gcB X) (firstn 5 (ss_objs (gcB X)))
              (O_data vD (kb16 vK) vC) rho w ltac:(vm_compute; reflexivity) eq_refl eq_refl) as [rho1 Hw3];
    [ intros HF; have_fact HF (SPUle (kb16 vK) (SLit 0)); clear HF; apply data_empty; assumption | exact HwB | ];
  exists (rho_sub rho1 (infer_sub 100 (gcC X) P_grown));
  apply (SPJ_entails_JG segsU C_U NF Kc rho0 P0_vr FB ML (gcC X) P_grown (infer_sub 100 (gcC X) P_grown) tv_f tv_post rho1 w);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ];
  destruct Hw3 as [Hsm3 HJ3]; split; [exact Hsm3 | exact (JG_drop_tv segsU C_U NF Kc rho0 P0_vr FB tv_m 1%nat _ _ _ HJ3)].

Lemma X_co_ok : forall rho b, TR (SPJ segsU (JGv tv_m) X_co rho) (FAM b).
Proof. gc_tac X_co. Qed.
Lemma X_co2_ok : forall rho b, TR (SPJ segsU (JGv tv_m) X_co2 rho) (FAM b).
Proof. gc_tac X_co2. Qed.

Lemma exits_okT : forall X tvX rvX rho, In (X, tvX, rvX) exitsE ->
  TR (SPJ segsU (JGv tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).
Proof.
  intros X tvX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]; injection H as <- <- <-.
  - apply X_E_ra.
  - apply X_E_c.
  - apply X_P_keep.
  - apply X_P_fail.
  - apply X_rf_ok.
  - apply X_rok_ok.
  - apply X_co_ok.
  - apply X_co2_ok.
Qed.
End SumT.

Theorem vr_darr_sum_S : triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc P0_vr FB tv0) Pre_vr rho0) Q.
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segsU C_U NF Kc rho0 P0_vr FB ML FUEL_vr cutpcs_vr 100 cutsE exitsE ok Q (proj1 HS)
                (ejcert_jcert segsU NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nI (map (@edrop) cutsE)) w \/ Q w)
                (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
                (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segsU ok A P Q' H)
                (call_soundP segsU ok)).
       - intros Ai rho1. apply (mc_calloc _ _ _ MC). exact HS.
       - intros FBc rho1. exact (rad.ra_darr_sum ok Kc FBc rho1 HS ML MC).
       - intros T tv rT vT rho b Hin _ _. exact (reenter_cutGE segsU C_U NF Kc rho0 P0_vr FB ok cutsE T tv (rT, vT) Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segsU C_U NF Kc P0_vr FB ok rho0 tv (Posts_vr Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.

Theorem vr_darr_sum_E : etriple segsU (SPJ segsU (JG_pre segsU C_U Kc P0_vr FB tv0) Pre_vr rho0) Q.
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segsU C_U NF Kc rho0 P0_vr FB ML FUEL_vr cutpcs_vr 100 cutsE exitsE Q ejcert_ok)
         with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeI segsU C_U NF Kc rho0 P0_vr FB) cutsE) b w \/ Q w)
                (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
                (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segsU A P Q' H)
                (call_completeP segsU)).
       - intros Ai rho1. apply (mcx_calloc _ _ _ MCX). exact Hvi.
       - intros FBc rho1. exact (rad.ra_darr_sum_ex Kc FBc rho1 Hvi ML MCX).
       - intros T tv rT vT rho b Hin H0 Hb. apply (ereenter_cutE segsU C_U NF Kc rho0 P0_vr FB cutsE T tv (rT, vT) Q b rho Hin).
         unfold emeas, ed_rank, ed_var. cbn [fst snd]. pose proof (urange (eval rho vT)). nia.
       - intros P tv rho b Hin. apply (eexit_postG segsU C_U NF Kc P0_vr FB rho0 tv (Posts_vr Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem vr_darr_sum : vr_darr_stmt_U.
Proof. intros ok Kc FB rho0 HS ML MC. apply vr_darr_sum_S; assumption. Qed.

Theorem vr_darr_sum_ex : vr_darr_ex_stmt_U.
Proof. intros Kc FB rho0 Hvi ML MCX. apply vr_darr_sum_E; assumption. Qed.

Theorem bli_darr_sum_U : S_bli.bli_darr_stmt_U.
Proof. exact (bli.bli_darr_ok_U vr_darr_sum). Qed.

Theorem bli_darr_sum_ex_U : S_bli.bli_darr_ex_stmt_U.
Proof. exact (bli.bli_darr_ex_ok_U vr_darr_sum_ex). Qed.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs hf_cuts.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10.S_pc.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6.S_pg.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module VRU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9.S_vr.
Module HN := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes.
Module PCU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10.S_pc.
Module PGU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6.S_pg.

Definition rawbase_U : list (nat * sv) :=
  [(9%nat, xb 528); (18%nat, xb 720); (19%nat, SLit 2); (21%nat, t_d co1); (22%nat, SLit 32); (23%nat, SLit 9);
   (24%nat, pA); (25%nat, am2); (26%nat, txt pP); (27%nat, magic_U)].

Definition rawregs_U : list (nat * sv) := rawbase_U ++ [(10%nat, SLit 1); (11%nat, SLit 3)].

Definition rawfacts_U : list sprop :=
  [SPUle xP0 pP; SPUle pP xE0; SPBranch BC_EQ pA (SLit 3); SPBranch BC_LTU (SLit 2) pA;
   SPUle pA (SLit (2 ^ 20))] ++ nzA_U.

Definition RAW_U : sstate := HS_U pc_raw_U rawregs_U [] pP coA [] rawfacts_U.

Definition raw_cps : list Z := [0x167f8; 0x18abc; 0x1dbf0; 0x193ac; 0x193f4; 0x19394; 0x195c8; 0x19854].

Definition raw_run (S : sstate) : list sstate :=
  match sym_run segsU FUEL_U raw_cps S true with Some ls => map lf_state ls | None => [] end.
Definition raw_at (S : sstate) (pc : Z) (k : nat) : sstate :=
  nth k (List.filter (fun l => Z.eqb (ss_pc l) pc) (raw_run S)) RAW_U.
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => RAW_U end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition s_vr (E : sstate) (t : sv * sv * sv) (e : Z) : wsub :=
  [(19%positive, SAlu ALU_ADD xD (SLit 32)); (15%positive, t_d t); (16%positive, t_c t); (17%positive, t_k t);
   (18%positive, SLit e)] ++ infer_sub 10 E VRU.Pre_vr.
Definition xg_of (E : sstate) (s : wsub) : sv * sv :=
  nth 0 (import_tv (import_sub s NF VRU.P_grown (ss_next E)) VRU.tv_post) tv_av.
Definition tvG_of (j : nat) (x : sv * sv) : list (sv * sv) := tvH_l1 j ++ x :: tvH_l2 j.

Definition E_mi_U : sstate :=
  HS_U VRU.vr_entry (rawbase_U ++ [(1%nat, SLit 0x195ec); (10%nat, xb 496); (11%nat, SAlu ALU_ADD (t_c mi1) pA);
    (12%nat, xAL)]) [] pP coA [] rawfacts_U.
Definition xs_mi : list xform := [XSplit 1 (SLit (-32))].
Definition E_mi1 : sstate := Eval vm_compute in optS (apply_xforms E_mi_U xs_mi).
Definition E_mi2 : sstate := Eval vm_compute in optS (unbase_obj_at E_mi1 1 (-32)).
Definition s_mi : wsub := Eval vm_compute in s_vr E_mi2 mi1 12.
Definition R_mi : list sobj := Eval vm_compute in optR (entails_fr E_mi2 VRU.Pre_vr s_mi).
Definition nz_mi : list (positive * Z * positive) := [(300%positive, 12, 302%positive)].
Definition RK1_0 : sstate := Eval vm_compute in T_after E_mi2 s_mi R_mi VRU.P_keep.
Definition RK1_U : sstate := Eval vm_compute in add_facts (TobjJVx.nz_facts nz_mi) RK1_0.
Definition RF1_U : sstate := Eval vm_compute in T_after E_mi2 s_mi R_mi VRU.P_fail.
Definition RG1_U : sstate := Eval vm_compute in T_after E_mi2 s_mi R_mi VRU.P_grown.
Definition xg1 : sv * sv := Eval vm_compute in xg_of E_mi2 s_mi.
Definition tvG1 : list (sv * sv) := Eval vm_compute in tvG_of 1 xg1.

Definition E_fv_U : sstate := Eval vm_compute in raw_at RK1_U VRU.vr_entry 0.
Definition s_fv : wsub := Eval vm_compute in s_vr E_fv_U fv1 4.
Definition R_fv : list sobj := Eval vm_compute in optR (entails_fr E_fv_U VRU.Pre_vr s_fv).
Definition nz_fv : list (positive * Z * positive) := [(303%positive, 4, 305%positive)].
Definition RK2_0 : sstate := Eval vm_compute in T_after E_fv_U s_fv R_fv VRU.P_keep.
Definition RK2_U : sstate := Eval vm_compute in add_facts (TobjJVx.nz_facts nz_fv) RK2_0.
Definition RF2_U : sstate := Eval vm_compute in T_after E_fv_U s_fv R_fv VRU.P_fail.
Definition RG2_U : sstate := Eval vm_compute in T_after E_fv_U s_fv R_fv VRU.P_grown.
Definition xg2 : sv * sv := Eval vm_compute in xg_of E_fv_U s_fv.
Definition tvG2 : list (sv * sv) := Eval vm_compute in tvG_of 2 xg2.

Definition E_mm_U : sstate := Eval vm_compute in raw_at RK2_U VRU.vr_entry 0.
Definition s_mm : wsub := Eval vm_compute in s_vr E_mm_U mm1 4.
Definition R_mm : list sobj := Eval vm_compute in optR (entails_fr E_mm_U VRU.Pre_vr s_mm).
Definition nz_mm : list (positive * Z * positive) := [(306%positive, 4, 308%positive)].
Definition RK3_0 : sstate := Eval vm_compute in T_after E_mm_U s_mm R_mm VRU.P_keep.
Definition RK3_U : sstate := Eval vm_compute in add_facts (TobjJVx.nz_facts nz_mm) RK3_0.
Definition RF3_U : sstate := Eval vm_compute in T_after E_mm_U s_mm R_mm VRU.P_fail.
Definition RG3_U : sstate := Eval vm_compute in T_after E_mm_U s_mm R_mm VRU.P_grown.
Definition xg3 : sv * sv := Eval vm_compute in xg_of E_mm_U s_mm.
Definition tvG3 : list (sv * sv) := Eval vm_compute in tvG_of 3 xg3.

Definition E_sg_U : sstate := Eval vm_compute in raw_at RK3_U VRU.vr_entry 0.
Definition s_sg : wsub := Eval vm_compute in s_vr E_sg_U sg1 4.
Definition R_sg : list sobj := Eval vm_compute in optR (entails_fr E_sg_U VRU.Pre_vr s_sg).
Definition nz_sg : list (positive * Z * positive) := [(309%positive, 4, 311%positive)].
Definition RK4_0 : sstate := Eval vm_compute in T_after E_sg_U s_sg R_sg VRU.P_keep.
Definition RK4_U : sstate := Eval vm_compute in add_facts (TobjJVx.nz_facts nz_sg) RK4_0.
Definition RF4_U : sstate := Eval vm_compute in T_after E_sg_U s_sg R_sg VRU.P_fail.
Definition RG4_U : sstate := Eval vm_compute in T_after E_sg_U s_sg R_sg VRU.P_grown.
Definition xg4 : sv * sv := Eval vm_compute in xg_of E_sg_U s_sg.
Definition tvG4 : list (sv * sv) := Eval vm_compute in tvG_of 4 xg4.

Definition X_F1a : sstate := Eval vm_compute in raw_at RF1_U (hf_ret HF_U) 0.
Definition X_F1b : sstate := Eval vm_compute in raw_at RF1_U (hf_ret HF_U) 1.
Definition X_F2a : sstate := Eval vm_compute in raw_at RF2_U (hf_ret HF_U) 0.
Definition X_F2b : sstate := Eval vm_compute in raw_at RF2_U (hf_ret HF_U) 1.
Definition X_F3a : sstate := Eval vm_compute in raw_at RF3_U (hf_ret HF_U) 0.
Definition X_F3b : sstate := Eval vm_compute in raw_at RF3_U (hf_ret HF_U) 1.
Definition X_F4a : sstate := Eval vm_compute in raw_at RF4_U (hf_ret HF_U) 0.
Definition X_F4b : sstate := Eval vm_compute in raw_at RF4_U (hf_ret HF_U) 1.
Definition X_K4 : sstate := Eval vm_compute in raw_at RK4_U (hf_ret HF_U) 0.
Definition X_G4 : sstate := Eval vm_compute in raw_at RG4_U (hf_ret HF_U) 0.

Definition raw_cuts : list edesc :=
  [(RAW_U, tvH, (81, HN.z0));
   (RK1_U, tvH, (79, HN.z0)); (RG1_U, tvG1, (79, HN.z0)); (RF1_U, tvH, (79, HN.z0));
   (RK2_U, tvH, (77, HN.z0)); (RG2_U, tvG2, (77, HN.z0)); (RF2_U, tvH, (77, HN.z0));
   (RK3_U, tvH, (75, HN.z0)); (RG3_U, tvG3, (75, HN.z0)); (RF3_U, tvH, (75, HN.z0));
   (RK4_U, tvH, (73, HN.z0)); (RG4_U, tvG4, (73, HN.z0)); (RF4_U, tvH, (73, HN.z0))].
Definition raw_exits : list edesc :=
  [(E_mi_U, tvH, (80, HN.z0)); (E_fv_U, tvH, (78, HN.z0)); (E_mm_U, tvH, (76, HN.z0)); (E_sg_U, tvH, (74, HN.z0));
   (X_F1a, tvH, (0, HN.z0)); (X_F1b, tvH, (0, HN.z0)); (X_F2a, tvH, (0, HN.z0)); (X_F2b, tvH, (0, HN.z0));
   (X_F3a, tvH, (0, HN.z0)); (X_F3b, tvH, (0, HN.z0)); (X_F4a, tvH, (0, HN.z0)); (X_F4b, tvH, (0, HN.z0));
   (X_K4, tvH, (0, HN.z0)); (X_G4, tvG4, (0, HN.z0))].

Fixpoint idx_of (f : sobj -> bool) (l : list sobj) : nat :=
  match l with [] => 0%nat | o :: l' => if f o then 0%nat else S (idx_of f l') end.
Definition stk_hi (o : sobj) : bool :=
  sv_eqb (ob_base o) (SAlu ALU_ADD (SVar 10) (SLit (-272))) && sv_eqb (ob_lo o) (SLit (-32)).
Definition stk_lo (o : sobj) : bool := sv_eqb (ob_base o) (SAlu ALU_ADD (SVar 10) (SLit (-304))).
Definition vb_off (o : sobj) : bool :=
  match ob_base o with
  | SAlu ALU_ADD (SVar v) (SLit _) => Pos.eqb v 12
  | _ => false
  end.
Definition xs_ret1 (X : sstate) : list xform :=
  let os := ss_objs X in
  let iD := idx_of stk_lo os in
  let iF := idx_of stk_hi os in
  [XSelect (iD :: iF :: List.filter (fun i => negb (Nat.eqb i iD || Nat.eqb i iF)) (seq 0 (length os)));
   XRebase 0; XRebase 1; XMerge 0].
Definition xs_ret2 (X : sstate) : list xform :=
  map XRebase (List.filter (fun i => vb_off (nth i (ss_objs X) (O_c (SLit 0)))) (seq 0 (length (ss_objs X)))).
Definition ret_norm (X : sstate) : option sstate :=
  match apply_xforms X (xs_ret1 X) with
  | Some Y => match apply_xforms Y (xs_ret2 Y) with Some Y2 => unbase_obj_at Y2 0 (-272) | None => None end
  | None => None
  end.
Definition ret_check (X : sstate) (tvX : list (sv * sv)) : bool :=
  match ret_norm X with
  | Some Y =>
      let s := infer_sub NP Y (HP_ret HF_U) in
      entails Y (HP_ret HF_U) s && wsub_id_below s NP && Pos.leb NP (ss_next Y) && tv_below (ss_next Y) tvX &&
      tv_sub_eqb s tvX tvH
  | None => false
  end.

Ltac argty f := let t := type of f in lazymatch t with forall _ : ?A, _ => exact A end.

Section Raw.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segsU C_U.

Let JGv (tv : list (sv * sv)) : jpred := JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv.

Lemma txt_extra_ok_raw : forall rho kept R o a,
  P0_hf FB rho0 -> agree_vals NP rho0 rho -> In o R -> is_txt o = true ->
  fst (obj_range rho o) <= a < snd (obj_range rho o) -> pclF segsU C_U rho0 (FBx FB rho kept) a.
Proof.
  intros rho kept R o a HP0 Hav Ho Ht Hr. unfold is_txt in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  unfold xB, xL in Hr. rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 100%positive ltac:(reflexivity)), <- (Hw 101%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  right; right.
  pose proof (bv_urange (rw rho0 101)) as R101.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [apply in_or_app; left; exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 101))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.

Section RawT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall J S rho (Q' : assn),
  (Forall (holds rho) (ss_facts S) -> TR (SPJ segsU J S rho) Q') -> TR (SPJ segsU J S rho) Q'.
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segsU (J x) S rho) Q') -> TR (SPJ segsU (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : forall (P P' Q' : assn), (forall w, P' w -> P w) -> TR P Q' -> TR P' Q'.
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn),
  (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : forall (X : Prop) (P Q' : assn), (X -> TR P Q') -> TR (fun w => X /\ P w) Q'.
Hypothesis TR_callP : ltac:(argty (client_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML (fun _ => VRU.P0_vr)
  VRU.Pre_vr VRU.tv0 VRU.PD_vr NF eq_refl TR TR_facts TR_ex TR_pre)).
Hypothesis TR_callJ : ltac:(argty (pure_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML TR TR_facts TR_pre)).
Hypothesis CVR : forall FBc rho1,
  TR (SPJ segsU (JG_pre segsU C_U Kc VRU.P0_vr FBc VRU.tv0) VRU.Pre_vr rho1)
     (LQP segsU NF rho1 (VRU.Posts_vr Kc FBc)).
Hypothesis CPC : forall tv rho rho1,
  TR (SP segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) PCU.Pre_pc_U rho1)
     (LQ segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) NF rho1 PCU.Posts_pc_U).
Hypothesis CTP : forall tv rho rho1,
  TR (SP segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) (PGU.Pre_pg_U []) rho1)
     (LQ segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) NF rho1 PGU.Posts_pg_U).
Hypothesis REENTER : forall T tv rv rho b, In (T, tv, rv) raw_cuts ->
  0 <= emeas (T, tv, rv) rho /\ emeas (T, tv, rv) rho < b ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv) T rho) (FAM b).
Hypothesis POST : forall P tv rho b, In (P, JLG segsU C_U Kc (P0_hf FB) FB tv) (Posts_hf_U Kc FB) ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv) P rho) (FAM b).

Let CLIENT := client_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML (fun _ => VRU.P0_vr)
  VRU.Pre_vr VRU.tv0 VRU.PD_vr NF eq_refl TR TR_facts TR_ex TR_pre TR_callP CVR.

Lemma X_ret_ok : forall X tvX rho b, ret_check X tvX = true -> TR (SPJ segsU (JGv tvX) X rho) (FAM b).
Proof.
  intros X tvX rho b H. unfold ret_check, ret_norm in H.
  destruct (apply_xforms X (xs_ret1 X)) as [Y|] eqn:E1; cbv beta iota in H; [|discriminate].
  destruct (apply_xforms Y (xs_ret2 Y)) as [Y2|] eqn:E2; cbv beta iota in H; [|discriminate].
  destruct (unbase_obj_at Y2 0 (-272)) as [Z3|] eqn:E3; cbv beta iota zeta in H; [|discriminate].
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply (TR_pre (SPJ segsU (JGv tvH) (HP_ret HF_U) (rho_sub rho (infer_sub NP Z3 (HP_ret HF_U))))).
  - intros w Hw.
    apply (SPJ_entails_JG segsU C_U NP Kc rho0 (P0_hf FB) FB ML Z3 (HP_ret HF_U) _ tvX tvH rho w H1 H2 H3 H4 H5).
    apply (SPJ_unbase segsU _ rho Y2 0 (-272) Z3 w E3).
    apply (SPJ_xforms segsU _ (xs_ret2 Y) rho Y Y2 w E2).
    exact (SPJ_xforms segsU _ (xs_ret1 X) rho X Y w E1 Hw).
  - apply POST. left. reflexivity.
Qed.

Ltac reenter T tv rT k :=
  apply (REENTER T tv (rT, HN.z0)); [apply (nth_error_In raw_cuts k); reflexivity |];
  rewrite TobjJVx.emeas_emeasZ; unfold TobjJVx.emeasZ;
  match goal with |- context [eval ?r HN.z0] => pose proof (urange (eval r HN.z0)) end; nia.

Ltac vr_pre d k e :=
  intros Ai ms HF HP0 Hav _ _ _ HZ _ HT; split;
  [ eapply robjs_checkF_sound with (extra := is_txt);
    [ exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT)
    | unfold tvz in *; apply Forall_forall; intros t Ht; apply (proj1 (Forall_forall _ _) HZ);
      apply in_or_app; left; exact Ht
    | vm_compute; reflexivity
    | intros o a Ho Hx Hr; eapply txt_extra_ok_raw; eauto ]
  | cbn beta; eapply (P0_vr_of_tvz _ d k e);
    [ reflexivity | reflexivity
    | unfold tvz in *; constructor; [|constructor]; apply (proj1 (Forall_forall _ _) HZ);
      apply in_or_app; right; left; reflexivity
    | eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto
    | lia ] ].

Lemma back_raw : forall j x tv S rho w, SPJ segsU (JGv (keptH j ++ [x])) S rho w ->
  tv = tvH_l1 j ++ x :: tvH_l2 j -> SPJ segsU (JGv tv) S rho w.
Proof.
  intros j x tv S rho w Hw ->.
  exact (TobjJVx.SPJ_JG_move_back segsU C_U NP Kc rho0 (P0_hf FB) FB (tvH_l1 j) (tvH_l2 j) x S rho w Hw).
Qed.

Lemma fwd_raw : forall j S rho w, tvH = tvH_l1 j ++ tvH_x j :: tvH_l2 j ->
  SPJ segsU (JGv tvH) S rho w -> SPJ segsU (JGv (keptH j ++ [tvH_x j])) S rho w.
Proof.
  intros j S rho w Heq Hw. rewrite Heq in Hw.
  exact (TobjJVx.SPJ_JG_move_last segsU C_U NP Kc rho0 (P0_hf FB) FB (tvH_l1 j) (tvH_l2 j) (tvH_x j) S rho w Hw).
Qed.

Ltac post_keep j K0 K nz rK k :=
  match goal with |- context [T_afterN ?n ?E ?s ?R VRU.P_keep] =>
    replace (T_afterN n E s R VRU.P_keep) with K0 by (vm_compute; reflexivity) end;
  match goal with |- context [import_tv ?a VRU.tv0] =>
    replace (import_tv a VRU.tv0) with [tvH_x j] by (vm_compute; reflexivity) end;
  match goal with |- TR (SPJ _ _ _ ?r) _ => apply (TR_pre (SPJ segsU (JGv tvH) K r)) end;
  [ | reenter K tvH rK k];
  let w := fresh "w" in let Hw := fresh "Hw" in let Hv := fresh "Hv" in intros w Hw;
  pose proof (back_raw j (tvH_x j) tvH _ _ _ Hw ltac:(vm_compute; reflexivity)) as Hv;
  replace K with (add_facts (TobjJVx.nz_facts nz) K0) by (vm_compute; reflexivity);
  apply SPJ_refacts_J; [exact Hv | vm_compute; reflexivity | ];
  let tr := fresh "tr" in let md := fresh "md" in let HJ := fresh "HJ" in let HFX := fresh "HFX" in
  intros tr md HJ HFX;
  eapply (TobjJVx.nz_facts_sound segsU C_U NP Kc rho0 (P0_hf FB) FB (ss_facts K0) tvH);
    [vm_compute; reflexivity | exact HFX | exact HJ].

Ltac post_fail j F rK k :=
  match goal with |- context [T_afterN ?n ?E ?s ?R VRU.P_fail] =>
    replace (T_afterN n E s R VRU.P_fail) with F by (vm_compute; reflexivity) end;
  match goal with |- context [import_tv ?a VRU.tv0] =>
    replace (import_tv a VRU.tv0) with [tvH_x j] by (vm_compute; reflexivity) end;
  match goal with |- TR (SPJ _ _ _ ?r) _ => apply (TR_pre (SPJ segsU (JGv tvH) F r)) end;
  [ | reenter F tvH rK k];
  let w := fresh "w" in let Hw := fresh "Hw" in intros w Hw;
  exact (back_raw j (tvH_x j) tvH _ _ _ Hw ltac:(vm_compute; reflexivity)).

Ltac post_grown j G xg tvG rK k :=
  match goal with |- context [T_afterN ?n ?E ?s ?R VRU.P_grown] =>
    replace (T_afterN n E s R VRU.P_grown) with G by (vm_compute; reflexivity) end;
  match goal with |- context [import_tv ?a VRU.tv_post] =>
    replace (import_tv a VRU.tv_post) with [xg] by (vm_compute; reflexivity) end;
  match goal with |- TR (SPJ _ _ _ ?r) _ => apply (TR_pre (SPJ segsU (JGv tvG) G r)) end;
  [ | reenter G tvG rK k];
  let w := fresh "w" in let Hw := fresh "Hw" in intros w Hw;
  exact (back_raw j xg tvG _ _ _ Hw ltac:(vm_compute; reflexivity)).

Ltac vr_call E2 s R j d k e r :=
  apply (CLIENT E2 s R r (keptH j) [tvH_x j] _);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vr_pre d k e | ].

Lemma X_E_mi : forall rho b, 80 * 2 ^ 64 <= b -> TR (SPJ segsU (JGv tvH) E_mi_U rho) (FAM b).
Proof.
  intros rho b Hb. eapply TR_pre.
  2: { vr_call E_mi2 s_mi R_mi 1%nat 300%positive 302%positive 12 rho.
       intros d rho' Hd _. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
       - post_keep 1%nat RK1_0 RK1_U nz_mi 79 1%nat.
       - post_fail 1%nat RF1_U 79 3%nat.
       - post_grown 1%nat RG1_U xg1 tvG1 79 2%nat. }
  intros w Hw.
  apply (SPJ_unbase segsU _ rho E_mi1 1 (-32) E_mi2 w ltac:(vm_compute; reflexivity)).
  apply (SPJ_xforms segsU _ xs_mi rho E_mi_U E_mi1 w ltac:(vm_compute; reflexivity)).
  apply (fwd_raw 1%nat); [vm_compute; reflexivity | exact Hw].
Qed.

Lemma X_E_fv : forall rho b, 78 * 2 ^ 64 <= b -> TR (SPJ segsU (JGv tvH) E_fv_U rho) (FAM b).
Proof.
  intros rho b Hb. eapply TR_pre.
  2: { vr_call E_fv_U s_fv R_fv 2%nat 303%positive 305%positive 4 rho.
       intros d rho' Hd _. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
       - post_keep 2%nat RK2_0 RK2_U nz_fv 77 4%nat.
       - post_fail 2%nat RF2_U 77 6%nat.
       - post_grown 2%nat RG2_U xg2 tvG2 77 5%nat. }
  intros w Hw. apply (fwd_raw 2%nat); [vm_compute; reflexivity | exact Hw].
Qed.

Lemma X_E_mm : forall rho b, 76 * 2 ^ 64 <= b -> TR (SPJ segsU (JGv tvH) E_mm_U rho) (FAM b).
Proof.
  intros rho b Hb. eapply TR_pre.
  2: { vr_call E_mm_U s_mm R_mm 3%nat 306%positive 308%positive 4 rho.
       intros d rho' Hd _. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
       - post_keep 3%nat RK3_0 RK3_U nz_mm 75 7%nat.
       - post_fail 3%nat RF3_U 75 9%nat.
       - post_grown 3%nat RG3_U xg3 tvG3 75 8%nat. }
  intros w Hw. apply (fwd_raw 3%nat); [vm_compute; reflexivity | exact Hw].
Qed.

Lemma X_E_sg : forall rho b, 74 * 2 ^ 64 <= b -> TR (SPJ segsU (JGv tvH) E_sg_U rho) (FAM b).
Proof.
  intros rho b Hb. eapply TR_pre.
  2: { vr_call E_sg_U s_sg R_sg 4%nat 309%positive 311%positive 4 rho.
       intros d rho' Hd _. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
       - post_keep 4%nat RK4_0 RK4_U nz_sg 73 10%nat.
       - post_fail 4%nat RF4_U 73 12%nat.
       - post_grown 4%nat RG4_U xg4 tvG4 73 11%nat. }
  intros w Hw. apply (fwd_raw 4%nat); [vm_compute; reflexivity | exact Hw].
Qed.

Lemma raw_exits_okT : forall X tvX rvX rho, In (X, tvX, rvX) raw_exits ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).
Proof using Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP TR_callJ CVR CPC CTP REENTER POST.
  intros X tvX rvX rho Hin. unfold raw_exits in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]; injection H as <- <- <-;
    unfold emeas, ed_rank, ed_var; cbn [fst snd]; pose proof (urange (eval rho HN.z0)).
  1: apply X_E_mi; lia.
  1: apply X_E_fv; lia.
  1: apply X_E_mm; lia.
  1: apply X_E_sg; lia.
  all: apply X_ret_ok; vm_compute; reflexivity.
Qed.
End RawT.
End Raw.

From Stdlib Require Import ZArith NArith List Bool PArith Lia Sorting.Permutation.
From stdpp Require Import bitvector base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require Import S_op.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require Import op_st.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import OptPushAddrU.

Lemma cm_okP (P : Z -> Prop) : P 1 -> P 3 -> forall cm, In cm op_cms -> P cm.
Proof. intros H1 H3 cm [<-|[<-|[]]]; assumption. Qed.

Ltac argty f := let t := type of f in lazymatch t with forall _ : ?A, _ => exact A end.
Ltac vmr := vm_compute; reflexivity.

Section Sum.
Variable cm : Z.
Hypothesis Hcm : In cm op_cms.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segsU C_U.

Ltac by_cm tac := pattern cm; match goal with |- ?F _ => refine (cm_okP F _ _ cm Hcm); cbv beta; tac end.

Let nI : forall n : sstate * list (sv * sv), jnode := nodeI segsU C_U NF Kc rho0 (OP1.P0_op FB) FB.
Let JGv (tv : list (sv * sv)) : jpred := JG segsU C_U NF Kc rho0 (OP1.P0_op FB) FB tv.
Let Q : assn := LQP segsU NF rho0 (Posts_op_U cm Kc FB).

Lemma ejcert_ok : ejcert segsU NF FUEL_op cutpcs_op_U 100 (cutsE_U cm) (exitsE_U cm) = true.
Proof using Hcm. by_cm ltac:(vm_cast_no_check (@eq_refl bool true)). Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall J S rho (Q' : assn),
  (Forall (holds rho) (ss_facts S) -> TR (SPJ segsU J S rho) Q') -> TR (SPJ segsU J S rho) Q'.
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segsU (J x) S rho) Q') -> TR (SPJ segsU (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : forall (P P' Q' : assn), (forall w, P' w -> P w) -> TR P Q' -> TR P' Q'.
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : forall (X : Prop) (P Q' : assn), (X -> TR P Q') -> TR (fun w => X /\ P w) Q'.
Hypothesis TR_callP : ltac:(argty (client_callT segsU C_U NF Kc rho0 (OP1.P0_op FB) FB ML (fun _ => VRU.P0_vr)
  VRU.Pre_vr VRU.tv0 VRU.PD_vr NF eq_refl TR TR_facts TR_ex TR_pre)).
Hypothesis CVR : forall FBc rho1,
  TR (SPJ segsU (JG_pre segsU C_U Kc VRU.P0_vr FBc VRU.tv0) VRU.Pre_vr rho1)
     (LQP segsU NF rho1 (PostsC segsU C_U Kc (fun _ => VRU.P0_vr) VRU.PD_vr FBc)).
Hypothesis REENTER : forall T tv rv rho b,
  In (T, tv, rv) (cutsE_U cm) -> 0 <= emeas (T, tv, rv) rho < b -> TR (SPJ segsU (JGv tv) T rho) (FAM b).
Hypothesis POST : forall P tv rho b,
  In (P, JLG segsU C_U Kc (OP1.P0_op FB) FB tv) (Posts_op_U cm Kc FB) -> TR (SPJ segsU (JGv tv) P rho) (FAM b).

Let CLIENT := client_callT segsU C_U NF Kc rho0 (OP1.P0_op FB) FB ML (fun _ => VRU.P0_vr)
  VRU.Pre_vr VRU.tv0 VRU.PD_vr NF eq_refl TR TR_facts TR_ex TR_pre TR_callP CVR.
Let CONT := contEJ_TR segsU C_U NF Kc rho0 (OP1.P0_op FB) FB ML TR TR_pre TR_exw TR_pureh.

Lemma X_P_ret : forall rho b, TR (SPJ segsU (JGv OP1.tvP) (P_ret_U cm) rho) (FAM b).
Proof. intros rho b. apply POST. cbn. tauto. Qed.

Ltac cont_to n xs A nzs vA rA rE vE i :=
  eapply (CONT xs 0 (-80) n _ A _ OP1.tvB OP1.tvB vA rA rE vE nzs);
  [ by_cm vmr | apply Permutation_refl | eassumption
  | let rho'' := fresh "rho''" in let Hm := fresh "Hm" in intros rho'' Hm;
    apply (REENTER A OP1.tvB (rA, vA) rho''); [apply (nth_error_In _ i); reflexivity | rewrite emeas_emeasZ; exact Hm] ].
Ltac site_client E rho AK AF AG iK iF iG vK rK vF rF rE vE :=
  change (JGv OP1.tvB) with (JGv ([] ++ OP1.tvB));
  apply (CLIENT (vr_view_U E) (vr_sub_U (vr_view_U E)) (R_of E) rho [] OP1.tvB _);
  [ by_cm vmr | by_cm vmr | by_cm vmr | by_cm vmr | by_cm vmr | by_cm vmr | by_cm vmr
  | intros Ai ms HF X1 X2 X3 X4 X5 HZ X6 HT; split;
    [ eapply robjs_checkF_sound with (extra := fun _ => false);
      [ exact HF | exact (TobjJVx.T_ok_T0_NF _ _ _ X2 HT) | constructor | by_cm vmr | intros o a _ X; discriminate X ]
    | cbn beta; eapply (OP1.P0_vr_of_tvz _ 280 282 4); [reflexivity | reflexivity | exact HZ | | lia];
      eapply (proj1 (Forall_forall _ _) HF); by_cm ltac:(vm_compute; tauto) ]
  | intros d rho' Hd Hag; destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app];
    [ cont_to (ss_next (vr_view_U E)) OP1.xs_keep AK nzB vK rK rE vE iK
    | cont_to (ss_next (vr_view_U E)) OP1.xs_keep AF (@nil (positive * Z * positive)) vF rF rE vE iF
    | cont_to (ss_next (vr_view_U E)) OP1.xs_grown AG (@nil (positive * Z * positive)) vK rK rE vE iG ] ].
Ltac site_view E rho :=
  let w := fresh "w" in let Hw := fresh "Hw" in intros w Hw;
  eapply (SPJ_unbase segsU _ rho (optS (apply_xforms E xs_vr)) 1 (-32) (vr_view_U E) w); [by_cm vmr |];
  eapply (SPJ_xforms segsU _ xs_vr rho E (optS (apply_xforms E xs_vr)) w); [by_cm vmr | exact Hw].

Lemma X_E_vrL : forall rho,
  TR (SPJ segsU (JGv OP1.tvB) (E_vrL_U cm) rho) (FAM (emeas (E_vrL_U cm, OP1.tvB, (50, OP1.VB OP1.pC (SLit 19))) rho)).
Proof.
  intros rho; eapply TR_pre;
    [ site_view (E_vrL_U cm) rho
    | site_client (E_vrL_U cm) rho (TA_L_U cm) (TF_L_U cm) (TA_L_U cm) 2%nat 3%nat 2%nat
        (OP1.VB OP1.pC (SLit 18)) 50 z0 45 50 (OP1.VB OP1.pC (SLit 19)) ].
Qed.
Lemma X_E_vr2v : forall rho,
  TR (SPJ segsU (JGv OP1.tvB) (E_vr2v_U cm) rho) (FAM (emeas (E_vr2v_U cm, OP1.tvB, (35, z0)) rho)).
Proof.
  intros rho; eapply TR_pre;
    [ site_view (E_vr2v_U cm) rho
    | site_client (E_vr2v_U cm) rho (TA_2_U cm OP1.vVALS) (TF_2_U cm) (TA_2_U cm OP1.vVALS) 5%nat 7%nat 5%nat
        z0 30 z0 30 35 z0 ].
Qed.
Lemma X_E_vr2d : forall rho,
  TR (SPJ segsU (JGv OP1.tvB) (E_vr2d_U cm) rho) (FAM (emeas (E_vr2d_U cm, OP1.tvB, (35, z0)) rho)).
Proof.
  intros rho; eapply TR_pre;
    [ site_view (E_vr2d_U cm) rho
    | site_client (E_vr2d_U cm) rho (TA_2_U cm OP1.vDEF) (TF_2_U cm) (TA_2_U cm OP1.vDEF) 6%nat 7%nat 6%nat
        z0 30 z0 30 35 z0 ].
Qed.

Lemma exits_okT : forall X tvX rvX rho, In (X, tvX, rvX) (exitsE_U cm) ->
  TR (SPJ segsU (JGv tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).
Proof.
  intros X tvX rvX rho Hin.
  change (TR (SPJ segsU (JGv (snd (fst (X, tvX, rvX)))) (fst (fst (X, tvX, rvX))) rho) (FAM (emeas (X, tvX, rvX) rho))).
  revert Hin. generalize (X, tvX, rvX) as e. intros e Hin. cbn [exitsE_U In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd].
  - apply X_E_vrL.
  - apply X_E_vr2v.
  - apply X_E_vr2d.
  - apply X_P_ret.
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis MC : malloc_contracts segsU C_U EC_U.
Hypothesis VRS : VRU.vr_stmt_U.

Theorem opt_push_sum :
  triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc (OP1.P0_op FB) FB OP1.tv0) (Pre_op_U cm) rho0)
    (LQP segsU NF rho0 (Posts_op_U cm Kc FB)).
Proof using Hcm HS MC ML VRS.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segsU C_U NF Kc rho0 (OP1.P0_op FB) FB ML FUEL_op cutpcs_op_U 100 (cutsE_U cm) (exitsE_U cm) ok Q (proj1 HS)
                (ejcert_jcert segsU NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nI (map (@edrop) (cutsE_U cm))) w \/ Q w)
                (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
                (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segsU ok A P Q' H)
                (triple_pureh segsU ok)
                (call_soundP segsU ok)).
       - intros FBc rho1. apply (VRS ok Kc FBc rho1 HS ML MC).
       - intros T tv rv rho b Hin _. exact (reenter_cutGE segsU C_U NF Kc rho0 (OP1.P0_op FB) FB ok (cutsE_U cm) T tv rv Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segsU C_U NF Kc (OP1.P0_op FB) FB ok rho0 tv (Posts_op_U cm Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.
Hypothesis VRX : VRU.vr_ex_stmt_U.

Theorem opt_push_sum_ex :
  etriple segsU (SPJ segsU (JG_pre segsU C_U Kc (OP1.P0_op FB) FB OP1.tv0) (Pre_op_U cm) rho0)
    (LQP segsU NF rho0 (Posts_op_U cm Kc FB)).
Proof using Hcm Hvi MCX ML VRX.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segsU C_U NF Kc rho0 (OP1.P0_op FB) FB ML FUEL_op cutpcs_op_U 100 (cutsE_U cm) (exitsE_U cm) Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeI segsU C_U NF Kc rho0 (OP1.P0_op FB) FB) (cutsE_U cm)) b w \/ Q w)
                (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
                (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segsU A P Q' H)
                (etriple_pureh segsU)
                (call_completeP segsU)).
       - intros FBc rho1. apply (VRX Kc FBc rho1 Hvi ML MCX).
       - intros T tv rv rho b Hin Hm. exact (ereenter_cutE segsU C_U NF Kc rho0 (OP1.P0_op FB) FB (cutsE_U cm) T tv rv Q b rho Hin Hm).
       - intros P tv rho b Hin. apply (eexit_postG segsU C_U NF Kc (OP1.P0_op FB) FB rho0 tv (Posts_op_U cm Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem opt_push_sum_U (VRS : VRU.vr_stmt_U) : forall cm, In cm op_cms -> opt_push_stmt_U cm.
Proof. intros cm Hcm ok Kc FB rho0 HS ML MC. exact (opt_push_sum cm Hcm Kc FB rho0 ML ok HS MC VRS). Qed.

Theorem opt_push_sum_ex_U (VRX : VRU.vr_ex_stmt_U) : forall cm, In cm op_cms -> opt_push_ex_stmt_U cm.
Proof. intros cm Hcm Kc FB rho0 Hvi ML MCX. exact (opt_push_sum_ex cm Hcm Kc FB rho0 ML Hvi MCX VRX). Qed.

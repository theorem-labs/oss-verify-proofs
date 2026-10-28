From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract Glue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform
  TobjJV TobjJVx TobjArena TobjJVA TobjJVAx TobjJVAy TobjJVAs ArenaDestroy.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require BuilderDispose.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo lo_defs lo_view lo_tail_addr lo4_common lo_bd_defs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require lo_entry.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4 Require Import S_bd.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module LoBdP.
Import LoBd.

Ltac find_idx F l := lazymatch l with | F :: _ => constr:(O) | _ :: ?t => let i := find_idx F t in constr:(S i) end.
Ltac have_fact HF F :=
  lazymatch type of HF with Forall _ ?l =>
    let l' := eval vm_compute in l in let F' := eval vm_compute in F in let i := find_idx F' l' in
    pose proof (Forall_pick _ _ i F HF eq_refl) end.
Ltac vb := vm_compute; reflexivity.

Lemma ejcert_ok : ejcertA segsU LD.NP FUEL cps LD.NP cutsE exitsE = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma view_bd : run_nsteps E_bd ns_bd = Some Ev_bd.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.

Lemma perm_bd : permb LoU.tvL (LoV.keptL slots_bd ++ LoV.passedL slots_bd) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma chk_bd : site_check C_U LD.NP Pre_bd (BuilderDispose.tvL 0) (AHead (SVar 199)) (PDAh PD_bd 199) 200 LoU.base_facts
  LD.is_txt Ev_bd s_bd (LoV.keptL slots_bd) (LoV.passedL slots_bd) LoU.amL 195 z0 conts_bd = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma Posts_bd_PD : forall Kc FB,
  Posts_bd Kc FB = PostsC segsU C_U Kc (fun _ : list (Z * Z) => BuilderDispose.P0_bd) PD_bd FB.
Proof. reflexivity. Qed.

Lemma l0d_eq : set_objs X_l0 (remove_nth iL0 (ss_objs X_l0)) = X_l0d.
Proof. vm_cast_no_check (@eq_refl sstate X_l0d). Qed.

Definition X_ok1 : sstate := Eval vm_compute in
  match run_nsteps (with_facts X_ok LoU.base_facts) ns_ok with Some X => X | None => X_ok end.
Lemma run_ok1 : run_nsteps (with_facts X_ok LoU.base_facts) ns_ok = Some X_ok1.
Proof. vm_cast_no_check (@eq_refl (option sstate) (Some X_ok1)). Qed.
Lemma ok1_eq : with_facts X_ok1 (ss_facts X_ok) = X_okN.
Proof. vm_cast_no_check (@eq_refl sstate X_okN). Qed.

Definition X_err1 : sstate := Eval vm_compute in
  match run_nsteps (with_facts X_err LoU.base_facts) ns_err with Some X => X | None => X_err end.
Lemma run_err1 : run_nsteps (with_facts X_err LoU.base_facts) ns_err = Some X_err1.
Proof. vm_cast_no_check (@eq_refl (option sstate) (Some X_err1)). Qed.
Lemma err1_eq : with_facts X_err1 (ss_facts X_err) = X_errN.
Proof. vm_cast_no_check (@eq_refl sstate X_errN). Qed.

Lemma P0f_eq : add_facts [SPNot (SPBranch BC_EQ LD.pH (SLit 0))] X_P0 = X_P0f.
Proof. vm_cast_no_check (@eq_refl sstate X_P0f). Qed.
Lemma P01_eq : ArenaDestroy.lenN_state X_P0f = X_P01.
Proof. vm_cast_no_check (@eq_refl sstate X_P01). Qed.
Lemma P02_eq : ArenaDestroy.pop_stateN X_P01 LD.pH (SVar (ss_next X_P0f)) = X_P02.
Proof. vm_cast_no_check (@eq_refl sstate X_P02). Qed.
Lemma Pf_eq : add_facts [SPNot (SPBranch BC_EQ pNX (SLit 0))] X_P = X_Pf.
Proof. vm_cast_no_check (@eq_refl sstate X_Pf). Qed.
Lemma P2_eq : ArenaDestroy.pop_stateN X_Pf pNX vG = X_P2.
Proof. vm_cast_no_check (@eq_refl sstate X_P2). Qed.

Lemma ameas_emeasZ : forall S tv am r v rho, ameas (S, (tv, am), (r, v)) rho = emeasZ r v rho.
Proof. intros. reflexivity. Qed.

Lemma meas_lt : forall (Y X : aedesc) rhoY rhoX, 0 <= ad_rank Y -> ad_rank Y + 1 <= ad_rank X ->
  0 <= ameas Y rhoY < ameas X rhoX.
Proof.
  intros Y X rhoY rhoX H0 H1. unfold ameas.
  pose proof (urange (eval rhoY (ad_var Y))). pose proof (urange (eval rhoX (ad_var X))). nia.
Qed.

Section Bd.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segsU C_U.

Let JGv (tv : list (sv * sv)) (am : amode) : jpred := JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB tv am.
Let Q : assn := LQP segsU LD.NP rho0 (Posts_loF_U Kc FB).

Lemma txt_pcl_U : forall rho o a, LD.P0_lo FB rho0 -> agree_vals LD.NP rho0 rho -> LD.is_txt o = true ->
  fst (obj_range rho o) <= a < snd (obj_range rho o) -> pclF segsU C_U rho0 FB a.
Proof.
  intros rho o a HP0 Hav Ht Hr.
  pose proof (txt_extra_ok_U FB rho0 rho [] [o] o a HP0 Hav (or_introl eq_refl) Ht Hr) as H.
  unfold FBx in H. cbn [List.filter map] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma l0_empty_U : forall rho tr md, JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LD.tv_fl LoU.amL rho tr md ->
  Forall (holds rho) (ss_facts X_l0) -> snd (obj_range rho O_ldat) <= fst (obj_range rho O_ldat).
Proof.
  intros rho tr md HJ HFX.
  destruct HJ as (Ai & (_ & _ & _ & _ & (_ & _ & HZ) & _) & _).
  have_fact HFX (SPBranch BC_EQ LD.xLD (SLit 0)). apply holds_beq in H.
  rewrite U_lit in H. unfold M64v in H. rewrite Z.mod_0_l in H by lia.
  pose proof (proj1 (Forall_forall _ _) HZ (LD.xLD, LD.kb 16 LD.xLK) (or_introl eq_refl)) as Z0.
  unfold tnz, tvv in Z0. cbn [fst snd] in Z0. specialize (Z0 (fun Hn => Hn H)).
  unfold obj_range, obj_lo_of, obj_hi_of, O_ldat, LD.O_lines. cbn [ob_base ob_lo ob_hi fst snd]. unfold soff. rewrite !bv_signed_U.
  rewrite Z0, U_lit. unfold M64v. rewrite Z.mod_0_l by lia. lia.
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
Hypothesis TR_pureh : forall (X : Prop) (P Q' : assn), (X -> TR P Q') -> TR (fun w => X /\ P w) Q'.
Hypothesis TR_callP : forall J Jp C Pre s R Posts (Q' : assn) rho,
  entails_fr C Pre s = Some R ->
  call_checkP C Pre s R (map fst Posts) = true ->
  (forall rho1, TR (SPJ segsU Jp Pre rho1) (LQP segsU (ss_next Pre) rho1 Posts)) ->
  (forall tr ms md, smatch segsU rho C (tr, mkCfg ms md) -> J rho tr md -> Jp (rho_sub (rho_absorb rho R ms) s) tr md) ->
  (forall L JL tr ms md rhoL tr' ms' md',
     In (L, JL) Posts -> smatch segsU rho C (tr, mkCfg ms md) -> J rho tr md ->
     agree_vals (ss_next Pre) (rho_sub (rho_absorb rho R ms) s) rhoL ->
     smatch segsU rhoL L (tr', mkCfg ms' md') -> JL (rho_sub (rho_absorb rho R ms) s) rhoL tr' md' ->
     import_okP rho ms R s Pre L rhoL /\
     (forall rho', call_linkP rho ms R s Pre C L rho' rhoL ->
        TR (SPJ segsU (J_ofP JL (rho_sub (rho_absorb rho R ms) s) rhoL) (import_post s (ss_next Pre) L (ss_next C) R) rho') Q')) ->
  TR (SPJ segsU J C rho) Q'.
Hypothesis CFREE : forall Ai rho1,
  TR (SPJ segsU (J_free_pre segsU C_U Ai Kc) (Pre_free EC_U) rho1)
     (LQP segsU NF rho1 [(L_free EC_U, JL_free segsU C_U Ai Kc)]).
Hypothesis C_bd : forall FBc rho1,
  TR (SPJ segsU (JGA_pre segsU C_U Kc ((fun _ : list (Z * Z) => BuilderDispose.P0_bd) FBc) FBc (BuilderDispose.tvL 0)
                   (AHead (SVar 199))) Pre_bd rho1)
     (LQP segsU 200 rho1 (PostsCA segsU C_U Kc (fun _ : list (Z * Z) => BuilderDispose.P0_bd) (PDAh PD_bd 199) FBc)).
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis POST : forall (P : sstate) (tv : list (sv * sv)) (am : amode) (rho : valuation) (b : Z),
  In (P, JLGA segsU C_U Kc (LD.P0_lo FB) FB tv am) (Posts_loF_U Kc FB) -> TR (SPJ segsU (JGv tv am) P rho) (FAM b).

Let FREE := free_callAT segsU C_U EC_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML TR TR_facts TR_ex TR_pre TR_callP.
Let ENTAS := entAs_TR segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML TR TR_pre TR_exw TR_pureh.

Lemma free_site : forall (E T : sstate) (s : wsub) (R : list sobj) (tv : list (sv * sv)) (am : amode) (t : sv * sv)
    (tvT : list (sv * sv)) (rvT : Z * sv) (b : Z) (rho : valuation),
  entails_fr E (Pre_free EC_U) s = Some R ->
  call_checkT C_U LD.NP E (Pre_free EC_U) s R [L_free EC_U] = true ->
  Pos.leb LD.NP (ss_next E) = true -> tv_below (ss_next E) tv = true -> am_below (ss_next E) am = true ->
  nth_error tv 0 = Some t ->
  sv_eqb (fst t) (wsub_get s 12) = true -> sv_eqb (snd t) (wsub_get s 13) = true ->
  robjs_check (ss_facts E) tv (Some 0%nat) (fun o => if hdr_obj am o then true else LD.is_txt o) R = true ->
  (Forall (holds rho) (ss_facts E) -> tvz rho tv -> tnz rho t) ->
  T_after E s R (L_free EC_U) = T -> remove_nth 0 tv = tvT -> In (T, (tvT, am), rvT) cutsE ->
  (forall rho', agree_vals (ss_next E) rho rho' -> Forall (holds rho) (ss_facts E) ->
     0 <= ameas (T, (tvT, am), rvT) rho' < b) ->
  TR (SPJ segsU (JGv tv am) E rho) (FAM b).
Proof.
  intros E T s R tv am t tvT rvT b rho He Hc Hl Htb Hab Hn H12 H13 Hr Hz HT Htv Hin Hm.
  apply sv_eqb_sound in H12. apply sv_eqb_sound in H13.
  apply TR_facts. intros HF0.
  apply (FREE E s R rho tv am 0%nat t _ CFREE He Hc Hl Htb Hab Hn).
  - intros Ai HF HP0 Hav HP HN HD HZ HXA (rhoM & md & HM) HT0.
    assert (Tnz : tnz rho t) by exact (Hz HF HZ).
    rewrite <- H12, <- H13. split; [exact Tnz|]. split; [reflexivity|].
    eapply (robjs_check_sound segsU C_U FB Ai rho (ss_facts E) tv (Some 0%nat) _ R _ rhoM md HM HT0 HF HN HD HZ Hr).
    + intros o a Ho Hx Hra. change (bv_unsigned (eval rho (fst t))) with (fst (tvv rho t)).
      revert Hx. cbv beta. destruct (hdr_obj am o) eqn:Hh; intros Hx.
      * exact (hdr_obj_caddr_free segsU C_U FB am Ai rho tv o a t rhoM md HM HN (nth_error_In _ _ Hn) Tnz HXA Hh Hra).
      * exact (pclF_caddr_free segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB (TobjJVA.NP_ok_intro LD.NP eq_refl)
                 Ai rho tv t a rhoM md HM Hav HT0 HP HN (nth_error_In _ _ Hn) Tnz (txt_pcl_U rho o a HP0 Hav Hx Hra)).
    + exists t. split; [exact Hn|]. split; [exact Tnz | reflexivity].
  - intros rho' Hag. rewrite HT, Htv. exact (REENTER T tvT am rvT rho' b Hin (Hm rho' Hag HF0)).
Qed.

Lemma X_E_bd : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_bd rho) (FAM (ameas (E_bd, (LoU.tvL, LoU.amL), (195, z0)) rho)).
Proof.
  intros rho. rewrite ameas_emeasZ.
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_bd rho w (permb_sound _ _ perm_bd)).
    exact (SPJ_nsteps segsU _ ns_bd rho E_bd Ev_bd w view_bd Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl)
            (fun _ : list (Z * Z) => BuilderDispose.P0_bd) Pre_bd (BuilderDispose.tvL 0) (AHead (SVar 199)) (PDAh PD_bd 199) 200
            eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP C_bd (txt_extra_ok_U FB rho0))
           Ev_bd s_bd (LoV.keptL slots_bd) (LoV.passedL slots_bd) LoU.amL 195 z0 conts_bd rho _ chk_bd).
  - intros ms R _ _ _ _. exact I.
  - intros c rho' Hc Hm. unfold conts_bd in Hc. destruct Hc as [<-|[]]. cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    exact (REENTER T_bd LD.tv_fl LoU.amL (190, z0) rho' _ ltac:(apply (nth_error_In cutsE 1); reflexivity) Hm).
Qed.

Lemma X_E_fl1 : forall rho,
  TR (SPJ segsU (JGv LD.tv_fl LoU.amL) E_fl1 rho) (FAM (ameas (E_fl1, (LD.tv_fl, LoU.amL), (185, z0)) rho)).
Proof.
  intros rho. apply (free_site E_fl1 T_fl1 s_fl1 R_fl1 LD.tv_fl LoU.amL (LD.xLD, LD.kb 16 LD.xLK) LoU.tv_ar (180, z0)).
  - vm_cast_no_check (@eq_refl (option (list sobj)) (Some R_fl1)).
  - vb.
  - vb.
  - vb.
  - vb.
  - reflexivity.
  - vb.
  - vb.
  - vb.
  - intros HF _. apply tnz_of_fact. have_fact HF (SPNot (SPBranch BC_EQ LD.xLD (SLit 0))). exact H.
  - vm_cast_no_check (@eq_refl sstate T_fl1).
  - reflexivity.
  - apply (nth_error_In cutsE 2). reflexivity.
  - intros rho' _ _. apply meas_lt; cbn; lia.
Qed.

Lemma X_E_fl2 : forall rho,
  TR (SPJ segsU (JGv LD.tv_fl LoU.amL) E_fl2 rho) (FAM (ameas (E_fl2, (LD.tv_fl, LoU.amL), (185, z0)) rho)).
Proof.
  intros rho. apply (free_site E_fl2 T_fl2 s_fl2 R_fl2 LD.tv_fl LoU.amL (LD.xLD, LD.kb 16 LD.xLK) LoU.tv_ar (180, z0)).
  - vm_cast_no_check (@eq_refl (option (list sobj)) (Some R_fl2)).
  - vb.
  - vb.
  - vb.
  - vb.
  - reflexivity.
  - vb.
  - vb.
  - vb.
  - intros HF _. apply tnz_of_fact. have_fact HF (SPNot (SPBranch BC_EQ LD.xLD (SLit 0))). exact H.
  - vm_cast_no_check (@eq_refl sstate T_fl2).
  - reflexivity.
  - apply (nth_error_In cutsE 3). reflexivity.
  - intros rho' _ _. apply meas_lt; cbn; lia.
Qed.

Lemma X_X_l0 : forall rho,
  TR (SPJ segsU (JGv LD.tv_fl LoU.amL) X_l0 rho) (FAM (ameas (X_l0, (LD.tv_fl, LoU.amL), (185, z0)) rho)).
Proof.
  intros rho. eapply TR_pre.
  2: { apply (landA_TR segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML TR TR_pre TR_exw [] X_l0d K_chk
                LoU.tv_ar LoU.tv_ar LoU.tv_ar LoU.amL LoU.amL rho); [vb | apply Permutation_refl |].
       intros rho'. apply (REENTER K_chk LoU.tv_ar LoU.amL (170, z0) rho');
         [apply (nth_error_In cutsE 4); reflexivity | apply meas_lt; cbn; lia]. }
  intros w Hw. change LoU.tv_ar with (remove_nth 0 LD.tv_fl).
  apply (SPJ_JGA_remove_nth segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB).
  rewrite <- l0d_eq.
  apply (SPJ_drop_empty segsU _ rho X_l0 iL0 O_ldat w);
    [vm_cast_no_check (@eq_refl (option sobj) (Some O_ldat)) | vb | | exact Hw].
  intros tr md HJ HFX. exact (l0_empty_U rho tr md HJ HFX).
Qed.

Lemma X_X_ok : forall rho,
  TR (SPJ segsU (JGv LoU.tv_ar LoU.amL) X_ok rho) (FAM (ameas (X_ok, (LoU.tv_ar, LoU.amL), (100, z0)) rho)).
Proof.
  intros rho. eapply TR_pre.
  2: { apply (landA_TR segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML TR TR_pre TR_exw [] X_okN P_ok_U
                LoU.tv_ar LoU.tv_ar LoU.tv_ar LoU.amL LoU.amL rho); [vb | apply Permutation_refl |].
       intros rho'. apply POST. left. reflexivity. }
  intros w Hw. rewrite <- ok1_eq.
  apply (SPJ_nsteps_keepfacts segsU _ ns_ok rho X_ok LoU.base_facts _ w run_ok1); [vb | vb | exact Hw].
Qed.

Lemma X_X_err : forall rho,
  TR (SPJ segsU (JGv [] am0) X_err rho) (FAM (ameas (X_err, ([], am0), (10, z0)) rho)).
Proof.
  intros rho. eapply TR_pre.
  2: { apply (landA_TR segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML TR TR_pre TR_exw [] X_errN P_err_U
                [] [] [] ANone ANone rho); [vb | apply Permutation_refl |].
       intros rho'. apply POST. right. left. reflexivity. }
  intros w Hw. rewrite <- err1_eq.
  apply (SPJ_nsteps_keepfacts segsU _ ns_err rho X_err LoU.base_facts _ w run_err1); [vb | vb |].
  apply (SPJ_JGA_to_none segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB [] am0). exact Hw.
Qed.

Lemma X_X_P0 : forall rho,
  TR (SPJ segsU (JGv LoU.tv_ar LoU.amL) X_P0 rho) (FAM (ameas (X_P0, (LoU.tv_ar, LoU.amL), (160, z0)) rho)).
Proof.
  intros rho.
  apply (TR_pre (SPJ segsU (JGv LoU.tv_ar (AHead LD.pH)) X_P0f rho)).
  { intros w Hw. rewrite <- P0f_eq. apply SPJ_refacts_J; [exact Hw | vb |]. intros tr md _ HF.
    have_fact HF (SPBranch BC_NE LD.pH (SLit 0)). clear - H. constructor; [|constructor]. unfold LD.pH in *. zfacts; lia. }
  apply (TR_pre (fun w => exists rho2, agree_below (ss_next X_P0f) rho rho2 /\
                   SPJ segsU (JGv (ArenaDestroy.pop_tv LD.pH (ss_next X_P01) LoU.tv_ar)
                                  (AHeadN (SVar (ss_next X_P01)) (SVar (ss_next X_P01 + 3)%positive))) X_P02 rho2 w)).
  { intros w Hw.
    destruct (JGA_lenN segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML LoU.tv_ar LD.pH X_P0f rho w
                ltac:(vb) ltac:(vb) ltac:(vb) ltac:(vb) Hw) as (rho1 & Hag1 & Hw1).
    rewrite P01_eq in Hw1.
    destruct (JGA_popN segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) LoU.tv_ar LD.pH
                (SVar (ss_next X_P0f)) X_P01 LD.is_txt rho1 w
                ltac:(vb) ltac:(vb) ltac:(vb) ltac:(vb) ltac:(vb) ltac:(vb)
                ltac:(intros o a _ Hx HP0 Hav _ Hr; exact (txt_pcl_U rho1 o a HP0 Hav Hx Hr)) ltac:(vb) Hw1)
      as (rho2 & Hag2 & Hw2 & _).
    rewrite P02_eq in Hw2.
    exists rho2. split; [|exact Hw2].
    eapply agree_below_trans; [exact Hag1|]. eapply agree_below_le; [|exact Hag2]. apply Pos.leb_le. vb. }
  apply TR_exw; intros rho2. apply TR_pureh; intros Hag.
  apply (ENTAS s_P0 (ss_next X_P0f) X_P02 C_L _ tv_L tv_L _ am_L (VGp 2) 60 160 z0 rho rho2).
  - vb.
  - apply Permutation_refl.
  - apply agree_below_vals. exact Hag.
  - intros rho' Hm. apply (REENTER C_L tv_L am_L (60, VGp 2) rho');
      [apply (nth_error_In cutsE 5); reflexivity | rewrite ameas_emeasZ; exact Hm].
Qed.

Lemma X_X_P : forall rho,
  TR (SPJ segsU (JGv LoU.tv_ar am_L) X_P rho) (FAM (ameas (X_P, (LoU.tv_ar, am_L), (60, VGm 1)) rho)).
Proof.
  intros rho.
  apply (TR_pre (fun w => exists rho1, agree_below (ss_next X_Pf) rho rho1 /\
                   SPJ segsU (JGv (ArenaDestroy.pop_tv pNX (ss_next X_Pf) LoU.tv_ar)
                                  (AHeadN (SVar (ss_next X_Pf)) (SVar (ss_next X_Pf + 3)%positive))) X_P2 rho1 w)).
  { intros w Hw.
    assert (Hwf : SPJ segsU (JGv LoU.tv_ar am_L) X_Pf rho w).
    { rewrite <- Pf_eq. apply SPJ_refacts_J; [exact Hw | vb |]. intros tr md _ HF.
      have_fact HF (SPNot (SPBranch BC_EQ pNX (SLit 0))). constructor; [exact H | constructor]. }
    destruct (JGA_popN segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) LoU.tv_ar pNX vG X_Pf
                LD.is_txt rho w
                ltac:(vb) ltac:(vb) ltac:(vb) ltac:(vb) ltac:(vb) ltac:(vb)
                ltac:(intros o a _ Hx HP0 Hav _ Hr; exact (txt_pcl_U rho o a HP0 Hav Hx Hr)) ltac:(vb) Hwf)
      as (rho1 & Hag1 & Hw1 & _).
    rewrite P2_eq in Hw1.
    exists rho1. split; [exact Hag1 | exact Hw1]. }
  apply TR_exw; intros rho1. apply TR_pureh; intros Hag.
  apply (ENTAS s_P (ss_next X_Pf) X_P2 C_L _ tv_L tv_L _ am_L (VGp 2) 60 60 (VGm 1) rho rho1).
  - vb.
  - apply Permutation_refl.
  - apply agree_below_vals. exact Hag.
  - intros rho' Hm. apply (REENTER C_L tv_L am_L (60, VGp 2) rho');
      [apply (nth_error_In cutsE 5); reflexivity | rewrite ameas_emeasZ; exact Hm].
Qed.

Lemma X_E_fd : forall rho,
  TR (SPJ segsU (JGv tv_L am_L) E_fd rho) (FAM (ameas (E_fd, (tv_L, am_L), (60, VGp 1)) rho)).
Proof.
  intros rho. apply (free_site E_fd T_fd s_fd R_fd tv_L am_L (pB, ArenaDestroy.blk_size pNn) LoU.tv_ar (60, VGp 0)).
  - vm_cast_no_check (@eq_refl (option (list sobj)) (Some R_fd)).
  - vb.
  - vb.
  - vb.
  - vb.
  - reflexivity.
  - vb.
  - vb.
  - vb.
  - intros HF _. apply tnz_of_fact. have_fact HF (SPUle (SLit 4096) pB). clear - H.
    intros Hz%holds_beq. unfold pB in *. zfacts; lia.
  - vm_cast_no_check (@eq_refl sstate T_fd).
  - reflexivity.
  - apply (nth_error_In cutsE 6). reflexivity.
  - intros rho' Hag HF0. have_fact HF0 (SPUle vG (SLit ArenaDestroy.two52)). clear - H Hag.
    unfold ameas, ad_rank, ad_var. cbn [fst snd]. unfold VGp, vG, ArenaDestroy.two52 in *.
    rewrite <- (eval_agree_vals (ss_next E_fd) rho rho' (SAlu ALU_ADD (SVar 504) (SLit 0)) Hag eq_refl).
    zfacts; lia.
Qed.

Lemma E_FA_free : forall rhoX rho (X : aedesc), 21 <= ad_rank X ->
  TR (SPJ segsU (JGv LoU.tv_ar am0) E_FA rho) (FAM (ameas X rhoX)).
Proof.
  intros rhoX rho X HX.
  apply (free_site E_FA T_fa s_fa R_fa LoU.tv_ar am0 (LD.xAR, SLit 64) [] (20, z0)).
  - vm_cast_no_check (@eq_refl (option (list sobj)) (Some R_fa)).
  - vb.
  - vb.
  - vb.
  - vb.
  - reflexivity.
  - vb.
  - vb.
  - vb.
  - intros _ HZ. unfold tnz. intros Hz.
    assert (Z0 : snd (tvv rho (LD.xAR, SLit 64)) = 0).
    { apply (proj1 (Forall_forall _ _) HZ (LD.xAR, SLit 64)); [left; reflexivity|]. intros Hn. apply Hn. exact Hz. }
    unfold tvv in Z0. cbn [fst snd] in Z0. rewrite U_lit in Z0. unfold M64v in Z0. vm_compute in Z0. discriminate Z0.
  - vm_cast_no_check (@eq_refl sstate T_fa).
  - reflexivity.
  - apply (nth_error_In cutsE 7). reflexivity.
  - intros rho' _ _. apply meas_lt; cbn; lia.
Qed.

Lemma X_X_fa0 : forall rho,
  TR (SPJ segsU (JGv LoU.tv_ar LoU.amL) X_fa0 rho) (FAM (ameas (X_fa0, (LoU.tv_ar, LoU.amL), (155, z0)) rho)).
Proof.
  intros rho. apply (TR_pre (SPJ segsU (JGv LoU.tv_ar am0) E_FA (rho_sub rho s_fa0))); [|apply (E_FA_free rho); cbn; lia].
  intros w Hw. apply (SPJ_entails_JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML X_fa0 E_FA s_fa0 LoU.tv_ar LoU.tv_ar am0 am0 rho w);
    [vb | vb | vb | vb | vb | vb | vb |].
  eapply (SPJ_head0 segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB). exact Hw.
Qed.

Lemma X_X_fa1 : forall rho,
  TR (SPJ segsU (JGv LoU.tv_ar am_L) X_fa1 rho) (FAM (ameas (X_fa1, (LoU.tv_ar, am_L), (30, z0)) rho)).
Proof.
  intros rho. apply (TR_pre (SPJ segsU (JGv LoU.tv_ar am0) E_FA (rho_sub rho s_fa1))); [|apply (E_FA_free rho); cbn; lia].
  intros w Hw. apply (SPJ_entails_JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML X_fa1 E_FA s_fa1 LoU.tv_ar LoU.tv_ar am0 am0 rho w);
    [vb | vb | vb | vb | vb | vb | vb |].
  eapply (SPJ_head0 segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB). exact Hw.
Qed.

Lemma exits_okT : forall X tvX amX rvX rho,
  In (X, (tvX, amX), rvX) exitsE ->
  TR (SPJ segsU (JGv tvX amX) X rho) (FAM (ameas (X, (tvX, amX), rvX) rho)).
Proof.
  intros X tvX amX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]; injection H as <- <- <- <-.
  - apply X_E_bd.
  - apply X_E_fl1.
  - apply X_E_fl2.
  - apply X_X_l0.
  - apply X_X_ok.
  - apply X_X_P0.
  - apply X_X_fa1.
  - apply X_X_fa0.
  - apply X_E_fd.
  - apply X_X_P.
  - apply X_X_err.
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis MC : malloc_contracts segsU C_U EC_U.
Hypothesis BD : builder_dispose_sum_stmt_U.

Theorem lo_bd_triple : forall rho, triple segsU ok (SPJ segsU (JGv LoU.tvL LoU.amL) LoU.K_bd rho) Q.
Proof.
  intros rho.
  apply (cfg_sound_JGAE segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML FUEL cps LD.NP cutsE exitsE ok Q (proj1 HS)
           (ejcertA_jcertA segsU LD.NP _ _ _ _ _ ejcert_ok)) with (rvT := (200, z0)); [|left; reflexivity].
  apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map (nodeA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB) (map (@adrop) cutsE)) w \/ Q w)
           (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
           (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
           (fun A P Q' H => @triple_ex segsU ok A P Q' H)
           (triple_pureh segsU ok)
           (call_soundP segsU ok)).
  - intros Ai rho1. apply (mc_free _ _ _ MC). exact HS.
  - intros FBc rho1.
    apply (JGA_frame_sum segsU C_U Kc (fun _ : list (Z * Z) => BuilderDispose.P0_bd) Pre_bd (BuilderDispose.tvL 0) PD_bd 200 199 ML);
      [reflexivity | intros F F' r _ H; exact H |].
    intros FBc' rho1'. rewrite <- (Posts_bd_PD Kc FBc'). exact (BD ok Kc FBc' rho1' ML HS MC).
  - intros T tv am rv rho' b Hin _. exact (reenter_cutGAE segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ok cutsE T tv am rv Q rho' Hin).
  - intros P tv am rho' b Hin. apply (exit_postGA segsU C_U LD.NP Kc (LD.P0_lo FB) FB ok rho0 tv am (Posts_loF_U Kc FB) P). exact Hin.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.
Hypothesis BDX : builder_dispose_sum_ex_stmt_U.

Theorem lo_bd_etriple : forall rho, etriple segsU (SPJ segsU (JGv LoU.tvL LoU.amL) LoU.K_bd rho) Q.
Proof.
  intros rho.
  apply (cfg_complete_JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML FUEL cps LD.NP cutsE exitsE Q ejcert_ok)
    with (rvT := (200, z0)); [|left; reflexivity].
  apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB) cutsE) b w \/ Q w)
           (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
           (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
           (fun A P Q' H => @etriple_ex segsU A P Q' H)
           (etriple_pureh segsU)
           (call_completeP segsU)).
  - intros Ai rho1. apply (mcx_free _ _ _ MCX). exact Hvi.
  - intros FBc rho1.
    apply (JGA_frame_sum_ex segsU C_U Kc (fun _ : list (Z * Z) => BuilderDispose.P0_bd) Pre_bd (BuilderDispose.tvL 0) PD_bd 200 199 ML);
      [reflexivity | intros F F' r _ H; exact H |].
    intros FBc' rho1'. rewrite <- (Posts_bd_PD Kc FBc'). exact (BDX Kc FBc' rho1' ML Hvi MCX).
  - intros T tv am rv rho' b Hin Hm. exact (ereenter_cutAE segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB cutsE T tv am rv Q b rho' Hin Hm).
  - intros P tv am rho' b Hin. apply (eexit_postGA segsU C_U LD.NP Kc (LD.P0_lo FB) FB rho0 tv am (Posts_loF_U Kc FB) P). exact Hin.
Qed.
End Existence.
End Bd.
End LoBdP.

Theorem lo_bd_sum_U : S_bd.builder_dispose_sum_stmt_U -> lo_entry.K_stmt LoU.K_bd.
Proof. intros BD ok Kc FB rho0 HS ML MC rho. exact (LoBdP.lo_bd_triple Kc FB rho0 ML ok HS MC BD rho). Qed.

Theorem lo_bd_sum_ex_U : S_bd.builder_dispose_sum_ex_stmt_U -> lo_entry.K_ex_stmt LoU.K_bd.
Proof. intros BDX Kc FB rho0 Hvi ML MCX rho. exact (LoBdP.lo_bd_etriple Kc FB rho0 ML Hvi MCX BDX rho). Qed.

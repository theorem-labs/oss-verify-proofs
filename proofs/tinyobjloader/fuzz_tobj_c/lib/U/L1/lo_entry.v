From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract Glue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require ClientLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import
  SumConv CfgGlue CursorGlue ObjXform ObjUnbase TobjJV TobjArena TobjJVA TobjJVAx TobjJVAy TobjJVAz DrvGlue2.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo S_u14e64 lo_defs lo_view lo_entry_defs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require u14e64.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4 Require Import ZeroKeep.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_bli.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require vrd.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_load__G1.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module LG := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue.

Definition K_stmt (K : sstate) : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc -> malloc_laws segsU C_U -> malloc_contracts segsU C_U EC_U ->
    forall rho, triple segsU ok (SPJ segsU (JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL LoU.amL) K rho)
      (LQP segsU LD.NP rho0 (Posts_loF_U Kc FB)).

Definition K_ex_stmt (K : sstate) : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    vm_insensitive Kc -> malloc_laws segsU C_U -> malloc_contracts_ex segsU C_U EC_U ->
    forall rho, etriple segsU (SPJ segsU (JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL LoU.amL) K rho)
      (LQP segsU LD.NP rho0 (Posts_loF_U Kc FB)).

Definition z0 : sv := SLit 0.
Definition cutsE : list aedesc :=
  [((Pre_lo_U, ([], ANone)), (100, z0)); ((T_mnull, ([], ANone)), (90, z0)); ((T_mok, (tv_m, ANone)), (90, z0));
   ((T_bi, (tv_m, ANone)), (80, z0)); ((K_A, (LoU.tvL, LoU.amL)), (60, z0))].
Definition exitsE : list aedesc :=
  [((E_m, ([], ANone)), (95, z0)); ((P_err_U, ([], ANone)), (0, z0)); ((X_bi_raw, (tv_m, ANone)), (85, z0));
   ((E_bli0, (tv_m, ANone)), (75, z0)); ((LoU.K_loop, (LoU.tvL, LoU.amL)), (0, z0));
   ((LoU.K_tail, (LoU.tvL, LoU.amL)), (0, z0)); ((LoU.K_bd, (LoU.tvL, LoU.amL)), (0, z0))].

Lemma ejcert_ok : ejcertA segsU LD.NP 8000 cps_e LD.NP cutsE exitsE = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma bi_prep_eq : bi_prep X_bi_raw = Some E_bi.
Proof. vm_cast_no_check (@eq_refl (option sstate) (Some E_bi)). Qed.

Lemma chk_bl : site_check C_U LD.NP S_bli.Pre_bli0 S_bli.tv0 ANone (PDAnone S_bli.PD_bli_darr) NF LoU.base_facts LD.is_txt
  E_bl s_bl tv_m [LD.nullL] ANone 75 z0 conts_bl = true.
Proof. vm_compute. reflexivity. Qed.

Lemma land_ok : landAs_check LD.NP [] sA T_L2 M_A (tvT ++ nulls) tvA (AHead (SLit 0)) LoU.amL = true.
Proof. vm_compute. reflexivity. Qed.

Lemma perm_ok : permb tvA LoU.tvL = true.
Proof. vm_compute. reflexivity. Qed.

Lemma SPJ_zk_all : forall J rho l S S' w, zk_all S l = Some S' -> SPJ segsU J S rho w -> SPJ segsU J S' rho w.
Proof.
  intros J rho l. induction l as [|i l IH]; intros S S' w H Hw; cbn [zk_all] in H.
  - injection H as <-. exact Hw.
  - destruct (zero_keep_at S i) as [S1|] eqn:E; [|discriminate].
    exact (IH S1 S' w H (SPJ_zero_keep segsU J rho S i S1 w E Hw)).
Qed.

Lemma SPJ_bi_prep : forall J rho S S' w, bi_prep S = Some S' -> SPJ segsU J S rho w -> SPJ segsU J S' rho w.
Proof.
  intros J rho S S' w. unfold bi_prep. destruct (run_nsteps S bi_ns) as [S1|] eqn:E; [|discriminate].
  intros H Hw. exact (SPJ_zk_all J rho zk_idx S1 S' w H (SPJ_nsteps segsU J bi_ns rho S S1 w E Hw)).
Qed.

Lemma SPJ_forget_all : forall J rho l S w, SPJ segsU J S rho w -> SPJ segsU J (fold_left obj_forget l S) rho w.
Proof.
  intros J rho l. induction l as [|i l IH]; intros S w Hw; cbn [fold_left]; [exact Hw|].
  apply IH. exact (SPJ_obj_forget segsU J rho S i w Hw).
Qed.

Lemma xor_lit_eq : forall rho a, eval rho (SAlu ALU_XOR a (SLit 18446744073709551615)) = eval rho (SAlu ALU_XOR a (SLit (-1))).
Proof.
  intros rho a. cbn [eval].
  replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)); [reflexivity|].
  apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
Qed.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis ML : malloc_laws segsU C_U.

Let nA : sstate * (list (sv * sv) * amode) -> jnode := nodeA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB.
Let JGv (tv : list (sv * sv)) (am : amode) : jpred := JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB tv am.
Let Q : assn := LQP segsU LD.NP rho0 (Posts_loF_U Kc FB).

Lemma txt_pcl : forall rho o a, LD.P0_lo FB rho0 -> agree_vals LD.NP rho0 rho -> LD.is_txt o = true ->
  fst (obj_range rho o) <= a < snd (obj_range rho o) -> pclF segsU C_U rho0 FB a.
Proof.
  intros rho o a HP0 Hav Ht Hr. unfold LD.is_txt in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  unfold LD.vB, LD.vL in Hr. rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 13%positive ltac:(reflexivity)), <- (Hw 14%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  right; right.
  pose proof (bv_urange (rw rho0 14)) as R14.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 14))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.

Lemma TXT : forall (rho : valuation) (kept : list (sv * sv)) (R : list sobj) (o : sobj) (a : Z),
  LD.P0_lo FB rho0 -> agree_vals LD.NP rho0 rho -> In o R -> LD.is_txt o = true ->
  fst (obj_range rho o) <= a < snd (obj_range rho o) -> pclF segsU C_U rho0 (FBx FB rho kept) a.
Proof.
  intros rho kept R o a HP0 Hav _ Ht Hr. apply pclF_FBx. exact (txt_pcl rho o a HP0 Hav Ht Hr).
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall (J : jpred) (S : sstate) (rho : valuation) (Q' : assn),
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
     smatch segsU rhoL L (tr', mkCfg ms' md') -> JL (rho_sub (rho_absorb rho R ms) s) rhoL tr' md' ->
     import_okP rho ms R s Pre L rhoL /\
     (forall rho', call_linkP rho ms R s Pre C L rho' rhoL ->
        TR (SPJ segsU (J_ofP JL (rho_sub (rho_absorb rho R ms) s) rhoL) (import_post s (ss_next Pre) L (ss_next C) R) rho') Q')) ->
  TR (SPJ segsU J C rho) Q'.
Hypothesis TR_callJ : forall (J Jp Jp' Jc' : jpred) (C0 Pre : sstate) (s : wsub) (R : list sobj) (Posts : list leaf)
  (Q' : assn) (rho : valuation),
  entails_fr C0 Pre s = Some R -> call_check C0 Pre s R Posts = true ->
  (forall rho1 : valuation, TR (SPJ segsU Jp Pre rho1) (LQJ segsU Jp' (ss_next Pre) rho1 Posts)) ->
  (forall tr ms md, smatch segsU rho C0 (tr, mkCfg ms md) -> J rho tr md -> Jp (rho_sub (rho_absorb rho R ms) s) tr md) ->
  (forall L rho' rhoL tr ms md tr' md', In L Posts -> smatch segsU rho C0 (tr, mkCfg ms md) -> J rho tr md ->
     call_link rho ms R s Pre C0 (lf_state L) rho' rhoL -> Jp' rhoL tr' md' -> Jc' rho' tr' md') ->
  (forall L rho', In L Posts -> agree_below (ss_next C0) rho rho' ->
     TR (SPJ segsU Jc' (import_post s (ss_next Pre) (lf_state L) (ss_next C0) R) rho') Q') ->
  TR (SPJ segsU J C0 rho) Q'.

Hypothesis CMALLOC : forall Ai rho1,
  TR (SPJ segsU (J_alloc_pre segsU C_U Ai Kc) (Pre_malloc EC_U) rho1) (LQP segsU NF rho1 (Posts_malloc segsU C_U EC_U Ai Kc)).
Hypothesis CBI : forall tv am rho rho1,
  TR (SP segsU (fun tr md => JGv tv am rho tr md) Pre_bi rho1)
     (LQ segsU (fun tr md => JGv tv am rho tr md) (ss_next Pre_bi) rho1 Posts_bi).
Hypothesis CBLI : forall (FBc : list (Z * Z)) (rho1 : valuation),
  TR (SPJ segsU (JGA_pre segsU C_U Kc (S_bli.P0_bli FBc) FBc S_bli.tv0 ANone) S_bli.Pre_bli0 rho1)
     (LQP segsU NF rho1 (PostsCA segsU C_U Kc S_bli.P0_bli (PDAnone S_bli.PD_bli_darr) FBc)).
Hypothesis KLOOP : forall rho b, TR (SPJ segsU (JGv LoU.tvL LoU.amL) LoU.K_loop rho) (FAM b).
Hypothesis KTAIL : forall rho b, TR (SPJ segsU (JGv LoU.tvL LoU.amL) LoU.K_tail rho) (FAM b).
Hypothesis KBD : forall rho b, TR (SPJ segsU (JGv LoU.tvL LoU.amL) LoU.K_bd rho) (FAM b).
Hypothesis REENTER : forall (T : sstate) (tv : list (sv * sv)) (am : amode) (rT : Z) (vT : sv) (rho : valuation) (b : Z),
  In ((T, (tv, am)), (rT, vT)) cutsE -> 0 <= rT -> (rT + 1) * 2 ^ 64 <= b ->
  TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis POST : forall (P : sstate) (tv : list (sv * sv)) (am : amode) (rho : valuation) (b : Z),
  In (P, JLGA segsU C_U Kc (LD.P0_lo FB) FB tv am) (Posts_loF_U Kc FB) ->
  TR (SPJ segsU (JGv tv am) P rho) (FAM b).

Let MALLOC := malloc_callAT segsU C_U EC_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML TR TR_facts TR_ex TR_pre TR_callP.
Let PURE := pure_callAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML TR TR_facts TR_pre TR_callJ.

Lemma bound_ge : forall r b rho v,
  (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v) <->
  (r + 1 <= b \/ (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v)).
Proof using . intros. pose proof (urange (eval rho v)). nia. Qed.
Ltac reenter T tv am rT vT := apply (REENTER T tv am rT vT); [cbn; tauto | lia | first [lia | unfold ameas, ad_rank, ad_var; cbn [fst snd]; apply bound_ge; left; lia]].

Lemma X_P_err : forall rho b, TR (SPJ segsU (JGv [] ANone) P_err_U rho) (FAM b).
Proof using POST. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_E_m : forall rho, TR (SPJ segsU (JGv [] ANone) E_m rho) (FAM (ameas ((E_m, ([], ANone)), (95, z0)) rho)).
Proof using CMALLOC ML REENTER TR_callP TR_ex TR_facts TR_pre.
  intros rho.
  apply (MALLOC E_m s_m R_m rho [] ANone _ CMALLOC).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HXA (rhoM & md & HM) HT. split.
    + eapply (robjs_check_sound segsU C_U FB Ai rho (ss_facts E_m) [] None LD.is_txt R_m None rhoM md HM HT HF HN HD HZ);
        [vm_compute; reflexivity | | exact I].
      intros o a _ Hx Hr. apply (pclF_caddrT segsU C_U LD.NP rho0 FB (TobjJVA.NP_ok_intro LD.NP eq_refl) rho Ai a Hav HT HP).
      exact (txt_pcl rho o a HP0 Hav Hx Hr).
    + change (wsub_get s_m 12) with (SLit 64). rewrite U_lit. unfold M64v. lia.
  - intros rho' _.
    replace (T_after E_m s_m R_m (L_malloc_null EC_U)) with T_mnull by (vm_compute; reflexivity).
    reenter T_mnull (@nil (sv * sv)) ANone 90 z0.
  - intros rho' _.
    replace (T_after E_m s_m R_m (L_malloc_ok EC_U)) with T_mok0 by (vm_compute; reflexivity).
    change (pos_add_nat (ss_next E_m) 10) with vN. change (wsub_get s_m 12) with (SLit 64).
    eapply TR_pre; [ | reenter T_mok tv_m ANone 90 z0 ].
    intros w Hw. unfold T_mok. apply SPJ_refacts_J; [exact Hw | reflexivity |].
    intros tr md HJ HF.
    eapply (JGA_tv_facts segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB); [exact HJ | left; reflexivity |].
    eapply (tnz_of_fact rho' (SVar vN)). pick_facts HF [19%nat]. assumption.
Qed.

Lemma X_bi : forall rho, TR (SPJ segsU (JGv tv_m ANone) X_bi_raw rho) (FAM (ameas ((X_bi_raw, (tv_m, ANone)), (85, z0)) rho)).
Proof using CBI ML REENTER TR_callJ TR_facts TR_pre.
  intros rho.
  apply (TR_pre (SPJ segsU (JGv tv_m ANone) E_bi rho)).
  { intros w Hw. exact (SPJ_bi_prep _ rho X_bi_raw E_bi w bi_prep_eq Hw). }
  apply (PURE E_bi Pre_bi s_bi R_bi Posts_bi rho tv_m ANone _ (CBI tv_m ANone rho)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros L rho' HL _. destruct HL as [<-|[]]. cbn [lf_state].
    change (add_facts (ss_facts E_bi) (import_post s_bi (ss_next Pre_bi) P_bi (ss_next E_bi) R_bi)) with T_bi.
    reenter T_bi tv_m ANone 80 z0.
Qed.

Lemma X_TN : forall rho b, 61 * 2 ^ 64 <= b -> TR (SPJ segsU (JGv tvT ANone) T_N rho) (FAM b).
Proof using ML REENTER TR_exw TR_pre.
  intros rho b Hb.
  apply (TR_pre (SPJ segsU (JGv (tvT ++ nulls) (AHead (SLit 0))) T_L2 rho)).
  { intros w Hw.
    apply (SPJ_JGA_head0 segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB (tvT ++ nulls) (SLit 0) T_L2 rho w ltac:(vm_compute; reflexivity)).
    apply (SPJ_JGA_add_nulls segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB tvT nulls ANone T_L2 rho w ltac:(vm_compute; reflexivity)).
    apply (SPJ_restate segsU _ rho T_L T_L2 w [(SAlu ALU_XOR LD.vOUT (SLit 18446744073709551615), LoU.vOUTn)] []);
      [vm_compute; reflexivity | vm_compute; reflexivity | | constructor | ].
    { constructor; [|constructor]. cbn [fst snd]. unfold LoU.vOUTn. apply xor_lit_eq. }
    apply (SPJ_nsteps segsU _ land_ns rho T_Z T_L w ltac:(vm_compute; reflexivity)).
    change T_Z with (fold_left obj_forget fg_idx T_Z0). apply SPJ_forget_all.
    apply (SPJ_zcells segsU _ rho T_Zc 27 [(1264, 1)] T_Z0 w ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
    apply (SPJ_zcells segsU _ rho T_Zb 25 [(885, 1)] T_Zc w ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
    apply (SPJ_zcells segsU _ rho T_Za 24 [(480, 8); (488, 1)] T_Zb w ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
    apply (SPJ_zcells segsU _ rho T_N 22 [(16, 8); (96, 4); (104, 8)] T_Za w ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
    exact Hw. }
  apply (landAs_TR segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML TR TR_pre TR_exw [] sA T_L2 M_A (tvT ++ nulls) tvA LoU.tvL
           (AHead (SLit 0)) LoU.amL rho (FAM b) land_ok (permb_sound _ _ perm_ok)).
  intros rho'. eapply TR_pre; [ | reenter K_A LoU.tvL LoU.amL 60 z0 ].
  intros w Hw. apply (SPJ_add_empties2 segsU _ rho' M_A (LD.datas LD.vsP) w); [vm_compute; reflexivity | vm_compute; reflexivity | exact Hw].
Qed.

Lemma X_bli : forall rho, TR (SPJ segsU (JGv tv_m ANone) E_bli0 rho) (FAM (ameas ((E_bli0, (tv_m, ANone)), (75, z0)) rho)).
Proof using CBLI ML REENTER TR_callP TR_ex TR_exw TR_facts TR_pre.
  intros rho.
  apply (TR_pre (SPJ segsU (JGv (tv_m ++ [LD.nullL]) ANone) E_bl rho)).
  { intros w Hw.
    apply (SPJ_add_empties segsU _ rho E_bl1 [dat0] w ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
    apply (SPJ_nsteps segsU _ bl_ns rho E_bli0 E_bl1 w ltac:(vm_compute; reflexivity)).
    apply (SPJ_JGA_add_nulls segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB tv_m [LD.nullL] ANone E_bli0 rho w ltac:(vm_compute; reflexivity)).
    exact Hw. }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) S_bli.P0_bli S_bli.Pre_bli0
            S_bli.tv0 ANone (PDAnone S_bli.PD_bli_darr) NF eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP CBLI TXT)
            E_bl s_bl tv_m [LD.nullL] ANone 75 z0 conts_bl rho _ chk_bl).
  - intros ms R HF HP0 Hav HZ. change (S_bli.P0_bli ?F ?r) with (LG.P0txt 13 12 F r).
    apply (LG.P0_txt_call FB rho0 rho 13 12 _ R ms s_bl); [vm_compute; reflexivity | vm_compute; reflexivity | exact HP0 | exact Hav].
  - intros c rho' Hc Hm. destruct Hc as [<-|[]]. cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    apply X_TN. unfold ameas, ad_rank, ad_var. cbn [fst snd]. pose proof (urange (eval rho z0)). lia.
Qed.

Lemma exits_ok_all : Forall (fun e => forall rho, TR (SPJ segsU (JGv (ad_tv e) (ad_am e)) (ad_state e) rho) (FAM (ameas e rho))) exitsE.
Proof using CBI CBLI CMALLOC KBD KLOOP KTAIL ML POST REENTER TR_callJ TR_callP TR_ex TR_exw TR_facts TR_pre.
  unfold exitsE.
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; exact X_E_m |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho; apply X_P_err |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; exact X_bi |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; exact X_bli |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho; apply KLOOP |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho; apply KTAIL |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho; apply KBD |].
  apply Forall_nil.
Qed.

Lemma exits_okT : forall X tvX amX rvX rho, In ((X, (tvX, amX)), rvX) exitsE ->
  TR (SPJ segsU (JGv tvX amX) X rho) (FAM (ameas ((X, (tvX, amX)), rvX) rho)).
Proof using CBI CBLI CMALLOC KBD KLOOP KTAIL ML POST REENTER TR_callJ TR_callP TR_ex TR_exw TR_facts TR_pre.
  intros X tvX amX rvX rho Hin. exact (proj1 (Forall_forall _ _) exits_ok_all _ Hin rho).
Qed.
End SumT.

Section Safety.
Hypothesis MC : malloc_contracts segsU C_U EC_U.
Hypothesis BI : builder_init_sum_stmt_U.
Hypothesis BLI : S_bli.bli_darr_stmt_U.
Hypothesis LOOP : K_stmt LoU.K_loop.
Hypothesis TAIL : K_stmt LoU.K_tail.
Hypothesis BD : K_stmt LoU.K_bd.

Theorem lo_entry_S : triple segsU ok (SPJ segsU (JGA_pre segsU C_U Kc (LD.P0_lo FB) FB [] ANone) Pre_lo_U rho0) Q.
Proof using BD BI BLI HS LOOP MC ML TAIL.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGAE segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML 8000 cps_e LD.NP cutsE exitsE ok Q (proj1 HS)
                (ejcertA_jcertA segsU LD.NP _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nA (map (@adrop) cutsE)) w \/ Q w)
                (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
                (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segsU ok A P Q' H)
                (call_soundP segsU ok) (call_soundJ segsU ok)).
       - intros Ai rho1. apply (mc_malloc _ _ _ MC). exact HS.
       - intros tv am rho rho1. apply BI. eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & (_ & HK & _) & _). exact HK.
       - intros FBc rho1. apply (JG_sum_none segsU C_U Kc S_bli.P0_bli S_bli.PD_bli_darr ok NF S_bli.Pre_bli0 S_bli.tv0).
         intros FBc' rho1'. exact (BLI ok Kc FBc' rho1' HS ML MC).
       - intros rho b. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | ].
         exact (LOOP ok Kc FB rho0 HS ML MC rho).
       - intros rho b. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | ].
         exact (TAIL ok Kc FB rho0 HS ML MC rho).
       - intros rho b. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | ].
         exact (BD ok Kc FB rho0 HS ML MC rho).
       - intros T tv am rT vT rho b Hin _ _. exact (reenter_cutGAE segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ok cutsE T tv am (rT, vT) Q rho Hin).
       - intros P tv am rho b Hin. apply (exit_postGA segsU C_U LD.NP Kc (LD.P0_lo FB) FB ok rho0 tv am (Posts_loF_U Kc FB) P). exact Hin. }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.
Hypothesis BIX : builder_init_sum_ex_stmt_U.
Hypothesis BLIX : S_bli.bli_darr_ex_stmt_U.
Hypothesis LOOPX : K_ex_stmt LoU.K_loop.
Hypothesis TAILX : K_ex_stmt LoU.K_tail.
Hypothesis BDX : K_ex_stmt LoU.K_bd.

Theorem lo_entry_E : etriple segsU (SPJ segsU (JGA_pre segsU C_U Kc (LD.P0_lo FB) FB [] ANone) Pre_lo_U rho0) Q.
Proof using BDX BIX BLIX Hvi LOOPX MCX ML TAILX.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML 8000 cps_e LD.NP cutsE exitsE Q ejcert_ok)
         with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
                (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segsU A P Q' H)
                (call_completeP segsU) (call_completeJ segsU)).
       - intros Ai rho1. apply (mcx_malloc _ _ _ MCX). exact Hvi.
       - intros tv am rho rho1. apply BIX.
       - intros FBc rho1. apply (JG_sum_none_ex segsU C_U Kc S_bli.P0_bli S_bli.PD_bli_darr NF S_bli.Pre_bli0 S_bli.tv0).
         intros FBc' rho1'. exact (BLIX Kc FBc' rho1' ML Hvi MCX).
       - intros rho b. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | ].
         exact (LOOPX Kc FB rho0 Hvi ML MCX rho).
       - intros rho b. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | ].
         exact (TAILX Kc FB rho0 Hvi ML MCX rho).
       - intros rho b. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | ].
         exact (BDX Kc FB rho0 Hvi ML MCX rho).
       - intros T tv am rT vT rho b Hin H0 Hb. apply (ereenter_cutAE segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB cutsE T tv am (rT, vT) Q b rho Hin).
         unfold ameas, ad_rank, ad_var. cbn [fst snd]. pose proof (urange (eval rho vT)). nia.
       - intros P tv am rho b Hin. apply (eexit_postGA segsU C_U LD.NP Kc (LD.P0_lo FB) FB rho0 tv am (Posts_loF_U Kc FB) P). exact Hin. }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem load_obj_sum_U : malloc_contracts segsU C_U EC_U ->
  K_stmt LoU.K_loop -> K_stmt LoU.K_tail -> K_stmt LoU.K_bd -> load_obj_stmt_U.
Proof.
  intros MC LOOP TAIL BD ok Kc FB rho0 HS.
  exact (lo_entry_S ok Kc FB rho0 HS ClientLaws.malloc_laws_U MC u14e64.builder_init_sum_U vrd.bli_darr_sum_U LOOP TAIL BD).
Qed.

Theorem load_obj_sum_ex_U : malloc_contracts_ex segsU C_U EC_U ->
  K_ex_stmt LoU.K_loop -> K_ex_stmt LoU.K_tail -> K_ex_stmt LoU.K_bd -> load_obj_ex_stmt_U.
Proof.
  intros MCX LOOPX TAILX BDX Kc FB rho0 Hvi.
  exact (lo_entry_E Kc FB rho0 ClientLaws.malloc_laws_U Hvi MCX u14e64.builder_init_sum_ex_U vrd.bli_darr_sum_ex_U LOOPX TAILX BDX).
Qed.

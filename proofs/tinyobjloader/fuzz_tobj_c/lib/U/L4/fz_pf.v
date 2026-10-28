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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require ClientLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform ZeroObj
  CellTile TobjJV TobjJVx TobjArena TobjJVA TobjJVAx TobjJVAs ArenaDestroy FuzzOneIface.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_load__G1.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4 Require Import ZeroKeep.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4 Require Import fz.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation segs := U.Init.segsU.
Local Abbreviation P0_lo := P.Lib_load__G1.Lib_load_obj_defs.P0_lo.

Lemma ejcert_ok : ejcertA segs NF FUEL_fz cutpcs_fz NF cutsE exitsE = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Ltac find_idx F l := lazymatch l with | F :: _ => constr:(O) | _ :: ?t => let i := find_idx F t in constr:(S i) end.
Ltac have_fact HF F :=
  lazymatch type of HF with Forall _ ?l =>
    let l' := eval vm_compute in l in let F' := eval vm_compute in F in let i := find_idx F' l' in
    pose proof (Forall_pick _ _ i F HF eq_refl) end.

Lemma ameas_emeasZ : forall S tv am r v rho,
  ameas (S, (tv, am), (r, v)) rho = emeasZ r v rho.
Proof. intros. reflexivity. Qed.

Lemma pay_range : forall FB rho0 rho o a,
  P0_fz FB rho0 -> agree_vals NF rho0 rho -> is_pay o = true ->
  fst (obj_range rho o) <= a < snd (obj_range rho o) ->
  exists b n, In (b, n) FB /\ b <= a < b + n.
Proof.
  intros FB rho0 rho o a HP0 Hav Ht Hr. unfold is_pay in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 12%positive ltac:(reflexivity)), <- (Hw 13%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  pose proof (bv_urange (rw rho0 13)) as R13.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 13))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.

Section Fz.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs C_U.

Let JGv (tv : list (sv * sv)) (am : amode) : jpred := JGA segs C_U NF Kc rho0 (P0_fz FB) FB tv am.
Let Q : assn := LQP segs NF rho0 (Posts_fuzz segs C_U FZ_U Kc FB).

Lemma pay_pclF : forall rho o a (objs : list sobj) (facts : list sprop),
  In o objs -> is_pay o = true -> P0_fz FB rho0 -> agree_vals NF rho0 rho -> Forall (holds rho) facts ->
  fst (obj_range rho o) <= a < snd (obj_range rho o) -> pclF segs C_U rho0 FB a.
Proof.
  intros rho o a objs facts _ Ht HP0 Hav _ Hr. destruct (pay_range FB rho0 rho o a HP0 Hav Ht Hr) as (b & n & Hin & Hbn).
  right; right. exists b, n. auto.
Qed.

Lemma pay_caddr_free : forall Ai rhoM rho md tv t o a,
  MInvR segs C_U Ai rhoM md -> fbin FB Ai -> tvin FB Ai rho tv -> In t tv -> tnz rho t ->
  P0_fz FB rho0 -> agree_vals NF rho0 rho -> is_pay o = true ->
  fst (obj_range rho o) <= a < snd (obj_range rho o) -> caddr segs C_U Ai (Some (fst (tvv rho t))) a.
Proof.
  intros Ai rhoM rho md tv t o a HM HP HN Ht Hnz HP0 Hav Htx Hr.
  destruct (pay_range FB rho0 rho o a HP0 Hav Htx Hr) as (b & n & Hin & Hbn).
  right; right. exists b, n. split; [exact (HP _ Hin)|]. split; [|exact Hbn].
  intros Heq. injection Heq as Heq.
  destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (Tpos & Tin & Tfb).
  unfold tvv in Heq, Tpos, Tin, Tfb. cbn [fst snd] in Heq, Tpos, Tin, Tfb. rewrite Heq in Tin, Tfb.
  set (tn := bv_unsigned (eval rho (snd t))) in *.
  assert (Hne : (b, tn) <> (b, n)) by (intros E; apply Tfb; rewrite E; exact Hin).
  exact (blocks_bases_differ segs C_U Ai rhoM md b tn b n HM Tin (HP _ Hin) Hne Tpos ltac:(lia) eq_refl).
Qed.

Lemma SPJ_JGA_JG : forall tv am S rho w,
  SPJ segs (JGv tv am) S rho w -> SPJ segs (JG segs C_U NF Kc rho0 (P0_fz FB) FB tv) S rho w.
Proof. intros tv am S rho w [Hs [Ai [HJ _]]]. split; [exact Hs|]. exists Ai. exact HJ. Qed.

Lemma lo_facts_ok : forall rho, Forall (holds rho) (ss_facts E_lo) -> Forall (holds rho) lo_facts.
Proof.
  intros rho HF.
  have_fact HF (SPUle (SVar 30) (SAlu ALU_ADD spm (SVar 15))). have_fact HF (SPBranch BC_GE (SLit (- FZ_DEPTH)) (SVar 15)).
  have_fact HF (SPBranch BC_GE (SVar 15) (SLit (- 2 ^ 40))). have_fact HF (SPUle (SVar 10) (SLit (2 ^ 47))).
  have_fact HF (SPUle (SVar 30) (SVar 10)).
  have_fact HF (SPUle (SLit aceil_lo) (SVar V_TOP)). have_fact HF (SPUle (SVar V_TOP) (SLit aceil_hi)). clear HF.
  unfold lo_facts, spm, aceil, FZ_DEPTH, V_TOP in *. zfacts; lia.
Qed.

Lemma P0_lo_of_fz : forall rho R ms,
  P0_fz FB rho0 -> agree_vals NF rho0 rho -> P0_lo (FBx FB rho []) (rho_sub (rho_absorb rho R ms) s_lo).
Proof.
  intros rho R ms HP0 Hav. unfold P.Lib_load__G1.Lib_load_obj_defs.P0_lo. rewrite !rw_call'.
  change (wsub_get s_lo 14) with (SVar 13). change (wsub_get s_lo 13) with (SVar 12). cbn [eval].
  destruct Hav as [Hw _]. rewrite <- (Hw 12%positive ltac:(reflexivity)), <- (Hw 13%positive ltac:(reflexivity)).
  unfold FBx. cbn [List.filter map]. rewrite app_nil_r. exact HP0.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall J S rho (Q' : assn),
  (Forall (holds rho) (ss_facts S) -> TR (SPJ segs J S rho) Q') -> TR (SPJ segs J S rho) Q'.
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : forall (P P' Q' : assn), (forall w, P' w -> P w) -> TR P Q' -> TR P' Q'.
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : forall (X : Prop) (P Q' : assn), (X -> TR P Q') -> TR (fun w => X /\ P w) Q'.
Hypothesis TR_callP : forall J Jp C Pre s R Posts (Q' : assn) rho,
  entails_fr C Pre s = Some R ->
  call_checkP C Pre s R (map fst Posts) = true ->
  (forall rho1, TR (SPJ segs Jp Pre rho1) (LQP segs (ss_next Pre) rho1 Posts)) ->
  (forall tr ms md, smatch segs rho C (tr, mkCfg ms md) -> J rho tr md -> Jp (rho_sub (rho_absorb rho R ms) s) tr md) ->
  (forall L JL tr ms md rhoL tr' ms' md',
     In (L, JL) Posts -> smatch segs rho C (tr, mkCfg ms md) -> J rho tr md ->
     agree_vals (ss_next Pre) (rho_sub (rho_absorb rho R ms) s) rhoL ->
     smatch segs rhoL L (tr', mkCfg ms' md') -> JL (rho_sub (rho_absorb rho R ms) s) rhoL tr' md' ->
     import_okP rho ms R s Pre L rhoL /\
     (forall rho', call_linkP rho ms R s Pre C L rho' rhoL ->
        TR (SPJ segs (J_ofP JL (rho_sub (rho_absorb rho R ms) s) rhoL) (import_post s (ss_next Pre) L (ss_next C) R) rho') Q')) ->
  TR (SPJ segs J C rho) Q'.
Hypothesis CFREE : forall Ai rho1,
  TR (SPJ segs (J_free_pre segs C_U Ai Kc) (Pre_free EC_U) rho1)
     (LQP segs NF rho1 [(L_free EC_U, JL_free segs C_U Ai Kc)]).
Hypothesis CLO : forall FBc rho1,
  TR (SPJ segs (JGA_pre segs C_U Kc (P0_lo FBc) FBc [] ANone) Pre_lo_U rho1)
     (LQP segs NP_lo rho1 (PostsCA segs C_U Kc P0_lo PDA_lo_U FBc)).
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE ->
  0 <= ameas (T, (tv, am), rv) rho < b ->
  TR (SPJ segs (JGv tv am) T rho) (FAM b).
Hypothesis POSTo : forall rho b, TR (SPJ segs (JG segs C_U NF Kc rho0 (P0_fz FB) FB []) L_reto rho) (FAM b).
Hypothesis POSTe : forall rho b, TR (SPJ segs (JG segs C_U NF Kc rho0 (P0_fz FB) FB []) L_rete rho) (FAM b).

Let FREE := free_callAT segs C_U EC_U NF Kc rho0 (P0_fz FB) FB ML TR TR_facts TR_ex TR_pre TR_callP.
Let ENTAS := entAs_TR segs C_U NF Kc rho0 (P0_fz FB) FB ML TR TR_pre TR_exw TR_pureh.
Let CALLLO := client_callAT segs C_U NF Kc rho0 (P0_fz FB) FB ML P0_lo Pre_lo_U [] ANone PDA_lo_U NP_lo
                (@eq_refl positive (ss_next Pre_lo_U)) TR TR_facts TR_ex TR_pre TR_callP CLO.

Lemma reenter_rank : forall T tv am rT vT (X : aedesc) rhoX rho,
  In (T, (tv, am), (rT, vT)) cutsE -> 0 <= rT -> rT + 1 <= ad_rank X ->
  TR (SPJ segs (JGv tv am) T rho) (FAM (ameas X rhoX)).
Proof.
  intros T tv am rT vT X rhoX rho Hin H0 Hr. apply (REENTER T tv am (rT, vT) rho); [exact Hin|].
  unfold ameas, ad_rank, ad_var in *. cbn [fst snd] in *.
  pose proof (urange (eval rho vT)). pose proof (urange (eval rhoX (snd (snd X)))). nia.
Qed.

Lemma E_lo_ok : forall rho,
  TR (SPJ segs (JGv tv00 ANone) E_lo rho) (FAM (ameas (E_lo, (tv00, ANone), (80, z0)) rho)).
Proof.
  intros rho. apply (TR_pre (SPJ segs (JGv tv00 ANone) E_lo3 rho)).
  { intros w Hw.
    apply (SPJ_recell segs _ rho E_lo2 1 0 4294967295 E_lo3 w ltac:(vm_cast_no_check (@eq_refl (option sstate) (Some E_lo3)))).
    apply (SPJ_unbase segs _ rho E_loB 4 (-1856) E_lo2 w ltac:(vm_cast_no_check (@eq_refl (option sstate) (Some E_lo2)))).
    apply (SPJ_unbase segs _ rho E_loA 2 (-216) E_loB w ltac:(vm_cast_no_check (@eq_refl (option sstate) (Some E_loB)))).
    apply (SPJ_unbase segs _ rho E_lo1z 1 (-360) E_loA w ltac:(vm_cast_no_check (@eq_refl (option sstate) (Some E_loA)))).
    apply (SPJ_zero_keep segs _ rho E_lo1 1 E_lo1z w ltac:(vm_cast_no_check (@eq_refl (option sstate) (Some E_lo1z)))).
    apply (SPJ_xforms segs _ [XSplit 0 (SLit (-360)); XSplit 1 (SLit (-216)); XSplit 2 (SLit (-8)); XSplit 4 (SLit (-1856))]
             rho E_lof E_lo1 w ltac:(vm_compute; reflexivity)).
    unfold E_lof. apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md _ HF. apply lo_facts_ok. exact HF. }
  change (JGv tv00 ANone) with (JGv ([] ++ []) ANone).
  apply (CALLLO E_lo3 s_lo R_lo rho [] [] ANone).
  - vm_cast_no_check (@eq_refl (option (list sobj)) (Some R_lo)).
  - vm_cast_no_check (@eq_refl bool true).
  - vm_cast_no_check (@eq_refl bool true).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai ms HF HP0 Hav HP HN HD HZ HXA HM HT. split.
    + eapply (robjs_checkF_sound segs C_U rho0 FB rho (ss_facts E_lo3) [] is_pay R_lo HF (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT)); [exact HZ | vm_cast_no_check (@eq_refl bool true) |].
      intros o a Ho Hx Hr. apply pclF_FBx. exact (pay_pclF rho o a _ _ Ho Hx HP0 Hav HF Hr).
    + apply P0_lo_of_fz; [exact HP0 | exact Hav].
  - intros d rho' Hd Hag. destruct Hd as [<-|[<-|[]]]; cbn [fst snd].
    + match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv ?am) ?T _) _ =>
        replace tv with tv_ok by (vm_compute; reflexivity); replace am with am_ok by (vm_compute; reflexivity);
        replace T with T_ok by (vm_cast_no_check (@eq_refl sstate T_ok)) end.
      apply (TR_pre (SPJ segs (JGv tv_ok am_ok) T_ok1 rho')).
      { intros w Hw.
        apply (SPJ_unbase segs _ rho' T_ok0 0 (-64) T_ok1 w ltac:(vm_cast_no_check (@eq_refl (option sstate) (Some T_ok1)))).
        exact (SPJ_xforms segs _ [XSplit 0 (SLit (-64))] rho' T_ok T_ok0 w ltac:(vm_compute; reflexivity) Hw). }
      apply (reenter_rank T_ok1 tv_ok am_ok 60 z0 _ rho rho'); [apply (nth_error_In cutsE 1); reflexivity | lia | cbn; lia].
    + match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv ?am) ?T _) _ =>
        replace tv with tv00 by (vm_compute; reflexivity); replace am with ANone by (vm_compute; reflexivity);
        replace T with T_err by (vm_cast_no_check (@eq_refl sstate T_err)) end.
      apply (reenter_rank T_err tv00 ANone 60 z0 _ rho rho'); [apply (nth_error_In cutsE 2); reflexivity | lia | cbn; lia].
Qed.

Lemma X_P0_ok : forall rho,
  TR (SPJ segs (JGv tv_ok am_ok) X_P0 rho) (FAM (ameas (X_P0, (tv_ok, am_ok), (50, z0)) rho)).
Proof.
  intros rho.
  apply (TR_pre (SPJ segs (JGv tv_ok am_ok) X_P0f rho)).
  { intros w Hw. unfold X_P0f. apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md _ HF.
    have_fact HF (SPBranch BC_NE pHi (SLit 0)). clear - H. constructor; [|constructor]. unfold pHi in *. zfacts; lia. }
  apply (TR_pre (fun w => exists rho2, agree_below (ss_next X_P0f) rho rho2 /\
                   SPJ segs (JGv (pop_tv pHi (ss_next X_P01) tv_ok) (AHeadN (SVar (ss_next X_P01)) (SVar (ss_next X_P01 + 3)%positive))) X_P02 rho2 w)).
  { intros w Hw.
    destruct (JGA_lenN segs C_U NF Kc rho0 (P0_fz FB) FB ML tv_ok pHi X_P0f rho w eq_refl eq_refl eq_refl ltac:(vm_cast_no_check (@eq_refl bool true)) Hw) as (rho1 & Hag1 & Hw1).
    destruct (JGA_popN segs C_U NF Kc rho0 (P0_fz FB) FB ML (TobjJVA.NP_ok_intro NF eq_refl) tv_ok pHi (SVar (ss_next X_P0f)) X_P01 is_pay rho1 w
                ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl eq_refl eq_refl eq_refl ltac:(vm_cast_no_check (@eq_refl bool true))
                ltac:(intros o a Ho Hx HP0 Hav HF Hr; exact (pay_pclF rho1 o a _ _ Ho Hx HP0 Hav HF Hr)) eq_refl Hw1) as (rho2 & Hag2 & Hw2 & _).
    exists rho2. split; [|exact Hw2].
    eapply agree_below_trans; [exact Hag1|]. eapply agree_below_le; [|exact Hag2]. apply Pos.leb_le. reflexivity. }
  apply TR_exw; intros rho2. apply TR_pureh; intros Hag.
  apply (ENTAS s_P0 (ss_next X_P0f) X_P02 C_L _ tv_L tv_L _ am_L (VGp 2) 40 50 z0 rho rho2).
  - vm_cast_no_check (@eq_refl bool true).
  - apply Permutation_refl.
  - apply agree_below_vals. exact Hag.
  - intros rho' Hm. apply (REENTER C_L tv_L am_L (40, VGp 2) rho'); [apply (nth_error_In cutsE 3); reflexivity | rewrite ameas_emeasZ; exact Hm].
Qed.

Lemma X_P_ok : forall rho,
  TR (SPJ segs (JGv tv_ok am_L) X_P rho) (FAM (ameas (X_P, (tv_ok, am_L), (40, VGm 1)) rho)).
Proof.
  intros rho.
  apply (TR_pre (fun w => exists rho1, agree_below (ss_next X_Pf) rho rho1 /\
                   SPJ segs (JGv (pop_tv pNX (ss_next X_Pf) tv_ok) (AHeadN (SVar (ss_next X_Pf)) (SVar (ss_next X_Pf + 3)%positive))) X_P2 rho1 w)).
  { intros w Hw.
    assert (Hwf : SPJ segs (JGv tv_ok am_L) X_Pf rho w).
    { unfold X_Pf. apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md _ HF.
      have_fact HF (SPNot (SPBranch BC_EQ pNX (SLit 0))). constructor; [exact H | constructor]. }
    destruct (JGA_popN segs C_U NF Kc rho0 (P0_fz FB) FB ML (TobjJVA.NP_ok_intro NF eq_refl) tv_ok pNX vG X_Pf is_pay rho w
                ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl eq_refl eq_refl eq_refl ltac:(vm_cast_no_check (@eq_refl bool true))
                ltac:(intros o a Ho Hx HP0 Hav HF Hr; exact (pay_pclF rho o a _ _ Ho Hx HP0 Hav HF Hr)) eq_refl Hwf) as (rho1 & Hag1 & Hw1 & _).
    exists rho1. split; [exact Hag1 | exact Hw1]. }
  apply TR_exw; intros rho1. apply TR_pureh; intros Hag.
  apply (ENTAS s_P (ss_next X_Pf) X_P2 C_L _ tv_L tv_L _ am_L (VGp 2) 40 40 (VGm 1) rho rho1).
  - vm_cast_no_check (@eq_refl bool true).
  - apply Permutation_refl.
  - apply agree_below_vals. exact Hag.
  - intros rho' Hm. apply (REENTER C_L tv_L am_L (40, VGp 2) rho'); [apply (nth_error_In cutsE 3); reflexivity | rewrite ameas_emeasZ; exact Hm].
Qed.

Lemma E_fd_ok : forall rho,
  TR (SPJ segs (JGv tv_L am_L) E_fd rho) (FAM (ameas (E_fd, (tv_L, am_L), (40, VGp 1)) rho)).
Proof.
  intros rho. apply TR_facts. intros HF0.
  apply (FREE E_fd s_fd R_fd rho tv_L am_L 0%nat (pB, blk_size pNn) _ CFREE).
  - vm_cast_no_check (@eq_refl (option (list sobj)) (Some R_fd)).
  - vm_cast_no_check (@eq_refl bool true).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HX HM HT.
    change (wsub_get s_fd 12) with pB. change (wsub_get s_fd 13) with (blk_size pNn).
    assert (Tnz : tnz rho (pB, blk_size pNn)).
    { apply tnz_of_fact. have_fact HF (SPUle (SLit 4096) pB). clear - H. intros Hz%holds_beq. unfold pB in *. zfacts; lia. }
    split; [exact Tnz|]. split; [reflexivity|].
    destruct HM as (rhoM & md & HM).
    eapply (robjs_check_sound segs C_U FB Ai rho (ss_facts E_fd) tv_L (Some 0%nat) is_pay R_fd _ rhoM md HM HT HF HN HD HZ).
    + vm_cast_no_check (@eq_refl bool true).
    + intros o a Ho Hx Hr. change (bv_unsigned (eval rho pB)) with (fst (tvv rho (pB, blk_size pNn))).
      exact (pay_caddr_free Ai rhoM rho md tv_L _ o a HM HP HN ltac:(left; reflexivity) Tnz HP0 Hav Hx Hr).
    + exists (pB, blk_size pNn). split; [reflexivity|]. split; [exact Tnz | reflexivity].
  - intros rho' Hag.
    replace (T_after E_fd s_fd R_fd (L_free EC_U)) with T_fd by (vm_cast_no_check (@eq_refl sstate T_fd)).
    change (remove_nth 0 tv_L) with tv_ok.
    apply (REENTER T_fd tv_ok am_L (40, VGp 0) rho'); [apply (nth_error_In cutsE 4); reflexivity|].
    have_fact HF0 (SPUle vG (SLit two52)). clear - H Hag.
    unfold ameas, ad_rank, ad_var. cbn [fst snd]. unfold VGp, vG, two52 in *.
    rewrite <- (eval_agree_vals (ss_next E_fd) rho rho' (SAlu ALU_ADD (SVar 404) (SLit 0)) Hag eq_refl).
    zfacts; lia.
Qed.

Lemma E_FAR_free : forall rhoX rho (X : aedesc), 21 <= ad_rank X ->
  TR (SPJ segs (JGv tv_ok am0) E_FAR rho) (FAM (ameas X rhoX)).
Proof.
  intros rhoX rho X HX.
  apply (FREE E_FAR s_fa R_fa rho tv_ok am0 0%nat (xARi, SLit 64) _ CFREE).
  - vm_cast_no_check (@eq_refl (option (list sobj)) (Some R_fa)).
  - vm_cast_no_check (@eq_refl bool true).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HX' HM HT.
    change (wsub_get s_fa 12) with xARi. change (wsub_get s_fa 13) with (SLit 64).
    assert (Tnz : tnz rho (xARi, SLit 64)).
    { apply tnz_of_fact. have_fact HF (SPUle (SLit 4096) xARi). clear - H. intros Hz%holds_beq. unfold xARi in *. zfacts; lia. }
    split; [exact Tnz|]. split; [reflexivity|].
    destruct HM as (rhoM & md & HM).
    eapply (robjs_check_sound segs C_U FB Ai rho (ss_facts E_FAR) tv_ok (Some 0%nat) is_pay R_fa _ rhoM md HM HT HF HN HD HZ).
    + vm_cast_no_check (@eq_refl bool true).
    + intros o a Ho Hx Hr. change (bv_unsigned (eval rho xARi)) with (fst (tvv rho (xARi, SLit 64))).
      exact (pay_caddr_free Ai rhoM rho md tv_ok _ o a HM HP HN ltac:(left; reflexivity) Tnz HP0 Hav Hx Hr).
    + exists (xARi, SLit 64). split; [reflexivity|]. split; [exact Tnz | reflexivity].
  - intros rho' Hag.
    replace (T_after E_FAR s_fa R_fa (L_free EC_U)) with T_far by (vm_cast_no_check (@eq_refl sstate T_far)).
    change (remove_nth 0 tv_ok) with tv00.
    apply (REENTER T_far tv00 am0 (20, z0) rho'); [apply (nth_error_In cutsE 5); reflexivity|].
    unfold ameas, ad_rank, ad_var in *. cbn [fst snd] in *. unfold z0. rewrite U_lit. unfold M64v. rewrite Z.mod_0_l by lia.
    pose proof (urange (eval rhoX (snd (snd X)))). nia.
Qed.

Lemma X_far0_ok : forall rho,
  TR (SPJ segs (JGv tv_ok am_ok) X_far0 rho) (FAM (ameas (X_far0, (tv_ok, am_ok), (55, z0)) rho)).
Proof.
  intros rho. apply (TR_pre (SPJ segs (JGv tv_ok am0) E_FAR (rho_sub rho (infer_sub NF X_far0 E_FAR)))); [|apply (E_FAR_free rho); cbn; lia].
  intros w Hw. apply (SPJ_entails_JGA segs C_U NF Kc rho0 (P0_fz FB) FB ML X_far0 E_FAR _ tv_ok tv_ok am0 am0 rho w);
    [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true) | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  eapply (SPJ_head0 segs C_U NF Kc rho0 (P0_fz FB) FB). exact Hw.
Qed.

Lemma X_far1_ok : forall rho,
  TR (SPJ segs (JGv tv_ok am_L) X_far1 rho) (FAM (ameas (X_far1, (tv_ok, am_L), (30, z0)) rho)).
Proof.
  intros rho. apply (TR_pre (SPJ segs (JGv tv_ok am0) E_FAR (rho_sub rho s_far1))); [|apply (E_FAR_free rho); cbn; lia].
  intros w Hw. apply (SPJ_entails_JGA segs C_U NF Kc rho0 (P0_fz FB) FB ML X_far1 E_FAR s_far1 tv_ok tv_ok am0 am0 rho w);
    [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true) | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  eapply (SPJ_head0 segs C_U NF Kc rho0 (P0_fz FB) FB). exact Hw.
Qed.

Lemma X_ret_ok : forall rho b, TR (SPJ segs (JGv tv00 am0) X_ret rho) (FAM b).
Proof.
  intros rho b. apply (TR_pre (SPJ segs (JG segs C_U NF Kc rho0 (P0_fz FB) FB []) L_reto (rho_sub rho s_ret))); [|apply POSTo].
  intros w Hw. apply (SPJ_JGA_JG tv00 am0).
  apply (SPJ_entails_JGA segs C_U NF Kc rho0 (P0_fz FB) FB ML X_ret2 L_reto s_ret tv00 tv00 am0 am0 rho w);
    [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true) | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  apply (SPJ_unbase segs _ rho X_ret1 1 (-368) X_ret2 w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ ret_xforms rho X_ret X_ret1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma X_rete_ok : forall rho b, TR (SPJ segs (JGv tv00 ANone) X_rete rho) (FAM b).
Proof.
  intros rho b. apply (TR_pre (SPJ segs (JG segs C_U NF Kc rho0 (P0_fz FB) FB []) L_rete (rho_sub rho s_rete))); [|apply POSTe].
  intros w Hw. apply (SPJ_JGA_JG tv00 ANone).
  apply (SPJ_entails_JGA segs C_U NF Kc rho0 (P0_fz FB) FB ML X_rete2 L_rete s_rete tv00 tv00 ANone ANone rho w);
    [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true) | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  apply (SPJ_unbase segs _ rho X_rete1 1 (-368) X_rete2 w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ rete_xforms rho X_rete X_rete1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma exits_okT : forall X tvX amX rvX rho,
  In (X, (tvX, amX), rvX) exitsE ->
  TR (SPJ segs (JGv tvX amX) X rho) (FAM (ameas (X, (tvX, amX), rvX) rho)).
Proof.
  intros X tvX amX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]; injection H as <- <- <- <-.
  - apply E_lo_ok.
  - apply X_rete_ok.
  - apply X_P0_ok.
  - apply X_far1_ok.
  - apply X_far0_ok.
  - apply E_fd_ok.
  - apply X_P_ok.
  - apply X_ret_ok.
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ok_sideK segs ok Kc.
Hypothesis MC : malloc_contracts segs C_U EC_U.
Hypothesis LOAD : load_obj_stmt_U.

Theorem fuzz_one_triple :
  triple segs ok (SPJ segs (JG_pre segs C_U Kc (P0_fz FB) FB []) Pre_fz rho0) Q.
Proof.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGAE segs C_U NF Kc rho0 (P0_fz FB) FB ML FUEL_fz cutpcs_fz NF cutsE exitsE ok Q (proj1 HS)
                (ejcertA_jcertA segs NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map (nodeA segs C_U NF Kc rho0 (P0_fz FB) FB) (map (@adrop) cutsE)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                (triple_pureh segs ok)
                (call_soundP segs ok)).
       - intros Ai rho1. apply (mc_free _ _ _ MC). exact HS.
       - intros FBc rho1. apply (LOAD ok Kc FBc rho1 HS).
       - intros T tv am rv rho b Hin _. exact (reenter_cutGAE segs C_U NF Kc rho0 (P0_fz FB) FB ok cutsE T tv am rv Q rho Hin).
       - intros rho b. apply (exit_postG segs C_U NF Kc (P0_fz FB) FB ok rho0 [] (Posts_fuzz segs C_U FZ_U Kc FB) L_reto). cbn. right. left. reflexivity.
       - intros rho b. apply (exit_postG segs C_U NF Kc (P0_fz FB) FB ok rho0 [] (Posts_fuzz segs C_U FZ_U Kc FB) L_rete). cbn. left. reflexivity. }
  intros w Hw. destruct (JG_pre_intro segs C_U NF Kc (P0_fz FB) FB rho0 [] Pre_fz w Hw) as [Hs HJ]. split; [exact Hs|].
  apply (proj2 (JGA_none segs C_U NF Kc rho0 (P0_fz FB) FB [] _ _ _)). exact HJ.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segs C_U EC_U.
Hypothesis LOADX : load_obj_ex_stmt_U.

Theorem fuzz_one_etriple :
  etriple segs (SPJ segs (JG_pre segs C_U Kc (P0_fz FB) FB []) Pre_fz rho0) Q.
Proof.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JGA segs C_U NF Kc rho0 (P0_fz FB) FB ML FUEL_fz cutpcs_fz NF cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeA segs C_U NF Kc rho0 (P0_fz FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                (etriple_pureh segs)
                (call_completeP segs)).
       - intros Ai rho1. apply (mcx_free _ _ _ MCX). exact Hvi.
       - intros FBc rho1. apply (LOADX Kc FBc rho1 Hvi).
       - intros T tv am rv rho b Hin Hm. exact (ereenter_cutAE segs C_U NF Kc rho0 (P0_fz FB) FB cutsE T tv am rv Q b rho Hin Hm).
       - intros rho b. apply (eexit_postG segs C_U NF Kc (P0_fz FB) FB rho0 [] (Posts_fuzz segs C_U FZ_U Kc FB) L_reto). cbn. right. left. reflexivity.
       - intros rho b. apply (eexit_postG segs C_U NF Kc (P0_fz FB) FB rho0 [] (Posts_fuzz segs C_U FZ_U Kc FB) L_rete). cbn. left. reflexivity. }
  intros w Hw. destruct (JG_pre_intro segs C_U NF Kc (P0_fz FB) FB rho0 [] Pre_fz w Hw) as [Hs HJ]. split; [exact Hs|].
  apply (proj2 (JGA_none segs C_U NF Kc rho0 (P0_fz FB) FB [] _ _ _)). exact HJ.
Qed.
End Existence.
End Fz.

Theorem fuzz_one_ok_U :
  malloc_laws segs C_U -> malloc_contracts segs C_U EC_U -> load_obj_stmt_U -> fuzz_one_sum_stmt_U.
Proof. intros ML MC LOAD ok Kc FBc rho1 HS. exact (fuzz_one_triple Kc FBc rho1 ML ok HS MC LOAD). Qed.

Theorem fuzz_one_ex_ok_U :
  malloc_laws segs C_U -> malloc_contracts_ex segs C_U EC_U -> load_obj_ex_stmt_U -> fuzz_one_sum_ex_stmt_U.
Proof. intros ML MCX LOADX Kc FBc rho1 Hvi. exact (fuzz_one_etriple Kc FBc rho1 ML Hvi MCX LOADX). Qed.

Theorem fuzz_one_U : malloc_contracts segs C_U EC_U -> load_obj_stmt_U -> fuzz_one_sum_stmt_U.
Proof. intros MC LOAD. exact (fuzz_one_ok_U ClientLaws.malloc_laws_U MC LOAD). Qed.

Theorem fuzz_one_ex_U : malloc_contracts_ex segs C_U EC_U -> load_obj_ex_stmt_U -> fuzz_one_sum_ex_stmt_U.
Proof. intros MCX LOADX. exact (fuzz_one_ex_ok_U ClientLaws.malloc_laws_U MCX LOADX). Qed.

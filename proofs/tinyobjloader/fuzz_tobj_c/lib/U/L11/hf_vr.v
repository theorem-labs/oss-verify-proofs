From Stdlib Require Import ZArith NArith List Bool PArith Lia Sorting.Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module VRU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9.S_vr.

Ltac argty f := let t := type of f in lazymatch t with forall _ : ?A, _ => exact A end.

Definition vr_site_checkU (E2 : sstate) (s : wsub) (j : nat) (nzk : list (positive * Z * positive))
    (TA TF : sstate) (vA : sv) (rA : Z) (vF : sv) (rF : Z) (rE : Z) (vE : sv) : bool :=
  match entails_fr E2 VRU.Pre_vr s with
  | Some R =>
      let Tk := T_afterN NF E2 s R VRU.P_keep in
      let Tk1 := add_facts (TobjJVx.nz_facts nzk) Tk in
      let Tf := T_afterN NF E2 s R VRU.P_fail in
      let Tg := T_afterN NF E2 s R VRU.P_grown in
      let kept := keptH j in
      let tvj := kept ++ [tvH_x j] in
      let tvk := kept ++ import_tv (import_sub s NF VRU.P_keep (ss_next E2)) VRU.tv0 in
      call_checkT C_U NP E2 VRU.Pre_vr s R (map fst VRU.PD_vr) &&
      wsub_dom_below s NF &&
      Pos.leb NP (ss_next E2) &&
      tv_below (ss_next E2) tvj &&
      tv_sub_eqb s [tvH_x j] VRU.tv0 &&
      forallb (fun d => tvL_ok NF s (ss_next E2) (fst d) (snd d) && new_objs_tv VRU.Pre_vr (fst d) (snd d))
        VRU.PD_vr &&
      robjs_check (ss_facts E2) kept None is_txt R &&
      forallb (sprop_below (ss_next Tk)) (TobjJVx.nz_facts nzk) &&
      forallb (TobjJVx.nz_entry_check (ss_facts Tk) tvk) nzk &&
      TobjJVx.contE_check NP (xs_keep (nobj Tk1)) 0 (-272) (ss_next E2) Tk1 TA tvk tvj vA rA rE vE &&
      TobjJVx.contE_check NP (xs_keep (nobj Tf)) 0 (-272) (ss_next E2) Tf TF
        (kept ++ import_tv (import_sub s NF VRU.P_fail (ss_next E2)) VRU.tv0) tvj vF rF rE vE &&
      TobjJVx.contE_check NP (xs_grown (nobj Tg)) 0 (-272) (ss_next E2) Tg TA
        (kept ++ import_tv (import_sub s NF VRU.P_grown (ss_next E2)) VRU.tv_post) tvj vA rA rE vE
  | None => false
  end.

Section VrSite.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.

Lemma txt_extra_ok_hfU : forall rho kept R o a,
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

Hypothesis ML : malloc_laws segsU C_U.
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
Hypothesis CVR : forall FBc rho1,
  TR (SPJ segsU (JG_pre segsU C_U Kc VRU.P0_vr FBc VRU.tv0) VRU.Pre_vr rho1)
     (LQP segsU NF rho1 (VRU.Posts_vr Kc FBc)).
Variable CUTS : list edesc.
Hypothesis REENTER : forall T tv rv rho b, In (T, tv, rv) CUTS ->
  0 <= emeas (T, tv, rv) rho /\ emeas (T, tv, rv) rho < b ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv) T rho) (FAM b).

Let CLIENT := client_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML (fun _ => VRU.P0_vr)
  VRU.Pre_vr VRU.tv0 VRU.PD_vr NF eq_refl TR TR_facts TR_ex TR_pre TR_callP CVR.
Let CONT := TobjJVx.contE_TR segsU C_U NP Kc rho0 (P0_hf FB) FB ML TR TR_pre TR_exw TR_pureh.

Lemma permH : forall j, (j < 9)%nat -> Permutation (keptH j ++ [tvH_x j]) tvH.
Proof.
  intros j Hj. apply Permutation_sym.
  pose proof (TobjJVx.perm_move_last (tvH_l1 j) (tvH_l2 j) (tvH_x j)) as Hpm.
  rewrite <- (tvH_split j Hj) in Hpm. exact Hpm.
Qed.

Lemma X_vr_site : forall (E E2 : sstate) (xs : list xform) (i : nat) (c : Z) (s : wsub) (j : nat)
    (nzk : list (positive * Z * positive)) (TA TF : sstate) (vA : sv) (rA : Z) (vF : sv) (rF : Z)
    (rE : Z) (vE : sv) (d k : positive) (e : Z) (rho : valuation),
  TobjJVx.norm_xu xs i c E = Some E2 ->
  vr_site_checkU E2 s j nzk TA TF vA rA vF rF rE vE = true ->
  (j < 9)%nat ->
  wsub_get s 17 = SVar k -> wsub_get s 15 = SVar d ->
  tvH_x j = (SVar d, SMd M_MUL (SLit e) (SVar k)) ->
  In (SPUle (SVar k) (SLit VRU.two47)) (ss_facts E2) ->
  1 <= e <= 4096 ->
  In (TA, tvH, (rA, vA)) CUTS -> In (TF, tvH, (rF, vF)) CUTS ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tvH) E rho) (FAM (emeas (E, tvH, (rE, vE)) rho)).
Proof.
  intros E E2 xs i c s j nzk TA TF vA rA vF rF rE vE d k e rho HN H Hj H17 H15 Hx Hk He HA HF.
  unfold vr_site_checkU in H.
  destruct (entails_fr E2 VRU.Pre_vr s) as [R|] eqn:HE; [|discriminate].
  cbv zeta in H.
  apply andb_prop in H as [H Cg]. apply andb_prop in H as [H Cf]. apply andb_prop in H as [H Ck].
  apply andb_prop in H as [H Cnz]. apply andb_prop in H as [H Cnb]. apply andb_prop in H as [H C2].
  apply andb_prop in H as [H Cp]. apply andb_prop in H as [H Cs]. apply andb_prop in H as [H Cb].
  apply andb_prop in H as [H Cn]. apply andb_prop in H as [C1 Cd].
  rewrite (TobjJVx.emeas_emeasZ E tvH rE vE rho).
  eapply TR_pre.
  2: { apply (CLIENT E2 s R rho (keptH j) [tvH_x j] _ HE C1 Cd Cn Cb Cs Cp).
  -
    intros Ai ms HFc HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound;
        [exact HFc | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ).
        apply in_or_app. left. exact Ht.
      * intros o a Ho Hxo Hr. eapply txt_extra_ok_hfU; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho d k e); [exact H17 | exact H15 | | | lia].
      * unfold tvz in *. constructor; [|constructor]. rewrite <- Hx.
        apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * exact (proj1 (Forall_forall _ _) HFc _ Hk).
  -
    intros dd rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply TR_pre.
      2: { eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ Ck); [apply permH; exact Hj | exact Hag |].
           intros rho'' Hm. apply (REENTER TA tvH (rA, vA) rho''); [exact HA |].
           rewrite TobjJVx.emeas_emeasZ. exact Hm. }
      intros w Hw. apply SPJ_refacts_J; [exact Hw | exact Cnb |].
      intros tr md HJ HFX.
      eapply (TobjJVx.nz_facts_sound segsU C_U NP Kc rho0 (P0_hf FB) FB _ _ nzk); [exact Cnz | exact HFX | exact HJ].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ Cf); [apply permH; exact Hj | exact Hag |].
      intros rho'' Hm. apply (REENTER TF tvH (rF, vF) rho''); [exact HF |].
      rewrite TobjJVx.emeas_emeasZ. exact Hm.
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ Cg); [apply permH; exact Hj | exact Hag |].
      intros rho'' Hm. apply (REENTER TA tvH (rA, vA) rho''); [exact HA |].
      rewrite TobjJVx.emeas_emeasZ. exact Hm.
  }
  intros w Hw. apply (TobjJVx.SPJ_norm_xu segsU _ _ _ _ _ _ rho w HN).
  rewrite (tvH_split j Hj) in Hw.
  apply (TobjJVx.SPJ_JG_move_last segsU C_U NP Kc rho0 (P0_hf FB) FB (tvH_l1 j) (tvH_l2 j) (tvH_x j)).
  exact Hw.
Qed.

End VrSite.

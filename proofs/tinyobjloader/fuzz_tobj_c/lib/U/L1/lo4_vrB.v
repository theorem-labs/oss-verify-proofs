From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout MallocLaws Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG SymEntail SymFrame SymSummary SymSoundR Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform TobjJV TobjJVx TobjJVA TobjJVAx TobjJVAy.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo lo_defs lo_view lo4_meas lo4_common.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require Import S_vr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module LG := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue.
Module HFD := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.

(* Call of vec_reserve (0x167f8) from 0x14640: a0 = the builder vector header at builder+120, a2 = allocator; 32-byte frame; it may grow that vector (slot 0). *)
Definition E_vrB : sstate := LoSite.E_vrB.
Definition vops_vrB : list LD.vop := [LD.VVec 120; LD.VDeep 32].
Definition ns_vrB : list nstep := Eval vm_compute in LoV.view_ns E_vrB vops_vrB.
Definition Ev_vrB : sstate := Eval vm_compute in LoV.view vops_vrB E_vrB.
Lemma view_vrB : run_nsteps E_vrB ns_vrB = Some Ev_vrB.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition slots_vrB : list nat := [0]%nat.
Lemma perm_vrB : permb LoU.tvL (LoV.keptL slots_vrB ++ LoV.passedL slots_vrB) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition x_vrB : wsub := [(99%positive, LD.pH); (19%positive, SAlu ALU_ADD LD.vDp (SLit 32))].
Definition s_vrB : wsub := Eval vm_compute in LoV.sOf Ev_vrB Pre_vr x_vrB.
Definition R_vrB : list sobj := Eval vm_compute in LoV.R_of Ev_vrB Pre_vr x_vrB.
Definition A_vrB1 : sstate := Eval vm_compute in T_afterN 100 Ev_vrB s_vrB R_vrB (P_keep).
Definition T_vrB1 : sstate := Eval vm_compute in LoV.renorm A_vrB1.
Definition is_vrB1 : wsub := Eval vm_compute in import_sub s_vrB 100 (P_keep) (ss_next Ev_vrB).
Definition tvT_vrB1 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_vrB (import_tv is_vrB1 tv0).
(* After the keep return the vector still has room for the wanted count >= 2, so its data pointer is non-null and the
   tracked-vector facts (4096 <= d, d + 4 cap <= hiA) hold: the return node carries them for the pointer checks that follow. *)
Definition nz_vrB1 : list (positive * Z * positive) := [(110%positive, 4, 112%positive)].
Lemma nzc_vrB1 : forallb (TobjJVx.nz_entry_check (ss_facts T_vrB1) tvT_vrB1) nz_vrB1 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition K_vrB1 : sstate := Eval vm_compute in add_facts (TobjJVx.nz_facts nz_vrB1) T_vrB1.
Definition A_vrB2 : sstate := Eval vm_compute in T_afterN 100 Ev_vrB s_vrB R_vrB (P_fail).
Definition T_vrB2 : sstate := Eval vm_compute in LoV.renorm A_vrB2.
Definition is_vrB2 : wsub := Eval vm_compute in import_sub s_vrB 100 (P_fail) (ss_next Ev_vrB).
Definition tvT_vrB2 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_vrB (import_tv is_vrB2 tv0).
Definition A_vrB3 : sstate := Eval vm_compute in T_afterN 100 Ev_vrB s_vrB R_vrB (P_grown).
Definition T_vrB3 : sstate := Eval vm_compute in LoV.renorm A_vrB3.
Definition is_vrB3 : wsub := Eval vm_compute in import_sub s_vrB 100 (P_grown) (ss_next Ev_vrB).
Definition tvT_vrB3 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_vrB (import_tv is_vrB3 tv_post).
Definition conts_vrB : list cdesc :=
  [(LoV.renorm_prog A_vrB1, (T_vrB1, (tvT_vrB1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrB LD.z0))));
   (LoV.renorm_prog A_vrB2, (T_vrB2, (tvT_vrB2, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrB LD.z0))));
   (LoV.renorm_prog A_vrB3, (T_vrB3, (tvT_vrB3, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrB LD.z0))))].
Lemma chk_vrB : site_check C_U LD.NP Pre_vr tv0 (AHead (SVar 99)) (PDAh PD_vr 99) 100 LoU.base_facts LD.is_txt
  Ev_vrB s_vrB (LoV.keptL slots_vrB) (LoV.passedL slots_vrB) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_vrB LD.z0) conts_vrB = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Section Exit.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segsU C_U.
Let JGv (tv : list (sv * sv)) (am : amode) : jpred := JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB tv am.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall J S rho (Q : assn),
  (Forall (holds rho) (ss_facts S) -> TR (SPJ segsU J S rho) Q) -> TR (SPJ segsU J S rho) Q.
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q : assn),
  (forall x, TR (SPJ segsU (J x) S rho) Q) -> TR (SPJ segsU (fun r t m => exists x, J x r t m) S rho) Q.
Hypothesis TR_pre : forall (P P' Q : assn), (forall w, P' w -> P w) -> TR P Q -> TR P' Q.
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
Hypothesis C_vrB : forall FBc rho1,
  TR (SPJ segsU (JGA_pre segsU C_U Kc ((fun _ : list (Z * Z) => P0_vr) FBc) FBc tv0 (AHead (SVar 99))) Pre_vr rho1)
     (LQP segsU 100 rho1 (PostsCA segsU C_U Kc (fun _ : list (Z * Z) => P0_vr) (PDAh PD_vr 99) FBc)).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_vrB1 : In (K_vrB1, (tvT_vrB1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrB LD.z0))) cutsE.
Hypothesis IN_vrB2 : In (T_vrB2, (tvT_vrB2, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrB LD.z0))) cutsE.
Hypothesis IN_vrB3 : In (T_vrB3, (tvT_vrB3, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrB LD.z0))) cutsE.
Lemma K_vrB1_of : forall rho w, SPJ segsU (JGv tvT_vrB1 LoU.amL) T_vrB1 rho w -> SPJ segsU (JGv tvT_vrB1 LoU.amL) K_vrB1 rho w.
Proof.
  intros rho w Hw. replace K_vrB1 with (add_facts (TobjJVx.nz_facts nz_vrB1) T_vrB1) by (vm_compute; reflexivity).
  apply SPJ_refacts_J; [exact Hw | vm_compute; reflexivity |].
  intros tr md HJ HF. eapply (TobjJVx.nz_facts_sound segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB (ss_facts T_vrB1) tvT_vrB1);
    [exact nzc_vrB1 | exact HF | eapply TobjJVAx.JGA_JG; exact HJ].
Qed.
Lemma L_E_vrB : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_vrB rho) (FAM (ameas (E_vrB, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_vrB LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_vrB, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_vrB LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_vrB LD.z0) rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_vrB rho w (permb_sound _ _ perm_vrB)).
    exact (SPJ_nsteps segsU _ ns_vrB rho E_vrB Ev_vrB w view_vrB Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) (fun _ : list (Z * Z) => P0_vr) Pre_vr
            tv0 (AHead (SVar 99)) (PDAh PD_vr 99) 100 eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            C_vrB (txt_extra_ok_U FB rho0))
           Ev_vrB s_vrB (LoV.keptL slots_vrB) (LoV.passedL slots_vrB) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_vrB LD.z0) conts_vrB rho _ chk_vrB).
  - intros ms R HF HP0 Hav HZ. cbn beta.
    eapply (HFD.P0_vr_of_tvz rho 110 112 4 R ms s_vrB); [vm_compute; reflexivity | vm_compute; reflexivity | | | lia].
    { eapply (LG.tvz_one rho _ _ HZ). apply in_or_app. right. left. reflexivity. }
    { eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto. }
  - intros c rho' Hc Hm. unfold conts_vrB in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { eapply TR_pre; [intros w Hw; exact (K_vrB1_of rho' w Hw) |].
      exact (REENTER K_vrB1 tvT_vrB1 LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_vrB LD.z0)) rho' _ IN_vrB1 Hm). }
    { exact (REENTER T_vrB2 tvT_vrB2 LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_vrB LD.z0)) rho' _ IN_vrB2 Hm). }
    { exact (REENTER T_vrB3 tvT_vrB3 LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_vrB LD.z0)) rho' _ IN_vrB3 Hm). }
Qed.
End Exit.

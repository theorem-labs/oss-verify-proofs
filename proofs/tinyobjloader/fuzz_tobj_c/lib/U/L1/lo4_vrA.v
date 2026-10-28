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

(* Call of vec_reserve (0x167f8) from 0x14470: a0 = the builder vector header at builder+216, a2 = allocator; 32-byte frame; it may grow that vector (slot 3). *)
Definition E_vrA : sstate := LoSite.E_vrA.
Definition vops_vrA : list LD.vop := [LD.VVec 216; LD.VDeep 32].
Definition ns_vrA : list nstep := Eval vm_compute in LoV.view_ns E_vrA vops_vrA.
Definition Ev_vrA : sstate := Eval vm_compute in LoV.view vops_vrA E_vrA.
Lemma view_vrA : run_nsteps E_vrA ns_vrA = Some Ev_vrA.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition slots_vrA : list nat := [3]%nat.
Lemma perm_vrA : permb LoU.tvL (LoV.keptL slots_vrA ++ LoV.passedL slots_vrA) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition x_vrA : wsub := [(99%positive, LD.pH); (19%positive, SAlu ALU_ADD LD.vDp (SLit 32))].
Definition s_vrA : wsub := Eval vm_compute in LoV.sOf Ev_vrA Pre_vr x_vrA.
Definition R_vrA : list sobj := Eval vm_compute in LoV.R_of Ev_vrA Pre_vr x_vrA.
Definition A_vrA1 : sstate := Eval vm_compute in T_afterN 100 Ev_vrA s_vrA R_vrA (P_keep).
Definition T_vrA1 : sstate := Eval vm_compute in LoV.renorm A_vrA1.
Definition is_vrA1 : wsub := Eval vm_compute in import_sub s_vrA 100 (P_keep) (ss_next Ev_vrA).
Definition tvT_vrA1 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_vrA (import_tv is_vrA1 tv0).
(* After the keep return the vector still has room for the wanted count >= 2, so its data pointer is non-null and the
   tracked-vector facts (4096 <= d, d + 4 cap <= hiA) hold: the return node carries them for the pointer checks that follow. *)
Definition nz_vrA1 : list (positive * Z * positive) := [(119%positive, 4, 121%positive)].
Lemma nzc_vrA1 : forallb (TobjJVx.nz_entry_check (ss_facts T_vrA1) tvT_vrA1) nz_vrA1 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition K_vrA1 : sstate := Eval vm_compute in add_facts (TobjJVx.nz_facts nz_vrA1) T_vrA1.
Definition A_vrA2 : sstate := Eval vm_compute in T_afterN 100 Ev_vrA s_vrA R_vrA (P_fail).
Definition T_vrA2 : sstate := Eval vm_compute in LoV.renorm A_vrA2.
Definition is_vrA2 : wsub := Eval vm_compute in import_sub s_vrA 100 (P_fail) (ss_next Ev_vrA).
Definition tvT_vrA2 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_vrA (import_tv is_vrA2 tv0).
Definition A_vrA3 : sstate := Eval vm_compute in T_afterN 100 Ev_vrA s_vrA R_vrA (P_grown).
Definition T_vrA3 : sstate := Eval vm_compute in LoV.renorm A_vrA3.
Definition is_vrA3 : wsub := Eval vm_compute in import_sub s_vrA 100 (P_grown) (ss_next Ev_vrA).
Definition tvT_vrA3 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_vrA (import_tv is_vrA3 tv_post).
Definition conts_vrA : list cdesc :=
  [(LoV.renorm_prog A_vrA1, (T_vrA1, (tvT_vrA1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrA LD.z0))));
   (LoV.renorm_prog A_vrA2, (T_vrA2, (tvT_vrA2, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrA LD.z0))));
   (LoV.renorm_prog A_vrA3, (T_vrA3, (tvT_vrA3, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrA LD.z0))))].
Lemma chk_vrA : site_check C_U LD.NP Pre_vr tv0 (AHead (SVar 99)) (PDAh PD_vr 99) 100 LoU.base_facts LD.is_txt
  Ev_vrA s_vrA (LoV.keptL slots_vrA) (LoV.passedL slots_vrA) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_vrA LD.z0) conts_vrA = true.
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
Hypothesis C_vrA : forall FBc rho1,
  TR (SPJ segsU (JGA_pre segsU C_U Kc ((fun _ : list (Z * Z) => P0_vr) FBc) FBc tv0 (AHead (SVar 99))) Pre_vr rho1)
     (LQP segsU 100 rho1 (PostsCA segsU C_U Kc (fun _ : list (Z * Z) => P0_vr) (PDAh PD_vr 99) FBc)).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_vrA1 : In (K_vrA1, (tvT_vrA1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrA LD.z0))) cutsE.
Hypothesis IN_vrA2 : In (T_vrA2, (tvT_vrA2, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrA LD.z0))) cutsE.
Hypothesis IN_vrA3 : In (T_vrA3, (tvT_vrA3, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrA LD.z0))) cutsE.
Lemma K_vrA1_of : forall rho w, SPJ segsU (JGv tvT_vrA1 LoU.amL) T_vrA1 rho w -> SPJ segsU (JGv tvT_vrA1 LoU.amL) K_vrA1 rho w.
Proof.
  intros rho w Hw. replace K_vrA1 with (add_facts (TobjJVx.nz_facts nz_vrA1) T_vrA1) by (vm_compute; reflexivity).
  apply SPJ_refacts_J; [exact Hw | vm_compute; reflexivity |].
  intros tr md HJ HF. eapply (TobjJVx.nz_facts_sound segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB (ss_facts T_vrA1) tvT_vrA1);
    [exact nzc_vrA1 | exact HF | eapply TobjJVAx.JGA_JG; exact HJ].
Qed.
Lemma L_E_vrA : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_vrA rho) (FAM (ameas (E_vrA, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_vrA LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_vrA, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_vrA LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_vrA LD.z0) rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_vrA rho w (permb_sound _ _ perm_vrA)).
    exact (SPJ_nsteps segsU _ ns_vrA rho E_vrA Ev_vrA w view_vrA Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) (fun _ : list (Z * Z) => P0_vr) Pre_vr
            tv0 (AHead (SVar 99)) (PDAh PD_vr 99) 100 eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            C_vrA (txt_extra_ok_U FB rho0))
           Ev_vrA s_vrA (LoV.keptL slots_vrA) (LoV.passedL slots_vrA) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_vrA LD.z0) conts_vrA rho _ chk_vrA).
  - intros ms R HF HP0 Hav HZ. cbn beta.
    eapply (HFD.P0_vr_of_tvz rho 119 121 4 R ms s_vrA); [vm_compute; reflexivity | vm_compute; reflexivity | | | lia].
    { eapply (LG.tvz_one rho _ _ HZ). apply in_or_app. right. left. reflexivity. }
    { eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto. }
  - intros c rho' Hc Hm. unfold conts_vrA in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { eapply TR_pre; [intros w Hw; exact (K_vrA1_of rho' w Hw) |].
      exact (REENTER K_vrA1 tvT_vrA1 LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_vrA LD.z0)) rho' _ IN_vrA1 Hm). }
    { exact (REENTER T_vrA2 tvT_vrA2 LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_vrA LD.z0)) rho' _ IN_vrA2 Hm). }
    { exact (REENTER T_vrA3 tvT_vrA3 LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_vrA LD.z0)) rho' _ IN_vrA3 Hm). }
Qed.
End Exit.

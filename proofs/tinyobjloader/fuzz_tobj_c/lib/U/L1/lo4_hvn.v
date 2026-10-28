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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require Import S_hvn.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module LG := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue.
Import HandleVnAddrU.

(* Call of handle_vn (0x1914c) from 0x142dc: a0 = builder, a1 = cursor; 48-byte frame; it may grow the normals vector (slot 2). *)
Definition E_hvn : sstate := LoSite.E_hvn.
Definition vops_hvn : list LD.vop := [LD.VDeep 48].
Definition ns_hvn : list nstep := Eval vm_compute in LoV.view_ns E_hvn vops_hvn.
Definition Ev_hvn : sstate := Eval vm_compute in LoV.view vops_hvn E_hvn.
Lemma view_hvn : run_nsteps E_hvn ns_hvn = Some Ev_hvn.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition slots_hvn : list nat := [2]%nat.
Lemma perm_hvn : permb LoU.tvL (LoV.keptL slots_hvn ++ LoV.passedL slots_hvn) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition x_hvn : wsub := [(99%positive, LD.pH)].
Definition s_hvn : wsub := Eval vm_compute in LoV.sOf Ev_hvn Pre_hvn_U x_hvn.
Definition R_hvn : list sobj := Eval vm_compute in LoV.R_of Ev_hvn Pre_hvn_U x_hvn.
Definition A_hvn1 : sstate := Eval vm_compute in T_afterN 100 Ev_hvn s_hvn R_hvn (P_ret_U hvnU_ret1).
Definition T_hvn1 : sstate := Eval vm_compute in LoV.renorm A_hvn1.
Definition is_hvn1 : wsub := Eval vm_compute in import_sub s_hvn 100 (P_ret_U hvnU_ret1) (ss_next Ev_hvn).
Definition tvT_hvn1 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_hvn (import_tv is_hvn1 HV.tvP).
Definition A_hvn2 : sstate := Eval vm_compute in T_afterN 100 Ev_hvn s_hvn R_hvn (P_ret_U hvnU_ret2).
Definition T_hvn2 : sstate := Eval vm_compute in LoV.renorm A_hvn2.
Definition is_hvn2 : wsub := Eval vm_compute in import_sub s_hvn 100 (P_ret_U hvnU_ret2) (ss_next Ev_hvn).
Definition tvT_hvn2 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_hvn (import_tv is_hvn2 HV.tvP).
Definition A_hvn3 : sstate := Eval vm_compute in T_afterN 100 Ev_hvn s_hvn R_hvn (P_ret_U hvnU_ret3).
Definition T_hvn3 : sstate := Eval vm_compute in LoV.renorm A_hvn3.
Definition is_hvn3 : wsub := Eval vm_compute in import_sub s_hvn 100 (P_ret_U hvnU_ret3) (ss_next Ev_hvn).
Definition tvT_hvn3 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_hvn (import_tv is_hvn3 HV.tvP).
Definition conts_hvn : list cdesc :=
  [(LoV.renorm_prog A_hvn1, (T_hvn1, (tvT_hvn1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hvn LD.z0))));
   (LoV.renorm_prog A_hvn2, (T_hvn2, (tvT_hvn2, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hvn LD.z0))));
   (LoV.renorm_prog A_hvn3, (T_hvn3, (tvT_hvn3, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hvn LD.z0))))].
Lemma chk_hvn : site_check C_U LD.NP Pre_hvn_U HV.tv0 (AHead (SVar 99)) (PDAh PD_hvn_U 99) 100 LoU.base_facts LD.is_txt
  Ev_hvn s_hvn (LoV.keptL slots_hvn) (LoV.passedL slots_hvn) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_hvn LD.z0) conts_hvn = true.
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
Hypothesis C_hvn : forall FBc rho1,
  TR (SPJ segsU (JGA_pre segsU C_U Kc (HV.P0_hvn FBc) FBc HV.tv0 (AHead (SVar 99))) Pre_hvn_U rho1)
     (LQP segsU 100 rho1 (PostsCA segsU C_U Kc HV.P0_hvn (PDAh PD_hvn_U 99) FBc)).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_hvn1 : In (T_hvn1, (tvT_hvn1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hvn LD.z0))) cutsE.
Hypothesis IN_hvn2 : In (T_hvn2, (tvT_hvn2, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hvn LD.z0))) cutsE.
Hypothesis IN_hvn3 : In (T_hvn3, (tvT_hvn3, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hvn LD.z0))) cutsE.
Lemma L_E_hvn : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_hvn rho) (FAM (ameas (E_hvn, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_hvn LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_hvn, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_hvn LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_hvn LD.z0) rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_hvn rho w (permb_sound _ _ perm_hvn)).
    exact (SPJ_nsteps segsU _ ns_hvn rho E_hvn Ev_hvn w view_hvn Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) HV.P0_hvn Pre_hvn_U
            HV.tv0 (AHead (SVar 99)) (PDAh PD_hvn_U 99) 100 eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            C_hvn (txt_extra_ok_U FB rho0))
           Ev_hvn s_hvn (LoV.keptL slots_hvn) (LoV.passedL slots_hvn) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_hvn LD.z0) conts_hvn rho _ chk_hvn).
  - intros ms R HF HP0 Hav HZ. change (HV.P0_hvn ?F ?r) with (LG.P0txt 18 15 F r).
    apply (LG.P0_txt_call FB rho0 rho 18 15 _ R ms s_hvn); [vm_compute; reflexivity | vm_compute; reflexivity | exact HP0 | exact Hav].
  - intros c rho' Hc Hm. unfold conts_hvn in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { exact (REENTER T_hvn1 tvT_hvn1 LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_hvn LD.z0)) rho' _ IN_hvn1 Hm). }
    { exact (REENTER T_hvn2 tvT_hvn2 LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_hvn LD.z0)) rho' _ IN_hvn2 Hm). }
    { exact (REENTER T_hvn3 tvT_hvn3 LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_hvn LD.z0)) rho' _ IN_hvn3 Hm). }
Qed.
End Exit.

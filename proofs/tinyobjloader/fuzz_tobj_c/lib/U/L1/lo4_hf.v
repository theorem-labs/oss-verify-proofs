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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L12 Require Import S_hl S_hp.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Module LG := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue.

(* Call of handle_f (0x19308) from 0x1439c: a0 = builder, a1 = cursor; 272-byte frame; it may grow the face vectors (slots 0, 7-10, 14-17). *)
Definition E_hf : sstate := LoSite.E_hf.
Definition vops_hf : list LD.vop := [LD.VDeep 272].
Definition ns_hf : list nstep := Eval vm_compute in LoV.view_ns E_hf vops_hf.
Definition Ev_hf : sstate := Eval vm_compute in LoV.view vops_hf E_hf.
Lemma view_hf : run_nsteps E_hf ns_hf = Some Ev_hf.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition slots_hf : list nat := [0; 7; 8; 9; 10; 14; 15; 16; 17]%nat.
Lemma perm_hf : permb LoU.tvL (LoV.keptL slots_hf ++ LoV.passedL slots_hf) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition x_hf : wsub := [(299%positive, LD.pH)].
Definition s_hf : wsub := Eval vm_compute in LoV.sOf Ev_hf (Pre_hf HF_U) x_hf.
Definition R_hf : list sobj := Eval vm_compute in LoV.R_of Ev_hf (Pre_hf HF_U) x_hf.
Definition A_hf1 : sstate := Eval vm_compute in T_afterN 300 Ev_hf s_hf R_hf (HP_ret HF_U).
Definition T_hf1 : sstate := Eval vm_compute in LoV.renorm A_hf1.
Definition is_hf1 : wsub := Eval vm_compute in import_sub s_hf 300 (HP_ret HF_U) (ss_next Ev_hf).
Definition tvT_hf1 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_hf (import_tv is_hf1 tvH).
Definition A_hf2 : sstate := Eval vm_compute in T_afterN 300 Ev_hf s_hf R_hf (HP_degen HF_U).
Definition T_hf2 : sstate := Eval vm_compute in LoV.renorm A_hf2.
Definition is_hf2 : wsub := Eval vm_compute in import_sub s_hf 300 (HP_degen HF_U) (ss_next Ev_hf).
Definition tvT_hf2 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_hf (import_tv is_hf2 tvH).
Definition conts_hf : list cdesc :=
  [(LoV.renorm_prog A_hf1, (T_hf1, (tvT_hf1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hf LD.z0))));
   (LoV.renorm_prog A_hf2, (T_hf2, (tvT_hf2, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hf LD.z0))))].
Lemma chk_hf : site_check C_U LD.NP (Pre_hf HF_U) tv_pre (AHead (SVar 299)) (PDAh PD_hf_U 299) 300 LoU.base_facts LD.is_txt
  Ev_hf s_hf (LoV.keptL slots_hf) (LoV.passedL slots_hf) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_hf LD.z0) conts_hf = true.
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
Hypothesis C_hf : forall FBc rho1,
  TR (SPJ segsU (JGA_pre segsU C_U Kc (P0_hf FBc) FBc tv_pre (AHead (SVar 299))) (Pre_hf HF_U) rho1)
     (LQP segsU 300 rho1 (PostsCA segsU C_U Kc P0_hf (PDAh PD_hf_U 299) FBc)).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_hf1 : In (T_hf1, (tvT_hf1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hf LD.z0))) cutsE.
Hypothesis IN_hf2 : In (T_hf2, (tvT_hf2, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hf LD.z0))) cutsE.
Lemma L_E_hf : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_hf rho) (FAM (ameas (E_hf, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_hf LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_hf, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_hf LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_hf LD.z0) rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_hf rho w (permb_sound _ _ perm_hf)).
    exact (SPJ_nsteps segsU _ ns_hf rho E_hf Ev_hf w view_hf Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) P0_hf (Pre_hf HF_U)
            tv_pre (AHead (SVar 299)) (PDAh PD_hf_U 299) 300 eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            C_hf (txt_extra_ok_U FB rho0))
           Ev_hf s_hf (LoV.keptL slots_hf) (LoV.passedL slots_hf) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_hf LD.z0) conts_hf rho _ chk_hf).
  - intros ms R HF HP0 Hav HZ. change (P0_hf ?F ?r) with (LG.P0txt 101 100 F r).
    apply (LG.P0_txt_call FB rho0 rho 101 100 _ R ms s_hf); [vm_compute; reflexivity | vm_compute; reflexivity | exact HP0 | exact Hav].
  - intros c rho' Hc Hm. unfold conts_hf in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { exact (REENTER T_hf1 tvT_hf1 LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_hf LD.z0)) rho' _ IN_hf1 Hm). }
    { exact (REENTER T_hf2 tvT_hf2 LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_hf LD.z0)) rho' _ IN_hf2 Hm). }
Qed.
End Exit.

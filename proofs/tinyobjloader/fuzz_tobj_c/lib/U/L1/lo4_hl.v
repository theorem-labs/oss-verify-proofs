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

(* Call of handle_l (0x19f68) from 0x14364: a0 = builder, a1 = cursor; 128-byte frame; it may grow the line-index and line-count vectors (slots 11, 12). *)
Definition E_hl : sstate := LoSite.E_hl.
Definition vops_hl : list LD.vop := [LD.VDeep 128].
Definition ns_hl : list nstep := Eval vm_compute in LoV.view_ns E_hl vops_hl.
Definition Ev_hl : sstate := Eval vm_compute in LoV.view vops_hl E_hl.
Lemma view_hl : run_nsteps E_hl ns_hl = Some Ev_hl.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition slots_hl : list nat := [11; 12]%nat.
Lemma perm_hl : permb LoU.tvL (LoV.keptL slots_hl ++ LoV.passedL slots_hl) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition x_hl : wsub := [(299%positive, LD.pH)].
Definition s_hl : wsub := Eval vm_compute in LoV.sOf Ev_hl Pre_hl_U x_hl.
Definition R_hl : list sobj := Eval vm_compute in LoV.R_of Ev_hl Pre_hl_U x_hl.
Definition A_hl1 : sstate := Eval vm_compute in T_afterN 300 Ev_hl s_hl R_hl (HLP_ret_U).
Definition T_hl1 : sstate := Eval vm_compute in LoV.renorm A_hl1.
Definition is_hl1 : wsub := Eval vm_compute in import_sub s_hl 300 (HLP_ret_U) (ss_next Ev_hl).
Definition tvT_hl1 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_hl (import_tv is_hl1 LP.tvL).
Definition conts_hl : list cdesc :=
  [(LoV.renorm_prog A_hl1, (T_hl1, (tvT_hl1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hl LD.z0))))].
Lemma chk_hl : site_check C_U LD.NP Pre_hl_U LP.tvL_pre (AHead (SVar 299)) (PDAh PD_hl_U 299) 300 LoU.base_facts LD.is_txt
  Ev_hl s_hl (LoV.keptL slots_hl) (LoV.passedL slots_hl) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_hl LD.z0) conts_hl = true.
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
Hypothesis C_hl : forall FBc rho1,
  TR (SPJ segsU (JGA_pre segsU C_U Kc (P0_hf FBc) FBc LP.tvL_pre (AHead (SVar 299))) Pre_hl_U rho1)
     (LQP segsU 300 rho1 (PostsCA segsU C_U Kc P0_hf (PDAh PD_hl_U 299) FBc)).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_hl1 : In (T_hl1, (tvT_hl1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hl LD.z0))) cutsE.
Lemma L_E_hl : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_hl rho) (FAM (ameas (E_hl, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_hl LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_hl, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_hl LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_hl LD.z0) rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_hl rho w (permb_sound _ _ perm_hl)).
    exact (SPJ_nsteps segsU _ ns_hl rho E_hl Ev_hl w view_hl Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) P0_hf Pre_hl_U
            LP.tvL_pre (AHead (SVar 299)) (PDAh PD_hl_U 299) 300 eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            C_hl (txt_extra_ok_U FB rho0))
           Ev_hl s_hl (LoV.keptL slots_hl) (LoV.passedL slots_hl) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_hl LD.z0) conts_hl rho _ chk_hl).
  - intros ms R HF HP0 Hav HZ. change (P0_hf ?F ?r) with (LG.P0txt 101 100 F r).
    apply (LG.P0_txt_call FB rho0 rho 101 100 _ R ms s_hl); [vm_compute; reflexivity | vm_compute; reflexivity | exact HP0 | exact Hav].
  - intros c rho' Hc Hm. unfold conts_hl in Hc. cbn [In] in Hc. destruct Hc as [<-|[]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { exact (REENTER T_hl1 tvT_hl1 LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_hl LD.z0)) rho' _ IN_hl1 Hm). }
Qed.
End Exit.

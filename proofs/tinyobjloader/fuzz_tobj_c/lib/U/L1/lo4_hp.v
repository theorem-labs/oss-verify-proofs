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

(* Call of handle_p (0x1a298) from 0x1438c: a0 = builder, a1 = cursor; 112-byte frame; it may grow the point-index vector (slot 13). *)
Definition E_hp : sstate := LoSite.E_hp.
Definition vops_hp : list LD.vop := [LD.VDeep 112].
Definition ns_hp : list nstep := Eval vm_compute in LoV.view_ns E_hp vops_hp.
Definition Ev_hp : sstate := Eval vm_compute in LoV.view vops_hp E_hp.
Lemma view_hp : run_nsteps E_hp ns_hp = Some Ev_hp.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition slots_hp : list nat := [13]%nat.
Lemma perm_hp : permb LoU.tvL (LoV.keptL slots_hp ++ LoV.passedL slots_hp) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition x_hp : wsub := [(299%positive, LD.pH)].
Definition s_hp : wsub := Eval vm_compute in LoV.sOf Ev_hp Pre_hp_U x_hp.
Definition R_hp : list sobj := Eval vm_compute in LoV.R_of Ev_hp Pre_hp_U x_hp.
Definition A_hp1 : sstate := Eval vm_compute in T_afterN 300 Ev_hp s_hp R_hp (HPP_ret_U).
Definition T_hp1 : sstate := Eval vm_compute in LoV.renorm A_hp1.
Definition is_hp1 : wsub := Eval vm_compute in import_sub s_hp 300 (HPP_ret_U) (ss_next Ev_hp).
Definition tvT_hp1 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_hp (import_tv is_hp1 LP.tvP).
Definition conts_hp : list cdesc :=
  [(LoV.renorm_prog A_hp1, (T_hp1, (tvT_hp1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hp LD.z0))))].
Lemma chk_hp : site_check C_U LD.NP Pre_hp_U LP.tvP_pre (AHead (SVar 299)) (PDAh PD_hp_U 299) 300 LoU.base_facts LD.is_txt
  Ev_hp s_hp (LoV.keptL slots_hp) (LoV.passedL slots_hp) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_hp LD.z0) conts_hp = true.
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
Hypothesis C_hp : forall FBc rho1,
  TR (SPJ segsU (JGA_pre segsU C_U Kc (P0_hf FBc) FBc LP.tvP_pre (AHead (SVar 299))) Pre_hp_U rho1)
     (LQP segsU 300 rho1 (PostsCA segsU C_U Kc P0_hf (PDAh PD_hp_U 299) FBc)).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_hp1 : In (T_hp1, (tvT_hp1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hp LD.z0))) cutsE.
Lemma L_E_hp : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_hp rho) (FAM (ameas (E_hp, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_hp LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_hp, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_hp LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_hp LD.z0) rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_hp rho w (permb_sound _ _ perm_hp)).
    exact (SPJ_nsteps segsU _ ns_hp rho E_hp Ev_hp w view_hp Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) P0_hf Pre_hp_U
            LP.tvP_pre (AHead (SVar 299)) (PDAh PD_hp_U 299) 300 eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            C_hp (txt_extra_ok_U FB rho0))
           Ev_hp s_hp (LoV.keptL slots_hp) (LoV.passedL slots_hp) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_hp LD.z0) conts_hp rho _ chk_hp).
  - intros ms R HF HP0 Hav HZ. change (P0_hf ?F ?r) with (LG.P0txt 101 100 F r).
    apply (LG.P0_txt_call FB rho0 rho 101 100 _ R ms s_hp); [vm_compute; reflexivity | vm_compute; reflexivity | exact HP0 | exact Hav].
  - intros c rho' Hc Hm. unfold conts_hp in Hc. cbn [In] in Hc. destruct Hc as [<-|[]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { exact (REENTER T_hp1 tvT_hp1 LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_hp LD.z0)) rho' _ IN_hp1 Hm). }
Qed.
End Exit.

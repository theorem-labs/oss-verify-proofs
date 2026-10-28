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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require Import S_ml.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.


(* Call of handle_mtllib (0x1a6b4) from 0x14844: a0 = builder, config object; 112-byte frame; it ends through diag_append's return. *)
Definition E_ml : sstate := LoSite.E_ml.
Definition vops_ml : list LD.vop := [LD.VDeep 112].
Definition ns_ml : list nstep := Eval vm_compute in LoV.view_ns E_ml vops_ml.
Definition Ev_ml : sstate := Eval vm_compute in LoV.view vops_ml E_ml.
Lemma view_ml : run_nsteps E_ml ns_ml = Some Ev_ml.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition x_ml : wsub := [].
Definition s_ml : wsub := Eval vm_compute in LoV.sOf Ev_ml Pre_ml x_ml.
Definition R_ml : list sobj := Eval vm_compute in LoV.R_of Ev_ml Pre_ml x_ml.
Definition I_ml1 : sstate := Eval vm_compute in add_facts (ss_facts Ev_ml) (import_post s_ml (ss_next Pre_ml) (lf_state (nth 0 Posts_ml (mkLeaf Pre_ml RsSymJump))) (ss_next Ev_ml) R_ml).
Definition T_ml1 : sstate := Eval vm_compute in LoV.renorm I_ml1.
Definition conts_ml : list (list nstep * aedesc) :=
  [(LoV.renorm_prog I_ml1, (T_ml1, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_ml LD.z0))))].
Lemma chk_ml : pure_site_check LD.NP Pre_ml Posts_ml LoU.base_facts Ev_ml s_ml LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_ml LD.z0) conts_ml = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.pure_site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

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
Hypothesis TR_pre : forall (P P' Q : assn), (forall w, P' w -> P w) -> TR P Q -> TR P' Q.
Hypothesis TR_callJ : forall (J Jp Jp' Jc' : jpred) (C0 Pre : sstate) (s : wsub) (R : list sobj) (Posts : list leaf) (Q : assn) (rho : valuation),
  entails_fr C0 Pre s = Some R -> call_check C0 Pre s R Posts = true ->
  (forall rho1, TR (SPJ segsU Jp Pre rho1) (LQJ segsU Jp' (ss_next Pre) rho1 Posts)) ->
  (forall tr ms md, smatch segsU rho C0 (tr, {| cfg_ms := ms; cfg_model := md |}) -> J rho tr md -> Jp (rho_sub (rho_absorb rho R ms) s) tr md) ->
  (forall L rho' rhoL tr ms md tr' md', In L Posts -> smatch segsU rho C0 (tr, {| cfg_ms := ms; cfg_model := md |}) -> J rho tr md ->
     call_link rho ms R s Pre C0 (lf_state L) rho' rhoL -> Jp' rhoL tr' md' -> Jc' rho' tr' md') ->
  (forall L rho', In L Posts -> agree_below (ss_next C0) rho rho' ->
     TR (SPJ segsU Jc' (import_post s (ss_next Pre) (lf_state L) (ss_next C0) R) rho') Q) ->
  TR (SPJ segsU J C0 rho) Q.
Hypothesis C_ml : forall tv am rho rho1,
  TR (SP segsU (fun tr md => JGv tv am rho tr md) Pre_ml rho1) (LQ segsU (fun tr md => JGv tv am rho tr md) (ss_next Pre_ml) rho1 Posts_ml).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_ml1 : In (T_ml1, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_ml LD.z0))) cutsE.
Lemma L_E_ml : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_ml rho) (FAM (ameas (E_ml, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_ml LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_ml, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_ml LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_ml LD.z0) rho).
  eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segsU _ ns_ml rho E_ml Ev_ml w view_ml Hw). }
  apply ((pure_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML Pre_ml Posts_ml LoU.base_facts TR TR_facts TR_pre TR_callJ C_ml)
           Ev_ml s_ml LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_ml LD.z0) conts_ml rho _ chk_ml).
  intros c rho' Hc Hm. unfold conts_ml in Hc. cbn [In] in Hc. destruct Hc as [<-|[]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
  { exact (REENTER T_ml1 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_ml LD.z0)) rho' _ IN_ml1 Hm). }
Qed.
End Exit.

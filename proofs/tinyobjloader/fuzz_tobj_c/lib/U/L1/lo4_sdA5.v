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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10 Require Import S_sd.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.


(* Call of scan_double (0x183d0) from 0x141d4: a0 = cursor, a1 = token end, a2 = the double local at sp+1656; 16-byte frame. *)
Definition E_sdA5 : sstate := LoSite.E_sdA5.
Definition vops_sdA5 : list LD.vop := [LD.VCarve (1656 - LoU.FR) 8; LD.VDeep 16].
Definition ns_sdA5 : list nstep := Eval vm_compute in LoV.view_ns E_sdA5 vops_sdA5.
Definition Ev_sdA5 : sstate := Eval vm_compute in LoV.view vops_sdA5 E_sdA5.
Lemma view_sdA5 : run_nsteps E_sdA5 ns_sdA5 = Some Ev_sdA5.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition x_sdA5 : wsub := [].
Definition s_sdA5 : wsub := Eval vm_compute in LoV.sOf Ev_sdA5 Pre_sd_U x_sdA5.
Definition R_sdA5 : list sobj := Eval vm_compute in LoV.R_of Ev_sdA5 Pre_sd_U x_sdA5.
Definition I_sdA51 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdA5) (import_post s_sdA5 (ss_next Pre_sd_U) (lf_state (nth 0 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdA5) R_sdA5).
Definition T_sdA51 : sstate := Eval vm_compute in LoV.renorm I_sdA51.
Definition I_sdA52 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdA5) (import_post s_sdA5 (ss_next Pre_sd_U) (lf_state (nth 1 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdA5) R_sdA5).
Definition T_sdA52 : sstate := Eval vm_compute in LoV.renorm I_sdA52.
Definition I_sdA53 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdA5) (import_post s_sdA5 (ss_next Pre_sd_U) (lf_state (nth 2 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdA5) R_sdA5).
Definition T_sdA53 : sstate := Eval vm_compute in LoV.renorm I_sdA53.
Definition I_sdA54 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdA5) (import_post s_sdA5 (ss_next Pre_sd_U) (lf_state (nth 3 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdA5) R_sdA5).
Definition T_sdA54 : sstate := Eval vm_compute in LoV.renorm I_sdA54.
Definition conts_sdA5 : list (list nstep * aedesc) :=
  [(LoV.renorm_prog I_sdA51, (T_sdA51, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0))));
   (LoV.renorm_prog I_sdA52, (T_sdA52, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0))));
   (LoV.renorm_prog I_sdA53, (T_sdA53, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0))));
   (LoV.renorm_prog I_sdA54, (T_sdA54, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0))))].
Lemma chk_sdA5 : pure_site_check LD.NP Pre_sd_U Posts_sd_U LoU.base_facts Ev_sdA5 s_sdA5 LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_sdA5 LD.z0) conts_sdA5 = true.
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
Hypothesis C_sdA5 : forall tv am rho rho1,
  TR (SP segsU (fun tr md => JGv tv am rho tr md) Pre_sd_U rho1) (LQ segsU (fun tr md => JGv tv am rho tr md) (ss_next Pre_sd_U) rho1 Posts_sd_U).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_sdA51 : In (T_sdA51, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0))) cutsE.
Hypothesis IN_sdA52 : In (T_sdA52, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0))) cutsE.
Hypothesis IN_sdA53 : In (T_sdA53, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0))) cutsE.
Hypothesis IN_sdA54 : In (T_sdA54, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0))) cutsE.
Lemma L_E_sdA5 : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_sdA5 rho) (FAM (ameas (E_sdA5, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdA5 LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_sdA5, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdA5 LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_sdA5 LD.z0) rho).
  eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segsU _ ns_sdA5 rho E_sdA5 Ev_sdA5 w view_sdA5 Hw). }
  apply ((pure_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML Pre_sd_U Posts_sd_U LoU.base_facts TR TR_facts TR_pre TR_callJ C_sdA5)
           Ev_sdA5 s_sdA5 LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_sdA5 LD.z0) conts_sdA5 rho _ chk_sdA5).
  intros c rho' Hc Hm. unfold conts_sdA5 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
  { exact (REENTER T_sdA51 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0)) rho' _ IN_sdA51 Hm). }
  { exact (REENTER T_sdA52 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0)) rho' _ IN_sdA52 Hm). }
  { exact (REENTER T_sdA53 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0)) rho' _ IN_sdA53 Hm). }
  { exact (REENTER T_sdA54 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0)) rho' _ IN_sdA54 Hm). }
Qed.
End Exit.

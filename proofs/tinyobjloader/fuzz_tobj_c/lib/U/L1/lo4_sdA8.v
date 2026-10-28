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


(* Call of scan_double (0x183d0) from 0x14234: a0 = cursor, a1 = token end, a2 = the double local at sp+1656; 16-byte frame. *)
Definition E_sdA8 : sstate := LoSite.E_sdA8.
Definition vops_sdA8 : list LD.vop := [LD.VCarve (1656 - LoU.FR) 8; LD.VDeep 16].
Definition ns_sdA8 : list nstep := Eval vm_compute in LoV.view_ns E_sdA8 vops_sdA8.
Definition Ev_sdA8 : sstate := Eval vm_compute in LoV.view vops_sdA8 E_sdA8.
Lemma view_sdA8 : run_nsteps E_sdA8 ns_sdA8 = Some Ev_sdA8.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition x_sdA8 : wsub := [].
Definition s_sdA8 : wsub := Eval vm_compute in LoV.sOf Ev_sdA8 Pre_sd_U x_sdA8.
Definition R_sdA8 : list sobj := Eval vm_compute in LoV.R_of Ev_sdA8 Pre_sd_U x_sdA8.
Definition I_sdA81 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdA8) (import_post s_sdA8 (ss_next Pre_sd_U) (lf_state (nth 0 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdA8) R_sdA8).
Definition T_sdA81 : sstate := Eval vm_compute in LoV.renorm I_sdA81.
Definition I_sdA82 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdA8) (import_post s_sdA8 (ss_next Pre_sd_U) (lf_state (nth 1 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdA8) R_sdA8).
Definition T_sdA82 : sstate := Eval vm_compute in LoV.renorm I_sdA82.
Definition I_sdA83 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdA8) (import_post s_sdA8 (ss_next Pre_sd_U) (lf_state (nth 2 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdA8) R_sdA8).
Definition T_sdA83 : sstate := Eval vm_compute in LoV.renorm I_sdA83.
Definition I_sdA84 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdA8) (import_post s_sdA8 (ss_next Pre_sd_U) (lf_state (nth 3 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdA8) R_sdA8).
Definition T_sdA84 : sstate := Eval vm_compute in LoV.renorm I_sdA84.
Definition conts_sdA8 : list (list nstep * aedesc) :=
  [(LoV.renorm_prog I_sdA81, (T_sdA81, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0))));
   (LoV.renorm_prog I_sdA82, (T_sdA82, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0))));
   (LoV.renorm_prog I_sdA83, (T_sdA83, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0))));
   (LoV.renorm_prog I_sdA84, (T_sdA84, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0))))].
Lemma chk_sdA8 : pure_site_check LD.NP Pre_sd_U Posts_sd_U LoU.base_facts Ev_sdA8 s_sdA8 LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_sdA8 LD.z0) conts_sdA8 = true.
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
Hypothesis C_sdA8 : forall tv am rho rho1,
  TR (SP segsU (fun tr md => JGv tv am rho tr md) Pre_sd_U rho1) (LQ segsU (fun tr md => JGv tv am rho tr md) (ss_next Pre_sd_U) rho1 Posts_sd_U).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_sdA81 : In (T_sdA81, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0))) cutsE.
Hypothesis IN_sdA82 : In (T_sdA82, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0))) cutsE.
Hypothesis IN_sdA83 : In (T_sdA83, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0))) cutsE.
Hypothesis IN_sdA84 : In (T_sdA84, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0))) cutsE.
Lemma L_E_sdA8 : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_sdA8 rho) (FAM (ameas (E_sdA8, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdA8 LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_sdA8, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdA8 LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_sdA8 LD.z0) rho).
  eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segsU _ ns_sdA8 rho E_sdA8 Ev_sdA8 w view_sdA8 Hw). }
  apply ((pure_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML Pre_sd_U Posts_sd_U LoU.base_facts TR TR_facts TR_pre TR_callJ C_sdA8)
           Ev_sdA8 s_sdA8 LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_sdA8 LD.z0) conts_sdA8 rho _ chk_sdA8).
  intros c rho' Hc Hm. unfold conts_sdA8 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
  { exact (REENTER T_sdA81 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0)) rho' _ IN_sdA81 Hm). }
  { exact (REENTER T_sdA82 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0)) rho' _ IN_sdA82 Hm). }
  { exact (REENTER T_sdA83 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0)) rho' _ IN_sdA83 Hm). }
  { exact (REENTER T_sdA84 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0)) rho' _ IN_sdA84 Hm). }
Qed.
End Exit.

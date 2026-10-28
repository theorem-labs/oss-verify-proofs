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


(* Call of scan_double (0x183d0) from 0x14194: a0 = cursor, a1 = token end, a2 = the double local at sp+1656; 16-byte frame. *)
Definition E_sdA3 : sstate := LoSite.E_sdA3.
Definition vops_sdA3 : list LD.vop := [LD.VCarve (1656 - LoU.FR) 8; LD.VDeep 16].
Definition ns_sdA3 : list nstep := Eval vm_compute in LoV.view_ns E_sdA3 vops_sdA3.
Definition Ev_sdA3 : sstate := Eval vm_compute in LoV.view vops_sdA3 E_sdA3.
Lemma view_sdA3 : run_nsteps E_sdA3 ns_sdA3 = Some Ev_sdA3.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition x_sdA3 : wsub := [].
Definition s_sdA3 : wsub := Eval vm_compute in LoV.sOf Ev_sdA3 Pre_sd_U x_sdA3.
Definition R_sdA3 : list sobj := Eval vm_compute in LoV.R_of Ev_sdA3 Pre_sd_U x_sdA3.
Definition I_sdA31 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdA3) (import_post s_sdA3 (ss_next Pre_sd_U) (lf_state (nth 0 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdA3) R_sdA3).
Definition T_sdA31 : sstate := Eval vm_compute in LoV.renorm I_sdA31.
Definition I_sdA32 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdA3) (import_post s_sdA3 (ss_next Pre_sd_U) (lf_state (nth 1 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdA3) R_sdA3).
Definition T_sdA32 : sstate := Eval vm_compute in LoV.renorm I_sdA32.
Definition I_sdA33 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdA3) (import_post s_sdA3 (ss_next Pre_sd_U) (lf_state (nth 2 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdA3) R_sdA3).
Definition T_sdA33 : sstate := Eval vm_compute in LoV.renorm I_sdA33.
Definition I_sdA34 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdA3) (import_post s_sdA3 (ss_next Pre_sd_U) (lf_state (nth 3 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdA3) R_sdA3).
Definition T_sdA34 : sstate := Eval vm_compute in LoV.renorm I_sdA34.
Definition conts_sdA3 : list (list nstep * aedesc) :=
  [(LoV.renorm_prog I_sdA31, (T_sdA31, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0))));
   (LoV.renorm_prog I_sdA32, (T_sdA32, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0))));
   (LoV.renorm_prog I_sdA33, (T_sdA33, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0))));
   (LoV.renorm_prog I_sdA34, (T_sdA34, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0))))].
Lemma chk_sdA3 : pure_site_check LD.NP Pre_sd_U Posts_sd_U LoU.base_facts Ev_sdA3 s_sdA3 LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_sdA3 LD.z0) conts_sdA3 = true.
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
Hypothesis C_sdA3 : forall tv am rho rho1,
  TR (SP segsU (fun tr md => JGv tv am rho tr md) Pre_sd_U rho1) (LQ segsU (fun tr md => JGv tv am rho tr md) (ss_next Pre_sd_U) rho1 Posts_sd_U).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_sdA31 : In (T_sdA31, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0))) cutsE.
Hypothesis IN_sdA32 : In (T_sdA32, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0))) cutsE.
Hypothesis IN_sdA33 : In (T_sdA33, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0))) cutsE.
Hypothesis IN_sdA34 : In (T_sdA34, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0))) cutsE.
Lemma L_E_sdA3 : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_sdA3 rho) (FAM (ameas (E_sdA3, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdA3 LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_sdA3, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdA3 LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_sdA3 LD.z0) rho).
  eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segsU _ ns_sdA3 rho E_sdA3 Ev_sdA3 w view_sdA3 Hw). }
  apply ((pure_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML Pre_sd_U Posts_sd_U LoU.base_facts TR TR_facts TR_pre TR_callJ C_sdA3)
           Ev_sdA3 s_sdA3 LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_sdA3 LD.z0) conts_sdA3 rho _ chk_sdA3).
  intros c rho' Hc Hm. unfold conts_sdA3 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
  { exact (REENTER T_sdA31 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0)) rho' _ IN_sdA31 Hm). }
  { exact (REENTER T_sdA32 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0)) rho' _ IN_sdA32 Hm). }
  { exact (REENTER T_sdA33 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0)) rho' _ IN_sdA33 Hm). }
  { exact (REENTER T_sdA34 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0)) rho' _ IN_sdA34 Hm). }
Qed.
End Exit.

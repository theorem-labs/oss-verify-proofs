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


(* Call of scan_double (0x183d0) from 0x14444: a0 = cursor, a1 = token end, a2 = the double local at sp+1672; 16-byte frame. *)
Definition E_sdB2 : sstate := LoSite.E_sdB2.
Definition vops_sdB2 : list LD.vop := [LD.VCarve (1672 - LoU.FR) 8; LD.VDeep 16].
Definition ns_sdB2 : list nstep := Eval vm_compute in LoV.view_ns E_sdB2 vops_sdB2.
Definition Ev_sdB2 : sstate := Eval vm_compute in LoV.view vops_sdB2 E_sdB2.
Lemma view_sdB2 : run_nsteps E_sdB2 ns_sdB2 = Some Ev_sdB2.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition x_sdB2 : wsub := [].
Definition s_sdB2 : wsub := Eval vm_compute in LoV.sOf Ev_sdB2 Pre_sd_U x_sdB2.
Definition R_sdB2 : list sobj := Eval vm_compute in LoV.R_of Ev_sdB2 Pre_sd_U x_sdB2.
Definition I_sdB21 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdB2) (import_post s_sdB2 (ss_next Pre_sd_U) (lf_state (nth 0 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdB2) R_sdB2).
Definition T_sdB21 : sstate := Eval vm_compute in LoV.renorm I_sdB21.
Definition I_sdB22 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdB2) (import_post s_sdB2 (ss_next Pre_sd_U) (lf_state (nth 1 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdB2) R_sdB2).
Definition T_sdB22 : sstate := Eval vm_compute in LoV.renorm I_sdB22.
Definition I_sdB23 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdB2) (import_post s_sdB2 (ss_next Pre_sd_U) (lf_state (nth 2 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdB2) R_sdB2).
Definition T_sdB23 : sstate := Eval vm_compute in LoV.renorm I_sdB23.
Definition I_sdB24 : sstate := Eval vm_compute in add_facts (ss_facts Ev_sdB2) (import_post s_sdB2 (ss_next Pre_sd_U) (lf_state (nth 3 Posts_sd_U (mkLeaf Pre_sd_U RsSymJump))) (ss_next Ev_sdB2) R_sdB2).
Definition T_sdB24 : sstate := Eval vm_compute in LoV.renorm I_sdB24.
Definition conts_sdB2 : list (list nstep * aedesc) :=
  [(LoV.renorm_prog I_sdB21, (T_sdB21, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0))));
   (LoV.renorm_prog I_sdB22, (T_sdB22, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0))));
   (LoV.renorm_prog I_sdB23, (T_sdB23, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0))));
   (LoV.renorm_prog I_sdB24, (T_sdB24, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0))))].
Lemma chk_sdB2 : pure_site_check LD.NP Pre_sd_U Posts_sd_U LoU.base_facts Ev_sdB2 s_sdB2 LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_sdB2 LD.z0) conts_sdB2 = true.
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
Hypothesis C_sdB2 : forall tv am rho rho1,
  TR (SP segsU (fun tr md => JGv tv am rho tr md) Pre_sd_U rho1) (LQ segsU (fun tr md => JGv tv am rho tr md) (ss_next Pre_sd_U) rho1 Posts_sd_U).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_sdB21 : In (T_sdB21, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0))) cutsE.
Hypothesis IN_sdB22 : In (T_sdB22, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0))) cutsE.
Hypothesis IN_sdB23 : In (T_sdB23, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0))) cutsE.
Hypothesis IN_sdB24 : In (T_sdB24, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0))) cutsE.
Lemma L_E_sdB2 : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_sdB2 rho) (FAM (ameas (E_sdB2, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdB2 LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_sdB2, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdB2 LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_sdB2 LD.z0) rho).
  eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segsU _ ns_sdB2 rho E_sdB2 Ev_sdB2 w view_sdB2 Hw). }
  apply ((pure_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML Pre_sd_U Posts_sd_U LoU.base_facts TR TR_facts TR_pre TR_callJ C_sdB2)
           Ev_sdB2 s_sdB2 LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_sdB2 LD.z0) conts_sdB2 rho _ chk_sdB2).
  intros c rho' Hc Hm. unfold conts_sdB2 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
  { exact (REENTER T_sdB21 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0)) rho' _ IN_sdB21 Hm). }
  { exact (REENTER T_sdB22 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0)) rho' _ IN_sdB22 Hm). }
  { exact (REENTER T_sdB23 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0)) rho' _ IN_sdB23 Hm). }
  { exact (REENTER T_sdB24 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0)) rho' _ IN_sdB24 Hm). }
Qed.
End Exit.

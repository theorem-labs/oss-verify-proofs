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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_bw.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.


(* Call of the warning builder (0x1a690) from 0x14974: a0 = builder (allocator, header and status pieces); it ends in a tail call of diag_append (T_bw1 is at diag_append's entry). *)
Definition E_bw : sstate := LoSite.E_bw.
Definition vops_bw : list LD.vop := [].
Definition ns_bw : list nstep := Eval vm_compute in LoV.view_ns E_bw vops_bw.
Definition Ev_bw : sstate := Eval vm_compute in LoV.view vops_bw E_bw.
Lemma view_bw : run_nsteps E_bw ns_bw = Some Ev_bw.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition x_bw : wsub := [].
Definition s_bw : wsub := Eval vm_compute in LoV.sOf Ev_bw Pre_bw x_bw.
Definition R_bw : list sobj := Eval vm_compute in LoV.R_of Ev_bw Pre_bw x_bw.
Definition I_bw1 : sstate := Eval vm_compute in add_facts (ss_facts Ev_bw) (import_post s_bw (ss_next Pre_bw) (lf_state (nth 0 Posts_bw (mkLeaf Pre_bw RsSymJump))) (ss_next Ev_bw) R_bw).
Definition T_bw1 : sstate := Eval vm_compute in LoV.renorm I_bw1.
Definition conts_bw : list (list nstep * aedesc) :=
  [(LoV.renorm_prog I_bw1, (T_bw1, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_bw LD.z0))))].
Lemma chk_bw : pure_site_check LD.NP Pre_bw Posts_bw LoU.base_facts Ev_bw s_bw LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_bw LD.z0) conts_bw = true.
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
Hypothesis C_bw : forall tv am rho rho1,
  TR (SP segsU (fun tr md => JGv tv am rho tr md) Pre_bw rho1) (LQ segsU (fun tr md => JGv tv am rho tr md) (ss_next Pre_bw) rho1 Posts_bw).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_bw1 : In (T_bw1, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_bw LD.z0))) cutsE.
Lemma L_E_bw : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_bw rho) (FAM (ameas (E_bw, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_bw LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_bw, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_bw LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_bw LD.z0) rho).
  eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segsU _ ns_bw rho E_bw Ev_bw w view_bw Hw). }
  apply ((pure_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML Pre_bw Posts_bw LoU.base_facts TR TR_facts TR_pre TR_callJ C_bw)
           Ev_bw s_bw LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_bw LD.z0) conts_bw rho _ chk_bw).
  intros c rho' Hc Hm. unfold conts_bw in Hc. cbn [In] in Hc. destruct Hc as [<-|[]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
  { exact (REENTER T_bw1 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_bw LD.z0)) rho' _ IN_bw1 Hm). }
Qed.
End Exit.

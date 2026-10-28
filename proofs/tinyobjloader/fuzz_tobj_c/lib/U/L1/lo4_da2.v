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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require Import S_da.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.


(* Call of diag_append with s7 = 2 (0x1bf5c) from 0x145a4: a0 = the builder's warning list (0); 64-byte frame. *)
Definition E_da2 : sstate := LoSite.E_da2.
Definition vops_da2 : list LD.vop := [LD.VDeep 64].
Definition ns_da2 : list nstep := Eval vm_compute in LoV.view_ns E_da2 vops_da2.
Definition Ev_da2 : sstate := Eval vm_compute in LoV.view vops_da2 E_da2.
Lemma view_da2 : run_nsteps E_da2 ns_da2 = Some Ev_da2.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition x_da2 : wsub := [].
Definition s_da2 : wsub := Eval vm_compute in LoV.sOf Ev_da2 Pre_da x_da2.
Definition R_da2 : list sobj := Eval vm_compute in LoV.R_of Ev_da2 Pre_da x_da2.
Definition I_da21 : sstate := Eval vm_compute in add_facts (ss_facts Ev_da2) (import_post s_da2 (ss_next Pre_da) (lf_state (nth 0 Posts_da (mkLeaf Pre_da RsSymJump))) (ss_next Ev_da2) R_da2).
Definition T_da21 : sstate := Eval vm_compute in LoV.renorm I_da21.
Definition conts_da2 : list (list nstep * aedesc) :=
  [(LoV.renorm_prog I_da21, (T_da21, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_da LD.z0))))].
Lemma chk_da2 : pure_site_check LD.NP Pre_da Posts_da LoU.base_facts Ev_da2 s_da2 LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_da LD.z0) conts_da2 = true.
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
Hypothesis C_da : forall tv am rho rho1,
  TR (SP segsU (fun tr md => JGv tv am rho tr md) Pre_da rho1) (LQ segsU (fun tr md => JGv tv am rho tr md) (ss_next Pre_da) rho1 Posts_da).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_da21 : In (T_da21, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_da LD.z0))) cutsE.
Lemma L_E_da2 : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_da2 rho) (FAM (ameas (E_da2, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_da LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_da2, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_da LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_da LD.z0) rho).
  eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segsU _ ns_da2 rho E_da2 Ev_da2 w view_da2 Hw). }
  apply ((pure_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML Pre_da Posts_da LoU.base_facts TR TR_facts TR_pre TR_callJ C_da)
           Ev_da2 s_da2 LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_da LD.z0) conts_da2 rho _ chk_da2).
  intros c rho' Hc Hm. unfold conts_da2 in Hc. cbn [In] in Hc. destruct Hc as [<-|[]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
  { exact (REENTER T_da21 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_da LD.z0)) rho' _ IN_da21 Hm). }
Qed.
End Exit.

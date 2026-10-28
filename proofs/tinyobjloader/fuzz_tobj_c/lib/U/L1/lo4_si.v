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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10 Require Import S_si.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.


(* Call of scan_int (0x1a54c) from 0x148b0: a0 = the text-pointer local at sp+1632, a2 = the int local at sp+1616. *)
Definition E_si : sstate := LoSite.E_si.
Definition vops_si : list LD.vop := [LD.VCarve (1632 - LoU.FR) 8; LD.VCarve (1616 - LoU.FR) 4].
Definition ns_si : list nstep := Eval vm_compute in LoV.view_ns E_si vops_si.
Definition Ev_si : sstate := Eval vm_compute in LoV.view vops_si E_si.
Lemma view_si : run_nsteps E_si ns_si = Some Ev_si.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
(* the end pointer arrives as pSL + (vB + pST) (the engine's add order); bind scan_int's base / cursor / end offsets *)
Definition x_si : wsub := [(15%positive, LD.vB); (16%positive, LD.pST); (17%positive, SAlu ALU_ADD LD.pST LD.pSL); (18%positive, LD.vL)].
Definition s_si : wsub := Eval vm_compute in LoV.sOf Ev_si Pre_si_U x_si.
Definition R_si : list sobj := Eval vm_compute in LoV.R_of Ev_si Pre_si_U x_si.
Definition I_si1 : sstate := Eval vm_compute in add_facts (ss_facts Ev_si) (import_post s_si (ss_next Pre_si_U) (lf_state (nth 0 Posts_si_U (mkLeaf Pre_si_U RsSymJump))) (ss_next Ev_si) R_si).
Definition T_si1 : sstate := Eval vm_compute in LoV.renorm I_si1.
Definition I_si2 : sstate := Eval vm_compute in add_facts (ss_facts Ev_si) (import_post s_si (ss_next Pre_si_U) (lf_state (nth 1 Posts_si_U (mkLeaf Pre_si_U RsSymJump))) (ss_next Ev_si) R_si).
Definition T_si2 : sstate := Eval vm_compute in LoV.renorm I_si2.
Definition conts_si : list (list nstep * aedesc) :=
  [(LoV.renorm_prog I_si1, (T_si1, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_si LD.z0))));
   (LoV.renorm_prog I_si2, (T_si2, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_si LD.z0))))].
Lemma chk_si : pure_site_check LD.NP Pre_si_U Posts_si_U LoU.base_facts Ev_si s_si LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_si LD.z0) conts_si = true.
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
Hypothesis C_si : forall tv am rho rho1,
  TR (SP segsU (fun tr md => JGv tv am rho tr md) Pre_si_U rho1) (LQ segsU (fun tr md => JGv tv am rho tr md) (ss_next Pre_si_U) rho1 Posts_si_U).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_si1 : In (T_si1, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_si LD.z0))) cutsE.
Hypothesis IN_si2 : In (T_si2, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_si LD.z0))) cutsE.
Lemma L_E_si : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_si rho) (FAM (ameas (E_si, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_si LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_si, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_si LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_si LD.z0) rho).
  eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segsU _ ns_si rho E_si Ev_si w view_si Hw). }
  apply ((pure_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML Pre_si_U Posts_si_U LoU.base_facts TR TR_facts TR_pre TR_callJ C_si)
           Ev_si s_si LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_si LD.z0) conts_si rho _ chk_si).
  intros c rho' Hc Hm. unfold conts_si in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
  { exact (REENTER T_si1 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_si LD.z0)) rho' _ IN_si1 Hm). }
  { exact (REENTER T_si2 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_si LD.z0)) rho' _ IN_si2 Hm). }
Qed.
End Exit.

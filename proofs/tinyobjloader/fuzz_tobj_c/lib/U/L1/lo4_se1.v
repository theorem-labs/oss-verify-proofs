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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require Import S_u18350.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.


(* Call of slice_eq (0x18350) from 0x140d4: a0 = token start in the text, a1 = token length, a2 = literal 0x102f7. *)
Definition E_se1 : sstate := LoSite.E_se1.
Definition vops_se1 : list LD.vop := [].
Definition ns_se1 : list nstep := Eval vm_compute in LoV.view_ns E_se1 vops_se1.
Definition Ev_se1 : sstate := Eval vm_compute in LoV.view vops_se1 E_se1.
Lemma view_se1 : run_nsteps E_se1 ns_se1 = Some Ev_se1.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition x_se1 : wsub := [].
Definition s_se1 : wsub := Eval vm_compute in LoV.sOf Ev_se1 (Pre_se 0x102f7) x_se1.
Definition R_se1 : list sobj := Eval vm_compute in LoV.R_of Ev_se1 (Pre_se 0x102f7) x_se1.
Definition I_se11 : sstate := Eval vm_compute in add_facts (ss_facts Ev_se1) (import_post s_se1 (ss_next (Pre_se 0x102f7)) (lf_state (nth 0 Posts_se (mkLeaf (Pre_se 0x102f7) RsSymJump))) (ss_next Ev_se1) R_se1).
Definition T_se11 : sstate := Eval vm_compute in LoV.renorm I_se11.
Definition I_se12 : sstate := Eval vm_compute in add_facts (ss_facts Ev_se1) (import_post s_se1 (ss_next (Pre_se 0x102f7)) (lf_state (nth 1 Posts_se (mkLeaf (Pre_se 0x102f7) RsSymJump))) (ss_next Ev_se1) R_se1).
Definition T_se12 : sstate := Eval vm_compute in LoV.renorm I_se12.
Definition I_se13 : sstate := Eval vm_compute in add_facts (ss_facts Ev_se1) (import_post s_se1 (ss_next (Pre_se 0x102f7)) (lf_state (nth 2 Posts_se (mkLeaf (Pre_se 0x102f7) RsSymJump))) (ss_next Ev_se1) R_se1).
Definition T_se13 : sstate := Eval vm_compute in LoV.renorm I_se13.
Definition conts_se1 : list (list nstep * aedesc) :=
  [(LoV.renorm_prog I_se11, (T_se11, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se1 LD.z0))));
   (LoV.renorm_prog I_se12, (T_se12, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se1 LD.z0))));
   (LoV.renorm_prog I_se13, (T_se13, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se1 LD.z0))))].
Lemma chk_se1 : pure_site_check LD.NP (Pre_se 0x102f7) Posts_se LoU.base_facts Ev_se1 s_se1 LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_se1 LD.z0) conts_se1 = true.
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
Hypothesis C_se1 : forall tv am rho rho1,
  TR (SP segsU (fun tr md => JGv tv am rho tr md) (Pre_se 0x102f7) rho1) (LQ segsU (fun tr md => JGv tv am rho tr md) (ss_next (Pre_se 0x102f7)) rho1 Posts_se).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_se11 : In (T_se11, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se1 LD.z0))) cutsE.
Hypothesis IN_se12 : In (T_se12, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se1 LD.z0))) cutsE.
Hypothesis IN_se13 : In (T_se13, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se1 LD.z0))) cutsE.
Lemma L_E_se1 : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_se1 rho) (FAM (ameas (E_se1, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_se1 LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_se1, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_se1 LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_se1 LD.z0) rho).
  eapply TR_pre. { intros w Hw. exact (SPJ_nsteps segsU _ ns_se1 rho E_se1 Ev_se1 w view_se1 Hw). }
  apply ((pure_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (Pre_se 0x102f7) Posts_se LoU.base_facts TR TR_facts TR_pre TR_callJ C_se1)
           Ev_se1 s_se1 LoU.tvL LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_se1 LD.z0) conts_se1 rho _ chk_se1).
  intros c rho' Hc Hm. unfold conts_se1 in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
  { exact (REENTER T_se11 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_se1 LD.z0)) rho' _ IN_se11 Hm). }
  { exact (REENTER T_se12 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_se1 LD.z0)) rho' _ IN_se12 Hm). }
  { exact (REENTER T_se13 LoU.tvL LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_se1 LD.z0)) rho' _ IN_se13 Hm). }
Qed.
End Exit.

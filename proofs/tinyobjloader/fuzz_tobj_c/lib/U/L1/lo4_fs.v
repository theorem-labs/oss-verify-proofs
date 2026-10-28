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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require Import S_fs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.


(* Call of finalize_shape (0x152cc) from 0x143f8: a0 = builder; its 192-byte frame and the 48-byte frame below are carved from the deep stack; it may grow the shape vectors and move the arena head (slots 6-13, 19). *)
Definition E_fs : sstate := LoSite.E_fs.
Definition vops_fs : list LD.vop := [LD.VDeep2 192 48].
Definition ns_fs : list nstep := Eval vm_compute in LoV.view_ns E_fs vops_fs.
Definition Ev_fs : sstate := Eval vm_compute in LoV.view vops_fs E_fs.
Lemma view_fs : run_nsteps E_fs ns_fs = Some Ev_fs.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition slots_fs : list nat := [7; 8; 9; 10; 11; 12; 13; 6; 19]%nat.
Lemma perm_fs : permb LoU.tvL (LoV.keptL slots_fs ++ LoV.passedL slots_fs) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition x_fs : wsub := [(19%positive, SAlu ALU_ADD LD.vDp (SLit 192))].
Definition s_fs : wsub := Eval vm_compute in LoV.sOf Ev_fs Pre_fs x_fs.
Definition R_fs : list sobj := Eval vm_compute in LoV.R_of Ev_fs Pre_fs x_fs.
Definition A_fs1 : sstate := Eval vm_compute in T_afterN FD.NP Ev_fs s_fs R_fs (P_nop).
Definition T_fs1 : sstate := Eval vm_compute in LoV.renorm A_fs1.
Definition is_fs1 : wsub := Eval vm_compute in import_sub s_fs FD.NP (P_nop) (ss_next Ev_fs).
Definition tvT_fs1 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_fs (import_tv is_fs1 tv0).
Definition amT_fs1 : amode := Eval vm_compute in am_subst is_fs1 ahd.
Definition A_fs2 : sstate := Eval vm_compute in T_afterN FD.NP Ev_fs s_fs R_fs (P_ok).
Definition T_fs2 : sstate := Eval vm_compute in LoV.renorm A_fs2.
Definition is_fs2 : wsub := Eval vm_compute in import_sub s_fs FD.NP (P_ok) (ss_next Ev_fs).
Definition tvT_fs2 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_fs (import_tv is_fs2 tvOK).
Definition amT_fs2 : amode := Eval vm_compute in am_subst is_fs2 amq.
Definition A_fs3 : sstate := Eval vm_compute in T_afterN FD.NP Ev_fs s_fs R_fs (P_fail).
Definition T_fs3 : sstate := Eval vm_compute in LoV.renorm A_fs3.
Definition is_fs3 : wsub := Eval vm_compute in import_sub s_fs FD.NP (P_fail) (ss_next Ev_fs).
Definition tvT_fs3 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_fs (import_tv is_fs3 tv0).
Definition amT_fs3 : amode := Eval vm_compute in am_subst is_fs3 amq.
Definition A_fs4 : sstate := Eval vm_compute in T_afterN FD.NP Ev_fs s_fs R_fs (P_failz).
Definition T_fs4 : sstate := Eval vm_compute in LoV.renorm A_fs4.
Definition is_fs4 : wsub := Eval vm_compute in import_sub s_fs FD.NP (P_failz) (ss_next Ev_fs).
Definition tvT_fs4 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_fs (import_tv is_fs4 tv0).
Definition amT_fs4 : amode := Eval vm_compute in am_subst is_fs4 amq.
Definition conts_fs : list cdesc :=
  [(LoV.renorm_prog A_fs1, (T_fs1, (tvT_fs1, amT_fs1), (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0))));
   (LoV.renorm_prog A_fs2, (T_fs2, (tvT_fs2, amT_fs2), (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0))));
   (LoV.renorm_prog A_fs3, (T_fs3, (tvT_fs3, amT_fs3), (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0))));
   (LoV.renorm_prog A_fs4, (T_fs4, (tvT_fs4, amT_fs4), (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0))))].
Lemma chk_fs : site_check C_U LD.NP Pre_fs tv0 ahd PDA_fs FD.NP LoU.base_facts LD.is_txt
  Ev_fs s_fs (LoV.keptL slots_fs) (LoV.passedL slots_fs) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_fs LD.z0) conts_fs = true.
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
Hypothesis C_fs : forall FBc rho1,
  TR (SPJ segsU (JGA_pre segsU C_U Kc (P0_fs FBc) FBc tv0 ahd) Pre_fs rho1)
     (LQP segsU FD.NP rho1 (PostsCA segsU C_U Kc P0_fs PDA_fs FBc)).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_fs1 : In (T_fs1, (tvT_fs1, amT_fs1), (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0))) cutsE.
Hypothesis IN_fs2 : In (T_fs2, (tvT_fs2, amT_fs2), (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0))) cutsE.
Hypothesis IN_fs3 : In (T_fs3, (tvT_fs3, amT_fs3), (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0))) cutsE.
Hypothesis IN_fs4 : In (T_fs4, (tvT_fs4, amT_fs4), (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0))) cutsE.
Lemma L_E_fs : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_fs rho) (FAM (ameas (E_fs, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_fs LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_fs, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_fs LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_fs LD.z0) rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_fs rho w (permb_sound _ _ perm_fs)).
    exact (SPJ_nsteps segsU _ ns_fs rho E_fs Ev_fs w view_fs Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) P0_fs Pre_fs
            tv0 ahd PDA_fs FD.NP eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            C_fs (txt_extra_ok_U FB rho0))
           Ev_fs s_fs (LoV.keptL slots_fs) (LoV.passedL slots_fs) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_fs LD.z0) conts_fs rho _ chk_fs).
  - intros ms R HF HP0 Hav HZ. exact I.
  - intros c rho' Hc Hm. unfold conts_fs in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { exact (REENTER T_fs1 tvT_fs1 amT_fs1 (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0)) rho' _ IN_fs1 Hm). }
    { exact (REENTER T_fs2 tvT_fs2 amT_fs2 (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0)) rho' _ IN_fs2 Hm). }
    { exact (REENTER T_fs3 tvT_fs3 amT_fs3 (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0)) rho' _ IN_fs3 Hm). }
    { exact (REENTER T_fs4 tvT_fs4 amT_fs4 (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0)) rho' _ IN_fs4 Hm). }
Qed.
End Exit.

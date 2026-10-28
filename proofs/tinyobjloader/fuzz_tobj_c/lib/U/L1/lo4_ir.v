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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L14 Require Import S_ir.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module LG := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue.

(* Call of intern_rest (0x18c6c) from 0x143e8: a0 = builder, a1 = cursor (two objects); its 32-byte frame and arena_alloc's 48-byte frame are carved from the deep stack; it may move the arena head (slot 19). *)
Definition E_ir : sstate := LoSite.E_ir.
Definition vops_ir : list LD.vop := [LD.VDeep2 32 48].
Definition ns_ir : list nstep := Eval vm_compute in LoV.view_ns E_ir vops_ir.
Definition Ev_ir : sstate := Eval vm_compute in LoV.view vops_ir E_ir.
Lemma view_ir : run_nsteps E_ir ns_ir = Some Ev_ir.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition slots_ir : list nat := [19]%nat.
Lemma perm_ir : permb LoU.tvL (LoV.keptL slots_ir ++ LoV.passedL slots_ir) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition x_ir : wsub := [(19%positive, SAlu ALU_ADD LD.vDp (SLit 32))].
Definition s_ir : wsub := Eval vm_compute in LoV.sOf Ev_ir Pre_ir x_ir.
Definition R_ir : list sobj := Eval vm_compute in LoV.R_of Ev_ir Pre_ir x_ir.
Definition A_ir1 : sstate := Eval vm_compute in T_afterN NF Ev_ir s_ir R_ir (P_fail).
Definition T_ir1 : sstate := Eval vm_compute in LoV.renorm A_ir1.
Definition is_ir1 : wsub := Eval vm_compute in import_sub s_ir NF (P_fail) (ss_next Ev_ir).
Definition tvT_ir1 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_ir (import_tv is_ir1 tv0).
Definition amT_ir1 : amode := Eval vm_compute in am_subst is_ir1 ahd.
Definition A_ir2 : sstate := Eval vm_compute in T_afterN NF Ev_ir s_ir R_ir (P_ok).
Definition T_ir2 : sstate := Eval vm_compute in LoV.renorm A_ir2.
Definition is_ir2 : wsub := Eval vm_compute in import_sub s_ir NF (P_ok) (ss_next Ev_ir).
Definition tvT_ir2 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_ir (import_tv is_ir2 tv0).
Definition amT_ir2 : amode := Eval vm_compute in am_subst is_ir2 am_ok.
Definition conts_ir : list cdesc :=
  [(LoV.renorm_prog A_ir1, (T_ir1, (tvT_ir1, amT_ir1), (LoMeas.rT, (LD.VLp LoMeas.kT_ir LD.z0))));
   (LoV.renorm_prog A_ir2, (T_ir2, (tvT_ir2, amT_ir2), (LoMeas.rT, (LD.VLp LoMeas.kT_ir LD.z0))))].
Lemma chk_ir : site_check C_U LD.NP Pre_ir tv0 ahd PDA_ir NF LoU.base_facts LD.is_txt
  Ev_ir s_ir (LoV.keptL slots_ir) (LoV.passedL slots_ir) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_ir LD.z0) conts_ir = true.
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
Hypothesis C_ir : forall FBc rho1,
  TR (SPJ segsU (JGA_pre segsU C_U Kc (P0_ir FBc) FBc tv0 ahd) Pre_ir rho1)
     (LQP segsU NF rho1 (PostsCA segsU C_U Kc P0_ir PDA_ir FBc)).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_ir1 : In (T_ir1, (tvT_ir1, amT_ir1), (LoMeas.rT, (LD.VLp LoMeas.kT_ir LD.z0))) cutsE.
Hypothesis IN_ir2 : In (T_ir2, (tvT_ir2, amT_ir2), (LoMeas.rT, (LD.VLp LoMeas.kT_ir LD.z0))) cutsE.
Lemma L_E_ir : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_ir rho) (FAM (ameas (E_ir, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_ir LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_ir, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_ir LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_ir LD.z0) rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_ir rho w (permb_sound _ _ perm_ir)).
    exact (SPJ_nsteps segsU _ ns_ir rho E_ir Ev_ir w view_ir Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) P0_ir Pre_ir
            tv0 ahd PDA_ir NF eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            C_ir (txt_extra_ok_U FB rho0))
           Ev_ir s_ir (LoV.keptL slots_ir) (LoV.passedL slots_ir) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_ir LD.z0) conts_ir rho _ chk_ir).
  - intros ms R HF HP0 Hav HZ. unfold P0_ir. apply (LG.P0_txt_call_nz FB rho0 rho 18 15 _ R ms s_ir); [vm_compute; reflexivity | vm_compute; reflexivity | exact HP0 | exact Hav | ].
    apply (LG.L_nz_of rho LD.pE (ss_facts Ev_ir) HF); vm_compute; tauto.
  - intros c rho' Hc Hm. unfold conts_ir in Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { exact (REENTER T_ir1 tvT_ir1 amT_ir1 (LoMeas.rT, (LD.VLp LoMeas.kT_ir LD.z0)) rho' _ IN_ir1 Hm). }
    { exact (REENTER T_ir2 tvT_ir2 amT_ir2 (LoMeas.rT, (LD.VLp LoMeas.kT_ir LD.z0)) rho' _ IN_ir2 Hm). }
Qed.
End Exit.

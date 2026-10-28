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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require Import S_op.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.


(* Call of opt_push (0x1bd78) from 0x149e8, cm = 3: a0 = the builder vector header at builder+280, a3/a4 = the value and default locals at sp+1632 / sp+1616; 80-byte frame; it may grow that vector (slot 5). *)
Definition E_op3 : sstate := LoSite.E_op3.
Definition vops_op3 : list LD.vop := [LD.VVec 280; LD.VCarve (1632 - LoU.FR) 12; LD.VCarve (1616 - LoU.FR) 12; LD.VDeep 80].
Definition ns_op3 : list nstep := Eval vm_compute in LoV.view_ns E_op3 vops_op3.
Definition Ev_op3 : sstate := Eval vm_compute in LoV.view vops_op3 E_op3.
Lemma view_op3 : run_nsteps E_op3 ns_op3 = Some Ev_op3.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition slots_op3 : list nat := [5]%nat.
Lemma perm_op3 : permb LoU.tvL (LoV.keptL slots_op3 ++ LoV.passedL slots_op3) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition x_op3 : wsub := [(99%positive, LD.pH)].
Definition s_op3 : wsub := Eval vm_compute in LoV.sOf Ev_op3 (Pre_op_U 3) x_op3.
Definition R_op3 : list sobj := Eval vm_compute in LoV.R_of Ev_op3 (Pre_op_U 3) x_op3.
Definition A_op31 : sstate := Eval vm_compute in T_afterN 100 Ev_op3 s_op3 R_op3 (P_ret_U 3).
Definition T_op31 : sstate := Eval vm_compute in LoV.renorm A_op31.
Definition is_op31 : wsub := Eval vm_compute in import_sub s_op3 100 (P_ret_U 3) (ss_next Ev_op3).
Definition tvT_op31 : list (sv * sv) :=
  Eval vm_compute in LoV.tvfill slots_op3 (import_tv is_op31 OP1.tvP).
Definition conts_op3 : list cdesc :=
  [(LoV.renorm_prog A_op31, (T_op31, (tvT_op31, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_op3 LD.z0))))].
Lemma chk_op3 : site_check C_U LD.NP (Pre_op_U 3) OP1.tv0 (AHead (SVar 99)) (PDAh (PD_op_U 3) 99) 100 LoU.base_facts LD.is_txt
  Ev_op3 s_op3 (LoV.keptL slots_op3) (LoV.passedL slots_op3) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_op3 LD.z0) conts_op3 = true.
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
Hypothesis C_op3 : forall FBc rho1,
  TR (SPJ segsU (JGA_pre segsU C_U Kc (OP1.P0_op FBc) FBc OP1.tv0 (AHead (SVar 99))) (Pre_op_U 3) rho1)
     (LQP segsU 100 rho1 (PostsCA segsU C_U Kc OP1.P0_op (PDAh (PD_op_U 3) 99) FBc)).
Variable cutsE : list aedesc.
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis IN_op31 : In (T_op31, (tvT_op31, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_op3 LD.z0))) cutsE.
Lemma L_E_op3 : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_op3 rho) (FAM (ameas (E_op3, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_op3 LD.z0))) rho)).
Proof.
  intros rho. change (ameas (E_op3, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_op3 LD.z0))) rho) with (emeasZ LoMeas.rE (LD.VLp LoMeas.kE_op3 LD.z0) rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_op3 rho w (permb_sound _ _ perm_op3)).
    exact (SPJ_nsteps segsU _ ns_op3 rho E_op3 Ev_op3 w view_op3 Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) OP1.P0_op (Pre_op_U 3)
            OP1.tv0 (AHead (SVar 99)) (PDAh (PD_op_U 3) 99) 100 eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            C_op3 (txt_extra_ok_U FB rho0))
           Ev_op3 s_op3 (LoV.keptL slots_op3) (LoV.passedL slots_op3) LoU.amL LoMeas.rE (LD.VLp LoMeas.kE_op3 LD.z0) conts_op3 rho _ chk_op3).
  - intros ms R _ _ _ _. exact I.
  - intros c rho' Hc Hm. unfold conts_op3 in Hc. cbn [In] in Hc. destruct Hc as [<-|[]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    { exact (REENTER T_op31 tvT_op31 LoU.amL (LoMeas.rT, (LD.VLp LoMeas.kT_op3 LD.z0)) rho' _ IN_op31 Hm). }
Qed.
End Exit.

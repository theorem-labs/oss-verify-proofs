From Stdlib Require Import ZArith NArith List Bool PArith Lia Sorting.Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV DrvLoop.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs hf_cuts hf_tail hf_tailc hf_pc hf_tok_defs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require Import hf_vr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10.S_pc.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6.S_pg.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module PCU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10.S_pc.
Module PGU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6.S_pg.

(* Token region of handle_f: latch heads T94z_U/T94n_U, corner vr call (exits Ev*, posts TAm/TAe/FAz/FAn),
   parse_corner call (exits EPm/EPe, posts TPm/TPe).  Leaves outside the region: T50_U (ent_cuts) and HP_ret. *)
Definition tok_cuts : list edesc :=
  [(T94z_U, tvH, (90, vT94_U)); (T94n_U, tvH, (90, vT94_U));
   (TAm_U, tvH, (90, vTA_U)); (TAe_U, tvH, (90, vTA_U)); (FAz_U, tvH, (85, z0)); (FAn_U, tvH, (85, z0));
   (TPm_U, tvH, (90, vTP_U)); (TPe_U, tvH, (90, vTP_U))].
Definition tok_exits : list edesc :=
  [(Evzm_U, tvH, (90, vEv_U)); (Evnm_U, tvH, (90, vEv_U)); (Evze_U, tvH, (90, vEv_U)); (Evne_U, tvH, (90, vEv_U));
   (EPm_U, tvH, (90, vEP_U)); (EPe_U, tvH, (90, vEP_U))].

Section Tok.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segsU C_U.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall J S rho (Q' : assn),
  (Forall (holds rho) (ss_facts S) -> TR (SPJ segsU J S rho) Q') -> TR (SPJ segsU J S rho) Q'.
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segsU (J x) S rho) Q') -> TR (SPJ segsU (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : forall (P P' Q' : assn), (forall w, P' w -> P w) -> TR P Q' -> TR P' Q'.
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn),
  (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : forall (X : Prop) (P Q' : assn), (X -> TR P Q') -> TR (fun w => X /\ P w) Q'.
Hypothesis TR_callP : ltac:(argty (client_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML (fun _ => VRU.P0_vr)
  VRU.Pre_vr VRU.tv0 VRU.PD_vr NF eq_refl TR TR_facts TR_ex TR_pre)).
Hypothesis TR_callJ : ltac:(argty (pure_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML TR TR_facts TR_pre)).
Hypothesis CVR : forall FBc rho1,
  TR (SPJ segsU (JG_pre segsU C_U Kc VRU.P0_vr FBc VRU.tv0) VRU.Pre_vr rho1)
     (LQP segsU NF rho1 (VRU.Posts_vr Kc FBc)).
Hypothesis CPC : forall tv rho rho1,
  TR (SP segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) PCU.Pre_pc_U rho1)
     (LQ segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) NF rho1 PCU.Posts_pc_U).
Hypothesis CTP : forall tv rho rho1,
  TR (SP segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) (PGU.Pre_pg_U []) rho1)
     (LQ segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) NF rho1 PGU.Posts_pg_U).
Hypothesis REENTER : forall T tv rv rho b, In (T, tv, rv) tok_cuts ->
  0 <= emeas (T, tv, rv) rho /\ emeas (T, tv, rv) rho < b ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv) T rho) (FAM b).
Hypothesis POST : forall P tv rho b, In (P, JLG segsU C_U Kc (P0_hf FB) FB tv) (Posts_hf_U Kc FB) ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv) P rho) (FAM b).

Let JGv (tv : list (sv * sv)) : jpred := JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv.
Let XS := X_vr_site Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP CVR tok_cuts REENTER.
Let XP := X_pc_site Kc FB rho0 ML TR FAM TR_facts TR_pre TR_exw TR_pureh TR_callJ CPC tok_cuts REENTER.

Lemma X_Evzm : forall rho, TR (SPJ segsU (JGv tvH) Evzm_U rho) (FAM (emeas (Evzm_U, tvH, (90, vEv_U)) rho)).
Proof.
  intros rho.
  apply (XS Evzm_U E2zm_U xs_t1 1%nat (-32) szm_U 5%nat nzco_U TAm_U FAz_U vTA_U 90 z0 85 90 vEv_U
           (svar_idx (t_d co1)) (svar_idx (t_k co1)) 12%Z rho);
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; tauto | lia
    | unfold tok_cuts; cbn [In]; tauto | unfold tok_cuts; cbn [In]; tauto ].
Qed.

Lemma X_Evnm : forall rho, TR (SPJ segsU (JGv tvH) Evnm_U rho) (FAM (emeas (Evnm_U, tvH, (90, vEv_U)) rho)).
Proof.
  intros rho.
  apply (XS Evnm_U E2nm_U xs_t1 1%nat (-32) snm_U 5%nat nzco_U TAm_U FAn_U vTA_U 90 z0 85 90 vEv_U
           (svar_idx (t_d co1)) (svar_idx (t_k co1)) 12%Z rho);
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; tauto | lia
    | unfold tok_cuts; cbn [In]; tauto | unfold tok_cuts; cbn [In]; tauto ].
Qed.

Lemma X_Evze : forall rho, TR (SPJ segsU (JGv tvH) Evze_U rho) (FAM (emeas (Evze_U, tvH, (90, vEv_U)) rho)).
Proof.
  intros rho.
  apply (XS Evze_U E2ze_U xs_t1 1%nat (-32) sze_U 5%nat nzco_U TAe_U FAz_U vTA_U 90 z0 85 90 vEv_U
           (svar_idx (t_d co1)) (svar_idx (t_k co1)) 12%Z rho);
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; tauto | lia
    | unfold tok_cuts; cbn [In]; tauto | unfold tok_cuts; cbn [In]; tauto ].
Qed.

Lemma X_Evne : forall rho, TR (SPJ segsU (JGv tvH) Evne_U rho) (FAM (emeas (Evne_U, tvH, (90, vEv_U)) rho)).
Proof.
  intros rho.
  apply (XS Evne_U E2ne_U xs_t1 1%nat (-32) sne_U 5%nat nzco_U TAe_U FAn_U vTA_U 90 z0 85 90 vEv_U
           (svar_idx (t_d co1)) (svar_idx (t_k co1)) 12%Z rho);
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; tauto | lia
    | unfold tok_cuts; cbn [In]; tauto | unfold tok_cuts; cbn [In]; tauto ].
Qed.

Lemma X_EPm : forall rho, TR (SPJ segsU (JGv tvH) EPm_U rho) (FAM (emeas (EPm_U, tvH, (90, vEP_U)) rho)).
Proof.
  intros rho. apply (XP EPm_U xs1pc 5 2 (xs2pc selPm) TPm_U vTP_U 90 90 vEP_U rho);
    [vm_compute; reflexivity | unfold tok_cuts; cbn [In]; tauto].
Qed.

Lemma X_EPe : forall rho, TR (SPJ segsU (JGv tvH) EPe_U rho) (FAM (emeas (EPe_U, tvH, (90, vEP_U)) rho)).
Proof.
  intros rho. apply (XP EPe_U xs1pc 5 2 (xs2pc selPe) TPe_U vTP_U 90 90 vEP_U rho);
    [vm_compute; reflexivity | unfold tok_cuts; cbn [In]; tauto].
Qed.

Lemma tok_exits_okT : forall X tvX rvX rho, In (X, tvX, rvX) tok_exits ->
  TR (SPJ segsU (JGv tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).
Proof using Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP TR_callJ CVR CPC CTP REENTER POST.
  intros X tvX rvX rho Hin. unfold tok_exits in Hin. cbn [In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[]]]]]]]; inversion H; subst;
    [apply X_Evzm | apply X_Evnm | apply X_Evze | apply X_Evne | apply X_EPm | apply X_EPe].
Qed.

End Tok.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue ObjUnbase ObjXform TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10.S_pc.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6.S_pg.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require Export hf_tri_defs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require Import hf_vr hf_tria hf_trb.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module PCU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10.S_pc.
Module PGU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6.S_pg.

Definition tri_cuts : list edesc := tria_cuts ++ trb_cuts.
Definition tri_exits : list edesc := tria_exits ++ trb_exits.

Section Tri.
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
Hypothesis REENTER : forall T tv rv rho b, In (T, tv, rv) tri_cuts ->
  0 <= emeas (T, tv, rv) rho /\ emeas (T, tv, rv) rho < b ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv) T rho) (FAM b).
Hypothesis POST : forall P tv rho b, In (P, JLG segsU C_U Kc (P0_hf FB) FB tv) (Posts_hf_U Kc FB) ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv) P rho) (FAM b).

Lemma tri_exits_okT : forall X tvX rvX rho, In (X, tvX, rvX) tri_exits ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).
Proof using Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP TR_callJ CVR CPC CTP REENTER POST.
  intros X tvX rvX rho Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply (tria_exits_okT Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP CVR); [| exact Hin].
    intros T tv rv rho' b HT Hb. apply (REENTER T tv rv rho' b); [apply in_or_app; left; exact HT | exact Hb].
  - apply (trb_exits_okT Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP TR_callJ CVR CPC CTP);
      [| exact POST | exact Hin].
    intros T tv rv rho' b HT Hb. apply (REENTER T tv rv rho' b); [apply in_or_app; right; exact HT | exact Hb].
Qed.

End Tri.

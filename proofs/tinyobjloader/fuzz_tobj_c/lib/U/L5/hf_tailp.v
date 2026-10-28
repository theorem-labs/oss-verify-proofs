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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs hf_tail hf_tailc.
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

Lemma cU_bk_holds : forall rho, Forall (holds rho) (ss_facts EU_bk) -> holds rho cU_bk.
Proof.
  intros rho HF. concrete_facts HF. pick_facts HF [0; 28; 32; 34; 67; 68]%nat.
  unfold cU_bk. zfacts; lia.
Qed.

Section Tail.
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
Hypothesis REENTER : forall T tv rv rho b, In (T, tv, rv) tail_cuts ->
  0 <= emeas (T, tv, rv) rho /\ emeas (T, tv, rv) rho < b ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv) T rho) (FAM b).
Hypothesis POST : forall P tv rho b, In (P, JLG segsU C_U Kc (P0_hf FB) FB tv) (Posts_hf_U Kc FB) ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv) P rho) (FAM b).

Let JGv (tv : list (sv * sv)) : jpred := JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv.
Let XS := X_vr_site Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP CVR tail_cuts REENTER.
Let ENT := TobjJVx.entE_TR segsU C_U NP Kc rho0 (P0_hf FB) FB ML TR TR_pre TR_exw TR_pureh.

Ltac in_pos n :=
  lazymatch n with
  | O => left; reflexivity
  | S ?m => right; in_pos m
  end.

Ltac vr_site E E2 xs i s j nzk TA TF vA vE v e na nf :=
  intros rho;
  apply (XS E E2 xs i (-32) s j nzk TA TF vA 40 z0 38 40 vE (svar_idx (t_d v)) (svar_idx (t_k v)) e rho);
  [ vm_compute; reflexivity | vm_compute; reflexivity | lia | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; tauto | lia
  | unfold tail_cuts; in_pos na | unfold tail_cuts; in_pos nf ].

Lemma X_EU_mi : forall rho, TR (SPJ segsU (JGv tvH) EU_mi rho) (FAM (emeas (EU_mi, tvH, (40, VL 8)) rho)).
Proof. vr_site EU_mi E2U_mi xs_t1 1%nat sU_mi 1%nat nzU_mi AU_mi FU_mi (VL 7) (VL 8) mi1 12%Z 1%nat 5%nat. Qed.

Lemma X_EU_fv : forall rho, TR (SPJ segsU (JGv tvH) EU_fv rho) (FAM (emeas (EU_fv, tvH, (40, VL 6)) rho)).
Proof. vr_site EU_fv E2U_fv xs_t0 0%nat sU_fv 2%nat nzU_fv AU_fv FU_fv (VL 5) (VL 6) fv1 4%Z 2%nat 6%nat. Qed.

Lemma X_EU_mm : forall rho, TR (SPJ segsU (JGv tvH) EU_mm rho) (FAM (emeas (EU_mm, tvH, (40, VL 4)) rho)).
Proof. vr_site EU_mm E2U_mm xs_t0 0%nat sU_mm 3%nat nzU_mm AU_mm FU_mm (VL 3) (VL 4) mm1 4%Z 3%nat 7%nat. Qed.

Lemma X_EU_sg : forall rho, TR (SPJ segsU (JGv tvH) EU_sg rho) (FAM (emeas (EU_sg, tvH, (40, VL 2)) rho)).
Proof. vr_site EU_sg E2U_sg xs_t0 0%nat sU_sg 4%nat nzU_sg AU_sg FU_sg (VL 1) (VL 2) sg1 4%Z 4%nat 8%nat. Qed.

Lemma X_EU_bk : forall rho, TR (SPJ segsU (JGv tvH) EU_bk rho) (FAM (emeas (EU_bk, tvH, (40, VL 0)) rho)).
Proof.
  intros rho. apply TR_facts. intros HF.
  rewrite (TobjJVx.emeas_emeasZ EU_bk tvH 40 (VL 0) rho).
  eapply TR_pre.
  { intros w Hw. exact (SPJ_add_facts segsU _ rho [cU_bk] EU_bk w Hw
      ltac:(constructor; [exact (cU_bk_holds rho HF) | constructor]) ltac:(vm_compute; reflexivity)). }
  apply (ENT (ss_next EU_bk) (add_facts [cU_bk] EU_bk) L14_U tvH tvH tvH (VL 9) 40 40 (VL 0) rho rho).
  - vm_compute. reflexivity.
  - apply Permutation_refl.
  - apply agree_vals_refl.
  - intros rho' Hm. apply (REENTER L14_U tvH (40, VL 9) rho'); [unfold tail_cuts, L14_rv; left; reflexivity |].
    rewrite TobjJVx.emeas_emeasZ. exact Hm.
Qed.

Lemma tail_exits_okT : forall X tvX rvX rho, In (X, tvX, rvX) tail_exits ->
  TR (SPJ segsU (JGv tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).
Proof using Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP TR_callJ CVR CPC CTP REENTER POST.
  intros X tvX rvX rho Hin. unfold tail_exits in Hin. cbn [In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <- <-.
  - apply X_EU_mi.
  - apply X_EU_fv.
  - apply X_EU_mm.
  - apply X_EU_sg.
  - apply X_EU_bk.
Qed.

End Tail.

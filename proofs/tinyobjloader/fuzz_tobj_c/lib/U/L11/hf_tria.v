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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require Import hf_tri_defs hf_vr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import HfAddrU.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition z0T : sv := SLit 0.

Definition tri_cps : list Z :=
  [vrU_entry; pcU_entry; pgU_entry; 0x18abc; 0x193ac; 0x193f4; 0x19394; 0x195c8; tri_K1; VRU.vr_ret;
   tri_K2; tri_J9; 0x199f4; 0x19b88].

Definition tri_vr_leaves (S : sstate) : list sstate :=
  match sym_run segsU FUEL_U tri_cps S true with
  | Some ls => filter (fun st => Z.eqb (ss_pc st) vrU_entry) (map lf_state ls)
  | None => []
  end.

Definition E_trA : sstate := Eval vm_compute in nth 0 (tri_vr_leaves K1_U) K1_U.
Definition E_trB : sstate := Eval vm_compute in nth 1 (tri_vr_leaves K1_U) K1_U.

Definition xs_tr : list xform := [XSplit 1 (SLit (-32))].
Definition E2_tr (E : sstate) : sstate :=
  match TobjJVx.norm_xu xs_tr 1 (-32) E with Some x => x | None => E end.
Definition s_tr (E2 : sstate) : wsub :=
  [(19%positive, SAlu ALU_ADD xD (SLit 32)); (15%positive, t_d tr1); (16%positive, SLit 0);
   (17%positive, t_k tr1); (18%positive, SLit 4)] ++ infer_sub 10 E2 VRU.Pre_vr.

Definition E2_trA : sstate := Eval vm_compute in E2_tr E_trA.
Definition E2_trB : sstate := Eval vm_compute in E2_tr E_trB.
Definition s_trA : wsub := Eval vm_compute in s_tr E2_trA.
Definition s_trB : wsub := Eval vm_compute in s_tr E2_trB.

Definition tria_cuts : list edesc :=
  [(K1_U, tvH, (70, SAlu ALU_SUB pA pK)); (KTbad_U, tvH, (66, z0T)); (KTok_U, tvH, (66, z0T));
   (FT_U, tvH, (66, z0T)); (K2_U, tvH, (64, SAlu ALU_SUB am2 pI)); (J9c_U, tvH, (48, z0T))].
Definition tria_exits : list edesc :=
  [(E_trA, tvH, (68, z0T)); (E_trB, tvH, (68, z0T))].

Section TriA.
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
Hypothesis CVR : forall FBc rho1,
  TR (SPJ segsU (JG_pre segsU C_U Kc VRU.P0_vr FBc VRU.tv0) VRU.Pre_vr rho1)
     (LQP segsU NF rho1 (VRU.Posts_vr Kc FBc)).
Hypothesis REENTER : forall T tv rv rho b, In (T, tv, rv) tria_cuts ->
  0 <= emeas (T, tv, rv) rho /\ emeas (T, tv, rv) rho < b ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv) T rho) (FAM b).

Let XS := X_vr_site Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP CVR tria_cuts REENTER.

Lemma X_E_trA : forall rho,
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tvH) E_trA rho) (FAM (emeas (E_trA, tvH, (68, z0T)) rho)).
Proof.
  intros rho.
  eapply (XS E_trA E2_trA xs_tr 1 (-32) s_trA 7 nz_tr_k KTbad_U FT_U z0T 66 z0T 66 68 z0T 318 320 4 rho).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. tauto.
  - lia.
  - unfold tria_cuts. right. left. reflexivity.
  - unfold tria_cuts. right. right. right. left. reflexivity.
Qed.

Lemma X_E_trB : forall rho,
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tvH) E_trB rho) (FAM (emeas (E_trB, tvH, (68, z0T)) rho)).
Proof.
  intros rho.
  eapply (XS E_trB E2_trB xs_tr 1 (-32) s_trB 7 nz_tr_k KTok_U FT_U z0T 66 z0T 66 68 z0T 318 320 4 rho).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. tauto.
  - lia.
  - unfold tria_cuts. right. right. left. reflexivity.
  - unfold tria_cuts. right. right. right. left. reflexivity.
Qed.

Lemma tria_exits_okT : forall X tvX rvX rho, In (X, tvX, rvX) tria_exits ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).
Proof.
  intros X tvX rvX rho Hin. unfold tria_exits in Hin.
  destruct Hin as [H|[H|[]]]; injection H as <- <- <-.
  - apply X_E_trA.
  - apply X_E_trB.
Qed.

End TriA.

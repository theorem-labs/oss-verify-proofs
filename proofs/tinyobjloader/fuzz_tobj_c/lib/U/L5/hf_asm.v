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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue TobjJV TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs hf_cuts hf_ent.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9.S_vr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10.S_pc.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6.S_pg.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7.S_r2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9.vr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4.pc
  OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6.pg_all.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes.
Import HfAddrU.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module VRU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9.S_vr.
Module PCU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10.S_pc.
Module PGU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6.S_pg.

Ltac argty f := let t := type of f in lazymatch t with forall _ : ?A, _ => exact A end.

Definition hf_cutsU (cutsR : list edesc) : list edesc := ent_cuts ++ cutsR.
Definition hf_exitsU (exitsR : list edesc) : list edesc := ent_exits ++ exitsR.
Definition hf_cpsU (cuts : list edesc) : list Z :=
  [vrU_entry; pcU_entry; pgU_entry] ++ map (fun e => ss_pc (fst (fst e))) cuts.

Definition RegionOK (L exitsR : list edesc) : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation)
    (ML : malloc_laws segsU C_U) (TR : assn -> assn -> Prop) (FAM : Z -> assn)
    (TR_facts : forall J S rho (Q' : assn),
       (Forall (holds rho) (ss_facts S) -> TR (SPJ segsU J S rho) Q') -> TR (SPJ segsU J S rho) Q')
    (TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
       (forall x, TR (SPJ segsU (J x) S rho) Q') -> TR (SPJ segsU (fun r t m => exists x, J x r t m) S rho) Q')
    (TR_pre : forall (P P' Q' : assn), (forall w, P' w -> P w) -> TR P Q' -> TR P' Q')
    (TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn),
       (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q')
    (TR_pureh : forall (X : Prop) (P Q' : assn), (X -> TR P Q') -> TR (fun w => X /\ P w) Q')
    (TR_callP : ltac:(argty (client_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML (fun _ => VRU.P0_vr)
       VRU.Pre_vr VRU.tv0 VRU.PD_vr NF eq_refl TR TR_facts TR_ex TR_pre)))
    (TR_callJ : ltac:(argty (pure_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML TR TR_facts TR_pre)))
    (CVR : forall FBc rho1,
       TR (SPJ segsU (JG_pre segsU C_U Kc VRU.P0_vr FBc VRU.tv0) VRU.Pre_vr rho1)
          (LQP segsU NF rho1 (VRU.Posts_vr Kc FBc)))
    (CPC : forall tv rho rho1,
       TR (SP segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) PCU.Pre_pc_U rho1)
          (LQ segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) NF rho1 PCU.Posts_pc_U))
    (CTP : forall tv rho rho1,
       TR (SP segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) (PGU.Pre_pg_U []) rho1)
          (LQ segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) NF rho1 PGU.Posts_pg_U))
    (REENTER : forall T tv rv rho b, In (T, tv, rv) L ->
       0 <= emeas (T, tv, rv) rho /\ emeas (T, tv, rv) rho < b ->
       TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv) T rho) (FAM b))
    (POST : forall P tv rho b, In (P, JLG segsU C_U Kc (P0_hf FB) FB tv) (Posts_hf_U Kc FB) ->
       TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv) P rho) (FAM b)),
  forall X tvX rvX rho, In (X, tvX, rvX) exitsR ->
    TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).

Definition RegionsOK (cutsR exitsR : list edesc) : Prop := RegionOK (hf_cutsU cutsR) exitsR.

Lemma RegionOK_mono : forall L L' E, incl L L' -> RegionOK L E -> RegionOK L' E.
Proof.
  intros L L' E Hi H Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP TR_callJ CVR CPC CTP
    REENTER POST.
  apply (H Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP TR_callJ CVR CPC CTP); [|exact POST].
  intros T tv rv rho b HT Hb. exact (REENTER T tv rv rho b (Hi _ HT) Hb).
Qed.

Lemma RegionOK_app : forall L E1 E2, RegionOK L E1 -> RegionOK L E2 -> RegionOK L (E1 ++ E2).
Proof.
  intros L E1 E2 H1 H2 Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP TR_callJ CVR CPC CTP
    REENTER POST X tvX rvX rho Hin.
  apply in_app_or in Hin as [Hin|Hin].
  - exact (H1 Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP TR_callJ CVR CPC CTP
             REENTER POST X tvX rvX rho Hin).
  - exact (H2 Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP TR_callJ CVR CPC CTP
             REENTER POST X tvX rvX rho Hin).
Qed.

Section Asm.
Variables cutsR exitsR : list edesc.
Hypothesis EJ : ejcert segsU NP FUEL_U (hf_cpsU (hf_cutsU cutsR)) NP (hf_cutsU cutsR) (hf_exitsU exitsR) = true.
Hypothesis XR : RegionsOK cutsR exitsR.

Section SumT.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segsU C_U.
Let JGv (tv : list (sv * sv)) : jpred := JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv.
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
  TR (SP segsU (fun tr md => JGv tv rho tr md) PCU.Pre_pc_U rho1)
     (LQ segsU (fun tr md => JGv tv rho tr md) NF rho1 PCU.Posts_pc_U).
Hypothesis CTP : forall tv rho rho1,
  TR (SP segsU (fun tr md => JGv tv rho tr md) (PGU.Pre_pg_U []) rho1)
     (LQ segsU (fun tr md => JGv tv rho tr md) NF rho1 PGU.Posts_pg_U).
Hypothesis REENTER : forall T tv rv rho b, In (T, tv, rv) (hf_cutsU cutsR) ->
  0 <= emeas (T, tv, rv) rho /\ emeas (T, tv, rv) rho < b -> TR (SPJ segsU (JGv tv) T rho) (FAM b).
Hypothesis POST : forall P tv rho b, In (P, JLG segsU C_U Kc (P0_hf FB) FB tv) (Posts_hf_U Kc FB) ->
  TR (SPJ segsU (JGv tv) P rho) (FAM b).

Lemma exits_okT : forall X tvX rvX rho, In (X, tvX, rvX) (hf_exitsU exitsR) ->
  TR (SPJ segsU (JGv tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).
Proof using XR ML TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP TR_callJ CVR CPC CTP REENTER POST.
  intros X tvX rvX rho Hin. unfold hf_exitsU in Hin. apply in_app_or in Hin as [Hin|Hin].
  - exact (ent_exits_okT Kc FB rho0 TR FAM POST X tvX rvX rho Hin).
  - exact (XR Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP TR_callJ CVR CPC CTP
             REENTER POST X tvX rvX rho Hin).
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis MC : malloc_contracts segsU C_U EC_U.
Hypothesis ML : malloc_laws segsU C_U.

Let nI : forall n : sstate * list (sv * sv), jnode := nodeI segsU C_U NP Kc rho0 (P0_hf FB) FB.
Let Q : assn := LQP segsU NP rho0 (Posts_hf_U Kc FB).

Theorem handle_f_sum_gen :
  triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc (P0_hf FB) FB tv_pre) (Pre_hf HF_U) rho0) Q.
Proof using EJ XR HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segsU C_U NP Kc rho0 (P0_hf FB) FB ML FUEL_U (hf_cpsU (hf_cutsU cutsR)) NP
                (hf_cutsU cutsR) (hf_exitsU exitsR) ok Q (proj1 HS)
                (ejcert_jcert segsU NP _ _ _ _ _ EJ)) with (rvT := (100, z0));
         [| apply in_or_app; left; left; reflexivity].
       apply (exits_okT Kc FB rho0 ML (triple segsU ok)
                (fun _ w => SPfamGJ segsU (map nI (map (@edrop) (hf_cutsU cutsR))) w \/ Q w)
                (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
                (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segsU ok A P Q' H)
                (triple_pureh segsU ok)
                (call_soundP segsU ok) (call_soundJ segsU ok)).
       - intros FBc rho1. apply (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9.vr.vr_sum ok Kc FBc rho1 HS ML MC).
       - intros tv rho rho1. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4.pc.parse_corner_sum_U.
         eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & _ & HK & _). exact HK.
       - intros tv rho rho1. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6.pg_all.tess_polygon_U.
         eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & _ & HK & _). exact HK.
       - intros T tv rv rho b Hin _.
         exact (reenter_cutGE segsU C_U NP Kc rho0 (P0_hf FB) FB ok (hf_cutsU cutsR) T tv rv Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segsU C_U NP Kc (P0_hf FB) FB ok rho0 tv (Posts_hf_U Kc FB) P).
         exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.
Section Existence.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.
Hypothesis ML : malloc_laws segsU C_U.
Hypothesis R2X : OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7.S_r2.r2_sum_ex_stmt_U.

Let Q : assn := LQP segsU NP rho0 (Posts_hf_U Kc FB).

Theorem handle_f_sum_ex_gen :
  etriple segsU (SPJ segsU (JG_pre segsU C_U Kc (P0_hf FB) FB tv_pre) (Pre_hf HF_U) rho0) Q.
Proof using EJ XR Hvi MCX ML R2X.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segsU C_U NP Kc rho0 (P0_hf FB) FB ML FUEL_U (hf_cpsU (hf_cutsU cutsR)) NP
                (hf_cutsU cutsR) (hf_exitsU exitsR) Q EJ) with (rvT := (100, z0));
         [| apply in_or_app; left; left; reflexivity].
       apply (exits_okT Kc FB rho0 ML (etriple segsU)
                (fun b w => SPfamEJ segsU (map (enodeI segsU C_U NP Kc rho0 (P0_hf FB) FB) (hf_cutsU cutsR)) b w
                            \/ Q w)
                (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
                (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segsU A P Q' H)
                (etriple_pureh segsU)
                (call_completeP segsU) (call_completeJ segsU)).
       - intros FBc rho1. apply (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9.vr.vr_sum_ex Kc FBc rho1 Hvi ML MCX).
       - intros tv rho rho1. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4.pc.parse_corner_sum_ex_U.
       - intros tv rho rho1. apply (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6.pg_all.tess_polygon_ex_U R2X).
       - intros T tv rv rho b Hin Hm.
         exact (ereenter_cutE segsU C_U NP Kc rho0 (P0_hf FB) FB (hf_cutsU cutsR) T tv rv Q b rho Hin Hm).
       - intros P tv rho b Hin. apply (eexit_postG segsU C_U NP Kc (P0_hf FB) FB rho0 tv (Posts_hf_U Kc FB) P).
         exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Asm.

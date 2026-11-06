(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7j OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunNs OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Le OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Ld. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHypR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7j OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvOpsCI3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La.BoAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8xp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS1.BoAllocMIm OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Rm.BoAllocM8g OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Rm.BoAllocM8h OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunNs.BoAllocM8n OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Le.BoAllocM8Lb OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Ld OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Le.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | hs_am_lia ].   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).





Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod8_of_64k : forall x, x mod 2 ^ 16 = 0 -> x mod 8 = 0.
Proof. intros x Hx. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition liftable (K : config -> Prop) : Prop :=
  forall (Hd : word -> bool), H_off_segments BSEGS Hd -> wx_segs_nowrap BSEGS ->
  forall (A : list (Z * Z)) regs (pc : word) r (pc' : word) (M M' rom : mem) (model : Model),
    msteps BSEGS (mkst regs pc (mrestrict Hd M) rom) (mkst r pc' (mrestrict Hd M') rom) ->
    (forall a : word, Hd a = true -> M' a = M a) ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall mdlm, same_but_materialized model mdlm -> MInv A mdlm -> K (mkCfg (mkst r pc' M' rom) mdlm)) ->
    K (mkCfg (mkst regs pc M rom) model).
(* [comment removed for export] *)
Definition s_regs (r : bvmap 5 word) (g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word) : Prop :=
  getr r 18 = g2 /\ getr r 19 = g3 /\ getr r 20 = g4 /\ getr r 21 = g5 /\ getr r 22 = g6 /\ getr r 23 = g7 /\ getr r 24 = g8 /\ getr r 25 = g9
  /\ getr r 26 = g10 /\ getr r 27 = g11.

(* [comment removed for export] *)
Lemma refill_cache_ne : forall (st : ast) (c m : Z), 1 <= m <= Z.of_nat (length (r_free (a_reg st c))) -> a_cache (op_refill st c m) c <> [].
Proof using.
  intros st c m Hm E. unfold op_refill, set_cache in E. cbn in E. unfold fupdZ in E. rewrite Z.eqb_refl in E.
  apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn [length] in E. lia.
Qed.

Lemma liftable_katD : forall Q, liftable (fun cf => katD BSEGS cf Q).
Proof using. intros Q Hd HO WX A regs pc r pc' M M' rom model. apply (lift_katD_mem Hd HO WX). Qed.
Lemma liftable_katwD : forall Qok Qf, liftable (fun cf => katwD BSEGS cf Qok Qf).
Proof using. intros Qok Qf Hd HO WX A regs pc r pc' M M' rom model. apply (lift_katwD_mem Hd HO WX). Qed.
Lemma liftable_katsD : forall Qok Qf, liftable (fun cf => katsD BSEGS cf Qok Qf).
Proof using.
  intros Qok Qf Hd HO WX A regs pc r pc' M M' rom model RUN SAME HALT LC AWF MI CONT.
  apply (katsD_msteps_acct BSEGS Hd HO WX A (mkst regs pc M rom) (mkst r pc' (mrestrict Hd M') rom) model Qok Qf LC AWF MI HALT).
  { rewrite mk_restrict_mkst. exact RUN. }
  intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
  replace (RiscvSemantics.ms_mem (mkst regs pc M rom)) with M by reflexivity.
  rewrite (mk_munrestrict_same Hd M M' SAME). exact (CONT mdlm SBMm MIm).
Qed.

Section L3.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Variable X : Z -> Prop.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation XL := (XL bt X).
  #[local] Abbreviation IA := (bt_ia bt).

  (* [comment removed for export] *)
  Lemma repx_widen_step : forall (Y Z0 : Z -> Prop) (Zd : Xdec Z0) st Lc FF (M M' : mem) mdl mdl',
    WF bt st Lc FF -> RepX bt Y st Lc FF M mdl ->
    (forall a : word, M' a <> M a -> (Z0 (U a) \/ ~ rep_cells bt st Lc FF (U a)) /\ M' a <> None) ->
    (forall a : word, Z0 (U a) -> M' a <> None) ->
    MInv (a_aa st) mdl' -> same_but_materialized mdl mdl' ->
    RepX bt (fun z => Y z \/ Z0 z) st Lc FF M' mdl'.
  Proof using.
    intros Y Z0 Zd st Lc FF M M' mdl mdl' W (M0 & R & D) CH ZDEF MI SBM.
    set (M0' := fun a : word => if Zd (U a) then M0 a else if decide (M a = M0 a) then M' a else M0 a).
    exists M0'. split.
    - apply (Rep_sbm bt st Lc FF M0' mdl mdl'); [| exact MI | exact SBM].
      apply (Rep_frame bt st Lc FF M0 M0' mdl W R). intros a Ha. unfold M0' in Ha |- *.
      destruct (Zd (U a)) as [HZ | NZ]; [exfalso; exact (Ha eq_refl)|].
      destruct (decide (M a = M0 a)) as [E | NE]; [| exfalso; exact (Ha eq_refl)].
      rewrite <- E in Ha. destruct (CH a Ha) as [[F | F] Dd]; [exfalso; exact (NZ F) | exact (conj F Dd)].
    - intros a Ha. unfold M0' in Ha.
      destruct (Zd (U a)) as [HZ | NZ]; [split; [right; exact HZ | exact (ZDEF a HZ)]|].
      destruct (decide (M a = M0 a)) as [E | NE]; [exfalso; exact (Ha eq_refl)|].
      destruct (D a NE) as [HY Dd]. split; [left; exact HY|].
      destruct (decide (M' a = M a)) as [E2 | NE2]; [rewrite E2; exact Dd | exact (proj2 (CH a NE2))].
  Qed.

  (* [comment removed for export] *)
  Definition gf_inv (M : mem) (c : Z) (spR raR s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word) : Prop :=
    rdn BSEGS M (Z_to_bv 64 (reginfo bt c)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60)))
    /\ (forall (k : Z) (v : word),
          In (k, v) [(-8, g_ra); (-16, g0); (-24, g1); (-32, g2); (-40, g3); (-48, g4); (-56, g5); (-64, g6); (-72, g7); (-80, g8); (-88, g9); (-96, g10); (-104, g11)] ->
          rdn BSEGS M (at_ (at_ spR (-32)) k) 8 = Some (LE8 v))
    /\ (forall (k : Z) (v : word), In (k, v) [(-8, raR); (-16, s0R); (-24, s1R)] -> rdn BSEGS M (at_ spR k) 8 = Some (LE8 v)).

  (* [comment removed for export] *)
  Lemma repx_step_widen : forall (Y Z0 FOOT : Z -> Prop) (Zd : Xdec Z0) st st' Lc Lc' FF FF' (M M' : mem) mdl mdl',
    RepX bt Y st Lc FF M mdl ->
    (forall a : word, M' a <> M a -> (Z0 (U a) \/ FOOT (U a)) /\ M' a <> None) ->
    (forall a : word, Z0 (U a) -> M' a <> None) ->
    (forall M0 M0' : mem, Rep bt st Lc FF M0 mdl ->
        (forall a : word, M a <> M0 a -> Y (U a) /\ M a <> None) ->
        (forall a : word, M0' a <> M0 a -> FOOT (U a) /\ ~ Z0 (U a) /\ M0' a <> None) ->
        (forall a : word, ~ Y (U a) -> ~ Z0 (U a) -> M0' a = M' a) ->
        (forall a : word, Z0 (U a) -> M0' a = M0 a) ->
        Rep bt st' Lc' FF' M0' mdl') ->
    RepX bt (fun z => Y z \/ Z0 z) st' Lc' FF' M' mdl'.
  Proof using.
    intros Y Z0 FOOT Zd st st' Lc Lc' FF FF' M M' mdl mdl' (M0 & R & D) CH ZDEF STEP.
    set (M0' := fun a : word => if Zd (U a) then M0 a else if decide (M a = M0 a) then M' a else M0 a).
    exists M0'. split.
    - apply (STEP M0 M0' R D).
      + intros a Ha. unfold M0' in Ha |- *. destruct (Zd (U a)) as [HZ | NZ]; [exfalso; exact (Ha eq_refl)|].
        destruct (decide (M a = M0 a)) as [E | NE]; [| exfalso; exact (Ha eq_refl)].
        rewrite <- E in Ha. destruct (CH a Ha) as [[F | F] Dd]; [exfalso; exact (NZ F) | exact (conj F (conj NZ Dd))].
      + intros a NY NZ. (lazymatch goal with |- ?G => let G' := eval unfold M0' in G in change_no_check G' end). destruct (Zd (U a)) as [HZ | _]; [exfalso; exact (NZ HZ)|].
        destruct (decide (M a = M0 a)) as [_ | NE]; [reflexivity | exfalso; exact (NY (proj1 (D a NE)))].
      + intros a HZ. (lazymatch goal with |- ?G => let G' := eval unfold M0' in G in change_no_check G' end). destruct (Zd (U a)) as [_ | NZ]; [reflexivity | exfalso; exact (NZ HZ)].
    - intros a Ha. unfold M0' in Ha.
      destruct (Zd (U a)) as [HZ | NZ]; [split; [right; exact HZ | exact (ZDEF a HZ)]|].
      destruct (decide (M a = M0 a)) as [E | NE]; [exfalso; exact (Ha eq_refl)|].
      destruct (D a NE) as [HY Dd]. split; [left; exact HY|].
      destruct (decide (M' a = M a)) as [E2 | NE2]; [rewrite E2; exact Dd | exact (proj2 (CH a NE2))].
  Qed.


  Theorem refill_head_K :
    forall (K : config -> Prop), liftable K ->
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR tp gp : word),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt X st Lc FF M mdl -> m_halted mdl = None ->
    a_cinit st = true -> a_cache st c = [] ->
    let r := a_reg st c in let nf := Z.of_nat (length (r_free r)) in
    nf < cache_hint c ->
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (T <= z < T + 2768)) ->
    getr regs 1 = raR -> getr regs 2 = spR -> getr regs 4 = tp -> getr regs 3 = gp -> getr regs 10 = Z_to_bv 64 (T + T_PC) -> getr regs 11 = Z_to_bv 64 (T + T_PC + PC_SZ * c) ->
    getr regs 12 = Z_to_bv 64 0x10ab58 -> getr regs 13 = Z_to_bv 64 c ->
    (CEIL + 160 <= U spR /\ U spR + 16 <= 2 ^ 47) ->
    writableZ BSEGS M (U spR - 160) (U spR) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        RepX bt (XL c) st Lc FF M' mdl' -> same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
        (forall a : word, M' a <> M a -> ((U spR - 160 <= U a < U spR) \/ (reginfo bt c <= U a < reginfo bt c + 8)) /\ M' a <> None) ->
        gf_inv M' c spR raR (getr regs 8) (getr regs 9) (Z_to_bv 64 0x5147c) (Z_to_bv 64 (T + T_PC + PC_SZ * c)) (Z_to_bv 64 (cache_hint c))
               (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ->
        gfp_regs (at_ spR (-32)) (Z_to_bv 64 (T + T_PC + PC_SZ * c + 16)) (reginfo bt c) SBEG c (cache_hint c) r' ->
        getr r' 1 = Z_to_bv 64 0x517f8 -> getr r' 10 = Z_to_bv 64 0x10ab58 -> getr r' 11 = at_ (Z_to_bv 64 T) 2768 -> getr r' 12 = Z_to_bv 64 c ->
        getr r' 13 = Z_to_bv 64 (reginfo bt c) -> getr r' 14 = Z_to_bv 64 (cache_hint c - nf) -> getr r' 4 = tp -> getr r' 3 = gp ->
        K (mkCfg (mkst r' (0x51844%bv : word) M' rom) mdl')) ->
    K (mkCfg (mkst regs (0x5143c%bv : word) M rom) mdl).
  Proof using PCELLS CELLS MIDEND FL PGP TSDP TP BT_ia BT_segs.
    intros K LK c st Lc FF M rom mdl regs spR raR tp gp Hc W RX HALT CINIT HC0 r nf NF XOFF H1 H2 H4 H3 H10 H11 H12 H13 Hsp WSTK CONT.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range spR) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _). fold nf in E7.
    pose proof (pk_thread_geom bt BT_ia st Lc FF W) as (T1 & T2 & C1 & C2 & T4k & TIMG & CIMG).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (TBAND & CBAND & TSP & CSP & S1 & S2 & S3).
    pose proof CELLS as CREST. do 18 (destruct CREST as (_ & CREST)). destruct CREST as (CELL_sbeg & _).
    pose proof PCELLS as (_ & PC_rib & _).
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    destruct R3 as (_ & _ & _ & _ & _ & _ & _ & TPC & _). destruct (TPC c Hc) as (P1 & P2 & P3 & P4). rewrite CINIT in P2.
    destruct (R4 c Hc) as [(G0 & G8 & G16 & _ & _ & _ & _ & _ & _ & GW) _]. fold r nf in G16.
    rewrite BT_segs in *. destruct R14 as (Bw1 & Bw2 & _).
    unfold KSPACE, PG, AS_HEAPLO, T_PC, PC_SZ in *.
    set (RIz := reginfo bt c) in *. assert (ERI : RIz = SBEG + 2 ^ 37 + 128 * c) by reflexivity.
    set (h := cache_hint c) in *.
    assert (Hh : 1 <= h <= 8) by ((lazymatch goal with |- ?G => let G' := eval unfold h, cache_hint in G in change_no_check G' end); lia).
    assert (EMC : cache_max c = 2 * h) by reflexivity.
    assert (EMC2 : cache_max c / 2 = h) by (rewrite EMC, Z.mul_comm; apply Z.div_mul; lia).
    destruct (pos_mod4096 T T1 T4k) as [T4 T8].
    (* [comment removed for export] *)
    assert (YIMG : forall z, X z -> ~ (AIMGLO <= z < AIMGHI)) by (intros z Hz; exact (proj1 (proj2 (XOFF z Hz)))).
    assert (XRI : forall i, RIz <= i < RIz + 128 -> ~ X i) by (intros i Hi Hx; exact (proj1 (XOFF i Hx) Hi)).
    assert (XT : forall i, T <= i < T + 2768 -> ~ X i) by (intros i Hi Hx; exact (proj2 (proj2 (XOFF i Hx)) Hi)).
    (* [comment removed for export] *)
    assert (KMC : rdn BSEGS M (Z_to_bv 64 (T + 208 + 80 * c + 4)) 4 = Some (LE4 (cache_max c)))
      by (apply (repx_rd X M M0 D _ 4 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XT; cbn in Hi; lia | exact P2]).
    assert (KSB := pk_const bt BT_segs X st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_sbeg ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (KRIB := pk_const bt BT_segs X st Lc FF M M0 mdl RP D YIMG _ _ _ PC_rib ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)). unfold KSPACE in KRIB.
    assert (KMTX : rdn BSEGS M (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0)))
      by (apply (repx_rd X M M0 D RIz 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G0]).
    assert (KNF : rdn BSEGS M (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)))
      by (apply (repx_rd X M M0 D (RIz + 16) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G16]).
    assert (WRI : writableZ BSEGS M RIz (RIz + 128)) by (apply (repx_wr X M M0 D); [lia | lia | exact GW]).
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (pk_nolazy_rt bt st Lc FF M0 mdl W RP z). left. exact Hz. }
    assert (HOFF : forall lo0 n, (forall z, lo0 <= z < lo0 + n -> Hd (Z_to_bv 64 z) = false) -> hid_off Hd lo0 n).
    { intros lo0 n Hz x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    set (Mr := mrestrict Hd M).
    assert (RDM : forall z (k : nat) v, 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> Hd (Z_to_bv 64 i) = false) ->
               rdn BSEGS M (Z_to_bv 64 z) k = Some v -> rdn BSEGS Mr (Z_to_bv 64 z) k = Some v).
    { intros z k v Z0 Z1 Hh0 Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hr | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; apply HOFF; exact Hh0]. }
    set (cache := Z_to_bv 64 (T + 208) : word). set (pc := Z_to_bv 64 (T + 208 + 80 * c) : word).
    assert (Ucache : U cache = T + 208) by ((lazymatch goal with |- ?G => let G' := eval unfold cache in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Upc : U pc = T + 208 + 80 * c) by ((lazymatch goal with |- ?G => let G' := eval unfold pc in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    (* [comment removed for export] *)
    destruct (rf_pro BSEGS ARB both_HRF regs Mr rom raR spR cache pc (Z_to_bv 64 0x10ab58) c (cache_max c) H1 H2 H10 H11 H12 H13
                ltac:(rewrite EMC; split; [lia | rewrite Z.mul_comm; apply Z_mod_mult])
                ltac:((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); rewrite store_ok_mrestrict; [apply (writableZ_sok M (U spR - 160) (U spR)); [exact WSTK | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia]
                                                             | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHs; lia])
                ltac:(lia) ltac:(rewrite Ucache, Upc; lia)
                ltac:(replace (at_ pc 4) with (Z_to_bv 64 (T + 208 + 80 * c + 4)) by (apply bv_eq; rewrite at_u by lia; rewrite Upc, u_Z2bv by lia; reflexivity);
                      apply RDM; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHrt; cbn in Hi; lia | exact KMC]))
      as (r1 & RUN1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & AG1).
    set (MR1 := rf_m1 regs Mr raR spR) in *.
    set (spG := at_ spR (-32)) in *.
    assert (UspG : U spG = U spR - 32) by ((lazymatch goal with |- ?G => let G' := eval unfold spG in G in change_no_check G' end); rewrite at_u by lia; lia).
    assert (OUT1 : forall x : word, (U x < U spR - 32 \/ U spR <= U x) -> MR1 x = Mr x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MR1 in G in change_no_check G' end). apply (rf_m1_outside ARB regs Mr raR spR ltac:(lia) x Hx). }
    assert (RD1 : forall z (k : nat) v, 0 <= z -> z + Z.of_nat k <= CEIL -> (forall i, z <= i < z + Z.of_nat k -> Hd (Z_to_bv 64 i) = false) ->
               rdn BSEGS M (Z_to_bv 64 z) k = Some v -> rdn BSEGS MR1 (Z_to_bv 64 z) k = Some v).
    { intros z k v Z0 Z1 Hh0 Hr. rewrite <- (RDM z k v Z0 ltac:(lia) Hh0 Hr). apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. apply OUT1. lia. }
    assert (SBEG8 : SBEG mod 8 = 0).
    { pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16). exact (mod8_of_64k _ S16). }
    assert (NI : forall i : reg, In i [18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv; 4%bv; 3%bv] -> getr r1 i = getr regs i).
    { intros i Hi. apply AG1. cbn [In] in Hi |- *. intros Xi. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi|]). exact Hi. }
    destruct (gfp_pre MR1 rom spG (at_ ARB 0x5147c) pc (Z_to_bv 64 (cache_max c / 2)) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (at_ cache 2560) (at_ pc 16) SBEG c (cache_max c / 2) nf r1
                A1 A2 A10 A11 A12 A13 A14 A8 A9
                (NI 18%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 19%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 20%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 21%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12))
                (NI 22%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 23%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 24%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 25%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12))
                (NI 26%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 27%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12))
                ltac:(rewrite UspG; lia) Hc ltac:(rewrite EMC2; lia) ltac:(split; [lia | split; [lia | exact SBEG8]]) ltac:(rewrite UspG; lia))
      as (r2 & RUN2 & GR & B1 & B10 & B11 & B12 & B13 & B14 & AG2).
    - (* [comment removed for export] *) eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold MR1 in G in change_no_check G' end); apply rf_m1_grows|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end).
      rewrite store_ok_mrestrict; [ | rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                    | rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHs; lia].
      apply (writableZ_sok M (U spR - 160) (U spR)); [exact WSTK | rewrite at_u by (rewrite UspG; lia); rewrite UspG; lia | rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHs; cbn in Hi; lia | exact KSB].
    - apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHs; cbn in Hi; lia | exact KRIB].
    - apply (RD1 RIz 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHri; cbn in Hi; lia | exact KMTX].
    - apply (RD1 (RIz + 16) 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHri; cbn in Hi; lia | exact KNF].
    - eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold MR1 in G in change_no_check G' end); apply rf_m1_grows|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end).
      rewrite store_ok_mrestrict; [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHri; lia].
      apply (writableZ_sok M RIz (RIz + 128)); [exact WRI | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - (* [comment removed for export] *)
      rewrite EMC2 in *.
      set (M' := r1_mem M spR raR (getr regs 8) (getr regs 9) (at_ ARB 0x5147c) pc (Z_to_bv 64 h) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                   (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) RIz).
      assert (EMEM : gfp_m1 MR1 spG (at_ ARB 0x5147c) pc (Z_to_bv 64 h) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                       (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (SBEG + 2 ^ 37 + 128 * c) = mrestrict Hd M').
      { (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). rewrite <- (r1_mem_mrestrict M spR raR (getr regs 8) (getr regs 9) (at_ ARB 0x5147c) pc (Z_to_bv 64 h) (getr regs 18) (getr regs 19) (getr regs 20)
                               (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) RIz ltac:(lia) ltac:(lia) Hd
                               ltac:(apply HOFF; intros z Hz; apply NHs; lia) ltac:(apply HOFF; intros z Hz; apply NHri; lia)).
        reflexivity. }
      rewrite EMEM in RUN2.
      rewrite (ARB_lit8 0x5153c) in RUN1 by lia. rewrite (ARB_lit8 0x5143c) in RUN1 by lia.
      replace (Z_to_bv 64 0x5153c : word) with (0x5153c%bv : word) in RUN1 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x5143c : word) with (0x5143c%bv : word) in RUN1 by (apply bv_eq; reflexivity).
      apply (LK Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st) regs _ r2 _ M M' rom mdl (msteps_trans _ _ _ _ RUN1 RUN2)); [ | exact HALT | apply lazy_cover_HID | exact Bw1 | exact Bw2 | ].
      + intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r1_mem_outside; [lia | lia | | ].
        * pose proof (hid_true_off Hd a (U spR - 160) 160 Ha ltac:(apply HOFF; intros z Hz; apply NHs; lia)). lia.
        * pose proof (hid_true_off Hd a RIz 8 Ha ltac:(apply HOFF; intros z Hz; apply NHri; lia)). lia.
      + intros mdlm SBM MIm.
        assert (FOOTM : forall a : word, M' a <> M a -> ((U spR - 160 <= U a < U spR) \/ (RIz <= U a < RIz + 8)) /\ M' a <> None).
        { intros a Ha.
          assert (IN : ((U spR - 160 <= U a < U spR) \/ (RIz <= U a < RIz + 8)) \/ ((U a < U spR - 160 \/ U spR <= U a) /\ (U a < RIz \/ RIz + 8 <= U a))) by (clear; lia).
          destruct IN as [IN | [O1 O2]]; [| exfalso; apply Ha; (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end); apply r1_mem_outside; [lia | lia | exact O1 | exact O2]].
          split; [exact IN|]. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r1_mem_grows.
          destruct IN as [I1 | I2]; [destruct (WSTK (U a) I1) as [Dd _] | destruct (WRI (U a) ltac:(lia)) as [Dd _]]; rewrite Z_to_bv_bv_unsigned in Dd; exact Dd. }
        destruct GR as (G2 & G8' & G9' & G18 & G19 & G20 & G21 & G22).
        apply (CONT r2 M' mdlm).
        * apply (repx_widen_step X (fun z => RIz <= z < RIz + 8) (Xdec_iv RIz (RIz + 8)) st Lc FF M M' mdl mdlm W RX); [ | | exact MIm | exact SBM].
          -- intros a Ha. destruct (FOOTM a Ha) as [[F | F] Dd]; (split; [| exact Dd]); [right | left; exact F].
             intros RCa. pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U a) W RCa). lia.
          -- intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r1_mem_grows. destruct (WRI (U a) ltac:(lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd.
        * exact SBM.
        * exact MIm.
        * exact FOOTM.
        * (lazymatch goal with |- ?G => let G' := eval unfold gf_inv in G in change_no_check G' end). fold RIz. split; [| split].
          -- (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r1_mem_lock; lia.
          -- intros k v Hin. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r1_mem_gslots; [lia | lia |]. rewrite (ARB_lit8 0x5147c) by lia. exact Hin.
          -- intros k v Hin. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r1_mem_rslots; [lia | lia | exact Hin].
        * (lazymatch goal with |- ?G => let G' := eval unfold gfp_regs in G in change_no_check G' end). fold RIz. rewrite ERI. unfold pc in G21. replace (at_ (Z_to_bv 64 (T + 208 + 80 * c)) 16) with (Z_to_bv 64 (T + 208 + 80 * c + 16)) in G21
            by (apply bv_eq; rewrite at_u by (rewrite u_Z2bv by lia; lia); rewrite !u_Z2bv by lia; reflexivity).
          repeat split; assumption.
        * exact B1.
        * exact B10.
        * rewrite B11. (lazymatch goal with |- ?G => let G' := eval unfold cache in G in change_no_check G' end). apply bv_eq. rewrite !at_u by (rewrite ?u_Z2bv by lia; lia). rewrite !u_Z2bv by lia. lia.
        * exact B12.
        * rewrite B13. rewrite ERI. reflexivity.
        * exact B14.
        * rewrite (AG2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). rewrite (NI 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12). exact H4.
        * rewrite (AG2 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). rewrite (NI 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 13). exact H3.
  Qed.



  Theorem refill_head0_K :
    forall (K : config -> Prop), liftable K ->
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR tp gp : word),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt X st Lc FF M mdl -> m_halted mdl = None ->
    a_cinit st = false -> a_cache st c = [] ->
    let r := a_reg st c in let nf := Z.of_nat (length (r_free r)) in
    nf < cache_hint c ->
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (T <= z < T + 2768)) ->
    getr regs 1 = raR -> getr regs 2 = spR -> getr regs 4 = tp -> getr regs 3 = gp -> getr regs 10 = Z_to_bv 64 (T + T_PC) -> getr regs 11 = Z_to_bv 64 (T + T_PC + PC_SZ * c) ->
    getr regs 12 = Z_to_bv 64 0x10ab58 -> getr regs 13 = Z_to_bv 64 c ->
    (CEIL + 160 <= U spR /\ U spR + 16 <= 2 ^ 47) ->
    writableZ BSEGS M (U spR - 160) (U spR) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        WF bt (op_cache_init st) Lc FF -> RepX bt (XL c) (op_cache_init st) Lc FF M' mdl' -> same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
        (forall a : word, M' a <> M a -> ((U spR - 160 <= U a < U spR) \/ (reginfo bt c <= U a < reginfo bt c + 8) \/ (T + T_PC + 84 <= U a < T + T_PC + 2496)) /\ M' a <> None) ->
        gf_inv M' c spR raR (getr regs 8) (getr regs 9) (Z_to_bv 64 0x5147c) (Z_to_bv 64 (T + T_PC + PC_SZ * c)) (Z_to_bv 64 (cache_hint c))
               (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ->
        gfp_regs (at_ spR (-32)) (Z_to_bv 64 (T + T_PC + PC_SZ * c + 16)) (reginfo bt c) SBEG c (cache_hint c) r' ->
        getr r' 1 = Z_to_bv 64 0x517f8 -> getr r' 10 = Z_to_bv 64 0x10ab58 -> getr r' 11 = at_ (Z_to_bv 64 T) 2768 -> getr r' 12 = Z_to_bv 64 c ->
        getr r' 13 = Z_to_bv 64 (reginfo bt c) -> getr r' 14 = Z_to_bv 64 (cache_hint c - nf) -> getr r' 4 = tp -> getr r' 3 = gp ->
        K (mkCfg (mkst r' (0x51844%bv : word) M' rom) mdl')) ->
    K (mkCfg (mkst regs (0x5143c%bv : word) M rom) mdl).
  Proof using PCELLS CELLS MIDEND FL PGP TSDP TP BT_ia BT_segs.
    intros K LK c st Lc FF M rom mdl regs spR raR tp gp Hc W RX HALT CINIT HC0 r nf NF XOFF H1 H2 H4 H3 H10 H11 H12 H13 Hsp WSTK CONT.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range spR) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _). fold nf in E7.
    pose proof (pk_thread_geom bt BT_ia st Lc FF W) as (T1 & T2 & C1 & C2 & T4k & TIMG & CIMG).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (TBAND & CBAND & TSP & CSP & S1 & S2 & S3).
    pose proof CELLS as CREST. do 18 (destruct CREST as (_ & CREST)). destruct CREST as (CELL_sbeg & _).
    pose proof PCELLS as (_ & PC_rib & _).
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    pose proof R3 as (_ & _ & _ & _ & _ & _ & _ & TPC & _). destruct (TPC c Hc) as (P1 & P2 & P3 & P4). rewrite CINIT in P2.
    destruct R3 as (_ & _ & _ & _ & _ & _ & _ & _ & TW & _).
    destruct (R4 c Hc) as [(G0 & G8 & G16 & _ & _ & _ & _ & _ & _ & GW) _]. fold r nf in G16.
    rewrite BT_segs in *. destruct R14 as (Bw1 & Bw2 & _).
    unfold KSPACE, PG, AS_HEAPLO, T_PC, PC_SZ in *.
    set (RIz := reginfo bt c) in *. assert (ERI : RIz = SBEG + 2 ^ 37 + 128 * c) by reflexivity.
    set (h := cache_hint c) in *.
    assert (Hh : 1 <= h <= 8) by ((lazymatch goal with |- ?G => let G' := eval unfold h, cache_hint in G in change_no_check G' end); lia).
    assert (EMC : cache_max c = 2 * h) by reflexivity.
    assert (EMC2 : cache_max c / 2 = h) by (rewrite EMC, Z.mul_comm; apply Z.div_mul; lia).
    destruct (pos_mod4096 T T1 T4k) as [T4 T8].
    (* [comment removed for export] *)
    assert (YIMG : forall z, X z -> ~ (AIMGLO <= z < AIMGHI)) by (intros z Hz; exact (proj1 (proj2 (XOFF z Hz)))).
    assert (XRI : forall i, RIz <= i < RIz + 128 -> ~ X i) by (intros i Hi Hx; exact (proj1 (XOFF i Hx) Hi)).
    assert (XT : forall i, T <= i < T + 2768 -> ~ X i) by (intros i Hi Hx; exact (proj2 (proj2 (XOFF i Hx)) Hi)).
    (* [comment removed for export] *)
    assert (KMC : rdn BSEGS M (Z_to_bv 64 (T + 208 + 80 * c + 4)) 4 = Some (LE4 0))
      by (apply (repx_rd X M M0 D _ 4 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XT; cbn in Hi; lia | exact P2]).
    assert (KSB := pk_const bt BT_segs X st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_sbeg ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (KRIB := pk_const bt BT_segs X st Lc FF M M0 mdl RP D YIMG _ _ _ PC_rib ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)). unfold KSPACE in KRIB.
    assert (KMTX : rdn BSEGS M (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0)))
      by (apply (repx_rd X M M0 D RIz 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G0]).
    assert (KNF : rdn BSEGS M (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)))
      by (apply (repx_rd X M M0 D (RIz + 16) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G16]).
    assert (WRI : writableZ BSEGS M RIz (RIz + 128)) by (apply (repx_wr X M M0 D); [lia | lia | exact GW]).
    assert (WT : writableZ BSEGS M T (T + 4096)) by (apply (repx_wr X M M0 D); [lia | lia | exact TW]).
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (pk_nolazy_rt bt st Lc FF M0 mdl W RP z). left. exact Hz. }
    assert (HOFF : forall lo0 n, (forall z, lo0 <= z < lo0 + n -> Hd (Z_to_bv 64 z) = false) -> hid_off Hd lo0 n).
    { intros lo0 n Hz x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    set (Mr := mrestrict Hd M).
    assert (RDM : forall z (k : nat) v, 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> Hd (Z_to_bv 64 i) = false) ->
               rdn BSEGS M (Z_to_bv 64 z) k = Some v -> rdn BSEGS Mr (Z_to_bv 64 z) k = Some v).
    { intros z k v Z0 Z1 Hh0 Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hr | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; apply HOFF; exact Hh0]. }
    set (cache := Z_to_bv 64 (T + 208) : word). set (pc := Z_to_bv 64 (T + 208 + 80 * c) : word).
    assert (Ucache : U cache = T + 208) by ((lazymatch goal with |- ?G => let G' := eval unfold cache in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Upc : U pc = T + 208 + 80 * c) by ((lazymatch goal with |- ?G => let G' := eval unfold pc in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    (* [comment removed for export] *)
    destruct (icmc_cache_max c Hc) as [EIC _].
    destruct (rf_pro0 BSEGS ARB both_HRF ARB_ok regs Mr rom raR spR cache pc (Z_to_bv 64 0x10ab58) c H1 H2 H10 H11 H12 H13
                ltac:((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); rewrite store_ok_mrestrict; [apply (writableZ_sok M (U spR - 160) (U spR)); [exact WSTK | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia]
                                                             | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHs; lia])
                ltac:(lia) ltac:(rewrite Ucache, Upc; lia)
                ltac:((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); rewrite store_ok_mrestrict; [apply (writableZ_sok M T (T + 4096)); [exact WT | rewrite at_u by lia; rewrite Ucache; lia | rewrite at_u by lia; rewrite Ucache; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia]
                                                             | rewrite at_u by lia; rewrite Ucache; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; rewrite Ucache; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHrt; lia])
                ltac:(replace (at_ pc 4) with (Z_to_bv 64 (T + 208 + 80 * c + 4)) by (apply bv_eq; rewrite at_u by lia; rewrite Upc, u_Z2bv by lia; reflexivity);
                      apply RDM; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHrt; cbn in Hi; lia | exact KMC]))
      as (r1 & RUN1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & AG1).
    rewrite EIC in A9, A14.
    set (MR1 := ic_mem regs Mr raR spR cache 31) in *.
    set (spG := at_ spR (-32)) in *.
    assert (UspG : U spG = U spR - 32) by ((lazymatch goal with |- ?G => let G' := eval unfold spG in G in change_no_check G' end); rewrite at_u by lia; lia).
    assert (OUT1 : forall x : word, (U x < U spR - 32 \/ U spR <= U x) -> (U x < T + 208 + 84 \/ T + 208 + 2496 <= U x) -> MR1 x = Mr x).
    { intros x Hx Hy. (lazymatch goal with |- ?G => let G' := eval unfold MR1 in G in change_no_check G' end). rewrite ic_mem_outside_p by (rewrite ?Ucache; first [lia | intros i Hi; lia]). apply (rf_m1_outside ARB regs Mr raR spR ltac:(lia) x Hx). }
    assert (RD1 : forall z (k : nat) v, 0 <= z -> z + Z.of_nat k <= CEIL -> (z + Z.of_nat k <= T \/ T + 4096 <= z) -> (forall i, z <= i < z + Z.of_nat k -> Hd (Z_to_bv 64 i) = false) ->
               rdn BSEGS M (Z_to_bv 64 z) k = Some v -> rdn BSEGS MR1 (Z_to_bv 64 z) k = Some v).
    { intros z k v Z0 Z1 ZT Hh0 Hr. rewrite <- (RDM z k v Z0 ltac:(lia) Hh0 Hr). apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. apply OUT1; [lia | clear - Hx ZT; lia]. }
    assert (SBEG8 : SBEG mod 8 = 0).
    { pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16). exact (mod8_of_64k _ S16). }
    assert (NI : forall i : reg, In i [18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv; 4%bv; 3%bv] -> getr r1 i = getr regs i).
    { intros i Hi. apply AG1. cbn [In] in Hi |- *. intros Xi. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi|]). exact Hi. }
    destruct (gfp_pre MR1 rom spG (at_ ARB 0x5147c) pc (Z_to_bv 64 (cache_max c / 2)) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (at_ cache 2560) (at_ pc 16) SBEG c (cache_max c / 2) nf r1
                A1 A2 A10 A11 A12 A13 A14 A8 A9
                (NI 18%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 19%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 20%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 21%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12))
                (NI 22%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 23%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 24%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 25%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12))
                (NI 26%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 27%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12))
                ltac:(rewrite UspG; lia) Hc ltac:(rewrite EMC2; lia) ltac:(split; [lia | split; [lia | exact SBEG8]]) ltac:(rewrite UspG; lia))
      as (r2 & RUN2 & GR & B1 & B10 & B11 & B12 & B13 & B14 & AG2).
    - (* [comment removed for export] *) eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold MR1 in G in change_no_check G' end); apply ic_mem_grows|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end).
      rewrite store_ok_mrestrict; [ | rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                    | rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHs; lia].
      apply (writableZ_sok M (U spR - 160) (U spR)); [exact WSTK | rewrite at_u by (rewrite UspG; lia); rewrite UspG; lia | rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - TIMG; lia | intros i Hi; apply NHs; cbn in Hi; lia | exact KSB].
    - apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - TIMG; lia | intros i Hi; apply NHs; cbn in Hi; lia | exact KRIB].
    - apply (RD1 RIz 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - TSP ERI Hc; lia | intros i Hi; apply NHri; cbn in Hi; lia | exact KMTX].
    - apply (RD1 (RIz + 16) 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - TSP ERI Hc; lia | intros i Hi; apply NHri; cbn in Hi; lia | exact KNF].
    - eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold MR1 in G in change_no_check G' end); apply ic_mem_grows|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end).
      rewrite store_ok_mrestrict; [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHri; lia].
      apply (writableZ_sok M RIz (RIz + 128)); [exact WRI | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - (* [comment removed for export] *)
      rewrite EMC2 in *.
      set (M' := r10_mem regs M spR raR cache (at_ ARB 0x5147c) pc (Z_to_bv 64 h) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                   (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) RIz).
      assert (EMEM : gfp_m1 MR1 spG (at_ ARB 0x5147c) pc (Z_to_bv 64 h) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                       (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (SBEG + 2 ^ 37 + 128 * c) = mrestrict Hd M').
      { (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). rewrite <- (r10_mem_mrestrict regs M spR raR cache (at_ ARB 0x5147c) pc (Z_to_bv 64 h) (getr regs 18) (getr regs 19) (getr regs 20)
                               (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) RIz ltac:(lia) ltac:(lia) ltac:(rewrite Ucache; lia) Hd
                               ltac:(apply HOFF; intros z Hz; apply NHs; lia) ltac:(apply HOFF; intros z Hz; apply NHri; lia) ltac:(rewrite Ucache; apply HOFF; intros z Hz; apply NHrt; lia)).
        reflexivity. }
      assert (OUTM : forall a : word, (U a < U spR - 160 \/ U spR <= U a) -> (U a < RIz \/ RIz + 8 <= U a) ->
                 (forall i : Z, 1 <= i <= 31 -> (U a < T + 208 + 80 * i + 4 \/ T + 208 + 80 * i + 16 <= U a)) -> M' a = M a).
      { intros a A1' A2' A3'. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r10_mem_outside; [lia | lia | rewrite Ucache; lia | exact A1' | exact A2' | rewrite Ucache; exact A3']. }
      rewrite EMEM in RUN2.
      rewrite (ARB_lit8 0x5153c) in RUN1 by lia. rewrite (ARB_lit8 0x5143c) in RUN1 by lia.
      replace (Z_to_bv 64 0x5153c : word) with (0x5153c%bv : word) in RUN1 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x5143c : word) with (0x5143c%bv : word) in RUN1 by (apply bv_eq; reflexivity).
      apply (LK Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st) regs _ r2 _ M M' rom mdl (msteps_trans _ _ _ _ RUN1 RUN2)); [ | exact HALT | apply lazy_cover_HID | exact Bw1 | exact Bw2 | ].
      + intros a Ha. apply OUTM.
        * pose proof (hid_true_off Hd a (U spR - 160) 160 Ha ltac:(apply HOFF; intros z Hz; apply NHs; lia)). lia.
        * pose proof (hid_true_off Hd a RIz 8 Ha ltac:(apply HOFF; intros z Hz; apply NHri; lia)). lia.
        * intros i Hi. pose proof (hid_true_off Hd a T 4096 Ha ltac:(apply HOFF; intros z Hz; apply NHrt; lia)). lia.
      + intros mdlm SBM MIm.
        assert (FOOTM : forall a : word, M' a <> M a ->
                  ((RIz <= U a < RIz + 8) \/ (U spR - 160 <= U a < U spR) \/ (exists i, 1 <= i <= 31 /\ T + 208 + 80 * i + 4 <= U a < T + 208 + 80 * i + 16)) /\ M' a <> None).
        { intros a Ha.
          assert (DEF : (RIz <= U a < RIz + 8) \/ (U spR - 160 <= U a < U spR) \/ (T <= U a < T + 4096) -> M' a <> None).
          { intros IN. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r10_mem_grows.
            destruct IN as [I1 | [I2 | I3]]; [destruct (WRI (U a) ltac:(lia)) as [Dd _] | destruct (WSTK (U a) I2) as [Dd _] | destruct (WT (U a) I3) as [Dd _]]; rewrite Z_to_bv_bv_unsigned in Dd; exact Dd. }
          destruct (Z_lt_le_dec (U a) (T + 208 + 84)) as [KK1|KK1].
          { assert (IN : ((RIz <= U a < RIz + 8) \/ (U spR - 160 <= U a < U spR)) \/ ((U a < U spR - 160 \/ U spR <= U a) /\ (U a < RIz \/ RIz + 8 <= U a))) by (clear; lia).
            destruct IN as [IN | [O1 O2]]; [| exfalso; apply Ha; apply OUTM; [exact O1 | exact O2 | intros i Hi; lia]].
            split; [clear - IN; lia | apply DEF; clear - IN; lia]. }
          destruct (Z_lt_le_dec (U a) (T + 208 + 2496)) as [KK2|KK2].
          { (* [comment removed for export] *)
            set (i := (U a - (T + 208)) / 80). assert (Hi : 1 <= i <= 31 /\ T + 208 + 80 * i <= U a < T + 208 + 80 * i + 80).
            { (lazymatch goal with |- ?G => let G' := eval unfold i in G in change_no_check G' end). pose proof (Z.div_mod (U a - (T + 208)) 80 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (U a - (T + 208)) 80 ltac:(lia)) as MB.
              assert (1 <= (U a - (T + 208)) / 80) by (apply Z.div_le_lower_bound; lia). assert ((U a - (T + 208)) / 80 < 32) by (apply Z.div_lt_upper_bound; lia). lia. }
            destruct Hi as [Hi1 Hi2].
            destruct (Z_lt_le_dec (U a) (T + 208 + 80 * i + 4)) as [D1|D1]; [exfalso; apply Ha; apply OUTM; [clear - KK1 KK2 SP1 T2 CR; lia | clear - KK1 KK2 TSP ERI Hc; lia | intros j Hj; clear - D1 Hi2 Hj; nia]|].
            destruct (Z_lt_le_dec (U a) (T + 208 + 80 * i + 16)) as [D2|D2].
            - split; [right; right; exists i; split; [exact Hi1 | lia] | apply DEF; right; right; clear - KK1 KK2; lia].
            - exfalso. apply Ha. apply OUTM; [clear - KK2 SP1 T2 CR; lia | clear - KK1 KK2 TSP ERI Hc; lia | intros j Hj; clear - D2 Hi2 Hj; nia]. }
          assert (IN : ((RIz <= U a < RIz + 8) \/ (U spR - 160 <= U a < U spR)) \/ ((U a < U spR - 160 \/ U spR <= U a) /\ (U a < RIz \/ RIz + 8 <= U a))) by (clear; lia).
          destruct IN as [IN | [O1 O2]]; [| exfalso; apply Ha; apply OUTM; [exact O1 | exact O2 | intros i Hi; lia]].
          split; [clear - IN; lia | apply DEF; clear - IN; lia]. }
        assert (W1 : WF bt (op_cache_init st) Lc FF) by (apply WF_cache_init; exact W).
        destruct GR as (G2 & G8' & G9' & G18 & G19 & G20 & G21 & G22).
        apply (CONT r2 M' mdlm).
        * exact W1.
        * apply (repx_step_widen X (fun z => RIz <= z < RIz + 8)
                   (fun z => (U spR - 160 <= z < U spR) \/ (exists i, 1 <= i <= 31 /\ T + 208 + 80 * i + 4 <= z < T + 208 + 80 * i + 16))
                   (Xdec_iv RIz (RIz + 8)) st (op_cache_init st) Lc Lc FF FF M M' mdl mdlm RX).
          -- intros a Ha. destruct (FOOTM a Ha) as [F Dd]. split; [| exact Dd]. clear - F. tauto.
          -- intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r10_mem_grows. destruct (WRI (U a) ltac:(lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd.
          -- intros N0 N0' RPn Dn DIFF EQ KEEP.
             apply (OPS_REP_cache_init_pf bt st Lc FF N0 N0' mdl mdlm W RPn); [ | | exact SBM | exact MIm].
             ++ intros a Ha. destruct (DIFF a Ha) as (F & _ & Dd). split; [| exact Dd]. (lazymatch goal with |- ?G => let G' := eval unfold foot_cache_init, T_PC, PC_SZ in G in change_no_check G' end).
                destruct F as [F | (i & Hi & F)]; [right; lia | left; exists i; split; [exact Hi | lia]].
             ++ intros i Hi. destruct (icmc_cache_max i Hi) as [E1' E2'].
                destruct (r10_mem_cells BSEGS regs M spR raR cache (at_ ARB 0x5147c) pc (Z_to_bv 64 h) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                            (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) RIz ltac:(lia) ltac:(lia) ltac:(rewrite Ucache; lia) ltac:(rewrite Ucache; clear - TSP ERI Hc; lia) i ltac:(lia)) as [CM CS].
                fold M' in CM, CS. rewrite E1' in CM. rewrite E2' in CS.
                replace (at_ cache (80 * i + 4)) with (Z_to_bv 64 (T + 208 + 80 * i + 4)) in CM by (apply bv_eq; rewrite at_u by (rewrite Ucache; lia); rewrite Ucache, u_Z2bv by lia; lia).
                replace (at_ cache (80 * i + 8)) with (Z_to_bv 64 (T + 208 + 80 * i + 8)) in CS by (apply bv_eq; rewrite at_u by (rewrite Ucache; lia); rewrite Ucache, u_Z2bv by lia; lia).
                (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN, T_PC, PC_SZ in G in change_no_check G' end). rewrite ?BT_segs. split.
                ** rewrite <- CM. apply rdn_ext; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx.
                   apply EQ; [apply XT; clear - Hx Hi; lia | clear - Hx Hi TSP ERI Hc; lia].
                ** rewrite <- CS. apply rdn_ext; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx.
                   apply EQ; [apply XT; clear - Hx Hi; lia | clear - Hx Hi TSP ERI Hc; lia].
        * exact SBM.
        * exact MIm.
        * intros a Ha. destruct (FOOTM a Ha) as [F Dd]. split; [| exact Dd]. fold RIz.
          destruct F as [F | [F | (i & Hi & F)]]; [right; left; exact F | left; exact F | right; right; clear - F Hi; lia].
        * (lazymatch goal with |- ?G => let G' := eval unfold gf_inv in G in change_no_check G' end). fold RIz. split; [| split].
          -- (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r10_mem_lock; lia.
          -- intros k v Hin. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r10_mem_gslots; first [rewrite (ARB_lit8 0x5147c) by lia; exact Hin | rewrite ?Ucache; clear - TSP ERI Hc; lia | rewrite ?Ucache; lia].
          -- intros k v Hin. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r10_mem_rslots; first [exact Hin | rewrite ?Ucache; clear - TSP ERI Hc; lia | rewrite ?Ucache; lia].
        * (lazymatch goal with |- ?G => let G' := eval unfold gfp_regs in G in change_no_check G' end). fold RIz. rewrite ERI. unfold pc in G21. replace (at_ (Z_to_bv 64 (T + 208 + 80 * c)) 16) with (Z_to_bv 64 (T + 208 + 80 * c + 16)) in G21
            by (apply bv_eq; rewrite at_u by (rewrite u_Z2bv by lia; lia); rewrite !u_Z2bv by lia; reflexivity).
          repeat split; assumption.
        * exact B1.
        * exact B10.
        * rewrite B11. (lazymatch goal with |- ?G => let G' := eval unfold cache in G in change_no_check G' end). apply bv_eq. rewrite !at_u by (rewrite ?u_Z2bv by lia; lia). rewrite !u_Z2bv by lia. lia.
        * exact B12.
        * rewrite B13. rewrite ERI. reflexivity.
        * exact B14.
        * rewrite (AG2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). rewrite (NI 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12). exact H4.
        * rewrite (AG2 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). rewrite (NI 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 13). exact H3.
  Qed.


End L3.
End WithCeil.

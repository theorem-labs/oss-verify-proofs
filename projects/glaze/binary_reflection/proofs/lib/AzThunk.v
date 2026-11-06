(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

Section Thunk.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
Variable SHC : list (Z * Z).
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops SWIN G SHC AINVH.
Hypothesis G_img_pg : g_img_lo G mod 4096 = 0 /\ g_img_hi G mod 4096 = 0.
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= u a < g_img_hi G) -> find_segment SEGS (u a) 1 = None.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.

#[local] Notation cfg := (fun fx R p M mdl => mkCfg (mkstF fx R (Z_to_bv 64 p) M (seg_rom SEGS)) mdl).

Lemma nmodel_trans : forall m1 m2 m3, nmodel m1 m2 -> nmodel m2 m3 -> nmodel m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3) (B1 & B2 & B3). split; [exact B1|]. split; [rewrite B2; exact A2 | rewrite B3; exact A3]. Qed.

(* [comment removed for export] *)
Lemma h_thunk_step : forall thunk body fx R M mdl L LF B C K T,
  (forall fx R M, RiscvSemantics.step SEGS (mkstF fx R (Z_to_bv 64 thunk) M (seg_rom SEGS))
                  = MachineOk (mkstF fx R (Z_to_bv 64 body) M (seg_rom SEGS))) ->
  m_halted mdl = None -> AINVH L LF B C K M mdl ->
  (forall mdl', nmodel mdl mdl' -> AINVH L LF B C K M mdl' -> RZ (cfg fx R body M mdl') T) ->
  RZ (cfg fx R thunk M mdl) T.
Proof.
  intros thunk body fx R M mdl L LF B C K T STEP Hh HA Hk.
  destruct (hp_lazy _ _ _ _ HP _ _ _ _ _ _ _ HA) as (AA & Hwf & Hminv & _ & _ & Hmat).
  pose proof (hp_facts _ _ _ _ HP _ _ _ _ _ _ _ HA) as HLZ.
  set (H := fun a : word => page_in_ranges (page_base a) (m_vm_lazy mdl)).
  assert (HH : H_off_segments SEGS H).
  { intros a Ha. unfold H in Ha. apply SEGS_out.
    unfold page_in_ranges in Ha. apply existsb_exists in Ha as [iv [Hin Hb]].
    apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2. unfold page_size in Hb2.
    pose proof (proj1 (Forall_forall _ _) HLZ iv Hin) as (L0 & L1 & L2).
    pose proof (page_base_le' a) as (P1 & P2 & P3). destruct G_img_pg as [GP1 GP2].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct L2 as [L2|L2]; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  assert (Hcov : lazy_cover H (m_vm_lazy mdl) AA).
  { intros w Hl Hw. unfold H in Hw. rewrite Hl in Hw. discriminate. }
  apply (AsVocab.AsanAcct.rz_msteps_restricted' SEGS H HH SEGS_wx (fun c => RZ c T) (fun c c' Hn Hr => RZ_silent1 c c' T Hn Hr) AA
           (mkstF fx R (Z_to_bv 64 thunk) M (seg_rom SEGS)) (mkstF fx R (Z_to_bv 64 body) (mrestrict H M) (seg_rom SEGS)) mdl Hcov Hwf Hminv Hh).
  - eapply msteps_one; [reflexivity|].
    change (restrict H (mkstF fx R (Z_to_bv 64 thunk) M (seg_rom SEGS))) with (mkstF fx R (Z_to_bv 64 thunk) (mrestrict H M) (seg_rom SEGS)).
    exact (STEP fx R (mrestrict H M)).
  - intros mdl' Hminv' Hsame _. cbn [ms_mem mkstF mkst].
    change (unrestrict H M (mkstF fx R (Z_to_bv 64 body) (mrestrict H M) (seg_rom SEGS))) with
           (mkstF fx R (Z_to_bv 64 body) (munrestrict H M (mrestrict H M)) (seg_rom SEGS)).
    rewrite munrestrict_mrestrict.
    pose proof (same_but_materialized_frame mdl mdl' Hsame) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfds & _ & _ & Hfs & Hhalt & _).
    apply Hk.
    + unfold nmodel. rewrite Hhalt. repeat split; assumption.
    + exact (Hmat mdl' Hminv' Hsame).
Qed.

(* [comment removed for export] *)
Theorem h_strlen_thunk : forall thunk body,
  (forall fx R M, RiscvSemantics.step SEGS (mkstF fx R (Z_to_bv 64 thunk) M (seg_rom SEGS))
                  = MachineOk (mkstF fx R (Z_to_bv 64 body) M (seg_rom SEGS))) ->
  h_strlen_at SEGS G FXOK RZ AINVH body -> h_strlen_at SEGS G FXOK RZ AINVH thunk.
Proof.
  intros thunk body STEP HB fx R M mdl L LF B C K ret sp s len T HFX Hh HA Hpre Hs Hstr Hoff Hpost.
  apply (h_thunk_step thunk body fx R M mdl L LF B C K T STEP Hh HA).
  intros mdl' Hnm HA'.
  apply (HB fx R M mdl' L LF B C K ret sp s len T HFX (proj1 Hnm) HA' Hpre Hs Hstr Hoff).
  intros fx' R' M' mdl'' HFX' Hkept Hlen Hch Hscr HA'' Hnm'.
  exact (Hpost fx' R' M' mdl'' HFX' Hkept Hlen Hch Hscr HA'' (nmodel_trans _ _ _ Hnm Hnm')).
Qed.
End Thunk.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

Section KnRestrict.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable A : atable.
Variable SWIN PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable SHC VSH : list (Z * Z).
Variable AINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable G : gtable.
Hypothesis AINV_if : AzNodesAlloc3.ifacts A PERMc SPTOPc SHC VSH G AINV.
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
Hypothesis SHC_stack : forall z, in_sshadow z -> in_shc SHC z = true.
Hypothesis SHC_image : forall z, in_ishadow G z -> in_shc SHC z = true.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_img_lo G <= lo /\ hi <= g_img_hi G.
Hypothesis G_img_hull : 0 <= g_img_lo G /\ g_img_lo G <= g_ro_lo G <= g_img_hi G.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
Hypothesis G_opnew_kn_wf : opnew_kn_wf G = true.

#[local] Notation Mr := (GPS.Mr SHC VSH).
#[local] Notation hid := (GPS.hid SHC VSH).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma opnew_kn_restrict : forall E cs model M B C K,
  AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M model ->
  (forall E0, Forall (fun K0 => kentry_ok SEGS E0 M K0) (g_opnew_kn G)) ->
  know_ok SEGS E (Mr E cs model M) (g_opnew_kn G).
Proof.
  intros E cs model M B C K HA H. unfold know_ok. apply Forall_forall. intros K0 HinK.
  pose proof (proj1 (Forall_forall _ _) (H E) K0 HinK) as F.
  pose proof (proj1 (forallb_forall _ _) G_opnew_kn_wf K0 HinK) as GK. cbv beta in GK.
  pose proof G_img_hull as GH. pose proof G_img_ceil as GC. pose proof GlzConst.ceil_hi as CH. unfold GlzConst.PTRHI in CH.
  assert (VISI : forall z, g_img_lo G <= z < g_img_hi G -> forall HZ : 0 <= z < 2 ^ 64, Mr E cs model M (Z_to_bv 64 z) = M (Z_to_bv 64 z)).
  { intros z Hz HZ. unfold GPS.Mr. apply mrestrict_visible.
    eapply (AzNodesAlloc3.hid_app_falseX A SWIN PERMc SPTOPc SHC VSH G A_img_hi A_img_lo SWIN_img AINV AINV_if); [exact HA|].
    right; right; right; right. rewrite u64_lit by exact HZ. exact Hz. }
  assert (VISS : forall z, in_ishadow G z -> forall HZ : 0 <= z < 2 ^ 64, Mr E cs model M (Z_to_bv 64 z) = M (Z_to_bv 64 z)).
  { intros z Hz HZ. unfold GPS.Mr. apply mrestrict_visible. apply (hid_shadow_false SHC VSH G SHC_stack SHC_image). right; right.
    rewrite (u64_lit z) by exact HZ. exact Hz. }
  destruct K0 as [[kb ko] w vv|[kb ko] zn|[kb ko] zn kb2|ilo ihi|e m|e rlo rhi|[kb ko] zn|a1 n1 a2 n2|[kb ko] zn fc|[kb ko] zn|[kb ko] zn|fv flo fd];
    try discriminate GK.
  - (* [comment removed for export] *)
    destruct kb as [z| | | | | | |]; try discriminate GK. destruct z; try discriminate GK. destruct vv as [vz| | | | | | |]; try discriminate GK.
    apply andb_prop in GK as [GK Gw]. apply andb_prop in GK as [G1 G2]. apply Z.leb_le in G1. apply Z.leb_le in G2. apply Nat.leb_le in Gw.
    cbn [kentry_ok] in F |- *. destruct F as (Fw & Fl & Frd).
    split; [exact Fw|]. split; [exact Fl|].
    assert (Hadr : adenot E (SA (ELit 0) ko) = Z_to_bv 64 ko).
    { rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E (SA (ELit 0) ko))), (flat_u E _ _ Fl), estart_lit0. reflexivity. }
    rewrite Hadr in Frd |- *. unfold GPS.Mr.
    rewrite (rdn_mrestrict_eq SEGS (hid E cs model) w M (Z_to_bv 64 ko)); [exact Frd|].
    intros k Hk. eapply (AzNodesAlloc3.hid_app_falseX A SWIN PERMc SPTOPc SHC VSH G A_img_hi A_img_lo SWIN_img AINV AINV_if); [exact HA|].
    right; right; right; right.
    unfold woff. rewrite u64_lit by (rewrite u64_lit by lia; lia). rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *)
    destruct kb as [z| | | | | | |]; try discriminate GK. destruct z; try discriminate GK. destruct zn as [n| | | | | | |]; try discriminate GK.
    apply andb_prop in GK as [GK G3]. apply andb_prop in GK as [G1 G2]. apply Z.ltb_lt in G1. apply Z.leb_le in G2. apply Z.leb_le in G3.
    cbn [kentry_ok] in F |- *. destruct F as [Fl Fz].
    unfold elenZ in Fz |- *. cbn [edenot] in Fz |- *. unfold flat in Fl |- *. rewrite estart_lit0 in Fl, Fz |- *.
    assert (D1 : g_img_lo G / 8 <= g_ro_lo G / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : g_img_hi G / 8 <= (g_img_hi G + 7) / 8) by (apply Z.div_le_mono; lia).
    assert (D3 : (g_img_hi G + 7) / 8 <= g_img_hi G) by (apply Z.div_le_upper_bound; lia).
    assert (D0 : 0 <= g_ro_lo G / 8) by (apply Z.div_pos; lia).
    split; [exact Fl|]. intros i Hi.
    rewrite (u_small n) in Hi by (unfold SB in *; lia).
    rewrite <- (Fz i ltac:(rewrite (u_small n) by (unfold SB in *; lia); exact Hi)).
    apply VISS; [unfold in_ishadow; lia | unfold SB in *; lia].
  - (* [comment removed for export] *)
    apply andb_prop in GK as [GK G3]. apply andb_prop in GK as [G1 G2]. apply Z.leb_le in G1. apply Z.leb_le in G2. apply Z.leb_le in G3.
    cbn [kentry_ok] in F |- *. destruct F as (F1 & F2 & F3).
    split; [lia|]. split; [lia|]. intros i Hi. rewrite (VISI i ltac:(lia) ltac:(lia)). apply F3. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End KnRestrict.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzFrame.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Frame.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.

(* [comment removed for export] *)
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
(* [comment removed for export] *)
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_vm : forall L B C M mdl mdl', AINVH L B C M mdl -> m_vmmaps mdl' = m_vmmaps mdl -> AINVH L B C M mdl'.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
(* [comment removed for export] *)
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok G b m.
(* [comment removed for export] *)
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.

(* [comment removed for export] *)
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
Hypothesis G_priv : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
(* [comment removed for export] *)
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= bv_unsigned a < g_img_hi G) -> find_segment SEGS (bv_unsigned a) 1 = None.

Lemma store_ok_defined : forall M (a : word),
  ~ (g_img_lo G <= bv_unsigned a < g_img_hi G) -> RiscvSemantics.store_ok SEGS M a 1 = true -> M a <> None.
Proof.
  intros M a Ha Hs Hn. cbn [RiscvSemantics.store_ok] in Hs. unfold wview in Hs. rewrite Hn in Hs.
  rewrite (SEGS_out a Ha) in Hs. discriminate Hs.
Qed.

(* [comment removed for export] *)
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HID : list (Z * Z).
Variable M0 : word -> option byte.
Variable B0 C0 : Z.
Hypothesis B0_nonneg : 0 <= B0.
Hypothesis C0_nonneg : 0 <= C0.

(* [comment removed for export] *)
Definition zone (a : word) : Prop :=
  (in_blocks HID (bv_unsigned a) \/ SPTOPc <= bv_unsigned a
   \/ (g_ro_lo G <= bv_unsigned a < g_img_hi G /\ ~ in_wins (g_priv G) (bv_unsigned a)))
  /\ ~ in_wins PERMc (bv_unsigned a) /\ ~ in_wins SWIN (bv_unsigned a).

(* [comment removed for export] *)
Definition perm_owned : Prop :=
  forall z, in_wins PERMc z -> in_blocks HID z \/ CEIL_run <= z \/ in_wins SWIN z.

(* [comment removed for export] *)
Lemma swin_byte : forall z, in_wins SWIN z -> g_ro_hi G <= z < g_img_hi G /\ ~ in_wins (g_priv G) z.
Proof.
  intros z (lo & hi & Hin & Hz). destruct (SWIN_img lo hi Hin) as (S1 & S2 & S3). split; [lia|].
  intros (plo & phi & Hpin & Hpz). destruct (S3 plo phi Hpin); lia.
Qed.

(* [comment removed for export] *)
Definition dzone (a : word) : Prop := (CEIL_run <= bv_unsigned a < SPTOPc) \/ in_wins PERMc (bv_unsigned a).

Definition AINV_f (Lc : list (Z * Z)) (B C : Z) (M : word -> option byte) (mdl : Model) : Prop :=
  AINVH (Lc ++ HID) (B0 + B) (C0 + C) M mdl
  /\ perm_owned
  /\ CEIL_run <= SPTOPc
  /\ (forall a, zone a -> M a = M0 a)
  /\ (forall a, dzone a -> M0 a <> None -> M a <> None).

(* [comment removed for export] *)
Lemma in_blocks_app : forall L1 L2 z, in_blocks (L1 ++ L2) z <-> in_blocks L1 z \/ in_blocks L2 z.
Proof.
  intros L1 L2 z. unfold in_blocks. split.
  - intros (b & n & Hin & Hz). apply in_app_iff in Hin as [Hin|Hin]; [left|right]; exists b, n; split; assumption.
  - intros [(b & n & Hin & Hz)|(b & n & Hin & Hz)]; exists b, n; split; try assumption; apply in_app_iff; [left|right]; assumption.
Qed.

Lemma in_blocks_mono : forall L L' z, (forall x, In x L -> In x L') -> in_blocks L z -> in_blocks L' z.
Proof. intros L L' z Hs (b & n & Hin & Hz). exists b, n. split; [apply Hs; exact Hin | exact Hz]. Qed.

(* [comment removed for export] *)
Lemma blk_byte : forall L B C M mdl b m z,
  AINVH L B C M mdl -> In (b, m) L -> b <= z < b + m -> z < CEIL_run /\ ~ (g_img_lo G <= z < g_img_hi G).
Proof.
  intros L B C M mdl b m z HA Hin Hz. destruct (AINVH_zone _ _ _ _ _ b m HA Hin) as (Z1 & Z2 & Z3). split; [lia | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AINV_f_frame : forall Lc B C M M' mdl,
  AINV_f Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc Lc a /\ M' a <> None) -> AINV_f Lc B C M' mdl.
Proof.
  pose proof G_ro_img as G_ro_img_kept.      (* [comment removed for export] *)
  intros Lc B C M M' mdl (HA & HP & HT & HF & HD) Hch. split; [|split; [exact HP | split; [exact HT|split]]].
  - eapply AINVH_frame; [exact HA|]. intros a Ha. destruct (Hch a Ha) as [Ho Hs]. split; [|exact Hs].
    destruct Ho as [Hb|[Hp|[Hst|Hsw]]].
    + left. apply in_blocks_app. left. exact Hb.
    + destruct (HP _ Hp) as [Hh|[Ho|Hsw']]; [left; apply in_blocks_app; right; exact Hh | right; left; exact Ho | right; right; exact Hsw'].
    + right. left. lia.
    + right. right. exact Hsw.
  - intros a Hz. destruct (decide (M' a = M a)) as [Heq|Hne].
    + rewrite Heq. exact (HF a Hz).
    + exfalso. destruct (Hch a Hne) as [Ho _]. destruct Hz as (Hz1 & Hnp & Hnsw).
      destruct Ho as [Hb|[Hp|[Hst|Hsw]]].
      * destruct Hb as (b & n & Hin & Hbz).
        destruct Hz1 as [Hh|[Ht|Hro]].
        -- destruct Hh as (b' & n' & Hin' & Hbz').
           destruct (in_split _ _ Hin) as (L1 & L2 & HL).
           pose proof (AINVH_disj _ _ _ _ _ L1 (L2 ++ HID) b n b' n' HA
                         ltac:(rewrite HL; rewrite <- app_assoc; reflexivity)
                         ltac:(rewrite app_assoc; apply in_app_iff; right; exact Hin')) as D. lia.
        -- pose proof (blk_byte _ _ _ _ _ b n (bv_unsigned a) HA ltac:(apply in_app_iff; left; exact Hin) Hbz). lia.
        -- pose proof (blk_byte _ _ _ _ _ b n (bv_unsigned a) HA ltac:(apply in_app_iff; left; exact Hin) Hbz). lia.
      * exact (Hnp Hp).
      * destruct Hz1 as [Hh|[Ht|Hro]].
        -- destruct Hh as (b' & n' & Hin' & Hbz').
           pose proof (blk_byte _ _ _ _ _ b' n' (bv_unsigned a) HA ltac:(apply in_app_iff; right; exact Hin') Hbz'). lia.
        -- lia.
        -- lia.
      * exact (Hnsw Hsw).
  - intros a Hd H0. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HD a Hd H0)|].
    exact (proj2 (Hch a Hne)).
Qed.

Lemma AINV_f_vm : forall Lc B C M mdl mdl', AINV_f Lc B C M mdl -> m_vmmaps mdl' = m_vmmaps mdl -> AINV_f Lc B C M mdl'.
Proof.
  intros Lc B C M mdl mdl' (HA & HP & HT & HF & HD) Hvm. split; [|split; [exact HP | split; [exact HT | split; [exact HF | exact HD]]]].
  eapply AINVH_vm; [exact HA | exact Hvm].
Qed.

Lemma AINV_f_mono : forall Lc B C B' C' M mdl, AINV_f Lc B C M mdl -> B <= B' -> C <= C' -> AINV_f Lc B' C' M mdl.
Proof.
  intros Lc B C B' C' M mdl (HA & HP & HT & HF & HD) HB HC. split; [|split; [exact HP | split; [exact HT | split; [exact HF | exact HD]]]].
  eapply AINVH_mono; [exact HA | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma AINV_f_zone : forall Lc B C M mdl b m, AINV_f Lc B C M mdl -> In (b, m) Lc -> blk_ok G b m.
Proof.
  intros Lc B C M mdl b m (HA & _) Hin. eapply AINVH_zone; [exact HA|]. apply in_app_iff. left. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma AINV_f_top : forall Lc B C M mdl, AINV_f Lc B C M mdl -> CEIL_run <= SPTOPc.
Proof. intros Lc B C M mdl (_ & _ & HT & _). exact HT. Qed.

(* [comment removed for export] *)
Lemma AINV_f_disj : forall Lc B C M mdl L1 L2 b m b' m',
  AINV_f Lc B C M mdl -> Lc = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Proof.
  intros Lc B C M mdl L1 L2 b m b' m' (HA & _) HL Hin. subst Lc.
  eapply (AINVH_disj _ _ _ _ _ L1 (L2 ++ HID)); [exact HA | rewrite <- app_assoc; reflexivity |].
  rewrite app_assoc. apply in_app_iff. left. exact Hin.
Qed.

Lemma AINV_f_perm_apart : forall Lc B C M mdl b m lo hi,
  AINV_f Lc B C M mdl -> In (b, m) Lc -> 1 <= m -> In (lo, hi) PERMc -> lo < hi -> b + m <= lo \/ hi <= b.
Proof.
  intros Lc B C M mdl b m lo hi (HA & HP & _) Hin Hm Hpin Hlh. pose proof G_ro_img as GR.
  pose proof (AINVH_zone _ _ _ _ _ b m HA ltac:(apply in_app_iff; left; exact Hin)) as (K1 & K2 & K3).
  destruct (Z_lt_ge_dec (b + m) (lo + 1)) as [|Hge]; [left; lia|].
  destruct (Z_lt_ge_dec hi (b + 1)) as [|Hge2]; [right; lia|].
  exfalso. set (z := Z.max lo b).
  assert (Hzw : lo <= z < hi) by (unfold z; lia). assert (Hzb : b <= z < b + m) by (unfold z; lia).
  destruct (HP z ltac:(exists lo, hi; split; [exact Hpin | exact Hzw])) as [Hh|[Hc|Hsw]].
  - destruct Hh as (b2 & m2 & Hin2 & Hbz2). destruct (in_split _ _ Hin) as (L1 & L2 & HL).
    pose proof (AINVH_disj _ _ _ _ _ L1 (L2 ++ HID) b m b2 m2 HA
                 ltac:(rewrite HL; rewrite <- app_assoc; reflexivity)
                 ltac:(rewrite app_assoc; apply in_app_iff; right; exact Hin2)). lia.
  - lia.
  - destruct (swin_byte _ Hsw) as [S1 _]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Alloc.
Variable stk : Z.
Hypothesis stk_ok : 0 <= stk <= MSTK.
Variable bcap ccap : Z.
Hypothesis bcap_ok : B0 + bcap <= GBUDGET.
Hypothesis ccap_ok : C0 + ccap <= GCOUNT.

#[local] Notation frame_kept := (GlzSpecsStr.GlzContracts.frame_kept SWIN PERMc SPTOPc G).

(* [comment removed for export] *)
Lemma alloc_changed_not_kept : forall Lfull Lc sp a B C M mdl,
  AINVH Lfull B C M mdl -> (forall x, In x Lc -> In x Lfull) -> (forall x, In x HID -> In x Lfull) -> perm_owned ->
  CEIL_run + MSTK <= sp ->
  alloc_changed G stk Lfull sp a -> frame_kept Lc sp a -> False.
Proof.
  intros Lfull Lc sp a B C M mdl HA Hsub Hhid HP Hsp Hch Hk.
  pose proof G_ro_img as GR. pose proof G_img_ceil as GC. pose proof stk_ok as SK.
  destruct Hk as [[Ho Hns]|[[Hro Hnp]|[Hab Hspt]]]; destruct Hch as [(Hhz & Hni & Hnb)|[Hsc|Hpv]].
  - destruct Ho as [Hb|[Hp|[Hst|Hsw]]].
    + apply Hnb. eapply in_blocks_mono; [exact Hsub | exact Hb].
    + destruct (HP _ Hp) as [Hb|[Hc|Hsw']]; [exact (Hnb (in_blocks_mono _ _ _ Hhid Hb)) | lia | destruct (swin_byte _ Hsw') as [X _]; apply Hni; lia].
    + lia.
    + destruct Hsw as (lo & hi & Hin & Hr). destruct (SWIN_img lo hi Hin) as (S1 & S2 & _). apply Hni. lia.
  - lia.
  - destruct Hpv as (plo & phi & Hpin & Hpr). destruct (G_priv plo phi Hpin) as [P1 P2].
    destruct Ho as [Hb|[Hp|[Hst|Hsw]]].
    + destruct Hb as (b & n & Hin & Hbz). destruct (blk_byte _ _ _ _ _ b n _ HA (Hsub _ Hin) Hbz) as [_ X]. apply X. lia.
    + destruct (HP _ Hp) as [Hb|[Hc|Hsw']].
      * destruct Hb as (b & n & Hin & Hbz). destruct (blk_byte _ _ _ _ _ b n _ HA (Hhid _ Hin) Hbz) as [_ X]. apply X. lia.
      * lia.
      * destruct (swin_byte _ Hsw') as [_ X]. apply X. exists plo, phi. split; [exact Hpin | exact Hpr].
    + lia.
    + destruct Hsw as (lo & hi & Hin & Hr). destruct (SWIN_img lo hi Hin) as (_ & _ & S3). destruct (S3 plo phi Hpin); lia.
  - apply Hni. lia.
  - unfold MSTK in *. lia.
  - apply Hnp. exact Hpv.
  - lia.
  - lia.
  - destruct Hpv as (plo & phi & Hpin & Hpr). destruct (G_priv plo phi Hpin) as [P1 P2]. unfold MSTK in *. lia.
Qed.

(* [comment removed for export] *)
Lemma alloc_changed_not_zone : forall Lfull sp a B C M mdl,
  AINVH Lfull B C M mdl -> (forall x, In x HID -> In x Lfull) -> CEIL_run + MSTK <= sp -> sp <= SPTOPc ->
  alloc_changed G stk Lfull sp a -> zone a -> False.
Proof.
  intros Lfull sp a B C M mdl HA Hsub Hsp Htop Hch (Hz1 & Hnp & Hnsw).
  pose proof G_ro_img as GR. pose proof G_img_ceil as GC. pose proof stk_ok as SK.
  destruct Hch as [(Hhz & Hni & Hnb)|[Hsc|Hpv]].
  - destruct Hz1 as [Hh|[Ht|Hro]].
    + apply Hnb. eapply in_blocks_mono; [exact Hsub | exact Hh].
    + lia.
    + apply Hni. lia.
  - destruct Hz1 as [Hh|[Ht|Hro]].
    + destruct Hh as (b & n & Hin & Hbz). destruct (blk_byte _ _ _ _ _ b n _ HA (Hsub _ Hin) Hbz) as [X _]. unfold MSTK in *. lia.
    + lia.
    + unfold MSTK in *. lia.
  - destruct Hpv as (plo & phi & Hpin & Hpr). destruct (G_priv plo phi Hpin) as [P1 P2].
    destruct Hz1 as [Hh|[Ht|Hro]].
    + destruct Hh as (b & n & Hin & Hbz). destruct (blk_byte _ _ _ _ _ b n _ HA (Hsub _ Hin) Hbz) as [_ X]. apply X. lia.
    + lia.
    + destruct Hro as [_ Hnpv]. apply Hnpv. exists plo, phi. split; [exact Hpin | exact Hpr].
Qed.

(* [comment removed for export] *)
Lemma dzone_changed_defined : forall Lfull sp a B C M M' mdl,
  perm_owned -> AINVH Lfull B C M mdl -> (forall x, In x HID -> In x Lfull) -> CEIL_run + MSTK <= sp ->
  alloc_changed G stk Lfull sp a ->
  (forall a' : word, sp - stk <= bv_unsigned a' < sp -> RiscvSemantics.store_ok SEGS M' a' 1 = true) ->
  dzone a -> M' a <> None.
Proof.
  intros Lfull sp a B C M M' mdl HP HA Hhid Hsp Hch Hscr Hdz.
  pose proof G_ro_img as GR. pose proof G_img_ceil as GC. pose proof stk_ok as SK.
  destruct Hch as [(Hhz & Hni & Hnb)|[Hsc|Hpv]].
  - exfalso. destruct Hdz as [Hst|Hp]; [lia|]. destruct (HP _ Hp) as [Hb|[Hc|Hsw']]; [| lia | destruct (swin_byte _ Hsw') as [X _]; apply Hni; lia].
    apply Hnb. eapply in_blocks_mono; [exact Hhid | exact Hb].
  - eapply store_ok_defined; [| exact (Hscr a Hsc)]. unfold MSTK in *. lia.
  - exfalso. destruct Hpv as (plo & phi & Hpin & Hpr). destruct (G_priv plo phi Hpin) as [P1 P2].
    destruct Hdz as [Hst|Hp]; [lia|]. destruct (HP _ Hp) as [Hb|[Hc|Hsw']].
    + destruct Hb as (b & n & Hin & Hbz). destruct (blk_byte _ _ _ _ _ b n _ HA (Hhid _ Hin) Hbz) as [_ X]. apply X. lia.
    + lia.
    + destruct (swin_byte _ Hsw') as [_ X]. apply X. exists plo, phi. split; [exact Hpin | exact Hpr].
Qed.

(* [comment removed for export] *)
Lemma nalloc_post_ok_of : forall fx R M mdl Lc B C n sp fx' R' M' mdl' p,
  AINV_f Lc B C M mdl -> CEIL_run + MSTK <= sp -> sp <= SPTOPc -> 1 <= n ->
  (forall a : word, sp - MSTK <= bv_unsigned a < sp -> RiscvSemantics.store_ok SEGS M a 1 = true) ->
  alloc_post_ok SEGS AINVH FXOK G stk fx R M mdl (Lc ++ HID) (B0 + B) (C0 + C) n sp fx' R' M' mdl' p ->
  nalloc_post_ok SEGS SWIN PERMc SPTOPc AINV_f FXOK G fx R M mdl Lc B C n sp fx' R' M' mdl' p.
Proof.
  intros fx R M mdl Lc B C n sp fx' R' M' mdl' p (HA & HP & HT & HF & HD) Hspc Hsptop Hn1 Hstk
         (HFX' & Hkept & Ha0 & Hpal & Hblk & Hdisj & Hdef & Hfr & Hscr & HA' & Hh' & Hlz' & Hmat' & Hfs' & Hfds').
  pose proof G_ro_img as GR. pose proof G_img_ceil as GC. pose proof stk_ok as SK.
  split; [exact HFX'|]. split; [exact Hkept|]. split; [exact Ha0|]. split; [exact Hpal|]. split; [exact Hblk|].
  split. { intros b m Hin. apply Hdisj. apply in_app_iff. left. exact Hin. }
  split.
  { (* [comment removed for export] *)
    intros lo hi Hin Hlh. destruct Hblk as (K1 & K2 & K3).
    destruct (Z_lt_ge_dec (bv_unsigned p + n) (lo + 1)) as [|Hge]; [left; lia|].
    destruct (Z_lt_ge_dec hi (bv_unsigned p + 1)) as [|Hge2]; [right; lia|].
    exfalso.
    (* [comment removed for export] *)
    set (z := Z.max lo (bv_unsigned p)).
    assert (Hzw : lo <= z < hi) by (unfold z; lia). assert (Hzb : bv_unsigned p <= z < bv_unsigned p + n) by (unfold z; lia).
    destruct (HP z ltac:(exists lo, hi; split; [exact Hin | exact Hzw])) as [Hb|[Hc|Hsw']]; [|lia| destruct (swin_byte _ Hsw') as [X _]; lia].
    destruct Hb as (b & m & Hinb & Hbz).
    pose proof (AINVH_disj _ _ _ _ _ [] (Lc ++ HID) (bv_unsigned p) n b m HA' eq_refl ltac:(cbn [app]; apply in_app_iff; right; exact Hinb)). lia. }
  split; [exact Hdef|].
  split.
  { intros a Hka. destruct (decide (M' a = M a)) as [Heq|Hne]; [exact Heq|]. exfalso.
    eapply (alloc_changed_not_kept (Lc ++ HID) Lc sp a); [exact HA | intros x Hx; apply in_app_iff; left; exact Hx
      | intros x Hx; apply in_app_iff; right; exact Hx | exact HP | exact Hspc | exact (Hfr a Hne) | exact Hka]. }
  split.
  { intros a Ha.
    assert (ST : RiscvSemantics.store_ok SEGS M' a 1 = true).
    { destruct (decide (M' a = M a)) as [Heq|Hne].
      - pose proof (Hstk a Ha) as X. cbn [RiscvSemantics.store_ok] in X |- *. unfold wview in X |- *. rewrite Heq. exact X.
      - destruct (Hfr a Hne) as [(Hhz & _ & _)|[Hsc|Hpv]].
        + exfalso. unfold MSTK in *. lia.
        + exact (Hscr a Hsc).
        + exfalso. destruct Hpv as (plo & phi & Hpin & Hpr). destruct (G_priv plo phi Hpin). unfold MSTK in *. lia. }
    split; [eapply store_ok_defined; [unfold MSTK in *; lia | exact ST] | exact ST]. }
  split.
  { split; [|split; [exact HP|split; [exact HT|split]]].
    - cbn [app]. replace (B0 + (B + mcost n)) with (B0 + B + mcost n) by lia. replace (C0 + (C + MCNT)) with (C0 + C + MCNT) by lia. exact HA'.
    - intros a Hz. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HF a Hz)|]. exfalso.
      eapply (alloc_changed_not_zone (Lc ++ HID) sp a); [exact HA | intros x Hx; apply in_app_iff; right; exact Hx | exact Hspc | exact Hsptop | exact (Hfr a Hne) | exact Hz].
    - intros a Hdz H0. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HD a Hdz H0)|].
      eapply dzone_changed_defined; [exact HP | exact HA | | exact Hspc | exact (Hfr a Hne) | exact Hscr | exact Hdz]. intros x Hx; apply in_app_iff; right; exact Hx. }
  repeat split; assumption.
Qed.


(* [comment removed for export] *)
Lemma alloc_pre_of : forall fx R M mdl Lc B C ret n sp,
  nalloc_pre SEGS SPTOPc AINV_f FXOK G bcap ccap fx R M mdl Lc B C ret n sp ->
  alloc_pre SEGS AINVH FXOK G stk GBUDGET GCOUNT fx R M mdl (Lc ++ HID) (B0 + B) (C0 + C) ret n sp.
Proof.
  intros fx R M mdl Lc B C ret n sp
         (Hh & Hlz & Hmat & HFX & (HA & HP & HT & HF & HD) & R1 & Rr & Re & Hn & Hnr & Hsp & Hal & Hspc & Hsptop & R4 & Hstk & HB & HC).
  pose proof stk_ok. pose proof bcap_ok. pose proof ccap_ok.
  split; [exact Hh|]. split; [exact Hlz|]. split; [exact Hmat|]. split; [exact HFX|]. split; [exact HA|].
  split; [exact R1|]. split; [exact Rr|]. split; [exact Re|]. split; [exact Hn|]. split; [exact Hnr|].
  split; [exact Hsp|]. split; [exact Hal|]. split; [lia|]. split; [exact R4|].
  split; [intros a Ha; apply Hstk; lia|]. lia.
Qed.



(* [comment removed for export] *)
Theorem malloc_nspec1_of_mspec1 : forall FRESH entry,
  malloc_mspec1 SEGS AINVH FXOK RZ G FRESH stk GBUDGET GCOUNT entry ->
  malloc_nspec1 SEGS SWIN PERMc SPTOPc AINV_f FXOK RZ G bcap ccap
    (fun Lc B C M mdl n => FRESH (Lc ++ HID) (B0 + B) (C0 + C) M mdl n) entry.
Proof.
  intros FRESH entry MS fx R M mdl Lc B C ret n sp Tok PRE HFR HT1 Hok.
  pose proof PRE as (Hh & Hlz & Hmat & HFX & HAF & R1 & Rr & Re & Hn & Hnr & Hsp & Hal & Hspc & Hsptop & R4 & Hstk & HB & HC).
  apply (MS fx R M mdl (Lc ++ HID) (B0 + B) (C0 + C) ret n sp Tok (alloc_pre_of _ _ _ _ _ _ _ _ _ _ PRE) HFR HT1).
  intros fx' R' M' mdl' p POST. apply (Hok fx' R' M' mdl' p). eapply nalloc_post_ok_of; [exact HAF | exact Hspc | exact Hsptop | lia | exact Hstk | exact POST].
Qed.

Theorem opnew_nspec_of_mspec : forall entry,
  opnew_mspecR SEGS AINVH FXOK RZ G stk GBUDGET GCOUNT entry ->
  opnew_nspec SEGS SWIN PERMc SPTOPc AINV_f FXOK RZ G bcap ccap entry.
Proof.
  intros entry MS fx R M mdl Lc B C ret n sp T PRE HT0 _ Hok.
  pose proof PRE as (Hh & Hlz & Hmat & HFX & HAF & R1 & Rr & Re & Hn & Hnr & Hsp & Hal & Hspc & Hsptop & R4 & Hstk & HB & HC).
  apply (MS fx R M mdl (Lc ++ HID) (B0 + B) (C0 + C) ret n sp T (alloc_pre_of _ _ _ _ _ _ _ _ _ _ PRE) HT0).
  intros fx' R' M' mdl' p POST. apply (Hok fx' R' M' mdl' p). eapply nalloc_post_ok_of; [exact HAF | exact Hspc | exact Hsptop | lia | exact Hstk | exact POST].
Qed.

Theorem free_nspec_of_mspec : forall entry,
  free_mspecR SEGS AINVH FXOK RZ G stk entry ->
  free_nspec SEGS SWIN PERMc SPTOPc AINV_f FXOK RZ G entry.
Proof.
  intros entry FS fx R M mdl Lc Lc' B C B' C' ret sp p T Hh Hlz Hmat HFX (HA & HP & HT & HF & HD) R1 Rr Re Hp CASES Hsp Hal Hspc Hsptop R4 Hstk Hk.
  pose proof G_ro_img as GR. pose proof G_img_ceil as GC. pose proof stk_ok as SK.
  (* [comment removed for export] *)
  assert (CASES' : exists Bq Cq,
    ((p = Z_to_bv 64 0 /\ Lc' ++ HID = Lc ++ HID /\ Bq = B0 + B /\ Cq = C0 + C)
     \/ (exists m L1 L2, Lc ++ HID = L1 ++ (bv_unsigned p, m) :: L2 /\ Lc' ++ HID = L1 ++ L2
                          /\ Bq = Z.max 0 (B0 + B - mcost m) /\ Cq = Z.max 0 (C0 + C - MCNT)))
    /\ Bq <= B0 + B' /\ Cq <= C0 + C' /\ (forall x, In x Lc' -> In x Lc)).
  { destruct CASES as [(H0 & -> & -> & ->)|(m & L1 & L2 & HL & -> & HB' & HC')].
    - exists (B0 + B), (C0 + C). split; [left; repeat split; try assumption; reflexivity|]. split; [lia|]. split; [lia|]. intros x Hx; exact Hx.
    - exists (Z.max 0 (B0 + B - mcost m)), (Z.max 0 (C0 + C - MCNT)). split.
      + right. exists m, L1, (L2 ++ HID). rewrite HL. rewrite <- !app_assoc. cbn [app]. repeat split; reflexivity.
      + split; [lia|]. split; [lia|]. intros x Hx. rewrite HL. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx]. }
  destruct CASES' as (Bq & Cq & HCASE & HBq & HCq & Hsub).
  apply (FS fx R M mdl (Lc ++ HID) (Lc' ++ HID) (B0 + B) (C0 + C) Bq Cq ret sp p T Hh Hlz Hmat HFX HA R1 Rr Re Hp HCASE Hsp Hal); try assumption.
  - lia.
  - intros a Ha. apply Hstk. lia.
  - intros fx' R' M' mdl' HFX' Hkept Hfr Hscr HA' Hh' Hlz' Hmat' Hfs' Hfds'.
    apply (Hk fx' R' M' mdl' HFX' Hkept).
    + intros a Hka. destruct (decide (M' a = M a)) as [Heq|Hne]; [exact Heq|]. exfalso.
      eapply (alloc_changed_not_kept (Lc' ++ HID) Lc' sp a); [exact HA' | intros x Hx; apply in_app_iff; left; exact Hx
        | intros x Hx; apply in_app_iff; right; exact Hx | exact HP | exact Hspc | exact (Hfr a Hne) | exact Hka].
    + intros a Ha.
      assert (ST : RiscvSemantics.store_ok SEGS M' a 1 = true).
      { destruct (decide (M' a = M a)) as [Heq|Hne].
        - pose proof (Hstk a Ha) as X. cbn [RiscvSemantics.store_ok] in X |- *. unfold wview in X |- *. rewrite Heq. exact X.
        - destruct (Hfr a Hne) as [(Hhz & _ & _)|[Hsc|Hpv]].
          + exfalso. unfold MSTK in *. lia.
          + exact (Hscr a Hsc).
          + exfalso. destruct Hpv as (plo & phi & Hpin & Hpr). destruct (G_priv plo phi Hpin). unfold MSTK in *. lia. }
      split; [eapply store_ok_defined; [unfold MSTK in *; lia | exact ST] | exact ST].
    + split; [|split; [exact HP|split; [exact HT|split]]].
      * eapply AINVH_mono; [exact HA' | exact HBq | exact HCq].
      * intros a Hz. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HF a Hz)|]. exfalso.
        eapply (alloc_changed_not_zone (Lc' ++ HID) sp a); [exact HA' | intros x Hx; apply in_app_iff; right; exact Hx | exact Hspc | exact Hsptop | exact (Hfr a Hne) | exact Hz].
      * intros a Hdz H0. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HD a Hdz H0)|].
        eapply dzone_changed_defined; [exact HP | exact HA' | | exact Hspc | exact (Hfr a Hne) | exact Hscr | exact Hdz]. intros x Hx; apply in_app_iff; right; exact Hx.
    + exact Hh'.
    + exact Hlz'.
    + exact Hmat'.
    + exact Hfs'.
    + exact Hfds'.
Qed.

End Alloc.

End Frame.
End GlzFrame.
Module GlzFrameStr.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Frame.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok G b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
Hypothesis G_priv : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= bv_unsigned a < g_img_hi G) -> find_segment SEGS (bv_unsigned a) 1 = None.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HID : list (Z * Z).
Variable M0 : word -> option byte.
Variable B0 C0 : Z.
Hypothesis B0_nonneg : 0 <= B0.
Hypothesis C0_nonneg : 0 <= C0.
Variable stk : Z.
Hypothesis stk_ok : 0 <= stk /\ stk + 80 <= MSTK.
Variable bcap ccap : Z.
Hypothesis bcap_ok : B0 + bcap <= GBUDGET.
Hypothesis ccap_ok : C0 + ccap <= GCOUNT.

#[local] Notation AINV_f := (GlzFrame.AINV_f SWIN G AINVH PERMc SPTOPc HID M0 B0 C0).
#[local] Notation zone := (GlzFrame.zone SWIN G PERMc SPTOPc HID).
#[local] Notation dzone := (GlzFrame.dzone PERMc SPTOPc).
#[local] Notation perm_owned := (GlzFrame.perm_owned SWIN PERMc HID).
#[local] Notation frame_kept := (GlzSpecsStr.GlzContracts.frame_kept SWIN PERMc SPTOPc G).

Lemma defined_store_ok : forall M (a : word),
  g_img_hi G <= bv_unsigned a -> M a <> None -> RiscvSemantics.store_ok SEGS M a 1 = true.
Proof.
  intros M a Ha Hd. cbn [RiscvSemantics.store_ok]. unfold wview. rewrite (SEGS_out a ltac:(lia)).
  destruct (M a) as [b|] eqn:E; [reflexivity | exfalso; exact (Hd eq_refl)].
Qed.

(* [comment removed for export] *)
Lemma owned_not_zone : forall Lc B C M mdl (a : word),
  AINVH (Lc ++ HID) B C M mdl -> CEIL_run <= SPTOPc -> owned SWIN PERMc SPTOPc Lc a -> zone a -> False.
Proof.
  intros Lc B C M mdl a HA HT Ho (Hz1 & Hnp & Hnsw). pose proof G_ro_img. pose proof G_img_ceil.
  destruct Ho as [Hb|[Hp|[Hst|Hsw]]]; [| exact (Hnp Hp) | | exact (Hnsw Hsw)].
  - destruct Hb as (b & n & Hin & Hbz). pose proof (AINVH_zone _ _ _ _ _ b n HA ltac:(apply in_app_iff; left; exact Hin)) as (Z1 & Z2 & Z3).
    destruct Hz1 as [Hh|[Ht|Hro]]; [| lia | lia].
    destruct Hh as (b' & n' & Hin' & Hbz'). destruct (in_split _ _ Hin) as (L1 & L2 & HL).
    pose proof (AINVH_disj _ _ _ _ _ L1 (L2 ++ HID) b n b' n' HA
                 ltac:(rewrite HL; rewrite <- app_assoc; reflexivity)
                 ltac:(rewrite app_assoc; apply in_app_iff; right; exact Hin')) as D. lia.
  - destruct Hz1 as [Hh|[Ht|Hro]]; [| lia | lia].
    destruct Hh as (b' & n' & Hin' & Hbz'). pose proof (AINVH_zone _ _ _ _ _ b' n' HA ltac:(apply in_app_iff; right; exact Hin')) as (Z1 & Z2 & Z3). lia.
Qed.

Lemma stk80_ok : 0 <= stk + 80 <= MSTK. Proof. pose proof stk_ok. lia. Qed.

(* [comment removed for export] *)
Lemma scratch_after : forall Lfull (M M' : word -> option byte) (obj : word) sp (a : word),
  sp <= bv_unsigned obj -> CEIL_run + MSTK <= sp ->
  (forall x : word, sp - MSTK <= bv_unsigned x < sp -> RiscvSemantics.store_ok SEGS M x 1 = true) ->
  (forall x : word, M' x <> M x -> bv_unsigned obj <= bv_unsigned x < bv_unsigned obj + 24 \/ alloc_changed G (stk + 80) Lfull sp x) ->
  (forall x : word, sp - stk - 80 <= bv_unsigned x < sp -> RiscvSemantics.store_ok SEGS M' x 1 = true) ->
  sp - MSTK <= bv_unsigned a < sp -> M' a <> None /\ RiscvSemantics.store_ok SEGS M' a 1 = true.
Proof.
  intros Lfull M M' obj sp a Hobj Hsp Hstk Hfr Hscr Ha. pose proof G_img_ceil. pose proof stk_ok. pose proof G_ro_img.
  assert (ST : RiscvSemantics.store_ok SEGS M' a 1 = true).
  { destruct (decide (M' a = M a)) as [Heq|Hne].
    - pose proof (Hstk a Ha) as X. cbn [RiscvSemantics.store_ok] in X |- *. unfold wview in X |- *. rewrite Heq. exact X.
    - destruct (Hfr a Hne) as [Ho|[(Hhz & _ & _)|[Hsc|Hpv]]].
      + exfalso. lia.
      + exfalso. unfold MSTK in *. lia.
      + apply Hscr. lia.
      + exfalso. destruct Hpv as (plo & phi & Hpin & Hpr). destruct (G_priv plo phi Hpin). unfold MSTK in *. lia. }
  split; [eapply (store_ok_defined SEGS G SEGS_out); [unfold MSTK in *; lia | exact ST] | exact ST].
Qed.

(* [comment removed for export] *)
Lemma galloc_pos : forall n cap, 0 <= cap -> 1 <= galloc n cap.
Proof. intros n cap Hc. unfold galloc. pose proof (lor7_bounds (Z.max n (2 * cap)) ltac:(lia)). lia. Qed.

Lemma perm_disjoint : forall (p : word) (g lo hi : Z),
  perm_owned -> (forall b m, In (b, m) HID -> bv_unsigned p + g <= b \/ b + m <= bv_unsigned p) ->
  blk_ok G (bv_unsigned p) g -> 1 <= g ->
  In (lo, hi) PERMc -> lo < hi -> bv_unsigned p + g <= lo \/ hi <= bv_unsigned p.
Proof.
  intros p g lo hi HP Hd (Hlo & Hhi & Himg) Hg Hin Hlh. pose proof G_ro_img as GR.
  destruct (Z.le_gt_cases (bv_unsigned p + g) lo) as [X|X]; [left; exact X|].
  destruct (Z.le_gt_cases hi (bv_unsigned p)) as [Y|Y]; [right; exact Y|]. exfalso.
  assert (Hz : exists z, bv_unsigned p <= z < bv_unsigned p + g /\ lo <= z < hi).
  { destruct (Z.le_gt_cases lo (bv_unsigned p)); [exists (bv_unsigned p); lia | exists lo; lia]. }
  destruct Hz as (z & Hz1 & Hz2).
  assert (Hw : in_wins PERMc z) by (exists lo, hi; split; [exact Hin | lia]).
  destruct (HP z Hw) as [Hb|[Hc|Hsw]]; [| lia | destruct (swin_byte SWIN G SWIN_img _ Hsw) as [S _]; lia].
  destruct Hb as (b & m & Hb & Hbz). destruct (Hd b m Hb); lia.
Qed.

Theorem growS_nspec_of_mspec : forall entry,
  resize_growS_mspec SEGS AINVH FXOK RZ G stk GBUDGET GCOUNT entry ->
  resize_growS_nspec SEGS SWIN PERMc SPTOPc AINV_f FXOK RZ G bcap ccap entry.
Proof.
  intros entry MS fx R M mdl Lc B C ret sp obj w0 cw s n T Hh Hlz Hmat HFX (HA & HP & HT & HF & HD) HTn
         R1 Rr Re R10 R11 R12 Hsp Hal Hspc Hsptop R4 Hstk (Ho1 & Ho2 & Ho3 & Ho4) RD8 Hw0 Hs Hn HnN HB HC Hk.
  pose proof stk_ok as Sok. pose proof G_img_ceil as Gic.
  apply (MS fx R M mdl (Lc ++ HID) (B0 + B) (C0 + C) ret sp obj w0 cw s n T Hh Hlz Hmat HFX HA HTn R1 Rr Re R10 R11 R12 Hsp Hal);
    try assumption.
  - unfold MSTK in *. lia.
  - intros a Ha. apply Hstk. unfold MSTK in *. lia.
  - unfold GBUDGET in *. pose proof bcap_ok. unfold GBUDGET in *. lia.
  - pose proof ccap_ok. lia.
  - intros fx' R' M' mdl' p HFX' Hkept Ha0 Hpal Hpblk Hdisj Hblk RD0' RD1' RD2' NUL Hfr Hscr Hobjd HA' Hh' Hlz' Hmat' Hfs' Hfds'.
    apply (Hk fx' R' M' mdl' p HFX' Hkept Ha0 Hpal Hpblk).
    + intros b m Hin. apply Hdisj. apply in_app_iff. left. exact Hin.
    + intros lo hi Hin Hlh. eapply perm_disjoint; [exact HP | | exact Hpblk | apply galloc_pos; lia | exact Hin | exact Hlh].
      intros b m Hb. apply Hdisj. apply in_app_iff. right. exact Hb.
    + exact Hblk.
    + exact RD0'.
    + exact RD1'.
    + exact RD2'.
    + exact NUL.
    + intros a Hka Hno. destruct (decide (M' a = M a)) as [Heq|Hne]; [exact Heq|]. exfalso.
      destruct (Hfr a Hne) as [Hob|Hch]; [exact (Hno Hob)|].
      eapply (alloc_changed_not_kept SWIN G AINVH AINVH_zone G_ro_img G_img_ceil G_priv SWIN_img PERMc SPTOPc HID (stk + 80) stk80_ok (Lc ++ HID) Lc sp a);
        [exact HA | intros x Hx; apply in_app_iff; left; exact Hx | intros x Hx; apply in_app_iff; right; exact Hx
        | exact HP | exact Hspc | exact Hch | exact Hka].
    + intros a Ha. eapply scratch_after; [exact Ho1 | exact Hspc | exact Hstk | exact Hfr | exact Hscr | exact Ha].
    + intros a Ha. split; [exact (Hobjd a Ha)|]. apply defined_store_ok; [unfold MSTK in *; lia | exact (Hobjd a Ha)].
    + split; [|split; [exact HP|split; [exact HT|split]]].
      * cbn [app]. replace (B0 + (B + mcost (galloc n 22))) with (B0 + B + mcost (galloc n 22)) by lia.
        replace (C0 + (C + MCNT)) with (C0 + C + MCNT) by lia. exact HA'.
      * intros a Hz. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HF a Hz)|]. exfalso.
        destruct (Hfr a Hne) as [Hob|Hch].
        -- eapply (owned_not_zone Lc); [exact HA | exact HT | exact (Ho4 a Hob) | exact Hz].
        -- eapply (alloc_changed_not_zone SWIN G AINVH AINVH_zone G_ro_img G_img_ceil G_priv PERMc SPTOPc HID (stk + 80) stk80_ok (Lc ++ HID) sp a);
             [exact HA | intros x Hx; apply in_app_iff; right; exact Hx | exact Hspc | exact Hsptop | exact Hch | exact Hz].
      * intros a Hdz H0. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HD a Hdz H0)|].
        destruct (Hfr a Hne) as [Hob|Hch]; [exact (Hobjd a Hob)|].
        eapply (dzone_changed_defined SEGS SWIN G AINVH AINVH_zone G_ro_img G_img_ceil G_priv SWIN_img SEGS_out PERMc SPTOPc HID (stk + 80) stk80_ok (Lc ++ HID) sp a);
          [exact HP | exact HA | intros x Hx; apply in_app_iff; right; exact Hx | exact Hspc | exact Hch | intros x Hx; apply Hscr; lia | exact Hdz].
    + exact Hh'.
    + exact Hlz'.
    + exact Hmat'.
    + exact Hfs'.
    + exact Hfds'.
Qed.

(* [comment removed for export] *)
Section OldBlock.
Variables (L1 L2 : list (Z * Z)) (B C : Z) (M : word -> option byte) (mdl : Model) (d : word) (cap : Z).
Hypothesis HA : AINVH (L1 ++ (bv_unsigned d, cap + 1) :: L2 ++ HID) B C M mdl.
Hypothesis HP : perm_owned.
Hypothesis HT : CEIL_run <= SPTOPc.

Lemma old_zone : blk_ok G (bv_unsigned d) (cap + 1).
Proof. eapply AINVH_zone; [exact HA|]. apply in_app_iff. right. left. reflexivity. Qed.

Lemma old_disj : forall b m, In (b, m) (L1 ++ L2 ++ HID) -> bv_unsigned d + (cap + 1) <= b \/ b + m <= bv_unsigned d.
Proof. intros b m Hin. eapply (AINVH_disj _ _ _ _ _ L1 (L2 ++ HID)); [exact HA | reflexivity | exact Hin]. Qed.

Lemma old_not_owned : forall a : word,
  bv_unsigned d <= bv_unsigned a < bv_unsigned d + cap + 1 -> owned SWIN PERMc SPTOPc (L1 ++ L2) a -> False.
Proof.
  intros a Ha Ho. pose proof old_zone as (Z1 & Z2 & Z3). pose proof G_img_ceil. pose proof G_ro_img.
  destruct Ho as [Hb|[Hp|[Hst|Hsw]]].
  - destruct Hb as (b & n & Hin & Hbz).
    destruct (old_disj b n ltac:(rewrite app_assoc; apply in_app_iff; left; exact Hin)); lia.
  - destruct (HP _ Hp) as [Hh|[Hc|Hsw]]; [|lia| destruct (swin_byte SWIN G SWIN_img _ Hsw) as [S _]; lia]. destruct Hh as (b & n & Hin & Hbz).
    destruct (old_disj b n ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hin)); lia.
  - lia.
  - destruct Hsw as (lo & hi & Hin & Hr). destruct (SWIN_img lo hi Hin) as (S1 & S2 & _). lia.
Qed.

Lemma old_not_kept : forall (a : word) sp, CEIL_run + MSTK <= sp ->
  bv_unsigned d <= bv_unsigned a < bv_unsigned d + cap + 1 -> frame_kept (L1 ++ L2) sp a -> False.
Proof.
  intros a sp Hsp Ha Hk. pose proof old_zone as (Z1 & Z2 & Z3). pose proof G_img_ceil. pose proof G_ro_img.
  destruct Hk as [[Ho _]|[[Hro _]|[Hab Hspt]]]; [exact (old_not_owned a Ha Ho) | lia | lia].
Qed.

Lemma old_not_zone : forall a : word, bv_unsigned d <= bv_unsigned a < bv_unsigned d + cap + 1 -> zone a -> False.
Proof.
  intros a Ha (Hz1 & Hnp & Hnsw). pose proof old_zone as (Z1 & Z2 & Z3). pose proof G_img_ceil. pose proof G_ro_img.
  destruct Hz1 as [Hh|[Ht|Hro]]; [| lia | lia].
  destruct Hh as (b & n & Hin & Hbz). destruct (old_disj b n ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hin)); lia.
Qed.

Lemma old_not_dzone : forall a : word, bv_unsigned d <= bv_unsigned a < bv_unsigned d + cap + 1 -> dzone a -> False.
Proof.
  intros a Ha Hdz. pose proof old_zone as (Z1 & Z2 & Z3). pose proof G_ro_img as GR. destruct Hdz as [Hst|Hp]; [lia|].
  destruct (HP _ Hp) as [Hh|[Hc|Hsw]]; [|lia| destruct (swin_byte SWIN G SWIN_img _ Hsw) as [S _]; lia]. destruct Hh as (b & n & Hin & Hbz).
  destruct (old_disj b n ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hin)); lia.
Qed.

(* [comment removed for export] *)
Lemma alloc_changed_old : forall s sp (a : word),
  alloc_changed G s (L1 ++ L2 ++ HID) sp a ->
  (bv_unsigned d <= bv_unsigned a < bv_unsigned d + cap + 1) \/ alloc_changed G s (L1 ++ (bv_unsigned d, cap + 1) :: L2 ++ HID) sp a.
Proof.
  intros s sp a Hch.
  destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned d)) as [Hlt|Hge];
    [| destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned d + cap + 1)) as [Hlt2|Hge2]; [left; lia|]]; right.
  all: destruct Hch as [(Hhz & Hni & Hnb)|[Hsc|Hpv]]; [left | right; left; exact Hsc | right; right; exact Hpv].
  all: split; [exact Hhz|]; split; [exact Hni|]; intros (b & n & Hin & Hbz); apply in_app_iff in Hin as [Hin|Hin];
       [apply Hnb; exists b, n; split; [apply in_app_iff; left; exact Hin | exact Hbz]|].
  all: destruct Hin as [Hdn|Hin]; [injection Hdn as <- <-; lia|].
  all: apply Hnb; exists b, n; split; [apply in_app_iff; right; exact Hin | exact Hbz].
Qed.
End OldBlock.

Theorem growL_nspec_of_mspec : forall entry,
  resize_growL_mspec SEGS AINVH FXOK RZ G stk GBUDGET GCOUNT entry ->
  resize_growL_nspec SEGS SWIN PERMc SPTOPc AINV_f FXOK RZ G bcap ccap entry.
Proof.
  intros entry MS fx R M mdl L1 L2 B C ret sp obj d w0 cw cap s n T Hh Hlz Hmat HFX (HA & HP & HT & HF & HD) HTn
         R1 Rr Re R10 R11 R12 Hsp Hal Hspc Hsptop R4 Hstk (Ho1 & Ho2 & Ho3 & Ho4) RD8 Hw0 Hcap8 Hcap23 RDs RDd
         Hs Hn HnN HcN Hdobj Hblk HB HC Hk.
  pose proof stk_ok as Sok. pose proof G_img_ceil as Gic. pose proof G_ro_img as Gri.
  assert (HAx : AINVH (L1 ++ (bv_unsigned d, cap + 1) :: L2 ++ HID) (B0 + B) (C0 + C) M mdl).
  { rewrite <- app_assoc in HA. exact HA. }
  pose proof (old_zone L1 L2 _ _ _ _ d cap HAx) as Zd. pose proof Zd as (Zd1 & Zd2 & Zd3).
  apply (MS fx R M mdl L1 (L2 ++ HID) (B0 + B) (C0 + C) ret sp obj d w0 cw cap s n T Hh Hlz Hmat HFX HAx HTn R1 Rr Re R10 R11 R12 Hsp Hal);
    try assumption.
  - unfold MSTK in *. lia.
  - intros a Ha. apply Hstk. unfold MSTK in *. lia.
  - intros a Ha. split; [| exact (Hblk a Ha)]. eapply (store_ok_defined SEGS G SEGS_out); [lia | exact (Hblk a Ha)].
  - pose proof bcap_ok. lia.
  - pose proof ccap_ok. lia.
  - intros fx' R' M' mdl' p HFX' Hkept Ha0 Hpal Hpblk Hdisj Hblk' RD0' RD1' RD2' NUL Hfr Hscr Hobjd HA' Hh' Hlz' Hmat' Hfs' Hfds'.
    apply (Hk fx' R' M' mdl' p HFX' Hkept Ha0 Hpal Hpblk).
    + intros b m Hin. apply Hdisj. rewrite app_assoc. apply in_app_iff. left. exact Hin.
    + intros lo hi Hin Hlh. eapply perm_disjoint; [exact HP | | exact Hpblk | apply galloc_pos; lia | exact Hin | exact Hlh].
      intros b m Hb. apply Hdisj. apply in_app_iff. right. apply in_app_iff. right. exact Hb.
    + exact Hblk'.
    + exact RD0'.
    + exact RD1'.
    + exact RD2'.
    + exact NUL.
    + intros a Hka Hno. destruct (decide (M' a = M a)) as [Heq|Hne]; [exact Heq|]. exfalso.
      destruct (Hfr a Hne) as [Hob|Hch]; [exact (Hno Hob)|].
      destruct (alloc_changed_old L1 L2 d cap _ sp a Hch) as [Hold|Hch'].
      * exact (old_not_kept L1 L2 _ _ _ _ d cap HAx HP a sp Hspc Hold Hka).
      * eapply (alloc_changed_not_kept SWIN G AINVH AINVH_zone G_ro_img G_img_ceil G_priv SWIN_img PERMc SPTOPc HID (stk + 80) stk80_ok _ (L1 ++ L2) sp a);
          [exact HAx | | | exact HP | exact Hspc | exact Hch' | exact Hka].
        -- intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; apply in_app_iff; left; exact Hx].
        -- intros x Hx. apply in_app_iff. right. right. apply in_app_iff. right. exact Hx.
    + intros a Ha. eapply (scratch_after (L1 ++ L2 ++ HID)); [exact Ho1 | exact Hspc | exact Hstk | | exact Hscr | exact Ha].
      intros x Hx. exact (Hfr x Hx).
    + intros a Ha. split; [exact (Hobjd a Ha)|]. apply defined_store_ok; [unfold MSTK in *; lia | exact (Hobjd a Ha)].
    + split; [|split; [exact HP|split; [exact HT|split]]].
      * cbn [app]. rewrite <- app_assoc. eapply AINVH_mono; [exact HA'| |]; pose proof B0_nonneg; pose proof C0_nonneg; lia.
      * intros a Hz. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HF a Hz)|]. exfalso.
        destruct (Hfr a Hne) as [Hob|Hch].
        -- eapply (owned_not_zone (L1 ++ (bv_unsigned d, cap + 1) :: L2)); [exact HA | exact HT | | exact Hz].
           destruct (Ho4 a Hob) as [Hb|Hr]; [left | right; exact Hr].
           destruct Hb as (b & m & Hin & Hbz). exists b, m. split; [|exact Hbz].
           apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; exact Hin | right; right; exact Hin].
        -- destruct (alloc_changed_old L1 L2 d cap _ sp a Hch) as [Hold|Hch'].
           ++ exact (old_not_zone L1 L2 _ _ _ _ d cap HAx HT a Hold Hz).
           ++ eapply (alloc_changed_not_zone SWIN G AINVH AINVH_zone G_ro_img G_img_ceil G_priv PERMc SPTOPc HID (stk + 80) stk80_ok _ sp a);
                [exact HAx | | exact Hspc | exact Hsptop | exact Hch' | exact Hz].
              intros x Hx. apply in_app_iff. right. right. apply in_app_iff. right. exact Hx.
      * intros a Hdz H0. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HD a Hdz H0)|].
        destruct (Hfr a Hne) as [Hob|Hch]; [exact (Hobjd a Hob)|].
        destruct (alloc_changed_old L1 L2 d cap _ sp a Hch) as [Hold|Hch'].
        -- exfalso. exact (old_not_dzone L1 L2 _ _ _ _ d cap HAx HP a Hold Hdz).
        -- eapply (dzone_changed_defined SEGS SWIN G AINVH AINVH_zone G_ro_img G_img_ceil G_priv SWIN_img SEGS_out PERMc SPTOPc HID (stk + 80) stk80_ok _ sp a);
             [exact HP | exact HAx | | exact Hspc | exact Hch' | intros x Hx; apply Hscr; lia | exact Hdz].
           intros x Hx. apply in_app_iff. right. right. apply in_app_iff. right. exact Hx.
    + exact Hh'.
    + exact Hlz'.
    + exact Hmat'.
    + exact Hfs'.
    + exact Hfds'.
Qed.
End Frame.
End GlzFrameStr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzNodesAlloc.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS. Import GCL.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma callee_saved_of_not_caller : forall n, (n < 32)%nat -> n <> 0%nat -> ~ In n caller_saved ->
  In (Z.of_nat n) callee_saved_regs.
Proof.
  intros n Hn.
  do 32 (destruct n as [|n];
    [intros A B; first [exfalso; apply A; reflexivity | exfalso; apply B; cbn; tauto | cbn; tauto] |]).
  lia.
Qed.

Lemma kept_ok_of_callee_saved : forall R R',
  (forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) -> kept_ok R R'.
Proof.
  intros R R' H r Hr0 Hnin.
  pose proof (ridx_range r) as Hrr.
  assert (Hnz : ridx r <> 0%nat).
  { intros X. apply Hr0. apply bv_eq. unfold ridx in X. 
    replace (bv_unsigned (0%bv : bv 5)) with 0 by reflexivity. pose proof (bv_unsigned_in_range _ r). lia. }
  rewrite (reg_of_ridx r (ridx r) eq_refl). apply H. apply callee_saved_of_not_caller; assumption.
Qed.

Lemma kn_vars_lt_forallb : forall b k, AP.kn_vars_lt b k = forallb (kentry_vars_lt b) k.
Proof. intros b k. induction k as [|K r IH]; [reflexivity|]. cbn [AP.kn_vars_lt forallb]. rewrite IH. reflexivity. Qed.



Lemma store_ok_bytes : forall SEGS M (a : word) n (x : word),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 -> store_ok SEGS M a n = true ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> store_ok SEGS M x 1 = true.
Proof.
  intros SEGS M a n x Hnw Hs Hx. apply store_ok_of_all; [change (Z.of_nat 1) with 1; lia|].
  intros y Hy. eapply store_ok_all; [exact Hnw | exact Hs | change (Z.of_nat 1) with 1 in Hy; lia].
Qed.

Lemma cost_hi_sound : forall SEGS E M k live ch,
  know_ok SEGS E M k -> cost_hi k live = Some ch -> GPS.bcost E live <= ch /\ 0 <= GPS.bcost E live.
Proof.
  intros SEGS E M k live. induction live as [|[b n] r IH]; intros ch HK H; cbn [cost_hi GPS.bcost] in H |- *.
  - injection H as <-. lia.
  - cbn [snd]. destruct (xhi k n) as [h|] eqn:Hh; [|discriminate]. destruct (cost_hi k r) as [c|] eqn:Hc; [|discriminate].
    injection H as <-. destruct (IH c HK eq_refl) as [IH1 IH2].
    pose proof (xhi_sound SEGS E M k n h HK Hh). pose proof (u64_range (edenot E n)). unfold GPS.uE, GPS.MBLK, GlzIface.MBLK in *. lia.
Qed.

Lemma bcost_app : forall E l1 l2, GPS.bcost E (l1 ++ l2) = GPS.bcost E l1 + GPS.bcost E l2.
Proof. intros E l1 l2. induction l1 as [|p r IH]; [reflexivity|]. cbn [app GPS.bcost]. rewrite IH. lia. Qed.
Lemma bcost_nonneg : forall E l, 0 <= GPS.bcost E l.
Proof. intros E l. induction l as [|p r IH]; cbn [GPS.bcost]; [lia|]. pose proof (u64_range (edenot E (snd p))). unfold GPS.uE, GPS.MBLK. lia. Qed.
Lemma bcount_app : forall l1 l2 : list (expr * expr), GPS.bcount (l1 ++ l2) = GPS.bcount l1 + GPS.bcount l2.
Proof. intros. unfold GPS.bcount. rewrite length_app. lia. Qed.

Lemma align16_of_ealign : forall a (z : Z), 4 <= a <= 64 -> (2 ^ a | z) -> z mod 16 = 0.
Proof.
  intros a z Ha [q ->]. replace a with (a - 4 + 4) by lia. rewrite Z.pow_add_r by lia.
  change (2 ^ 4) with 16. rewrite Z.mul_assoc. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINV_mono : forall Lc B C B' C' M mdl,
  AINV Lc B C M mdl -> B <= B' -> C <= C' -> AINV Lc B' C' M mdl.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.
Variable G : gtable.
Variable bcap ccap : Z.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ).

Lemma some_inj : forall {A} (a b : A), Some a = Some b -> a = b.
Proof. intros A a b H. injection H as H. exact H. Qed.

(* [comment removed for export] *)
Lemma call_ok_sound : forall entry cs ret E fx R M model,
  cs_ok E cs fx R M model -> call_ok nx0 G entry cs = Some ret ->
  let k := kn cs in let sp := reg cs 2 in let '(spb, spk) := split_lit sp in
  pc cs = entry
  /\ fresh_ok nx0 cs = true /\ length (s_regs (a_ss cs)) = 32%nat
  /\ getr R (Z_to_bv 5 1) = Z_to_bv 64 ret /\ 0 <= ret < 2 ^ 64 /\ ret mod 2 = 0
  /\ getr R (Z_to_bv 5 4) = Z_to_bv 64 (g_tp G)
  /\ getr R (Z_to_bv 5 2) = edenot E sp
  /\ uE E sp = uE E spb + spk /\ uE E sp mod 16 = 0 /\ CEIL_run + MSTK <= uE E sp /\ uE E sp <= SPTOPc
  /\ (forall a : word, uE E sp - MSTK <= bv_unsigned a < uE E sp -> store_ok SEGS M a 1 = true)
  /\ forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (a_vis cs ++ a_ghost cs) = true.
Proof.
  intros entry cs ret E fx R M model HC H.
  unfold call_ok in H.
  destruct (negb (Z.eqb (pc cs) entry)) eqn:Hpc; [discriminate|]. apply negb_false_iff in Hpc. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret'|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 4) as [tp|] eqn:Htp; [|discriminate].
  cbv zeta in H.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as ->.
  apply andb_prop in Hc as [Hc Hflat]. apply andb_prop in Hc as [Hc Hfl]. apply andb_prop in Hc as [Hc Hkw].
  apply andb_prop in Hc as [Hc Hal]. apply andb_prop in Hc as [Hc Hlen]. apply andb_prop in Hc as [Htpe Hfresh].
  apply Z.eqb_eq in Htpe. subst tp. apply Nat.eqb_eq in Hlen. apply Z.leb_le in Hal.
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  destruct (ret_lit_sound E cs R ret HR Hret) as (R1 & _ & Rr & Re).
  destruct (reg_lit_sound E cs R 4 (g_tp G) HR ltac:(lia) Htp) as [R4 _].
  pose proof (reg_sound E cs R 2 HR ltac:(lia)) as R2.
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) spb (spk - MSTK) (ELit MSTK) HK HK Hkw) as (W1 & W2 & W3).
  rewrite elenZ_lit in W1, W3 by (unfold MSTK; lia). rewrite estart_SA in W1, W2, W3.
  pose proof (split_lit_denot E (reg cs 2) spb spk Hsp) as Hspd.
  destruct (ealign_sound SEGS E M (kn cs) (reg cs 2) HK) as [A1 A2].
  pose proof (u64_range (edenot E spb)) as Rspb.
  (* [comment removed for export] *)
  assert (FL : forall z, bv_unsigned (edenot E spb) + (spk - MSTK) <= z < bv_unsigned (edenot E spb) + (spk - MSTK) + MSTK ->
               CEIL_run <= z < SPTOPc /\ SPTOPc < 2 ^ 64).
  { intros z Hz. rewrite <- (co_top HC).
    assert (Hz64 : 0 <= z < 2 ^ 64) by (unfold MSTK in *; lia).
    pose proof (GPS.in_floor_sound SEGS E M (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - MSTK) (ELit MSTK) (Z_to_bv 64 z)
                  HK Hfl (co_floor HC)) as X.
    rewrite estart_SA, elenZ_lit, u64_lit in X by (unfold MSTK in *; lia). apply X. lia. }
  assert (Hspv : uE E (reg cs 2) = uE E spb + spk).
  { unfold uE. rewrite Hspd. apply u64_lit. pose proof (FL (bv_unsigned (edenot E spb) + spk - 1) ltac:(unfold MSTK; lia)).
    pose proof GlzConst.ceil_lo. unfold MSTK in *. lia. }
  cbv zeta. rewrite Hsp.
  split; [exact Hpc|]. split; [exact Hfresh|]. split; [exact Hlen|]. split; [exact R1|]. split; [unfold two64 in Rr; lia|].
  split; [exact Re|]. split; [exact R4|]. split; [exact R2|]. split; [exact Hspv|].
  split; [eapply align16_of_ealign; [| exact A2]; lia|].
  split; [pose proof (FL (bv_unsigned (edenot E spb) + spk - MSTK) ltac:(unfold MSTK; lia)); unfold uE in *; lia|].
  split; [pose proof (FL (bv_unsigned (edenot E spb) + spk - 1) ltac:(unfold MSTK; lia)); unfold uE in *; lia|].
  split; [|exact Hflat].
  intros a Ha. eapply (store_ok_bytes SEGS M (Z_to_bv 64 (bv_unsigned (edenot E spb) + (spk - MSTK))) (Z.to_nat MSTK));
    [rewrite u64_lit by lia; unfold MSTK in *; lia | apply W1; lia | rewrite u64_lit by lia; unfold uE, MSTK in *; lia].
Qed.

(* [comment removed for export] *)
Lemma in_floor_top_ok : forall k fl top bud b off n, in_floor k fl top bud b off n = true -> top_ok k fl top bud = true.
Proof.
  intros k fl top bud b off n H. unfold in_floor in H. unfold top_ok.
  destruct (split_lit top) as [tb tk]. destruct (base_range k tb) as [[tlo thi]|]; [|destruct fl; discriminate].
  destruct fl as [f|]; [apply andb_prop in H as [H _]|]; apply andb_prop in H as [H _]; exact H.
Qed.

Lemma call_ok_top_ok : forall entry cs ret, call_ok nx0 G entry cs = Some ret -> top_ok (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) = true.
Proof.
  intros entry cs ret H. unfold call_ok in H.
  destruct (negb (Z.eqb (pc cs) entry)); [discriminate|].
  destruct (ret_lit cs); [|discriminate]. destruct (reg_lit cs 4); [|discriminate].
  cbv zeta in H. destruct (split_lit (reg cs 2)) as [spb spk].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [_ Hfl]. exact (in_floor_top_ok _ _ _ _ _ _ _ Hfl).
Qed.

Lemma top_ok_sound : forall E M k fl top bud tb tk,
  know_ok SEGS E M k -> top_ok k fl top bud = true -> split_lit top = (tb, tk) ->
  sptop_den E top = bv_unsigned (edenot E tb) + tk /\ 0 <= bud /\ 0 < bv_unsigned (edenot E tb) + tk < 2 ^ 64
  /\ (fl = None -> CEIL + bud <= bv_unsigned (edenot E tb) + tk).
Proof.
  intros E M k fl top bud tb tk HK H Hsp. unfold top_ok in H. rewrite Hsp in H.
  destruct (base_range k tb) as [[tlo thi]|] eqn:Hbr; [|destruct fl; discriminate].
  pose proof (base_range_sound SEGS E M k tb tlo thi HK Hbr) as [B1 B2].
  pose proof (u64_range (edenot E tb)) as Rt.
  assert (NUM : 0 <= bud /\ 0 < tlo + tk /\ thi + tk < 2 ^ 64 /\ (fl = None -> CEIL + bud <= tlo + tk)).
  { destruct fl as [f|]; apply andb_prop in H as [H H3]; apply andb_prop in H as [H1 H2];
      apply Z.leb_le in H1; apply Z.ltb_lt in H3; [apply Z.ltb_lt in H2 | apply Z.leb_le in H2]; unfold CEIL, two64 in *;
      (split; [lia|]); (split; [lia|]); (split; [lia|]); intros HN; [discriminate HN | lia]. }
  destruct NUM as (N1 & N2 & N3 & N4).
  assert (Ht : uE E top = bv_unsigned (edenot E tb) + tk).
  { unfold uE. rewrite (split_lit_denot E top tb tk Hsp). apply u64_lit. lia. }
  unfold sptop_den. rewrite Ht. destruct (Z.eqb_spec (bv_unsigned (edenot E tb) + tk) 0) as [Hz|Hz]; [lia|].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. intros HN. specialize (N4 HN). lia.
Qed.

(* [comment removed for export] *)
Lemma floor_win_sound : forall E M k fl top bud tb tk fwb fwo fwl,
  know_ok SEGS E M k -> top_ok k fl top bud = true -> split_lit top = (tb, tk) ->
  GPS.floor_sem E fl top bud -> floor_win fl top bud = (SA fwb fwo, fwl) ->
  CEIL_run <= uE E fwb + fwo /\ fwl = ELit (bud + WSTK).
Proof.
  intros E M k fl top bud tb tk fwb fwo fwl HK Htok Hsp Hfl Hfw.
  destruct (top_ok_sound E M k fl top bud tb tk HK Htok Hsp) as (TOPEQ & Hb & TOPR & TOPN).
  destruct fl as [f|]; cbn [floor_win GPS.floor_sem] in Hfw, Hfl.
  - injection Hfw as <- <- <-. split; [unfold uE in *; lia | reflexivity].
  - rewrite Hsp in Hfw. injection Hfw as <- <- <-. rewrite TOPEQ in Hfl. split; [unfold uE in *; lia | reflexivity].
Qed.
Lemma floor_win_vars : forall v ms top bud fwb fwo fwl,
  AP.maps_vars_lt v ms = true -> AP.expr_vars_lt v top = true ->
  floor_win (acs_floor ms) top bud = (SA fwb fwo, fwl) -> AP.expr_vars_lt v fwb = true.
Proof.
  intros v ms top bud fwb fwo fwl Hms Htop Hfw. destruct ms as [|[f l kd] r]; cbn [acs_floor floor_win] in Hfw.
  - destruct (split_lit top) as [tb tk] eqn:Hsp. injection Hfw as <- <- <-. eapply GCL.split_lit_vars; [exact Hsp | exact Htop].
  - injection Hfw as <- <- <-. cbn [AP.maps_vars_lt forallb am_base am_len] in Hms.
    apply andb_prop in Hms as [Hms _]. apply andb_prop in Hms as [Hf _]. exact Hf.
Qed.

(* [comment removed for export] *)
Lemma disj_facts_ok : forall E M M0 k p n live (pw : word),
  know_ok SEGS E M0 k ->
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) live = true ->
  edenot E p = pw ->
  (forall b m, In (b, m) (blocks_den E live) -> bv_unsigned pw + uE E n <= b \/ b + m <= bv_unsigned pw) ->
  know_ok SEGS E M (disj_facts p n live).
Proof.
  intros E M M0 k p n live pw HK Hflat Hp Hd. unfold disj_facts, know_ok. apply Forall_forall. intros K HKin.
  apply in_map_iff in HKin as [[b0 ln] [HKe Hin]]. cbn [fst snd] in HKe.
  destruct (split_lit b0) as [lb lk] eqn:Hs. subst K. cbn [kentry_ok].
  rewrite !estart_SA. cbn [edenot]. rewrite Hp. unfold elenZ.
  pose proof (split_lit_denot E b0 lb lk Hs) as Hd0.
  pose proof (proj1 (forallb_forall _ _) Hflat _ Hin) as Hfl. cbn [fst snd] in Hfl. rewrite Hs in Hfl.
  pose proof (bflat_x_sound SEGS E _ k lb lk ln HK Hfl) as (F1 & F2 & F3). rewrite !estart_SA in F1, F2, F3.
  specialize (Hd (uE E b0) (uE E ln)).
  assert (Hin' : In (uE E b0, uE E ln) (blocks_den E live)).
  { unfold blocks_den. apply in_map_iff. exists (b0, ln). split; [reflexivity | exact Hin]. }
  specialize (Hd Hin'). unfold uE in Hd. rewrite Hd0 in Hd. rewrite u64_lit in Hd by lia.
  pose proof (u64_range pw). lia.
Qed.

Lemma blocks_den_app : forall E l1 l2, blocks_den E (l1 ++ l2) = blocks_den E l1 ++ blocks_den E l2.
Proof. intros. unfold blocks_den. apply map_app. Qed.

(* [comment removed for export] *)
Lemma kentry_range_foot : forall E M K b off len,
  kentry_ok SEGS E M K -> kentry_range K = Some (b, off, len) ->
  kfoot E K = Some (estart E (SA b off), uE E len).
Proof.
  intros E M K b off len HK HR.
  destruct K as [[b' o'] w vv|[b' o'] nn|[b' o'] nn kb|ilo ihi|e m|e rlo rhi|[b' o'] nn|a1 n1 a2 n2|[b' o'] nn fc|[b' o'] nn];
    cbn [kentry_range] in HR; try discriminate; injection HR as <- <- <-; cbn [kfoot]; try reflexivity.
  cbn [kentry_ok] in HK. destruct HK as (Hw & _ & _). unfold uE. cbn [edenot]. rewrite u64_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kdisj_of_facts_ok : forall E M M0 k (p n : expr) (pw : word) ks acc,
  know_ok SEGS E M0 k -> edenot E p = pw ->
  (forall K b off len, In K ks -> kentry_range K = Some (b, off, len) -> 1 <= uE E len ->
      bv_unsigned pw + uE E n <= uE E b + off \/ uE E b + off + uE E len <= bv_unsigned pw) ->
  know_ok SEGS E M acc ->
  know_ok SEGS E M (kdisj_of_facts k p n ks acc).
Proof.
  intros E M M0 k p n pw ks. induction ks as [|K r IH]; intros acc HK Hp Hsep Hacc; [exact Hacc|].
  cbn [kdisj_of_facts].
  assert (REST : forall acc', know_ok SEGS E M acc' -> know_ok SEGS E M (kdisj_of_facts k p n r acc')).
  { intros acc' Hacc'. apply IH; [exact HK | exact Hp | | exact Hacc'].
    intros K' b off len HK' HR Hl. apply (Hsep K' b off len); [right; exact HK' | exact HR | exact Hl]. }
  destruct (kdisj_of_fact k p n K) as [D|] eqn:HD; [|apply REST; exact Hacc].
  destruct (existsb (kentry_eqb D) acc); [apply REST; exact Hacc|].
  apply REST. constructor; [|exact Hacc].
  unfold kdisj_of_fact in HD. destruct (kentry_range K) as [[[b off] len]|] eqn:HR; [|discriminate].
  assert (GEN : forall l, xlo k len = Some l -> 1 <= l -> D = KDisj (SA p 0) n (SA b off) len -> kentry_ok SEGS E M D).
  { intros l Hxl Hl1 ->. pose proof (xlo_sound SEGS E M0 k len l HK Hxl) as Hlen.
    cbn [kentry_ok]. rewrite !estart_SA. cbn [edenot a_base a_off]. rewrite Hp. unfold elenZ.
    destruct (Hsep K b off len (or_introl eq_refl) HR ltac:(unfold uE; lia)) as [H|H]; unfold uE in *; lia. }
  destruct b as [bz| | | | | | |]; try discriminate HD;
    (destruct (xlo k len) as [l|] eqn:Hxl; [|discriminate HD]); (destruct (Z.leb 1 l) eqn:Hl1; [|discriminate HD]);
    injection HD as <-; apply Z.leb_le in Hl1; exact (GEN l eq_refl Hl1 eq_refl).
Qed.

(* [comment removed for export] *)
Lemma block_not_kept_loc : forall Lc (p n sp : Z) z,
  blk_ok G p n -> g_img_lo G <= g_ro_lo G ->
  (forall b m, In (b, m) Lc -> p + n <= b \/ b + m <= p) ->
  (forall lo hi, In (lo, hi) PERMc -> lo < hi -> p + n <= lo \/ hi <= p) ->
  CEIL_run <= sp -> sp <= SPTOPc ->
  p <= z < p + n -> ~ kept_loc PERMc SPTOPc G Lc z.
Proof.
  intros Lc p n sp z (K1 & K2 & K3) Gimg Hdisj Hperm Hsp Htop Hz [Hb|[Hp|[Hst|[Hab|Him]]]].
  - destruct Hb as (b & m & Hin & Hbz). destruct (Hdisj b m Hin); lia.
  - destruct Hp as (lo & hi & Hin & Hlh). destruct (Hperm lo hi Hin ltac:(lia)); lia.
  - lia.
  - lia.
  - lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac node_alloc_prologue HC Hco Hn entry cs cs' ret E fx R M model :=
  unfold node_alloc in Hn;
  rewrite Hco in Hn;
  pose proof (call_ok_sound entry cs ret E fx R M model HC Hco) as CO;
  cbv zeta in Hn; cbv zeta in CO;
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp;
  destruct CO as (Hpc & Hfresh & Hlen & R1 & Rr & Re & R4 & R2 & Hspv & Hal & Hsplo & Hsptop & Hstk & Hflat);
  destruct (xlo (kn cs) (reg cs 10)) as [nlo|] eqn:Hnlo; [|discriminate];
  destruct (xhi (kn cs) (reg cs 10)) as [nhi|] eqn:Hnhi; [|discriminate];
  destruct (cost_hi (kn cs) (a_vis cs)) as [ch|] eqn:Hch; [|discriminate];
  lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate];
  apply andb_prop in Hc as [Hc Hnv]; apply andb_prop in Hc as [Hc HC'];
  apply andb_prop in Hc as [Hc HB']; apply andb_prop in Hc as [Hn1 HnN];
  apply Z.leb_le in Hn1; apply Z.leb_le in HnN; apply Z.leb_le in HB'; apply Z.leb_le in HC';
  apply some_inj in Hn; subst cs';
  pose proof (co_regs HC) as HR; pose proof (co_know HC) as HK;
  destruct (cost_hi_sound SEGS E M (kn cs) (a_vis cs) ch HK Hch) as [Hcost Hcost0];
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle);
  pose proof (xlo_sound SEGS E M (kn cs) (reg cs 10) nlo HK Hnlo) as Nlo;
  pose proof (xhi_sound SEGS E M (kn cs) (reg cs 10) nhi HK Hnhi) as Nhi;
  pose proof (reg_sound E cs R 10 HR ltac:(lia)) as R10;
  set (n := uE E (reg cs 10)) in *;
  set (Lc := blocks_den E (a_vis cs));
  assert (Hceil : CEIL_run <= sp_lin E (reg cs 2)) by (unfold sp_lin; rewrite Hsp; unfold MSTK in *; lia)
  end.

(* [comment removed for export] *)
Lemma node_alloc_pre_sound : forall entry cs cs' ret E fx R M model,
  cs_ok E cs fx R M model -> call_ok nx0 G entry cs = Some ret -> node_alloc nx0 G bcap ccap entry cs = Some cs' ->
  pc cs = entry
  /\ nalloc_pre SEGS SPTOPc AINV FXOK G bcap ccap fx R M model (blocks_den E (a_vis cs)) (GPS.bcost E (a_vis cs)) (GPS.bcount (a_vis cs))
                ret (uE E (reg cs 10)) (uE E (reg cs 2)).
Proof.
  intros entry cs cs' ret E fx R M model HC Hco Hn.
  node_alloc_prologue HC Hco Hn entry cs cs' ret E fx R M model.
  split; [exact Hpc|]. unfold nalloc_pre.
  split; [exact (co_halt HC)|]. split; [exact (co_lazy HC)|]. split; [exact (co_mat HC)|]. split; [exact (co_fx HC)|].
  split; [exact (co_ainv HC)|]. split; [exact R1|]. split; [exact Rr|]. split; [exact Re|].
  split; [unfold n, uE; rewrite <- R10; reflexivity|]. split; [unfold n, uE; lia|].
  split; [unfold uE; rewrite <- R2; reflexivity|]. split; [exact Hal|]. split; [exact Hsplo|]. split; [exact Hsptop|].
  split; [exact R4|]. split; [exact Hstk|]. split; [unfold mcost in *; unfold n, uE; lia | unfold GPS.bcount; lia].
Qed.

(* [comment removed for export] *)
Lemma node_alloc_ok_sound : forall entry cs cs' ret E fx R M model fx' R' M' mdl' (p : word),
  g_img_lo G <= g_ro_lo G -> 0 <= g_img_lo G <= g_img_hi G /\ g_img_hi G < 2 ^ 64 ->
  cs_ok E cs fx R M model -> call_ok nx0 G entry cs = Some ret -> node_alloc nx0 G bcap ccap entry cs = Some cs' ->
  nalloc_post_ok SEGS SWIN PERMc SPTOPc AINV FXOK G fx R M model (blocks_den E (a_vis cs)) (GPS.bcost E (a_vis cs)) (GPS.bcount (a_vis cs))
                 (uE E (reg cs 10)) (uE E (reg cs 2)) fx' R' M' mdl' p ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' fx' R' M' mdl' /\ pc cs' = ret.
Proof.
  intros entry cs cs' ret E fx R M model fx' R' M' mdl' p Gimg Gimg2 HC Hco Hn.
  node_alloc_prologue HC Hco Hn entry cs cs' ret E fx R M model.
  intros (HFX' & Hkept & Ha0 & Hpal & Hblk & Hdisj & Hpermd & Hdef & Hfr & Hscr & HAINV' & Hh' & Hlz' & Hmat' & Hfs' & Hfds').
  set (v := nxt cs) in *.
  set (E1 := ext1 E v p).
  set (E' := ext_call E1 (S v) R').
  assert (Hag1 : env_agree v E E1) by apply ext1_agree.
  assert (Hag2 : env_agree (S v) E1 E') by apply ext_call_agree.
  assert (Hag : env_agree v E E') by (eapply env_agree_trans; [exact Hag1 | eapply env_agree_le; [exact Hag2 | lia]]).
  assert (Hpv : edenot E' (EVar v) = p).
  { cbn [edenot]. rewrite <- (proj1 Hag2 v ltac:(lia)). unfold E1. apply ext1_at. }
  assert (Hne : edenot E' (reg cs 10) = edenot E (reg cs 10)) by (symmetry; eapply edenot_agree'; [exact Hag | exact Hnv]).
  assert (Hnr : 0 <= n) by (unfold n, uE; pose proof (u64_range (edenot E (reg cs 10))); lia).
  assert (HKE' : know_ok SEGS E' M (kn cs)) by (eapply know_ok_agree'; [exact Hag | exact Fkn | exact HK]).
  assert (HLc : blocks_den E' (a_vis cs) = Lc) by (unfold Lc; eapply blocks_den_agree; [exact Hag | exact (pairs_vars_lt_app_l _ _ _ Fallow)]).
  assert (Hsp2 : edenot E' (reg cs 2) = edenot E (reg cs 2)).
  { symmetry. eapply (edenot_agree' v); [exact Hag|]. unfold reg. apply nth_sr_vars_lt; [exact Fsr | lia]. }
  assert (Hspb : edenot E' spb = edenot E spb).
  { symmetry. eapply (edenot_agree' v); [exact Hag|]. eapply GCL.split_lit_vars; [exact Hsp|]. unfold reg. apply nth_sr_vars_lt; [exact Fsr | lia]. }
  pose proof Hblk as (K1 & K2 & K3). pose proof (u64_range p) as Hpr. pose proof GlzConst.ceil_hi as CH. unfold GlzConst.PTRHI in CH. pose proof GlzConst.ceil_lo as CL.
  exists E'. split; [|split; [|reflexivity]].
  + split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
  + constructor; cbn [a_ss s_regs s_log s_know kn a_vis a_totsz a_eager a_ylo a_brk].
    * (* [comment removed for export] *)
      unfold ret_regs.
      pose proof (regs_after_call E1 (s_regs (a_ss cs)) R R' (S v) (Some (EVar v))) as RA. cbn iota in RA. apply RA.
      -- eapply regs_ok_agree'; [exact Hag1 | exact Fsr | exact HR].
      -- eapply sr_vars_lt_mono; [exact Fsr | lia].
      -- apply kept_ok_of_callee_saved. exact Hkept.
      -- split; [cbn; apply Nat.leb_refl|]. cbn [edenot]. unfold E1. rewrite ext1_at. exact Ha0.
    * reflexivity.
    * (* [comment removed for export] *)
      pose proof Hflat as HflatV. rewrite forallb_app in HflatV. apply andb_prop in HflatV as [HflatV HflatG].
      assert (Hsum : edenot E' (eadd (EVar v) (reg cs 10)) = Z_to_bv 64 (bv_unsigned p + n)).
      { unfold eadd. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. cbn [edenot] in Hpv. rewrite Hpv, Hne. unfold v_add, n, uE. reflexivity. }
      assert (Hes : estart E' (SA (EVar v) 0) = bv_unsigned p) by (rewrite estart_SA, Hpv; lia).
      assert (Hel : elenZ E' (reg cs 10) = n) by (unfold elenZ, n, uE; rewrite Hne; reflexivity).
      pose proof (call_ok_top_ok _ _ _ Hco) as Htok.
      destruct (split_lit (a_brk cs)) as [tb tk] eqn:Htop.
      destruct (floor_win (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs)) as [[fwb fwo] fwl] eqn:Hfw.
      destruct (floor_win_sound E M (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) tb tk fwb fwo fwl HK Htok Htop (co_floor HC) Hfw) as [FWlo ->].
      assert (Hfwb : edenot E' fwb = edenot E fwb).
      { symmetry. eapply (edenot_agree' v); [exact Hag|]. exact (floor_win_vars v (a_maps cs) (a_brk cs) (a_ylo cs) fwb fwo _ Fmaps Fbrk Hfw). }
      unfold block_facts, block_rng, block_sep. rewrite Hfw.
      unfold know_ok. rewrite <- !app_assoc. repeat (apply Forall_app; split).
      -- (* [comment removed for export] *)
        repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [kentry_ok].
        ++ rewrite Hpv. unfold GlzConst.PTRLO, GlzConst.PTRHI in *. unfold n, uE in *. lia.
        ++ rewrite Hsum. unfold GlzConst.PTRLO, GlzConst.PTRHI in *. rewrite u64_lit by (unfold n, uE in *; lia). unfold n, uE in *; lia.
        ++ rewrite Hpv. lia.
      -- (* [comment removed for export] *)
        repeat apply Forall_cons; [| | apply Forall_nil]; cbn [kentry_ok].
        ++ rewrite Hes, Hel. split; [unfold flat; rewrite Hes; lia|].
           intros d m Hd Hdm. apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
           intros x Hx. rewrite u64_lit in Hx by lia.
           destruct (Hdef x ltac:(lia)) as [_ Hs1].
           eapply (store_ok_all SEGS M' 1 x); [change (Z.of_nat 1) with 1; pose proof (u64_range x); lia | exact Hs1 | change (Z.of_nat 1) with 1; lia].
        ++ rewrite Hes, Hel. split; [unfold flat; rewrite Hes; lia|].
           intros i Hi. apply (Hdef (Z_to_bv 64 (bv_unsigned p + i))). rewrite u64_lit by lia. lia.
      -- (* [comment removed for export] *)
        repeat apply Forall_cons; [| | apply Forall_nil]; cbn [kentry_ok]; rewrite Hes, Hel, estart_SA.
        ++ rewrite Hfwb. left. unfold uE in *. lia.
        ++ cbn [edenot]. rewrite (u64_lit 0) by lia. rewrite (elenZ_lit E') by lia. lia.
      -- (* [comment removed for export] *)
        eapply (disj_facts_ok E' M' M (kn cs)); [exact HKE' | | exact Hpv |].
        ++ rewrite forallb_app. apply andb_true_intro. split; [exact HflatV|].
           unfold perm_nonempty. apply forallb_forall. intros x Hx. apply filter_In in Hx as [Hx _]. exact (proj1 (forallb_forall _ _) HflatG x Hx).
        ++ rewrite blocks_den_app, HLc. intros b m Hin. unfold uE. rewrite Hne. fold (uE E (reg cs 10)). fold n.
           apply in_app_iff in Hin as [Hin|Hin]; [exact (Hdisj b m Hin)|].
           unfold blocks_den in Hin. apply in_map_iff in Hin as [[gb gl] [Hgeq Hing]]. cbn [fst snd] in Hgeq. injection Hgeq as <- <-.
           unfold perm_nonempty in Hing. apply filter_In in Hing as [Hing Hgl]. cbn [snd] in Hgl.
           destruct (xlo (kn cs) gl) as [l|] eqn:Hxl; [|discriminate]. apply Z.leb_le in Hgl.
           pose proof (xlo_sound SEGS E M (kn cs) gl l HK Hxl) as Hl.
           assert (Hgb : uE E' gb = uE E gb) by (unfold uE; f_equal; symmetry; eapply edenot_agree'; [exact Hag | exact (proj1 (andb_prop _ _ (proj1 (forallb_forall _ _) (pairs_vars_lt_app_r _ _ _ Fallow) _ Hing)))]).
           assert (Hgl' : uE E' gl = uE E gl) by (unfold uE; f_equal; symmetry; eapply edenot_agree'; [exact Hag | exact (proj2 (andb_prop _ _ (proj1 (forallb_forall _ _) (pairs_vars_lt_app_r _ _ _ Fallow) _ Hing)))]).
           rewrite Hgb, Hgl'.
           destruct (Hpermd (uE E gb) (uE E gb + uE E gl)) as [X|X]; [| unfold uE in *; lia | lia | lia].
           rewrite <- (co_perm HC). unfold wins_den. apply in_map_iff. exists (gb, gl). split; [reflexivity | exact Hing].
      -- (* [comment removed for export] *)
        eapply (kdisj_of_facts_ok E' M' M (kn cs)); [exact HKE' | exact Hpv | | constructor].
        intros K b off len HKin HKR Hl.
        (* [comment removed for export] *)
        assert (HKok : kentry_ok SEGS E M K).
        { rewrite keep_owned_eq in HKin. unfold keep_owned_ref in HKin. rewrite Hsp in HKin. apply in_app_iff in HKin as [HKin'|HKin']; apply filter_In in HKin' as [HKin' _].
          - exact (proj1 (Forall_forall _ _) HK K HKin').
          - refine (proj1 (Forall_forall _ _) _ K HKin'). eapply know_ok_cutout; [exact HK|]. intros; reflexivity. }
        pose proof (kentry_range_foot E M K b off len HKok HKR) as HF.
        assert (HKv : kentry_vars_lt v K = true).
        { pose proof (keep_owned_vars G (kn cs) (a_vis cs ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) v) as KV.
          rewrite kn_vars_lt_forallb in KV. exact (proj1 (forallb_forall _ _) KV K HKin). }
        assert (Hbe : uE E' b = uE E b).
        { unfold uE. f_equal. symmetry. eapply edenot_agree'; [exact Hag|].
          destruct K as [[? ?] ? ?|[? ?] ?|[? ?] ? ?| | | |[? ?] ?| |[? ?] ? ?|[? ?] ?]; cbn [kentry_range] in HKR; try discriminate; injection HKR as <- <- <-;
            cbn [kentry_vars_lt saddr_vars_lt a_base] in HKv; repeat (apply andb_prop in HKv as [HKv ?]); first [exact HKv | assumption]. }
        assert (Hle : uE E' len = uE E len).
        { unfold uE. f_equal. symmetry. eapply edenot_agree'; [exact Hag|].
          destruct K as [[? ?] ? ?|[? ?] ?|[? ?] ? ?| | | |[? ?] ?| |[? ?] ? ?|[? ?] ?]; cbn [kentry_range] in HKR; try discriminate; injection HKR as <- <- <-;
            cbn [kentry_vars_lt saddr_vars_lt a_base expr_vars_lt] in HKv; repeat (apply andb_prop in HKv as [HKv ?]); first [reflexivity | exact HKv | assumption]. }
        rewrite Hbe, Hle in *. assert (Hn' : uE E' (reg cs 10) = n) by (unfold uE, n; rewrite Hne; reflexivity). rewrite Hn'.
        destruct (Z_lt_ge_dec (bv_unsigned p + n) (uE E b + off + 1)) as [|Hge1]; [left; lia|].
        destruct (Z_lt_ge_dec (uE E b + off + uE E len) (bv_unsigned p + 1)) as [|Hge2]; [right; lia|].
        exfalso. set (z := Z.max (bv_unsigned p) (uE E b + off)).
        assert (Hz1 : bv_unsigned p <= z < bv_unsigned p + n) by (unfold z; unfold n, uE in *; lia).
        assert (Hz2 : uE E b + off <= z < uE E b + off + uE E len) by (unfold z; unfold uE in *; lia).
        assert (Hsp1 : CEIL_run <= uE E (reg cs 2)) by (unfold MSTK in *; lia).
        refine (block_not_kept_loc Lc (bv_unsigned p) n (uE E (reg cs 2)) z Hblk Gimg Hdisj Hpermd Hsp1 Hsptop Hz1 _).
        eapply (keep_owned_loc SEGS PERMc SPTOPc G E M (kn cs) (a_vis cs) (a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk v K z
                  HK Hflat (co_perm HC) (co_top HC) Hsp (co_floor HC) HKin).
        unfold in_kfoot. rewrite HF, estart_SA. unfold uE in *. lia.
      -- (* [comment removed for export] *)
        apply (know_ok_agree' SEGS v E E'); [exact Hag | apply keep_owned_vars |].
        unfold know_ok. apply Forall_forall. intros K HKin.
        eapply (keep_owned_sound SEGS SWIN PERMc SPTOPc G E M M' (kn cs) (a_vis cs) (a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk v K
                  HK Hflat (co_perm HC) (co_top HC) Hsp); [| exact (co_floor HC) | | | exact HKin].
        ++ pose proof (u64_range (edenot E (reg cs 2))). unfold uE in Hspv. lia.
        ++ intros a Ha. apply Hfr. exact Ha.
        ++ exact Hscr.
    * exact Hh'.
    * exact Hlz'.
    * rewrite Hfs'. exact (co_fs HC).
    * rewrite Hfds'. exact (co_fds HC).
    * (* [comment removed for export] *)
      cbn [blocks_den map fst snd GPS.bcost]. fold (blocks_den E' (a_vis cs)). rewrite HLc.
      unfold uE at 1 2 3. rewrite Hpv, Hne. fold (uE E (reg cs 10)). fold n.
      rewrite (GPS.bcost_agree v E E' (a_vis cs) Hag (GPS.pairs_vars_lt_app_l _ _ _ Fallow)).
      replace (n + GPS.MBLK + GPS.bcost E (a_vis cs)) with (GPS.bcost E (a_vis cs) + mcost n) by (unfold mcost, GlzIface.MBLK, GPS.MBLK; lia).
      replace (GPS.bcount ((EVar v, reg cs 10) :: a_vis cs)) with (GPS.bcount (a_vis cs) + MCNT) by (unfold GPS.bcount, MCNT; cbn [length]; lia).
      exact HAINV'.
    * eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | exact (co_uinv HC)].
    * exact HFX'.
    * cbn [a_ghost]. rewrite (wins_den_agree v E E' (a_ghost cs) Hag (pairs_vars_lt_app_r _ _ _ Fallow)). exact (co_perm HC).
    * rewrite (sptop_den_agree v E E' (a_brk cs) Hag Fbrk). exact (co_top HC).
    * exact Hmat'.
    * eapply GPS.floor_sem_agree; [exact Hag | exact Fbrk | exact Fmaps | exact (co_floor HC)].
Qed.


(* [comment removed for export] *)
Theorem node_alloc_sound_gen : forall entry (XTRA : (word -> option byte) -> Prop) (chk : acs -> bool),
  g_img_lo G <= g_ro_lo G -> 0 <= g_img_lo G <= g_img_hi G /\ g_img_hi G < 2 ^ 64 ->
  (forall cs E fx R M model, cs_ok E cs fx R M model -> chk cs = true -> XTRA M) ->
  alloc1_nspec SEGS SWIN PERMc SPTOPc AINV FXOK RZ G bcap ccap XTRA entry ->
  GPS.node1_stmtN SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ chk (node_alloc nx0 G bcap ccap entry).
Proof.
  intros entry XTRA chk Gimg Gimg2 HX MS cs cs' E fx R M model T HT0 HC Hchk Hn Hk.
  pose proof Hn as Hn0. unfold node_alloc in Hn0.
  destruct (call_ok nx0 G entry cs) as [ret|] eqn:Hco; [|discriminate]. clear Hn0.
  destruct (node_alloc_pre_sound entry cs cs' ret E fx R M model HC Hco Hn) as [Hpc PRE].
  unfold cfgF. rewrite Hpc.
  apply (MS fx R M model _ _ _ ret _ _ T PRE HT0 (HX cs E fx R M model HC Hchk)).
  intros fx' R' M' mdl' p POST.
  pose proof POST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfs' & _).
  destruct (node_alloc_ok_sound entry cs cs' ret E fx R M model fx' R' M' mdl' p Gimg Gimg2 HC Hco Hn POST) as (E' & Hag & HC' & Hpc').
  rewrite <- Hpc'. exact (Hk E' fx' R' M' mdl' Hag HC' Hfs').
Qed.


Lemma remove_block_split : forall p live m live',
  remove_block p live = Some (m, live') ->
  exists L1 L2, live = L1 ++ (p, m) :: L2 /\ live' = L1 ++ L2.
Proof.
  intros p live. induction live as [|[b n] r IH]; intros m live' H; cbn [remove_block] in H; [discriminate|].
  destruct (expr_eqb b p) eqn:Heq.
  - injection H as <- <-. apply expr_eqb_eq in Heq. subst b. exists [], r. split; reflexivity.
  - destruct (remove_block p r) as [[m' r']|] eqn:Hr; [|discriminate]. injection H as <- <-.
    destruct (IH m' r' eq_refl) as (L1 & L2 & -> & ->). exists ((b, n) :: L1), L2. split; reflexivity.
Qed.


Theorem node_release_sound : forall entry,
  free_nspec SEGS SWIN PERMc SPTOPc AINV FXOK RZ G entry -> node1_stmt always (node_release nx0 G entry).
Proof.
  intros entry FS cs cs' E fx R M model T HC _ Hn Hk.
  unfold node_release in Hn.
  destruct (call_ok nx0 G entry cs) as [ret|] eqn:Hco; [|discriminate].
  pose proof (call_ok_sound entry cs ret E fx R M model HC Hco) as CO.
  cbv zeta in Hn. cbv zeta in CO.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp.
  destruct CO as (Hpc & Hfresh & Hlen & R1 & Rr & Re & R4 & R2 & Hspv & Hal & Hsplo & Hsptop & Hstk & Hflat).
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (reg_sound E cs R 10 HR ltac:(lia)) as R10. change (Z.of_nat 10) with 10 in R10.
  set (v := nxt cs) in *.
  (* [comment removed for export] *)
  assert (SHAPE : exists live',
    cs' = ACS (mk_ss ret (ret_regs (s_regs (a_ss cs)) v None) (keep_owned G (kn cs) (live' ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) v) (v + NCS)%nat)
              (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) live' (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
    /\ (getr R (Z_to_bv 5 10) = Z_to_bv 64 0 /\ live' = a_vis cs
        \/ exists m L1 L2, a_vis cs = L1 ++ (reg cs 10, m) :: L2 /\ live' = L1 ++ L2)).
  { destruct (reg cs 10) as [z|x|sh e1 e2|op e1 e2|op e1 e2|w e1|c e1 e2|e1] eqn:Hp10.
    1: destruct (Z.eq_dec z 0) as [->|Hz].
    1: { apply some_inj in Hn. exists (a_vis cs). split; [rewrite <- Hn; destruct cs; reflexivity|].
         left. split; [rewrite R10; reflexivity | reflexivity]. }
    1: destruct z; [lia| |].
    all: destruct (remove_block _ (a_vis cs)) as [[m live']|] eqn:Hrb; try discriminate;
         apply some_inj in Hn; exists live'; split; [rewrite <- Hn; reflexivity|]; right;
         destruct (remove_block_split _ _ _ _ Hrb) as (L1 & L2 & HL & HL'); exists m, L1, L2; split; assumption. }
  clear Hn. destruct SHAPE as (live' & -> & CASES).
  set (Lc := blocks_den E (a_vis cs)). set (Lc' := blocks_den E live').
  assert (Hsub : forall x, In x live' -> In x (a_vis cs)).
  { destruct CASES as [[_ ->]|(m & L1 & L2 & HL & ->)]; intros x Hx; [exact Hx|].
    rewrite HL. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx]. }
  assert (Hflat' : forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) (live' ++ a_ghost cs) = true).
  { apply forallb_forall. intros x Hx. apply (proj1 (forallb_forall _ _) Hflat x).
    apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact (Hsub x Hx) | right; exact Hx]. }
  assert (Hvars' : pairs_vars_lt v live' = true).
  { unfold pairs_vars_lt. apply forallb_forall. intros x Hx.
    exact (proj1 (forallb_forall _ _) (pairs_vars_lt_app_l _ _ _ Fallow) x (Hsub x Hx)). }
  unfold cfgF. rewrite Hpc.
  apply (FS fx R M model Lc Lc' (GPS.bcost E (a_vis cs)) (GPS.bcount (a_vis cs)) (GPS.bcost E live') (GPS.bcount live')
           ret (uE E (reg cs 2)) (getr R (Z_to_bv 5 10)) T
           (co_halt HC) (co_lazy HC) (co_mat HC) (co_fx HC) (co_ainv HC) R1 Rr Re eq_refl).
  - destruct CASES as [[H0 ->]|(m & L1 & L2 & HL & ->)].
    + left. split; [exact H0 | repeat split; reflexivity].
    + right. exists (uE E m), (blocks_den E L1), (blocks_den E L2).
      unfold Lc, Lc'. rewrite HL, !blocks_den_app, !bcost_app, !bcount_app. cbn [blocks_den map fst snd app GPS.bcost GPS.bcount length]. rewrite R10.
      pose proof (bcost_nonneg E L1). pose proof (bcost_nonneg E L2). pose proof (u64_range (edenot E m)). unfold mcost, MCNT, uE, GlzIface.MBLK, GPS.MBLK in *.
      split; [reflexivity|]. split; [reflexivity|]. unfold GPS.bcount in *. cbn [length] in *. split; lia.
  - unfold uE. rewrite <- R2. reflexivity.
  - exact Hal.
  - exact Hsplo.
  - exact Hsptop.
  - exact R4.
  - exact Hstk.
  - (* [comment removed for export] *)
    intros fx' R' M' mdl' HFX' Hkept Hfr Hscr HAINV' Hh' Hlz' Hmat' Hfs' Hfds'.
    set (E' := ext_call E v R').
    assert (Hag : env_agree v E E') by apply ext_call_agree.
    assert (HLc : blocks_den E' live' = Lc') by (unfold Lc'; eapply blocks_den_agree; [exact Hag | exact Hvars']).
    apply (Hk E' fx' R' M' mdl').
    + split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
    + constructor; cbn [a_ss s_regs s_log s_know kn a_vis a_totsz a_eager].
      * unfold ret_regs.
        pose proof (regs_after_call E (s_regs (a_ss cs)) R R' v None) as RA. cbn iota in RA. apply RA.
        -- exact HR.
        -- exact Fsr.
        -- apply kept_ok_of_callee_saved. exact Hkept.
        -- exact I.
      * reflexivity.
      * apply (know_ok_agree' SEGS v E E'); [exact Hag | apply keep_owned_vars |].
        unfold know_ok. apply Forall_forall. intros K HKin.
        eapply (keep_owned_sound SEGS SWIN PERMc SPTOPc G E M M' (kn cs) live' (a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk v K
                  HK Hflat' (co_perm HC) (co_top HC) Hsp); [| | | | exact HKin].
        -- pose proof (u64_range (edenot E (reg cs 2))). unfold uE in Hspv. lia.
        -- exact (co_floor HC).
        -- intros a Ha. apply Hfr. exact Ha.
        -- exact Hscr.
      * exact Hh'.
      * exact Hlz'.
      * rewrite Hfs'. exact (co_fs HC).
      * rewrite Hfds'. exact (co_fds HC).
      * rewrite HLc. rewrite (GPS.bcost_agree v E E' live' Hag Hvars'). exact HAINV'.
      * eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | exact (co_uinv HC)].
      * exact HFX'.
      * cbn [a_ghost]. rewrite (wins_den_agree v E E' (a_ghost cs) Hag (pairs_vars_lt_app_r _ _ _ Fallow)). exact (co_perm HC).
      * cbn [a_brk]. rewrite (sptop_den_agree v E E' (a_brk cs) Hag Fbrk). exact (co_top HC).
      * exact Hmat'.
      * cbn [a_brk a_ylo a_maps]. eapply GPS.floor_sem_agree; [exact Hag | exact Fbrk | exact Fmaps | exact (co_floor HC)].
    + exact Hfs'.
Qed.

(* [comment removed for export] *)
Theorem node_malloc1_sound_gen : forall (FRESH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop) args,
  g_img_lo G <= g_ro_lo G -> 0 <= g_img_lo G <= g_img_hi G /\ g_img_hi G < 2 ^ 64 ->
  (forall cs E fx R M model, cs_ok E cs fx R M model -> fresh_chk args cs = true ->
      FRESH (blocks_den E (a_vis cs)) (GPS.bcost E (a_vis cs)) (GPS.bcount (a_vis cs)) M model (uE E (reg cs 10))) ->
  malloc_nspec1 SEGS SWIN PERMc SPTOPc AINV FXOK RZ G bcap ccap FRESH (g_malloc_thunk G) ->
  malloc_nspec1 SEGS SWIN PERMc SPTOPc AINV FXOK RZ G bcap ccap FRESH (g_malloc G) ->
  GPS.node1_stmtN SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ always (node_malloc1 nx0 G bcap ccap args).
Proof.
  intros FRESH args Gimg Gimg2 HF MT MI cs cs' E fx R M model T HT0 HC _ Hn Hk.
  unfold node_malloc1, node_malloc2 in Hn.
  destruct (fresh_chk args cs) eqn:Hfc; [|discriminate].
  destruct (call_ok nx0 G (malloc_entry G cs) cs) as [ret|] eqn:Hco; [|discriminate].
  destruct (node_alloc nx0 G bcap ccap (malloc_entry G cs) cs) as [ok|] eqn:Hna; [|discriminate].
  injection Hn as <-.
  destruct (node_alloc_pre_sound (malloc_entry G cs) cs ok ret E fx R M model HC Hco Hna) as [Hpc PRE].
  assert (MS : malloc_nspec1 SEGS SWIN PERMc SPTOPc AINV FXOK RZ G bcap ccap FRESH (malloc_entry G cs)).
  { unfold malloc_entry in *. destruct (Z.eqb (pc cs) (g_malloc_thunk G)); [exact MT | exact MI]. }
  unfold cfgF. rewrite Hpc.
  apply (MS fx R M model _ _ _ ret _ _ T PRE (HF cs E fx R M model HC Hfc) HT0).
  intros fx' R' M' mdl' p POST.
  pose proof POST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfs' & _).
  destruct (node_alloc_ok_sound (malloc_entry G cs) cs ok ret E fx R M model fx' R' M' mdl' p Gimg Gimg2 HC Hco Hna POST) as (E' & Hag & HC' & Hpc').
  rewrite <- Hpc'. exact (Hk E' fx' R' M' mdl' Hag HC' Hfs').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem node_opnew_sound :
  g_img_lo G <= g_ro_lo G -> 0 <= g_img_lo G <= g_img_hi G /\ g_img_hi G < 2 ^ 64 ->
  opnew_nspec SEGS SWIN PERMc SPTOPc AINV FXOK RZ G bcap ccap (g_opnew G) ->
  OBL_opnew SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ G bcap ccap.
Proof.
  intros G1 G2 MO cs cs' E fx R M model T HT0 HC _ Hn Hk. unfold node_opnew in Hn.
  refine (node_alloc_sound_gen (g_opnew G) (fun _ => True) (fun _ => true) G1 G2 _ MO cs cs' E fx R M model T HT0 HC eq_refl Hn Hk).
  intros; exact I.
Qed.

Theorem node_free_sound :
  free_nspec SEGS SWIN PERMc SPTOPc AINV FXOK RZ G (g_free_thunk G) -> free_nspec SEGS SWIN PERMc SPTOPc AINV FXOK RZ G (g_free G) ->
  OBL_free SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ G.
Proof.
  intros FT FI cs cs' E fx R M model T HC Hpre Hn Hk. unfold node_free in Hn.
  destruct (Z.eqb (pc cs) (g_free_thunk G)).
  - exact (node_release_sound _ FT cs cs' E fx R M model T HC Hpre Hn Hk).
  - exact (node_release_sound _ FI cs cs' E fx R M model T HC Hpre Hn Hk).
Qed.

Theorem node_opdel_sound :
  free_nspec SEGS SWIN PERMc SPTOPc AINV FXOK RZ G (g_opdel G) -> OBL_opdel SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ G.
Proof. intros F. exact (node_release_sound _ F). Qed.

Theorem node_opdel_sized_sound :
  free_nspec SEGS SWIN PERMc SPTOPc AINV FXOK RZ G (g_opdel_sized G) -> OBL_opdel_sized SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ G.
Proof. intros F. exact (node_release_sound _ F). Qed.

(* [comment removed for export] *)

Theorem node_blkfact_sound :
  0 <= g_img_lo G <= g_img_hi G /\ g_img_hi G < 2 ^ 64 -> g_img_lo G <= g_ro_lo G ->
  (forall Lc B C M mdl b m, AINV Lc B C M mdl -> In (b, m) Lc -> blk_ok G b m) ->
  (forall Lc B C M mdl L1 L2 b m b' m', AINV Lc B C M mdl -> Lc = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b) ->
  (forall Lc B C M mdl b m lo hi, AINV Lc B C M mdl -> In (b, m) Lc -> 1 <= m -> In (lo, hi) PERMc -> lo < hi -> b + m <= lo \/ hi <= b) ->
  (forall Lc B C M mdl, AINV Lc B C M mdl -> CEIL_run <= SPTOPc) ->
  forall args, node1_stmt always (node_blkfact G args).
Proof.
  intros Gimg2 Gimg AINV_zone AINV_disj AINV_perm AINV_top args. apply (GlzIface.GlzNodesArith.add_facts_sound SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ).
  intros cs cs' E fx R M model HC Hn. unfold node_blkfact in Hn.
  destruct args as [|b [|]]; try discriminate.
  destruct (remove_block b (a_vis cs)) as [[n live']|] eqn:Hrb; [|discriminate]. cbv zeta in Hn.
  destruct (xlo (kn cs) n) as [nlo|] eqn:Hnlo; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hlf]. apply andb_prop in Hc as [Hc Hbf]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _].
  apply andb_prop in Hc as [Hn1 Htok]. apply Z.leb_le in Hn1.
  pose proof (co_know HC) as HK. unfold live_flat in Hlf.
  destruct (remove_block_split _ _ _ _ Hrb) as (L1 & L2 & HL & HL').
  destruct (split_lit (a_brk cs)) as [tb tk] eqn:Htop.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp.
  destruct (floor_win (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs)) as [[fwb fwo] fwl] eqn:Hfw.
  destruct (floor_win_sound E M (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) tb tk fwb fwo fwl HK Htok Htop (co_floor HC) Hfw) as [FWlo ->].
  destruct (top_ok_sound E M (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) tb tk HK Htok Htop) as (TOPEQ & _ & TOPR & _).
  pose proof (xlo_sound SEGS E M (kn cs) n nlo HK Hnlo) as Nlo.
  assert (Hinv : In (b, n) (a_vis cs)) by (rewrite HL; apply in_app_iff; right; left; reflexivity).
  assert (Hin : In (uE E b, uE E n) (blocks_den E (a_vis cs))).
  { unfold blocks_den. apply in_map_iff. exists (b, n). split; [reflexivity | exact Hinv]. }
  pose proof (AINV_zone _ _ _ _ _ _ _ (co_ainv HC) Hin) as Hblk. pose proof Hblk as (K1 & K2 & K3).
  pose proof GlzConst.ceil_hi as CH. unfold GlzConst.PTRHI in CH. pose proof GlzConst.ceil_lo as CL.
  pose proof (u64_range (edenot E b)) as Rb. pose proof (u64_range (edenot E n)) as Rn.
  assert (Hsum : bv_unsigned (edenot E (eadd b n)) = uE E b + uE E n).
  { unfold eadd. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add. unfold uE in *. apply u64_lit. lia. }
  (* [comment removed for export] *)
  assert (Hsub : forall x, In x live' -> In x (a_vis cs)).
  { intros x Hx. rewrite HL, HL' in *. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx]. }
  assert (Hdisj : forall b' m', In (b', m') (blocks_den E live') -> uE E b + uE E n <= b' \/ b' + m' <= uE E b).
  { intros b' m' Hin'. eapply (AINV_disj _ _ _ _ _ (blocks_den E L1) (blocks_den E L2)); [exact (co_ainv HC) | | ].
    - rewrite HL. unfold blocks_den. rewrite map_app. cbn [map fst snd]. reflexivity.
    - rewrite HL', blocks_den_app in Hin'. exact Hin'. }
  assert (Hperm : forall lo hi, In (lo, hi) PERMc -> lo < hi -> uE E b + uE E n <= lo \/ hi <= uE E b).
  { intros lo hi Hpin Hlh. eapply AINV_perm; [exact (co_ainv HC) | exact Hin | unfold uE in *; lia | exact Hpin | exact Hlh]. }
  assert (Hflat' : forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) (live' ++ a_ghost cs) = true).
  { apply forallb_forall. intros x Hx. apply (proj1 (forallb_forall _ _) Hlf x).
    apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact (Hsub x Hx) | right; exact Hx]. }
  (* [comment removed for export] *)
  eexists. split; [reflexivity|].
  unfold know_ok. apply Forall_app. split; [|apply Forall_app; split].
  - (* [comment removed for export] *)
    unfold block_place. rewrite Hfw.
    repeat apply Forall_cons; [| | | | apply Forall_nil]; cbn [kentry_ok].
    + unfold GlzConst.PTRLO, GlzConst.PTRHI in *. unfold uE in *. lia.
    + rewrite Hsum. unfold GlzConst.PTRLO, GlzConst.PTRHI in *. unfold uE in *. lia.
    + rewrite !estart_SA. cbn [a_base a_off]. unfold elenZ. left. unfold uE in *. lia.
    + rewrite !estart_SA. cbn [edenot a_base a_off]. rewrite (u64_lit 0) by lia. rewrite (elenZ_lit E) by lia. unfold elenZ. unfold uE in *. lia.
  - (* [comment removed for export] *)
    eapply (disj_facts_ok E M M (kn cs) b n _ (edenot E b)); [exact HK | | reflexivity |].
    + apply forallb_forall. intros x Hx. apply in_app_iff in Hx as [Hx|Hx].
      * exact (proj1 (forallb_forall _ _) Hlf x ltac:(apply in_app_iff; left; exact (Hsub x Hx))).
      * unfold perm_nonempty in Hx. apply filter_In in Hx as [Hx _]. exact (proj1 (forallb_forall _ _) Hlf x ltac:(apply in_app_iff; right; exact Hx)).
    + rewrite blocks_den_app. intros b' m' Hin'. apply in_app_iff in Hin' as [Hin'|Hin']; [exact (Hdisj b' m' Hin')|].
      unfold blocks_den in Hin'. apply in_map_iff in Hin' as [[gb gl] [Hgeq Hing]]. cbn [fst snd] in Hgeq. injection Hgeq as <- <-.
      unfold perm_nonempty in Hing. apply filter_In in Hing as [Hing Hgl]. cbn [snd] in Hgl.
      destruct (xlo (kn cs) gl) as [l|] eqn:Hxl; [|discriminate]. apply Z.leb_le in Hgl.
      pose proof (xlo_sound SEGS E M (kn cs) gl l HK Hxl) as Hl.
      destruct (Hperm (uE E gb) (uE E gb + uE E gl)) as [X|X]; [| unfold uE in *; lia | unfold uE in *; lia | unfold uE in *; lia].
      rewrite <- (co_perm HC). unfold wins_den. apply in_map_iff. exists (gb, gl). split; [reflexivity | exact Hing].
  - (* [comment removed for export] *)
    eapply (kdisj_of_facts_ok E M M (kn cs)); [exact HK | reflexivity | | constructor].
    intros K b0 off len HKin HKR Hl.
    assert (HKok : kentry_ok SEGS E M K).
    { rewrite keep_owned_eq in HKin. unfold keep_owned_ref in HKin. rewrite Hsp in HKin. apply in_app_iff in HKin as [HKin'|HKin']; apply filter_In in HKin' as [HKin' _].
      - exact (proj1 (Forall_forall _ _) HK K HKin').
      - refine (proj1 (Forall_forall _ _) _ K HKin'). eapply know_ok_cutout; [exact HK|]. intros; reflexivity. }
    pose proof (kentry_range_foot E M K b0 off len HKok HKR) as HF.
    destruct (Z_lt_ge_dec (uE E b + uE E n) (uE E b0 + off + 1)) as [|Hge1]; [left; unfold uE in *; lia|].
    destruct (Z_lt_ge_dec (uE E b0 + off + uE E len) (uE E b + 1)) as [|Hge2]; [right; unfold uE in *; lia|].
    exfalso. set (z := Z.max (uE E b) (uE E b0 + off)).
    assert (Hz1 : uE E b <= z < uE E b + uE E n) by (unfold z; unfold uE in *; lia).
    assert (Hz2 : uE E b0 + off <= z < uE E b0 + off + uE E len) by (unfold z; unfold uE in *; lia).
    pose proof (keep_owned_loc SEGS PERMc SPTOPc G E M (kn cs) live' (a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk (nxt cs) K z
                  HK Hflat' (co_perm HC) (co_top HC) Hsp (co_floor HC) HKin ltac:(unfold in_kfoot; rewrite HF, estart_SA; unfold uE in *; lia)) as LOC.
    destruct LOC as [Hb|[Hp|[Hst|[Hab|Him]]]].
    + destruct Hb as (b2 & m2 & Hin2 & Hbz2). destruct (Hdisj b2 m2 Hin2); lia.
    + destruct Hp as (lo & hi & Hpin & Hlh). destruct (Hperm lo hi Hpin ltac:(lia)); lia.
    + unfold uE in *. lia.
    + (* [comment removed for export] *) pose proof (AINV_top _ _ _ _ _ (co_ainv HC)). unfold uE in *. lia.
    + unfold uE in *. lia.
Qed.

End Sound.
End GlzNodesAlloc.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzCallLib GlzNodesAlloc GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS. Import GCL.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition resplit_addr (k : list kentry) (a : saddr) : saddr :=
  let '(b', k') := split_lit (a_base a) in
  if Z.eqb k' 0 then a else
  match base_range k b' with
  | Some (lo, hi) => if (Z.leb 0 (lo + k') && Z.ltb (hi + k') two64)%bool then SA b' (a_off a + k') else a
  | None => a
  end.
Definition kresplit (k : list kentry) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (resplit_addr k a) w v
  | KZero a n => KZero (resplit_addr k a) n
  | KBlob a n b => KBlob (resplit_addr k a) n b
  | KWr a n => KWr (resplit_addr k a) n
  | KDisj a1 n1 a2 n2 => KDisj (resplit_addr k a1) n1 (resplit_addr k a2) n2
  | KFill a n c => KFill (resplit_addr k a) n c
  | KUnk a n => KUnk (resplit_addr k a) n
  | _ => K
  end.

Section Sem.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)

Lemma resplit_addr_estart : forall E M k a,
  know_ok SEGS E M k -> estart E (resplit_addr k a) = estart E a /\ adenot E (resplit_addr k a) = adenot E a.
Proof.
  intros E M k [b o] HK.
  assert (GEN : forall a', estart E a' = estart E (SA b o) -> estart E a' = estart E (SA b o) /\ adenot E a' = adenot E (SA b o)).
  { intros a' H. split; [exact H|]. unfold adenot, v_addi. unfold estart in H. apply bv_eq.
    rewrite !Z_to_bv_unsigned. cbn [a_base a_off] in *. unfold bv_wrap. f_equal. exact H. }
  apply GEN. unfold resplit_addr. cbn [a_base a_off].
  destruct (split_lit b) as [b' k'] eqn:Hsp. destruct (Z.eqb k' 0); [reflexivity|].
  destruct (base_range k b') as [[lo hi]|] eqn:Hbr; [|reflexivity].
  destruct (Z.leb 0 (lo + k') && Z.ltb (hi + k') two64)%bool eqn:Hc; [|reflexivity].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
  pose proof (base_range_sound SEGS E M k b' lo hi HK Hbr) as [B1 B2].
  unfold estart. cbn [a_base a_off]. rewrite (split_lit_denot E b b' k' Hsp). rewrite u64_lit by lia. lia.
Qed.

Lemma kentry_ok_kresplit : forall E M M0 k K,
  know_ok SEGS E M0 k -> kentry_ok SEGS E M K -> kentry_ok SEGS E M (kresplit k K).
Proof.
  intros E M M0 k K HK H.
  destruct K as [a w v|a n|a n kb|lo hi|x m|x lo hi|a n|a1 n1 a2 n2|a n c|a n]; cbn [kresplit kentry_ok] in *; try exact H;
    unfold flat in *;
    repeat match goal with |- context [estart E (resplit_addr k ?a0)] => rewrite (proj1 (resplit_addr_estart E M0 k a0 HK)) end;
    repeat match goal with |- context [adenot E (resplit_addr k ?a0)] => rewrite (proj2 (resplit_addr_estart E M0 k a0 HK)) end;
    exact H.
Qed.

End Sem.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Entails.
(* [comment removed for export] *)
#[local] Notation "a || b" := (if a then true else b) (at level 50, left associativity, only parsing) : bool_scope.
Variable segs : list Segment.
Variable A : atable.

(* [comment removed for export] *)
Definition kentails (k : list kentry) (K : kentry) : bool :=
  kn_incl1_h A k K
  || match K with
     | KRange e lo hi => APC.kpure_entails k K   (* [comment removed for export] *)
     | KAlign e m => Z.ltb 0 m && Z.eqb (2 ^ ealign k e mod m) 0
     | KWr (SA b o) n => kwritable_x k k b o n && bflat_x k b o n
     | KUnk (SA b o) n => kn_readable_x k b o n && bflat_x k b o n
     | KZero (SA b o) n => kzero_x k k b o n && bflat_x k b o n
     | KDisj (SA b1 o1) n1 (SA b2 o2) n2 => ranges_apart_x k b1 o1 n1 b2 o2 n2
     | KWord (SA b o) w v =>
         Nat.leb 1 w && Nat.leb w 8 && flat_x k b o (ELit (Z.of_nat w))
         && match know_lookup segs k b o w false [] [] with
            | LHit v' [] _ => expr_eqb v v'
            | _ => false
            end
     | _ => false
     end%bool.

Definition kentails_all_ref (k : list kentry) (tk : list kentry) : bool := forallb (kentails k) tk.
End Entails.

(* [comment removed for export] *)
Section EntailsB.
#[local] Notation "a || b" := (if a then true else b) (at level 50, left associativity, only parsing) : bool_scope.
#[local] Notation "a && b" := (if a then b else false) (at level 40, left associativity, only parsing) : bool_scope.
Variable segs : list Segment.
Variable A : atable.
Definition bflat_x_b (bc : AX2B.bctx) (b : expr) (off : Z) (n : expr) : bool :=
  match AX2B.base_rangeB bc b, AX2B.xhiB bc n with
  | Some (lo, hi), Some nh => Z.leb 0 (lo + off) && Z.ltb (hi + off) two64 && Z.leb (hi + off + nh) two64
  | _, _ => false
  end%bool.
Lemma bflat_x_b_fe : forall k, bflat_x_b (AX2B.mkbc k) = bflat_x k.
Proof.
  intros k. do 3 (apply functional_extensionality; intro). unfold bflat_x_b, bflat_x. rewrite AX2B.base_rangeB_eqf, AX2B.xhiB_eqf. reflexivity.
Qed.
Definition kn_readable_x_b (bc : AX2B.bctx) (k : list kentry) (rb : expr) (rk : Z) (ne : expr) : bool :=
  AX2B.existsb_lz (fun K => match K with
                    | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
                        AX2B.xinsideB bc rb rk ne kb kk len
                    | _ => false
                    end) k.
Lemma kn_readable_x_b_fe : forall k, kn_readable_x_b (AX2B.mkbc k) k = kn_readable_x k.
Proof.
  intros k. do 3 (apply functional_extensionality; intro). unfold kn_readable_x_b, kn_readable_x. rewrite AX2B.existsb_lz_fe, AX2B.xinsideB_eqf.
  reflexivity.
Qed.
Definition kentailsB (bc : AX2B.bctx) (k : list kentry) (K : kentry) : bool :=
  kn_incl1_hB A bc k K
  || match K with
     | KRange e lo hi => APC.kpure_entailsB bc K
     | KAlign e m => Z.ltb 0 m && Z.eqb (2 ^ AX2B.ealignB bc e mod m) 0
     | KWr (SA b o) n => kwritable_xB bc k b o n && bflat_x_b bc b o n
     | KUnk (SA b o) n => kn_readable_x_b bc k b o n && bflat_x_b bc b o n
     | KZero (SA b o) n => kzero_xB bc k b o n && bflat_x_b bc b o n
     | KDisj (SA b1 o1) n1 (SA b2 o2) n2 => AX2B.ranges_apart_xB bc b1 o1 n1 b2 o2 n2
     | KWord (SA b o) w v =>
         Nat.leb 1 w && Nat.leb w 8 && flat_xB bc b o (ELit (Z.of_nat w))
         && match AX2B.know_lookupB segs bc b o w false [] [] with
            | LHit v' [] _ => expr_eqb v v'
            | _ => false
            end
     | _ => false
     end%bool.
Lemma kentailsB_eq : forall k K, kentailsB (AX2B.mkbc k) k K = kentails segs A k K.
Proof.
  intros. unfold kentailsB, kentails.
  rewrite ?kn_incl1_hB_eq, ?APC.kpure_entailsB_eq, ?AX2B.ealignB_eqf, ?kwritable_xB_eqf, ?kzero_xB_eqf, ?AX2B.ranges_apart_xB_eqf,
          ?flat_xB_eqf, ?AX2B.know_lookupB_eqf, ?kn_readable_x_b_fe, ?bflat_x_b_fe.
  reflexivity.
Qed.
Definition kentails_all (k : list kentry) (tk : list kentry) : bool :=
  let bc := AX2B.mkbc k in AX2B.forallb_lz (kentailsB bc k) tk.
Lemma kentails_all_eq : forall k tk, kentails_all k tk = kentails_all_ref segs A k tk.
Proof.
  intros. unfold kentails_all, kentails_all_ref. cbv zeta. rewrite AX2B.forallb_lz_fe.
  induction tk as [|K tk IH]; [reflexivity|]. cbn [forallb]. rewrite IH, kentailsB_eq. reflexivity.
Qed.
End EntailsB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record gcallee : Type := GCE {
  ce_nxf : nat;            (* [comment removed for export] *)
  ce_tin : acs;            (* [comment removed for export] *)
  ce_touts : list acs;     (* [comment removed for export] *)
  ce_bcap : Z;             (* [comment removed for export] *)
  ce_ccap : Z              (* [comment removed for export] *)
}.

Section Node.
(* [comment removed for export] *)
#[local] Notation "a || b" := (if a then true else b) (at level 50, left associativity, only parsing) : bool_scope.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : nat.          (* [comment removed for export] *)
Variable bcap ccap : Z.      (* [comment removed for export] *)

Fixpoint ot_set (t : list (option expr)) (i : nat) (c : expr) {struct i} : list (option expr) :=
  match i, t with
  | O, [] => [Some c]
  | O, _ :: r => Some c :: r
  | S i', [] => None :: ot_set [] i' c
  | S i', x :: r => x :: ot_set r i' c
  end.

(* [comment removed for export] *)
Fixpoint bind_regs (nxf : nat) (tr cr : list expr) (acc : list (option expr)) : option (list (option expr)) :=
  match tr, cr with
  | [], [] => Some acc
  | t :: tr', c :: cr' =>
      match t with
      | EVar i =>
          if Nat.ltb i nxf then
            match nth i acc None with
            | None => bind_regs nxf tr' cr' (ot_set acc i c)
            | Some c0 => if expr_eqb c0 c then bind_regs nxf tr' cr' acc else None
            end
          else bind_regs nxf tr' cr' acc
      | _ => bind_regs nxf tr' cr' acc
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Fixpoint fill_args (acc : list (option expr)) (args : list expr) : option (list expr) :=
  match acc with
  | [] => match args with [] => Some [] | _ => None end
  | Some c :: r => match fill_args r args with Some th => Some (c :: th) | None => None end
  | None :: r => match args with
                 | a :: args' => match fill_args r args' with Some th => Some (a :: th) | None => None end
                 | [] => None
                 end
  end.

Definition bind (ce : gcallee) (args : list expr) (cs : acs) : option (list expr) :=
  match bind_regs (ce_nxf ce) (s_regs (a_ss (ce_tin ce))) (s_regs (a_ss cs)) (repeat None (ce_nxf ce)) with
  | Some acc => if Nat.eqb (length acc) (ce_nxf ce) then fill_args acc args else None
  | None => None
  end.

(* [comment removed for export] *)
Definition out_subst (th : list expr) (nxf ntout v : nat) : list expr :=
  th ++ map (fun j => EVar (v + j)%nat) (seq 0 (ntout - nxf)).

(* [comment removed for export] *)
Definition above_sp (k : list kentry) (sp : expr) (b : expr) (off : Z) (n : expr) : bool :=
  let '(spb, spk) := split_lit sp in
  (xinside k b off n spb spk (ELit two47) || xinside0 k b off n spb spk (ELit two47))%bool.   (* [comment removed for export] *)

Definition keep_fact_call (G : gtable) (k : list kentry) (keepblocks : list (expr * expr)) (ws : list (expr * expr))
           (sp : expr) (K : kentry) : bool :=
  match K with
  | KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true
  | KImg lo hi => Z.leb (g_ro_lo G) lo && Z.leb hi (g_img_hi G) && lit_disjoint lo hi (g_priv G)   (* [comment removed for export] *)
  | KWr _ _ | KUnk _ _ => false      (* [comment removed for export] *)
  | _ => match kentry_range K with
         | Some (b, off, n) =>
             (existsb (fun bl => let '(lb, lk) := split_lit (fst bl) in xinside k b off n lb lk (snd bl)) keepblocks
              || above_sp k sp b off n
              || img_lit_x G k b off n)      (* [comment removed for export] *)
             && forallb (fun w => let '(wb, wk) := split_lit (fst w) in ranges_apart_x k b off n wb wk (snd w)) ws
         | None => false
         end
  end%bool.

(* [comment removed for export] *)
Fixpoint kcut (ws : list (expr * expr)) (k : list kentry) : list kentry :=
  match ws with
  | [] => k
  | w :: ws' => let '(wb, wk) := split_lit (fst w) in kn_cutout (kcut ws' k) wb wk (snd w)
  end.

(* [comment removed for export] *)
Definition sticky_call (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KWr (SA b off) n | KUnk (SA b off) n => owned_x k live fl top bud b off n || above_x k top sp b off n   (* [comment removed for export] *)
  | _ => false
  end%bool.

(* [comment removed for export] *)
Definition above_sp_b (bc : AX2B.bctx) (sp : expr) (b : expr) (off : Z) (n : expr) : bool :=
  let '(spb, spk) := split_lit sp in
  (AX2B.xinsideB bc b off n spb spk (ELit two47) || AX2B.xinside0B bc b off n spb spk (ELit two47))%bool.
Lemma above_sp_b_eq : forall k sp b off n, above_sp_b (AX2B.mkbc k) sp b off n = above_sp k sp b off n.
Proof. intros. unfold above_sp_b, above_sp. rewrite AX2B.xinsideB_eqf, AX2B.xinside0B_eqf. reflexivity. Qed.
Definition keep_fact_call_b (G : gtable) (bc : AX2B.bctx) (keepblocks : list (expr * expr)) (ws : list (expr * expr))
           (sp : expr) (K : kentry) : bool :=
  match K with
  | KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true
  | KImg lo hi => Z.leb (g_ro_lo G) lo && Z.leb hi (g_img_hi G) && lit_disjoint lo hi (g_priv G)
  | KWr _ _ | KUnk _ _ => false
  | _ => match kentry_range K with
         | Some (b, off, n) =>
             if (exists_inside_b bc b off n keepblocks || above_sp_b bc sp b off n || img_lit_x_b G bc b off n)
             then forallb (fun w => let '(wb, wk) := split_lit (fst w) in AX2B.ranges_apart_xB bc b off n wb wk (snd w)) ws
             else false
         | None => false
         end
  end%bool.
Lemma keep_fact_call_b_eq : forall G k keepblocks ws sp K, keep_fact_call_b G (AX2B.mkbc k) keepblocks ws sp K = keep_fact_call G k keepblocks ws sp K.
Proof.
  intros. unfold keep_fact_call_b, keep_fact_call.
  destruct K; try reflexivity; (destruct (kentry_range _) as [[[b off] nn]|]; [|reflexivity]);
    rewrite exists_inside_b_eq, above_sp_b_eq, img_lit_x_b_eq, AX2B.ranges_apart_xB_eqf; reflexivity.
Qed.
Definition sticky_call_b (bc : AX2B.bctx) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KWr (SA b off) n | KUnk (SA b off) n => if owned_x_b bc live fl top bud b off n then true else above_x_b bc top sp b off n
  | _ => false
  end.
Lemma sticky_call_b_eq : forall k live fl top bud sp K, sticky_call_b (AX2B.mkbc k) live fl top bud sp K = sticky_call k live fl top bud sp K.
Proof. intros. unfold sticky_call_b, sticky_call. destruct K as [| | | | | | [b off] n0 | | | [b off] n0]; try reflexivity; rewrite owned_x_b_eq, above_x_b_eq; reflexivity. Qed.
Fixpoint kcutM (ws : list (expr * expr)) (k : list kentry) : list kentry :=
  match ws with
  | [] => k
  | w :: ws' => let '(wb, wk) := split_lit (fst w) in kn_cutoutM (kcutM ws' k) wb wk (snd w)
  end.
Lemma kcutM_eq : forall ws k, kcutM ws k = kcut ws k.
Proof. induction ws as [|w ws IH]; intros k; [reflexivity|]. cbn [kcutM kcut]. rewrite IH, kn_cutoutM_eq. reflexivity. Qed.
Definition call_kept_ref (G : gtable) (k : list kentry) (keepblocks ws : list (expr * expr)) (sp : expr) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z)
           (v : nat) : list kentry :=
  List.filter (fun K => kentry_vars_lt v K && sticky_call k live fl top bud sp K)%bool k
  ++ List.filter (fun K => kentry_vars_lt v K && keep_fact_call G k keepblocks ws sp K)%bool (kcut ws k).
Definition call_kept (G : gtable) (k : list kentry) (keepblocks ws : list (expr * expr)) (sp : expr) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z)
           (v : nat) : list kentry :=
  let bc := AX2B.mkbc k in
  List.filter (fun K => if kentry_vars_lt v K then sticky_call_b bc live fl top bud sp K else false) k
  ++ List.filter (fun K => if kentry_vars_lt v K then keep_fact_call_b G bc keepblocks ws sp K else false) (kcutM ws k).
Lemma call_kept_fe : call_kept = call_kept_ref.
Proof.
  repeat (apply functional_extensionality; intros ?). unfold call_kept, call_kept_ref. cbv zeta. rewrite kcutM_eq.
  f_equal; apply filter_ext; intros K; [rewrite sticky_call_b_eq | rewrite keep_fact_call_b_eq]; reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint remove_pair (p : expr * expr) (l : list (expr * expr)) : option (list (expr * expr)) :=
  match l with
  | [] => None
  | q :: r => if pair_eqb p q then Some r else match remove_pair p r with Some r' => Some (q :: r') | None => None end
  end.
Fixpoint remove_pairs (ps : list (expr * expr)) (l : list (expr * expr)) : option (list (expr * expr)) :=
  match ps with
  | [] => Some l
  | p :: ps' => match remove_pair p l with Some l' => remove_pairs ps' l' | None => None end
  end.

(* [comment removed for export] *)
Definition acs_eqb_nopc (t t' : acs) : bool :=
  (list_eqb expr_eqb (s_regs (a_ss t)) (s_regs (a_ss t'))
   && list_eqb kentry_eqb (kn t) (kn t')
   && Nat.eqb (nxt t) (nxt t')
   && match s_log (a_ss t), s_log (a_ss t') with [], [] => true | _, _ => false end
   && list_eqb pair_eqb (a_vis t) (a_vis t') && list_eqb pair_eqb (a_ghost t) (a_ghost t')
   && expr_eqb (a_brk t) (a_brk t') && Z.eqb (a_ylo t) (a_ylo t')
   && list_eqb amap_eqb (a_maps t) (a_maps t'))%bool.      (* [comment removed for export] *)
Definition touts_agree (touts : list acs) : bool :=
  match touts with
  | [] => false
  | t :: r => forallb (acs_eqb_nopc t) r
  end.

(* [comment removed for export] *)
Definition is_ret_at (p : Z) : bool :=
  match itab_lookup (mk_itab_ranges segs [(p, 1%nat)]) p with
  | Some (Jalr rd rs imm) => bv_eqb rd 0%bv && bv_eqb rs (Z_to_bv 5 1) && Z.eqb (bv_signed imm) 0
  | _ => false
  end%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wsok_ref (G : gtable) (ce : gcallee) (k : list kentry) (cs tin : acs) (th : list expr) (nxf : nat)
           (keepblocks ws : list (expr * expr)) (top sp : expr) : bool :=
  (forallb (fun w => let '(wb, wk) := split_lit (fst w) in
                            owned_x k (keepblocks ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) wb wk (snd w) && bflat_x k wb wk (snd w)
                            && ranges_apart_x k wb wk (snd w) (ELit 0) (g_img_lo G) (ELit (g_img_hi G - g_img_lo G))) ws   (* [comment removed for export] *)
                 && forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (keepblocks ++ a_ghost cs)
                 && expr_eqb top sp
                 && Z.leb 0 (a_ylo tin)
                 && (let '(spb, spk) := split_lit sp in
                     (* [comment removed for export] *)
                     let yreq := match acs_floor (a_maps tin) with None => Z.max 1 (a_ylo tin) | Some _ => 1 end in
                     in_floor k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - yreq) (ELit yreq) && bflat_x k spb spk (ELit 0)
                     && match acs_floor (a_maps tin) with
                        | None => true
                        | Some f' => maps_vars_lt nxf (a_maps tin) && in_floor k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (tsubst th f') 0 (ELit 1)
                        end)
                 && match cost_hi k keepblocks with Some ch => Z.leb 0 ch && Z.leb (ch + ce_bcap ce) bcap | None => false end
                 && Z.leb (Z.of_nat (length keepblocks) + ce_ccap ce) ccap
                 && Z.leb 0 (ce_bcap ce) && Z.leb 0 (ce_ccap ce))%bool.
Section WsokLazy.
#[local] Notation "a && b" := (if a then b else false) (at level 40, left associativity, only parsing) : bool_scope.
Fixpoint cost_hi_b (bc : AX2B.bctx) (live : list (expr * expr)) : option Z :=
  match live with
  | [] => Some 0
  | (_, n) :: r => match AX2B.xhiB bc n, cost_hi_b bc r with Some h, Some c => Some (h + MBLK + c) | _, _ => None end
  end.
Lemma cost_hi_b_eq : forall k live, cost_hi_b (AX2B.mkbc k) live = cost_hi k live.
Proof. intros k live. induction live as [|[x n] r IH]; [reflexivity|]. cbn [cost_hi_b cost_hi]. rewrite IH, AX2B.xhiB_eqf. reflexivity. Qed.
Lemma owned_x_b_fe : forall k, owned_x_b (AX2B.mkbc k) = owned_x k.
Proof. intros k. do 7 (apply functional_extensionality; intro). apply owned_x_b_eq. Qed.
Definition wsok (G : gtable) (ce : gcallee) (k : list kentry) (cs tin : acs) (th : list expr) (nxf : nat)
           (keepblocks ws : list (expr * expr)) (top sp : expr) : bool :=
  let bc := AX2B.mkbc k in
  (AX2B.forallb_lz (fun w => let '(wb, wk) := split_lit (fst w) in
                            owned_x_b bc (keepblocks ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) wb wk (snd w) && bflat_x_b bc wb wk (snd w)
                            && AX2B.ranges_apart_xB bc wb wk (snd w) (ELit 0) (g_img_lo G) (ELit (g_img_hi G - g_img_lo G))) ws   (* [comment removed for export] *)
                 && AX2B.forallb_lz (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x_b bc lb lk (snd bl)) (keepblocks ++ a_ghost cs)
                 && expr_eqb top sp
                 && Z.leb 0 (a_ylo tin)
                 && (let '(spb, spk) := split_lit sp in
                     (* [comment removed for export] *)
                     let yreq := match acs_floor (a_maps tin) with None => Z.max 1 (a_ylo tin) | Some _ => 1 end in
                     in_floorB bc (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - yreq) (ELit yreq) && bflat_x_b bc spb spk (ELit 0)
                     && match acs_floor (a_maps tin) with
                        | None => true
                        | Some f' => maps_vars_lt nxf (a_maps tin) && in_floorB bc (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (tsubst th f') 0 (ELit 1)
                        end)
                 && match cost_hi_b bc keepblocks with Some ch => Z.leb 0 ch && Z.leb (ch + ce_bcap ce) bcap | None => false end
                 && Z.leb (Z.of_nat (length keepblocks) + ce_ccap ce) ccap
                 && Z.leb 0 (ce_bcap ce) && Z.leb 0 (ce_ccap ce))%bool.
Lemma wsok_fe : wsok = wsok_ref.
Proof.
  do 11 (apply functional_extensionality; intro). unfold wsok, wsok_ref. cbv zeta.
  rewrite ?AX2B.forallb_lz_fe, ?owned_x_b_fe, ?bflat_x_b_fe, ?AX2B.ranges_apart_xB_eqf, ?in_floorB_eqf, ?cost_hi_b_eq.
  reflexivity.
Qed.
End WsokLazy.

Definition node_call (G : gtable) (ce : gcallee) (args : list expr) (cs : acs) : option acs :=
  let tin := ce_tin ce in let nxf := ce_nxf ce in
  match ce_touts ce with
  | [] => None
  | tout :: _ =>
  if negb (Z.eqb (pc cs) (pc tin) && fresh_ok nx0 cs && touts_agree (ce_touts ce)
           && forallb (fun t => is_ret_at (pc t)) (ce_touts ce)
           && Nat.eqb (length (s_regs (a_ss cs))) 32 && Nat.eqb (length (s_regs (a_ss tin))) 32
           && Nat.eqb (length (s_regs (a_ss tout))) 32
           && match s_log (a_ss tin), s_log (a_ss tout) with [], [] => true | _, _ => false end
           && Nat.leb nxf (nxt tout) && kn_vars_lt (nxt tout) (kn tout) && sr_vars_lt (nxt tout) (s_regs (a_ss tout))
           && pairs_vars_lt (nxt tout) (a_vis tout)
           && kn_vars_lt nxf (kn tin) && pairs_vars_lt nxf (a_vis tin) && pairs_vars_lt nxf (a_ghost tin)
           && expr_vars_lt nxf (a_brk tin)
           && list_eqb pair_eqb (a_ghost tin) (a_ghost tout) && expr_eqb (a_brk tin) (a_brk tout))%bool
  then None else
  match bind ce args cs with
  | None => None
  | Some th =>
    if negb (forallb (expr_vars_lt (nxt cs)) th && Nat.eqb (length th) nxf)%bool then None else
    let k := kn cs in let sp := reg cs 2 in
    (* [comment removed for export] *)
    if negb (list_eqb expr_eqb (map (tsubst th) (s_regs (a_ss tin))) (s_regs (a_ss cs))) then None else
    (* [comment removed for export] *)
    match ret_lit cs, nth 1 (s_regs (a_ss tout)) (ELit 0), nth 1 (s_regs (a_ss tin)) (ELit 0) with
    | Some ret, EVar r1, EVar r1' =>
      if negb (Nat.eqb r1 r1' && Nat.ltb r1 nxf)%bool then None else
      (* [comment removed for export] *)
      if negb (kentails_all segs A k (map (ktsubst th) (kn tin))) then None else
      (* [comment removed for export] *)
      let passed := map (ptsubst th) (a_vis tin) in
      match remove_pairs passed (a_vis cs) with
      | None => None
      | Some keepblocks =>
        let ws := map (ptsubst th) (a_ghost tin) in
        let top := tsubst th (a_brk tin) in
        (* [comment removed for export] *)
        if negb (wsok G ce k cs tin th nxf keepblocks ws top sp)
        then None else
        (* [comment removed for export] *)
        let v := nxt cs in
        let th' := out_subst th nxf (nxt tout) v in
        let kept := call_kept G k keepblocks ws sp (keepblocks ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) v in   (* [comment removed for export] *)
        Some (ACS (mk_ss ret (map (tsubst th') (s_regs (a_ss tout))) (map (kresplit k) (map (ktsubst th') (kn tout)) ++ kept)
                         (v + (nxt tout - nxf))%nat)
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (keepblocks ++ map (ptsubst th') (a_vis tout)) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      end
    | _, _, _ => None
    end
  end
  end.
(* [comment removed for export] *)
Definition call_shareU (G : gtable) (ce : gcallee) (args : list expr) (cs : acs) : option (bool * option (bool * list kentry)) :=
  let tin := ce_tin ce in let nxf := ce_nxf ce in
  match bind ce args cs with
  | None => None
  | Some th =>
    let k := kn cs in let sp := reg cs 2 in
    Some (kentails_all segs A k (map (ktsubst th) (kn tin)),
      let passed := map (ptsubst th) (a_vis tin) in
      match remove_pairs passed (a_vis cs) with
      | None => None
      | Some keepblocks =>
        let ws := map (ptsubst th) (a_ghost tin) in
        let top := tsubst th (a_brk tin) in
        let v := nxt cs in
        Some (wsok G ce k cs tin th nxf keepblocks ws top sp,
              call_kept G k keepblocks ws sp (keepblocks ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) v)
      end)
  end.
Definition node_callSU (sh : option (bool * option (bool * list kentry))) (G : gtable) (ce : gcallee) (args : list expr) (cs : acs) : option acs :=
  let tin := ce_tin ce in let nxf := ce_nxf ce in
  match ce_touts ce with
  | [] => None
  | tout :: _ =>
  if negb (Z.eqb (pc cs) (pc tin) && fresh_ok nx0 cs && touts_agree (ce_touts ce)
           && forallb (fun t => is_ret_at (pc t)) (ce_touts ce)
           && Nat.eqb (length (s_regs (a_ss cs))) 32 && Nat.eqb (length (s_regs (a_ss tin))) 32
           && Nat.eqb (length (s_regs (a_ss tout))) 32
           && match s_log (a_ss tin), s_log (a_ss tout) with [], [] => true | _, _ => false end
           && Nat.leb nxf (nxt tout) && kn_vars_lt (nxt tout) (kn tout) && sr_vars_lt (nxt tout) (s_regs (a_ss tout))
           && pairs_vars_lt (nxt tout) (a_vis tout)
           && kn_vars_lt nxf (kn tin) && pairs_vars_lt nxf (a_vis tin) && pairs_vars_lt nxf (a_ghost tin)
           && expr_vars_lt nxf (a_brk tin)
           && list_eqb pair_eqb (a_ghost tin) (a_ghost tout) && expr_eqb (a_brk tin) (a_brk tout))%bool
  then None else
  match bind ce args cs with
  | None => None
  | Some th =>
    if negb (forallb (expr_vars_lt (nxt cs)) th && Nat.eqb (length th) nxf)%bool then None else
    let k := kn cs in let sp := reg cs 2 in
    (* [comment removed for export] *)
    if negb (list_eqb expr_eqb (map (tsubst th) (s_regs (a_ss tin))) (s_regs (a_ss cs))) then None else
    (* [comment removed for export] *)
    match ret_lit cs, nth 1 (s_regs (a_ss tout)) (ELit 0), nth 1 (s_regs (a_ss tin)) (ELit 0) with
    | Some ret, EVar r1, EVar r1' =>
      if negb (Nat.eqb r1 r1' && Nat.ltb r1 nxf)%bool then None else
      (* [comment removed for export] *)
      if negb (match sh with Some (e, _) => e | None => kentails_all segs A k (map (ktsubst th) (kn tin)) end) then None else
      (* [comment removed for export] *)
      let passed := map (ptsubst th) (a_vis tin) in
      match remove_pairs passed (a_vis cs) with
      | None => None
      | Some keepblocks =>
        let ws := map (ptsubst th) (a_ghost tin) in
        let top := tsubst th (a_brk tin) in
        (* [comment removed for export] *)
        if negb (match sh with Some (_, Some (c0, _)) => c0 | _ => wsok G ce k cs tin th nxf keepblocks ws top sp end)
        then None else
        (* [comment removed for export] *)
        let v := nxt cs in
        let th' := out_subst th nxf (nxt tout) v in
        let kept := match sh with Some (_, Some (_, f)) => f | _ => call_kept G k keepblocks ws sp (keepblocks ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) v end in   (* [comment removed for export] *)
        Some (ACS (mk_ss ret (map (tsubst th') (s_regs (a_ss tout))) (map (kresplit k) (map (ktsubst th') (kn tout)) ++ kept)
                         (v + (nxt tout - nxf))%nat)
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (keepblocks ++ map (ptsubst th') (a_vis tout)) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      end
    | _, _, _ => None
    end
  end
  end.
Lemma node_callSU_eq : forall G ce args cs, node_callSU (call_shareU G ce args cs) G ce args cs = node_call G ce args cs.
Proof.
  intros G ce args cs. unfold node_callSU, node_call, call_shareU. cbv zeta.
  destruct (ce_touts ce) as [|tout touts]; [reflexivity|].
  destruct (bind ce args cs) as [th|]; [|reflexivity].
  destruct (remove_pairs (map (ptsubst th) (a_vis (ce_tin ce))) (a_vis cs)) as [keepblocks|]; cbv beta iota; reflexivity.
Qed.
(* [comment removed for export] *)
Record gcallee2 : Type := GCE2 {
  c2_nxf : nat; c2_tin : acs; c2_touts0 : list acs; c2_touts1 : list acs; c2_bcap : Z; c2_ccap : Z }.
Definition c2_class0 (c : gcallee2) : gcallee := GCE (c2_nxf c) (c2_tin c) (c2_touts0 c) (c2_bcap c) (c2_ccap c).
Definition c2_class1 (c : gcallee2) : gcallee := GCE (c2_nxf c) (c2_tin c) (c2_touts1 c) (c2_bcap c) (c2_ccap c).
Definition c2_merged (c : gcallee2) : gcallee := GCE (c2_nxf c) (c2_tin c) (c2_touts0 c ++ c2_touts1 c) (c2_bcap c) (c2_ccap c).
Lemma call_shareU_classes : forall G c args cs, call_shareU G (c2_class0 c) args cs = call_shareU G (c2_class1 c) args cs.
Proof. intros. reflexivity. Qed.
Definition node_call2 (G : gtable) (c : gcallee2) (args : list expr) (cs : acs) : option (acs * acs) :=
  let sh := call_shareU G (c2_class0 c) args cs in   (* [comment removed for export] *)
  match node_callSU sh G (c2_class0 c) args cs, node_callSU sh G (c2_class1 c) args cs with
  | Some a, Some b => Some (a, b)
  | _, _ => None
  end.
Lemma node_call2_eq : forall G c args cs, node_call2 G c args cs =
  match node_call G (c2_class0 c) args cs, node_call G (c2_class1 c) args cs with
  | Some a, Some b => Some (a, b)
  | _, _ => None
  end.
Proof.
  intros. unfold node_call2. cbv zeta. rewrite (node_callSU_eq G (c2_class0 c)), (call_shareU_classes G c args cs), (node_callSU_eq G (c2_class1 c)).
  reflexivity.
Qed.
(* [comment removed for export] *)
Definition node_call2_cond (G : gtable) (COND : acs -> list expr -> bool) (c : gcallee2) (args : list expr) (cs : acs) : option (acs * acs) :=
  match bind (c2_class0 c) args cs with
  | Some th => if COND cs th then node_call2 G c args cs else None
  | None => None
  end.
End Node.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable A : atable.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.

(* [comment removed for export] *)

Lemma kn_readable_x_sound : forall E M k sb sk ne,
  know_ok SEGS E M k -> kn_readable_x k sb sk ne = true ->
  0 <= estart E (SA sb sk) /\ estart E (SA sb sk) + elenZ E ne <= 2 ^ 64
  /\ forall i, 0 <= i < elenZ E ne -> M (Z_to_bv 64 (estart E (SA sb sk) + i)) <> None.
Proof.
  intros E M k sb sk ne HK H. unfold kn_readable_x in H. apply existsb_exists in H as [K [HinK HKt]].
  pose proof (proj1 (Forall_forall _ _) HK K HinK) as HKK.
  pose proof (u64_range (edenot E ne)) as Hne. unfold elenZ in *.
  assert (GEN : forall kb kk len (P : option byte -> Prop),
            xinside k sb sk ne kb kk len = true ->
            flat E (SA kb kk) (bv_unsigned (edenot E len)) ->
            (forall i, 0 <= i < bv_unsigned (edenot E len) -> P (M (Z_to_bv 64 (estart E (SA kb kk) + i)))) ->
            (forall x, P x -> x <> None) ->
            0 <= estart E (SA sb sk) /\ estart E (SA sb sk) + bv_unsigned (edenot E ne) <= 2 ^ 64
            /\ forall i, 0 <= i < bv_unsigned (edenot E ne) -> M (Z_to_bv 64 (estart E (SA sb sk) + i)) <> None).
  { intros kb kk len P Hx Hfl HP HPn.
    destruct (xinside_sound SEGS E M k sb sk ne kb kk len HK Hx) as [X1 X2]. unfold elenZ in X2.
    destruct Hfl as (F1 & F2 & F3 & F4).
    split; [lia|]. split; [lia|]. intros i Hi.
    replace (estart E (SA sb sk) + i) with (estart E (SA kb kk) + (estart E (SA sb sk) - estart E (SA kb kk) + i)) by lia.
    apply HPn. apply HP. lia. }
  destruct K as [|[kb kk] len|[kb kk] len j| | | | | |[kb kk] len c|[kb kk] len]; try discriminate; cbn [kentry_ok] in HKK; unfold elenZ in HKK.
  - destruct HKK as [Hfl Hz]. eapply (GEN kb kk len (fun x => x = Some (Z_to_bv 8 0))); [exact HKt | exact Hfl | exact Hz | intros x ->; discriminate].
  - destruct HKK as (Hfl & Hl & Hz). eapply (GEN kb kk len (fun x => exists b, x = Some b)); [exact HKt | exact Hfl | | intros x [b ->]; discriminate].
    intros i Hi. eexists. apply Hz. exact Hi.
  - destruct HKK as [Hfl Hz]. eapply (GEN kb kk len (fun x => x = Some (Z_to_bv 8 c))); [exact HKt | exact Hfl | exact Hz | intros x ->; discriminate].
  - destruct HKK as [Hfl Hz]. eapply (GEN kb kk len (fun x => x <> None)); [exact HKt | exact Hfl | exact Hz | intros x Hx; exact Hx].
Qed.

Lemma kentails_sound : forall E M k K,
  know_ok SEGS E M k -> kentails SEGS A k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k K HK H. unfold kentails in H. apply orb_prop in H as [H|H].
  { assert (H1 : kn_incl_h A k [K] = true) by (unfold kn_incl_h; cbn [forallb]; rewrite H; reflexivity).
    pose proof (kn_incl_h_sound SEGS A SEGS_in_hull HULL_ok E M k [K] HK H1) as X. exact (Forall_inv X). }
  destruct K as [[b o] w v|[b o] n|a n kb|lo hi|e m|e lo hi|[b o] n|[b1 o1] n1 [b2 o2] n2|a n c|[b o] n]; try discriminate; cbn [kentry_ok].
  - (* [comment removed for export] *)
    apply andb_prop in H as [H Hl]. apply andb_prop in H as [H Hfl]. apply andb_prop in H as [Hw1 Hw8].
    apply Nat.leb_le in Hw1. apply Nat.leb_le in Hw8.
    destruct (know_lookup SEGS k b o w false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
    destruct scs; [|discriminate]. apply expr_eqb_eq in Hl. subst v'.
    pose proof (flat_x_sound SEGS E M k b o (ELit (Z.of_nat w)) HK Hfl) as (F1 & F2 & F3).
    cbn [edenot] in F2, F3. rewrite u64_lit in F2, F3 by lia.
    assert (Hflat : flat E (SA b o) (Z.of_nat w)) by (unfold flat; lia).
    destruct (lookup_piece SEGS E M k b o w v hs HK ltac:(lia) HL Hflat) as (bs & Hrd & Hlen & Hbs).
    split; [lia|]. split; [exact Hflat|]. rewrite adenot_SA, Hrd, <- Hbs. reflexivity.
  - (* [comment removed for export] *)
    apply andb_prop in H as [H Hbf].
    destruct (kzero_x_sound SEGS E M k k b o n HK HK H) as (Hz & Z1 & Z2).
    destruct (bflat_x_sound SEGS E M k b o n HK Hbf) as (B1 & B2 & B3).
    split; [unfold flat; pose proof (u64_range (edenot E n)); unfold elenZ in *; lia | exact Hz].
  - (* [comment removed for export] *)
    apply andb_prop in H as [Hm Hd]. apply Z.ltb_lt in Hm. apply Z.eqb_eq in Hd.
    destruct (ealign_sound SEGS E M k e HK) as [A1 [q Hq]]. split; [lia|].
    apply Z.mod_divide in Hd; [|lia]. destruct Hd as [r Hr]. rewrite Hq, Hr.
    rewrite Z.mul_assoc. apply Z_mod_mult.
  - (* [comment removed for export] *)
    exact (GPS.kpure_entails_sound SEGS E M k (KRange e lo hi) HK H).
  - (* [comment removed for export] *)
    apply andb_prop in H as [H Hbf].
    destruct (kwritable_x_sound SEGS E M k k b o n HK HK H) as (W1 & W2 & W3).
    destruct (bflat_x_sound SEGS E M k b o n HK Hbf) as (B1 & B2 & B3).
    split; [unfold flat; pose proof (u64_range (edenot E n)); unfold elenZ in *; lia|].
    intros d m Hd Hdm. unfold elenZ in *. destruct m as [|m']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    eapply (store_ok_all SEGS M (Z.to_nat (d + Z.of_nat (S m'))) (Z_to_bv 64 (estart E (SA b o))));
      [rewrite u64_lit by lia; lia | apply W1; lia | rewrite u64_lit by lia; lia].
  - (* [comment removed for export] *)
    exact (ranges_apart_x_sound SEGS E M k b1 o1 n1 b2 o2 n2 HK H).
  - (* [comment removed for export] *)
    apply andb_prop in H as [H Hbf].
    destruct (kn_readable_x_sound E M k b o n HK H) as (R1 & R2 & R3).
    destruct (bflat_x_sound SEGS E M k b o n HK Hbf) as (B1 & B2 & B3).
    split; [unfold flat; pose proof (u64_range (edenot E n)); unfold elenZ in *; lia | exact R3].
Qed.

Lemma kentails_all_sound : forall E M k tk,
  know_ok SEGS E M k -> kentails_all SEGS A k tk = true -> know_ok SEGS E M tk.
Proof.
  intros E M k tk HK H. rewrite kentails_all_eq in H. unfold know_ok. apply Forall_forall. intros K Hin.
  eapply kentails_sound; [exact HK|]. exact (proj1 (forallb_forall _ _) H K Hin).
Qed.

End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CallSound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable A : atable.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_vm : forall L B C M mdl mdl', AINVH L B C M mdl -> m_vmmaps mdl' = m_vmmaps mdl -> AINVH L B C M mdl'.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok G b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
Hypothesis G_img_hull : 0 <= g_img_lo G <= g_img_hi G /\ g_img_hi G < 2 ^ 64.
Hypothesis G_priv : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= bv_unsigned a < g_img_hi G) -> find_segment SEGS (bv_unsigned a) 1 = None.

#[local] Notation AINVf := (AINV_f SWIN G AINVH).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nil_of (l : list (Z * Z)) : list (Z * Z) := match l with _ => [] end.
#[local] Notation AINV0 := (AINV_f (nil_of SWIN) G AINVH).
Definition UTRUE (E : env) : Prop := True.
(* [comment removed for export] *)
Lemma AINVH_frame_nil : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins (nil_of SWIN) (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Proof.
  intros L B C M M' mdl HA H. eapply AINVH_frame; [exact HA|]. intros a Hne. destruct (H a Hne) as [Ho HD].
  split; [|exact HD]. destruct Ho as [Hb|[Hc|Hw]]; [left; exact Hb | right; left; exact Hc |].
  destruct Hw as (lo & hi & Hin & _). cbn in Hin. destruct Hin.
Qed.

Lemma in_wins_dec : forall W z, in_wins W z \/ ~ in_wins W z.
Proof.
  intros W z. destruct (existsb (fun p => Z.leb (fst p) z && Z.ltb z (snd p))%bool W) eqn:H.
  - left. apply existsb_exists in H as [[lo hi] [Hin Hb]]. cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists lo, hi. split; [exact Hin | lia].
  - right. intros (lo & hi & Hin & Hr). assert (X : existsb (fun p => Z.leb (fst p) z && Z.ltb z (snd p))%bool W = true); [|rewrite X in H; discriminate].
    apply existsb_exists. exists (lo, hi). split; [exact Hin|]. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition callee_contract_when (Q : env -> Prop) (ce : gcallee) : Prop :=
  forall (PERMf : list (Z * Z)) (TOPf : Z) (HID : list (Z * Z)) (M0 : word -> option byte) (B0 C0 : Z)
         (FS0 : Fs.Fs) (FDS0 : list (word * FdEntry)) E fx R M mdl (T : TSet),
    0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
    Q E ->
    GPS.cs_ok SEGS PERMf TOPf FS0 FDS0 (AINV0 PERMf TOPf HID M0 B0 C0) FXOK UTRUE E (ce_tin ce) fx R M mdl ->
    T [] ->
    (forall tout E' fx' R' M' mdl', In tout (ce_touts ce) -> env_agree (ce_nxf ce) E E' ->
        GPS.cs_ok SEGS PERMf TOPf FS0 FDS0 (AINV0 PERMf TOPf HID M0 B0 C0) FXOK UTRUE E' tout fx' R' M' mdl' ->
        m_fs mdl' = m_fs mdl ->
        RZ (cfgF SEGS fx' R' (pc tout) M' mdl') T) ->
    RZ (cfgF SEGS fx R (pc (ce_tin ce)) M mdl) T.
Definition QTRUE (E : env) : Prop := True.
Definition callee_contract : gcallee -> Prop := callee_contract_when QTRUE.

(* [comment removed for export] *)
Variable nx0 : nat.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable HIDc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Variable bcap ccap : Z.
Hypothesis bcap_ok : B0c + bcap <= GBUDGET.
Hypothesis ccap_ok : C0c + ccap <= GCOUNT.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.

#[local] Notation AINVc := (AINVf PERMc SPTOPc HIDc M0c B0c C0c).
#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ).

(* [comment removed for export] *)

Lemma remove_pair_perm : forall p l l', remove_pair p l = Some l' -> Permutation.Permutation l (p :: l').
Proof.
  intros p l. induction l as [|q r IH]; intros l' H; cbn [remove_pair] in H; [discriminate|].
  destruct (pair_eqb p q) eqn:Heq.
  - injection H as <-. apply pair_eqb_eq in Heq. subst q. apply Permutation.Permutation_refl.
  - destruct (remove_pair p r) as [r'|] eqn:Hr; [|discriminate]. injection H as <-.
    eapply Permutation.Permutation_trans; [apply Permutation.perm_skip; apply IH; reflexivity|]. apply Permutation.perm_swap.
Qed.

Lemma remove_pairs_perm : forall ps l l', remove_pairs ps l = Some l' -> Permutation.Permutation l (ps ++ l').
Proof.
  intros ps. induction ps as [|p ps IH]; intros l l' H; cbn [remove_pairs] in H.
  - injection H as <-. apply Permutation.Permutation_refl.
  - destruct (remove_pair p l) as [l1|] eqn:Hp; [|discriminate].
    eapply Permutation.Permutation_trans; [apply remove_pair_perm; exact Hp|]. cbn [app]. apply Permutation.perm_skip. apply IH. exact H.
Qed.

Lemma remove_pairs_incl : forall ps l l' x, remove_pairs ps l = Some l' -> In x l' -> In x l.
Proof.
  intros ps l l' x H Hin. pose proof (remove_pairs_perm ps l l' H) as P.
  apply (Permutation.Permutation_in x (Permutation.Permutation_sym P)). apply in_app_iff. right. exact Hin.
Qed.

Lemma blocks_den_perm : forall E l l', Permutation.Permutation l l' -> Permutation.Permutation (blocks_den E l) (blocks_den E l').
Proof. intros. unfold blocks_den. apply Permutation.Permutation_map. assumption. Qed.

Lemma acs_eqb_nopc_cs_ok : forall PERM TOP FS FDS AINV UI t t' E fx R M mdl,
  acs_eqb_nopc t t' = true ->
  GPS.cs_ok SEGS PERM TOP FS FDS AINV FXOK UI E t' fx R M mdl -> GPS.cs_ok SEGS PERM TOP FS FDS AINV FXOK UI E t fx R M mdl.
Proof.
  intros PERM TOP FS FDS AINV UI t t' E fx R M mdl H HC. unfold acs_eqb_nopc in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply (list_eqb_eq expr_eqb expr_eqb_eq) in H. apply (list_eqb_eq kentry_eqb kentry_eqb_eq) in X6.
  apply (list_eqb_eq pair_eqb pair_eqb_eq) in X3. apply (list_eqb_eq pair_eqb pair_eqb_eq) in X2.
  apply expr_eqb_eq in X1. apply Z.eqb_eq in X0. apply (list_eqb_eq amap_eqb APS.amap_eqb_eq) in X.
  destruct (s_log (a_ss t)) eqn:HL; [|discriminate].
  destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT CM CFL]; constructor; unfold kn in *; rewrite ?H, ?X6, ?X3, ?X2, ?X1, ?X0, ?X; try assumption.
Qed.

Lemma is_ret_at_sound : forall p fx R M,
  is_ret_at SEGS p = true ->
  RiscvSemantics.step SEGS (mkstF fx R (Z_to_bv 64 p) M (seg_rom SEGS))
  = MachineOk (mkstF fx R (v_jalr (getr R (Z_to_bv 5 1)) 0) M (seg_rom SEGS)).
Proof.
  intros p fx R M H. unfold is_ret_at in H.
  destruct (itab_lookup (mk_itab_ranges SEGS [(p, 1%nat)]) p) as [i|] eqn:Hit; [|discriminate].
  pose proof (mk_itab_ranges_sound SEGS [(p, 1%nat)] _ _ Hit) as Hen. unfold itab_entry in Hen.
  destruct (fetch_word SEGS (Z_to_bv 64 p)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:Hec; [discriminate|].
  destruct (decode_any w) as [[i' isz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb isz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst isz. injection Hen as ->.
  destruct i as [ | | | rd rs imm | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ]; try discriminate.
  apply andb_prop in H as [H Himm]. apply andb_prop in H as [Hrd Hrs].
  assert (rd = 0%bv) by (apply bv_eq; unfold bv_eqb in Hrd; apply Z.eqb_eq in Hrd; exact Hrd). subst rd.
  assert (rs = Z_to_bv 5 1) by (apply bv_eq; unfold bv_eqb in Hrs; apply Z.eqb_eq in Hrs; exact Hrs). subst rs.
  apply Z.eqb_eq in Himm.
  unfold mkstF. rewrite <- !mkstR_None.
  rewrite (stepR_jalr fx SEGS R _ M (seg_rom SEGS) None w 0%bv (Z_to_bv 5 1) imm Hf Hec Hd).
  rewrite bv_eqb_refl. rewrite Himm. reflexivity.
Qed.

(* [comment removed for export] *)
Definition node_call_cond (COND : acs -> list expr -> bool) (ce : gcallee) (args : list expr) (cs : acs) : option acs :=
  match bind ce args cs with
  | Some th => if COND cs th then node_call SEGS A nx0 bcap ccap G ce args cs else None
  | None => None
  end.

(* [comment removed for export] *)
Lemma node_call_split : forall ce args cs cs' E fx R M model,
  cs_ok E cs fx R M model -> node_call SEGS A nx0 bcap ccap G ce args cs = Some cs' ->
  exists th keepblocks,
    bind ce args cs = Some th /\ remove_pairs (map (ptsubst th) (a_vis (ce_tin ce))) (a_vis cs) = Some keepblocks /\
    let Ef := tenv E th in
    let PERMf := wins_den Ef (a_ghost (ce_tin ce)) in let TOPf := sptop_den Ef (a_brk (ce_tin ce)) in
    let HIDf := blocks_den E keepblocks ++ HIDc in let B0f := B0c + bcost E keepblocks in let C0f := C0c + bcount keepblocks in
    GPS.cs_ok SEGS PERMf TOPf FS0 FDS0 (AINV0 PERMf TOPf HIDf M B0f C0f) FXOK UTRUE Ef (ce_tin ce) fx R M model
    /\ 0 <= B0f /\ 0 <= C0f /\ B0f + ce_bcap ce <= GBUDGET /\ C0f + ce_ccap ce <= GCOUNT /\ pc cs = pc (ce_tin ce)
    /\ (forall T : TSet, T [] ->
         (forall E2 fx2 R2 M2 mdl2, env_agree nx0 E E2 /\ env_agree (nxt cs) E E2 -> cs_ok E2 cs' fx2 R2 M2 mdl2 ->
            m_fs mdl2 = m_fs model -> RZ (cfgF SEGS fx2 R2 (pc cs') M2 mdl2) T) ->
         forall toutj E' fx' R' M' mdl', In toutj (ce_touts ce) -> env_agree (ce_nxf ce) Ef E' ->
           GPS.cs_ok SEGS PERMf TOPf FS0 FDS0 (AINV0 PERMf TOPf HIDf M B0f C0f) FXOK UTRUE E' toutj fx' R' M' mdl' ->
           m_fs mdl' = m_fs model -> RZ (cfgF SEGS fx' R' (pc toutj) M' mdl') T).
Proof.
  pose proof SWIN_img as SWIN_img_kept.    (* [comment removed for export] *)
  intros ce args cs cs' E fx R M model HC Hn.
  unfold node_call in Hn. rewrite call_kept_fe, wsok_fe in Hn. unfold call_kept_ref, wsok_ref in Hn.
  destruct (ce_touts ce) as [|tout touts'] eqn:Htouts; [discriminate|].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc1; [|discriminate] end. cbn [negb] in Hn.
  destruct (bind ce args cs) as [th|] eqn:Hbind; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc2; [|discriminate] end. cbn [negb] in Hn.
  cbv zeta in Hn.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hregs; [|discriminate] end. cbn [negb] in Hn.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (nth 1 (s_regs (a_ss tout)) (ELit 0)) as [|r1| | | | | |] eqn:Hr1; try discriminate.
  destruct (nth 1 (s_regs (a_ss (ce_tin ce))) (ELit 0)) as [|r1'| | | | | |] eqn:Hr1'; try discriminate.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc3; [|discriminate] end. cbn [negb] in Hn.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hent; [|discriminate] end. cbn [negb] in Hn.
  destruct (remove_pairs (map (ptsubst th) (a_vis (ce_tin ce))) (a_vis cs)) as [keepblocks|] eqn:Hrm; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc4; [|discriminate] end. cbn [negb] in Hn.
  apply some_inj in Hn. subst cs'.
  (* [comment removed for export] *)
  repeat match type of Hc1 with (_ && _)%bool = true => apply andb_prop in Hc1 as [Hc1 ?X] end.
  rename Hc1 into Hpc. apply Z.eqb_eq in Hpc. rename X15 into Hfresh. rename X14 into Hagree. rename X13 into Hrets.
  apply Nat.eqb_eq in X12. apply Nat.eqb_eq in X11. apply Nat.eqb_eq in X10. rename X12 into Hlen. rename X11 into Hlenin. rename X10 into Hlenout.
  destruct (s_log (a_ss (ce_tin ce))) eqn:Hlogin; [|discriminate]. destruct (s_log (a_ss tout)) eqn:Hlogout; [|discriminate]. clear X9.
  apply Nat.leb_le in X8. rename X8 into Hnxf_le. rename X7 into Hknout_v. rename X6 into Hsrout_v. rename X5 into Hvisout_v.
  rename X4 into Hknin_v. rename X3 into Hvisin_v. rename X2 into Hghin_v. rename X1 into Hbrkin_v.
  apply (list_eqb_eq pair_eqb pair_eqb_eq) in X0. rename X0 into Hgh_io. apply expr_eqb_eq in X. rename X into Hbrk_io.
  apply andb_prop in Hc2 as [Hth_v Hth_len]. apply Nat.eqb_eq in Hth_len.
  apply (list_eqb_eq expr_eqb expr_eqb_eq) in Hregs.
  apply andb_prop in Hc3 as [Hr11 Hr1n]. apply Nat.eqb_eq in Hr11. subst r1'. apply Nat.ltb_lt in Hr1n.
  repeat match type of Hc4 with (_ && _)%bool = true => apply andb_prop in Hc4 as [Hc4 ?X] end.
  rename Hc4 into Hws. rename X6 into Hkbflat. rename X5 into Htop. rename X4 into Hylo0. rename X3 into Hbt.
  rename X2 into Hcost. apply Z.leb_le in X1. apply Z.leb_le in X0. apply Z.leb_le in X. apply Z.leb_le in Hylo0.
  rename X1 into HCcap. rename X0 into HBo0. rename X into HCo0.
  apply expr_eqb_eq in Htop.
  (* [comment removed for export] *)
  set (tin := ce_tin ce) in *. set (nxf := ce_nxf ce) in *. set (v := nxt cs) in *. set (sp := reg cs 2) in *.
  set (k := kn cs) in *.
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (Ef := tenv E th).
  (* [comment removed for export] *)
  assert (HRf : regs_ok Ef (s_regs (a_ss tin)) R).
  { apply (proj1 (regs_ok_tsubst E th (s_regs (a_ss tin)) R)). rewrite Hregs. exact HR. }
  assert (HKf : know_ok SEGS Ef M (kn tin)).
  { apply (proj1 (know_ok_ktsubst SEGS E th M (kn tin))). eapply kentails_all_sound; [exact SEGS_in_hull | exact HULL_ok | exact HK | exact Hent]. }
  set (ws := map (ptsubst th) (a_ghost tin)) in *.
  set (PERMf := wins_den Ef (a_ghost tin)).
  set (TOPf := sptop_den Ef (a_brk tin)).
  assert (HPERMf : wins_den E ws = PERMf) by (unfold ws, PERMf, Ef; apply wins_den_ptsubst).
  destruct (split_lit sp) as [spb spk] eqn:Hssp. apply andb_prop in Hbt as [Hbt Hcf]. apply andb_prop in Hbt as [Hfloor Hspbf].
  pose proof (split_lit_denot E sp spb spk Hssp) as Hspd.
  assert (Hspv2 : uE E sp = bv_unsigned (edenot E spb) + spk).
  { destruct (bflat_x_sound SEGS E M k spb spk (ELit 0) HK Hspbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B3.
    unfold uE. rewrite Hspd. apply u64_lit. lia. }
  (* [comment removed for export] *)
  set (yf := match acs_floor (a_maps tin) with None => Z.max 1 (a_ylo tin) | Some _ => 1 end) in Hfloor.
  assert (Hyf1 : 1 <= yf) by (unfold yf; destruct (acs_floor (a_maps tin)); lia).
  assert (FL : forall z, bv_unsigned (edenot E spb) + (spk - yf) <= z < bv_unsigned (edenot E spb) + (spk - yf) + yf ->
               CEIL_run <= z < SPTOPc /\ SPTOPc < 2 ^ 64).
  { intros z Hz. rewrite <- (co_top HC).
    destruct (bflat_x_sound SEGS E M k spb spk (ELit 0) HK Hspbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B3.
    assert (Hz0 : 0 <= z < 2 ^ 64 /\ yf < 2 ^ 64).
    { (* [comment removed for export] *)
      pose proof Hfloor as Hfl'. unfold in_floor in Hfl'. destruct (split_lit (a_brk cs)) as [tb tk] eqn:Htsp.
      destruct (base_range k tb) as [[tlo thi]|] eqn:Hbr; [|destruct (acs_floor (a_maps cs)); discriminate].
      pose proof (base_range_sound SEGS E M k tb tlo thi HK Hbr) as [T1 T2]. pose proof (u64_range (edenot E tb)) as Rtb.
      pose proof (co_floor HC) as CF0. destruct (acs_floor (a_maps cs)) as [f0|]; cbn [GPS.floor_sem] in CF0.
      - apply andb_prop in Hfl' as [Hfl' L2]. apply andb_prop in Hfl' as [Hfl' L1]. apply andb_prop in Hfl' as [Hfl' H3]. apply andb_prop in Hfl' as [H1 H2].
        apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
        pose proof (lin_ge0_sound SEGS E M k _ _ HK L1) as X1. pose proof (lin_ge0_sound SEGS E M k _ _ HK L2) as X2. cbn [xt_den] in X1, X2.
        cbn [edenot] in X2. rewrite (u64_lit yf) in X2 by (pose proof GlzConst.ceil_lo; unfold GPS.uE, two64 in *; lia).
        pose proof GlzConst.ceil_lo. unfold GPS.uE, two64 in *. lia.
      - apply andb_prop in Hfl' as [Hg Hx]. apply andb_prop in Hg as [Hg H3]. apply andb_prop in Hg as [H1 H2].
        apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
        pose proof (xinside_sound SEGS E M k spb (spk - yf) (ELit yf) tb (tk - a_ylo cs) (ELit (a_ylo cs)) HK Hx) as [X1 X2].
        rewrite !estart_SA in X1, X2. rewrite !(APS.elenZ_lit E) in X2 by (unfold CEIL, two64 in *; lia).
        unfold CEIL, two64 in *. lia. }
    pose proof (GPS.in_floor_sound SEGS E M k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - yf) (ELit yf) (Z_to_bv 64 z) HK Hfloor (co_floor HC)) as X.
    rewrite estart_SA, (APS.elenZ_lit E) in X by lia.
    rewrite u64_lit in X by lia. apply X. lia. }
  assert (Hspv : CEIL_run + yf <= uE E sp).
  { pose proof (FL (bv_unsigned (edenot E spb) + spk - yf) ltac:(lia)). rewrite Hspv2. lia. }
  assert (Hyf : 1 <= yf /\ (acs_floor (a_maps tin) = None -> a_ylo tin <= yf)) by (unfold yf; destruct (acs_floor (a_maps tin)); split; [lia | intros HN; discriminate HN | lia | intros _; lia]).
  assert (HTOPf : TOPf = uE E sp).
  { unfold TOPf, Ef. rewrite <- sptop_den_tsubst, Htop. unfold sptop_den.
    destruct (Z.eqb_spec (uE E sp) 0); [pose proof GlzConst.ceil_lo; lia | reflexivity]. }
  assert (HTOPle : uE E sp <= SPTOPc).
  { pose proof (FL (bv_unsigned (edenot E spb) + spk - 1) ltac:(lia)). rewrite Hspv2. lia. }
  assert (Hceil : CEIL_run <= sp_lin E sp) by (unfold sp_lin; rewrite Hssp; unfold uE in *; lia).
  assert (HPERMown : forall z, in_wins PERMf z ->
            (in_blocks (blocks_den E keepblocks) z \/ in_wins PERMc z \/ (CEIL_run <= z < SPTOPc)) /\ ~ (g_img_lo G <= z < g_img_hi G)).
  { intros z Hz. rewrite <- HPERMf in Hz. destruct Hz as (lo & hi & Hin & Hz).
    unfold wins_den in Hin. apply in_map_iff in Hin as [[wb0 wn] [Heq Hin]]. cbn [fst snd] in Heq. injection Heq as <- <-.
    pose proof (proj1 (forallb_forall _ _) Hws _ Hin) as Hw. cbn [fst snd] in Hw.
    destruct (split_lit wb0) as [wb wk] eqn:Hwsp. apply andb_prop in Hw as [Hw Himg]. apply andb_prop in Hw as [Hown Hbf].
    destruct (bflat_x_sound SEGS E M k wb wk wn HK Hbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B2, B3.
    pose proof (split_lit_denot E wb0 wb wk Hwsp) as Hwd.
    assert (Hu : uE E wb0 = bv_unsigned (edenot E wb) + wk) by (unfold uE; rewrite Hwd; apply u64_lit; lia).
    rewrite Hu in Hz. unfold uE in Hz.
    pose proof (owned_x_sound3 SEGS PERMc SPTOPc E M k keepblocks (a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) wb wk wn (Z_to_bv 64 z)
                  HK Hkbflat (co_perm HC) (co_top HC) (co_floor HC) Hown) as Ho.
    rewrite estart_SA in Ho. unfold elenZ in Ho. rewrite u64_lit in Ho by lia. specialize (Ho Hz).
    unfold owned3 in Ho. rewrite u64_lit in Ho by lia. split; [exact Ho|].
    pose proof (ranges_apart_x_sound SEGS E M k wb wk wn (ELit 0) (g_img_lo G) (ELit (g_img_hi G - g_img_lo G)) HK Himg) as D.
    rewrite !estart_SA in D. unfold elenZ in D. cbn [edenot] in D. rewrite (u64_lit 0) in D by lia.
    rewrite (u64_lit (g_img_hi G - g_img_lo G)) in D by (pose proof G_img_hull; lia). lia. }
  set (HIDf := blocks_den E keepblocks ++ HIDc).
  set (B0f := B0c + bcost E keepblocks). set (C0f := C0c + bcount keepblocks).
  destruct (co_ainv HC) as (HA & HP & HTc & HF & HD).
  assert (Hpermv : Permutation.Permutation (a_vis cs) (map (ptsubst th) (a_vis tin) ++ keepblocks)) by (apply remove_pairs_perm; exact Hrm).
  assert (HBC : bcost E (a_vis cs) = bcost Ef (a_vis tin) + bcost E keepblocks).
  { rewrite (bcost_perm E _ _ Hpermv), GlzNodesAlloc.bcost_app, bcost_ptsubst. reflexivity. }
  assert (HCC : bcount (a_vis cs) = bcount (a_vis tin) + bcount keepblocks).
  { rewrite (bcount_perm _ _ Hpermv), GlzNodesAlloc.bcount_app. unfold bcount. rewrite length_map. reflexivity. }
  destruct (cost_hi k keepblocks) as [ch|] eqn:Hch; [|discriminate]. apply andb_prop in Hcost as [Hch0 HBcap].
  apply Z.leb_le in Hch0. apply Z.leb_le in HBcap.
  destruct (GlzNodesAlloc.cost_hi_sound SEGS E M k keepblocks ch HK Hch) as [Hchle Hkb0].
  assert (Hperm_vis : Permutation.Permutation (blocks_den E (a_vis cs)) (blocks_den Ef (a_vis tin) ++ blocks_den E keepblocks)).
  { unfold Ef. rewrite <- blocks_den_ptsubst, <- GlzNodesAlloc.blocks_den_app. apply blocks_den_perm. apply remove_pairs_perm. exact Hrm. }
  assert (HAf : AINV0 PERMf TOPf HIDf M B0f C0f (blocks_den Ef (a_vis tin)) (bcost Ef (a_vis tin)) (bcount (a_vis tin)) M model).
  { split; [|split; [|split; [|split]]].
    - unfold HIDf, B0f, C0f. rewrite app_assoc.
      replace (B0c + bcost E keepblocks + bcost Ef (a_vis tin)) with (B0c + bcost E (a_vis cs)) by (rewrite HBC; lia).
      replace (C0c + bcount keepblocks + bcount (a_vis tin)) with (C0c + bcount (a_vis cs)) by (rewrite HCC; lia).
      eapply AINVH_perm; [|exact HA].
      apply Permutation.Permutation_app_tail. exact Hperm_vis.
    - (* [comment removed for export] *)
      intros z Hz. destruct (HPERMown z Hz) as [[Hb|[Hp|Hst]] Hnimg].
      + left. unfold HIDf. apply (in_blocks_app). left. exact Hb.
      + destruct (HP z Hp) as [Hh|[Ho|Hsw]]; [left; unfold HIDf; apply in_blocks_app; right; exact Hh | right; left; exact Ho |].
        exfalso. destruct (swin_byte SWIN G SWIN_img _ Hsw) as [S1 _]. apply Hnimg. pose proof G_ro_img. lia.
      + right. left. lia.
    - rewrite HTOPf. lia.
    - intros a _. reflexivity.
    - intros a _ H0. exact H0. }
  assert (HCf : GPS.cs_ok SEGS PERMf TOPf FS0 FDS0 (AINV0 PERMf TOPf HIDf M B0f C0f) FXOK UTRUE Ef tin fx R M model).
  { constructor; try assumption.
    - exact (co_halt HC). - exact (co_lazy HC). - exact (co_fs HC). - exact (co_fds HC).
    - exact I.
    - exact (co_fx HC).
    - reflexivity.
    - reflexivity.
    - exact (co_mat HC).
    - (* [comment removed for export] *)
      destruct Hyf as [_ Hyf2].
      destruct (acs_floor (a_maps tin)) as [f'|] eqn:Hft; cbn [GPS.floor_sem].
      + (* [comment removed for export] *)
        apply andb_prop in Hcf as [_ Hcf].
        unfold Ef, GPS.uE. rewrite <- tsubst_denot.
        pose proof (GPS.in_floor_sound SEGS E M k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (tsubst th f') 0 (ELit 1)
                      (edenot E (tsubst th f')) HK Hcf (co_floor HC)) as X.
        rewrite estart_SA, (APS.elenZ_lit E) in X by lia. apply X. lia.
      + unfold TOPf in HTOPf |- *. rewrite HTOPf. specialize (Hyf2 eq_refl). lia. }
  (* [comment removed for export] *)
  exists th, keepblocks. split; [first [exact Hbind | reflexivity]|]. split; [first [exact Hrm | reflexivity]|].
  cbv zeta. fold Ef. fold PERMf TOPf. fold HIDf B0f C0f.
  split; [exact HCf|]. split; [unfold B0f; lia|]. split; [unfold C0f, bcount; lia|]. split; [unfold B0f; lia|]. split; [unfold C0f, bcount; lia|].
  split; [first [exact Hpc | reflexivity]|].
  intros T HT Hk.
    intros toutj E' fx' R' M' mdl' Hinj Hag HCj Hfs'. try rewrite Htouts in Hinj.
    (* [comment removed for export] *)
    assert (HCo : GPS.cs_ok SEGS PERMf TOPf FS0 FDS0 (AINV0 PERMf TOPf HIDf M B0f C0f) FXOK UTRUE E' tout fx' R' M' mdl').
    { destruct Hinj as [<-|Hinj]; [exact HCj|].
      unfold touts_agree in Hagree. pose proof (proj1 (forallb_forall _ _) Hagree toutj Hinj) as Heq.
      exact (acs_eqb_nopc_cs_ok _ _ _ _ _ _ tout toutj E' fx' R' M' mdl' Heq HCj). }
    (* [comment removed for export] *)
    pose proof (proj1 (forallb_forall _ _) Hrets toutj Hinj) as Hret_at.
    destruct (ret_lit_sound E cs R ret HR Hret) as (R1 & Rok & Rr & Re).
    assert (HR1' : getr R' (Z_to_bv 5 1) = Z_to_bv 64 ret).
    { rewrite (co_regs HCo (Z_to_bv 5 1)). unfold sr_get.
      replace (bv_eqb (Z_to_bv 5 1) 0%bv) with false by reflexivity.
      replace (ridx (Z_to_bv 5 1)) with 1%nat by reflexivity. rewrite Hr1. cbn [edenot].
      rewrite <- (proj1 Hag r1 Hr1n). unfold Ef. cbn [tenv ev]. rewrite <- Hth_len in Hr1n.
      replace (Nat.ltb r1 (length th)) with true by (symmetry; apply Nat.ltb_lt; exact Hr1n).
      rewrite <- R1. rewrite (HR (Z_to_bv 5 1)). unfold sr_get.
      replace (bv_eqb (Z_to_bv 5 1) 0%bv) with false by reflexivity. replace (ridx (Z_to_bv 5 1)) with 1%nat by reflexivity.
      rewrite <- Hregs. replace (ELit 0) with (tsubst th (ELit 0)) by reflexivity. rewrite map_nth. rewrite Hr1'.
      cbn [tsubst]. replace (Nat.ltb r1 (length th)) with true by (symmetry; apply Nat.ltb_lt; exact Hr1n). reflexivity. }
    unfold cfgF. eapply RZ_step; [exact (co_halt HCo) | exact (co_lazy HCo) | reflexivity | apply is_ret_at_sound; exact Hret_at |].
    rewrite HR1'. unfold ret_ok in Rok. rewrite Rok.
    (* [comment removed for export] *)
    set (E'' := Env (fun n => if Nat.ltb n v then ev E n else ev E' (n - v + nxf)%nat) (eb E)).
    assert (Hag'' : env_agree v E E'').
    { split; [|reflexivity]. intros n Hn. unfold E''. cbn [ev]. replace (Nat.ltb n v) with true by (symmetry; apply Nat.ltb_lt; exact Hn). reflexivity. }
    set (th' := out_subst th nxf (nxt tout) v) in *.
    assert (Hebf : eb E' = eb E) by (rewrite <- (proj2 Hag); reflexivity).
    assert (Hagout : env_agree (nxt tout) E' (tenv E'' th')).
    { split; [|cbn [tenv eb]; exact Hebf]. intros n Hn. unfold th', out_subst. cbn [tenv ev].
      rewrite length_app, length_map, length_seq, Hth_len.
      replace (Nat.ltb n (nxf + (nxt tout - nxf))) with true by (symmetry; apply Nat.ltb_lt; lia).
      destruct (Nat.ltb_spec n nxf) as [Hlt|Hge].
      - rewrite app_nth1 by lia. rewrite <- (proj1 Hag n Hlt). unfold Ef. cbn [tenv ev]. rewrite Hth_len.
        replace (Nat.ltb n nxf) with true by (symmetry; apply Nat.ltb_lt; exact Hlt).
        apply (edenot_agree' v); [exact Hag''|].
        assert (HH : (n < length th)%nat) by lia. exact (proj1 (forallb_forall _ _) Hth_v _ (nth_In th (ELit 0) HH)).
      - rewrite app_nth2 by lia. rewrite Hth_len.
        rewrite (nth_indep _ (ELit 0) (EVar (v + 0)%nat)) by (rewrite length_map, length_seq; lia).
        rewrite (map_nth (fun j : nat => EVar (v + j)%nat)). rewrite seq_nth by lia. cbn [edenot]. unfold E''. cbn [ev].
        replace (Nat.ltb (v + (0 + (n - nxf))) v) with false by (symmetry; apply Nat.ltb_ge; lia).
        f_equal. lia. }
    assert (Hagout' : env_agree (nxt tout) (tenv E'' th') E').
    { destruct Hagout as [A1 A2]. split; [intros n Hn; symmetry; apply A1; exact Hn | symmetry; exact A2]. }
    (* [comment removed for export] *)
    destruct (co_ainv HCo) as (HA' & _ & _ & HF' & HD').
    (* [comment removed for export] *)
    assert (STICK : forall x : word,
      (in_blocks (blocks_den E keepblocks) (bv_unsigned x) \/ in_wins PERMc (bv_unsigned x) \/ (CEIL_run <= bv_unsigned x < SPTOPc))
      \/ SPTOPc <= bv_unsigned x ->
      M x <> None -> M' x <> None).
    { intros x Ho0 HMx.
      destruct (Z_lt_le_dec (bv_unsigned x) TOPf) as [Hlt|Hge].
      - assert (Ho : in_blocks (blocks_den E keepblocks) (bv_unsigned x) \/ in_wins PERMc (bv_unsigned x) \/ (CEIL_run <= bv_unsigned x < SPTOPc))
          by (destruct Ho0 as [Ho|Hab]; [exact Ho | exfalso; lia]).
        destruct (Z_lt_le_dec (bv_unsigned x) CEIL_run) as [Hlc|Hgc].
        + (* [comment removed for export] *)
          destruct (in_wins_dec PERMf (bv_unsigned x)) as [Hpf|Hnpf]; [apply HD'; [right; exact Hpf | exact HMx]|].
          rewrite (HF' x); [exact HMx|]. split; [|split; [exact Hnpf|]].
          * destruct Ho as [Hb|[Hp|Hst]]; [left; unfold HIDf; apply in_blocks_app; left; exact Hb | | lia].
            destruct (HP _ Hp) as [Hh|[Hc|Hsw]]; [left; unfold HIDf; apply in_blocks_app; right; exact Hh | lia |].
            destruct (swin_byte SWIN G SWIN_img _ Hsw) as [S1 S2]. right; right. split; [pose proof G_ro_img; lia | exact S2].
          * intros (lo & hi & Hin & _). cbn in Hin. destruct Hin.
        + apply HD'; [left; lia | exact HMx].
      - destruct (in_wins_dec PERMf (bv_unsigned x)) as [Hpf|Hnpf]; [apply HD'; [right; exact Hpf | exact HMx]|].
        rewrite (HF' x); [exact HMx|]. split; [right; left; exact Hge|]. split; [exact Hnpf|].
        intros (lo & hi & Hin & _). cbn in Hin. destruct Hin. }
    assert (HKout : know_ok SEGS E'' M' (map (kresplit k) (map (ktsubst th') (kn tout)))).
    { assert (HK'' : know_ok SEGS E'' M k) by (eapply know_ok_agree'; [exact Hag'' | exact Fkn | exact HK]).
      assert (X : know_ok SEGS E'' M' (map (ktsubst th') (kn tout))).
      { apply (proj2 (know_ok_ktsubst SEGS E'' th' M' (kn tout))). eapply know_ok_agree'; [exact Hagout | exact Hknout_v | exact (co_know HCo)]. }
      unfold know_ok in X |- *. apply Forall_forall. intros K HinK. apply in_map_iff in HinK as [K0 [<- Hin0]].
      eapply kentry_ok_kresplit; [exact HK''|]. exact (proj1 (Forall_forall _ _) X K0 Hin0). }
    assert (HRout : regs_ok E'' (map (tsubst th') (s_regs (a_ss tout))) R').
    { apply (proj2 (regs_ok_tsubst E'' th' (s_regs (a_ss tout)) R')). eapply regs_ok_agree'; [exact Hagout | exact Hsrout_v | exact (co_regs HCo)]. }
    assert (HBD1 : blocks_den E'' keepblocks = blocks_den E keepblocks).
    { eapply blocks_den_agree; [exact Hag''|]. unfold pairs_vars_lt. apply forallb_forall. intros x Hx.
      exact (proj1 (forallb_forall _ _) (pairs_vars_lt_app_l _ _ _ Fallow) x (remove_pairs_incl _ _ _ x Hrm Hx)). }
    assert (HBD2 : blocks_den E'' (map (ptsubst th') (a_vis tout)) = blocks_den E' (a_vis tout)).
    { rewrite blocks_den_ptsubst. eapply blocks_den_agree; [exact Hagout | exact Hvisout_v]. }
    assert (HBC1 : bcost E'' keepblocks = bcost E keepblocks).
    { eapply bcost_agree; [exact Hag''|]. unfold pairs_vars_lt. apply forallb_forall. intros x Hx.
      exact (proj1 (forallb_forall _ _) (pairs_vars_lt_app_l _ _ _ Fallow) x (remove_pairs_incl _ _ _ x Hrm Hx)). }
    assert (HBC2 : bcost E'' (map (ptsubst th') (a_vis tout)) = bcost E' (a_vis tout)).
    { rewrite bcost_ptsubst. eapply bcost_agree; [exact Hagout | exact Hvisout_v]. }
    (* [comment removed for export] *)
    assert (ZONE : forall b off n,
      0 <= estart E (SA b off) -> estart E (SA b off) < 2 ^ 64 ->
      forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E n ->
      ((existsb (fun bl => let '(lb, lk) := split_lit (fst bl) in xinside k b off n lb lk (snd bl)) keepblocks
        || above_sp k sp b off n
        || img_lit_x G k b off n)
       && forallb (fun w => let '(wb, wk) := split_lit (fst w) in ranges_apart_x k b off n wb wk (snd w)) ws)%bool = true ->
      zone (nil_of SWIN) G PERMf TOPf HIDf x).
    { intros b off n E1 E2 x Hx Hb. apply andb_prop in Hb as [HA0 HB].
      pose proof (u64_range (edenot E n)) as Hnr. unfold elenZ in Hx.
      (* [comment removed for export] *)
      assert (NP : ~ in_wins PERMf (bv_unsigned x)).
      { intros Hp. rewrite <- HPERMf in Hp. destruct Hp as (lo & hi & Hin & Hr).
        unfold wins_den in Hin. apply in_map_iff in Hin as [[wb0 wn] [Heq Hin]]. cbn [fst snd] in Heq. injection Heq as <- <-.
        pose proof (proj1 (forallb_forall _ _) HB _ Hin) as Hap. cbn [fst snd] in Hap.
        pose proof (proj1 (forallb_forall _ _) Hws _ Hin) as Hw. cbn [fst snd] in Hw.
        destruct (split_lit wb0) as [wb wk] eqn:Hwsp. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [_ Hwbf].
        destruct (bflat_x_sound SEGS E M k wb wk wn HK Hwbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B2, B3.
        pose proof (ranges_apart_x_sound SEGS E M k b off n wb wk wn HK Hap) as D. rewrite !estart_SA in D. unfold elenZ in D.
        rewrite estart_SA in Hx.
        assert (Hu : uE E wb0 = bv_unsigned (edenot E wb) + wk) by (unfold uE; rewrite (split_lit_denot E wb0 wb wk Hwsp); apply u64_lit; lia).
        rewrite Hu in Hr. unfold uE in Hr. lia. }
      assert (CASES : in_blocks (blocks_den E keepblocks) (bv_unsigned x)
                      \/ TOPf <= bv_unsigned x
                      \/ (g_ro_lo G <= bv_unsigned x < g_img_hi G /\ ~ in_wins (g_priv G) (bv_unsigned x))).
      { apply orb_prop in HA0 as [HA0|HA3]; [apply orb_prop in HA0 as [HA1|HA2]|].
        - apply existsb_exists in HA1 as [[lb0 ln] [Hin Hxi]]. cbn [fst snd] in Hxi.
          destruct (split_lit lb0) as [lb lk] eqn:Hls.
          pose proof (proj1 (forallb_forall _ _) Hkbflat (lb0, ln) ltac:(apply in_app_iff; left; exact Hin)) as Hlbf. cbn [fst snd] in Hlbf. rewrite Hls in Hlbf.
          destruct (bflat_x_sound SEGS E M k lb lk ln HK Hlbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B2, B3.
          destruct (xinside_sound SEGS E M k b off n lb lk ln HK Hxi) as [X1 X2]. rewrite !estart_SA in X1, X2. unfold elenZ in X2. rewrite estart_SA in Hx.
          left. eapply (in_blocks_den E keepblocks lb0 ln); [exact Hin|].
          assert (Hu : uE E lb0 = bv_unsigned (edenot E lb) + lk) by (unfold uE; rewrite (split_lit_denot E lb0 lb lk Hls); apply u64_lit; lia).
          rewrite Hu. unfold uE. lia.
        - right. left. unfold above_sp in HA2. rewrite Hssp in HA2.
          assert (XX : estart E (SA spb spk) <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= estart E (SA spb spk) + elenZ E (ELit two47)).
          { apply orb_prop in HA2 as [HA2|HA2]; [exact (xinside_sound SEGS E M k b off n spb spk (ELit two47) HK HA2)|].
            unfold xinside0 in HA2.
            lazymatch type of HA2 with (if ?c then _ else _) = _ => destruct c eqn:HB1; [|discriminate] end.
            pose proof (lin_ge0_sound SEGS E M k _ _ HK HB1) as LA. pose proof (lin_ge0_sound SEGS E M k _ _ HK HA2) as LB.
            cbn [xt_den] in LA, LB. unfold estart, elenZ. cbn [a_base a_off]. lia. }
          destruct XX as [X1 X2]. rewrite !estart_SA in X1. rewrite estart_SA in Hx.
          rewrite HTOPf, Hspv2. lia.
        - right. right. exact (img_lit_x_sound SEGS G E M k b off n x HK HA3 E1 E2 Hx). }
      split; [|split; [exact NP|]].
      - destruct CASES as [Hb|[Ht|Hro]]; [left; unfold HIDf; apply in_blocks_app; left; exact Hb | right; left; exact Ht | right; right; exact Hro].
      - intros (lo & hi & Hin & _). cbn in Hin. destruct Hin. }
    (* [comment removed for export] *)
    set (inws := fun (x : word) => existsb (fun p => Z.leb (fst p) (bv_unsigned x) && Z.ltb (bv_unsigned x) (snd p))%bool (wins_den E ws)).
    set (M1 := fun x : word => if inws x then M' x else M x).
    assert (HCUT : forall ws0, (forall w, In w ws0 -> In w ws) ->
              know_ok SEGS E (fun x : word => if existsb (fun p => Z.leb (fst p) (bv_unsigned x) && Z.ltb (bv_unsigned x) (snd p))%bool (wins_den E ws0)
                                              then M' x else M x) (kcut ws0 k)).
    { induction ws0 as [|w ws0 IH]; intros Hsub.
      - cbn [kcut wins_den map existsb]. exact HK.
      - cbn [kcut]. destruct w as [wb0 wn]. cbn [fst snd]. destruct (split_lit wb0) as [wb wk] eqn:Hwsp.
        pose proof (proj1 (forallb_forall _ _) Hws (wb0, wn) (Hsub _ (or_introl eq_refl))) as Hw. cbn [fst snd] in Hw. rewrite Hwsp in Hw.
        apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [_ Hwbf].
        destruct (bflat_x_sound SEGS E M k wb wk wn HK Hwbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B2, B3.
        assert (Hu : uE E wb0 = bv_unsigned (edenot E wb) + wk) by (unfold uE; rewrite (split_lit_denot E wb0 wb wk Hwsp); apply u64_lit; lia).
        eapply know_ok_cutout; [apply IH; intros w' Hw'; apply Hsub; right; exact Hw'|].
        intros x Hx. rewrite estart_SA in Hx. unfold elenZ in Hx. cbn [wins_den map existsb fst snd].
        rewrite Hu. unfold uE at 1 2.
        replace (Z.leb (bv_unsigned (edenot E wb) + wk) (bv_unsigned x) && Z.ltb (bv_unsigned x) (bv_unsigned (edenot E wb) + wk + bv_unsigned (edenot E wn)))%bool with false; [reflexivity|].
        symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
    assert (HK1 : know_ok SEGS E M1 (kcut ws k)) by (apply HCUT; intros w Hw; exact Hw).
    assert (HSTICKY : forall K, In K (List.filter (fun K => kentry_vars_lt v K && sticky_call k (keepblocks ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp K)%bool k) ->
                    kentry_ok SEGS E'' M' K).
    { intros K HinK. apply filter_In in HinK as [HinK Hkeep]. apply andb_prop in Hkeep as [HKv Hkeep].
      pose proof (proj1 (Forall_forall _ _) HK K HinK) as HKK.
      assert (DEF : forall b o n x, (owned_x k (keepblocks ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) b o n || above_x k (a_brk cs) sp b o n)%bool = true ->
                estart E (SA b o) <= bv_unsigned x < estart E (SA b o) + elenZ E n ->
                (M x <> None -> M' x <> None) /\ (~ (g_img_lo G <= bv_unsigned x < g_img_hi G) \/ M' x = M x)).
      { intros b o n x Hox0 Hx. apply orb_prop in Hox0 as [Hox|Habv].
        2:{ pose proof (above_x_sound SEGS SPTOPc E M k (a_brk cs) sp b o n x HK Habv (co_top HC) Hx) as [AB1 AB2].
            split; [intros HM; exact (STICK x (or_intror AB1) HM)|]. left. pose proof G_img_ceil. lia. }
        pose proof (owned_x_sound3 SEGS PERMc SPTOPc E M k keepblocks (a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) b o n x HK Hkbflat (co_perm HC) (co_top HC) (co_floor HC) Hox Hx) as Ho.
        split; [intros HM; exact (STICK x (or_introl Ho) HM)|].
        destruct Ho as [Hb|[Hp|Hst]]; [| | left; pose proof G_img_ceil; lia].
        - destruct Hb as (b' & m' & Hin' & Hbz').
          assert (HinL : In (b', m') (blocks_den E (a_vis cs))).
          { unfold blocks_den in Hin' |- *. apply in_map_iff in Hin' as [y [Hy Hiny]]. apply in_map_iff. exists y. split; [exact Hy|].
            eapply remove_pairs_incl; [exact Hrm | exact Hiny]. }
          pose proof (AINVH_zone _ _ _ _ _ b' m' HA ltac:(apply in_app_iff; left; exact HinL)) as (Z1 & Z2 & Z3). left. lia.
        - destruct (HP _ Hp) as [Hh|[Hc|Hsw]]; [| left; pose proof G_img_ceil; lia |].
          + destruct Hh as (b' & m' & Hin' & Hbz').
            pose proof (AINVH_zone _ _ _ _ _ b' m' HA ltac:(apply in_app_iff; right; exact Hin')) as (Z1 & Z2 & Z3). left. lia.
          + (* [comment removed for export] *)
            right. destruct (swin_byte SWIN G SWIN_img _ Hsw) as [S1 S2]. apply HF'.
            split; [right; right; split; [pose proof G_ro_img; lia | exact S2]|].
            split; [intros Hpf; exact (proj2 (HPERMown _ Hpf) ltac:(pose proof G_ro_img; lia)) | intros (lo & hi & Hin0 & _); cbn in Hin0; destruct Hin0]. }
      assert (AG0 : kentry_ok SEGS E M' K).
      { unfold sticky_call in Hkeep.
        destruct K as [[b o] w vv|[b o] nn|[b o] nn kb|ilo ihi|e m|e rlo rhi|[b o] nn|a1 n1 a2 n2|[b o] nn fc|[b o] nn]; try discriminate.
        - (* [comment removed for export] *) apply (proj1 (kwr_bytes SEGS E M b o nn)) in HKK as [Hfl HS]. apply (proj2 (kwr_bytes SEGS E M' b o nn)). split; [exact Hfl|].
          intros x Hx. destruct (DEF b o nn x Hkeep Hx) as [D1 [D2|Heq]].
          2:{ cbn [RiscvSemantics.store_ok]. unfold wview. rewrite Heq. exact (HS x Hx). }
          assert (HMx : M x <> None) by (eapply (store_ok_defined SEGS G SEGS_out); [exact D2 | apply HS; exact Hx]).
          pose proof (D1 HMx) as HM'. cbn [RiscvSemantics.store_ok]. unfold wview. destruct (M' x); [reflexivity | exfalso; apply HM'; reflexivity].
        - (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl HS]. split; [exact Hfl|]. intros i Hi.
          pose proof Hfl as (F1 & F2 & F3 & F4). set (x := Z_to_bv 64 (estart E (SA b o) + i)).
          assert (Hux : bv_unsigned x = estart E (SA b o) + i) by (unfold x; apply u64_lit; lia).
          destruct (DEF b o nn x Hkeep ltac:(rewrite Hux; lia)) as [D1 D2]. apply D1. apply HS. exact Hi. }
      assert (X : know_ok SEGS E'' M' [K]).
      { eapply know_ok_agree'; [exact Hag'' | | constructor; [exact AG0 | constructor]].
        cbn [AP.kn_vars_lt]. rewrite HKv. reflexivity. }
      exact (Forall_inv X). }
    assert (HKEPT : forall K, In K (List.filter (fun K => kentry_vars_lt v K && keep_fact_call G k keepblocks ws sp K)%bool (kcut ws k)) ->
                    kentry_ok SEGS E'' M' K).
    { intros K HinK. apply filter_In in HinK as [HinK Hkeep]. apply andb_prop in Hkeep as [HKv Hkeep].
      pose proof (proj1 (Forall_forall _ _) HK1 K HinK) as HKK.
      (* [comment removed for export] *)
      assert (AG0 : kentry_ok SEGS E M' K).
      { eapply kentry_ok_footprint; [exact HKK|]. intros x Hx.
        unfold M1. destruct (inws x) eqn:Hinws; [reflexivity|]. apply HF'. unfold in_kfoot, kfoot in Hx.
        unfold keep_fact_call in Hkeep.
        destruct K as [[b o] w vv|[b o] nn|[b o] nn kb|ilo ihi|e m|e rlo rhi|[b o] nn|a1 n1 a2 n2|[b o] nn fc|[b o] nn];
          cbn [kentry_range] in Hkeep; try (destruct Hx; fail); try discriminate Hkeep; cbn [kentry_ok] in HKK.
        4:{ (* [comment removed for export] *) apply andb_prop in Hkeep as [Hkeep Hdj]. apply andb_prop in Hkeep as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
            split; [right; right; split; [lia|]; eapply lit_disjoint_sound; [exact Hdj | lia]|]. split.
            - intros Hp. exact (proj2 (HPERMown _ Hp) ltac:(pose proof G_ro_img; lia)).
            - intros (lo & hi & Hin & _). cbn in Hin. destruct Hin. }
        1: destruct HKK as (Hw8 & Hfl & Hrd).
        all: try (destruct HKK as [Hfl HKrest]).
        all: destruct Hfl as (F1 & F2 & F3 & F4).
        1: { apply (ZONE b o (ELit (Z.of_nat w))); [lia | lia | | exact Hkeep]. rewrite APS.elenZ_lit by lia. exact Hx. }
        all: apply (ZONE b o nn); [lia | lia | exact Hx | exact Hkeep]. }
      (* [comment removed for export] *)
      assert (X : know_ok SEGS E'' M' [K]).
      { eapply know_ok_agree'; [exact Hag'' | | constructor; [exact AG0 | constructor]].
        cbn [AP.kn_vars_lt]. rewrite HKv. reflexivity. }
      exact (Forall_inv X). }
    apply (Hk E'' fx' R' M' mdl').
    + split; [eapply env_agree_le; [exact Hag'' | exact Fle] | exact Hag''].
    + constructor; cbn [a_ss s_regs s_log s_know kn a_vis a_totsz a_eager a_ghost a_brk mk_ss].
      * exact HRout.
      * reflexivity.
      * apply Forall_app. split; [exact HKout|]. apply Forall_app. split; apply Forall_forall; [exact HSTICKY | exact HKEPT].
      * exact (co_halt HCo).
      * exact (co_lazy HCo).
      * rewrite Hfs'. exact (co_fs HC).
      * rewrite (co_fds HCo). reflexivity.
      * (* [comment removed for export] *)
        split; [|split; [exact HP | split; [exact HTc|split]]].
        -- rewrite GlzNodesAlloc.blocks_den_app, HBD1, HBD2, GlzNodesAlloc.bcost_app, GlzNodesAlloc.bcount_app, HBC1, HBC2.
           replace (B0c + (bcost E keepblocks + bcost E' (a_vis tout))) with (B0f + bcost E' (a_vis tout)) by (unfold B0f; lia).
           replace (bcount (map (ptsubst th') (a_vis tout))) with (bcount (a_vis tout)) by (unfold bcount; rewrite length_map; reflexivity).
           replace (C0c + (bcount keepblocks + bcount (a_vis tout))) with (C0f + bcount (a_vis tout)) by (unfold C0f; lia).
           eapply AINVH_perm; [|exact HA']. unfold HIDf. rewrite app_assoc. apply Permutation.Permutation_app_tail. apply Permutation.Permutation_app_comm.
        -- intros a Hza. rewrite <- (HF a Hza). apply HF'.
           destruct Hza as (Hz1 & Hnp & Hnsw). split; [|split; [|intros (lo & hi & Hin & _); cbn in Hin; destruct Hin]].
           ++ destruct Hz1 as [Hh|[Ht|Hro]].
              ** left. unfold HIDf. apply in_blocks_app. right. exact Hh.
              ** right. left. rewrite HTOPf. lia.
              ** right. right. exact Hro.
           ++ intros Hp. destruct (HPERMown _ Hp) as [[Hb|[Hpc'|Hst]] _].
              ** destruct Hb as (b & m & Hin & Hbz).
                 assert (HinL : In (b, m) (blocks_den E (a_vis cs))).
                 { unfold blocks_den in Hin |- *. apply in_map_iff in Hin as [x [Hx Hinx]]. apply in_map_iff. exists x. split; [exact Hx|].
                   eapply remove_pairs_incl; [exact Hrm | exact Hinx]. }
                 pose proof (AINVH_zone _ _ _ _ _ b m HA ltac:(apply in_app_iff; left; exact HinL)) as (Z1 & Z2 & Z3).
                 destruct Hz1 as [Hh|[Ht|Hro]].
                 --- destruct Hh as (b' & m' & Hin' & Hbz'). destruct (in_split _ _ HinL) as (L1 & L2 & HL).
                     pose proof (AINVH_disj _ _ _ _ _ L1 (L2 ++ HIDc) b m b' m' HA
                                   ltac:(rewrite HL; rewrite <- app_assoc; reflexivity)
                                   ltac:(rewrite app_assoc; apply in_app_iff; right; exact Hin')). lia.
                 --- lia.
                 --- pose proof G_ro_img. lia.
              ** exact (Hnp Hpc').
              ** destruct Hz1 as [Hh|[Ht|Hro]].
                 --- destruct Hh as (b' & m' & Hin' & Hbz'). pose proof (AINVH_zone _ _ _ _ _ b' m' HA ltac:(apply in_app_iff; right; exact Hin')) as (Z1 & Z2 & Z3). lia.
                 --- lia.
                 --- pose proof G_ro_img. pose proof G_img_ceil. lia.
        -- (* [comment removed for export] *)
           intros a Hdz H0. apply STICK; [| exact (HD a Hdz H0)].
           left. destruct Hdz as [Hst|Hp]; [right; right; exact Hst | right; left; exact Hp].
      * eapply UINV_agree; [eapply env_agree_le; [exact Hag'' | exact Fle] | exact (co_uinv HC)].
      * exact (co_fx HCo).
      * rewrite (wins_den_agree v E E'' (a_ghost cs) Hag'' (pairs_vars_lt_app_r _ _ _ Fallow)). exact (co_perm HC).
      * rewrite (sptop_den_agree v E E'' (a_brk cs) Hag'' Fbrk). exact (co_top HC).
      * exact (co_mat HCo).
      * cbn [a_ylo a_maps a_brk]. eapply GPS.floor_sem_agree; [exact Hag'' | exact Fbrk | exact Fmaps | exact (co_floor HC)].
    + rewrite Hfs'. reflexivity.
Qed.

Theorem node_call_cond_sound : forall (Q : env -> Prop) (COND : acs -> list expr -> bool) ce args,
  callee_contract_when Q ce ->
  (forall cs th E fx R M model, bind ce args cs = Some th -> COND cs th = true -> cs_ok E cs fx R M model -> Q (tenv E th)) ->
  GPS.node1_stmtN SEGS nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ always (node_call_cond COND ce args).
Proof.
  intros Q COND ce args CC HQ cs cs' E fx R M model T HT HC _ Hn Hk.
  unfold node_call_cond in Hn. destruct (bind ce args cs) as [th0|] eqn:Hbind0; [|discriminate].
  destruct (COND cs th0) eqn:Hcond; [|discriminate].
  pose proof (HQ cs th0 E fx R M model Hbind0 Hcond HC) as HQE.
  destruct (node_call_split ce args cs cs' E fx R M model HC Hn) as (th & kb & Hbind & Hrm & HCf & HB0 & HC0 & HBc & HCc & Hpc & EXIT).
  rewrite Hbind0 in Hbind. injection Hbind as ->.
  unfold cfgF. rewrite Hpc.
  apply (CC _ _ _ M _ _ FS0 FDS0 (tenv E th) fx R M model T HB0 HC0 HBc HCc HQE HCf HT).
  exact (EXIT T HT Hk).
Qed.

(* [comment removed for export] *)
Theorem node_call_sound : forall ce args,
  callee_contract ce -> GPS.node1_stmtN SEGS nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ always (node_call SEGS A nx0 bcap ccap G ce args).
Proof.
  intros ce args CC cs cs' E fx R M model T HT HC Hp Hn Hk.
  apply (node_call_cond_sound QTRUE (fun _ _ => true) ce args CC ltac:(intros; exact I) cs cs' E fx R M model T HT HC Hp); [|exact Hk].
  unfold node_call_cond. unfold node_call in Hn |- *.
  destruct (ce_touts ce); [discriminate|].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c; [|discriminate] end. cbn [negb] in Hn |- *.
  destruct (bind ce args cs); [exact Hn | discriminate].
Qed.

(* [comment removed for export] *)
Theorem node_call2_cond_sound : forall (Q : env -> Prop) (COND : acs -> list expr -> bool) c args,
  callee_contract_when Q (c2_merged c) ->
  (forall cs th E fx R M model, bind (c2_class0 c) args cs = Some th -> COND cs th = true -> cs_ok E cs fx R M model -> Q (tenv E th)) ->
  node2_stmt SEGS nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ (node_call2_cond SEGS A nx0 bcap ccap G COND c args).
Proof.
  intros Q COND c args CC HQ cs csa csb E fx R M model T HC Hn HT KA KB.
  unfold node_call2_cond in Hn. destruct (bind (c2_class0 c) args cs) as [th0|] eqn:Hbind0; [|discriminate].
  destruct (COND cs th0) eqn:Hcond; [|discriminate].
  pose proof (HQ cs th0 E fx R M model Hbind0 Hcond HC) as HQE.
  rewrite node_call2_eq in Hn.
  destruct (node_call SEGS A nx0 bcap ccap G (c2_class0 c) args cs) as [a|] eqn:Hna; [|discriminate].
  destruct (node_call SEGS A nx0 bcap ccap G (c2_class1 c) args cs) as [b|] eqn:Hnb; [|discriminate].
  injection Hn as Ea Eb. subst a b.
  destruct (node_call_split (c2_class0 c) args cs csa E fx R M model HC Hna) as (th & kb & Hbind & Hrm & HCf & HB0 & HC0 & HBc & HCc & Hpc & EXIT0).
  destruct (node_call_split (c2_class1 c) args cs csb E fx R M model HC Hnb) as (th1 & kb1 & Hbind1 & Hrm1 & _ & _ & _ & _ & _ & _ & EXIT1).
  rewrite Hbind0 in Hbind. injection Hbind as Eth0. subst th0.
  cbn [c2_class0 c2_class1 c2_merged ce_nxf ce_tin ce_touts ce_bcap ce_ccap] in *.
  assert (Eth : th1 = th) by (unfold bind in Hbind0, Hbind1; cbn [ce_nxf ce_tin c2_class0 c2_class1] in Hbind0, Hbind1; rewrite Hbind0 in Hbind1; injection Hbind1 as E1; symmetry; exact E1).
  subst th1. rewrite Hrm in Hrm1. injection Hrm1 as <-.
  unfold cfgF. rewrite Hpc.
  apply (CC _ _ _ M _ _ FS0 FDS0 (tenv E th) fx R M model T HB0 HC0 HBc HCc HQE HCf HT).
  intros tout E' fx' R' M' mdl' Hin Hag HCo Hfs. cbn [ce_touts] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exact (EXIT0 T HT KA tout E' fx' R' M' mdl' Hin Hag HCo Hfs).
  - exact (EXIT1 T HT KB tout E' fx' R' M' mdl' Hin Hag HCo Hfs).
Qed.

Theorem node_call2_sound : forall c args,
  callee_contract (c2_merged c) ->
  node2_stmt SEGS nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ (node_call2 SEGS A nx0 bcap ccap G c args).
Proof.
  intros c args CC cs csa csb E fx R M model T HC Hn HT KA KB.
  rewrite node_call2_eq in Hn.
  destruct (node_call SEGS A nx0 bcap ccap G (c2_class0 c) args cs) as [a|] eqn:Hna; [|discriminate].
  destruct (node_call SEGS A nx0 bcap ccap G (c2_class1 c) args cs) as [b|] eqn:Hnb; [|discriminate].
  injection Hn as Ea Eb. subst a b.
  destruct (node_call_split (c2_class0 c) args cs csa E fx R M model HC Hna) as (th & kb & Hbind & Hrm & HCf & HB0 & HC0 & HBc & HCc & Hpc & EXIT0).
  destruct (node_call_split (c2_class1 c) args cs csb E fx R M model HC Hnb) as (th1 & kb1 & Hbind1 & Hrm1 & _ & _ & _ & _ & _ & _ & EXIT1).
  cbn [c2_class0 c2_class1 c2_merged ce_nxf ce_tin ce_touts ce_bcap ce_ccap] in *.
  assert (Eth : th1 = th) by (unfold bind in Hbind, Hbind1; cbn [ce_nxf ce_tin c2_class0 c2_class1] in Hbind, Hbind1; rewrite Hbind in Hbind1; injection Hbind1 as E1; symmetry; exact E1).
  subst th1. rewrite Hrm in Hrm1. injection Hrm1 as <-.
  unfold cfgF. rewrite Hpc.
  apply (CC _ _ _ M _ _ FS0 FDS0 (tenv E th) fx R M model T HB0 HC0 HBc HCc I HCf HT).
  intros tout E' fx' R' M' mdl' Hin Hag HCo Hfs. cbn [ce_touts] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exact (EXIT0 T HT KA tout E' fx' R' M' mdl' Hin Hag HCo Hfs).
  - exact (EXIT1 T HT KB tout E' fx' R' M' mdl' Hin Hag HCo Hfs).
Qed.

End CallSound.

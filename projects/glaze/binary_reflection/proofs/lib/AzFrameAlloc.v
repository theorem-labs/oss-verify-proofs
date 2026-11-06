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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesLibc2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesLibc2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require PuLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= PuLia.lia_nd.
#[local] Ltac nia ::= PuLia.znia_nd.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation u := bv_unsigned.

Section FrameAlloc.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
Variable SHC : list (Z * Z).
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
(* [comment removed for export] *)
Variable AINVHN : Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops SWIN G SHC AINVH.
(* [comment removed for export] *)
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.
Hypothesis G_priv : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Variable FPC : (word -> option byte) -> Z -> Z -> Prop.
(* [comment removed for export] *)
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HID : list (Z * Z).
Variable HIDF : list (Z * Z).
Variable M0 : word -> option byte.
Variable B0 C0 : Z.
Hypothesis B0_nonneg : 0 <= B0.
Hypothesis C0_nonneg : 0 <= C0.
(* [comment removed for export] *)
Variable bcap ccap : Z.
Hypothesis bcap_ok : B0 + bcap <= GBUDGET.
Hypothesis ccap_ok : C0 + ccap <= GCOUNT.
(* [comment removed for export] *)
Variable FTOPc : Z.
Hypothesis FTOPc_ok : Z.of_nat (length HIDF) + FTOPc <= FMIN.

#[local] Notation AINVf := (AINV_f SWIN G AINVH PERMc SPTOPc HID HIDF M0 B0 C0).
#[local] Notation zone := (AzFrame.zone SWIN G PERMc SPTOPc HID HIDF).
#[local] Notation dzone := (AzFrame.dzone G PERMc SPTOPc).   (* [comment removed for export] *)
#[local] Notation perm_owned := (AzFrame.perm_owned SWIN PERMc SPTOPc HID HIDF).
#[local] Notation nkept := (AzNSpec.nkept SWIN PERMc G).
#[local] Notation hchanged := (AzNSpec.hchanged G).
#[local] Notation scratch := AzNSpec.scratch.

(* [comment removed for export] *)
Definition AINV_fN (n : Z) : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop :=
  AINV_f SWIN G (AINVHN n) PERMc SPTOPc HID HIDF M0 B0 C0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma sub_vis : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall x, In x (Lc ++ Lf) -> In x ((Lc ++ HID) ++ (Lf ++ HIDF)).
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left|right]; apply in_app_iff; left; exact Hx. Qed.
Lemma sub_hid : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall x, In x (HID ++ HIDF) -> In x ((Lc ++ HID) ++ (Lf ++ HIDF)).
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left|right]; apply in_app_iff; right; exact Hx. Qed.

(* [comment removed for export] *)
Lemma obj_ablk : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall b m, In (b, m) ((Lc ++ HID) ++ (Lf ++ HIDF)) -> ablk_ok G b m.
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros b m Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (proj1 (ZB b m Hin)) | exact (proj1 (ZF b m Hin))]. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Lemma NUMS : SB = 0x7fff8000 /\ HEAPLO = 0x10007fff8000 /\ KHI = 0x10007fff8000 /\ SHMAPLO = 0x7fff7000 /\ two47 = 2 ^ 47 /\ PTRLO = 0x1010.
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma lshadow_band : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall z, in_lshadow ((Lc ++ HID) ++ (Lf ++ HIDF)) z ->
  SB <= z /\ z < SB + CEIL_run / 8 /\ z < KHI /\ (z < SB + g_img_lo G / 8 \/ SB + g_img_hi G / 8 <= z).
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros z (b & n & Hin & Hsh). exact (ablk_shadow G G_ro_img G_img_al G_img_shlo b n z (obj_ablk Lc Lf B C K M mdl HA HPo HT b n Hin) Hsh).
Qed.

(* [comment removed for export] *)
Lemma pshadow_cases : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall z, in_pshadow PERMc z ->
  in_lshadow (HID ++ HIDF) z \/ in_sshadow z \/ in_ishadow G z.
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros z (lo & hi & Hin & Hlt & [S1 S2]).
  (* [comment removed for export] *)
  pose proof (proj1 HT) as HT1.
  set (z1 := Z.max lo (8 * (z - SB))).
  assert (W1 : lo <= z1 < hi) by (subst z1; clear - Hlt S1 S2; lia).
  assert (G1 : z1 / 8 = z - SB) by (subst z1; clear - Hlt S1 S2; lia).
  pose proof (proj2 HPo z1 ltac:(exists lo, hi; split; [exact Hin | exact W1])) as H47.
  destruct (proj1 HPo z1 ltac:(exists lo, hi; split; [exact Hin | exact W1])) as [Hh|[Hf|[Hc|Hsw]]].
  - left. destruct Hh as (b & n & Hbin & Hbz). exists b, n. split; [apply in_app_iff; left; exact Hbin|]. unfold in_shadow. clear - Hbz G1 W1. lia.
  - left. apply in_blocks_fusable in Hf as (f & m & Hfin & Hfz). exists f, m. split; [apply in_app_iff; right; exact Hfin|].
    unfold in_shadow. clear - Hfz G1 W1. lia.
  - right; left. unfold in_sshadow. pose proof NUMS as NU. clear - NU H47 Hc HT1 G1. lia.
  - right; right. destruct (swin_byte SWIN G G_ro_img G_img_al SWIN_img z1 Hsw) as [[Q1 Q2] _]. unfold in_ishadow. pose proof G_ro_img as GR. clear - Q1 Q2 GR G1. lia.
Qed.

(* [comment removed for export] *)
Lemma scratch_not_nkept : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall sp stk a, SFLOOR + stk <= sp -> 0 <= stk ->
  scratch sp stk a -> nkept Lc Lf (scratch sp stk) a -> False.
Proof. pose proof sfloor_ge as SFG_.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros sp stk a Hsp Hstk Hs Hk.
  pose proof (band_lits G G_img_al) as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7).
  pose proof (G_img_ceil G G_img_al G_img_shlo) as GC. pose proof G_ro_img as (GR0 & GR1 & GR2).
  unfold AzNSpec.scratch in Hs.
  destruct Hk as [[_ [Hns _]]|[[Hi _]|[Hl|[Hss|[Hish|Hpsh]]]]].
  - exact (Hns Hs).
  - lia.
  - pose proof (lshadow_band Lc Lf B C K M mdl HA HPo HT (u a) (in_lshadow_mono _ _ _ (sub_vis Lc Lf B C K M mdl HA HPo HT) Hl)). lia.
  - destruct Hss. lia.
  - destruct (ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hish). lia.
  - destruct (pshadow_cases Lc Lf B C K M mdl HA HPo HT (u a) Hpsh) as [Hl|[Hs'|Hi']].
    + pose proof (lshadow_band Lc Lf B C K M mdl HA HPo HT (u a) (in_lshadow_mono _ _ _ (sub_hid Lc Lf B C K M mdl HA HPo HT) Hl)). lia.
    + destruct Hs'. lia.
    + destruct (ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hi'). lia.
Qed.

Lemma scratch_not_zone : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall sp stk a, SFLOOR + stk <= sp -> 0 <= stk -> sp <= SPTOPc ->
  scratch sp stk a -> zone a -> False.
Proof. pose proof sfloor_ge as SFG_.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros sp stk a Hsp Hstk Htop Hs (Hz & Hnp & Hnsw).
  pose proof (band_lits G G_img_al) as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7).
  pose proof (G_img_ceil G G_img_al G_img_shlo) as GC. pose proof G_ro_img as (GR0 & GR1 & GR2).
  unfold AzNSpec.scratch in Hs.
  destruct Hz as [Hh|[Hhf|[Ht|[Him|[Hlsh|[Hssh|[Hish|Hflo]]]]]]].
  - destruct Hh as (b & n & Hin & Hbz). pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo b n (u a) (proj1 (ZB b n ltac:(apply in_app_iff; right; exact Hin))) Hbz). lia.
  - destruct Hhf as (f & m & Hin & Hbz). pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo f m (u a) (proj1 (ZF f m ltac:(apply in_app_iff; right; exact Hin))) Hbz). lia.
  - lia.
  - lia.
  - pose proof (lshadow_band Lc Lf B C K M mdl HA HPo HT (u a) (in_lshadow_mono _ _ _ (sub_hid Lc Lf B C K M mdl HA HPo HT) Hlsh)). lia.
  - destruct Hssh. lia.
  - destruct (ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hish). lia.
  - (* [comment removed for export] *) lia.
Qed.

(* [comment removed for export] *)
Lemma perm_cases : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall z, in_wins PERMc z ->
  in_blocks (Lc ++ HID) z \/ in_blocks (Lf ++ HIDF) z \/ SPTOPc <= z \/ in_wins SWIN z.
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros z Hp. destruct (proj1 HPo z Hp) as [Hh|[Hf|[Hc|Hsw]]].
  - left. destruct Hh as (b & n & Hin & Hz). exists b, n. split; [apply in_app_iff; right; exact Hin | exact Hz].
  - right; left. apply in_blocks_fusable in Hf as (f & m & Hin & Hz). exists f, m. split; [apply in_app_iff; right; exact Hin | lia].
  - right; right; left. exact Hc.
  - right; right; right. exact Hsw.
Qed.

(* [comment removed for export] *)
Definition rtpriv (Lc Lf : list (Z * Z)) (a : word) : Prop :=
  u a < CEIL_run /\ ~ (g_img_lo G <= u a < g_img_hi G) /\ ~ nvisible G (Lc ++ HID) (Lf ++ HIDF) (u a).

Lemma rtpriv_not_nkept : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall P a, rtpriv Lc Lf a -> nkept Lc Lf P a -> False.
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros P a (Hr & Hni & Hnv) Hk. pose proof HT as [HT1 HT2]. pose proof G_ro_img as (GR0 & GR1 & GR2).
  unfold nvisible in Hnv.
  destruct Hk as [[Ho _]|[[Hi _]|[Hl|[Hss|[Hish|Hpsh]]]]].
  - destruct Ho as [Hb|[Hf|[Hp|[Hs|Hw]]]].
    + apply Hnv. left. apply in_blocks_app. left. exact Hb.
    + apply Hnv. right; left. apply in_blocks_app. left. exact Hf.
    + destruct (perm_cases Lc Lf B C K M mdl HA HPo HT _ Hp) as [Q|[Q|[Q|Q]]].
      * apply Hnv. left. exact Q.
      * apply Hnv. right; left. exact Q.
      * lia.
      * destruct (swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Q) as [[Q1 Q2] _]. lia.
    + lia.
    + destruct (swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Hw) as [[Q1 Q2] _]. lia.
  - lia.
  - apply Hnv. right; right; left. eapply in_lshadow_mono; [exact (sub_vis Lc Lf B C K M mdl HA HPo HT) | exact Hl].
  - apply Hnv. right; right; right; left. exact Hss.
  - apply Hnv. right; right; right; right. exact Hish.
  - destruct (pshadow_cases Lc Lf B C K M mdl HA HPo HT (u a) Hpsh) as [Hl|[Hs|Hi]].
    + apply Hnv. right; right; left. eapply in_lshadow_mono; [exact (sub_hid Lc Lf B C K M mdl HA HPo HT) | exact Hl].
    + apply Hnv. right; right; right; left. exact Hs.
    + apply Hnv. right; right; right; right. exact Hi.
Qed.

Lemma rtpriv_not_zone : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall a, rtpriv Lc Lf a -> zone a -> False.
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros a (Hr & Hni & Hnv) (Hz & Hnp & Hnsw). pose proof HT as [HT1 HT2]. unfold nvisible in Hnv.
  destruct Hz as [Hh|[Hhf|[Ht|[Him|[Hlsh|[Hssh|[Hish|Hflo]]]]]]].
  - apply Hnv. left. apply in_blocks_app. right. exact Hh.
  - apply Hnv. right; left. apply in_blocks_app. right. exact Hhf.
  - lia.
  - pose proof G_ro_img. lia.
  - apply Hnv. right; right; left. eapply in_lshadow_mono; [exact (sub_hid Lc Lf B C K M mdl HA HPo HT) | exact Hlsh].
  - apply Hnv. right; right; right; left. exact Hssh.
  - apply Hnv. right; right; right; right. exact Hish.
  - (* [comment removed for export] *) lia.
Qed.

Lemma rtpriv_not_dzone : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall a, rtpriv Lc Lf a -> dzone a -> False.
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros a (Hr & Hni & Hnv) [Hs|[Hp|Hew]]; [lia| |unfold errw in Hew; pose proof (hp_errno _ _ _ _ HP); pose proof G_ro_img; lia].   (* [comment removed for export] *)
  pose proof HT as [HT1 HT2]. unfold nvisible in Hnv.
  destruct (perm_cases Lc Lf B C K M mdl HA HPo HT _ Hp) as [Q|[Q|[Q|Q]]].
  - apply Hnv. left. exact Q.
  - apply Hnv. right; left. exact Q.
  - lia.
  - destruct (swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Q) as [[Q1 Q2] _]. pose proof G_ro_img. lia.
Qed.

(* [comment removed for export] *)
Lemma priv_img : forall z, in_wins (g_priv G) z -> g_ro_hi G <= z < g_img_hi G.
Proof. intros z (lo & hi & Hin & Hz). destruct (G_priv lo hi Hin). lia. Qed.
(* [comment removed for export] *)
Lemma privx_img : forall z, in_wins (g_privx G) z -> g_ro_hi G <= z < g_img_hi G.
Proof. intros z (lo & hi & Hin & Hz). destruct (AzFrame.G_privx SWIN G SHC AINVH HP G_priv lo hi Hin). lia. Qed.
Lemma errno_not_nkept : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall P a, errw G (u a) -> nkept Lc Lf P a -> False.
Proof.
  intros Lc Lf B C K M mdl HA HPo HT P a He Hk.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  pose proof (hp_errno _ _ _ _ HP) as GE. pose proof G_ro_img as (GR0 & GR1 & GR2). pose proof HT as [HT1 HT2].
  pose proof (band_lits G G_img_al) as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7).
  pose proof (G_img_ceil G G_img_al G_img_shlo) as GC. pose proof G_img_shlo as GS. unfold errw in He.
  destruct Hk as [[_ [_ Hx]]|[[Hi Hnp]|[Hl|[Hss|[Hish|Hpsh]]]]].
  - destruct (Hx ltac:(unfold errw; lia)) as [Hb|[Hf|Hc]].
    + destruct Hb as (b & n & Hin & Hz). pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo b n (u a) (proj1 (ZB b n ltac:(apply in_app_iff; left; exact Hin))) Hz). lia.
    + destruct Hf as (f & m & Hin & Hz). pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo f m (u a) (proj1 (ZF f m ltac:(apply in_app_iff; left; exact Hin))) Hz). lia.
    + lia.
  - apply Hnp. apply AzKnowLib.in_wins_privx. left. unfold errw. lia.
  - pose proof (lshadow_band Lc Lf B C K M mdl HA HPo HT (u a) (in_lshadow_mono _ _ _ (sub_vis Lc Lf B C K M mdl HA HPo HT) Hl)). lia.
  - destruct Hss. lia.
  - destruct (ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hish). lia.
  - destruct (pshadow_cases Lc Lf B C K M mdl HA HPo HT (u a) Hpsh) as [Hl|[Hs'|Hi']].
    + pose proof (lshadow_band Lc Lf B C K M mdl HA HPo HT (u a) (in_lshadow_mono _ _ _ (sub_hid Lc Lf B C K M mdl HA HPo HT) Hl)). lia.
    + destruct Hs'. lia.
    + destruct (ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hi'). lia.
Qed.

Lemma priv_not_nkept : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall P a, in_wins (g_priv G) (u a) -> nkept Lc Lf P a -> False.
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros P a Hp Hk. pose proof (priv_img _ Hp) as [P1 P2]. pose proof HT as [HT1 HT2].
  pose proof (band_lits G G_img_al) as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7).
  pose proof (G_img_ceil G G_img_al G_img_shlo) as GC. pose proof G_ro_img as (GR0 & GR1 & GR2). pose proof G_img_shlo as GS.
  destruct Hk as [[Ho _]|[[Hi Hnp]|[Hl|[Hss|[Hish|Hpsh]]]]].
  - destruct Ho as [Hb|[Hf|[Hpp|[Hs|Hw]]]].
    + destruct Hb as (b & n & Hin & Hz). pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo b n (u a) (proj1 (ZB b n ltac:(apply in_app_iff; left; exact Hin))) Hz). lia.
    + destruct Hf as (f & m & Hin & Hz). pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo f m (u a) (proj1 (ZF f m ltac:(apply in_app_iff; left; exact Hin))) Hz). lia.
    + destruct (perm_cases Lc Lf B C K M mdl HA HPo HT _ Hpp) as [Q|[Q|[Q|Q]]].
      * destruct Q as (b & n & Hin & Hz). pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo b n (u a) (proj1 (ZB b n Hin)) Hz). lia.
      * destruct Q as (f & m & Hin & Hz). pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo f m (u a) (proj1 (ZF f m Hin)) Hz). lia.
      * lia.
      * exact (proj2 (swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Q) Hp).
    + lia.
    + exact (proj2 (swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Hw) Hp).
  - apply Hnp. apply AzKnowLib.in_wins_privx. right. exact Hp.   (* [comment removed for export] *)
  - pose proof (lshadow_band Lc Lf B C K M mdl HA HPo HT (u a) (in_lshadow_mono _ _ _ (sub_vis Lc Lf B C K M mdl HA HPo HT) Hl)). lia.
  - destruct Hss. lia.
  - destruct (ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hish). lia.
  - destruct (pshadow_cases Lc Lf B C K M mdl HA HPo HT (u a) Hpsh) as [Hl|[Hs'|Hi']].
    + pose proof (lshadow_band Lc Lf B C K M mdl HA HPo HT (u a) (in_lshadow_mono _ _ _ (sub_hid Lc Lf B C K M mdl HA HPo HT) Hl)). lia.
    + destruct Hs'. lia.
    + destruct (ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hi'). lia.
Qed.

Lemma priv_not_zone : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall a, in_wins (g_privx G) (u a) -> zone a -> False.   (* [comment removed for export] *)
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros a Hp (Hz & Hnpp & Hnsw). pose proof (privx_img _ Hp) as [P1 P2]. pose proof HT as [HT1 HT2].
  pose proof (band_lits G G_img_al) as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7).
  pose proof (G_img_ceil G G_img_al G_img_shlo) as GC. pose proof G_ro_img as (GR0 & GR1 & GR2). pose proof G_img_shlo as GS.
  destruct Hz as [Hh|[Hhf|[Ht|[[_ Him]|[Hlsh|[Hssh|[Hish|Hflo]]]]]]].
  - destruct Hh as (b & n & Hin & Hbz). pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo b n (u a) (proj1 (ZB b n ltac:(apply in_app_iff; right; exact Hin))) Hbz). lia.
  - destruct Hhf as (f & m & Hin & Hbz). pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo f m (u a) (proj1 (ZF f m ltac:(apply in_app_iff; right; exact Hin))) Hbz). lia.
  - lia.
  - exact (Him Hp).
  - pose proof (lshadow_band Lc Lf B C K M mdl HA HPo HT (u a) (in_lshadow_mono _ _ _ (sub_hid Lc Lf B C K M mdl HA HPo HT) Hlsh)). lia.
  - destruct Hssh. lia.
  - destruct (ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hish). lia.
  - (* [comment removed for export] *) lia.
Qed.

Lemma priv_not_dzone : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall a, in_wins (g_priv G) (u a) -> ~ errw G (u a) -> dzone a -> False.   (* [comment removed for export] *)
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros a Hp Hne [Hs|[Hpp|Hew]]; pose proof (priv_img _ Hp) as [P1 P2]; pose proof HT as [HT1 HT2];
    pose proof (G_img_ceil G G_img_al G_img_shlo) as GC; [lia| |exact (Hne Hew)].
  destruct (perm_cases Lc Lf B C K M mdl HA HPo HT _ Hpp) as [Q|[Q|[Q|Q]]].
  - destruct Q as (b & n & Hin & Hz). pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo b n (u a) (proj1 (ZB b n Hin)) Hz). lia.
  - destruct Q as (f & m & Hin & Hz). pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo f m (u a) (proj1 (ZF f m Hin)) Hz). lia.
  - lia.
  - exact (proj2 (swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Q) Hp).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma hchanged_not_nkept : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall sp stk a, SFLOOR + stk <= sp -> 0 <= stk ->
  hchanged stk (Lc ++ HID) (Lf ++ HIDF) sp a -> nkept Lc Lf (scratch sp stk) a -> False.
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros sp stk a Hsp Hstk [Hs|[Hr|Hp]] Hk.
  - exact (scratch_not_nkept Lc Lf B C K M mdl HA HPo HT sp stk a Hsp Hstk Hs Hk).
  - exact (rtpriv_not_nkept Lc Lf B C K M mdl HA HPo HT _ a Hr Hk).
  - apply AzKnowLib.in_wins_privx in Hp as [He|Hp].   (* [comment removed for export] *)
    + exact (errno_not_nkept Lc Lf B C K M mdl HA HPo HT _ a He Hk).
    + exact (priv_not_nkept Lc Lf B C K M mdl HA HPo HT _ a Hp Hk).
Qed.
Lemma hchanged_not_zone : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall sp stk a, SFLOOR + stk <= sp -> 0 <= stk -> sp <= SPTOPc ->
  hchanged stk (Lc ++ HID) (Lf ++ HIDF) sp a -> zone a -> False.
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros sp stk a Hsp Hstk Htop [Hs|[Hr|Hp]] Hz.
  - exact (scratch_not_zone Lc Lf B C K M mdl HA HPo HT sp stk a Hsp Hstk Htop Hs Hz).
  - exact (rtpriv_not_zone Lc Lf B C K M mdl HA HPo HT a Hr Hz).
  - exact (priv_not_zone Lc Lf B C K M mdl HA HPo HT a Hp Hz).
Qed.
Lemma hchanged_dzone_defined : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall sp stk a (M' M1 : word -> option byte), SFLOOR + stk <= sp -> 0 <= stk ->
  hchanged stk (Lc ++ HID) (Lf ++ HIDF) sp a -> scratch_ok SEGS M' sp stk -> errno_kept G M1 M' -> M1 a <> None -> dzone a -> M' a <> None.   (* [comment removed for export] *)
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros sp stk a M' M1 Hsp Hstk [Hs|[Hr|Hp]] Hscr Hek HMa Hd.
  - exact (proj1 (Hscr a Hs)).
  - exfalso. exact (rtpriv_not_dzone Lc Lf B C K M mdl HA HPo HT a Hr Hd).
  - destruct (errw_dec G (u a)) as [He|Hne]; [exact (Hek a He HMa)|].
    apply AzKnowLib.in_wins_privx in Hp as [He|Hp]; [exact (False_ind _ (Hne He))|].
    exfalso. exact (priv_not_dzone Lc Lf B C K M mdl HA HPo HT a Hp Hne Hd).
Qed.

(* [comment removed for export] *)
Lemma fresh_apart_perm : forall Lc Lf B C K M mdl (HA : AINVH (Lc ++ HID) (Lf ++ HIDF) B C K M mdl) (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0),
  forall p n, ablk_ok G p n ->
  (forall b m, In (b, m) ((Lc ++ HID) ++ (Lf ++ HIDF)) -> p + n <= b \/ b + m <= p) ->
  forall z, in_wins PERMc z -> ~ (p <= z < p + n).
Proof.
  intros Lc Lf B C K M mdl HA HPo HT.
  pose proof (fun b m (Hin : In (b, m) (Lc ++ HID)) => hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b m HA Hin) as ZB.
  pose proof (fun f m (Hin : In (f, m) (Lf ++ HIDF)) => hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA Hin) as ZF.
  intros p n Hblk Hdisj z Hz Hzin. pose proof HT as [HT1 HT2]. destruct Hblk as (A1 & A2 & A3 & A4).
  destruct (perm_cases Lc Lf B C K M mdl HA HPo HT _ Hz) as [Q|[Q|[Q|Q]]].
  - destruct Q as (b & m & Hin & Hbz). destruct (Hdisj b m ltac:(apply in_app_iff; left; exact Hin)); lia.
  - destruct Q as (f & m & Hin & Hbz). destruct (Hdisj f m ltac:(apply in_app_iff; right; exact Hin)); lia.
  - lia.
  - destruct (swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Q) as [[Q1 Q2] _]. pose proof G_ro_img. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Notation cfg := (fun fx R p M mdl => mkCfg (mkstF fx R (Z_to_bv 64 p) M (seg_rom SEGS)) mdl).

(* [comment removed for export] *)
Definition FRESHf (FRESHA : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop)
           (Lc Lf : list (Z * Z)) (B C K : Z) (M : word -> option byte) (mdl : Model) (n : Z) : Prop :=
  FRESHA (Lc ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K M mdl n.

(* [comment removed for export] *)
Lemma nmalloc_pre_h : forall fpcreq fx R M mdl Lc Lf B C K ret n sp stk,
  nmalloc_pre SEGS SPTOPc G AINVf FXOK FPC bcap ccap fpcreq fx R M mdl Lc Lf B C K ret n sp stk ->
  hmalloc_pre SEGS G FXOK AINVH FPC fpcreq fx R M mdl (Lc ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K ret n sp stk.
Proof.
  intros fpcreq fx R M mdl Lc Lf B C K ret n sp stk (Hh & HFX & HAf & Hpre & Hn & Hnr & Hfpc & HB & HCc & HK).
  pose proof HAf as (HA & HPo & HT & HF & HD).
  destruct Hpre as (R1 & Rr & Re & R2 & Hal & Hsplo & Hsptop & Hsphi & R4 & Hstk').
  pose proof (GPS.sfloor_stk _ _ Hsplo) as HsploC.   (* [comment removed for export] *)
  pose proof G_ro_img as GRI_.                        (* [comment removed for export] *)
  split; [exact HFX|]. split; [exact Hh|]. split; [exact HA|].
  split; [repeat (split; [assumption|]); exact Hstk'|].
  split; [exact Hn|]. split; [exact Hnr|]. split; [exact Hfpc|]. unfold mcost in *. lia.
Qed.

Lemma nmalloc_post_ok_f : forall R M mdl Lc Lf B C K n sp stk fx' R' M' mdl' p,
  0 <= stk -> AINVf Lc Lf B C K M mdl -> ncall_pre SEGS SPTOPc G R M 0 sp stk \/ (SFLOOR + stk <= sp /\ sp <= SPTOPc) ->
  hmalloc_post_ok SEGS G FXOK AINVH R M mdl (Lc ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K n sp stk fx' R' M' mdl' p ->
  nmalloc_post_ok SEGS SWIN PERMc G AINVf FXOK R M mdl Lc Lf B C K n sp stk fx' R' M' mdl' p.
Proof.
  intros R M mdl Lc Lf B C K n sp stk fx' R' M' mdl' p Hstk HAf Hsp H.
  assert (Hsplo : SFLOOR + stk <= sp /\ sp <= SPTOPc).
  { destruct Hsp as [Hpre|Hsp]; [|exact Hsp]. destruct Hpre as (_ & _ & _ & _ & _ & X1 & X2 & _). split; assumption. }
  destruct Hsplo as [Hsplo Hsptop].
  pose proof HAf as (HA & HPo & HT & HF & HD).
  destruct H as (HFX' & Hkept & Ha0 & Hpal & Hblk & Hal2k & Hdisj & Hdef & Hshk & Hshw & Hch & Hek & Hscr & HA' & Hnm).   (* [comment removed for export] *)
  split; [exact HFX'|]. split; [exact Hkept|]. split; [exact Ha0|]. split; [exact Hpal|]. split; [exact Hblk|]. split; [exact Hal2k|].
  split; [intros b m Hin; apply Hdisj; apply (sub_vis Lc Lf _ _ _ _ _ HA HPo HT); exact Hin|].
  split; [exact (fresh_apart_perm Lc Lf _ _ _ _ _ HA HPo HT (u p) n Hblk Hdisj)|].
  split; [exact Hdef|]. split; [exact Hshk|]. split; [exact Hshw|].
  split.
  { intros a Hk. destruct (decide (M' a = M a)) as [Heq|Hne]; [exact Heq|]. exfalso.
    exact (hchanged_not_nkept Lc Lf _ _ _ _ _ HA HPo HT sp stk a Hsplo Hstk (Hch a Hne) Hk). }
  split; [exact Hek|].   (* [comment removed for export] *)
  split; [exact Hscr|].
  split; [|exact Hnm].
  split; [|split; [exact HPo | split; [exact HT | split]]].
  - cbn [app]. replace (B0 + (B + mcost n)) with (B0 + B + mcost n) by lia. replace (C0 + (C + MCNT)) with (C0 + C + MCNT) by lia. exact HA'.
  - intros a Hz. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HF a Hz)|]. exfalso.
    exact (hchanged_not_zone Lc Lf _ _ _ _ _ HA HPo HT sp stk a Hsplo Hstk Hsptop (Hch a Hne) Hz).
  - intros a Hdz H0. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HD a Hdz H0)|].
    exact (hchanged_dzone_defined Lc Lf _ _ _ _ _ HA HPo HT sp stk a M' _ Hsplo Hstk (Hch a Hne) Hscr Hek (HD a Hdz H0) Hdz).   (* [comment removed for export] *)
Qed.



(* [comment removed for export] *)
Theorem malloc1_nspec_f : forall FRESHA stk entry,
  0 <= stk ->
  h_malloc1_at SEGS G FXOK RZ AINVH FPC FRESHA stk entry ->
  malloc_nspec1 SEGS SWIN PERMc SPTOPc G AINVf FXOK RZ FPC bcap ccap (FRESHf FRESHA) stk entry.
Proof.
  intros FRESHA stk entry Hstk HM fx R M mdl Lc Lf B C K ret n sp Tok Hpre Hfresh HTok Hok.
  pose proof Hpre as (Hh & HFX & HAf & Hcall & _).
  assert (Hsp : SFLOOR + stk <= sp /\ sp <= SPTOPc) by (destruct Hcall as (_ & _ & _ & _ & _ & X1 & X2 & _); split; assumption).
  apply (HM fx R M mdl (Lc ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K ret n sp Tok (nmalloc_pre_h _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre) Hfresh HTok).
  intros fx' R' M' mdl' p Hpost. apply (Hok fx' R' M' mdl' p). eapply nmalloc_post_ok_f; [exact Hstk | exact HAf | right; exact Hsp | exact Hpost].
Qed.


(* [comment removed for export] *)
Theorem alloc1_nspec_f : forall XTRA stk entry,
  0 <= stk ->
  h_alloc1_at SEGS G FXOK RZ AINVH FPC XTRA stk entry ->
  alloc1_nspec SEGS SWIN PERMc SPTOPc FTOPc G AINVf FXOK RZ FPC bcap ccap XTRA stk entry.
Proof.
  intros XTRA stk entry Hstk HM fx R M mdl Lc Lf B C K ret n sp T Hpre HX HFDS HLF HT0 Hok.
  pose proof Hpre as (Hh & HFX & HAf & Hcall & _).
  assert (Hsp : SFLOOR + stk <= sp /\ sp <= SPTOPc) by (destruct Hcall as (_ & _ & _ & _ & _ & X1 & X2 & _); split; assumption).
  assert (HLF' : Z.of_nat (length (Lf ++ HIDF)) + 1 <= FMIN) by (rewrite length_app; pose proof FTOPc_ok; lia).   (* [comment removed for export] *)
  apply (HM fx R M mdl (Lc ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K ret n sp T (nmalloc_pre_h _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre) HX HFDS HLF' HT0).
  intros fx' R' M' mdl' p Hpost. apply (Hok fx' R' M' mdl' p). eapply nmalloc_post_ok_f; [exact Hstk | exact HAf | right; exact Hsp | exact Hpost].
Qed.

(* [comment removed for export] *)
Theorem free_nspec_f : forall stk entry,
  0 <= stk ->
  h_free_at SEGS G FXOK RZ AINVH FPC stk entry ->
  free_nspec SEGS SWIN PERMc SPTOPc G AINVf FXOK RZ FPC stk entry.
Proof.
  intros stk entry Hstk HFr fx R M mdl Lc Lc' Lf B C K B' C' K' ret sp p T Hh HFX HAf Hpre Hp Hfpc CASES Hpost.
  pose proof HAf as (HA & HPo & HT & HF & HD).
  destruct Hpre as (R1 & Rr & Re & R2 & Hal & Hsplo & Hsptop & Hsphi & R4 & Hstk').
  (* [comment removed for export] *)
  assert (CASES' : exists Bq Cq,
    ((p = Z_to_bv 64 0 /\ Lc' ++ HID = Lc ++ HID /\ Bq = B0 + B /\ Cq = C0 + C /\ K' = K)
     \/ (exists m L1 L2, Lc ++ HID = L1 ++ (u p, m) :: L2 /\ Lc' ++ HID = L1 ++ L2
                          /\ Bq = Z.max 0 (B0 + B - mcost m) /\ Cq = Z.max 0 (C0 + C - MCNT) /\ K' = K + KFREE /\ K' <= GKCAP))
    /\ Bq <= B0 + B' /\ Cq <= C0 + C' /\ (forall x, In x Lc' -> In x Lc)).
  { destruct CASES as [(H0 & -> & -> & -> & ->)|(m & L1 & L2 & HL & -> & HB' & HC' & -> & HKc)].
    - exists (B0 + B), (C0 + C). split; [left; repeat split; try assumption; reflexivity|]. split; [lia|]. split; [lia|]. intros x Hx; exact Hx.
    - exists (Z.max 0 (B0 + B - mcost m)), (Z.max 0 (C0 + C - MCNT)). split.
      + right. exists m, L1, (L2 ++ HID). rewrite HL. rewrite <- !app_assoc. cbn [app]. repeat split; try reflexivity. exact HKc.
      + split; [lia|]. split; [lia|]. intros x Hx. rewrite HL. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx]. }
  destruct CASES' as (Bq & Cq & HCASE & HBq & HCq & Hsub).
  apply (HFr fx R M mdl (Lc ++ HID) (Lc' ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K Bq Cq K' ret sp p T HFX Hh HA).
  - unfold hcall_pre. split; [exact R1|]. split; [exact Rr|]. split; [exact Re|]. split; [exact R2|]. split; [exact Hal|].
    split; [exact (GPS.sfloor_stk _ _ Hsplo)|]. split; [exact Hsphi|]. split; [exact R4|]. exact Hstk'.
  - exact Hp.
  - exact Hfpc.
  - exact HCASE.
  - intros fx' R' M' mdl' HFX' Hkept Hch Hek Hscr HA' Hnm.   (* [comment removed for export] *)
    apply (Hpost fx' R' M' mdl' HFX' Hkept).
    + intros a Hk. destruct (decide (M' a = M a)) as [Heq|Hne]; [exact Heq|]. exfalso.
      exact (hchanged_not_nkept Lc' Lf _ _ _ _ _ HA' HPo HT sp stk a Hsplo Hstk (Hch a Hne) Hk).
    + exact Hek.
    + exact Hscr.
    + split; [|split; [exact HPo | split; [exact HT | split]]].
      * eapply (hp_mono _ _ _ _ HP); [exact HA' | exact HBq | exact HCq | lia].
      * intros a Hz. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HF a Hz)|]. exfalso.
        exact (hchanged_not_zone Lc' Lf _ _ _ _ _ HA' HPo HT sp stk a Hsplo Hstk Hsptop (Hch a Hne) Hz).
      * intros a Hdz H0. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HD a Hdz H0)|].
        exact (hchanged_dzone_defined Lc' Lf _ _ _ _ _ HA' HPo HT sp stk a M' _ Hsplo Hstk (Hch a Hne) Hscr Hek (HD a Hdz H0) Hdz).   (* [comment removed for export] *)
    + exact Hnm.
Qed.


(* [comment removed for export] *)
Lemma hfcount_le_length : forall n LF, hfcount n LF <= Z.of_nat (length LF).
Proof. intros n LF. induction LF as [|f r IH]; cbn [hfcount length]; [lia|]. destruct (Z.eqb (snd f) n); lia. Qed.

Lemma hfcount_app : forall n L1 L2, hfcount n (L1 ++ L2) = hfcount n L1 + hfcount n L2.
Proof. intros n L1 L2. induction L1 as [|f r IH]; cbn [hfcount app]; [lia|]. rewrite IH. lia. Qed.
Lemma FTOPc_small : FTOPc <= 2 ^ 62.
Proof. unfold FMIN in FTOPc_ok. lia. Qed.

(* [comment removed for export] *)
Theorem stkmal_nspec_f : forall k,
  h_stkmal SEGS G FXOK RZ AINVH k ->
  stkmal_nspec SEGS SWIN PERMc SPTOPc FTOPc G AINVf FXOK RZ k.
Proof.
  intros k HS. unfold stkmal_nspec. intros fx R M mdl Lc Lf B C K ret sp T Hk Hh HFX HAf Hpre Hcnt Hpost.
  pose proof HAf as (HA & HPo & HT & HF & HD).
  destruct Hpre as (R1 & Rr & Re & R2 & Hal & Hsplo & Hsptop & Hsphi & R4 & Hstk').
  assert (Hstk : 0 <= MSTK_F) by (unfold MSTK_F; lia).
  apply (HS fx R M mdl (Lc ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K ret sp T Hk HFX Hh HA).
  - unfold hcall_pre. split; [exact R1|]. split; [exact Rr|]. split; [exact Re|]. split; [exact R2|]. split; [exact Hal|].
    split; [exact (GPS.sfloor_stk _ _ Hsplo)|]. split; [exact Hsphi|]. split; [exact R4|]. exact Hstk'.
  - rewrite hfcount_app. pose proof (hfcount_le_length (64 * 2 ^ k) Lf). pose proof (hfcount_le_length (64 * 2 ^ k) HIDF). lia.
  - intros fx' R' M' mdl' f flag HFX' Hkept Ha0 Hfal Hblk Hdisj Hdef Hlast Hsh0 Hshw Hch Hek Hscr HA' Hnm.   (* [comment removed for export] *)
    apply (Hpost fx' R' M' mdl' f flag HFX' Hkept Ha0 Hfal Hblk).
    + intros b m Hin. apply Hdisj. apply (sub_vis Lc Lf _ _ _ _ _ HA HPo HT). exact Hin.
    + exact (fresh_apart_perm Lc Lf _ _ _ _ _ HA HPo HT (u f) (64 * 2 ^ k) Hblk Hdisj).
    + exact Hdef.
    + exact Hlast.
    + exact Hsh0.
    + exact Hshw.
    + intros a Hkp. destruct (decide (M' a = M a)) as [Heq|Hne]; [exact Heq|]. exfalso.
      exact (hchanged_not_nkept Lc Lf _ _ _ _ _ HA HPo HT sp MSTK_F a Hsplo Hstk (Hch a Hne) Hkp).
    + exact Hek.
    + exact Hscr.
    + split; [|split; [exact HPo | split; [exact HT | split]]].
      * cbn [app]. exact HA'.
      * intros a Hz. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HF a Hz)|]. exfalso.
        exact (hchanged_not_zone Lc Lf _ _ _ _ _ HA HPo HT sp MSTK_F a Hsplo Hstk Hsptop (Hch a Hne) Hz).
      * intros a Hdz H0. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HD a Hdz H0)|].
        exact (hchanged_dzone_defined Lc Lf _ _ _ _ _ HA HPo HT sp MSTK_F a M' _ Hsplo Hstk (Hch a Hne) Hscr Hek (HD a Hdz H0) Hdz).   (* [comment removed for export] *)
    + exact Hnm.
Qed.

(* [comment removed for export] *)
Theorem fakerel_nspec_f :
  h_fakerel SEGS G FXOK RZ AINVH ->
  fakerel_nspec SEGS SWIN PERMc G AINVf FXOK RZ.
Proof.
  intros HR p rs fx R M mdl Lc Lf F1 F2 B C K f n flag T Hh HFX HAf HLf Hlast Hfw Hrs Hflag Hp0 Hp4 Hpost.
  pose proof HAf as (HA & HPo & HT & HF & HD).
  rewrite HLf in HA. rewrite <- app_assoc in HA. cbn [app] in HA.
  apply (HR p rs fx R M mdl (Lc ++ HID) ((F1 ++ (f, n) :: F2) ++ HIDF) F1 (F2 ++ HIDF) (B0 + B) (C0 + C) K f n flag T HFX Hh).
  - rewrite <- app_assoc. exact HA.
  - rewrite <- app_assoc. reflexivity.
  - exact Hlast.
  - exact Hfw.
  - exact Hrs.
  - exact Hflag.
  - exact Hp0.
  - exact Hp4.
  - intros M' mdl' Hch HA' Hnm.
    assert (HA'' : AINVH (Lc ++ HID) ((F1 ++ F2) ++ HIDF) (B0 + B) (C0 + C) K M' mdl') by (rewrite <- app_assoc; exact HA').
    assert (CH : forall a : word, M' a <> M a -> rtpriv Lc (F1 ++ F2) a).
    { intros a Ha. destruct (Hch a Ha) as (Hu & Hr & Hni & Hnv). unfold rtpriv. rewrite Hu. rewrite <- app_assoc. split; [exact Hr | split; [exact Hni | exact Hnv]]. }
    apply (Hpost M' mdl').
    + intros a Hk. destruct (decide (M' a = M a)) as [Heq|Hne]; [exact Heq|]. exfalso.
      exact (rtpriv_not_nkept Lc (F1 ++ F2) _ _ _ _ _ HA'' HPo HT _ a (CH a Hne) Hk).
    + (* [comment removed for export] *)
      intros a He HMa. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact HMa|]. exfalso.
      destruct (CH a Hne) as (_ & Hni & _). apply Hni. unfold errw in He. pose proof (hp_errno _ _ _ _ HP). pose proof G_ro_img. lia.
    + split; [exact HA''|]. split; [exact HPo|]. split; [exact HT|]. split.
      * intros a Hz. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HF a Hz)|]. exfalso.
        exact (rtpriv_not_zone Lc (F1 ++ F2) _ _ _ _ _ HA'' HPo HT a (CH a Hne) Hz).
      * intros a Hdz H0. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HD a Hdz H0)|]. exfalso.
        exact (rtpriv_not_dzone Lc (F1 ++ F2) _ _ _ _ _ HA'' HPo HT a (CH a Hne) Hdz).
    + exact Hnm.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma CEIL_le_run : CEIL <= CEIL_run.
Proof. pose proof ceil_rng as CR. unfold CEIL. lia. Qed.

Section LFrame.
Hypothesis LC : lcontracts SEGS SWIN G FXOK RZ AINVH.

(* [comment removed for export] *)
Lemma hdst_of_ndst : forall Lc Lf B C K M mdl (HAf : AINVf Lc Lf B C K M mdl) a,
  ndst SWIN PERMc SPTOPc Lc Lf a -> hdst SWIN (Lc ++ HID) (Lf ++ HIDF) a.
Proof. pose proof sfloor_ge as SFG_.
  intros Lc Lf B C K M mdl HAf a Ho. pose proof HAf as (HA & HPo & HT & _). pose proof CEIL_le_run as CL.
  unfold ndst, GPS.owned in Ho. unfold hdst.
  destruct Ho as [Hb|[Hp|[Hs|Hw]]].
  - apply in_blocks_app in Hb as [Hb|Hf]; [left; apply in_blocks_app; left; exact Hb | right; left; rewrite map_fusable_app; apply in_blocks_app; left; exact Hf].
  - destruct (proj1 HPo _ Hp) as [Hh|[Hf|[Hc|Hsw]]]; [left; apply in_blocks_app; right; exact Hh | right; left; rewrite map_fusable_app; apply in_blocks_app; right; exact Hf | right; right; left; lia | right; right; right; exact Hsw].
  - right; right; left. lia.
  - right; right; right. exact Hw.
Qed.
Lemma hshvis_of_nshvis : forall Lc Lf B C K M mdl (HAf : AINVf Lc Lf B C K M mdl) b n,
  nshvis PERMc G Lc Lf b n -> hshvis G (Lc ++ HID) (Lf ++ HIDF) b n.
Proof.
  intros Lc Lf B C K M mdl HAf b n H z Hz. pose proof HAf as (HA & HPo & HT & _). pose proof CEIL_le_run as CL.
  destruct (H z Hz) as [Hb|[Hp|[Hs|Hi]]].
  - left. apply in_blocks_app in Hb as [Hb|Hf]; apply in_blocks_app; [left; apply in_blocks_app; left; exact Hb | right; rewrite map_fusable_app; apply in_blocks_app; left; exact Hf].
  - pose proof (proj2 HPo _ Hp) as H47. destruct (proj1 HPo _ Hp) as [Hh|[Hf|[Hc|Hsw]]].
    + left. apply in_blocks_app. left. apply in_blocks_app. right. exact Hh.
    + left. apply in_blocks_app. right. rewrite map_fusable_app. apply in_blocks_app. right. exact Hf.
    + right; left. lia.
    + right; right. destruct (swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Hsw) as [[Q1 Q2] _]. pose proof G_ro_img. lia.
  - right; left. lia.
  - right; right. exact Hi.
Qed.
Lemma hdst_pre_of : forall Lc Lf B C K M mdl (HAf : AINVf Lc Lf B C K M mdl) dst n,
  ndst_pre SEGS SWIN PERMc SPTOPc G M Lc Lf dst n -> hdst_pre SEGS SWIN G M (Lc ++ HID) (Lf ++ HIDF) dst n.
Proof.
  intros Lc Lf B C K M mdl HAf dst n (NB & M1 & M2 & ACC & SHV & OWN). unfold hdst_pre.
  split; [exact NB|]. split; [exact M1|]. split; [exact M2|]. split; [exact ACC|]. split; [exact (hshvis_of_nshvis _ _ _ _ _ _ _ HAf _ _ SHV)|].
  intros a Ha. destruct (OWN a Ha) as [Ho Hs]. split; [exact (hdst_of_ndst _ _ _ _ _ _ _ HAf a Ho) | exact Hs].
Qed.
Lemma hsrc_pre_of : forall Lc Lf B C K M mdl (HAf : AINVf Lc Lf B C K M mdl) src n bs,
  nsrc_pre SEGS PERMc G M Lc Lf src n bs -> hsrc_pre SEGS G M (Lc ++ HID) (Lf ++ HIDF) src n bs.
Proof.
  intros Lc Lf B C K M mdl HAf src n bs (M1 & M2 & ACC & SHV & RD). unfold hsrc_pre.
  split; [exact M1|]. split; [exact M2|]. split; [exact ACC|]. split; [exact (hshvis_of_nshvis _ _ _ _ _ _ _ HAf _ _ SHV) | exact RD].
Qed.

(* [comment removed for export] *)
Lemma hcall_pre_of : forall R M ret sp stk,
  ncall_pre SEGS SPTOPc G R M ret sp stk -> hcall_pre SEGS G R M ret sp stk /\ SFLOOR + stk <= sp /\ sp <= SPTOPc.
Proof.
  intros R M ret sp stk (R1 & Rr & Re & R2 & Hal & Hsplo & Hsptop & Hsphi & R4 & Hstk').
  pose proof (GPS.sfloor_stk _ _ Hsplo) as HsploC.
  split; [|split; assumption]. unfold hcall_pre. repeat (split; [assumption|]). exact Hstk'.
Qed.

(* [comment removed for export] *)
Lemma nmem_post_of : forall R M mdl Lc Lf B C K ret sp dst n bytes T,
  AINVf Lc Lf B C K M mdl ->
  SFLOOR + MSTK_M <= sp -> sp <= SPTOPc ->
  (forall a : word, dst <= u a < dst + n -> ndst SWIN PERMc SPTOPc Lc Lf a) ->
  (forall i, (i < Z.to_nat n)%nat -> bytes i <> None) -> 0 <= dst -> dst + n <= two47 ->
  nmem_post SEGS AINVf FXOK RZ R M mdl Lc Lf B C K ret sp dst n bytes T ->
  hmem_post SEGS FXOK RZ AINVH R M mdl (Lc ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K ret sp dst n bytes T.
Proof.
  intros R M mdl Lc Lf B C K ret sp dst n bytes T HAf Hsplo Hsptop OWN BY D0 D1 Hpost.
  pose proof HAf as (HA & HPo & HT & HF & HD).
  intros fx' R' M' mdl' HFX' Hkept Ha0 Hby Hch Hscr HA' Hnm.
  apply (Hpost fx' R' M' mdl' HFX' Hkept Ha0 Hby Hch Hscr); [|exact Hnm].
  split; [exact HA'|]. split; [exact HPo|]. split; [exact HT|]. split.
  - intros a Hz. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HF a Hz)|]. exfalso.
    destruct (Hch a Hne) as [Hd|Hs].
    + eapply (AzFrame.gowned_not_zone SWIN G SHC AINVH HP G_ro_img G_img_al G_img_shlo PERMc SPTOPc HID HIDF M0 B0 C0 _ _ _ _ _ _ _ HAf a); [|exact Hz].
      left. exact (OWN a Hd).
    + exact (scratch_not_zone Lc Lf _ _ _ _ _ HA HPo HT sp MSTK_M a Hsplo ltac:(unfold MSTK_M; lia) Hsptop Hs Hz).
  - intros a Hdz H0. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HD a Hdz H0)|].
    destruct (Hch a Hne) as [Hd|Hs]; [|exact (proj1 (Hscr a Hs))].
    pose proof (u64_range a) as AR. pose proof NUMS as (_ & _ & _ & _ & N47 & _). rewrite N47 in D1.
    replace a with (Z_to_bv 64 (dst + Z.of_nat (Z.to_nat (u a - dst)))) by (apply bv_eq; rewrite u64_lit; lia).
    rewrite (Hby (Z.to_nat (u a - dst))) by lia. apply BY. lia.
Qed.

Lemma nmem_two47 : forall a b, nmem a -> nmem b -> 0 <= a /\ b <= two47.
Proof. intros a b Ha Hb. pose proof NUMS as (N1 & N2 & N3 & N4 & N5 & N6). unfold nmem in Ha, Hb. lia. Qed.

Theorem copy_nspec_f : forall entry, h_copy_at SEGS SWIN G FXOK RZ AINVH entry -> copy_nspec SEGS SWIN PERMc SPTOPc G AINVf FXOK RZ entry.
Proof.
  intros entry HM fx R M mdl Lc Lf B C K ret sp dst src n bs T Hh HFX HAf Hpre R10 R11 R12 Hap DST SRC SC1 SC2 Hpost.
  pose proof HAf as (HA & HPo & HT & HF & HD). destruct (hcall_pre_of _ _ _ _ _ Hpre) as (Hpre' & Hsplo & Hsptop).
  apply (HM fx R M mdl (Lc ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K ret sp dst src n bs T HFX Hh HA Hpre' R10 R11 R12 Hap
           (hdst_pre_of _ _ _ _ _ _ _ HAf _ _ DST) (hsrc_pre_of _ _ _ _ _ _ _ HAf _ _ _ SRC) SC1 SC2).
  destruct DST as (NB & M1 & M2 & _ & _ & OWN). destruct (nmem_two47 _ _ M1 M2) as [D0 D1].
  apply (nmem_post_of R M mdl Lc Lf B C K ret sp dst n _ T HAf Hsplo Hsptop); try assumption.
  - intros a Ha. exact (proj1 (OWN a Ha)).
  - intros i Hi. discriminate.
Qed.

Theorem move_nspec_f : forall entry, h_move_at SEGS SWIN G FXOK RZ AINVH entry -> move_nspec SEGS SWIN PERMc SPTOPc G AINVf FXOK RZ entry.
Proof.
  intros entry HM fx R M mdl Lc Lf B C K ret sp dst src n bs T Hh HFX HAf Hpre R10 R11 R12 Hmv DST SRC SC1 SC2 Hpost.
  pose proof HAf as (HA & HPo & HT & HF & HD). destruct (hcall_pre_of _ _ _ _ _ Hpre) as (Hpre' & Hsplo & Hsptop).
  apply (HM fx R M mdl (Lc ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K ret sp dst src n bs T HFX Hh HA Hpre' R10 R11 R12 Hmv
           (hdst_pre_of _ _ _ _ _ _ _ HAf _ _ DST) (hsrc_pre_of _ _ _ _ _ _ _ HAf _ _ _ SRC) SC1 SC2).
  destruct DST as (NB & M1 & M2 & _ & _ & OWN). destruct (nmem_two47 _ _ M1 M2) as [D0 D1].
  apply (nmem_post_of R M mdl Lc Lf B C K ret sp dst n _ T HAf Hsplo Hsptop); try assumption.
  - intros a Ha. exact (proj1 (OWN a Ha)).
  - intros i Hi. discriminate.
Qed.

Theorem fill_nspec_f : forall entry, h_fill_at SEGS SWIN G FXOK RZ AINVH entry -> fill_nspec SEGS SWIN PERMc SPTOPc G AINVf FXOK RZ entry.
Proof.
  intros entry HM fx R M mdl Lc Lf B C K ret sp dst c n T Hh HFX HAf Hpre R10 R11 R12 DST SC1 Hpost.
  pose proof HAf as (HA & HPo & HT & HF & HD). destruct (hcall_pre_of _ _ _ _ _ Hpre) as (Hpre' & Hsplo & Hsptop).
  apply (HM fx R M mdl (Lc ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K ret sp dst c n T HFX Hh HA Hpre' R10 R11 R12
           (hdst_pre_of _ _ _ _ _ _ _ HAf _ _ DST) SC1).
  destruct DST as (NB & M1 & M2 & _ & _ & OWN). destruct (nmem_two47 _ _ M1 M2) as [D0 D1].
  apply (nmem_post_of R M mdl Lc Lf B C K ret sp dst n _ T HAf Hsplo Hsptop); try assumption.
  - intros a Ha. exact (proj1 (OWN a Ha)).
  - intros i Hi. discriminate.
Qed.

(* [comment removed for export] *)
Lemma nstr_post_of : forall R M mdl Lc Lf B C K ret sp len T,
  AINVf Lc Lf B C K M mdl -> SFLOOR + MSTK_M <= sp -> sp <= SPTOPc ->
  nstr_post SEGS AINVf FXOK RZ R M mdl Lc Lf B C K ret sp len T ->
  hstr_post SEGS FXOK RZ AINVH R M mdl (Lc ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K ret sp len T.
Proof.
  intros R M mdl Lc Lf B C K ret sp len T HAf Hsplo Hsptop Hpost.
  pose proof HAf as (HA & HPo & HT & HF & HD).
  intros fx' R' M' mdl' HFX' Hkept Ha0 Hch Hscr HA' Hnm.
  apply (Hpost fx' R' M' mdl' HFX' Hkept Ha0 Hch Hscr); [|exact Hnm].
  split; [exact HA'|]. split; [exact HPo|]. split; [exact HT|]. split.
  - intros a Hz. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HF a Hz)|]. exfalso.
    exact (scratch_not_zone Lc Lf _ _ _ _ _ HA HPo HT sp MSTK_M a Hsplo ltac:(unfold MSTK_M; lia) Hsptop (Hch a Hne) Hz).
  - intros a Hdz H0. destruct (decide (M' a = M a)) as [Heq|Hne]; [rewrite Heq; exact (HD a Hdz H0)|].
    exact (proj1 (Hscr a (Hch a Hne))).
Qed.

Theorem strlen_nspec_f : forall entry, h_strlen_at SEGS G FXOK RZ AINVH entry -> strlen_nspec SEGS PERMc SPTOPc G AINVf FXOK RZ entry.
Proof.
  intros entry HM fx R M mdl Lc Lf B C K ret sp s len T Hh HFX HAf Hpre R10 PRE SC Hpost.
  pose proof HAf as (HA & HPo & HT & HF & HD). destruct (hcall_pre_of _ _ _ _ _ Hpre) as (Hpre' & Hsplo & Hsptop).
  apply (HM fx R M mdl (Lc ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K ret sp s len T HFX Hh HA Hpre' R10).
  - destruct PRE as (L0 & L1 & M1 & M2 & ACC & SHV & BY & NUL & HULL). unfold hstr_pre.
    split; [exact L0|]. split; [exact L1|]. split; [exact M1|]. split; [exact M2|]. split; [exact ACC|].
    split; [exact (hshvis_of_nshvis _ _ _ _ _ _ _ HAf _ _ SHV)|]. split; [exact BY|]. split; [exact NUL | exact HULL].
  - exact SC.
  - exact (nstr_post_of R M mdl Lc Lf B C K ret sp len T HAf Hsplo Hsptop Hpost).
Qed.
End LFrame.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Inst.
Variable A : atable.
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
(* [comment removed for export] *)
Variable AINVX : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HPX : hprops SWIN G SHC AINVX.
#[local] Notation AINVfX := (AINV_f SWIN G AINVX PERMc SPTOPc HID HIDF M0 B0 C0).
#[local] Notation VSHf := (AzFrame.VSHf HID HIDF).

(* [comment removed for export] *)
Lemma perm_casesX : forall Lc Lf (HPo : perm_owned) z, in_wins PERMc z ->
  in_blocks (Lc ++ HID) z \/ in_blocks (Lf ++ HIDF) z \/ SPTOPc <= z \/ in_wins SWIN z.
Proof.
  intros Lc Lf HPo z Hp. destruct (proj1 HPo z Hp) as [Hh|[Hf|[Hc|Hsw]]].
  - left. destruct Hh as (b & n & Hin & Hz). exists b, n. split; [apply in_app_iff; right; exact Hin | exact Hz].
  - right; left. apply in_blocks_fusable in Hf as (f & m & Hin & Hz). exists f, m. split; [apply in_app_iff; right; exact Hin | lia].
  - right; right; left. exact Hc.
  - right; right; right. exact Hsw.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma pshadow_casesX : forall (HPo : perm_owned) (HT : CEIL_run <= SPTOPc /\ SPTOPc mod 8 = 0) z, in_pshadow PERMc z ->
  in_lshadow (HID ++ HIDF) z \/ in_sshadow z \/ in_ishadow G z.
Proof.
  intros HPo HT z (lo & hi & Hin & Hlt & [S1 S2]).
  (* [comment removed for export] *)
  pose proof (proj1 HT) as HT1.
  set (z1 := Z.max lo (8 * (z - SB))).
  assert (W1 : lo <= z1 < hi) by (subst z1; clear - Hlt S1 S2; lia).
  assert (G1 : z1 / 8 = z - SB) by (subst z1; clear - Hlt S1 S2; lia).
  pose proof (proj2 HPo z1 ltac:(exists lo, hi; split; [exact Hin | exact W1])) as H47.
  destruct (proj1 HPo z1 ltac:(exists lo, hi; split; [exact Hin | exact W1])) as [Hh|[Hf|[Hc|Hsw]]].
  - left. destruct Hh as (b & n & Hbin & Hbz). exists b, n. split; [apply in_app_iff; left; exact Hbin|]. unfold in_shadow. clear - Hbz G1 W1. lia.
  - left. apply in_blocks_fusable in Hf as (f & m & Hfin & Hfz). exists f, m. split; [apply in_app_iff; right; exact Hfin|].
    unfold in_shadow. clear - Hfz G1 W1. lia.
  - right; left. unfold in_sshadow. pose proof NUMS as NU. clear - NU H47 Hc HT1 G1. lia.
  - right; right. destruct (swin_byte SWIN G G_ro_img G_img_al SWIN_img z1 Hsw) as [[Q1 Q2] _]. unfold in_ishadow. pose proof G_ro_img as GR. clear - Q1 Q2 GR G1. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma If_facts : forall Lc Lf B C K M mdl, AINVfX Lc Lf B C K M mdl ->
  Forall (fun iv => 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= CEIL_run
                    /\ (u (fst iv) + u (snd iv) <= img_lo A \/ img_hi A <= u (fst iv))) (m_vm_lazy mdl).
Proof. intros Lc Lf B C K M mdl HAf. rewrite A_img_hi, A_img_lo. exact (AINV_f_facts SWIN G SHC AINVX HPX PERMc SPTOPc HID HIDF M0 B0 C0 _ _ _ _ _ _ _ HAf). Qed.

Lemma If_nolazy : forall Lc Lf B C K M mdl b n (a : word),
  AINVfX Lc Lf B C K M mdl -> In (b, n) (Lc ++ Lf) -> b <= u a < b + n -> lz mdl a = false.
Proof.
  intros Lc Lf B C K M mdl b n a HAf Hin Hz. eapply (AINV_f_nolazy SWIN G SHC AINVX HPX); [exact HAf | | exact Hz].
  apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; exact Hin | right; apply in_app_iff; right; apply in_app_iff; left; exact Hin].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma If_perm_nolazy : forall Lc Lf B C K M mdl (a : word), AINVfX Lc Lf B C K M mdl -> in_wins PERMc (u a) -> lz mdl a = false.
Proof.
  intros Lc Lf B C K M mdl a HAf Hp. pose proof HAf as (HA & HPo & HT & _).
  assert (NOLZ : forall lo, (forall iv, In iv (m_vm_lazy mdl) -> u (fst iv) + u (snd iv) <= lo \/ u a < u (fst iv)) -> lo mod 4096 = 0 -> lo <= u a -> lz mdl a = false).
  { intros lo Hivs Hlo Hle. destruct (lz mdl a) eqn:Hl; [|reflexivity]. exfalso.
    unfold lz, page_in_ranges in Hl. apply existsb_exists in Hl as [iv [Hin Hb]].
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (page_base_le' a) as (P1 & P2 & P3). unfold page_size in *. destruct (Hivs iv Hin); lia. }
  pose proof (hp_facts _ _ _ _ HPX _ _ _ _ _ _ _ HA) as FACTS.
  destruct (perm_casesX Lc Lf HPo _ Hp) as [Hh|[Hf|[Hc|Hsw]]].
  - destruct Hh as (b & n & Hin & Hz). eapply (hp_nolazy _ _ _ _ HPX); [exact HA | apply in_app_iff; left; exact Hin | exact Hz].
  - destruct Hf as (f & m & Hin & Hz). eapply (hp_nolazy _ _ _ _ HPX); [exact HA | apply in_app_iff; right; exact Hin | exact Hz].
  - apply (NOLZ CEIL_run); [| exact ceil_pg | lia]. intros iv Hin. pose proof (proj1 (Forall_forall _ _) FACTS iv Hin) as (F1 & F2 & F3). lia.
  - destruct (swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Hsw) as [[Q1 Q2] _]. pose proof G_ro_img as (GR0 & GR1 & GR2).
    destruct (lz mdl a) eqn:Hl; [|reflexivity]. exfalso.
    unfold lz, page_in_ranges in Hl. apply existsb_exists in Hl as [iv [Hin Hb]].
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (page_base_le' a) as (P1 & P2 & P3). unfold page_size in *.
    pose proof (proj1 (Forall_forall _ _) FACTS iv Hin) as (F1 & F2 & F3). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma If_top : forall Lc Lf B C K M mdl, AINVfX Lc Lf B C K M mdl -> CEIL_run <= SPTOPc.
Proof. intros Lc Lf B C K M mdl (_ & _ & HT & _). lia. Qed.

Lemma If_perm_vsh : forall Lc Lf B C K M mdl z, AINVfX Lc Lf B C K M mdl -> in_pshadow PERMc z -> in_shv VSHf z = true \/ in_shc SHC z = true.
Proof.
  intros Lc Lf B C K M mdl z HAf Hp. pose proof HAf as (HA & HPo & HT & _).
  destruct (pshadow_casesX HPo HT z Hp) as [Hl|[Hs|Hi]].
  - left. unfold AzFrame.VSHf, in_shv. apply existsb_exists. destruct Hl as (b & n & Hin & [Z1 Z2]). exists (b, n). split; [exact Hin|].
    cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
  - right. exact (hp_shc_stack _ _ _ _ HPX z Hs).
  - right. apply (hp_shc_image _ _ _ _ HPX z). exact Hi.
Qed.

Lemma If_perm_bnd : forall Lc Lf B C K M mdl z, AINVfX Lc Lf B C K M mdl -> in_wins PERMc z -> z < two47.
Proof. intros Lc Lf B C K M mdl z (_ & HPo & _) Hp. exact (proj2 HPo z Hp). Qed.

Lemma If_perm_mem : forall Lc Lf B C K M mdl z, AINVfX Lc Lf B C K M mdl -> in_wins PERMc z -> z < SHMAPLO \/ KHI <= z.
Proof.
  intros Lc Lf B C K M mdl z HAf Hp. pose proof HAf as (HA & HPo & HT & _).
  pose proof (band_lits G G_img_al) as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7). pose proof G_img_shlo as GS.
  destruct (perm_casesX Lc Lf HPo _ Hp) as [Hh|[Hf|[Hc|Hsw]]].
  - destruct Hh as (b & n & Hin & Hz). pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo b n z (proj1 (hp_zone _ _ _ _ HPX _ _ _ _ _ _ _ b n HA Hin)) Hz). lia.
  - destruct Hf as (f & m & Hin & Hz). pose proof (ablk_byte G G_ro_img G_img_al G_img_shlo f m z (proj1 (hp_fzone _ _ _ _ HPX _ _ _ _ _ _ _ f m HA Hin)) Hz). lia.
  - lia.
  - destruct (swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Hsw) as [[Q1 Q2] _]. lia.
Qed.

Lemma If_zone : forall Lc Lf B C K M mdl b m, AINVfX Lc Lf B C K M mdl -> In (b, m) (Lc ++ Lf) -> ablk_ok G b m.
Proof.
  intros Lc Lf B C K M mdl b m HAf Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exact (proj1 (AINV_f_zone SWIN G SHC AINVX HPX PERMc SPTOPc HID HIDF M0 B0 C0 _ _ _ _ _ _ _ b m HAf Hin)).
  - exact (proj1 (AINV_f_fzone SWIN G SHC AINVX HPX PERMc SPTOPc HID HIDF M0 B0 C0 _ _ _ _ _ _ _ b m HAf Hin)).
Qed.

Lemma If_disj : forall Lc Lf B C K M mdl L1 L2 b m b' m',
  AINVfX Lc Lf B C K M mdl -> Lc = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2 ++ Lf) -> b + m <= b' \/ b' + m' <= b.
Proof.
  intros Lc Lf B C K M mdl L1 L2 b m b' m' HAf HL Hin. rewrite app_assoc in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exact (AINV_f_disj SWIN G SHC AINVX HPX PERMc SPTOPc HID HIDF M0 B0 C0 _ _ _ _ _ _ _ L1 L2 b m b' m' HAf HL Hin).
  - eapply (AINV_f_bfdisj SWIN G SHC AINVX HPX PERMc SPTOPc HID HIDF M0 B0 C0); [exact HAf | rewrite HL; apply in_app_iff; right; left; reflexivity | exact Hin].
Qed.

Lemma If_perm_apart : forall Lc Lf B C K M mdl b m lo hi,
  AINVfX Lc Lf B C K M mdl -> In (b, m) Lc -> 1 <= m -> In (lo, hi) PERMc -> lo < hi -> b + m <= lo \/ hi <= b.
Proof.
  intros Lc Lf B C K M mdl b m lo hi HAf Hin Hm Hp Hlt. pose proof HAf as (HA & HPo & HT & _).
  destruct (Z_le_gt_dec (b + m) lo) as [|G1]; [left; lia|]. destruct (Z_le_gt_dec hi b) as [|G2]; [right; lia|]. exfalso.
  set (z := Z.max lo b).
  assert (Hz : lo <= z < hi) by (subst z; lia). assert (Hbz : b <= z < b + m) by (subst z; lia).
  pose proof (proj1 (hp_zone _ _ _ _ HPX _ _ _ _ _ _ _ b m HA ltac:(apply in_app_iff; left; exact Hin))) as ZBm.
  pose proof (band_lits G G_img_al) as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7).
  destruct (proj1 HPo z ltac:(exists lo, hi; split; [exact Hp | exact Hz])) as [Hh|[Hf|[Hc|Hsw]]].
  - destruct Hh as (b' & n' & Hin' & Hz'). destruct (in_split _ _ Hin) as (L1 & L2 & HL).
    destruct (hp_disj _ _ _ _ HPX _ _ _ _ _ _ _ L1 (L2 ++ HID) b m b' n' HA ltac:(rewrite HL; rewrite <- app_assoc; reflexivity)
                ltac:(rewrite app_assoc; apply in_app_iff; right; exact Hin')); lia.
  - apply in_blocks_fusable in Hf as (f & n' & Hin' & Hz').
    destruct (hp_bfdisj _ _ _ _ HPX _ _ _ _ _ _ _ b m f n' HA ltac:(apply in_app_iff; left; exact Hin) ltac:(apply in_app_iff; right; exact Hin')); lia.
  - destruct ZBm as (A1 & A2 & A3 & A4). lia.
  - destruct (swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Hsw) as [[Q1 Q2] _]. pose proof G_ro_img. destruct ZBm as (A1 & A2 & A3 & A4). lia.
Qed.

Lemma If_ifacts : AzNodesAlloc3.ifacts A PERMc SPTOPc SHC VSHf G AINVfX.
Proof.
  split; [exact If_facts|]. split; [exact If_nolazy|]. split; [exact If_perm_nolazy|]. split; [exact If_top|].
  split; [exact If_perm_vsh|]. split; [exact If_perm_bnd | exact If_zone].
Qed.
End Inst.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Obl.
Variable A : atable.
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
Hypothesis HPN : forall n, hprops SWIN G SHC (AINVHN n).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (u a) = false -> find_segment SEGS (u a) 1 = None.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_wr : AzCallLib.GCL.segs_wr_ok SEGS.
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= u a < g_img_hi G) -> find_segment SEGS (u a) 1 = None.
Hypothesis ROM_ok : forall x : word, g_ro_lo G <= u x -> u x < g_ro_hi G -> seg_rom SEGS x <> None.
Hypothesis RO_hi : g_ro_hi G < 2 ^ 64.
Hypothesis G_newh_img : g_img_lo G <= g_newh_got G /\ g_newh_got G + 8 <= g_img_hi G /\ g_img_lo G <= g_newh_cell G /\ g_newh_cell G + 8 <= g_img_hi G.
Hypothesis G_opnew_kn_wf : opnew_kn_wf G = true.   (* [comment removed for export] *)
Variable KCAP : Z.
Hypothesis GKCAP_le : GKCAP <= KCAP.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable nx0 : nat.
Variable FS0 : Fs.Fs.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Hypothesis FPC_kfpc : forall M v lo, AX2S.fpc M v lo DMAXN -> FPC M v lo.
Variable FRESHA : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis HCc : hcontracts_core SEGS G FXOK RZ AINVH AINVHN FPC FRESHA.   (* [comment removed for export] *)
Hypothesis LC : lcontracts SEGS SWIN G FXOK RZ AINVH.

#[local] Notation VSHf := (AzFrame.VSHf HID HIDF).
Let HI := If_ifacts A A_img_hi A_img_lo AINVH HP.
Let HIN := fun n => If_ifacts A A_img_hi A_img_lo (AINVHN n) (HPN n).
Let SHC_stack := hp_shc_stack _ _ _ _ HP.
Let SHC_image : forall z, in_ishadow G z -> in_shc SHC z = true := hp_shc_image _ _ _ _ HP.
Let SWIN_img' : forall lo hi, In (lo, hi) SWIN -> g_img_lo G <= lo /\ hi <= g_img_hi G :=
  fun lo hi Hin => match SWIN_img lo hi Hin with conj S1 (conj S2 _) => conj (Z.le_trans _ _ _ (Z.le_trans _ _ _ (proj1 G_ro_img) (proj1 (proj2 G_ro_img))) S1) S2 end.
Let G_img_hull : 0 <= g_img_lo G /\ g_img_lo G <= g_ro_lo G <= g_img_hi G :=
  conj (proj1 G_img_al) (conj (proj1 G_ro_img) (Z.le_trans _ _ _ (proj1 (proj2 G_ro_img)) (proj2 (proj2 G_ro_img)))).
Let G_img_ceil := AzFrame.G_img_ceil G G_img_al G_img_shlo.
Let G_errno_img : g_img_lo G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.   (* [comment removed for export] *)
Proof. pose proof (hp_errno _ _ _ _ HP). pose proof G_ro_img. lia. Qed.
Let G_ro_img' : g_ro_lo G <= g_ro_hi G <= g_img_hi G := proj2 G_ro_img.

Theorem gcontracts_core_f :
  gcontracts_core SEGS IT A nx0 PERMc SPTOPc FS0 SHC VSHf AINVf KCAP FTOPc FXOK UINV RZ G.
Proof.
  pose proof HI as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
  constructor.
  - (* [comment removed for export] *)
    exact (node_imgload_sound SEGS IT IT_ok nx0 SWIN PERMc SPTOPc FS0 SHC VSHf AINVf KCAP FTOPc
             (AINV_f_frame SWIN G SHC AINVH HP G_ro_img G_img_al G_img_shlo PERMc SPTOPc HID HIDF M0 B0 C0)
             (AINV_f_lazy SWIN G SHC AINVH HP PERMc SPTOPc HID HIDF M0 B0 C0)
             A I1 SEGS_in_hull SEGS_wx FXOK UINV UINV_agree RZ RZ_silent1 G ROM_ok RO_hi).
  - (* [comment removed for export] *)
    exact (node_free_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G FPC
             HI A_img_hi A_img_lo SHC_stack SHC_image SWIN_img' G_img_hull G_img_ceil G_errno_img GKCAP_le FPC_kfpc G_newh_img
             (free_nspec_f MSTK_A _ ltac:(unfold MSTK_A; lia) (hcc_free_thunk _ _ _ _ _ _ _ _ HCc))
             (free_nspec_f MSTK_A _ ltac:(unfold MSTK_A; lia) (hcc_free _ _ _ _ _ _ _ _ HCc))).
  - (* [comment removed for export] *)
    exact (node_blkfact_obl SEGS nx0 PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV RZ G
             I7 (If_disj AINVH HP) (If_perm_apart AINVH HP) I4 I6 G_img_hull G_img_ceil).
  - (* [comment removed for export] *)
    exact (node_opdel_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G FPC
             HI A_img_hi A_img_lo SHC_stack SHC_image SWIN_img' G_img_hull G_img_ceil G_errno_img GKCAP_le FPC_kfpc G_newh_img
             (free_nspec_f MSTK_A _ ltac:(unfold MSTK_A; lia) (hcc_opdel _ _ _ _ _ _ _ _ HCc))).
  - (* [comment removed for export] *)
    exact (node_opdel_sized_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G FPC
             HI A_img_hi A_img_lo SHC_stack SHC_image SWIN_img' G_img_hull G_img_ceil G_errno_img GKCAP_le FPC_kfpc G_newh_img
             (free_nspec_f MSTK_A _ ltac:(unfold MSTK_A; lia) (hcc_opdel_sized _ _ _ _ _ _ _ _ HCc))).
  - (* [comment removed for export] *)
    exact (node_memcpy_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             I1 A_img_hi A_img_lo SEGS_in_hull SEGS_wr I2 I3 I4 SHC_stack SHC_image SWIN_img' SEGS_out G_img_ceil G_errno_img G_img_shlo G_img_hull I7 I5 I6
             (If_perm_mem AINVH HP) (copy_nspec_f _ (lc_memcpy _ _ _ _ _ _ LC))).
  - (* [comment removed for export] *)
    exact (node_memset_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             I1 A_img_hi A_img_lo SEGS_in_hull I2 I3 I4 SHC_stack SHC_image SWIN_img' SEGS_out G_img_ceil G_errno_img G_img_shlo G_img_hull I7 I5 I6
             (If_perm_mem AINVH HP) (fill_nspec_f _ (lc_memset _ _ _ _ _ _ LC))).
  - (* [comment removed for export] *)
    exact (node_memmove_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             I1 A_img_hi A_img_lo SEGS_in_hull SEGS_wr I2 I3 I4 SHC_stack SHC_image SWIN_img' SEGS_out G_img_ceil G_errno_img G_img_shlo G_img_hull I7 I5 I6
             (If_perm_mem AINVH HP) (move_nspec_f _ (lc_memmove _ _ _ _ _ _ LC))).
  - (* [comment removed for export] *)
    exact (node_strlen_obl SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             I1 A_img_hi A_img_lo SEGS_in_hull I2 I3 I4 SHC_stack SHC_image SWIN_img' SEGS_out G_img_ceil G_errno_img G_img_shlo G_img_hull I7 I5 I6 G_ro_img'
             (strlen_nspec_f _ (lc_strlen _ _ _ _ _ _ LC))).
  - (* [comment removed for export] *)
    exact (node_amemcpy_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             I1 A_img_hi A_img_lo SEGS_in_hull SEGS_wr I2 I3 I4 SHC_stack SHC_image SWIN_img' SEGS_out G_img_ceil G_errno_img G_img_shlo G_img_hull I7 I5 I6
             (If_perm_mem AINVH HP) (copy_nspec_f _ (lc_amemcpy _ _ _ _ _ _ LC))).
  - (* [comment removed for export] *)
    exact (node_amemset_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             I1 A_img_hi A_img_lo SEGS_in_hull I2 I3 I4 SHC_stack SHC_image SWIN_img' SEGS_out G_img_ceil G_errno_img G_img_shlo G_img_hull I7 I5 I6
             (If_perm_mem AINVH HP) (fill_nspec_f _ (lc_amemset _ _ _ _ _ _ LC))).
  - (* [comment removed for export] *)
    exact (node_amemmove_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             I1 A_img_hi A_img_lo SEGS_in_hull SEGS_wr I2 I3 I4 SHC_stack SHC_image SWIN_img' SEGS_out G_img_ceil G_errno_img G_img_shlo G_img_hull I7 I5 I6
             (If_perm_mem AINVH HP) (move_nspec_f _ (lc_amemmove _ _ _ _ _ _ LC))).
  - (* [comment removed for export] *)
    exact (node_stkmal_all_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             HI A_img_hi A_img_lo SHC_stack SHC_image SWIN_img' G_img_hull G_img_ceil G_errno_img G_newh_img
             (fun k Hk => stkmal_nspec_f k (hcc_stkmal _ _ _ _ _ _ _ _ HCc k Hk))).
  - (* [comment removed for export] *)
    exact (node_fakerel_obl SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ RZ_silent1 G
             HI A_img_hi A_img_lo SHC_stack SHC_image SWIN_img' G_img_hull G_errno_img G_newh_img
             (AINV_f_lazy SWIN G SHC AINVH HP PERMc SPTOPc HID HIDF M0 B0 C0) SEGS_in_hull SEGS_wx FTOPc_small IT IT_ok
             (fakerel_nspec_f (hcc_fakerel _ _ _ _ _ _ _ _ HCc))).
Qed.
Hypothesis HOP : h_alloc1_at SEGS G FXOK RZ AINVH FPC (hopnew_x SEGS G) MSTK_N (g_opnew G).   (* [comment removed for export] *)
Theorem gcontracts_f :
  gcontracts SEGS IT A nx0 PERMc SPTOPc FS0 SHC VSHf AINVf KCAP FTOPc FXOK UINV RZ G bcap ccap.
Proof.
  pose proof HI as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
  destruct gcontracts_core_f as [g0 g11 g13 g21 g22 g1 g2 g3 g4 g5 g6 g7 g50 g51].
  constructor; try assumption.
  - (* [comment removed for export] *)
    exact (node_opnew_obl SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G bcap ccap FPC
             HI A_img_hi A_img_lo SHC_stack SHC_image SWIN_img' G_img_hull G_img_ceil G_errno_img GKCAP_le FPC_kfpc G_newh_img G_opnew_kn_wf
             (alloc1_nspec_f _ MSTK_N _ ltac:(unfold MSTK_N; lia) HOP)).
Qed.
End Obl.

End FrameAlloc.

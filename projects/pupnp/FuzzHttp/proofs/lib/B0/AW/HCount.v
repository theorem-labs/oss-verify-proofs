(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpAllocA HObjA.
Import ListNotations.
Open Scope Z_scope.

Lemma a0_cls0_iff : forall n, 0 <= n -> (a0_cls n = 0 <-> 64513 <= n).
Proof.
  intros n Hn. unfold a0_cls.
  assert (NEED : (n <= 64512 -> 1 <= a0_need n <= 65536) /\ (64513 <= n -> 65536 < a0_need n)).
  { unfold a0_need, a0_rzlog.
    destruct (n <=? 48) eqn:E1; [apply Z.leb_le in E1; change (Z.shiftl 16 0) with 16; split; intros; Z.div_mod_to_equations; lia|]. apply Z.leb_gt in E1.
    destruct (n <=? 96) eqn:E2; [apply Z.leb_le in E2; change (Z.shiftl 16 1) with 32; split; intros; Z.div_mod_to_equations; lia|]. apply Z.leb_gt in E2.
    destruct (n <=? 448) eqn:E3; [apply Z.leb_le in E3; change (Z.shiftl 16 2) with 64; split; intros; Z.div_mod_to_equations; lia|]. apply Z.leb_gt in E3.
    destruct (n <=? 3968) eqn:E4; [apply Z.leb_le in E4; change (Z.shiftl 16 3) with 128; split; intros; Z.div_mod_to_equations; lia|]. apply Z.leb_gt in E4.
    destruct (n <=? 16128) eqn:E5; [apply Z.leb_le in E5; change (Z.shiftl 16 4) with 256; split; intros; Z.div_mod_to_equations; lia|]. apply Z.leb_gt in E5.
    destruct (n <=? 32256) eqn:E6; [apply Z.leb_le in E6; change (Z.shiftl 16 5) with 512; split; intros; Z.div_mod_to_equations; lia|]. apply Z.leb_gt in E6.
    destruct (n <=? 64512) eqn:E7; [apply Z.leb_le in E7; change (Z.shiftl 16 6) with 1024; split; intros; Z.div_mod_to_equations; lia|]. apply Z.leb_gt in E7.
    change (Z.shiftl 16 7) with 2048. split; intros; Z.div_mod_to_equations; lia. }
  destruct NEED as [N1 N2].
  destruct (a0_need n <=? 65536) eqn:E.
  - apply Z.leb_le in E. split; [| intros H; specialize (N2 H); lia].
    intros C. assert (n <= 64512) by (destruct (Z_le_gt_dec n 64512); [assumption| specialize (N2 ltac:(lia)); lia]).
    pose proof (a0_class_of_range (a0_need n) (N1 ltac:(lia))). lia.
  - apply Z.leb_gt in E. split; [| reflexivity]. intros _. destruct (Z_le_gt_dec n 64512) as [L|G]; [specialize (N1 L); lia| lia].
Qed.

Definition CG_A : Z := 322535.
Definition CG_B : Z := 64513.
Definition CG_SL : Z := 645070.

Section C.
Context {HCEIL : HasCeiling}.
Variable FI : fs_if.
Variable AI : am_if FI.
Local Notation hdr := (HObjA.hdr FI AI).
Local Notation nsec1 := (HttpAllocA.nsec1).

Definition w0 (n : Z) : Z := if a0_cls n =? 0 then n else 0.
#[using="Type"] Lemma w0_nonneg : forall n, 0 <= n -> 0 <= w0 n.
Proof. intros n H. unfold w0. destruct (a0_cls n =? 0); lia. Qed.
#[using="Type"] Lemma w0_le : forall n, 0 <= n -> w0 n <= n.
Proof. intros n H. unfold w0. destruct (a0_cls n =? 0); lia. Qed.

#[using="Type"] Lemma w0_new : forall c, 0 <= c -> 5 * nsec1 (c + 1) <= w0 (c + 1).
Proof.
  intros c Hc. unfold HttpAllocA.nsec1, w0. destruct (a0_cls (c + 1) =? 0) eqn:E; [| lia].
  apply Z.eqb_eq in E. apply (a0_cls0_iff (c + 1) ltac:(lia)) in E. lia.
Qed.

#[using="Type"] Lemma w0_grow : forall c c', 0 <= c -> c + 5 <= c' -> 5 * nsec1 (c' + 1) <= w0 (c' + 1) - w0 (c + 1).
Proof.
  intros c c' Hc Hg. unfold HttpAllocA.nsec1, w0.
  destruct (a0_cls (c' + 1) =? 0) eqn:E'; destruct (a0_cls (c + 1) =? 0) eqn:E; try lia.
  exfalso. apply Z.eqb_eq in E. apply Z.eqb_neq in E'. apply E'. apply (a0_cls0_iff (c' + 1) ltac:(lia)).
  apply (a0_cls0_iff (c + 1) ltac:(lia)) in E. lia.
Qed.

#[using="Type"] Lemma w0_same : forall c, 0 <= 5 * 0 <= w0 (c + 1) - w0 (c + 1).
Proof. intros c. lia. Qed.

Definition phiH (hs : list hdr) : Z := fold_right (fun h a => w0 (vcap FI AI h + 1) + w0 (ncap FI AI h + 1) + a) 0 hs.
Definition hlenA (hs : list hdr) : Z := fold_right (fun h a => vlen FI AI h + nlen FI AI h + a) 0 hs.
#[using="Type"] Lemma phiH_app : forall hs1 hs2, phiH (hs1 ++ hs2) = phiH hs1 + phiH hs2.
Proof. intros hs1 hs2. unfold phiH. induction hs1 as [|h hs1 IH]; cbn [app fold_right]; [lia| rewrite IH; lia]. Qed.
#[using="Type"] Lemma hlenA_app : forall hs1 hs2, hlenA (hs1 ++ hs2) = hlenA hs1 + hlenA hs2.
Proof. intros hs1 hs2. unfold hlenA. induction hs1 as [|h hs1 IH]; cbn [app fold_right]; [lia| rewrite IH; lia]. Qed.
#[using="Type"] Lemma phiH_nonneg : forall hs, Forall (hdro_pure FI AI) hs -> 0 <= phiH hs.
Proof.
  intros hs H. induction H as [|h hs (V1 & V2 & N1 & N2 & _) _ IH]; cbn [phiH fold_right]; [lia|].
  pose proof (w0_nonneg (vcap FI AI h + 1) ltac:(lia)). pose proof (w0_nonneg (ncap FI AI h + 1) ltac:(lia)). unfold phiH in IH. lia.
Qed.

#[using="Type"] Lemma w0_len : forall l c, 1 <= l <= c -> c <= l + 5 -> 64507 * w0 (c + 1) <= 64513 * l.
Proof.
  intros l c H1 H2. unfold w0. destruct (a0_cls (c + 1) =? 0) eqn:E; [| lia].
  apply Z.eqb_eq in E. apply (a0_cls0_iff (c + 1) ltac:(lia)) in E. lia.
Qed.
#[using="Type"] Lemma phiH_le : forall hs, Forall (hdro_pure FI AI) hs -> 64507 * phiH hs <= 64513 * hlenA hs.
Proof.
  intros hs H. induction H as [|h hs (V1 & V2 & N1 & N2 & _) _ IH]; cbn [phiH hlenA fold_right]; [lia|].
  pose proof (w0_len (vlen FI AI h) (vcap FI AI h) V1 V2). pose proof (w0_len (nlen FI AI h) (ncap FI AI h) N1 N2).
  unfold phiH, hlenA in IH. lia.
Qed.

Definition cgG (hs : list hdr) : Z := CG_B * hlenA hs - 64507 * phiH hs.
#[using="Type"] Lemma cgG_nil : cgG [] = 0.
Proof. reflexivity. Qed.
#[using="Type"] Lemma cgG_app : forall hs1 hs2, cgG (hs1 ++ hs2) = cgG hs1 + cgG hs2.
Proof. intros hs1 hs2. unfold cgG. rewrite phiH_app, hlenA_app. lia. Qed.
#[using="Type"] Lemma cgG_nonneg : forall hs, Forall (hdro_pure FI AI) hs -> 0 <= cgG hs.
Proof. intros hs H. pose proof (phiH_le hs H). unfold cgG, CG_B. lia. Qed.

#[using="Type"] Lemma cgG_step : forall hs hs' dN d, 5 * dN <= phiH hs' - phiH hs -> hlenA hs' <= hlenA hs + d -> CG_A * dN + cgG hs' <= cgG hs + CG_B * d.
Proof. intros hs hs' dN d H1 H2. unfold cgG, CG_A, CG_B. lia. Qed.
End C.

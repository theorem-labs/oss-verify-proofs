(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Decode Agree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Globals.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
Import ListNotations.
Open Scope Z_scope.

Lemma app_ivs_disjoint_range : forall W A n, app_ivs W -> shband A -> shband (A + n - 1) -> disjoint_from W A n.
Proof.
  intros W A n H HA HB. unfold shband, SH_LO, SH_HI in HA, HB. induction H as [|[lo hi] W Hiv _ IH]; cbn; [exact I|].
  split; [| exact IH]. unfold app_iv, SH_HI in Hiv. cbn in Hiv. lia.
Qed.

Definition globals_shadow (m : word -> option byte) : Prop :=
  Forall (fun g => match g with (b, srz, _) => exists bs, rw_cells asegs m (sh b) [CB (Z.to_nat (srz / 8)%Z) bs] end) A0_GLOBALS
  /\ (exists bs, rw_cells asegs m (sh 0xaedc0) [CB 656 bs]).

Lemma globals_bounds :
  Forall (fun g => match g with (b, srz, _) => 0x213e0 <= b /\ 0 <= srz /\ srz mod 8 = 0 /\ b + srz <= 0x5e6060 end)%Z A0_GLOBALS.
Proof.
  unfold A0_GLOBALS. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.

Lemma globals_shadow_frame : forall W m m', globals_shadow m -> munch W m m' -> wmono asegs m m' -> app_ivs W -> globals_shadow m'.
Proof.
  intros W m m' [G [bsd GD]] MU WM AW. unfold globals_shadow in *.
  split; [| exists bsd; eapply rw_cells_transport; [exact GD | exact MU | exact WM |];
            cbn [cells_size csize Nat.add]; apply app_ivs_disjoint_range; [exact AW| |]; unfold shband, SH_LO, SH_HI, sh, SHADOW_OFF; Z.div_mod_to_equations; lia ].
  apply Forall_forall. intros [[b srz] odr] Hin.
  pose proof (proj1 (Forall_forall _ _) G _ Hin) as (bs & RC). pose proof (proj1 (Forall_forall _ _) globals_bounds _ Hin) as (B1 & B2 & B3 & B4).
  cbn beta iota in RC, B1, B2, B3, B4 |- *.
  exists bs. eapply rw_cells_transport; [exact RC | exact MU | exact WM |].
  cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (Z.div_mod_to_equations; lia).
  apply app_ivs_disjoint_range; [exact AW| |]; unfold shband, SH_LO, SH_HI, sh, SHADOW_OFF; Z.div_mod_to_equations; lia.
Qed.

Lemma globals_shadow_agree : forall (P : Z -> Prop) m m', gagree_on P m m' ->
  (forall a, 0x7fffa000 <= a < 0x800b9200 -> P a) -> globals_shadow m -> globals_shadow m'.
Proof.
  intros P m m' AG HP [G [bsd GD]]. unfold globals_shadow in *.
  split; [| exists bsd; eapply rw_cells_gagree; [exact AG | exact GD |];
            cbn [cells_size csize Nat.add]; intros a Ha; apply HP; unfold sh, SHADOW_OFF in Ha; Z.div_mod_to_equations; lia ].
  apply Forall_forall. intros [[b srz] odr] Hin.
  pose proof (proj1 (Forall_forall _ _) G _ Hin) as (bs & RC). pose proof (proj1 (Forall_forall _ _) globals_bounds _ Hin) as (B1 & B2 & B3 & B4).
  cbn beta iota in RC, B1, B2, B3, B4 |- *.
  exists bs. eapply rw_cells_gagree; [exact AG | exact RC |].
  cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (Z.div_mod_to_equations; lia).
  intros a Ha. apply HP. unfold sh, SHADOW_OFF in Ha. Z.div_mod_to_equations. lia.
Qed.

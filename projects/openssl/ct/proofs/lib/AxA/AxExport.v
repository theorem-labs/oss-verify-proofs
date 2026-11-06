(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OSSVerify.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Mem RzCPS.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie AxLin AxVal AxBytes AxMem AxState AxSys AxModelRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Export.
Variable segs : list Segment.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R segs amodel (MR segs fs0 ρ) LIM ρ B (mkCfg ms model).
Variable A' : list (Z * Z).

(* [comment removed for export] *)
Definition mX : word -> option byte := mrestrict (RzCPS.HID A' model) (ms_mem ms).

(* [comment removed for export] *)
Definition vis (lo hi : Z) : Prop := forall z, lo <= z < hi -> RzCPS.HID A' model (wz z) = false.

Lemma vis_mrd (a : word) : RzCPS.HID A' model a = false -> Mem.mrd segs mX a = rv segs (ms_mem ms) a.
Proof. intros H. unfold Mem.mrd, rv, mX, mrestrict. rewrite H. reflexivity. Qed.

Lemma vis_wview (a : word) : RzCPS.HID A' model a = false -> wview segs mX a = wview segs (ms_mem ms) a.
Proof. intros H. unfold wview, mX, mrestrict. rewrite H. reflexivity. Qed.

Lemma R_region (Rg : region) : In Rg (a_mem B) -> is_entry Rg = false -> RRegion0 segs ρ (ms_mem ms) Rg.
Proof.
  intros HIn He. pose proof (r_mem _ _ _ _ _ _ _ HR) as [_ HF]. cbn [cfg_ms] in HF.
  rewrite <- (RRegion_ne segs ρ (ms_mem ms) Rg He). exact (proj1 (Forall_forall _ _) HF Rg HIn).
Qed.

(* [comment removed for export] *)
Theorem export_byte (Rg : region) (y : int) : In Rg (a_mem B) -> is_entry Rg = false -> to_Z y < to_Z (rg_n Rg) ->
  RzCPS.HID A' model (wz (rbase ρ Rg + to_Z y)) = false ->
  (exists b, Mem.mrd segs mX (wz (rbase ρ Rg + to_Z y)) = Some b /\ xb_bv ρ (rbyte segs Rg y) b)
  /\ (rk_writable (rg_kind Rg) = true -> wview segs mX (wz (rbase ρ Rg + to_Z y)) <> None).
Proof.
  intros HIn He Hy Hv. destruct (R_region Rg HIn He y Hy) as [[b [Hb Hx]] Hw]. split.
  - exists b. rewrite (vis_mrd _ Hv). split; [exact Hb | exact Hx].
  - intros Hk. rewrite (vis_wview _ Hv). exact (Hw Hk).
Qed.

(* [comment removed for export] *)
Lemma xb_lit (c : int) (b : byte) : xb_bv ρ (BL c) b -> b = Z_to_bv 8 (to_Z c).
Proof. unfold xb_bv. cbn [xb_z]. intros H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Theorem export_lit (Rg : region) (y c : int) : In Rg (a_mem B) -> is_entry Rg = false -> to_Z y < to_Z (rg_n Rg) ->
  RzCPS.HID A' model (wz (rbase ρ Rg + to_Z y)) = false -> rbyte segs Rg y = BL c ->
  Mem.mrd segs mX (wz (rbase ρ Rg + to_Z y)) = Some (Z_to_bv 8 (to_Z c)).
Proof.
  intros HIn He Hy Hv Hc. destruct (export_byte Rg y HIn He Hy Hv) as [[b [Hb Hx]] _]. rewrite Hc in Hx. rewrite (xb_lit c b Hx) in Hb. exact Hb.
Qed.

End Export.

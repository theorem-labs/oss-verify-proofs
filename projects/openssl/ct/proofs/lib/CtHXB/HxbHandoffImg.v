(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OSSVerify.Proofs.openssl.ct.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.ct.lib.B Require Import SegRw.
From OSSVerify.Proofs.openssl.ct.lib.CtB Require Import Layout R_unwind_chain RT_iface D_defs.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxImg HxQuery HxLearn.
From OSSVerify.Proofs.openssl.ct.lib.HXS Require Import HxsStep HxsStepSound HxsHookSound HxsKit.
From OSSVerify.Proofs.openssl.ct.lib.CtHXS Require Import HxsHookCt.
From OSSVerify.Proofs.openssl.ct.lib.CtHXB Require Import HxbInit HxbImage HxbIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint rom_bytes_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' => match seg_rom ctbsegs (wa A) with Some b' => (bv_unsigned b =? bv_unsigned b') && rom_bytes_b (A + 1) bs' | None => false end
  end.

Lemma view_bytes_at (m : word -> option byte) : forall (bs : list byte) (A : Z), rom_bytes_b A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> mrd ctbsegs m (wa a) = seg_rom ctbsegs (wa a)) -> bytes_at ctbsegs m A bs.
Proof.
  intros bs A Hb HA Hl Hv. split; [exact HA|]. split; [exact Hl|]. revert A Hb HA Hl Hv.
  induction bs as [|b bs IH]; intros A Hb HA Hl Hv i Hi; [cbn in Hi; lia|]. cbn [rom_bytes_b] in Hb.
  destruct (seg_rom ctbsegs (wa A)) as [b'|] eqn:E; [|discriminate]. apply andb_prop in Hb as [Hb1 Hb2]. apply Z.eqb_eq in Hb1. apply bv_eq in Hb1. subst b'.
  cbn [length] in Hl, Hv, Hi. destruct i as [|i].
  - cbn [nth_error Z.of_nat]. rewrite Z.add_0_r, (Hv A ltac:(lia)). exact E.
  - cbn [nth_error]. replace (A + Z.of_nat (Datatypes.S i)) with (A + 1 + Z.of_nat i) by lia.
    apply (IH (A + 1) Hb2 ltac:(lia) ltac:(lia)); [|lia]. intros a Ha. apply Hv. lia.
Qed.

(* [comment removed for export] *)
Lemma seg_rw_c8' (m : word -> option byte) (a : Z) : seg_rw_ok ctbsegs a 8 = true -> exists v, rw_cells ctbsegs m a [C8 v].
Proof.
  intros H. destruct (seg_rw_ok_sound ctbsegs a 8 H m) as [W S].
  destruct (stk_bytes_n ctbsegs m a 8 S) as (bs & Hl & B).
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). split; [split; [cbn; tauto|] | exact W].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le8, word_to_le_bytes.
  pose proof (AS.PropExec.bytes_le_to_Z_bound bs) as Bd. pose proof (AS.PropExec.bytes_le_to_Z_nonneg bs) as Bn. rewrite Hl in Bd.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Bd; lia).
  rewrite <- Hl at 1. rewrite Z_to_le_bytes_of_bytes. exact B.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac closed_side := first [ vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; discriminate ].

Local Ltac img_region i sg sgchunk rd wrl findl :=
  eapply (img_region_ok_view ctbsegs _ _ _ _ _ _ i _ _ sg (chunk_of sg) _ (eq_refl : nth_error ctbsegs i = Some sg) sgchunk rd);
  [ first [ intros _; exact wrl | discriminate ]
  | vm_compute; reflexivity
  | intros a Ha; apply findl; revert Ha; vm_compute (to_Z _); lia
  | apply Z.leb_le; vm_compute; reflexivity
  | vm_compute; reflexivity
  | vm_compute; reflexivity
  | idtac
  | vm_compute; reflexivity | vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; discriminate
  | vm_compute; reflexivity | vm_compute; reflexivity ].

Lemma seg_rw_errno : seg_rw_ok ctbsegs 12435852 4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg_rw_tsd_used : seg_rw_ok ctbsegs 12435866 1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg_rw_guard : seg_rw_ok ctbsegs 12567152 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma rom_pthread_zero : rom_bytes_b 12571040 (Z_to_le_bytes 1080 0) = true. Proof. vm_compute. reflexivity. Qed.

Section HandoffImg.
Variables (rho : valuation) (m : word -> option byte).
Hypothesis MI : mem_inv ctbsegs m.
Hypothesis V_relro : forall a, 5685248 <= a < 6176768 -> mrd ctbsegs m (wa a) = seg_rom ctbsegs (wa a).
Hypothesis V_lib : forall a, in_ranges LIB_PRISTINE a -> mrd ctbsegs m (wa a) = seg_rom ctbsegs (wa a).

Local Ltac lib_view Ha := apply V_lib; revert Ha; vm_compute (to_Z _); unfold in_ranges, LIB_PRISTINE; intros Ha.

Lemma rg4_ok : region_ok ctbsegs rho 4%uint63 rg_4 m.
Proof. unfold rg_4. img_region 0%nat seg0 seg0_chunk seg0_rd seg0_ro find_seg0_in. intros a Ha. unfold mrd. rewrite (ro_none m a MI); [reflexivity|]. revert Ha. vm_compute (to_Z _). lia. Qed.

Lemma rg5_ok : region_ok ctbsegs rho 5%uint63 rg_5 m.
Proof. unfold rg_5. img_region 2%nat seg2 seg2_chunk seg2_rd seg2_wr find_seg2_in. intros a Ha. apply V_relro. revert Ha. vm_compute (to_Z _). lia. Qed.

Lemma rg6_ok : region_ok ctbsegs rho 6%uint63 rg_6 m.
Proof.
  unfold rg_6. img_region 3%nat seg3 seg3_chunk seg3_rd seg3_wr find_seg3_in. intros a Ha. lib_view Ha.
  exists 0x5e74e0, 0x5e7fc0. split; [cbn [In]; tauto | lia].
Qed.

Lemma rg8_ok : region_ok ctbsegs rho 8%uint63 rg_8 m.
Proof.
  unfold rg_8. img_region 3%nat seg3 seg3_chunk seg3_rd seg3_wr find_seg3_in. intros a Ha. lib_view Ha.
  exists 0xbd7500, 0xbd7de0. split; [cbn [In]; tauto | lia].
Qed.

Lemma rg11_ok : region_ok ctbsegs rho 11%uint63 rg_11 m.
Proof.
  unfold rg_11. img_region 3%nat seg3 seg3_chunk seg3_rd seg3_wr find_seg3_in. intros a Ha. lib_view Ha.
  exists 0xbdc1d0, 0xbdc1d8. split; [cbn [In]; tauto | lia].
Qed.

Lemma rg15_ok : region_ok ctbsegs rho 15%uint63 rg_15 m.
Proof.
  unfold rg_15. img_region 3%nat seg3 seg3_chunk seg3_rd seg3_wr find_seg3_in. intros a Ha. lib_view Ha.
  exists 0xbfd5e0, 0xbfd620. split; [cbn [In]; tauto | lia].
Qed.

End HandoffImg.

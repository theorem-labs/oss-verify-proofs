(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read RT_liveprim L_libA. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt L2StmtS B0_sessK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpSess CmpSess2 CmpSessB CmpFsKit0 AsanKit AsanCut B0_b2c_cbV B0_b2c_hcV B0_b2c_wrV B0_b2c_wrE B0_b2c_wrI.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCarve BzCLemmasFs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_bs CmpCutCB DecTac2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).


Section InitK.
Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition zarr_of_junkb (J : list byte) : zarr := zarr_of_list (map bv_unsigned J).
Lemma zarr_of_junkb_get : forall J i, 0 <= i < Z.of_nat (length J) -> zget (zarr_of_junkb J) i = bv_unsigned (nth (Z.to_nat i) J (Z_to_bv 8 0)).
Proof.
  intros J i Hi. unfold zarr_of_junkb. replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia. rewrite zget_of_list by (rewrite length_map; lia).
  change 0 with (bv_unsigned (Z_to_bv 8 0)). rewrite map_nth. reflexivity.
Qed.
Lemma zarr_of_junkb_ok : forall J, zbok (zarr_of_junkb J).
Proof.
  intros J i. destruct (Z_lt_dec i 0) as [L|L]; [| destruct (Z_lt_dec i (Z.of_nat (length J))) as [L'|L']].
  - unfold zarr_of_junkb, zarr_of_list. rewrite zget_of_list_at_below by lia. rewrite zget_znew. lia.
  - rewrite zarr_of_junkb_get by lia. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) J (Z_to_bv 8 0))) as R. unfold bv_modulus in R. cbn in R. lia.
  - unfold zarr_of_junkb, zarr_of_list. rewrite CmpCutCB.zget_of_list_at_above by (rewrite length_map; lia). rewrite zget_znew. lia.
Qed.
Lemma zb8_of_junk : forall segs m A n (J : list byte), rw_cells segs m A [CB (Z.to_nat n) J] -> 0 <= n -> u8arr segs m A (zb8 (zarr_of_junkb J) n).
Proof.
  intros segs m A n J H Hn. pose proof (u8arr_of_rw_cells segs m A _ J H) as U.
  assert (LJ : length J = Z.to_nat n) by (destruct H as [[Hwf _] _]; cbn in Hwf; destruct Hwf as [HL _]; exact HL).
  replace (zb8 (zarr_of_junkb J) n) with J; [exact U|].
  apply nth_error_ext. intros k. destruct (Nat.lt_ge_cases k (Z.to_nat n)) as [L|Gk].
  - replace k with (Z.to_nat (Z.of_nat k)) at 2 by lia. rewrite zb8_nth by lia. rewrite zarr_of_junkb_get by lia. rewrite Nat2Z.id, definitions.Z_to_bv_bv_unsigned.
    apply nth_error_nth'. lia.
  - rewrite (proj2 (nth_error_None _ _)) by lia. rewrite (proj2 (nth_error_None _ _)) by (rewrite zb8_length_nat; lia). reflexivity.
Qed.

(* [comment removed for export] *)
#[local] Transparent jw.
Lemma jw_range : forall J k, 0 <= bv_unsigned (jw J k) < 4294967296.
Proof.
  intros J k. unfold jw, le_bytes_to_word. set (bs := firstn 4 (skipn (Z.to_nat (4 * k)) J)).
  assert (LB : (length bs <= 4)%nat) by (unfold bs; rewrite length_firstn; lia).
  rewrite ZBridge.Bytes.bytes_le_to_Z_le_val.
  assert (BO : ZBridge.Bytes.bytes_ok (map bv_unsigned bs)).
  { apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (b & <- & _). pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. }
  pose proof (ZBridge.Bytes.le_val_range _ BO) as R. rewrite length_map in R.
  assert (256 ^ Z.of_nat (length bs) <= 4294967296).
  { change 4294967296 with (256 ^ 4). apply Z.pow_le_mono_r; lia. }
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [lia|]. cbn. lia.
Qed.
#[local] Opaque jw.
Lemma zarr_of_junkw_w32 : forall J n, 0 <= n -> bh_w32 (S0_cmp_bs.zarr_of_junkw J n).
Proof.
  intros J n Hn i. destruct (Z_lt_dec i 0) as [L|L]; [| destruct (Z_lt_dec i n) as [L'|L']].
  - unfold S0_cmp_bs.zarr_of_junkw, zarr_of_list. rewrite zget_of_list_at_below by lia. rewrite zget_znew. lia.
  - rewrite S0_cmp_bs.zarr_of_junkw_get by lia. apply jw_range.
  - unfold S0_cmp_bs.zarr_of_junkw, zarr_of_list. rewrite CmpCutCB.zget_of_list_at_above by (rewrite length_map, length_seq; lia). rewrite zget_znew. lia.
Qed.

(* [comment removed for export] *)
Definition ESHAPE1A : list nat := [8; 4; 4; 4; 4; 8; 8; 8; 4; 4; 8; 8; 8; 8; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4]%nat.
Definition ESHAPE2A : list nat := [4; 4; 4; 4; 4; 4; 4; 4]%nat.
Lemma EJ1wA_jcells : forall J, jcells J 0 ESHAPE1A = EJ1wA J (jw8 J 0) (jw8 J 24) (jw8 J 32) (jw8 J 40).
Proof. reflexivity. Qed.
Lemma EJ2A_jcells : forall J, jcells J 640 ESHAPE2A = EJ2A J.
Proof. reflexivity. Qed.
Definition EL3A (J : list byte) : list cell :=
  jcells J 0 ESHAPE1A ++ [CB 256 (jseg J 128 256); CB 256 (jseg J 384 256)] ++ jcells J 640 ESHAPE2A ++ [CB (Z.to_nat 55096) (jseg J 672 55096)].
Lemma estate_carveA : forall segs m E J,
  rw_cells segs m E [CB (Z.to_nat 55768) J] -> Z.of_nat (length J) = 55768 ->
  rw_cells segs m E (EJ1wA J (jw8 J 0) (jw8 J 24) (jw8 J 32) (jw8 J 40)) /\
  rw_cells segs m (E + 128) [CB 256 (jseg J 128 256)] /\
  rw_cells segs m (E + 384) [CB 256 (jseg J 384 256)] /\
  rw_cells segs m (E + 640) (EJ2A J) /\
  rw_cells segs m (E + 672) [CB (Z.to_nat 55096) (jseg J 672 55096)].
Proof.
  intros segs m E J H LJ.
  assert (X : rw_cells segs m E (EL3A J)).
  { eapply carve_cb; [exact H | | |].
    - unfold EL3A. rewrite !cells_wf_app.
      repeat match goal with |- _ /\ _ => split end;
      first [ apply jcells_wf; cbn [sum_nat ESHAPE1A ESHAPE2A Nat.add]; zlit; lia
            | cbn [cells_wf cell_wf]; rewrite ?jseg_length_nat by lia; repeat split; reflexivity ].
    - unfold EL3A. rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite !app_nil_r.
      rewrite !jcells_bytes by (cbn [sum_nat ESHAPE1A ESHAPE2A Nat.add length]; zlit; lia). cbn [sum_nat ESHAPE1A ESHAPE2A Nat.add]. zlit.
      rewrite <- ?app_assoc. etransitivity; [| exact (jseg_all J 55768 LJ)].
      rewrite (jseg_cat J 640 32 672 55096 55128) by lia. rewrite (jseg_cat J 384 256 640 55128 55384) by lia.
      rewrite (jseg_cat J 128 256 384 55384 55640) by lia. rewrite (jseg_cat J 0 128 128 55640 55768) by lia. reflexivity.
    - unfold EL3A. rewrite !cells_size_app, !jcells_size. reflexivity. }
  unfold EL3A in X.
  apply (proj1 (DecTac2.rw_cells_app_iff segs m E _ _)) in X. destruct X as [X1 X]. rewrite jcells_size in X. cbn [sum_nat Nat.add ESHAPE1A] in X. zlit_in X.
  apply (proj1 (rw_cells_cons_iff _ _ _ _ _)) in X. destruct X as [X2 X]. cbn [csize] in X. rewrite <- ?Z.add_assoc in X. zlit_in X.
  apply (proj1 (rw_cells_cons_iff _ _ _ _ _)) in X. destruct X as [X3 X]. cbn [csize] in X. rewrite <- ?Z.add_assoc in X. zlit_in X.
  apply (proj1 (DecTac2.rw_cells_app_iff segs m _ _ _)) in X. destruct X as [X4 X5]. rewrite jcells_size in X5. cbn [sum_nat Nat.add ESHAPE2A] in X5. zlit_in X5.
  rewrite <- ?Z.add_assoc in X5. zlit_in X5.
  rewrite EJ1wA_jcells in X1. rewrite EJ2A_jcells in X4.
  split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4| exact X5].
Qed.
End InitK.

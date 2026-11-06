(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjAlloc.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim Stdio SjModel AtpModel OdModel.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_new
  Atp_h_defsA Od_hkit0A Od_lkitB Od_setup_defsB Od_setupkB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma z8_inj : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z_to_bv 8 a = Z_to_bv 8 b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
  rewrite !bv_wrap_small in E by (unfold bv_modulus; cbn; lia). exact E.
Qed.

Lemma strip_bom_cases : forall s : list Z, bytes_ok s -> (3 <= length s)%nat ->
  (firstn 3 (zbytes s) = BOM_BYTES /\ strip_bom s = skipn 3 s /\ zlength (strip_bom s) = zlength s - 3)
  \/ (firstn 3 (zbytes s) <> BOM_BYTES /\ strip_bom s = s).
Proof.
  intros s OK L. destruct s as [|a [|b [|c r]]]; cbn [length] in L; try lia.
  inversion OK as [|? ? Ra OK1]; subst. inversion OK1 as [|? ? Rb OK2]; subst. inversion OK2 as [|? ? Rc _]; subst.
  destruct (Z.eq_dec a 239) as [Ea|Na]; [destruct (Z.eq_dec b 187) as [Eb|Nb]; [destruct (Z.eq_dec c 191) as [Ec|Nc]|]|].
  - left. subst. split; [reflexivity|]. split; [reflexivity|]. cbn [strip_bom]. unfold zlength. cbn [length]. lia.
  - right. split.
    + cbn [zbytes map firstn]. unfold BOM_BYTES. intros E. apply Nc. apply (z8_inj c 191 Rc ltac:(lia)). exact (f_equal (fun l => nth 2 l (Z_to_bv 8 0)) E).
    + subst. cbn [strip_bom]. destruct c as [|pc|pc]; try reflexivity.
      repeat (destruct pc as [pc|pc|]; try reflexivity). contradiction Nc. reflexivity.
  - right. split.
    + cbn [zbytes map firstn]. unfold BOM_BYTES. intros E. apply Nb. apply (z8_inj b 187 Rb ltac:(lia)). exact (f_equal (fun l => nth 1 l (Z_to_bv 8 0)) E).
    + subst. cbn [strip_bom]. destruct b as [|pb|pb]; try reflexivity.
      repeat (destruct pb as [pb|pb|]; try reflexivity). contradiction Nb. reflexivity.
  - right. split.
    + cbn [zbytes map firstn]. unfold BOM_BYTES. intros E. apply Na. apply (z8_inj a 239 Ra ltac:(lia)). exact (f_equal (fun l => nth 0 l (Z_to_bv 8 0)) E).
    + cbn [strip_bom]. destruct a as [|pa|pa]; try reflexivity.
      repeat (destruct pa as [pa|pa|]; try reflexivity). contradiction Na. reflexivity.
Qed.

Lemma strip_bom_short : forall s : list Z, (length s < 3)%nat -> strip_bom s = s.
Proof. intros s L. destruct s as [|a [|b [|c r]]]; cbn [length] in L; try lia; cbn [strip_bom]; try reflexivity.
  - destruct a as [|pa|pa]; try reflexivity. repeat (destruct pa as [pa|pa|]; try reflexivity).
  - destruct a as [|pa|pa]; try reflexivity. repeat (destruct pa as [pa|pa|]; try reflexivity).
    destruct b as [|pb|pb]; try reflexivity. repeat (destruct pb as [pb|pb|]; try reflexivity).
Qed.

Lemma od_s0_ok : forall dz, bytes_ok dz -> bytes_ok (od_s0 dz).
Proof.
  intros dz OK. destruct (oa_els_shape 0 (tl dz)) as (_ & _ & _ & _ & PREF).
  unfold od_s0, od_parts, od_rest. rewrite PREF. unfold bytes_ok in *.
  assert (T : Forall (fun b => 0 <= b < 256) (tl dz)) by (destruct dz as [|c l]; cbn [tl]; [exact OK| inversion OK; assumption]).
  rewrite <- (firstn_skipn (length (nth 0 (atp_parts (tl dz)) [])) (tl dz)) in T. apply Forall_app in T. exact (proj1 T).
Qed.

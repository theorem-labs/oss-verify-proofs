(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk StreamSim WsegFast CoverFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMem VStepMemSound VParamsCheck.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Lemma bytes_ok_intro (f : Z -> bool) n : forall a, (forall x, a <= x < a + Z.of_nat n -> f x = true) -> VParamsCheck.bytes_ok f a n = true.
Proof.
  induction n as [|n IH]; intros a H; [reflexivity|].
  cbn [VParamsCheck.bytes_ok]. rewrite (H a ltac:(lia)). cbn [andb]. apply IH. intros x Hx. apply H. lia.
Qed.

Lemma wordZ_unsigned x : 0 <= x < 2 ^ 64 -> bv_unsigned (wordZ x) = x.
Proof. intros H. unfold wordZ. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Lemma readable1_of_seg SEGS x seg :
  0 <= x < 2 ^ 64 -> find_segment SEGS x 1 = Some seg -> seg_readable seg = true -> byte_def seg x ->
  readable1 SEGS x = true.
Proof.
  intros Hx Hf Hr [b Hb]. unfold readable1, seg_rom, memory_read.
  rewrite (wordZ_unsigned x Hx). change (Z.of_N 1) with 1. rewrite Hf, Hr.
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite Hb. reflexivity.
Qed.

Lemma writable1_of_seg SEGS x seg :
  0 <= x < 2 ^ 64 -> find_segment SEGS x 1 = Some seg -> seg_writable seg = true -> byte_def seg x ->
  writable1 SEGS x = true.
Proof.
  intros Hx Hf Hw [b Hb]. unfold writable1. apply store_ok_wseg.
  cbn [wseg_ok]. rewrite (wordZ_unsigned x Hx), Hf, Hw, Hb. reflexivity.
Qed.

Definition rw_seg (s : Segment) : bool := (seg_writable s && seg_readable s)%bool.

Definition params_check_imgF (SEGS : list Segment) (frame : Z) (fcells segs pristine : list (Z * Z)) (rom : pmap Z)
           (splo sphi : Z) : bool :=
  Z.leb 0 frame && Z.ltb sphi C64
  && forallb (fun r : Z * Z => Z.leb 0 (fst r) && Z.leb (snd r) (splo - frame)
                               && range_cover seg_readable SEGS (fst r) (Z.to_nat (snd r - fst r))) segs
  && forallb (fun c : Z * Z => Z.leb 0 (fst c) && Z.leb (fst c + snd c) (splo - frame)
                               && range_cover rw_seg SEGS (fst c) (Z.to_nat (snd c))
                               && forallb (fun r : Z * Z => Z.leb (snd r) (fst c) || Z.leb (fst c + snd c) (fst r)) pristine)
             fcells
  && forallb (fun r : Z * Z => Z.leb 0 (fst r) && Z.leb (snd r) (splo - frame)) pristine
  && pm_forallb (fun k b => let a := Z.pos k in
                            in_ranges pristine a 1 &&
                            match seg_rom SEGS (wordZ a) with Some bb => Z.eqb (bv_unsigned bb) b | None => false end) rom.

Definition params_checkF (SEGS : list Segment) (P : vparams) : bool :=
  params_check_imgF SEGS (vp_frame P) (vp_fcells P) (vp_segs P) (vp_pristine P) (vp_rom P) (vp_splo P) (vp_sphi P)
  && params_check_unit P.

Lemma forallb_imp {A} (f g : A -> bool) l : (forall x, f x = true -> g x = true) -> forallb f l = true -> forallb g l = true.
Proof. intros H. induction l as [|a l IH]; [reflexivity|]. cbn [forallb]. intros E. apply andb_prop in E as [E1 E2]. rewrite (H _ E1), (IH E2). reflexivity. Qed.

Lemma params_check_imgF_imp SEGS frame fcells segs pristine rom splo sphi :
  params_check_imgF SEGS frame fcells segs pristine rom splo sphi = true ->
  params_check_img SEGS frame fcells segs pristine rom splo sphi = true.
Proof.
  unfold params_check_imgF, params_check_img. intros H.
  apply andb_prop in H as [H Hrom]. apply andb_prop in H as [H Hpr]. apply andb_prop in H as [H Hfc].
  apply andb_prop in H as [H0 Hsegs].
  rewrite H0, Hpr, Hrom. cbn [andb]. rewrite !andb_true_r.
  apply andb_true_intro. split.
  - revert Hsegs. apply forallb_imp. intros r E. apply andb_prop in E as [E Hc]. rewrite E. cbn [andb].
    apply bytes_ok_intro. intros x Hx.
    destruct (range_cover_sound _ _ _ _ Hc x Hx) as [Hx64 [seg [Hf [HP Hb]]]].
    exact (readable1_of_seg SEGS x seg Hx64 Hf HP Hb).
  - revert Hfc. apply forallb_imp. intros c E. apply andb_prop in E as [E Hp]. apply andb_prop in E as [E Hc].
    rewrite E, Hp. cbn [andb]. rewrite andb_true_r.
    apply bytes_ok_intro. intros x Hx.
    destruct (range_cover_sound _ _ _ _ Hc x Hx) as [Hx64 [seg [Hf [HP Hb]]]].
    unfold rw_seg in HP. apply andb_prop in HP as [HW HR].
    rewrite (writable1_of_seg SEGS x seg Hx64 Hf HW Hb), (readable1_of_seg SEGS x seg Hx64 Hf HR Hb). reflexivity.
Qed.

Theorem params_checkF_imp SEGS P : params_checkF SEGS P = true -> params_check SEGS P = true.
Proof.
  unfold params_checkF, params_check. intros H. apply andb_prop in H as [H1 H2].
  rewrite (params_check_imgF_imp _ _ _ _ _ _ _ _ H1), H2. reflexivity.
Qed.

Corollary params_check_soundF' SEGS P : params_checkF SEGS P = true -> params_ok SEGS P.
Proof. intros H. exact (params_check_sound' SEGS P (params_checkF_imp SEGS P H)). Qed.

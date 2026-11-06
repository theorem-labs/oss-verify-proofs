(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMem VStepMemSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint bytes_ok (f : Z -> bool) (a : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => f a && bytes_ok f (a + 1) n'
  end.

Lemma bytes_ok_sound f n : forall a, bytes_ok f a n = true -> forall x, a <= x < a + Z.of_nat n -> f x = true.
Proof.
  induction n as [|n IH]; intros a H x Hx; [lia|].
  cbn [bytes_ok] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec x a) as [->|Hne]; [exact H1|]. apply (IH (a + 1) H2). lia.
Qed.

Definition readable1 (SEGS : list Segment) (a : Z) : bool :=
  match seg_rom SEGS (wordZ a) with Some _ => true | None => false end.

Definition writable1 (SEGS : list Segment) (a : Z) : bool :=
  store_ok SEGS (fun _ => None) (wordZ a) 1.

Lemma readable1_sound SEGS a : readable1 SEGS a = true -> exists b, rdn SEGS (fun _ => None) (wordZ a) 1 = Some [b].
Proof.
  unfold readable1. rewrite rdn_1. destruct (seg_rom SEGS (wordZ a)) as [b|]; [|discriminate]. intros _. exists b. reflexivity.
Qed.

(* [comment removed for export] *)
Definition params_check_img (SEGS : list Segment) (frame : Z) (fcells segs pristine : list (Z * Z)) (rom : pmap Z)
           (splo sphi : Z) : bool :=
  Z.leb 0 frame && Z.ltb sphi C64
  && forallb (fun r : Z * Z => Z.leb 0 (fst r) && Z.leb (snd r) (splo - frame)
                               && bytes_ok (readable1 SEGS) (fst r) (Z.to_nat (snd r - fst r))) segs
  && forallb (fun c : Z * Z => Z.leb 0 (fst c) && Z.leb (fst c + snd c) (splo - frame)
                               && bytes_ok (fun a => writable1 SEGS a && readable1 SEGS a) (fst c) (Z.to_nat (snd c))
                               && forallb (fun r : Z * Z => Z.leb (snd r) (fst c) || Z.leb (fst c + snd c) (fst r)) pristine)
             fcells
  && forallb (fun r : Z * Z => Z.leb 0 (fst r) && Z.leb (snd r) (splo - frame)) pristine
  && pm_forallb (fun k b => let a := Z.pos k in
                            in_ranges pristine a 1 &&
                            match seg_rom SEGS (wordZ a) with Some bb => Z.eqb (bv_unsigned bb) b | None => false end) rom.

(* [comment removed for export] *)
Definition params_check_unit (P : vparams) : bool :=
  forallb (fun c : Z * Z => existsb (fun f : Z * Z => Z.leb (fst f) (fst c) && Z.leb (fst c + snd c) (fst f + snd f)) (vp_fcells P))
          (vp_wcells P)
  && forallb (fun r : Z * Z => Z.leb (- vp_frame P) (fst r) && Z.leb (snd r) 0) (vp_wstack P).

Definition params_check (SEGS : list Segment) (P : vparams) : bool :=
  params_check_img SEGS (vp_frame P) (vp_fcells P) (vp_segs P) (vp_pristine P) (vp_rom P) (vp_splo P) (vp_sphi P)
  && params_check_unit P.

Local Ltac bprop H :=
  repeat match type of H with
         | (_ && _) = true => apply andb_prop in H; destruct H as [H ?]
         end.

Theorem params_check_sound SEGS P :
  params_check_img SEGS (vp_frame P) (vp_fcells P) (vp_segs P) (vp_pristine P) (vp_rom P) (vp_splo P) (vp_sphi P) = true ->
  params_check_unit P = true ->
  params_ok SEGS P.
Proof.
  intros HI HU. unfold params_check_img in HI. unfold params_check_unit in HU.
  apply andb_prop in HI as [HI Hrom]. apply andb_prop in HI as [HI Hpr]. apply andb_prop in HI as [HI Hfc].
  apply andb_prop in HI as [HI Hsegs]. apply andb_prop in HI as [Hfr Hsphi].
  apply andb_prop in HU as [Hwc Hws].
  apply Z.leb_le in Hfr. apply Z.ltb_lt in Hsphi. rewrite C64_eq in Hsphi.
  unfold params_ok. split; [exact Hfr|]. split; [exact Hsphi|].
  split; [|split; [|split; [|split; [|split]]]].
  - intros lo hi Hin. pose proof (proj1 (forallb_forall _ _) Hsegs _ Hin) as H. cbn [fst snd] in H.
    apply andb_prop in H as [H Hb]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    split; [exact H1|]. split; [exact H2|]. intros a Ha. apply readable1_sound.
    apply (bytes_ok_sound _ _ _ Hb). rewrite Z2Nat.id by lia. lia.
  - intros c Hin. pose proof (proj1 (forallb_forall _ _) Hfc _ Hin) as H.
    apply andb_prop in H as [H Hp]. apply andb_prop in H as [H Hb]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    split; [exact H1|]. split; [exact H2|]. split.
    + intros a Ha.
      assert (Hn : 0 <= snd c) by lia.
      pose proof (bytes_ok_sound _ _ _ Hb a ltac:(rewrite Z2Nat.id by lia; lia)) as X. cbn beta in X.
      apply andb_prop in X as [X1 X2]. split; [exact X1|apply readable1_sound; exact X2].
    + intros lo hi Hp'. pose proof (proj1 (forallb_forall _ _) Hp _ Hp') as X. cbn [fst snd] in X.
      apply orb_prop in X. destruct X as [X|X]; apply Z.leb_le in X; [left|right]; exact X.
  - intros c Hin. pose proof (proj1 (forallb_forall _ _) Hwc _ Hin) as H.
    apply existsb_exists in H as [f [Hf H]]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    exists f. split; [exact Hf|]. split; [exact H1|exact H2].
  - intros r Hin. pose proof (proj1 (forallb_forall _ _) Hws _ Hin) as H.
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. split; [exact H1|exact H2].
  - intros lo hi Hin. pose proof (proj1 (forallb_forall _ _) Hpr _ Hin) as H. cbn [fst snd] in H.
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. split; [exact H1|exact H2].
  - intros a b Ha Hg.
    pose proof (pm_forallb_sound _ _ Hrom _ Hg) as H. cbn beta in H. rewrite Z2Pos.id in H by exact Ha.
    apply andb_prop in H as [H1 H2]. split; [exact H1|].
    destruct (seg_rom SEGS (wordZ a)) as [bb|]; [|discriminate]. apply Z.eqb_eq in H2. exists bb. split; [reflexivity|exact H2].
Qed.

Corollary params_check_sound' SEGS P : params_check SEGS P = true -> params_ok SEGS P.
Proof.
  unfold params_check. intros H. apply andb_prop in H as [H1 H2]. exact (params_check_sound SEGS P H1 H2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition segs_wr_readable (SEGS : list Segment) : bool :=
  forallb (fun seg => negb (seg_writable seg) || seg_readable seg) SEGS.

Lemma find_segment_In segs x n seg : find_segment segs x n = Some seg -> In seg segs.
Proof.
  induction segs as [|s t IH]; cbn [find_segment]; [discriminate|].
  destruct (Z.leb _ _ && Z.leb _ _); [intros H; injection H as ->; now left|intros H; right; exact (IH H)].
Qed.

Lemma store_ok1_rdn SEGS mem (a : word) :
  segs_wr_readable SEGS = true -> store_ok SEGS mem a 1 = true -> exists b, rdn SEGS mem a 1 = Some [b].
Proof.
  intros Hwr Hok. rewrite rdn_1. cbn [store_ok] in Hok. unfold wview in Hok.
  destruct (mem a) as [b|] eqn:Em; [exists b; reflexivity|].
  destruct (find_segment SEGS (bv_unsigned a) 1) as [seg|] eqn:Ef; [|discriminate].
  destruct (seg_writable seg) eqn:Ew; [|discriminate].
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Eb; [|discriminate].
  pose proof (proj1 (forallb_forall _ _) Hwr _ (find_segment_In _ _ _ _ Ef)) as Hr. cbn beta in Hr. rewrite Ew in Hr. cbn [negb orb] in Hr.
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite Ef, Hr.
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite Eb. exists b. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma frame_store_ok_readable SEGS mem lo hi :
  segs_wr_readable SEGS = true ->
  (forall a : word, lo <= bv_unsigned a < hi -> store_ok SEGS mem a 1 = true) ->
  0 <= lo -> hi <= 2 ^ 64 ->
  forall a, lo <= a < hi -> store_ok SEGS mem (wordZ a) 1 = true /\ exists b, rdn SEGS mem (wordZ a) 1 = Some [b].
Proof.
  intros Hwr Hok Hlo Hhi a Ha.
  assert (Hu : bv_unsigned (wordZ a) = a) by (apply u_wordZ; lia).
  pose proof (Hok (wordZ a) ltac:(rewrite Hu; lia)) as H1. split; [exact H1|]. exact (store_ok1_rdn _ _ _ Hwr H1).
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import MainExport.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Reader.
Variable segs : list Segment.

Definition bval (V : nat -> Z) (B : option zexp) : Z := match B with None => 0 | Some b => zv V b end.

(* [comment removed for export] *)
Definition aoff (B : option zexp) (a : zexp) : option Z :=
  match B with
  | None => match a with ZLit a0 => Some a0 | _ => None end
  | Some b =>
      if zexp_eqb a b then Some 0
      else match a with
           | ZAdd b' (ZLit k) => if zexp_eqb b' b then Some k else None
           | _ => None
           end
  end.

Lemma aoff_sound : forall V B a k, aoff B a = Some k -> zv V a = bval V B + k.
Proof.
  intros V [b|] a k H; cbn [aoff bval] in *.
  - destruct (zexp_eqb a b) eqn:E.
    + apply zexp_eqb_eq in E. subst a. injection H as <-. lia.
    + destruct a as [z|n|b' c|p q|p q|p q]; try discriminate. destruct c as [k'|n|p q|p q|p q|p q]; try discriminate.
      destruct (zexp_eqb b' b) eqn:E'; [|discriminate]. apply zexp_eqb_eq in E'. subst b'. injection H as <-. reflexivity.
  - destruct a as [z|n|p q|p q|p q|p q]; try discriminate. injection H as <-. cbn [zv]. lia.
Qed.

Definition inr (k n x : Z) : bool := (k <=? x) && (x <? k + n).
Lemma inr_true : forall k n x, inr k n x = true -> k <= x < k + n.
Proof. intros k n x H. unfold inr in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. Qed.

(* [comment removed for export] *)
Definition fbyte (B : option zexp) (f : mfact) (x : Z) : option byte :=
  match f with
  | MCell a w (ZLit v) =>
      match aoff B a with
      | Some k => if inr k (Z.of_nat w) x then nth_error (cbytes (cellw w v)) (Z.to_nat (x - k)) else None
      | None => None end
  | MRo a w (ZLit v) =>
      match aoff B a with
      | Some k => if inr k (Z.of_nat w) x then nth_error (word_to_le_bytes w (Z_to_bv 64 v)) (Z.to_nat (x - k)) else None
      | None => None end
  | MZeroC a n => match aoff B a with Some k => if inr k n x then Some (Z_to_bv 8 0) else None | None => None end
  | MZero a n => match aoff B a with Some k => if inr k n x then Some (Z_to_bv 8 0) else None | None => None end
  | MFill a n c => match aoff B a with Some k => if inr k n x then Some (Z_to_bv 8 c) else None | None => None end
  | MImg lo hi => match B with None => if inr lo (hi - lo) x then seg_rom segs (wa x) else None | Some _ => None end
  | _ => None
  end.

(* [comment removed for export] *)
Definition frel (B : option zexp) (x n : Z) (f : mfact) : bool :=
  let ov k l := (k <? x + n) && (x <? k + l) in
  match f with
  | MCell a w _ | MRo a w _ => match aoff B a with Some k => ov k (Z.of_nat w) | None => false end
  | MZeroC a l | MZero a l | MFill a l _ => match aoff B a with Some k => ov k l | None => false end
  | MImg lo hi => match B with None => ov lo (hi - lo) | Some _ => false end
  | _ => false
  end.

Fixpoint fread (B : option zexp) (MF : list mfact) (x : Z) : option byte :=
  match MF with
  | [] => None
  | f :: r => match fbyte B f x with Some b => Some b | None => fread B r x end
  end.

Fixpoint fbytes_go (B : option zexp) (F : list mfact) (x : Z) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' => match fread B F x with
            | Some b => match fbytes_go B F (x + 1) n' with Some r => Some (b :: r) | None => None end
            | None => None
            end
  end.

Definition fbytes (B : option zexp) (MF : list mfact) (x : Z) (n : nat) : option (list byte) :=
  fbytes_go B (List.filter (frel B x (Z.of_nat n)) MF) x n.

Fixpoint beqs (l1 l2 : list byte) : bool :=
  match l1, l2 with
  | [], [] => true
  | b1 :: r1, b2 :: r2 => bv_eqb b1 b2 && beqs r1 r2
  | _, _ => false
  end.
Lemma beqs_eq : forall l1 l2, beqs l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|b1 r1 IH]; intros [|b2 r2] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [Hb H]. unfold bv_eqb in Hb. apply Z.eqb_eq in Hb. apply bv_eq in Hb. subst b2.
  f_equal. apply IH. exact H.
Qed.

Definition fchk (B : option zexp) (MF : list mfact) (x : Z) (bs : list byte) : bool :=
  match fbytes B MF x (length bs) with Some bs' => beqs bs bs' | None => false end.
Definition fcov (B : option zexp) (MF : list mfact) (x : Z) (n : nat) : bool :=
  match fbytes B MF x n with Some _ => true | None => false end.

Lemma nth_error_zeros : forall n i b, nth_error (zeros n) i = Some b -> b = Z_to_bv 8 0.
Proof. intros n i b H. unfold zeros in H. apply nth_error_In in H. apply repeat_spec in H. exact H. Qed.

Lemma fbyte_sound : forall V m B f x b, mfact_ok segs V m f -> 0 <= bval V B + x < 2 ^ 64 -> fbyte B f x = Some b ->
  mrd segs m (wa (bval V B + x)) = Some b.
Proof.
  intros V m B f x b Hf Hx H.
  destruct f as [a w v|a k|a w v|a k|a k c|lo hi|a k|a k|a k]; cbn [fbyte] in H; try discriminate.
  - (* [comment removed for export] *) destruct v as [v|n|p q|p q|p q|p q]; try discriminate.
    destruct (aoff B a) as [k|] eqn:Ea; [|discriminate]. destruct (inr k (Z.of_nat w) x) eqn:Er; [|discriminate].
    apply inr_true in Er. pose proof (aoff_sound V B a k Ea) as Ez.
    cbn [mfact_ok zv] in Hf. destruct Hf as [[Hwf (B0 & B1 & HB)] _].
    cbn [cells_bytes] in HB. rewrite app_nil_r in HB.
    assert (Hlen : (Z.to_nat (x - k) < length (cbytes (cellw w v)))%nat) by (apply nth_error_Some; rewrite H; discriminate).
    pose proof (HB _ Hlen) as Hb. rewrite H in Hb.
    replace (zv V a + Z.of_nat (Z.to_nat (x - k))) with (bval V B + x) in Hb by lia. exact Hb.
  - (* [comment removed for export] *) destruct (aoff B a) as [k0|] eqn:Ea; [|discriminate]. destruct (inr k0 k x) eqn:Er; [|discriminate].
    apply inr_true in Er. pose proof (aoff_sound V B a k0 Ea) as Ez. injection H as <-.
    cbn [mfact_ok] in Hf. destruct Hf as [[Hwf (B0 & B1 & HB)] _].
    cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
    cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
    assert (Hi : (Z.to_nat (x - k0) < length (zeros k))%nat) by (rewrite Hl; lia).
    pose proof (HB _ Hi) as Hb. replace (zv V a + Z.of_nat (Z.to_nat (x - k0))) with (bval V B + x) in Hb by lia.
    destruct (nth_error (zeros k) (Z.to_nat (x - k0))) as [z|] eqn:Ez'; [| apply nth_error_None in Ez'; lia].
    rewrite (nth_error_zeros _ _ _ Ez') in Hb. exact Hb.
  - (* [comment removed for export] *) destruct v as [v|n|p q|p q|p q|p q]; try discriminate.
    destruct (aoff B a) as [k|] eqn:Ea; [|discriminate]. destruct (inr k (Z.of_nat w) x) eqn:Er; [|discriminate].
    apply inr_true in Er. pose proof (aoff_sound V B a k Ea) as Ez.
    cbn [mfact_ok zv] in Hf. destruct Hf as (B0 & B1 & HB).
    assert (Hlen : (Z.to_nat (x - k) < length (word_to_le_bytes w (Z_to_bv 64 v)))%nat) by (apply nth_error_Some; rewrite H; discriminate).
    pose proof (HB _ Hlen) as Hb. rewrite H in Hb.
    replace (zv V a + Z.of_nat (Z.to_nat (x - k))) with (bval V B + x) in Hb by lia. exact Hb.
  - (* [comment removed for export] *) destruct (aoff B a) as [k0|] eqn:Ea; [|discriminate]. destruct (inr k0 k x) eqn:Er; [|discriminate].
    apply inr_true in Er. pose proof (aoff_sound V B a k0 Ea) as Ez. injection H as <-.
    cbn [mfact_ok] in Hf. specialize (Hf (x - k0) ltac:(lia)).
    replace (zv V a + (x - k0)) with (bval V B + x) in Hf by lia. unfold mrd. rewrite Hf. reflexivity.
  - (* [comment removed for export] *) destruct (aoff B a) as [k0|] eqn:Ea; [|discriminate]. destruct (inr k0 k x) eqn:Er; [|discriminate].
    apply inr_true in Er. pose proof (aoff_sound V B a k0 Ea) as Ez. injection H as <-.
    cbn [mfact_ok] in Hf. specialize (Hf (x - k0) ltac:(lia)).
    replace (zv V a + (x - k0)) with (bval V B + x) in Hf by lia. unfold mrd. rewrite Hf. reflexivity.
  - (* [comment removed for export] *) destruct B as [b0|]; [discriminate|]. destruct (inr lo (hi - lo) x) eqn:Er; [|discriminate].
    apply inr_true in Er. cbn [mfact_ok] in Hf. specialize (Hf x ltac:(lia)). cbn [bval]. rewrite Z.add_0_l.
    unfold mrd. rewrite Hf. exact H.
Qed.

Lemma fread_sound : forall V m B MF x b, Forall (mfact_ok segs V m) MF -> 0 <= bval V B + x < 2 ^ 64 -> fread B MF x = Some b ->
  mrd segs m (wa (bval V B + x)) = Some b.
Proof.
  intros V m B MF x b HF Hx. induction MF as [|f r IH]; intros H; cbn [fread] in H; [discriminate|].
  apply Forall_cons_iff in HF as [Hf HF]. destruct (fbyte B f x) as [b'|] eqn:E.
  - injection H as <-. exact (fbyte_sound V m B f x b' Hf Hx E).
  - exact (IH HF H).
Qed.

Lemma fbytes_go_sound : forall V m B F n x bs, Forall (mfact_ok segs V m) F ->
  0 <= bval V B + x -> bval V B + x + Z.of_nat n <= 2 ^ 64 -> fbytes_go B F x n = Some bs ->
  length bs = n /\ forall i, (i < n)%nat -> mrd segs m (wa (bval V B + x + Z.of_nat i)) = nth_error bs i.
Proof.
  intros V m B F. induction n as [|n IH]; intros x bs HF H0 H1 H; cbn [fbytes_go] in H.
  - injection H as <-. split; [reflexivity|]. intros i Hi. lia.
  - destruct (fread B F x) as [b|] eqn:Ef; [|discriminate].
    destruct (fbytes_go B F (x + 1) n) as [r|] eqn:Eg; [|discriminate]. injection H as <-.
    destruct (IH (x + 1) r HF ltac:(lia) ltac:(lia) Eg) as [Hl Hr]. split; [cbn; lia|].
    intros [|i] Hi.
    + cbn [nth_error]. rewrite Z.add_0_r. apply (fread_sound V m B F x b HF); [lia| exact Ef].
    + cbn [nth_error]. replace (bval V B + x + Z.of_nat (S i)) with (bval V B + (x + 1) + Z.of_nat i) by lia.
      apply Hr. lia.
Qed.

Theorem rd_bytes : forall V m B MF x n bs, Forall (mfact_ok segs V m) MF ->
  0 <= bval V B + x -> bval V B + x + Z.of_nat n <= 2 ^ 64 -> fbytes B MF x n = Some bs ->
  length bs = n /\ bytes_at segs m (bval V B + x) bs.
Proof.
  intros V m B MF x n bs HF H0 H1 H. unfold fbytes in H.
  assert (HF' : Forall (mfact_ok segs V m) (List.filter (frel B x (Z.of_nat n)) MF)).
  { apply Forall_forall. intros f Hf. apply filter_In in Hf as [Hf _]. exact (proj1 (Forall_forall _ _) HF f Hf). }
  destruct (fbytes_go_sound V m B _ n x bs HF' H0 H1 H) as [Hl Hr]. split; [exact Hl|].
  split; [exact H0|]. split; [rewrite Hl; exact H1|]. intros i Hi. apply Hr. lia.
Qed.

(* [comment removed for export] *)
Theorem rd_chunk : forall V m B MF x cs, Forall (mfact_ok segs V m) MF -> cells_wf cs ->
  fchk B MF x (cells_bytes cs) = true ->
  0 <= bval V B + x -> bval V B + x + Z.of_nat (cells_size cs) <= 2 ^ 64 -> cells_at segs m (bval V B + x) cs.
Proof.
  intros V m B MF x cs HF Hwf Hc H0 H1. unfold fchk in Hc.
  destruct (fbytes B MF x (length (cells_bytes cs))) as [bs'|] eqn:E; [|discriminate]. apply beqs_eq in Hc. subst bs'.
  assert (El : length (cells_bytes cs) = cells_size cs) by (apply cells_bytes_length; exact Hwf).
  split; [exact Hwf|]. assert (H1' : bval V B + x + Z.of_nat (length (cells_bytes cs)) <= 2 ^ 64) by (rewrite El; exact H1).
  exact (proj2 (rd_bytes V m B MF x _ _ HF H0 H1' E)).
Qed.

(* [comment removed for export] *)
Theorem rd_junk : forall V m B MF x n, Forall (mfact_ok segs V m) MF -> fcov B MF x n = true ->
  0 <= bval V B + x -> bval V B + x + Z.of_nat n <= 2 ^ 64 -> exists j, cells_at segs m (bval V B + x) [CB n j].
Proof.
  intros V m B MF x n HF Hc H0 H1. unfold fcov in Hc. destruct (fbytes B MF x n) as [bs|] eqn:E; [|discriminate].
  destruct (rd_bytes V m B MF x n bs HF H0 H1 E) as [Hl Hb]. exists bs. split.
  - cbn [cells_wf cell_wf]. split; [exact Hl| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
Qed.

End Reader.
